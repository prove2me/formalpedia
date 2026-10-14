-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:28:20.837378+00:00
-- url     : https://prove2.me/submissions/57f2b140-d33f-4828-a033-b594e207b0e9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 363669064 ≤ n < 363848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 363670314 1250 363669064 363669079
    0x60c030e04020f091002010b10050304021917070609121707050607030207030e180106051806070503210c25211805010c150b0604060c0303050106030623 67
    0x3030005007240d10003070b00b06441d103c0104400903a4181401210088000ba00013080080c0c4441c0c009000c4001c80003603442000000800182152905c40103550440c095241050030191074030714480d001c2550520401046c895140006407132845034014000709c81207030b0204080d404403500c03242900d0920790710703036050000d08004000005030100251442480d99543c0141c9400d201c2c540100b00c803601024003445500108144184c1d000000603036411100c29040240d0307240003c0000c0300c4c162120801c00c586c030071400700d491010700c84048002c01144401d03a4501c0004440c040003c10702540a84119a0500050081c94138002c62551894071400c2d00400e5040e100f0415982d800720101c02640003241c00b00342892151006801440100c10042c22504408845040c02c00091030001030718005460064411103600c00010075a001201995010b4071803a5107076107560016040c0c211004045000915046c000910300e4440d01c11601500d5400e203096000303082c5900031802d12100303403541d00c2d400f801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 363671564 1250 363670314 363670337
    0x1012020f070c0e010f0b03011805070e04330f12111018090203070f0c061b020a050706081306020304050c060310140f010207120c030209070e100c020a060c03 69
    0x411249800052540400c0c020300c5604150346000d000806600510340500c052005020310048006da0005274138100c3c03000680d41d507807400100c1c0d0604600d540c150704945000920801000756400720302c0710070540c01070031120541d5100e4910340d41c042ca208402e020110030001b8020340e030320020503408541c000c022940b00980e0490004000075490400000071640455524500281c102c40030303c01488202e004605501d03109a020b440340d01858250020007034038070388180c200861948018400801100c00c1c0e080c8819590019540b80410704007038486104007040007854501c20103080303108a0701040c4074a110460b42c1d070b4420180d000035100f00c400e1302480034903c4203600c3d100081c40c494900b16410384c4980b868522001529440e001c94540034510804009410780d80000d00d000c00c60b0840b60b00386c1450301c0203041c0840080800d4000a61010b103a00501611641c0404002000201110700707440703004000c14240d4200300710030030003904403c6051041140358050402210001d000342051003a108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 363672814 1250 363671564 363671573
    0x9060904020d140a0c09050402010e01090303022d010c030203270a06050a1d100b040b0603010e1b0c160b0702011403100807031b1a1914071101020c1012020f07 70
    0x5646d080302506a0f91a0700300015581e00104220360f40d082824071401140c01c40d10300139210a0307500f11307290750340c4036104400341c1c04818404c5407a1280c100a008200410403118001c01a600c251003d400c0f1034001003006042096842c5a88444c5003902c0c001d018820460303403054040d000003132103900259920742105e03100d4241c803400d900c401c13075610000d044159048191041110000c3d40300b103009a2814214502caa2641811a81540e056406242142c1d4842583c44103042103410080102c08011401079024180081c88140d05001c04620b04040794480901c13000602031840042d001906561000d22003048400003940c100d25030f0201840074644415520746005a5584100e6103030341036620320088240c1b103103582303005040404180e00350503642c12014044c5018560b01e501403150141102581180640031140f002568070a9258480340d080c28407881414016294601600030080c0c1c900d03462030002c07500302c0741d034815841d40250000187c606400a41000540048040d03007081b903840441c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 363674064 1250 363672814 363672833
    0x6040e1503010507021504061d030d02040302090109230a110f070b0f0103020d0605151503070914011209020f04020f040612290d0204150509060904020d140a 69
    0x385404000c0c100a03900c0303242894219840100040704641000d600d11b61904008551359030042e41041001c984950344014610a48200c0284481280700003c0c6442c6001403640141044034000c44022090b13a13030301e0981c5011346a046104000314040d82600c0f484180c000f1510303c1e0443c4002000146400340c01c6a42c010950041810326030a08020507803000300300025080641c00100c0c40c8030304986515560124542100b9680000e0a06031200b0004152902d4444002c9090360010714101544484a903141400e40c42542c1000c0010715461f0b0100c1c004038800500e4540d10010303511003c245642c0140403006040090040741c2c04010f5500d00051a034950001d40f4902080b210150381d00d030306e0300402910240100c02807030300c0d45080480008107000d14020103032032140c1d0402940300c8074640c840010301080fa00f1000030740c8a0b00c0d208845101010b00401311090b108280c58000c90340c0c0390041080400601140c0083d8020a002ea00d1000586a4a139507010441e1000848080040d2650742d407103003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 363675314 1250 363674064 363674071
    0x40209040f0c0810021803010c02030f07060b0a0b07060c0f05031506040938031e0f100204090f0207020f100c050109030810290a0c050a08130b040806011406040e 71
    0x41d5001b10340b43c070009120080c0c08403110307012002000385c000000d0020751203016410170011000004503502081c4009038011140d5148010060954251148240c0b203968005a000b610f005141c8803441c2d0700b0724014446000c0880e895160682141d48100d0003a00114884403281e4100c0c0e410310002540c078000b401251281d1599a2081900c0e00c0500e484142110b20a84000100031101d1034190141d2070214001c8602060000c145103620158640c0720714040c20080180060f1260041e8140c1e01ca48960180095545a40c8107000a80c5280c0e0044180c0c0240e84004e540300c204902241000c0c5000508040b200b9818113100c100c0340c03907549600d804c49107101c00a0300403524203c200b1010b4250211100b020348040e240c0d072803202d00344100060140ca06041050901c600004032000014010360410f10700c40e0b808800c46030415414680241e02d07410000c21810b4007907045c1c902142d0000d00500b0b41d8261202e400041a0b00c0c6e20b05858150750880b50b111854000c08100301c08581b0304000b42c5658403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 363676564 1250 363675314 363675343
    0x515060a0c021809011808070602130b0705010510060203040f0b160b0406060303120911090603210c16060c061e0207030806101b02061c0507080a0f05040209040f0c08 73
    0x70f130710b4084445401d480f1005d48640590b2842501800011111416180456004080140c072103807000c510080244c174079048150003080200d56001040015008144a401c41d84054814590346140c1641d69002d207008409401700004414403203041040c02515072040401d02c805801c280d552200042424183d030141d40540c1c542c00180141604041007810416003928108807a00c0340761100c0d514640d125100502c110107020208810f40d0702000243c4240702040d4045034603503030324607400140746d2042c2c0607040036000e0b201c408230800d1850058002119000d407251202e101d01c9a480600034801c80b60030001128074050b007011019a1880a411064400c1c0c07215141400d00c502005000303c5d01000c084100041c44020741c034070088903511031840e83e1341552801c0e16003c0e0582d412041d10030031414400c4052074003040000ca190310100e194040c4c180804204401c12103010803000381c403400c5502a400400c2a00404c0c00155808648130495001d00044601580c03240c00c020b08004c00c0341c0000a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 363677814 1250 363676564 363676609
    0x603150c1909060e060a0c082a010b0406140904080c0111191704120e130c0201140108070807231203090a09090c03022107030302100e010515060a0c02 66
    0x2003060307001601d04220b004d0884055003844c180e00d6008003041d8100100901101001c07815040041e020110000800c9107102d08101c1144261200d03030003040d02c903407200d10460611a0004100529001c000007040010300351260b103a0b01da80740c0700b14550180310380c980290f5880c00042c1c42002c000b40541501c2c0100360380a0302030203035607030000c009510004101032045200c20030b010005544a0b06821180561706020484280d4040010b45400300d454800d0403150422441c0120181c0c1940482c881800c1000402003690702c80c49840d40c2d64210f4000c400250780310620501050381000c000032128122101c0c410b1300e050760382c0c020814510311990600d54a03440810302d00204c0c80c2c00d1507454040c181404003000402d0071501c1b440181142c620000e40100ca02902801e1541e4481900080d04c1008030101d5502c02d54901c1c00070351f505e410070417507aa0310740b07090341080d001c040c18050580200e21407004c60590307201d82803c00000307034032006a103c10300540c62038000043c0c4030240c10000802c0e04001d2031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 363679064 1250 363677814 363677819
    0x206091f08100e07090e101a040602070b0a050d1109032a04020c0c04020d0921031503020d150f0609020403050d050309070e0a1e020c010f050603150c1909 68
    0x280b810b90070f801031141e0a1002040000c420317030159510080320b214100783ca4180d21400020414a5100d0300000e682d00039646100500c1c003c190010400c440d5241d01f103c80030b69640d040c180050007425641400502e00304200c0c0c050001c160483e015825402034070703502d4089981c0010b480c202090410001041c40088140b00440240c4404810100e00303036001c1d17141c11940c40c003107034072880d50b4107241d44140e41c042514186404958480e00c40c803075001003828880c004c002c403100b0300c2403c0c071111140080e090100001046901d5200d2404690b4090042e181640c0780d0ba4480500101010002c00206c0d030390341c09868414203d006100060041c1000107036200d046040207800c20030b042040e8000d2002c10802c3c4401c000001030b4140c00c984d407445aa0000391a0748507020050140e601071050700c4244480c0303404564650303070300524881d02d08c3c034002c11189501d801208152002210003551641142140c2d0444087d4041100c4c1d002020064003843c02c9912841510803926207801e01c8002456039200303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 363680314 1250 363679064 363679081
    0xc030509070501090f06110a020312070506061503040224030115020f12041503020403050d1d030a020a050609010201020d0501120203070902031006051803070b03091908070206091f08 80
    0x6001c0030700360038078045142e581081414119000383d845554100f280300340c140d2044120034000c15038480da00078295a44d040702c41101c1d1225400241c07007507405006200110340d440c50010300311b1010200810405055688540030400e212080c8000e040c1030340740c05c0700c5040c007203851a00190302810f0780c00e020000b2205079010007850035003e991055002e50008030348100815006041c0c81c101c51180d0812000141a28400c80c00781c0038540c401841481440c406024060708400340e50011048040c088203400103000400d6642e65050030b02a411981410082c025070074080c00800c060101070001525260004107840101c41c426800300e00d007040e804181a0071881c040c00a8002059070500c19070460909416071802d0010a00c070740b0302032140c001110500c5880704c4c84641d1204100a081c0c0d4116039445079803800d564401c9880e41c03054052408588206200003611024141d00040400d0602c6025420312031598403e04440303900052042e0a03558209a00641c1301c2c00066640e611145418040b08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 363681564 1250 363680314 363680323
    0x2090a020d1a0306010e0c2701030e0d2304030b0a0e060c070308010b030a0f0c0e030c0103020c0304050628031b1b030309110303040815060d0206120403120c030509 72
    0x3a02c410580e415401e580303140d030002005030544200810b0304403242c541910f40c003401d1046000500700e080001c1c40100619644c3c40c2d40380f181440a0302c05209019440d40503d03200d5940d00300c0c0002080454a986032a01500c61140248007854801d1a00e065103a40710844c61041c101c442c81817040c2c03144982d4140c21030601005401000380000d0604221540d600030307110070014081c001011034003000050f20228150401c11002035201410010700d01c06400c0188034000c0321003924080c1c452490140c0e00e5510a1084550303e0700c0d0200518101420001008100d92020b51480f0b40d110040c02e0380041751703184c071044184110598a001400b1400002c81c85070080e4401480d20601002b06000c41000603034544c07031040c01e5032620300069034100b24501006181241031203070b50188400318011820940000f603203c014030b840e50118125988287c00c1002c0300200326002034201c4020300000382400b400400b919040791080c20108403185255040c0011102003081c0d02d00001e8640d018484910001d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 363682814 1250 363681564 363681581
    0x91a04150e0306130302010b09010e040c080708120f09040608031308030f04053a020108241309080325020c030316050c10021f05010315051302090a020d 67
    0x9100d8104101c40002036207603c4020000560034004141c00000c0510030340c440d04c0c50308802032084040e561203920003001400100d0b800c4420900000c80401c000700d0000e40cbd00d04a506140082030194181240c0c40100c0e084062040710b000014481c20705950340743e001d214040c0110200450300d40c1da5444007404107c50310f901840440d00300b0040d00f031a5407c10003c48003529416521044105c0584020644601c11b21040c04400142d103c0050084040400501951030007661380764465200c0302441c0c00c4500200b5421119240310b0009800340d4101001c0d140c410214070400050a100e81c1c3e02d440509078422941c034204800b501d244110741440702c10350718881154610050486008802c0841e03524403030185e50000704106000903404000040100344065040504217110040c5200700107507446180079007607440c48590b83d60351000c1c0050740c41000d04a139080442d000340281d0915001d0010000035041c5640307050340c00801c030096183d40c584140200380a050040c0d82d51044030209003107a5081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 363684064 1250 363682814 363682817
    0x50c090a0506090a0b06070201030c0519021b060313140a120207060f0c0210080a0b1c02270103032610030201081b07020f04021b0c1c02090a0c091a0415 67
    0xd04501e291151001d1f074100c245d0a00300014131403d488416521402a0443c1c80d0100c80c1d807018211b0340ca80d0110301e08a403d0005809150801f03c1c0300c0400c140c1e07010271552801e90300c4500f00040e01140030802d200c5041c3c4000c90640b00700028645a0500c124516019032001da4130a44042003081d6005e03405c030074402c0c010318001c41e070f030b120941c0000d9001004000b076004003d4040c3c041000b06000e64042e8000107002000c000007050f6140303402c00c43c5c000d01d003001c4c0d02c0340180140b1582e1003280460244003211181c07040d00d010b41e085983c140e035078148503001144110514840d80591844c118681401114a908050341161841c8001802103400504101001040242040201507800107075000c059048410b542000d0040c8080707002400340180c914001c41202ca8400428440800d0440c0a980c3c20354843d00201c003c0c800c50303070003d03d1070344000790041c1140001803812503540c8c0c082c41401d881d81c034101500359078039a203024a01100020050048600240c10800c0030151300c09004000c20a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 363685314 1250 363684064 363684071
    0x609070e0601030c0e090901020f12060a0b070f080c07050d03020c0325090209030102090a03031d01020102070b0f060103060b1c0b0306130b04030512040c080114060319050c090a0506090a 82
    0x543c10007420115034000d1703a4081c54119012401d02d040072340603078181c1300e4410000c5492341c055202c511120101980c040d406508070100110340b5254090454a500d5002070b040940451541d41c2d009280d840404411911b00a0f1100880e06a46051000006c240070380e006000c1413801c10101810301412034034010132903201106603c0030000d581d1001d41140d403001c90040e00c429444001ca40a84954a85030b03620419000d80403081642000302001440c00c001081021b810207200164200c3c170030820040d02c6c06007400c0001d405405100c0d8041e6104c0010314010030702d00d81d52024505550454078001e00031014072580946810f03450310a850501c4030460091403d820309101091300c10a0100024080d11148800901894050300880d9041001c0b40750f008458989400d00c00401e10940c0510b0065508151616100d241505016800b40c0700c000d000d04098602d02c51045600760f14118103c80c41d00410501e4400c590303c203040c40e0701c1406d00d800c0c0402c2c00c2c94840d0400c08812001400300000d0b0f440c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 363686564 1250 363685314 363685331
    0xd1d0c0d030f05090105042d0801090b010b090409050d02061801050c0708031e01030f060b0103090b0f220812070807051c02040512070e180307150b030609070e060103 73
    0x1403007060318241c0340e02c0e414004d50722203200e07004079034600c59a00404189001801c643c51803281e02c00990690380c41c82c40143c00b0054654004509035590b144014005d20444401806030644140050007403200007040000c01190702d44c5d405040c800302440000147c1c00c1f8a04101c0000c0030180c0c4c440c40818048020820791401b113a400410b80902d68020b41240307408000603c0e4400080c2403054510061100c421030303580d40f850000104020110201c89442c141000c00385d155001e0702031040302c0c690000c01600569a00700344c0d0403c40e100209410f1110201c03030044202940c040600003001401054441e60710154032461100014014120310304225404007009001c0368030900351620840024010140d48070300486c6a03010307020315085194800e2036100f00341c00c6500002000400c613140c0d101107940d10b1780c80c8003c2d5452482041003568564000b04041000a1403140c0b140006003202d040c0003568031078030400720f86403400844401c000741c0d10107441409154004003101340d0040003441c1c180910301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 363687814 1250 363686564 363686567
    0x80a0c06030e0304060c1e1416090c1209021f0c02090601110d03050618090609100501050f060d180b0a0e011505040b010c06020a022b0c03140d1d0c0d03 67
    0x651b119010304911001c041d0040d51390b03410300d24848019009081075480d050554602a02c03401003d882880140c00c1010004a585080c095480400c0c6991a101d1411801206190181c54001d008a0b4016013620040d140403025042010200703030b081d50b400151021a02c18480341031409031440c0c0c14096002c4071000c107004009004440d040c4d06140104564607150082404040e00b5201c0403a0445d1170420084660f40020710240701c0c041d0a022510700b0ba280380d844504981082c003407240c01c40b00340b00254140f810f1040c000c001040404c0b20000d00300d40031142c0d6a6541400c0e5a00b200c002459400344509100c0900440c4040c4544a0080004007100111140c00303114503c0f41600031030b00c8016000c0c0a038003d0034506042c80c2c02c0071040d0750368162031000030b450340f02906d500101c40d90304002c0203810040c00307a03500c3ca035801b868444070307030050090b20141e030b200d0203423130340c8140026080240c0f05200b0704074011118110645a1100300117003c010f440b50508000c21020380c0111920704256000c05d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 363689064 1250 363687814 363687827
    0x1806040e0606071104111908071e0e04090501090203101e0c0201090b07030e01060b04151419090521060402122b1e0207140604080a0c06030e030406 65
    0x4401260a01e58070303d4103141c9a107032034002d2400198000d00e4400c0d050520036142c0000c080c2d0315031030142c0c540c0c180107400f002c3d500090240d0342c4c0c60008448001c4449411079084841c1a08800c07410480000c07103d140004081e250322400881d0755944400100e011410300f00301449a141940005124000b0501004068400310398090408242c83e5150300700d00600079030021050b0380c1c0012000006103050304015000e407400031000000c640c40c2040c0001c104000e501501d059982c501610503806e81c50b01812601142c5001c00c00384402000c0100c601503640e8900c420312a1a02030703c40c940058605000c000c486403078882200140010080c00c0080f68030041000ca07401641141d03010141d0200b541050716001c80381100400c10f210412120000c410050581c82c0940c1a42d550100b9406030000c150082149110310800035a018000c144003c92014020880070705020b440e45041035580e83c003151400200100603145214000b0003401519414002c4c22652a801801149850710b44070303004144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 363690314 1250 363689064 363689071
    0x50f0d0e0103180501050a0b09010506040324180c0e0c0f1b0c06040b180f06030a180b040303050709091a190518012309150d06020c01021806040e 64
    0x4243d0750720341080080101800359122150840000c12003407030211300081c010510b08818902c200014400010180703002400c40d030940340c0c000710075200075044014803c0007503ca5042c0000054a4900514141d0042c000d6402d56038000d511880020349030a035481e0302104080d0000c030115030304100e5624400d03e1001155286415240f2154111b40e6a0080d83c4c00e000c400d03040d040c1e003d100083d00007a40400d00300540200c240f10f1408441c0000d40304100490300d1100d600380d031b82040050000841c0e0220341d50000e1001007064004113003502d641e80c1c40a044810494080f00841d40c0c030000d00484543c490310240207050007560800196100380600003182001c0851544282c1c910401c024204e82c2030040b0800903c405041c40c00d64441c40b488510032850700f402582c1ca005040c01c81c0c82e2495601c5501d44090b4400034250b44010b032110703c0f25017080000c0105007504044940003441c00940304e8402405450b03011000143c0b07a49040d00003c0445103600c1c000c5100f44030501082c80b200760940303e03c940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 363691564 1250 363690314 363690317
    0x1507092102090403021c030e06061008010b03071b0308091606090b0a090504090521070b04020f010507050a03030b190311040b031006080c12030711010806060c0a050a050f0d0e01 78
    0x3003d54031440d04a2404900030008040e180d845500719030f4854040d000b0400c00404101a0f60103641d0710018801800b00c0020541c001401c0400104501c0ca55240190380028242c6405096010940e0319941411020041180000c983d28100301001c1024440c2d2009055089072403001c4a28103100208440301c1d0740900c08943c4030004d03020700402e000718546c00090102030001c0c041c03252181856a1a020010a5541524a24140021304d426070b02c0407a510607500c43da07402c001e9104c176002c2c8030309002000062414080200440f0010a02c10061181c01500c82e94001c40c4c460700403000d000c044490a11a0b810000d03181c03009000081c0103080007000e0b81800d0360006400310002c00081d00d000c0000f940000c042d4905076001c03442d40004507401c054581d056030030f40310f004c2440462035500c0c426005c2c06002680a00c3e80c0b40b00c19071160080075007040e00200050700340581200c01e6400c100e0043d0013142c0307a9214070240c000f0003200b800f4102030240100701034280d65018980c058003000340e44408030f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 363692814 1250 363691564 363691579
    0x90a110103090b2d010846030f020c0109140102070b07060c020c010509030c0d02010e03030c010b031006050a1503060b0301080f0f0610051903051507092102 69
    0x24090340309a20100c610ba4201c800c00c000b5042002000340882250a506203c0030b400300303003580c0000000a0101d040f0f40c0f00a000380002540300b00785035010750b0800c811511760000400d00d11195072045a840010041014044550700a03a24002d403900c540e1103144810342d00300c40c207000560381e00001030008071400d02c120300b00441c00d002e0040381840c0d910340200881060100c0c0c80e0052107459404680d440303000d50201d80503000c0039001900d45018498800ea40340c1e02c5800c0c0351116003004028000707060700c103051440180b9049070000c1c1c156002015800c509079541c5181050070314007000200024517001004002e0300d4144804503080c2140341c010100d24500c000e6208441510030b40c0b1800c020a6807610340c41d100d58481c01c509845994052103140b5610500071001440b09001c11124002c1010000038000e9a03c1c000900128905106000100071a90b003000030110f5804d00c42200c40060319803d003503035480d01a1000c1c04c0f0103125000f0641149204c50b40d86c503c0298016424803180e0110b4504 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 363694064 1250 363692814 363692843
    0x90306090133080a030c052e0c140f1c06030b0105060f0906180108100e01050d02120102030106030b21190602090a1403072414040305030a05120c03090a 67
    0x120885595510400e02449031354546024076501c0800c980600b0322a1042e81d4200709031703082c1c0140380c011041030880d00610b03103084200c1002e0203a2000d0354001240c1880d10100c4035a1841860070340060040c2554082c0000380141c042d0810243d83d840360000c05d82c1081014155203400500e2a81409014068800005c10a044910070800c0da020341e10010815076440300d031042d00034210300d40c01040c035011814000102e404155078404110030f845952650441aa04c0c4c141040558019039205036040203000f0f9030203414400030300045010b1710094801091040300042400031481a024091002d00d149010740342c01c080d030200c0d0302d01488204803181d4039510082c1c00c010000313104000b58503520030440782002407400c0500392440340e09601202942e0603903945241440e800f980c03081c068034044071107404100c482070165006d600001c00d001c09103803e040c1c685e51182e1440d400b0364081404200301046180540003c240801c1d4080c909560701400c40c14048412a030f41c00314a40020f007a0b19444650 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 363695314 1250 363694064 363694151
    0x6010207031b05040608010209030d030c11010213150c03020a08070809090f090f030703210618051506071a06031f0e060901111b010609020703050903060901 69
    0x446001d15001031428050032814420b46220800910034503010702e08107500010000018401e0b9042003a000d0b000d441000b0403141708a000b0071408500c0000d01c1104803401070364450900c050311010b600301812200c030509050356044c15800c1c0058100c00c0000b4030703c1980000c1d0340460002c407541e600110060300c0e0780b002d10780345503075001e0f125400d900314100c1d508020f641c0224840c107600804040c81034412039002d0350201c07a00d074440c2913000b50100b01421103d11084415403a0a80003040300c0c040000c410340c81e07089851581d801c40f0020702d549504e6001b801201c1c001402c01346860384040321500c1c03904460b9550302c0140c000b03c02e0510201480c440006020751400e0001441a02d01015010306400801001400800e54001440d48912034080041c026080511440c40c02400f3342214074142004880304a0000d580e540c6600001c2d500e37090002080b4985001800c0c005100c6d84495854080c80000d042c0341c6100102042c103e607040001754404803580d15422001c0780144000341c507403400d03110003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 363696564 1250 363695314 363695323
    0x1403040f09020c0a061b0e1c03050708070f050d0e01030507080109020d06050301020d091a0103020616060905011103010915051c020f190812040e0a02030703090b010303261608060102 80
    0x5020710b401c1c26000b9218001c2e110201d0702415464403640007100e40342c82800701405d602868040804140c48c08400480e010304c2c00782c07900070700c16880c2c203281c01c00941da1940e20b0b512035903040701e44d6480b601c5802102c03604540b1101c42c0b42c200f840d0401842c0b0f00450010502d14041c03155a0100d540003030181c1c040f41841d00070300084d110140c002d41da20b0b40b10f80c1e03030300c4000c24201d101611002c1c90b28080070001020b58180a040344c3d0014003150508008602551101b140d41008490a85e52104840c2c00500280111544a030921001a85961401038030b2400d9480e509900812110640300900580e640c240e8010f00c0212800480440c0d6204c5201150f000b104120f100b540c02184c0c242d4400119050b0f586181c00d0302e0741e54050b110301c9026101214540e0040e03001c1c28001d60100703400604612007507809158028071364540410244080e440311034800c002a0030641c00200101010207180303401103c100b80707000701091044840e16083c01d58215504400703150702e04100004d00401c0d2660710800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 363697814 1250 363696564 363696583
    0xa0c06090203031215120106080309040507110607020604030e030c09011502070f0e06100804110f04061203020d02010509070311130b030d020c030106060c11190b0c0a1403040f09020c 80
    0x440c0c075090501915851403003008500c5c2e184500d000d0702d0910b883e510180142d8040741c00b0f4400950400243d80c0801c40500f000a24490820000790009610003004100c518081e49c41c40e0003070b1695003810708000b4080340030540c0d0203002c0c0c1d1024460754850789486e81c4403411035203403070f580084180032540200c1c1031940c1540900704094103d50041074481c010f0301e040340120001c17a806040f01c9441c4000b56070440080310064103c0e800c5580d138203a10b0400b0b20061144c1d030001040080c802d6181d8101c41c1c20160f10150560059000c03094403006990240300b65a0890f19402c0200340d000e196a0f02d041c112200d5007801c034015030031100b61005042450f001022a40340042c08d550944054a500a694105140743d6134401d6007012000141c060160051855240d08034070f0303040010b29003030244180303240d220030f68150422110030f0018050280720302404902e5207042c041e0003580380c0c41c141074256640004041d9844d800c00c1004102e00b40c0503503080c00031142e0660000d1303110202107061a0030300c3c6814 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 363699064 1250 363697814 363697837
    0xc0203090a23030a0b010608060409020d080703080a0501150309023001110a0e2101050c07060b03010506010c150b06070320070f0918060e070501140a0c0609020303 72
    0x11000319054051082c002200020300e030b440450040035004240c0c2d2401280b102501c0010400010711406201d0817215520100c09807020aa1403850360104003030145004094406180111b2010100b40c0e102c040c09800c511740c1d5006120319410010010001c03d100764803d4145940d9205110454a444a00d80b07040c1a0b5034600022042c1403658054002032400c0c2d11440c254a003001c6610902c0c1604150f5908400076500c21549444090602403c0070b2804081d607440000c03d80101d002920034050b1502c503400f2041c08545030b40c044c1c6814019600c0d9810b80034800d034148070401c8040e0764060b1561051a0704011900740c4240c00d000380c00e0080c0140d800035600302d50001006400d15801c410004c1c0e05c81e20001080354507078003042140d0b84520352402190014040b4403010040d101c2d0a0300026548080d048000c440b0f1100c7c1e60f03070b00b8103d03441443d1010302900b24a104000b41d6070000c0003842c1c1040161350b40d030711380101d00d44001c004051000d001400b842d50740003900195102041500d800ca10b8a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 363700314 1250 363699064 363699079
    0xd020c19150503041703090c06211014120c0f06040803120403080906060a15031e0f0b010f08041b030807030e0306070e03030d0c0c12050d06090b03030a030c020309 72
    0x40c200700400a0380120313820340d607594415484241104e4a0ba08891164440a0144c00384d513103240c0c00c00045074000c100a800c0580b14803c0c4980c8001c220181e40e0081e25020301c10340000386055070820b40c0685821169204508104280341e000340d01240a031190340c8122041624204c4c8507001038454091a0494078143c40041558142c4180c41d80c4000e00581c000d40307482c1065517501205c1c2e03690f20000c6948940081004100b0068030a00f500e45a050740346a0802090344000c0d03504a1354200450441e808045e5143c02e11018413440354817031035070b0244080c80d00900b03050303219001901e4001d000e0302c000c19007802009800170b0b07150003040943c050350344a12200d6492001e814001e0132f0342800000b0501c030703001b90000701e030055019420400c1125000383c041c5080541c1610134000410100a0704030034840c1d9001508002480319801684888141e00d60720f40702c0c5188041d2404079007494210b155190b06c0c1c80326003c0a80d600200341d407480b00007480c0101c2c2d0f00c0d510341c100b01e046006000c40650860071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 363701564 1250 363700314 363700349
    0x3050a05010507030b0901140910052808010615180306060608041a070c03053a050723030604060b0301180e0114010e04050f0706030515030d020c19 65
    0x2010b410441c01081c0035a001c1c803000007074030204400342e14203110f032000701840044d1200c001c3c2400b001d80c0e503121503401c440704107407a47d070000b040340007000c0300c400c92500401c0c00e80b8010181d8262402d002900804c4000c025407410910008075811041030f8280900405030204201c400200341280b016590080c01404416900c00c1c026103075178004e403001c0b5003401c407101d05a0440680e5000786841000260356410018615032030548142d84113022010b11031030709507007245940c10306088449400c07101d80b104a0400300d075014500201c41c1c004e4410400c100d2408040e10100540442e440030440640ca0003a50700d031036160018008081c69400b43e042c0c078402000010384441410600441104120010700180d01d1104065080f40e41c0c102c0781d4800f2100000051000d0442015040e521600c41c404072218020811035540c60300c0c400d9401000083e0711181044002440500210121201500280b6480c0011a0f01030f440d001202c80c4180207240c02e180c5c1141c840509080d6900070030040c200e0520501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 363702814 1250 363701564 363701573
    0xd0204090b0315060a06050c1504120908010902010818150a20041a09120102030c03240108010303030e030d02040308040614070807060c0e03030a0207061116050d05030403050a 77
    0x81c5511035403003400b8681100d0209031072456668030600c0024980c420044c28130b00141c034140c01c0814511807900c00c003a01e694085820400503405540240800400488008002071035014650428170703180e41801e50301c100507600000142e402601c0849184102420404040c0c507240510749141d48200203181032060415040d88200c0501102d81c58004c00c8000c5a00c090215204034424071508101110050342d070864088050801e1340d000520f000d0803802142c0315a82660401c7d100380c10075800000c140187d0102418050b60440e2268440e0705810441d6800a000c051052101400303041d25000b00508044060080b905030000001e03007151100c1e101e050820b041d07041401594041042d10b40081d81c0f100010080d102690f60022005103041115510140940351600d000c0301400102e43d10030005540600c080c0c50b824540794020f100e01890408010300040382504811001d1700030b074004400034124407114406855003942d207000420b041d49803440c5988100d50003c0c0c042e0194103813850411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 363704064 1250 363702814 363702821
    0xf0b182b050d050906030c0706140103080d06061115102606010806160f020709140411060309030a1b051f05160801030f02010e03030309030c0f01091e080d020409 71
    0x4902601c201c0b5803114820350151880d109002c42203902207010b0000403c1d000d031540c018422184100300210303a100036a881400c000781e081c1c008513072284020890089040c0e00e885114020710b0720340341150042c0c411420254880c0c8d0006e04440382c120b45940000c08050700f4000e07501c014080d221000400311400c00b20b203903005900300442c02e40b6019140c0000b0f540c2c5000254540205410680b48003603031703111001582e03600d840f001001c0550181000c0020132002c00d10a24892040403065040c15143ca07242c43c0355810362040120380305000520034410300503400000e403448940ba504020070780000985210389c07590030314a40180f240c03140014026000451917060036411402410620554039464140b01f5014131500980740041c0d0032100401c0824030392010b00304064010306020152031503c8011a04540c411100e0000e2580300283c0032901c140300300b01c0c0c00100a11200200800e6036160340e00c0c5201202d10070341e5150041102004800c1c00140f8040365910b640d840c00c115900d0342e540ea00540074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 363705314 1250 363704064 363704149
    0x70807062a110d1a0c1b070f0b0d090f051c090b1801030213060f0f110c01050306120102030103050105040c0b1206121005010801150f0b18 61
    0x11281216440c00d4005680070107621025030112040c4007154180c020320000d050080e00c10b43e41131212240210f03a030b0710a0b2100d00d0203501c403054a2666008441001041e0b1000b00d41007000d02c3d030156004100c400e07820003004082d6800d202c016640c5d40307100450340e0043c180c1000040c04200f0303141003940c1040703400910503914903105170100d4200b9a181c842681da11006101e0404110020001004205100d9044076103030f18050400504080a20144940151445c2c0140010661420b2505039090300180c1d0842d10107201d10300b1250848450806986800c03645001a060210100201d2900e6595001000c00300204400840d01c039030352800c1640c040c11050b10266603503007050001151084085080314550002d11601651030388842c005d020710080b43d41c141d580c0c80e006030303d01c00020a1940c02070724020109880041040b130043ca03032800740c00003181c0c82152441050801009070401d51020b80d414040c00e030200084000895011400c041c402c02c6407204d841e0702143c140100741c25040940320741e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 363706564 1250 363705314 363705347
    0x3290a0b010e042c0a0b06040510080a05010906060f05010504090507030b130b0108060609010f080c0405030106092c07030b0c1e0706050f2205010e070e0103030e0d08090108060307080706 82
    0x501d2185005003a1700c600c00307418091701c3d01d58458000380c3c0301d0601d80c101d542c025009100c2c2d504040e0b80c8401d080d092129401c0300701da250f51100f980c40240f20b814084c1102802102040541084c134040c0043c100e88118400d845017603407154000340360640254416001b0a1000d4584220182403409031001482110307066070100b0020380106105040580130388000c0c41040c0c440360f0500c0c221001c203864000004000204440081001046a45085c02840018140e00380042042e441a10014021006a40e00e440e40640c00a4103541ea040002460600322904000c0741d0292383c440305000415845100e070700c160440980075001840070038520003011168082c0f1000c0105c1d455804201c030700160203407543d0a00324060302810014600c40d20074100c05c00c7c869000012059211042c160030040b056024902c5003090f040100189034212001c4c2d44c003444210741c143d0168500381d440d05440d00030a201c0e5810002404001030050702d0400264010701040c4080358045982e4036001003052001554051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 363707814 1250 363706564 363706631
    0x3120709060306150c15060510120b09060d080d020f0711030d030e0607030c02150112140a050303071101150312030b03030c07060e01121503290a0b010e04 68
    0x4e2000400d0320903003001c501e1582c807101901c095841d06000022030044030100f19a588a0004995842040d888081c041d00d458810440140990b175034212100400000e000d841c2c04000c000c110703641c5071040d0b80d0070381e80640c4051700c981006010b00024082d000e900d408002000400303000344410840010f0740107100718206d40250a00b160100e003580c44014664002d0360104000c905028001d820582004505204580c1c8144041000c0c0c01c10800030f901020300002d0b400c5443e010300c4404148118120010401480046d12503550385079a40302c01801c4c1001c00007041c6241c00c580030290018228031614125018010f5140d044c0344141a00b070740c0c03101000c00e10306451080642804000d680104614401801c0c80d90b28201098640065498000e0704009090b09819080d84003403041d801c5003851003c00450250942c5000b00ca076031242c0302400d41d280c4c3c0c2c1d1a403044230881403801c02d0750b00410b05880810000c61100050703078158000c10b8600c0d40181040102180301d18461410000c00c00f0528004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 363709064 1250 363707814 363707819
    0x711030109030c02060d020d1503060b01180303030b06121603050a090201091e05090906090607360914041b12110f090a020d06060e030a0f0503120709060306 69
    0x50880d055a03078010049140c84070440c01601e4281c016100c00080820701510b05190340010200302d41082e0117203150150b45c4042401404240d208029005400b8248000c0d6070340403903240c2d40201403900c0018201603c909014149071291015108202d680800200c090704244401011122216505500007850400081c040342c1103409103680f00c64060311039400c5982071040c034804003058201c0030003c51500403400116500e0340c0e0f490500c520001c00240140307060001c0d1a82c00d1141c0a05554100410452078030001652a2050030300603c3c0c441c00710091080c6540c00400404c0703940d004040c050328045d03d035400e903e24185082d215a100d2311000039a03161075030f00300813020203074010700c0501c4c4c625030b801c000000ca402c00c4560114600511a027003c400c1c01002400b00303c01141c62100e49030300410400c0029041780a68070152419090410181041801181e6100404031001d0310140d00140d81c0c2c402d11100340115800c40c40b4440c02509a403a1101000d8407011240c031641c0d00007803410400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 363710314 1250 363709064 363709069
    0x9050f060c0d0506041d030a080105010509060306061b071e0e102d060f080603060603060703091e0b010e070305060f01030209122a030c03062e0801020711 68
    0x41482241c0385520942000e594442210003000300401441d0403503500e07001c100c0708154100307a06040301940e00c001c69580940c9030008044000c183e1000f414000c051080c0200c5030780f9074064960005080d58400e032034100f91321400701c003034811300070000145c014008042050750860b41f2820390100c4058480c82d0b070554035001e006c1100c00440c0e582c484292017040034441a502c5a41015034034030070900346a801d08a080c0a001e00c035101790f101d00042002006450445500014246e81c003640403000740c40c641c43c00402294960000800b81c02c10999103080b81c07070400550003418080f808003458001501d07652490300310705c0c0800130300600010010302d60000b91a039120303020300c0b0b02c900005020b1811132503171280198065004003059580c08800c000f46803c0f410001c01081c0e514031085000911802d500401001041d40c40340c1c10742d4020381050450107115100055800e4108030a43c00c0280788c984006501601072031446031100200101201c0001c0c50941500600140e500486101d00524494001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 363711564 1250 363710314 363710323
    0xa031514040b1317130e15031209150304080307020c0a030c032303030702060a0f0b0312030a0603020603070804061a010e040c1b08070b070203040b160507030605070309050f 76
    0x100204042c0355400000e5805000c280340c0048244a803c01149244d6401d101071000e8021303070440703111100041002c000c0c13400302d0790007160000c41c0c9070302c240c07000742c50080840d45030380002d58203100f0071200140e995615103c07919503034500c200d000d01c0aa2681468034215034294401e4942800510489950b503050b407820206100c1140d500000c2140c00b185540e5484401041c401d032a05100740001440d40742c0100180011441415a40d001d0030070343c500740d40404202d80c203101c07500e954203140c00075a00c403030386000403109081a40c00000e25100c1e1384800301600640300382d8000a4000b1800301c00d0203031203030b0401891b07406207200750818440050454040b15451268400503070000703e02c1007148541d030515906c5503450402d9450b001e450508402100d80d400d48100000704c9000000040d148144805104840c0d0000308600c09503107414a8808502c08502500e101d05040026510210080140400480707004661010040c082c501d049440603004000d0464155521302035401c5201000c1400314 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 363712814 1250 363711564 363711571
    0x12109050601060e0a06080606090a03060c021c051e0403050307030207090e06071b030c0b0114041b050702060c100c08041214180a0b04030f031101110403061a0a031514 74
    0x38205e140403464154101d5040c1c20140100da0401800c101c0e0400c1602d807000b103840614001e48020842d1281108000d10707020708031100354038410030f101c81512010740c05001c03542242c0e20750b400304180160000c05030708103121700c0d0f00c003c2151200107165000c1540200e40b1a08035076100404028156080000640303698045903a0400070304085150302d4503141c1039122814807806803820f248032454541d00d44504800c283c0186000c02094010800b070741c0303001e0207030405040081442d01c00c1c0f098106805040d501034010b0007072041c10040b41c401c2c0c400c1400c000000140d04009814003050900241c00703001d851083d1425100e48240b030060300344a6010f441c3d0025180c3c0e003a51a01e2500840c04a07603001c10003840301865108200c0e04002070641040805800a03500803219001110301500d009007215601440030b00169041c00f0306213418042c0d480030754045035040b910200380c0c2c1b500d440c42c6100c0c0c400c0c1c205a05500100384c51003c130512080d011b41c81c4003011186020004011020440500c070074046 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 363714064 1250 363712814 363712819
    0x10b09011d0402010c06020d0e010e0c0a050f120a0b0a06060e0603130201080a0b060c010e25090f1d0705091308160206040b07030507060b010f0c0b06012109050601060e 74
    0x1080898010f510905c1504941c900620700103081188401e0780d802038030403410403c10756039181c140c0e2001c0160241b00410b0356a804a545041c89c0d484d18003c03581c40d45035000d030548180d007a00521380784014280034004c40706612401601d07981c90003034030001c001e113000d015071000101d5000e0389010394100503080703078001d42d4003091010300e0704d425600446624034020b151105480e1601c54082003512504090003c010100340007080405002001500d440003007a8158014021102e03240103030803181d12048140c0b024264080b030181070079405c3c40081c0807144003282d045000c10030108581000481e9031001d85000f02c508000315111400c0143d00f000d41c804016000100030000c1030074504540a090740d20f144041c140c241801e6603070201c88400c0d044440c0540105000140450800610f807042c40c141c007009007401c090480c1d5460006115100310079000707200c880c3d21001700d0311980c02980031810f5451440f1081403001d0b211209000a07240881088826104140021400314003a0f600c910005102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 363715314 1250 363714064 363714119
    0xf06030924150a0b160311070e040204050c040315020a090f1e060203030702071202040905031c0501060906050f0d1e020c07080d050a0f2c0f0907050328020408010b0901 74
    0x1852002d900011340140403024004007d1392400340b40e400741b062400504903040c0840c100e18150040c0300585da8000d10032034142004000500014401c102071804c00140100010303240c0c400300d0025038138000385400088101d00c410b203000400b4924400c01c031111001b5841c0c5070f1501c83d52000b05a13501e020954015000d170b00158000e02000340c07581c0308041032030700003080840c05110546400d0b00303590125000e0181d194003401c2400d0344242c0d40c0640c600401d401c2c078200c0300092a102c8014800c0c09420312440201d45c0c00100d8120001d4140c003e846180007a4402170315680340e05043c1d000030360011040440b44c0c0036042000890450102d40310380a07040a407507941c0303441d02c54001110606c2c06c40a01c0801d0120808800700f00400c202111260103000716011480409041c0410103400c1f5544c4400c0d01c00e02c200000c110500e41c1c00001d50b40c200d00c0015003012030b2400300d140f050f030440d946c0000340f00d032074404074000035418015000000c510000781c801c0354030b6980f28070004502285035007002a620b0710 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 363716564 1250 363715314 363715327
    0x2010e0103200901050f0f03072a02040f0902090c09032404060207140a0503130e070909020a050c0a0f02100207060221040320130603020f06030924150a0b 68
    0x11050014028420145001e40c98001c50004400300b41d008000504091f403004002c00c000d19400610142d491900810500c910070000842d400c1c0201110100038040ea8460100300401e1426411500701076600170503029042c90304030600405504045c1c1c020f48a0311131209044c42d040c125141c40c0f10102c08092507804541d41d551500e2001e580000b03011142035800210b59210b241d0144410248035100c0c201556440150540e248032001403a08074941c015007413814400030f01c2c1c000491400301e5020490158403031020303400644550007004c0040700180905c9091600304404100001c0011b4421910f08030100d003000c804a07611b4015004210150f0300034a80715801e0708860942160741102013150303074a0a80c0302c3d0b903100b0000c00000003503807541c00a8220b035400d900d44902400c1c400760044104002062440e00054151031000c01c40d1405003100201150102c80140845580038504800d4080f41c10007036620401d040008172120341405840c41080b1010b450080703000301c202c40c042d0410f9800d200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 363717814 1250 363716564 363716621
    0x8040f02030a02030703080301060f0e03100c0504081f0501091e0902210607020609011a060c031201030c06020606010302030c030f100302090109150b0702060f031e0a050402010e0103 80
    0x58046406a0741885400d6400006075001c005200c0074600c01e41103691254500300018091800921041040c8520345201046540700090004083c58405001042d032880d1182c0c2550a482541c2000000c2e000b1028540c1591034030450f2000e940d03440c010208110fa0707079101054115146100ac00c1ca00b0304020f42201500300240d000188410700041415440000d007107029189031064283d01c140e250064010403001c01d07010b01c20f90b03034041482e4000781300c285001c0042c401c000e00200402c51181c9408038603005240420000d40310fa40c94601410320080d40c41c2e0034404c41104140c8103140041c4500d20014096511074000d503401019441c642c80d003941c4901d81500c000200080055102607110720000026a454511716402005652400100c03180400d07c0e0100555190b0030000618030304000307000041e00c81008845010121030f2016480f600c8596560152041c8001280347c0c040ca004140100b0040d40d610190003a4402d0300c070508042c1d0854019070542e0a100900c18401100030300845808 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 363719064 1250 363717814 363717833
    0xd02120f1b01020c0a030c02090a05060306011a160f0b1e0f09030706090c050a0b04080d0e0a180f050601030917030a0b0d050d0f0c050c04020706020702091609050d030804 75
    0x75035144009410650000e02c12454103105103000c1d400100b0046103001035061a003080d60700035000642c1030100c1c0c5880e6000c02d80d11001031044141019a0481c812100e00e08141a10508581c19030821100d50141c00c2044084500013001d580007210940400c10300f02881c441841c8007502c0460400c0d50350b41780e100d111031848000b03200f0320890004008032400150684102260980300e103000d4400c03641084e050042003102030308031000e0b40e14100001d000041c2d0000380c0f016041e4043c40c001319180124008074001e0900d44e48108850b001e14011440b1008054024417943c507648001080240e4441c0011416201c1700c0c2d0340500001510004058035800d49801143c0c000b1507280302240c4080c0b03902c04030720300b050314003420780f130b2070700080f009046640d0b00c040e060002184034038142020701e1240d00e64a0700c9580c1c00306103d11641e400607800c2d0802c030458040d141416002000c1165031f00c1c100e508100c031201e514556000042c201040400d0618117040828115074260740c40c001c3d05d41ea40d6030340c01d088 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 363720314 1250 363719064 363719107
    0x804080a030b0316150f050910022103070e06091003050402190f050a1406040e0601140c061801020c0a2004151509121e080307020d02120f 61
    0x10107444050b001500d4070204088082e041245940d860614500009a41210842c084074010480b44003604001c05a00100344d80448400301d4044d8248290018144e00e04440030205501803400200400170302a030713007c00b45210702010f0300c42c015403012040401516100f141012980402034142c11ba04030381c4030390301a0358060303c00b034a1040c00e41d011400040304880d69600800d101140e5a40c180840d003005003041d0014560a14804541011440000c89a0240d4098502d149070110005110780c1c3c41182541103170544030441071f541d141801d4480d40c0340e0038220390b0320490014450819039814414421218a00000b4001d018003201c10303950070702c1d00e0410180020410ba41500f260410f50b881c0c8c81020600d02c0056000d01e8121319005040340c1c1071406140c4182840403000081004401c1c1103501100b86510100005103044180515540203412170b401038241600481001006d5400190780d41d820805078088640011302e049002035030303200f414072000c2812810701c402d00302c0704c503110400c10a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 363721564 1250 363720314 363720317
    0x1e0c01170a060f080706020705061602090925090509060702030a050c030d0e0a0b07080f040f020102010216260309070e061f020a022707050a05281106070804080a 71
    0x148560b03111010034080105820425141d0800b01701004640c0d010482c08004040c00d480d003d0406030018803001c088a06074401074010001000004c21400c402d0020030004c401005048102144140d2036045842d00d80c0a05140b55140c0004504140c000040d821b100c2e4103103034029850603400000440312a040056900760340d00c030a00c425110b441a5000718501885898000c2c100281c4904029041da880601118240001841071103e4050b2003600784e940684c100f6400e0111184901c0102d00a101d0151f40d043c1503141c501c04803040244101129000315407144142d00b829000c403411441611094038031062507401098100030303001e514103102d80d1004000b054500b1400c407011110b401c80c8510004540140c00c1040030401310301c0c1058030641a15850a04038441d0001c2e59603c85036841c010344000c06000c3d01043c0540356502c00c01c1103a0b030112458800200c1010b41da00059000082ca0000d003001c91422850020446c00029880340706100b16030314440c07144c0b1180c66100803030b07001156020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 363722814 1250 363721564 363721571
    0x218030f060613141306051315020306182502011517030c0703300507150609020d060503100b0319020a150c0615061d0409050703051e0c01170a 63
    0x501380114004010300c292400c0c400800044201c2c50300764110340c0000d10340741c801c00c0c130300c1040c001040c7c2d51600403007007009001c4010382e03c1d11344030700052480e003d40d0500c3e0507559500c0108060603d40510301711342c0070400c491035203460308820810703401c5e10040f02880f0342c0b1078030407801000b24881264000e0f608501843c20ba920704204680b0711818904103030425140680c2c80420040390500d07506490000d100480e00320480c146030700304010102d10842c1006011024244920100368a155000d08010001000c0031592006008451000f80000e8426140709006040c040d0312111014042d454843c10020060700300a80741e1004a204560210016130300600a02c90114117003000c6410700d21061980e4680c0070403e5514602107003507404030521044c80540b0780788100035491300400c086403847c40d505c05503408850184d0100d80100070402010b461842842400024080041100e2004603c1c26695a0200c03502919540e51640c1c440f41c01382c00540710580783d503400042040d00d1504002c00e502c011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 363724064 1250 363722814 363722831
    0xc0117060d02100801030323030a05061219150b03070e090c040906060819110d03050f03040308010f0b0702100f0e12161a1b031204060218030f060613 66
    0x2c1ca4103207803c2090000c18a91030050092580110141e6141498030160b0102111410300e603400354000508070400b055181c0010840954074186035000d09411502218803081c100c1001c944141980c0e2000d0ba01150280b411440c0c1c54860300030f004160b840500140074181c60700e4070030150014000d21101c010302805001d4415541e03140101c0c0c1d40140a00b0001c59181d080c041c00030b0a0020840d1066541c86031460803034000340b0089080202c04a044a0303840e203a40941c10f0550301c0344035016440e05281000410803040642000d44075060b50102c2c50390316245500c4042d005018402c422001c0d42c443c1c0c0005603038400d14880c17082d9014041c0c4900d485520750310440c0104490760003031007005050345c000b403e040c241c0c1c41c4c4004100004080040348030030314284c0c0d40455030303641c40307141c48005070003102005010240707a040003100c1e4403080784100e14000d0314190904400a402210140000c1003600449142138980042e03200800f2141c0d02c080c000ea41c0b2548100305413040103d004804282e201c2d0942e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 363725314 1250 363724064 363724069
    0xf0206040c030f150e28111203040308130f060203040605070209060a0305030d0501170d21090c06020709140c1c0e0a1a0f010819050304050d120906020c0117060d02 72
    0x7040c45d4400404024040d00f0181004c160010842940c6000601701600c3d880011034000164100c3c2200c007503515410b80314140c00c489045202750303000640816000540c078280140103071019022507081a0800174541c1d03c4140407a00c9119620440c400030300103000003000362519041003900644010308240d41196240d40c2c9a06507040881804541e07640c400040002c01c0c0e50300c1381700441030310f0713040540500315a00c1d10240c007425403584400d00d24000c2118044020042d03603c0020030903040382c44031181541e183d00c000d41c1c030030444c000c4940365800c00b800c080c0500c04281526020300d540034140c50030100354204541289003400c00b0070070515280c2a2810b1700a0b014003207102c17600d0260010400e4036069181640c2510000341c500700c43c00f1044070041100c442d0104101c0003849020008151030300f01c90500078074601a5030020755115003c00c505601b00460002030201401903a16110b0780396030b40340340c182e8681c214400d1140c0800c10508201d810b00c5032203040540d12104c018050510300761944c02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 363726564 1250 363725314 363725321
    0x90b0607061a010305061210020c01140f100501020a151e0507051305030609070302120a050d11150c0a0c1506030b010f231011060c0a0f0206040c030f15 67
    0xb00384920150041448a1550b40f600030341e80e12000030f403202e071103400505071015550240110300d00072017680031a14554201c000e4000e180340c40d0000360841c00f142044c40b451034903540152030300060304104c0b070f10000d610350002c50300100840e041580543c0c01c012445101c000341980f100b18800d5041c440d1400c0d6100d501c1413040034010000c070340d61591220540740214058452981125110b41d121204102c285003001030140b0a0300e605582007408070b40f24100742072500d00011001421401403c2184071100d034418a9078005800c4002107034003001101010204d203c0e000c0d250303006044410080c3d44921b60280b1005840940f04180300d04494000507061030440700703150401c613441041d00c401080003000a06241000d0095007541071160312804641d0f12008800c040c1031390045401c4000340305194050200c802c10079850205680c240d1420411a0b5004d9003c00c0d001c20100346002d00d203032905c51000070310510560707020b105821210b0454413010108003108408450303149100c41d043d403c0700c03481d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 363727814 1250 363726564 363726581
    0x70309140f1b04180609030c051506010e1e010e010207090213030210020f070e040819020a0318061b080f190201050112020f040506040e30070309090b060706 69
    0x1c1c0903000c0d214000360207801503030302540e07209600300441504c1c1d181c4000b040c0c20445034802030025845400f403400b90380d401c00c1244050b107240611002000364000180c1103c0c8240c00907616600311401040810980040034040151608002180346802d5409440c1c05541100140112100240c2d0703180107005030790040701054400003446104004500300b001c04a000d411140c0090a00301d071200c8041d6903904a64462041d090a041c804a400d001040c0b04842c000e10303800341c400504015020000e903580350442d508500041401c0030b1090040f1311041c0c45015501d4642e114110b00e26501d4081492600c844410350b81c40c401040003880a030399020050842d035610604140c80710195000290131160168003013015594020022030060340c5070100e907255010101c60003da6905c9280c08134000b042e05c040a01e0f61480344403846501030100902c4440b894418103070382022000e0310fa00150043c02441e0005012805000e0309002000940c1c000d03862905c0c02500d02d50030b1507a5a100c035406e0310b00c000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 363729064 1250 363727814 363727843
    0x11120705010e0c06120f070c06020301091505030706020d140904090c0602100204060503130c0308041d09210c010e100603060e0d0f0e0a0b03040803061804020907030914 74
    0x220409661050144030643c0c890200b00c0360b00d41000c80b100c016640780b00d0000c1c8a8030401354100300041c4d08902907030000b800250400421510fa68540c41540010301032404004c002141070040040c8515001801b9010b6030b00c0c503405040e40e90340a00054402c000d425211103080f400078018001151645e01c90190014041d2001b100300701d140540103401c00d00c00c5120300810600403c01800700c150400c1c100c03900845040c41400e00e001e03250811072625856904002c05803600081c000410314001040054184d03c1680b06002545603190f100d0390310200b401e08c4000720180c1c000d10125054000010f41000a04e00c07001249810f400d03d603072400c0c654550b0302c01d042c00d03076500d000340144801d41c0b1419001d00c0c2504000c14028552480c05402e074800e0501440c1000410f00c41d035000e5844005030750b030041070840f882d03640302d01781703454029469081158550f00030b01c0200c480d000904002e0340b003031340625000b50030071855440340b4400328064100a2010382d100c1ca01289207035004102000105e06c0c07800c51 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 363730314 1250 363729064 363729071
    0x7020f120124061707180807060f0201140406181e060b030a050601050907030f06031a06030a03091206020405060307020c03070f0e0c03060102010608070807090606090e071112070501 80
    0x1003426166a0300e8540c0b00d840058410315109008250300722107190380ea66044401e280d0103603a060811a1000c41c00c03003810a460018440018288100040c1c5e18180e038500d458898220303080301030032400c8644103c0e480140b694280d02290205d03503c0d40c4003841c14103516111500608594540c40e2800001c403408910480b02c60325070605000b03162241d454038140890141c82003070320395119103a0304c09041c00340d00e11400280c0042102c80313020307502511810000300001c0c00419501d080111518914070441512142e003203000851a150104008007400d03803645031070200d14100000400042c403070b0790085601d258201b0000c90305a49140c081d40c85100781c1c2e401442510384460a1605021032a0b00642d0410b440000600668088602d9640c0c484081c1c84100d850740e40e0100107c0c00f6008503401000d140c01047d0001c41d13859008603400f41030340d24491080c008aa80c4400031141981d080c410744181d03400c030501003180c19200d40700701c040e00040d1608541c0101c5814407404450791201c0302c03c850700ea55 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 363731564 1250 363730314 363730331
    0x120a092f0103050a090b041502131202040f18030c05120d05091005070f0c0c05061209070605070206310b0903070b03060a210602040b03011403011104060507020f1201 73
    0x340b43c000d881e4000300d412014019101d19a0380c9555510300548028007680155045a0356042c0580c180c07040840c92031500c400c0c0c071b039450200f00100e00c2400020b07070140d03003008900004804c2c030b0301440d00300b90405134201101d603855480c2110072400c074000845850007544401124014800c0152001c075005810015803400d0a1030498030f40048040d000031294105001c000001c0e8102d2100041d132034640c10541e060800e24504042c00c1d0b91aa0846680100c0215100311050100365806114480c002c0c1140c001a840352400e5a86014000000350701440c1000004003202045d440c034421010a200003c4002c2041d01140300c48a141c0d4000f9582d100b4080f4075080c0d40d01d0200900c00050689600c0d00389982020404100340141900940c2000c079000d0450110038141c44800d428040d4000750210b4031503403650381940312984288514402401c2c1404096910f24061180c0840409000703585450070745002803e0710f00d070300500c0013a0390048071041500d03a580c8558016004210000000080550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 363732814 1250 363731564 363731567
    0x50403150e150106021b04090803040f0209090a0804090c03020d0c02010c020d05180607080c0f0318090f040b09010b04090606060f090e0402060f0f0a0207060e06120a092f01 76
    0x200c202802c110141c60820040124507008a1200e4120015016681264203030343d01141c050002d6201c02011032100100700320612515140c2d54501c103100f11245000303a15040051a0f58840f074440190a064080000308581c2c0d46030340c0045000040c2d81400f5060801c041510002c40d40107000010250b5100c2c40e0388200d540d814004607010141394101a81030200101190042180c07241c401405503000203490814024070800303460b00c10081004981d1320142000310309450350000310544504150b44070882e555440e19144461044188968200751a0b640d5240e072151404080e01404840d5618180300c05251642c2c0903214005010300c6006c146a49440c400511146024181c60100581e1010030700900e11601151900190100c1e4019202d010942c88900380748900c440311039912400246802c850380d004a076200c111615038580c1c81400d0009000c1c8403840c822044d0ba04c00200c00c1000080803a03442e640f0401307400340070b0741807440f01010060080700120b00301034000c2c02c0240004034003801503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 363734064 1250 363732814 363732823
    0x903091701060b070f24020d0c03050c070b060f03071d0c070c0611030f04080f070519051c080a050c07090b0105181909060302150c0706050a050403150e 67
    0x4000300340003080a0b6180045454150140200040c120340200b2059418002107140460400304a01c0c03041c200602407007102402544541d5100c41030605100f403540503980607100385485880d8100c0a10300e00042c3c1c1c0d07200003c04500504140d48140400e5001e87c250700e00f00414005000c182c0c1c500f2201c2c0b450f401c4581c40400c0c000303141c0003000e4010032500002038500307000c45085440d14201056586100100c8600b18000c162201268010200d40018880d500040055803008108241c4019135115010b00c188010b40300c0904c0c6002d100d0380340820060411800c0e45000c44507a003126040618a035480d0507a0390701c04465240050310214100703113603420520800c4010462a1810410625010b0010b4010b024080d400700c1c1c4401c205140c2c03c055201e01800c0c114003040180307484400d5440b07002041c0104040c2c04184c1c090400b80004030150134510f4100c503442265a8024440d561404404407001c2d8424245541003090a000020000390a007d0b40407400c04403110100341e503a00c8034021ba292 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 363735314 1250 363734064 363734099
    0x1b03051803040e07050903010207030c1505270102040b0309030405100f0c20030d12060b0f030105040504020310150611030a170a0e0604050120070b010b1b01090309 72
    0x810002903121504000000708880844504201440041e6a601400d60b528081c00140c9901940000740f00300806600c654400e122510032840381d40e02c40401c900b0a01150340407215a45c2600130010300b000b5180c4040b041d085c0203045000058901a1501c0c421a9242c1047c0c5400a1552011400703015528010b038040c1e548824070329160000c4001950000c0c00190325400140c264075018030303104220080c41c05010f0841c800502291101c8200342c500030003c40075292110042450244040b03100c1c02150121403040d001081140c0c00c603420542004010240604200c2c1e161103a5070302140f00b1207040c06001c8000390040c041014880c40e102c8042c01424035240241300f19041000b044400c81d410a024044010341c00d040c81f415595040020001021505100d00962042c40700308010032005411030b00c441911120404d0f107150160b02c2104450240f540010711a440002c0107018250b40c1101820015104218000e4001d5000290b103084079580e0109074005260108103005854581c02e04040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 363736564 1250 363735314 363735331
    0x6071a06011d1c02030a030801061b080403020f04090f0602030402180c070b040c0902070b090c040b03060c0313060203010806090607050a0228061b0e010306050d02060c0f011b0305 79
    0xc1e2062404011038003102d03851049100c0c400d008806651031410180716002c19501030100c885034001070038080c000450911800000030301d1045040007900520000a060340e030700603142400c00381540e0070000006d00002c100d64000c1c1c1d4440780580800c84451100b64003074020701d001a540c1c2081d0040c03142000c050040f0800200c1900184001e1148860403260800c0e0000710001094503185089003400303038a684060780c0c0324008203010301409803044545008070b15060441d072242e00000244030565640f0020071741d040e0407200000343c40d070307920800442d400780c14400380c0013170030103690b603520308030307042a0854103840d0f10501c100050141c0c10050a50014594205903050101d0080004e40d030344980110b14600c1d4420304100003031201507412004010340d0183c000d00c0130304644400c4241c040d200074030b0400003a034180c880301d00b40c0d4003074030425003500c20103800380c41070481a4003800b0182d8000300c120030541c85441351803840e00d10203100d620701c14080000ea825141c0b00d1258000d0070345001038501d10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 363737814 1250 363736564 363736577
    0x61706010c0b0406050a0f050c040623040e1003020a09020d050a0e030f070f0c090b0108160e010302030c0d05150a0f0e0f0601090815040c080c010f110102040506071a0601 75
    0x800b0032070410840c2c0e03006030b01040201e200d03902c0c000c0103406002d2600a200d04c02e414402440100381c1c1c1c050140054134000c1c3c1c0c4520421420b105030400d4484245c0d0300120303100301084280040c00402040550020b845044211502d6881c1c0c0821909205a0b00c51080365901207000c0c181844a80540fa40100103d002844500f4051b40b20039200c0c4240745940c2181400080c01da030400c61110034545610b9046502c150400c1d40e66500306010b0190001070b035001405100004002d4190120511640302040da03800c2e880052a1005600030b5001800c0c00d08001e800b88201c07032106204e4050b8610030300200c08408400c01180c0188042100650000800c2520500c1c05001100d900c025142d440003041e50031284030303140c4000685680415400c5000c0340c0c01000c071000b00c0b0062600001f40928401d01910b40b142d5030300d14086841e0300180c0d000e140054556a207000c6124032401c000700c0602050000149880c0c1c2c0c0350000f0348941e001d031004503407007444d81c1112800501c04000c1164000d1080c2460b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 363739064 1250 363737814 363737837
    0xe030a0f030c180f090b060c030a0804150905070602011107050a080d06030c0306020c1b090f040804150804060c0201050615071e11091b04060507050c0a06170601 71
    0x103400104031100500800d0394440404102d0303481500031565605840022100c1a82c4951403040d10496034011642518104603448065050000848012850a002442c00c1001c41c003411190b900300640705a0384504452070300e514102d00e911990311218825401442c2c8246018406425620040909010602e041c4454400308001041c2c407c0301543c86200306544958215020008140396080075103001d642c0e0001204004265000300b80c0951208119144110040400c00412a181103655004001803010490a01d50039071a070b9005407041c001141460f4440303051844603c0100041d400050805041c4014009036205003010342d40c40c0c1c4020b0006203030ac1d0300860104404001c0324601b21800240c0324041c811403142c100512600700c0041d1884813000d05211800990f1030110b244106849008101c912180d00501401e5500c01c2000d00e040519241054541d600142c6042d55a401403d034140310710307602d2070260301c042c140544450440f040c40494000c4030410042116040c400c168221 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 363740314 1250 363739064 363739067
    0xe0f0d02120a03020c19030504140603010f052101020a0918020406020616031104032f090c0702040f060b030115030c020618100c0e0312160f1a01080706030e030a 71
    0x84410b116401e04001d40d459040079141c0d46407150940b041c41e05189640c40340c8040540c05801401115981c040c4c8141c051505820821039120a01c034070b0b414001d52030000c004a0230000c0303a88004403032650120241c2d1800c040c0c61400c1e83d000c811300340c00040d0710082c140aa200d80d0304009005402e4076004604040c18124040d40e00c05001d89508400c081c1d800c51550414425003000044600a2540347d454030380d64603110800400c00100811900310320718030b15200e084100e01c1d60b0140c110061004c801d0b601c5e41280407015a0000a060f600661540200e683e03106081c0a258010441104030729941e615004000403207498554000302010309001441000340d600160103504030f000244107c1c0680301a0101d00d00d0007200c011004a41070414044002007034005a2605101c542503040e40d070040d010041e021040e21480121540c4004004d08140c0410006100300c80414030519848102641c402102e5580300c200340d00c42c1c03515030f002807010f0085c9030b03250055401c030000c0c501c02181003c2d11181c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 363741564 1250 363740314 363740317
    0x60a0602190609050f070b030f0606090315070e03060903030103031701060806060a1e0f110a0f0b09070512010f0b090103150e010b041d1204030807150f0e0f0d0212 72
    0x10142c03070252500c0c0c4441c144242806040c80c01c03801c00703088404565840710500c035682c20031240030f01e16110b20b4001541505050048031404800140a1702540d118441e40040780080940114108074110f500307604282c40c04c02256000380c4c0c20340300035500d0b5031440c5401849000030500d240b4100e84008010010543c000c8003413074011108599403916601840e0382126940c00c510125181c2014101040c0b548035000f50880e00c0c8400300740e2b40c00c1418007645101580d42da00307055004100310750b070364140e10114669074000f07074000b01c042040d03460031551040000e00155031014824280d9644070b0114000c8a0144140003151405443d410459031540c0c80b0100c440706507034520a0256114030307032552400e070b0a6028410550380140100002000803582c20005040804840c00034170955910700024900001982c04403031340316460a18003030307265503020300d84480d030f042c0d1502c00d9403600d01c4c1108001c0c41b03016012550311900c0003840550a607880c22850504071603640402d40d00300090380c000890070b000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 363742814 1250 363741564 363741613
    0x3010606140313020105120f04030807021216020a2d050315060405090a0b150111071203050f160812360a050613120206070e0f13090b060a0602 63
    0x14041520300111300050300e0500c50002862540341c20f01040000c41c028050440380920f0007a9074071059996105410b03070b0744508001245059040c1805030042c07011004515600513031000d4640005956544440d0f400e085800006070a00c0101c0c540c6a104000e4014031440100411401840081d2104500d209103400140a0070f01440c0c0303450014110420030405032a00c144c2c401d41d80c16091030030a005203070b54496004464001a08201c030762b400d16600092110548040c004020b4140b0700c99501940d0035072010201e60f030104000d01402e895030401c00e900c400e0039800303580107684d02d076409500c002c90700c1c10081c944400640d214840d10503c00005003a0300c42d280496030700b00b80c425082d805c03252510208402c01051071203804104201500380c444c011459a11071802c9641503091620241d032182d10443d5048002046802c0141c56481c2083c400f000d9500f0181c2854180701b00180c1c0d81d0155943c01c04159040a6844140b100c64100661908008d0000784060417850300c04039441b5002d01e082f803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 363744064 1250 363742814 363742831
    0xb010905060d091506080d08090601060c050a0503040803031e04030e0405061201020c030904060f0303020a121110090209070c020603011a0c030a03061a0336010c050306030106061403 80
    0x214400c260811641e010081071034000d00300b144c1201540001e200070b0b0034280285012401158000d09406001e5643e80340141d0070310001d400e0507802d1810803203441c00d011006584902c182040080441c1c410300040014005601c0a0b640c1c03881c204040300c801a24803d80302d0014a981d40410010981c44080300e4a500000c40740400c154940c040003690100c11010198240c0d4800600340c2c0c0a0710b8008020700140d14241c50a2000b6581c5818010445040b0b2001a0160f0414440e0200060ba02da42e2240019924140003543c0c4a03181d0409103000b1001000310041c550755071072101549002c100f0903503c01c0c400c3ca48100005d8099000c55078902042c4260586400d02c02c440c2440e6000c4207064078a884880c404480d203591242400030040c22a900c603020040040071110002c041418003140d2080d0080028180301c41003d000c443c98000032400320803040030071440c3d049803014007030048601e0000241d88071500c1e4201203041500311000d6511100c18041688084104015413009480d40460306 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 363745314 1250 363744064 363744067
    0x106030b0f041a1503010f09020f0306010303050d0c03020d050114181003020d08070605040b04141923160801050a090c0b0c07120c140108040206180f09091f0b01090506 74
    0x104c2d10300350304811454904681c5542001c403111a1400ea507800090315500031142d03901d084006009040e22542d081c00098002402000852015101501301c1c5d0030074030340307486c006150000b0007040c181110000c4c1c012500003001c503d1065818500458851b41503003680c0c031061107038100418900340c5150399210007030003002445166010710001c07006807000745800400600c0306182501c1c21950101c011101141d0340b0f0038500c5021007415001604483c240801580c0200c170017555150f4500c00e151145c42031840c2052030b2104414403006004890680308000881d849070390a0002e01030a60304002d0941813905c2c9001000c41c04a040c0c542108101d4000c001c106a8030111801c0303007800c1c0011034110b00c40b42d10041c01500100413070003071031004440c40e291080b0314054100004580c19403007a02e000e50f0052052001c90581e0145400c010b44181d00105103080300d20301c6001088101d90200c80c11074994100c00140c4100c0055000109560140d941c1c08100c5a034492001070410901402064000c410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 363746564 1250 363745314 363745321
    0x30402010f032f0706020f0304120201061809050f0a080a0e090c0304032d0203070c090b09010504151806050f0105040308070b0c09060c07050a0906121205070210020106030b0f041a 79
    0x80300804c41d41d446070051025540e0310321240044099a0041d42d040318080014650070180910601c40d10b001c0e42c0c00b90740b2400c210740c10001c150020f440c0b041c0055030030b4040c4028216140b0b008000f4549418403c001c0552510040400601150004100c00d800360741e540b0108060840680308a0354001d40c542000301c008450802c00c0c141030030419042050f140c00000da40d43c0d040d0340000207055454404c0b41e400b00f07040d854190754010743c0c440c07500590300306c1820b800510071850300e80c0080817030100030100b100240b5500c003901d8240700d141d039030001d1859603900401c0c860350421b1440c000c0086800c4c01c0041c07a061469417444014460004043c003d207032050041071004c51444101c0e41c1a01c5c0080000b41c8498907d032005813201e10320702c512445100072940c0021078031a280640c0c1d04540500da00b210f1440400c1d12000c0401e080a560b07541000020440d1a0050351102e05440f6101741c03583c00090f003036080d4900035200e1030001e0008255214502e00b0440000d604024911000c1035240100b0300301e84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 363747814 1250 363746564 363746651
    0xf050102040e071101060f0e0a0b13020a18050a0302090f09010603021003020c0c0a060c0305091309080c07080c091f0f0b090901090e2508070b030402010f03 69
    0x80c40c0c10442c18250070a051186060b8840c03800e10000321540300810a8907503d481c00f10148440d84194150725403114002014100c580c0c2c08141c524401400041342d000110810500303c2c2e012200e031401184031980d0300d40705441c4042080e805090b09880f4003622500b55000641600401400c4c04080d142c20000941450702c00c0d000030000b598003514122050340402000360180d0410314a0018510a4031005401c030f150041c4e0a4044808a485080d0408119101105c056000d8010700d0b410403c41118040340301d40a125076041140540308007a01c581005010508107510755225001980c44001c00003074075038617107140c1034000780385c40321a02c00082414240e036680e0a0542c8100d4208840500001f00e07070920702c00034943c0c400115800b0009a88544420b001c030341c904400700b50641e122074800b4070782c9240d020320003d01e8150840c00c8c269041d903800245182050542005024600210a0000b1541c10481c441c1421146040a11034004000b400c3c52004240b192000054150b00c00c65080c2507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 363749064 1250 363747814 363747817
    0x60f09080708030f070c0b0318010b0916050c071509031a040201092c0a1b0207030b010b1b0307080706060e041203050604020c031210050604060f05070c0503010504050a020f040c0206040f050102 85
    0x14850601d2248c0c4a01e0040700c03000840c054018060142e508020840e002032401055082c480c0c03130320503000800614103600c06c42c0c076038008a0056074588109800810006260320741416808101e540e0583d85078103500d0a030fa00385542c5e42c0034411400c510018000142c1e0409a0392064482014201190208034a40c0500081400c2c0e04983c002401c1414440d41d26425088514602258241d03404803000d90f640490391410548000b41401c0c03d0040140301d000d290000802032a40b01076120444500c1c400f01399411a130014a0440b220100007819108000d50750040f4401050b03031042e003401c103181a8032200300c1c0b15135041820041569500000350180d07034550540d00e20450020449884001e003521440c0010810794a24288001c034290000e01494848100d80581d65595100c014000c081e45094480d9048020110b41e44542c804020507592000d21034039214500410080654414a006010401801c0e841d40b5000d142058000b4883c241c0018425401c50b50044103c2d280b50301c18100715009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 363750314 1250 363749064 363749069
    0x516020402120f0a0b0f090c0304060605150c0c0409020d033b0a0e091b03030d050703021e040b0405011206030f03080405010e060115050307020a050106060f09080708030f070c 77
    0x480040b142405421100903000381c1c40703030710008000c0280034115800c02a45440040001f94406620800108035060680c080c6411501c2550007042c815141c0c000511014840303c0101d03080071011943c044480c0080000070315110082c1c90400124035560081000c1400002b400344c1484500e04910703031410310907030b03c004458601484084825a0100d0311105442602c1401d0384288802e15010880f5040701e4601402016200c0061040c4a6a9001060f50802980ca03943e03250105001200342c040c060b015103032103001c1d1a500142d864900381c45085000d07407030441c020401e80c4140000e001d5810381208607010b0317945c06d090035603190445140002c080d041c00d40004198170b145c3d8485400301500018000c2c00389100710000c1c0a1081e48180c0155a04824401c80d802c01e8180c1001c0d074070050182e0011900100f04d403060b1140e00245844407405d4800a902c40340006040c2501d1681d0594041e0800d40580708010251030414501110741c0d81d01c0c012500b4048243c640000e841c0d0801131401400d000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 363751564 1250 363750314 363750337
    0xb030f1906090b0126040212010f0c03020901030e341502060108060f0c0702010f030e0a051b0409050d0806180a02040905090d09030311010902090c0901030e0d0516020402 75
    0x40ba2116005400b07004109043c3c0c0c041805020098000d40c600140d081400103004404006582c4940030060000140480d8420315584e0382e1054100c201d860107007000001c040e03100503035124090070004040703507202c2d00c4110060304108240071030381201c02da8508403404020101c5c10302007101d40c4400c0c41100b031030b8030070002c17100483c03501e0344141d4002c16441d04031a0305c28103981c85a918004042d002503c2110880085c85003000b5040066018001d5015904070030702c1c000407102c0200028a04c0c000c0300060503a4a0380c040306504c0544480501d031011040c10564081c803c0d04d400342d48a80e5200d80342500322041c852302400085070350322030740703242d1030956170300c040000c400d040210081d00258820300640400d03d00b08000070301240700c0041e181020451a07a50302d1405440c60b217045500803650809525a55203a1800070003603030ba03580d45030317014040512045640700103840c00502190000300d009185504560203580d01c050700030090b07071252615403241080e00945880020001e101d10b500040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 363752814 1250 363751564 363751571
    0x10e031204080a21050a05031003021c06050c090604030209040218040327120b06010509030d080a0c1e260906070e061606090f0c060512100b030f19 65
    0x740d07068000343c0011024082c0a800c440b4024048101016903c802d00f1440843c0c0e0811103442d682e846503000b0f6601c8054809c0100c295a101e50000b0000d099681d411301c9404800080d40061040c18820960888030102810b8603140050000c61214015484060701c9200d032003001130250b4540003920750603980150110580d920b001d180103040c05091005c0116414122807000e007000c0c814152050680b099421101c0e2520410798070040b003218010320450410200307108403802c03510108440c25100c4580d480d00000c074900180403404440c5010740c91800c10094225000550130174a044034110348403490000c00032908004540484010003c090540d402210100050010042009401404280c2e10110042c008804000c2c0c1c0703000f19840800241c0865400100041580e80a20300052081404c24100b843c80d444d41081040c0560050f0302081d4000340340403001a40c0541c4075407080019580c03021013410280801e10500005007030030600092003000ca00401e80302c445000c20b8054442060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 363754064 1250 363752814 363752819
    0x18061b05010b09090f0f06060a270608010603020f041505130e150105011803080306040c111c080f0c0403020103020903012c0d0e062b020a0314180a02010e031204 71
    0x4170794910380d9041a8586001c1c0c14040781c01000301040c0140502d40041840041c1401d25800d01c05200c00000c0014258807004140c045404040c09035034000c00680340000740313482ca50300500c907500c00703144c071032610451400c103403034112405400c90001a9501500e00000b09104000508000c104070f4010080c984544401c00c054401419003ca059038020790b02e0044443d50511110891240c9000050040c03000b440000d0103410a40c2c010450701186141c52298004005442824140720112811140c042c140701810300c0b541202a01d84c01800c48482500c1d2460010004a4540114040241010340000d034140c1c081e6025002051811540002e5403007000300c04e01e48a50050740d2800000040c050136240d211854000c98020441036005400240303811800880545410100e807207108003a0ba039030305041061a21803010f84807111591710b00043c9003c1e44292001c01c16001410100c0e60802c80200122060380400c0861020b070342820030040000e21100028107140035485251a50031010400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 363755314 1250 363754064 363754081
    0x51c1103010911070b040b13140c01021204120303020906190e03010b0f0d08032d0105031905031c021605030d050703061d0a0b0d030201020a18061b05010b09 69
    0x294121902c08404001c500f01d552500c150a0180c02e0014186900140008001c41d0300781c00119030102407044c032507248100c541e0302e803903030400709130746007071861784020308008503540c04012101032241b101c0302180c189803900c880540e170800d100e0030040130944c0200e018482a1504415199035a030581595559607625160041005907141401c5100e982081e8000e101404c0c0a80d500c07141d2800a0104130842125407521031903540084c18140f0045d02c0c000442c41128848280e00101503140306440c6000d516120405280109241c030081035001d00c01894000254004103c510483d4055120811900e0004200c0024001c444030085a142e102c1d041e0302c01c00c14044020300c000628804100616151900110708a0f420ac1c0140c080c5200c0c070460080e00010040c0b01c03035174080c0803108081111420341c8041040f8801190084001d44c4d000306402c1034954100400c480c8005038080101c401d149481d000a0404800302060001105500c81d20340600000b904803840400002c1e00c241010304100f41e0b0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 363756564 1250 363755314 363755317
    0x90c0509060703030b13020f0708070809030109120e0306161b1401060303120b030607051c1a1e060a0f02070807062304050117070c231002030610051c11 67
    0x1030b030601c038074042e240c0042c0f1114144252000e003a2148023443c1480d901351740ea0340c440c0d8001d076016200180c05100c1070358543d42c03d000e41034441c1d100e000075240241000c20080c0c0000c651103600c61094119404121104150000c8403940b24074514100f010303e0105010341148641d0b109010f080a0003d664010f80703044150071140807207103c0c3d1340d007905000c1c03140954401c850640c03247c558550090700100e84a03074801c2e005401a810000344040324000c140701241c080f2480c0c440460541850b1210708011031600c81496840f9480f0700140460b061040350000e0018824080c9800c1448155070307070400505d10030881100982010713801c4848107502d90501405291100322080c0d00c00304a58040b00121a141c3c0981d812a13106843c0d82c00448490441d040884c03000078102d82c200030100501c5008101040c4250701c45d402074440c480280070421110328249450ba0a03034082140c0100140a119112408024840503d51424540300c00b85220b1150f450182202410080c03400c01c1c00100d8010381240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 363757814 1250 363756564 363756581
    0xb0a0233010803040521030703081b0d0c0f02010b010801030b0a02130902040314070308040e250f030e0705030a0213060e0408090a0f06051c110f04080105010803030907090c050906070303 82
    0x1c620b080010546c0004151090203030050860a40083c4104000079000b0f0840b1034010200711180420058604602da0303003504801c401f825819100d45160340300d56005500343c410390055100074018414600000fa2600f4010710009051401b107000103208c490070307907066902c0c0c0012079062529903680c90308064043e411030b02041c1c0b020424034607801a003440c00145c1c0c904503584000001c1c141380c5081e038000c140c040c006000b551050f100f011130b001890192042010341540907102c128500054040080803101c061611404131f6002d010705200c80d0350009010f80a9603411500000c0b0400402101030152495502641c00c01f91214144403c102511014064102e402d0720305403801a6a203a603910200400d104007400305408200050f4000300d000d803003c554000590000ca001c642c2404c01d494103070300c42c1c8101c0d0f01d000004101480940b07404c1c0038560040200c000114210b09240880ca0b48030303403641c440c40e000aa48c8056403519903010704199200008010300c41a04c560380f90070054050100708 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 363759064 1250 363757814 363757819
    0x20705090604050708070c05031606050f061903080f07051c1d0a09200d06050307050a0501021507021f090311010c090501030b010c02040510030203070b0a02330108030405 75
    0x1000040c0e01c0c0c10b1030f1080e0742c4034585940d039880c03180d180c1100c29036031000d07a008150360601041041321442c0c181c0c0c0a030044420b1091034006400d190940b205070704003101402c541d116000784120364080d07040456500054035001801141d0344d03c4d41e6030300d41c1e9407481400c000404070302031070b0071000401e038104c074101c5070004958450b0102d07007080c960b481030b1494032612855800202c071b680520120300940d20000e5403070004201c031a110501d0b16101d41d120303081000e0300380c10b04d501d030300d002c3c000c81c1403d100c2040100000d03100307241c2c0581010b0010751034055840101c2c0441d4020350008014500c00c01c980c10a03c0d0604410032804240540f810b03000d8628100d0550100d1402044154140c405100c1ca102001107580c8114241d82080c00440107060400710036030420410070304020250b502d522690b0f0292a00508030640a891841403500f8907800760711202d08088180003001c02540c000c40d0404100b543c0149050041e0f0801c00c02c000c8414800601020090b4014008580b15900000078000d81d03a04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 363760314 1250 363759064 363759079
    0x10e060f0f010501020d12020d051602070503160b070c090203043f14121303020c010f090e04060f0f060806100303090e06031207060221090607080603030f0a020705 72
    0x1c0c04000102481d0a114003070040c0d03c03120780c034404140708407009040320760f03103481c0585007a024601c41c005840c0245c48440c40140184202d0752016010401e9100070001a0082c010403c6483c0c0381c81e0744160300e4420381110310000280c039010405107840365000b03881c0c048004c640303e0606041c100c2c2e0740401210211400c102041008402141d0900c0b81441501e81ca0a0020b40190303600084601c907458001e050300c2c00d40240030402c62403042d841e0b19840796241c0e00007550f411030581802070fd08032807000440d0501110041c0a0085070780a04100c0694010f8100289544c5a0b494118024508195080d0840d072030642c1084429525402010880700c41c04101c03030075902d45c03c020203d1410284801030105422100401900301240c48581e40044014190750910103440030b40041d44e40100422a0b0040d80018102004404204006204180c42d500a261440d00c0e440c0709542d200040d05d03181c10300428a000418903a0104111480540c0b0106999266045944041d5850310704d80500c600c40c03e030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 363761564 1250 363760314 363760321
    0x605060f0906040c091a0c070614040b1303150b19080a020d06060e01030f120f14070501060915030209010504111b0c060304110f1206010504150305010e060f 69
    0x1031101819812140082002106454a10400000704141a101ca040c4442644000f441d05052065405400600b903260f681e0707420340c1c41e415400c044c40c136002903062011001e4202940b42a040a640079501b090b403100f5510340983c0c1d02c0508280e125440201070300402082420032802d603400001c0098015600c6440c03540400608518540b0240144d000d1544000c1414000d85072507602e81c100076004010009101c1d80700c6400c1111130100b40c00607a0180c413010b030300b00104149100507510607200c40c0381c40c07440e91444580c000d11a801034402c0c292002800304548007400b03070070342c0258001d00315000104801c2c03030051010389107034801e48000d911910284000080310304050140c55032030b80d00d29001514086460b07040c1302d00785a114659003c02c3c8190840d270309260300c52000440c051401410030101440302d1b8410021a8041c90540c3d41c0103403e5800854041900001ca082c1074900c11100481c50521200200c200358205600c00b800c0d660074408004144840444d210740a01e411100300303c882e0741c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 363762814 1250 363761564 363761569
    0x80c2a01030b0d0506071409060a11190209060409142a010c0809190e190c0c0f0b0c09060d050402010f180501050d0207080c0d080a0608071502010b060a0c060506 71
    0x11901d010182040c0c005c000043e880c144520341800140d26a0302209080035441d03400f09001d40c00000e20704c0c001c0f0728207018074901400d0810106941620004810071048074550104a032600c2c0500264060390710340088208120004168450882c500c0003200c0b4007440c0060380170441b1009110035400050314013440142035202d01e0207551a00d412076040c0d807a0420244c14401c009110007081d04802d003404502180800c1d5003d0300600940d09100094480c1461900781030840d071240d440c200c03e101401030090005218111405051504200950310766914540d008109125910300f0503401f690024040d450b001c0d195011a000350b0003a41c411b0944600a801610304025121210586404d10341c010409580305100504640c202554054180501d50351403100a400c117402d50a00351300800c141d01641307a840b052140d44001100340a04c0f8041c03900e82c4194490601e4041c150040d5045a40c0c141441c2c004d41114806032401b0780156a06c48503400001c20300d1140c10001c40d413a1f1f040101007a902d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 363764064 1250 363762814 363762829
    0x181101090b0c0601290a05030103170403050d1206080f1b0103050408190c021e0112051311030c03071806060f080f070c0804090903200703080c2a01030b 67
    0x201c0c00b10042c100d82c0d0900803410b0589003002c008a50a0400c042100c0541c0142c00140c801803500c0c0d1500703038a950440c504042000340fa0f06000c810608180420004100001042041d8500904100250403840039010004d03041d590004106441002c074115400c800004403014481450b20b0788002d40c0001c0c1c2c00440540b1802d44014000072000e20103017891107000002c5804180700c0b170a0400c4131030055408246100d5007400c24090000ca109800c1619580144803100c1d60b041148080290307107421640340942d81c201800152141c10005413500013518100f150035080b0400600f00c030700c0596600c00703000d6480a0410307441c9644d4104140081c080b8042c0d0500781000c3c1d03294541040d25690756001c0350a0031401400707202005416843c650200b141c26008001400400340d010482000504010b40504030841070886040b070300d040380b1402c0340d5000c9000d030700752548121800d41d620001030489140100c0040580f800001d00905ea8044880c0ca48440107022001c0e01c080c41210015001c00a21 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 363765314 1250 363764064 363764077
    0xf091403180306040203061b0408070b09090a0902060d0f02040e0c0c07060c1205090103090f05011b0e030c04110c060a05040218040b16050403050307080706060b070302030a08040204181101090b 85
    0x141c0c444004100c856007804508e8010f0801100c0e40c0341000e80d941c2c00303149041510340c080ca556090004a8100605000c09456803180059100703205031502c950101d001c0d40b0444136075401c80c90b554904100038241c070350100c80c011301555220202d81d007007410650341140d0040d007118140388501400082c400340109070345100303190428050003d03500d40e00e0302501c56500042c0c0c058101542e40d510840003501c0d061803018898010300c0001040310b0002010b0a0300c103049a907890a10600521200495500146118804905841c08600404174400031400c0e405000c54648040c00b5880c10400e0007a81a40070798816030084034210000b0040c01585058548241d401800caa622240080c3c8e40c100c180340d0000101040746002890301c0d0741ca4841354215046040111510200012181c040c403801c0d015110240800070758140c07900b125994003940c4c902c111480302050000b120002404d5517200d900c200c003620020525581d0b01c2e000b0345403a100b08141503001a02048400c00086903641401d0240c0d4403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 363766564 1250 363765314 363765319
    0xf07080d020d0e0601211a09010e0d052a1501080303042009040f080d090302070806060612010618050a080c031c020d0e061b03030403090510120f0914031803060402 72
    0x42d051b5204190403c8600117440560b0742515000a03142c60407100745900384035403e520f0000032a0300c0501003041c01d2034007101d00c070010414248584082c0600c140e00310240c01c0d40348040d8247c2001c01d400c0e81c6007088144400c09000c0c07040350300001a00d43c0044025880350b40b0a0784008ac08800c070540c2610005580c3e00e016801110b03040c0020000303284941c8015007540241a030030b05005881c11010169080108100d00580040350b080102540400189800c000e00300c3c0c2880c10306068500e1340124100c1442844100814100d0182e01d8495458200c405854050007402d003aa4443c1070b425520302c8510b014501a208024071148124015212010280c460354090441400030f0002100d0030048406a90362000701000321020407203a05040414002c485005035440e031802d4103024010300d507161f11490041d46110551906103901050220001c80b668100184801c258000c00c0b00402060a0041140380c8068020080c01d00c004041c00e40c5014034039244101c1d0200310189501c400d0160380094 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 363767814 1250 363766564 363766589
    0x20c1018030c0b07020a0b10052103071b08010609050106120510050f03030c030304060506090f0f1308070b0c0414030c060a0e030f0615010305090c10050f07080d020d0e0601 76
    0x9000403100302002c1c1e0050500e1040f85c6c12928151141e007480d400c00c4d903940810048201c0d040007a42018a07041c0138004000885011075022000d0954480c483c16000500480402c10764403040107144003410050000303480208803142d00e0b404d00c0001800203000d08004562401100c0e4021903441c012548112022030346401c45520703150034820040618039695078580424086598006000c00c040c40c4034600420001c200e07402d104052004c80c00b005414030310800b08884c204074014100303000c126041401c421404c0d4007031030380782422040c0d030160500042c144c1d040c48040c4150800294044c00540758940b461115100e03e02080642e2803080e03c15160f00010144541c00e512401500ca10760103082c045d05662040c03202070f0480d41081c404580d40600b007400f650811106503414031850741e11080c5c9d00003c2c103401c0041e1002072415240d0b0410f000402500099440750103c04600b42e91415034048042902c40c140024000007940000e002402c4581c5400780013000007800080f5241201c407480c0d401c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 363769064 1250 363767814 363767837
    0x1406030f0d030b012706080f09070e0402010509180a0f02090d06020306040902180f0c0a0c020d02040f0e010504050c03191509020604180b030d0504050409050f01020c101803 76
    0x307501030201c4030720b15414011004002c00505203044031541d846503000c5000d81c89141090341c003605039003000c8c0c900c14000f0041c00400003071500010315002582e200c00c00420071a911480100c6e84c0d0700c5000c4586030089051165941400d0003042d10b980180801c1400703004a100c0818008205d01840092503441401c64003c0310115646034021034120001a10106218920f6000301c0d500000c0031410042c2101c0d6402000a9407440b104170b55040403c11039454600700060364000c010781e61809002e407040c000707c000ca00465407140d000a40f0745c6501001403115800844c20140201021030301a943d40c0690a099411403038042030054180b0540d034100b1440f40b01648685c140420186401458699598039420150340e03103402034802042c00c441c0700a40204035449140c1a5070700101c20b80d010394800d48a24604039017003c265030503a0400c1d01c0009a850b11410078138a00312000454030455480003c450b14003041c081414502528500030620011910316482030b4000d0303031740340d0240c005010078112 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 363770314 1250 363769064 363769067
    0x20091302130f0e070201050c03060a03201c110a0303140c120f0a1d0109050d02030c270115020a060c1701180e06010515090d0b01091406030f0d 63
    0x76100d1001c141da146184562a5500020041c045030448850040610200710340d095090240da41d01140c03201c0c0d21070035418904c012984408172070000400c0d0990705020b5001603200740e110030402d0f0728010004907900445070b242080c03503400841d065401206040d00900a41400d210041c12240e2560b01c090100080300442040c541118440c002d19000741000c640c014444000504034000701c0c404080d54900466402400e1030910700c0010649061114000c5100c0e83c04c2030110007100c90a44480e204050300d840000d0901c13040d010516801132100140b100c02c040102d448644502c940f5400014590700c529400e00291764000c4000e006038046141000040d182e6003001c0200b40c01c0d0b0800ca004405000b006c0030036108260051954000c0c42201000740d4a428001d03e0015440307080033b011254185404202d0382c0e886518889403500c1c00040b0f000c60364070780705503134110503420121341c0b8910b50f11440603c014202011190142442c5200800c200d45004914804c218a03808010038458298900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 363771564 1250 363770314 363770317
    0x91f030b0109110903210f1c0605030c010f03020a0e0904210207080703120909020307080702120a05160804080a1203050a0e0606130605040e07090c090b0403060510170120091302 78
    0x3d691140b1009004900c9108400c0c13016118120a00030323050950314103132034000100c80711030b4001840780d800b442ca0000030340d0304900c104811022502e00907030b07078100d040026164036040c440c546400c03503003090410084c0011403048485200e41d02d84000c80050104808070307690511401481c405030004802040080c5114a00721041480390400160050f92240c850080303802c00ca41d2040824150810042107030b50600c1144150803140083c1d909000c8144002010b500604088209031100a080541071103002c100b641c0043c0016800c6901c03103c1a0b141a4174405540301c03481e0082400c1c140410203402040c010301000e20782810007840b0300e070b80e25030402542508041c22040c19555520300810540c60314040e4440e4041844020401c5924240c200d100b01da1440240204226440209202c40495a8200c03800c881e000440410380d901c4041050954580300d611403c0040c00a28079207a82c1d0a0642042c080400c04000940014948100005a87c800d0741407080d407140e1041c04041a0045960 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 363772814 1250 363771564 363771613
    0xb0103060305060106230304060b1003020a020c060c16030c031505010e060105030403090302043801051c110301171b010806011b08070f050d030204050f091f030b0109110903 76
    0x81120480390031060b18682a5209823002d58039251200101c84d40c0d41002d40b051070750a0820710f070861601c050108025121250842c90621802d800240032038011000c2017418180203441d07c00039003030b5907213141c0034156080601c02141c80006100d8074000340001880307018100c07081d4018003816940c401c40112055803004004500707101101c1c1010001d40c03220321400091404080d01c504400c1003c1240000205001400c401c0658003c8a8400b0076640300d41655400c81010030007815130302d20640741001809040507400701e0142c010000051106052628060041402064500c001c2d00074051901004501156030702140c2244003080306544980c140b8070340ca0403031428500c114862a03480d81c031140c0c0b040609440f0501c03141220401d1102c00e020800394080e060a08602c0c180c504000719060415042d5154481c1088d500012152524010b001070812030382c2c2d206681250b100d16041e12448030a0041501c814545004030b68651408000c407640780c81c000b001070080800300216510301d80c4101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 363774064 1250 363772814 363772847
    0x1021e0a0507051b01140c07060c0c08010c03020a11060402100e15160b06010206130f060e0609150a1413080702100c0218040f0b090c0a06050d0b0103060305060106 72
    0x2c200180100348140102e0a0025136000c013180781c0c43c0e005000410f011030a6000c0903100c0c00410264442d0f490001d80002100d0441c107013001c03050a1403c214050740596440300300a9403d203281e50366410ba05a008141d00d450304e49a003891080400001c0d550307450216130003500045541d20903020741c0e008402c80051080010010444c121941c038000e0419001600b40d80e91038041500f14004210b90540d0541d8072140a10040c103047c9800000702101c0c40d00c200300034107c0300400c44041c0601c40c0381c0c5c01000b5908084012501e030b90600b1001140e41c3c1805980c80e0241091140200c0c0030706280b402020341c42400e0350000301c0c054446450000f0b0002442c1c03801c0742d03041c804200740401600d512440c03005001c0c00e1f03100e99890003113a005004900311050002c030201000ea40c104000030702401141441e0316000f10300c2c03080e0307540d4a10205292030b01150352690700c038400940c00100320b5070100041c02c4038a0302500034009042c4040c0154162003217800002d00c030ba0031260050112622806090081e141d80323 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 363775314 1250 363774064 363774067
    0x1d04020a0503010c0305010906080307020105300903090118140402180913060f0c0c0303180b090a030908010203160c151514010212030115020f060a150801021e0a05 72
    0x1201c0000e400c40301070081281c082074a40004100c0b41040d44141d400405541024500d00406640002d14900c1010841d56640300301c1000d0030011213050210081d2144040c800070a6404c16641c41941c9812401e5903d0000c2c0501e4040b8201002c200d034008201ca08080646861038008410003010f0740025813034000701310840080c2200769540580d45402018448041d0080c100c5500701403055800c140b018141c0d580c02c29486030101541301100101803a0075250025070b00085142041d860140d0a0b000b801c000d40702028440e0101010412480c20ba119889224040f9600c030100c41c21707800103c811141030580c060603029994081c00501d1403451140040c80070796203241c4000e000300d4102001220403055103010500c0300302505030303014006031400d000400d01c3c8480303c0354942c2144814001c0190a02030480c0241005000300708041042c200070007500c10514158280741c008010b01d90340c14502107100c0c00b000801113018802c43e07404103511140200e05805003131900d46694003600680c1c041050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 363776564 1250 363775314 363775319
    0x1509150f050732070b04030b090a0c090c110f060402090709090501090b0f03011406040c0c02090f0901140c0307080c070f03020706120b06090f040b0a090c0f091d04020a 74
    0x7842c01c40ba10340c0011000c120f2940c1803c0c400080c0104035070608091030f0380645400d0101c0a14001039504403a4000310307207201036458200c3c640c1030540e551801049005a07010101c2d00c000345821100701c01c555903940c0c0a40b91007105049039920200340c20f8840c01e41001c1e010401508190402a03805080e605218103204e640e107001201f00d8a00768030011006a0b59003a010040c64040c800c0c82c00a07600310000d1003401d03a0005074030b10400001d00b4441c4915910f540200d10310340503200401006070000e102030070030f1500683c81181500d040303480080325413802001e402070380c2c0b501003a43d014140c40e0a40303c3c01d599400c18181c2d1300d100e0160103029000004d22160380044e14905003500d8580c442e50103461194a0716070007402c00582402d0030001070b8108030764080141c54aa00340d68114500712144444c08510401103402880e010068581007006c00300003080c9041c00750080040c3c201d49548298105411034070480e09100d003030085541d910b42d4400c849140000c04e200d16600070340020f081c48203459 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 363777814 1250 363776564 363776573
    0x50d020303091f0206010605272805040c0206042a050a120c0f05060d050c091f1e120b0f190503160f030807080906070c1509150f0507 59
    0x10f00300700d02a160039100c80c0448103140d040c03040c1401492541029810001280c601010f4400c43c0403100b41b0041d00a020600300e991500103d0103001010411040c181c0f40082c2c1500c0858020300456001e00d09008540c42c1c0b4a20024480d0f1003260050030003415a841100340054000c2d901ca006041c6010842004c516641c0d408403070401400480c0b58240d42076200c0c9800070641a456001403d180b01c0508108503e40302c040468000900242c00041c07136684441c4143c3d10fa0064820341e41c1c0040301c0b8604007001001144840282c9a180d0701c40c002c4080c2c000070000003e915200d54840000c07201c8010840350455500050217250340140040c1c82c0c10900c0002c40c402d03e40346000074201103043c440410850078248040035101110300841e8500c2c9040c401d111100d00d06c1031000801024000407010280315020007600c040c5c01c0001c0445aa03131916047c0820022001d01420313000e9200c4510700704203603002d404160101c4402c110380301c030071440103207080d52250900c6440d2800d2220402500c000030307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 363779064 1250 363777814 363777829
    0x180302040c0807030e0a0201080115050c06010303020703031707141b010509030a1b02060f13090204030b061c170f09030105011706060603040b0f0709120b041b0f050d02030309 77
    0x2403100d0380e00c405552415007030080035610606417040042e0040c15289000d80d0703000301c0c0c072030544d00c0d07803a036013440c00280d048100c0f01442103454541442c0181350010040680c00b180075030850f070280d91550040b402c8000394030061201601e1030404a00b42140a450188032240645800e0888400e00300c60012021600c5007034540807654101c01e60000a0172164054000d0401c585998641c3e9050300c4a00d213070781c0071800d24440e00b19000000750011502100c103840155222000e04040309003075450340c1d0780749401481d5150130b81700c00740714a150041103542d441c2d00e00070300c1034442e810141d000b03411182e00c1e83c18561580b020301020381000041040c0d0185840902400d8003c01522600c20000001c03919a14100540034001034888c2c2e50070028030020902c08950340383c000d2000d0303c10070120f440c2c8600a8400903910780c04108280342441c030040c10300c221000c0c1148a1030196902c0c282c60403e401c1071581c00b00050003140d0000341030724014402e40c00d2060f226811548040c2c1101c1c50500040000b4490 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 363780314 1250 363779064 363779081
    0x40c03060801060f0305060a0b1f08070e121005060a210204060b090108181005180d0e0d0b180102040b1806040e010e0910020307053718030204 63
    0x11a4480c0020070146809100c0d00c40149444448900501d08680e165a141d1070040c01c26182d45481e6030124240740e40d81c190501d1540b1490b03205d107100c00c0d4a0a00a0400d69040b40d02c4030201e8418500494141804c980189918403001c0182036403141c5481c0860040a020388280c0e00f040c040180802d481155803141d80000500cc0311011220b00d25104010566460740c00c450b02402040c81a90516600129010f0b0843d0050410101c090409080185000b030344a00c2c26950703505150900125501d1041c1804060607084150f5094041c824002d447e00c4401801c01a0007030840ca0400011800078002190003400c450582640345c1802c0300550b0030fa80180d08404286039000070f40c00c01101d020710380c0110350602a240c00f420a4070301505008034800521420040241042c0001d400380d0051000303a80850426804546909004030014501e4008418113080038483c01c0c45038501c4d000c51072180001d03c103840c0442103855803551089941d00342803000d50141c0e4111f20008070050350f540c0541c2d41c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 363781564 1250 363780314 363780317
    0x30708090c0301180209010902160b0a020903060a02120f091b01050403021002060105010801061409010305060105070f1101020d02060103050717070e07020a1709030c0f1809060103050111190f090302040c 89
    0x404d82ca0040065814044c0d02a01c106481040307015210220761f05000f103943c1d00480548584d5654840c80c8010344101c0303c00c217038140035003803c208144c61580d0240c100c01c5540607204003e13a8540484030360180303081d42c1103103440d071140007440d100283d0b41d021400840418507009040c00d40d2940496100b540c005546009078001c02d0051010b940c0c0504e0403401844181342c01d4a20070891100c0d031003248070700008241015204d03c0012241d901403800c41d511150300000301014680e290070066124554003c1c03150041c052008482d10043c030004c1e0050503030b0b8000028100b43c80c507000c07071f00c0d0a51031484251034050050b0480060b5240154111901c40d01950f00034180e030018500c3c03c01070809d101951450900010f0101c2503440d2000240409082029210402c98092080000d20050324500021171400302d00000c1007e029400b040040c12680b190000b803240805810031208527005800c2160881c41d2124800d10b0014440d010072204c0c4045400d01070449500d80d00410140c030f803600e10700310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 363782814 1250 363781564 363781601
    0x106080610060311160b0403210906050702011406040b18100819030210090311070303050705012f07081314100809031e0c010e150f010605030708090c0301 68
    0x702c543c1501030003031340c2400e103c64903150001a07940800c1c00c48119801821034000507000400300341c05502460703042c051711a0801079120659210344050314610004852072410040813491f124014000d400000e10401e02e00f04140e501c40b0244001480413030040c035444890603007114601801d05440354091036801812903c083d04210009240044144040c0c0d0382d0451150944c0202e0350210303000301e9410f50001c01003011015400c0c00c90b64102c40c811851600e00826000108140d0400c00514a60313100300004e010054800c80d50808000741e4400c41c19900c4e02003e0f118482400c11401088000e05c80c900780b508003808a00010101c1d0700c240c2004c00300c0e160107141503000349840b0301091210394651618401c0b41c40c040041076101c0c000d04100d032090440c02c1c401c0000080d41e03402034810307201c0040b008008400000d03100b507a4461078590124246c80c0342c0002b00d5a46207004107414182e84268031803502e55140d0301d00072121188003c080a40c01d010710400704807942e8081c00b840c11201140c142c2c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 363784064 1250 363782814 363782819
    0xc0f0f03010b100c050127060510170304031104140402010f1206060c33020705010908130611070302011d03031603090f1d0403140f030a1e0207020f0609030106080610 73
    0x1d03085402a031509084109220410442c0c09a0341c0d4681f482990700c480301056944401c825a040341c810b507000071410319000c90300a02650000805002200d024180752840848604144011181d2102c4d81013840501c01c0002805035008010000d032a00b114a403850000755061701410459000381c024100141c80b6400700f90602c0405520206903c03507014255a104003c510420788500402c44450049600855000140982175010032040307138106500c1a034400104088005c5080c0c1c501540300401c0701041d209021440002d00907080e2035068403000c2d254402c140705403c0e04a580b12010741d0511041016901030b50385080c1056445100c1d07100e000c400ea04144040c00004002e0300320541140c000c000554140e095059415085030700b6003004c1e113052841c0000c0395050320520360b61000c2c0d07040000902c81020140e60104e01000418410ba04a00c204c281c0c52109130700c11000c02952045402c00a041c007454058000c3c052410010000030b0784c070f07507113400241c10702108988048085003500e804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 363785314 1250 363784064 363784073
    0x30708030a0204090f0e071a07020303030c03180a05030a0c1707031d01030c020613020d050f1b0d020f1e0d11030c03120a03020703170a1b020c0f0f03010b100c 70
    0xb00b05c0c110650080030311000da5010b044651711003071440350182080310119051580004141110f89690f00581a281d50b0310f4001d03000c1a407540300707031403000038684a130941c141807400118583c2d20065018000d540750541c0c0300022541000080000c1c1c2d40c07203580803c80848030792190b00030700d11075100c2e840700700107681c0240304101c2d020320320503000741850704007611103d0850b0f0206a0303e601042201142c50310200c1400820284803181c0802440f0380f0403400d445c071400070002110100c0d402700304904594007201c60306220405003440ba00a40250801e0540581460034150034a00d0100e0044100d0183c00c4000c006034003180c140d4403d960301d00c0440700010f02c5003010301c10030304c1c00070055000304002c40c0701142d490740c02d11030020103170209076011500c003081601c0740d02c0b001d0085034080344490b494100704028100a0070104200032620741d030b100c4803140d100d001149511011034014290010307241d140b028066142807a003020741c1e00d5560b5000c5031302c071640c402d015441c1090060703440920030314440c5030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 363786564 1250 363785314 363785321
    0x50609070306050303040b070f050a1b1e120f0629100e100e09040b180616030e070b0a180f05030606100201140c1c050105061b030708030a020409 64
    0x2410541064001d02540e1000011202207d5250100950310b08460400d10300024609500a01901625030f007a024000741c44c0195442d1900003507001021562000031240012510310000705504501e2001c10100c98043e84840321607000741c2641d80c18042640e24002100d0b521960382c801e030640c00002228403080e10b50030700e45084007a200109200000400540009110945140b041c011a410000107620a81035011249405040000d103801d21303292076101804100c410070103000d944620298400f1000071901c0c05a41340191000142c0013080c011409010803036010340d0113210b280c900180e4424540006d01048003559500a040a680a03007400705031600e9200000641d00744c4010700c5940c1c0c02103031140e04004125041e4450100851042e405040d507040f00190f2102e0000c00c002e89151550000c0031890800102040fa04c00414891411541c0038082e403a08018180b01d4a0203954442204100919050b4116410f254a0b42c0d640243e640c000c551044580c1d40100c0c0800c9003540502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 363787814 1250 363786564 363786571
    0x10c02012009090103081c09030c0201080c1305150f0c0d0e09040c0e15040c08090c0a06080a2703020d09270c110d08040c14030a030806010306120501050609 69
    0x2076030a18140c0c4001c0054405074040c0030251014000141d0340e0001c00400800303518060401106004000315402e0150480c81c144030140d01040500c0d00140080c86050112803900e2101d40b80c2001c20f5041a00f800322080b0468410007034510b00b0042c1100090860b80901604081500105440003007284014540310300d0b802c140307000f0b01100060000280b005d00c105819281600141d0405603aa201c52050900030100519089450f04030024801640071201078403071000b200c1102c11502d405020300070880c1c2a0711a07100042c1041c0042000200d49070490001d050311800750800304074044240821402d0310a80803005a1f114501040702d05070000008802492220a0f0b4504103840078010555199006c09200384030360703601c100d9824140035203460791110b01803104031090481c0d00c2c500586002401d65040da188030800c02c0010b0041c203602e030343c01a5114090050f140c0b518a0356000d980419018244505154541c440402c021131044940740050b0b018070000b0400c0c0c2804014441d0103800603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 363789064 1250 363787814 363787871
    0xe1206010f1a0a0302090a09020a080406140106090e04150c11070b03011404020c01091b08210a08071e1d031204121505150111010e1e0f010c0201 64
    0x3554203482c81c11075602070390503181c0380d810090713a100c10000004103442c8403500848c051610200c1c440010f0741e4000c0307074144031324070440c020011941c110b004080600b03801d11a5500049801c042403180405124400b80c00a05c1222488a0701d9002807642051782c880c080140c0c0060114082c10203102d00800c1208020006400050700e95418014411124032644140074041d42e0001a070400702c540960040d04c030250824074001d50315800d00741820441503203120315403540c4503075060384651800300c002010000ea2851101071810500e01c0c02514400c0c0d0082c072940c1400004404a054052602d000b41078802e96030351181e580d084403010b500b01a10500414901a80c054015107041004000c11142038400280282c1d0250116140400e9102c92110050b0242814502401204190785040c500d83c480241c0b500d406640b080000742d1700b2542070484070b00582d030001c42207016030680604680c115405003403d599030120000e41041c2075412131968980142c3d942c5841c18600760b0b03090242545045803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 363790314 1250 363789064 363789089
    0x912030b011409060c1b1503150108041401020403032604030c02130e0a11010905060307050904050c0c0a0c030201030e0a0c18090c06020703020108060402071a070e1206010f 76
    0x100000301201400181d4002c00350340003d01001990301c82043e0360140880d07108607a00103550b5070303256610751010014180140c255000601c00d074160b1400ba85d1140710740d801c0da480030095000044074896000b90085c2c0d040040030120410000c020f000410165000b40c0361015640298440c500594692030a504081004403040c0400207078800c0035840b41c607404481000c1c460340b4108481004005815842040744a0284424108130030b0941d1110500402d8031102e4013035980e401403014030301c41200c8800020f82e08111024981c40c00e0340c406504803420181003810007100c1440c030307442d200c11902c0a607440290320000304110340c0d0601034146102c11030400b612006849541d10358454150f801444905070b01c107080044c901c0d14662181114541050019120b260750b840083e403100142c2c002070303000401000009050b0b042c180215040c0a6200700461740140c262104a0006140945078804019a442d20f0765001d655030401d21301d5600600380501600d5140c0389555004092980c0840c100700700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 363791564 1250 363790314 363790331
    0x70812072c0d060b0102030c15090f06191e020414030601091e09050a021503100f030305070807110916021b060306090c04050a03150e0a2d06090501091203 68
    0x10b40301180c8844a600100c046035030a07440e4010703030840c0903204e43c1c0030036403040107140411002c4c201d55080c0036144400550781e0b1003400c02002c58546c90111100c0320300e01507070080121903000b1035000e403410146170003501003041008660300c3e0590b4400d9100c01141d4200c011400c610345406d103c00ca00405040d44104101070f001c01885a41102c85110501c900e6540d22002c01444810300c4000c007200c0e4024a1030200e41b854400822064005903400c590320000c001021a00d80c4000d02c040d0141d0360103488482c01c00304c0a40d1110665801000215841070164541c006030792944041d8034001c07041149030070554004000020f180280c01030090341d03d01142c1700700204e292204411260840002e41e0b016000d6900c0da41a84410710880c1d001c50303005005814004184010100510100012110140441032031050155642e65407040081e0a481e49288034903055403a40e05c1c48180800d0048100b08048082d844003011500000420f59059440309200401c010303105a040794000c0203420100001007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 363792814 1250 363791564 363791569
    0x203100918120c05030d0203130c0f08100e0c0301060f08010b030105010b0313080f030406020a080114031f0603061104060e0109240e06130806011217070812072c 71
    0xa2948000b84180060504080180201881240c000509102c1c040d03640303080040494005402800f0b040e5035141c4014000318941c41914824001c44905034020400b0b542c03810b50324030003440c00c24807896040c4a2a03803070318001d4400303020b514020071440d5003a00c0014038011505007590417411081e4400d0745010014080c002d1703100140c036045440204506407a4030301c1d2406d42054407401414100500002c4104801c1001c10380080180c4043d85d519641140d981e82038006c2001d04009049605030082000c83c2400440b0b09010710740c2e00b409a8000c24042d50343d071a10401c5030150a84441c02c210002020f001d055080303159422440c00a20380f89a00c00d141051400110b410311025400c02c00b42149030030700c014803039540c403280d2440041c40c603a900e881d85c9084801c200458824070500d03009aa0000502e100c8400341e0507410303508042c4e0754410070000381001900794001c18003290075950501070130504c0d403075140c00a4032410840c0c6070318a241c080c0e1048070049102c0015860000c0c002011100e8454 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 363794064 1250 363792814 363792833
    0x230d030c050421051e07060c050c0405100f03050a05011803020d0807120509010c03050a0203070903030c050f0d1107080a0c090c090e13021822050a060203100918 71
    0x44858003241c1c1c00404100c0c0c0c071000c0000c4203c001501c1482040750710003e048120545d00201c441c00800c498005036950310070303078500581c2407019145800500d90b00c0360700d00f895008503074030402c20b5100d1645c40e511940180500d48003134106032003507802400c6c20300810100f4420080c0000301b56105511490349a07034000c1d50f80700c2800f08007007000075010214800364000c0414170b6076090031840c140081d10303044034030301e000742401e0762000c0021381000c0100707045602c28401c40c0e024260079650b5084090440c2c90a0702c00000b1220b048541e4402e1640004a220382880100200078031a60384120b61b4480510345450800d07d81c2040d101600403808640c0011080d51101d0100c0c0c00c0d032800410111a950400d8a4828a903031254040d41c45c02000c000a440e600c1c1112409140301301d4034000340880d8042c141c090a10300f26134040a4001e94000c018028120b19510a20b0501c12000c03100d04201640e42d02c8181d0b002030321000c2d04030028142c14400c426440c0900100c080210341c44c14106000c80d02c803484503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 363795314 1250 363794064 363794069
    0x22107120c05311b0305100b0a2601060924031109030a060b03070b030606181207080c0a0b0307020705010e03030912070302091602030f090d230d030c0504 68
    0x490b074032401000066440c2900484003041d6050b005411079940192902900c03902c110078203070540780790180d48400e011b0f10a0034050140144020801c40c2031044109840d0311a2a0340c9041c05609800303042140540209d0205001040d00070740e40551410fa00544075450b1f07608a1507000804000c0755146070f42c40b8615500c80503040c900446c00881c8030785180780e14400c24030001d0301400b88440c004c0c00d001c01900700d9031060105400700c0b0141c60350760380360a05900041e102c00d94070842c108410340810300d9200140740d0451004181e010144010310f0a00e01d0b000c4036900640068004500300d4455142144081c0d0050920581e0540386240c0240025201d40345030007401d041c01005003445256460070000d68140b00c40141c41030310341504440e81a6698007181c44124030554202002501d000e1400140301c2443e1155001542010a9246061100e40041140c03e0304414000c2c3ca94001c601120b10240000c5070300c0c10840014000e410880e0704203d002d020f44028142000e0040103000e1317026044504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 363796564 1250 363795314 363795319
    0x412031802060703080f07050c120c15012309040f02040c02030f120a0e070b0d050601170a0f0c0504050d03080c040b030709290313020d022107120c05 66
    0x14894041510050340c8018050069042030000c90344608054001a5007130244401c0c8412845d1956000400c0728584100e2284043d29040ba000d1b95008030034800203050703618040e80550b060080c80c036040040c1035009a01280d0b50a2016100c11608400401c0500300b001c016594403c0600c0c00da222480c03c001f54840c02400b503991201c020500c80c3c400c0c07041da550416160304850f0360303050329442d84841d072000b628003804040c0340088521382e5000010b082421103004229003802c084000095400401008007414144000501a10158031b0750003a1688202c08113a070029076480101038000454400000a20034080c04200038041640c601c0e03005640107030b251900408036554038682d03c48500542c3d000403021b50000c03040c0822a40c01088400a0fa82a490510450300e40768010140440314080316a1038040d0030800b00b00d6640543d24541c001074000386c01c0300405155980455100c0d41e040f6000104000000380124003224103000304c0b002403850b08400d0b24a40e00c41e40b82d10101c01c411348115413 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 363797814 1250 363796564 363796571
    0xf0901140d06020307020f0609070509180a0501090803040b07081902070602120a0905061b0a121410051212030f060307030b1603050c13150903020307030f021503041203 74
    0x850950700d0541203000c240d441038056489003440782001c1d550721150a8003100500510300000c80c0b200c4001034000032a28020902c80650304c480400024041d03151410342e0715801520160300204d202400340164061280f40c0850707070b80c90305040400c000b8402410b100100007080042c000c812242420ba0305003a4602d260040c5d8803650381c903004000b84120072842070058504020003038192002d43c41007508078000c5040e19403698610503000354844502c80260a02d0500b80a0656054030074080341030030402c520000201e400c2e00040b91149144100e0b040c1e00ca440c00d2100612003400c003800c110301607030600c038000c242c030603101c0c440c02d00d683c00001d1106c0c8540c000000000d4285e03a04014000046801101c180618103003480035420300108948104080381c181030101d800104200f044502000c140304000005600b861403061100d6000b96244003001102c2c000440943d8050020100840c403401c45046040070905c14088441e4030100024039030201401080081144001c4e10701c58400c0525000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 363799064 1250 363797814 363797849
    0x803031306020a0e09010305072103020307030e0a091a0103061406160804120303060819030c11030313140406080a030f0806030102070c0306050405060a0606090b0c071e030b060f0901 80
    0x1c0398440c1c00c0d401c0c0340794400001707000002805400300745c8905490f0300c0c150588000c0e500b260500c47d299021980200140d00821500b00840e100383d4540700039030310040c10070f010103a6805084081c0c0306d00300e001186020303402d007402d0030a42c0c140c8220390003400e040440080c0413402c50300060306402800941c2d040d5501c0040d0a804200d40241120003500c1d2039030883d07010039140e0030014010102ea00580b103081c4a90211604002c2c2402d100c412403030740c550b032840c01078041591f8550b0380c60034602140d50140301c01e1080d121586242503804018080a8200440e030f600041c08205c162040f41d4032403d45900300c0d0641d0800709610801b014014001d900704507085032900b001080c0203104100c0c0103132442c0e44408021081002940000d405107000f50110385071030304c40f40c3c08102111100d10a89001c074030782560400100d180c40000e0b005141c1000700799070b8036580c0d0b82081c1d80360076507800240350030042401c0107100704001c0c03c2c0890380010050380c402c52000e58040218510b0a41801445031000d0600400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 363800314 1250 363799064 363799067
    0x180d020a0803060a05101d1f030903030e06092506020c0126040b011e051e01180b030702061513090f02101808010203060312071a07090f0803031306020a 67
    0x6450007000040d103205000710349854010000e400300742440b01d1142a07050704c24454509a07044000621148c0307481601035003261015001402c8804048062648580015025001c2400094800c1100c00c1c060039024046005510040991400c03011694038054001c2c46243c1e8001b4071040720070b800b8201010040014030082840c180c8000c001c005440302d03502040104a800c0003030a04a6000b15030512120000a1341501d00d40614094190172000343c000078083c03d045e0481031005000c1c1814600508034040c801f60724000c2d41c1d500301410000e00003051000e01641041156071102512550380c01070b00c454000510042c0c242e106171042e682d104c02c00390301404012815a070b28983d00400007040b506107000301500c15490b26070320a8161110010002e800c04042c001c030383c42000001d018021700801555070030707025040501d091750002d249411400d4103402910206000e4101501d44083c40d9140030801d00902c1915009003142e50028010303c40c1440010440740c6056a02040140e00e0300080e0300d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 363801564 1250 363800314 363800329
    0x601080c0c070b1207020a03080601350106080c040f03080d063f05030702060c120c0102071b2103140706020c06070c08071e020d0506180d020a080306 66
    0x3501c03021400764030b40000301c2800000c024102140154240c04041d0b8441c407050f61504090038018000c00d0000002422647c800d8922848401c0e40b003903a49400320a502c40301d4510540064800b02d403a80b8580180040b0f90000043c80c2d10076030010342d4a180c60304012401c030000700c0a00c8020308004010800c03106085154100c94050300b1441484403038072580060050020b003c10004100150700343c5016041d036078446008041c1d15030000010751034070210f81e00740f220a5115191922183c0508036025451400c0003004110700c0c4001e500141c0c55444030306012640881000043c860380c1d4a4210402055080c8610000c0031010303c80340c9103001001d42070903141201da0a80c3c2450089000900b00c04000c601d41c0500008009001250502daa0b40380c0180d50003c1d4280011300103100900c1810002600840d04024482000c01c480301820242d5010856045841c401169030340c100000700b00446a02040384010b100741c0e0b80c000c21140da980d183c085c1d100c00d072103e80070b4190040080042e105403204032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 363802814 1250 363801564 363801577
    0x150b03030904051e011a040b1803062a07030f030c03140c0c060a021305060c0312010605070605070c020f0f0301180507030302060a090201170916090c0e040905060601080c 75
    0xb04140140c1ca440003c00700b005115031028001d0000351400810425014902101c0c02c1c2d8a280e5402c2c545420501074041e075070420070003010400034203018804507031400d106130360140c060f2f42d280c0c801550301c5480c280e2128003059011402c9040c18044140460390045c140d8180d4603a5044c0080c01e5184008118041c1400c00e41420210170300c801071244c0ca070707142001003809a40f05030607038500341c07116030044069204001510390340c0540c1d00c0e4180031910b4450010308101042004592403e4403681c903068154009a00c1a00840d00124000042c0308650080704d40c0000c551401500c03542c45540018448000c402c2d0343c6c1d001d603080c0482c4841c0764500350b04c21140d45080c04207658460707009241c0940c0e500c145000031001400303080c1c040761a8492601900041990507110811911800d01d108108200014090340d0548190b20050281101d00321002c40a049504004110030302c25000c090200780f503101d0158040d52405c450000455000f24280d50011000d19005e0410349840c2e601c0c450902920 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 363804064 1250 363802814 363802819
    0xf08060f010e1e1003200a11060a05040312150b1317100c080c07020607080d02070c050907020703030905060703031e050115080601080a0e120703030f050a0504150b030309 75
    0x600c07010301c070680d84402800a2203801c0b07540601104c54003108400b500c60181a4408640e0240001100080841c024041c6105203207880c69a444048504a143c0481035030b2800046039602c0030300080c0360384000340c45000404d144040c07180503204e035028481c0719218441c2c1402c800740030070b0806102d085506402c0060005480c0320740c60003000c0300c030300f41c450110710052540d051034450180c0e481c0317004040b018815120303207540b00e051003840d8083c41051b074801c1c44200c503100310411218080c0e81342d502c040c041e042d024607031513031007681420203110199202428401c2598808401000001da100c16040140c82c8152100f54a900d11450140e001d0602690010728020b240645032100c10410b5003c10704031241c6003810f2030440007800065811030340658009001807154400680444015084a100203005c00201e030310341d14090740600941d0f0052002203000030703241d03144c80035541000d0180d80c0c0c0001d550401000300d0b0410303941d5508015280038551708195220480c0e2011560140242c0d10103000c003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 363805314 1250 363804064 363804079
    0x2040311041a15090f0d05071205030405040e0a060f0506030318041b120b0411220308031e36103603020303150d02040603030203190f08060f010e 64
    0x200c0036401e106420105000c1c0c0617520b04071500ca41c5150079140f000002d60004040c044040c10070184854590b040300d03090300c96100030000000c0b40c0d12544906007040c8000000780c000350040e8a002c1003a110800c45208900b810030060000c160f0b0044101d81800341415820001c0241d44804a800b51040031541d0005010102d405640150401d11014001c030b4442000c216902d90f500c100821036249112180d140c8005000b034010400d0324503503c41046540c613291820303141e40d0b0303910241d090b4800c940702039001c00c2d8050342898000b8007400c0a0340000b0309081d0000000e84c0015904500c000c2e11492001e0a070115a220360007050a02842d002011804014840c2c0480400e00700350600d45142d0b0103003144000150303103501c2d0020724540c2103441d078140e010b545503841c3d0300c3e1141c982d104070320120780e8800d42c03500c40c040040c1e0301c40c81039400442c801d402550700c0f0300c1090011645000f07130410740001d010000c28030a55041d800351206901001c1160000c001ca0311400040329a508c0790100180c00100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 363806564 1250 363805314 363805339
    0x6070c0609080c03041719060902030a060e0f010b032125030e1215040605340207051f031a060c0c15070c091d07031b050402040311041a 60
    0x440180140c0b2074102e01c3e070780b0040031b1011503669004206035101d601c203110112240004c409800c02e001c400e000504a600d0071130144c0701e000403a0010b1040804070791114000401c01ca10a00645075000c00440280c5000a50710030148282d89880c10144801c0000081c0106851490b41c0fa40b54103002c14010180300d05000c2c60080d01e009591800d440c0b0802110521700605840002c40740e9640f0001d800d008050303101c03a0b640138090000607059550300108401403459100d0008015004031180001205a120111102a0900700c4a8201c05e004110310f041103d03842d080c600010071603048511740080e2040071b901301020201551404658402c0b40041d90889809001503140c2915400b01d4000b850741110403a95061032207105e80c0100323a240700c41420801881154000380a50f00100941030510b802164464200f42e8a0f400850f1295101d03105a0801c00016030401d02409042d18110720303260a544811304422100c20b81c161080f61139002150a01c030146090607d130400280607245c698170b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 363807814 1250 363806564 363806587
    0x1110d0e01080a050105030c0112061203050711030604081c060f0b2106240d02040b0403050106050103020f12060a0803132d05061305090c03011403060402010206070c060908 76
    0x80c0c0180c06540050701c02e40203e03000243c54450b040c12203200400900c010214080103485000c0074011081c6402c0c0d6808000820340000d08803000d44a100340e941d070355030303030f4080c500f82425082c0103200600a600500421000070700c00803c42c0c1c650070031704880405c6148101a91800381c83d164001c0d05841000c840001014000d101c09000d0b510190740ba181c10461a001109918510884529a11110100404400c40c904400004100403c41d807590b15040c50b8811040a170707072040d0b000c1844410006020801d02000b0b101c1d030000b6240900e429443e200154110070310398059407030040d00c0311002d040401d07910b0b529800e219004001c1d0310180c0351101480002440c20f001d1502c28071080a40300c00e440361680341708001004101d105100c44261650a00040c03165541003150303143c1500c00075050108103580c41400107803056003602b5241346d0b650304040265003280141c2c1c00080c06603029005100042c0e8012900759800382c1540f1f08117000402905088000d0a070084015000c400c0010b00c100c41e84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 363809064 1250 363807814 363807827
    0x60b1801051e18010e030628060f03120807020d0e120c0d050c040b030307020d1407030606151407170c01090b0a0c020d1403070f0c061e06051203030604050601110d 72
    0x883c400d0b04c5400c401c401a01c140758540314110703200404510341400c50306005040b1054650000f01e680800a00079403074408010701c0a000c0d030015222408080f898070402a03000800c6076014540d8809003900b00c1e2180390240807268101d08042c07240385070101c442c10b8600704000a11204400420304060b0302d007903060450700d079515480310b24000d50a055280d5500c0c14000100d511940c0e010301441202126a1103c18a111106110300d4503030203203840003c0420705500948014142072071445102405000c0040c00390140c1c1710040441d06400d00081c00401e504a07040401200c24245903547c4a03c5200c400d40100490030300203085110b8002031003c40d00c42c0d60f005030a000115001ca172014030020f0b5058889244100d003031144504104001826244290b120001c80c51f07039428520b8039403042d03580d81802d480c55408611858681002c408016103510b003c0c034401003809840045640310003a086076220300c1300520017030003117071281c001c950707030780d206500c58501060000282c80391410b140400600c01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 363810314 1250 363809064 363809107
    0x822030501060605040501021b120607111005060f10031d0109022403041704050d03030b030c0f03030901080c09030a030f030b0108070c02090405150910060b1801051e 73
    0x650b18011001c1a001e00031000c650036594143c00800700d54010a1469030005010000c4075089030b4080c001c2c04d800c010400820b4000d010503100c40f884a84001e03000b03890080c54200b80d6440c41d0a100c144030b51501e031542001d40c3e400c015151401c4490103400223401522807458600e0001660111403010204194022901c3e244225400c4188501e4130140c0144035130210307520103410004001150024504007030807008182d041114509081d0349d00006210903c03034503415404261108000c600740c1c80d003030001030000003080b9011042c84901c1c5011075502d006080c0c810f810b000302c8801050001d004041501c103114402800c031403c40b042460028000c02d45043c017207004ca82004800c0d041507010703201c0c8038070800003561a8050a88150204202c1c1c40d80075005842a02854400500448052405502c604403040042010358440a5840c0c120b4420360b004400301d003030601c0400707880d03000710110b00c0301410700b4a04035803a005501c603030f89000c00c124a50b0380d0f0174560002c2c1500e540e2145907a403500c4c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 363811564 1250 363810314 363810323
    0x4030915020c0414010e06100210090606170607020d0f09050a0603200304021e1305070810290a1803050c0406080109050d210501080307060509070b070f082203 70
    0x309443c0070302078281c130030207001e00d41c42040d00e07170000b40850800e01c501600750b10040c8101c1e4020341041429500712014102c0075a1656181c60b402c4c0700000c821000c01c1348045102004113445d18000c04002e4071501d0900340341041101c050220540030744207031071841c0503080003446001004c4d5102c8010b80202000e4011407030008030905040038401848003540d210b01e401a03c189000d44014000c1e041143e2410f084940c04103202c20351400001a0f44680c0b4810710003510b0b40401030404000c0721100c100e040d804640e18910101c042982082c00c488001c0d102811600413036100c0c1e02408082d9402d002c80304061341c8a5442100000500c0000145402c3c0082c064504000e500e803542d4800c2e003031340d0360680041c065903c04982403c07050711400c00118200380348084c106c166409011450283c84017a40005075990000c110041408401d124090300700c10000018500c162400d0505030441c010303000003800e8200f140c40c0410a014004045858a1501c600e20b501d0b290783d002052500c203100b5010998 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 363812814 1250 363811564 363811571
    0xd02030a060b0c0a110402070803040605040b090a0309030b090a12020601140109151409030f030c0f0601050d1b09110a090816140d12020f1903050307050304030915020c04 75
    0x107007100d01070100d0f00401445400740040080c541c807500c00f0090362080194206074200f0104021820748005503026501c2003401184038105818002d41d4400d024000001d45c1d0080c0a803080080c1c0c224440c501101c2c0d1013a4013403980c0d9a16168641000111000075040f02941d10006090f99408a0001d0503511908003900302224280c5c01102d86104038068090100c0c42401c000c6c00d0755014a0450301e012418050941c40d0014000c00b00742401c030700d9031039815030741c0c00403a118401000a1085c0d40c2404203540051086c1d61500740020071240050101500ca44500c0c0c0300004502e800c501888040c2c4000c00003400025692651181603901001c0124009503078818003142c4900e000c9009810011450200c01d542c90500084030b010f20300302903150794001c16140447c00002c8042c038010a124003d90080e02214071f01c14410f600f0145a00c2208085401d41201e440000360040180d0780c02050701e05c3c1080c0c0f2541c480c50260b45020305604a00422a1782504c00c01016500040002505000340c5090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 363814064 1250 363812814 363812819
    0x506061b0a03110d080c1309020c01060317090a0e0a0207050105041113110426010f0903081005030601151116061d060a0e150d060e060906030c040b03120d02030a06 72
    0x43e0349542d4284c042c00001000e902c0403807459450383c0094403110074049a0f2401260f6180041c1049a02c031414030300c010b0f51140d00800900c080b58944080000004a072145400100030020f8480c641034001c840c0c1d090140c1d000704c1c00014095055840f450790107030080080d4201410012213240c41051154841d1104010080031178400e070213221007581ca030005482c28203041c0210f0840d89520078906076440001c007204050301400902443c2452580384100003100303280c50400500c09e4500519000c00c03400039080800c51600d0010b10302d411551070014546170000c2d960b1003203c00e1030b5150b07010407180c42050030b120456a441e43c50002221802d490702a42014180c450b60715080e110b111882d40003400748a901907043c0918283d908034100100758003001c284100c2c40074815000902000091599140f080c4400744080224542054084444690390b10708080080e540791050308900340203544400b206c040030789041104034540e0b25903583d41030b2a1040f5000c0c120003500121200c000c41414007000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 363815314 1250 363814064 363814097
    0x1050609060415140f0a1701060b0705060705070f140607120917132402100509061302040e010c05030406060e01050306010e0403020c090c190509010e040506061b0a03 73
    0x82a034614121404030f02e6042c5000318a40040741c000702c0081e0048080d148071403065036100900c0c400f4040c5a0281815100072590703007401c5a6094009001d0880d08020140c042800003540c0ac0d444181d40c90240d68515003468004000200c02e04001c14230b00440340301424031840407640a01c281c2c003641e9080702c0c0307034003044060095450848028081e1a018240420070284c0c40c4010119900b5a00c01481e44036510040350081202088041501c0307401040018525641881807802034880001c0c05d20203401d080c0b4030b440c4c403608050070350790002000d06402021519035070009020800d082d4020803950103000380161082e88122012154686499000300b44c0810701a0707003e06031840a40100001e80c00c1c0240c00d032101401400c10b40c00e511070056031802e2503441440e09407054412450058440c0c06c000340034800c181550200105004040c081030b0040e0f40e010003840c29202e011580802c5580f2007002241e4280b040750300d0080340303440c0c0e140d0307070302d038072440000c0c007400941c8030703940d11003906030310011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 363816564 1250 363815314 363815321
    0x31c15121205040b07060f0b03030a09030b0907031101030b010c24060f0b030f0a020d1a0102010e0601080c01051c0c090e07030207080a0c1b081b03070b04090e031b010506090604 78
    0xf403038240404c00c2c07003100003140c403503480740c14001e000c4c600c00103019031008000f9107190040000500020038011082c800c0001242081c1c1d0090f04102c001c08107241503507105500c08820a1015040542e5250680c416a100d986011081d42c1c000c410800e030040300e5506a0703461030442050724145414035100103030109000b01b101d03003102c0c240d01607282140c458491903081d5040103009440e40c00d409011030380045919104010540410310801c0000d451840006825500e03040c2c41c3d0302c8540c000390010003000b0004164403942032801d1a005a45004c07081e65001d2600b0281e0031701c142985400c22508107160002118420380d500d0342c1c07074803406070b55641c000c6003a489030b840000c00c584414008201c0340c601a009140c941031160f00d070085100da410340240315640e044c0d80140c0d25903005505821800b02c1d09041d44032680703819406032092904103072500c9410b10951040e80340c21960350350004205801441907a4000c0c2c00b0440440422500d160344502900e01900d50910078070841c00881c00700d152510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 363817814 1250 363816564 363816569
    0x30901020f030910140d0204090f0516080103031112030f10050a030309050904061404050a0201030c031416020c06030109020a300c05210126031c1512120504 69
    0x200415800d0118502c05c903440320f590103442803001c20078002100d0210050000e01b028082c0c0711030004a00c4121303e0003100340c80001e0200c040e051844401034603415840b01c401d6041d20717014146800082415490246004801e80c1c6005020f2804030030301c418074420309082406841e20000300c4625940f03502c100a9100713098400100400e40012041006007000e4006a610034021900000c010310064602c084001044030100c9480d00100301c18021507806205150b2404030501d4208009140c3e44418085900040c0080504451488000050350b100b000f050410440144c00303130351a542d4945010b4040e4000c08007200c04034841c03c4030304200b0348001861510344850044102c418031007038008a4000c1c0442e03a40c440411400304000301d0004500c0e519040310000c03410120250750b150664444007564400c10314101d1000000e0b00c0c0c1548031000054036060034512003041c90040b5444881001042c440d8201284056086000601218282a4a03250600034011001202c00e00101202c0e40e00c02ca0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 363819064 1250 363817814 363817819
    0x100305043905030d020d0809151501092103030e1c0c0c06050316050901030b031f06090e0d05030a09050a1406060d0309210212010b0a1d01210b040302030901020f0309 73
    0x5000c11803035544501802a0410b054000340e4000c240d08003270a41b20010119016080000443c6004215513440700e40c0c04e0003001b03180b2030701e142c1004050400c52035561123031000e800c00d0344540902c4407071801842440040d03a00c02140c1050580c00100145c440780103280c00b901c5504150a001580c2805582102d00c0740d4807000c03810034440c80300b4400380c5090b042001d8040c1010703500c800380f40d8076440400c54205030300d078601003205002039140350380f806682843d04591402428850607030400d010000341120003020a040090326940e074490310740300410a421000e49144100e11801e0700707126a41015000e00088001562490f0342c4e0300c020302880198110000b40000e1071248100619003c81490b54441129a044489804000d400148585503944280402655a801300110034a002002c40e001066104484501010002803151a441d814425190560499440e0202e0200003900310000c140c1c0c4100400c55a0929041c020354139000750f0005400741c4910380310020540d0002050b1455000f00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 363820314 1250 363819064 363819073
    0x70309050601031401020d060605040f0506070f020f03030f0703200c0a0302091e0c0901020c09040f020603040f06020c0a0203070812041406160b0601020c090402100305043905030d02 80
    0x3c681d1640307111186101082c055550901c4440d0b80f420b240d002d03213001000c0d1680c0f00d41c1c0380c90401c11500f60508080d40501d21984040103541c0c00605070745090080e09804540e05461010003002280c02d52050300700040e082ea40009a11013019008000e400080200c0d01071042000c0307410840b10b035503040308013a05030702140004c003c000601d40707001510380c44400300b5080140e42c90380300004112041c0c00c1d129440745400215140d034165904008a007178518003159604a9420541c0703881042c0300010340080c0c000ea40010004040c041001e038940b0344582d21480c1155141c0b441002542c450150b202e00303d20070f0050300310004131703070400160040c05140700b03800d014036141c94200d085082e000c80c0e000041d00007805010103800307888490b20720b44489000e9500c0401a24080300024184040080c0e4648a02c030104180009600c1d0340d0003200c030034107041c2000501c90326103040903000721407030200d0b081c00440e013040c4806454031f00300000400c078540b120030500c40300c0d1036108042e19000d140f20070741c0044c0d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 363821564 1250 363820314 363820319
    0x60906060e0d230606090703050601080a020d090f0602030f060103290a1509030606050108040807021c0b0a060602060108010207050a02090c09030703140607090614090109050a06030c08070309050601 87
    0x2070103085035022610403140544080d801d4400c220700f000e0586142c2816800030000c001d1715003842031035154000c1044c9000c101b180340c01c40018000440c09005480026808160003500170f003603a01410701349030810215098080f440c80c01c00c0c0030754806c48030903a12040304008611194001d0040c426002641001c4c00c181a010b00c0194904041d0009103075402a811580003032561100c001a4110030100d40d00e0000050941c00c1142c103031210b540c00035040111820400000c600302c082038035811541210385200d10904003c2003540c8000f9501d000e4000c5c0403210503c41040003980c41041220344680aa4005a9035405560700300e02a0100c00b8095800c03010a510043c509906000c1c2d002505904041c00d02403098082071901c082600100c0320100000c0c440b00481004021140c1c0c00403a515107001107500f8014020551740c1001520f200501c1e0210b80c0b0100c3d07030b01450001024182c0640a114465a5208020b002e02031303640c1030b0400b207000100803c40251090107028950fa8021004000a91 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 363822814 1250 363821564 363821569
    0x5040305100603021e100e0a0902030703090c150507080307110f07170105060a050d080c032710120518010f0c180b032202030609010b100f0210050c0c06011503060906060e 75
    0x1f850007502c5a10800703081c5c5c0420310741c80c644080c2d400b541140e40e000691801500d841031840d8074a03040f041290600340711500030035a00404840907568015411134803034461000540c1d40e28861040d6200074065203000107021400011002c00301c3d0344650030421342d80c102c101c0c6142215019a2070176081340308810f00380300343c4c142010b4042c000d500c2000f4a500e00b03074000300c00c0b6084da00103008400065811079040c088091400406400e0709900311403101d10494a421702800c43c541c0584011090f682b60310000b03410b5192441e548100141c410300900000b0a2440d07001c0091080c1154200030800850b0a0a4001c0c41d801c4200b05503180c00324540d103592100102e01d004980c09892040081012406840050301d05200d400e000740b10a00002ca099901c48040000710410b507080602080314031100420890790001d01c0306207900d80c0460004441c2c403003095050f128411600d200116115000c000a04a007070304940310100101642d08006442c5c940105131f080d10300c10f00c10580081c0b88e1404220345403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 363824064 1250 363822814 363822827
    0x40f050d091a0708070c0905100e0f16030b030d08100b090307030b041707080307021e1e0a0c08060f0108030a080105091f0f212105040305100603021e10 67
    0x1c0e00a221807070a0103017a54405070003445941000c0002074640e0240700b003421050603c14090207101d29161300c11300d0035005a1004080051400a6101051140c10341d081d02036808499007803800f40603a0300c8055819005040c0075402d543e4410b0340c010307010340000c40180d0141501c1110b0b400030b010386000c81c6140c4803000c0d0315501510580e8928065542403c20642c0900100390852141c1c14045d102d2500c0d10300a81800301d0982401c0d2a11100c0071000d6185c5408248130018112460780301e420b034100841d8440c0342525048000340080380059002c2062040055001d1055912898261a03680c90780348440d16801f4660000e0301140340030300103006c545002045154446c1081304440c40c03003146c2a10402e8040070640c030031f000d40000b0b40d409100030501e54440752808400003080e106a84503980d81e42101c040c610b200104980c40300c3e070b58591800e204d0702c203d0b0b0066030010120307102040d41006100082213984012031107980541505550140170b4003480000c10310061294800400206090700c11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 363825314 1250 363824064 363824077
    0xa1401051c060b070c03031b08030a0207060b060c0312011703070b0a0902040f051006050301030b01050f01020f160f050d03021b0d020d1511030c03070309020f09040f050d091a 77
    0xc10761109404121043e481015000355802014180c3c8545d1031420003404000441800707030307003241b6251881d9000c0b480f5501103c1d00050781c03410042e40c900e0a030a08000808080c1901c0340d01020008901000290000141001c3c140c03284002c88117907070b10121b44000c0c000704070701809581c0043c1b24031004110301d00c1100d980041407900210380e801032540040d007100c6048107031903015690340c0d09102c00135036054507020203400d45092080c51541551907803030b00741405205080c0f0401140200c10096442488458140b2000764101c9000e03040c52070102c1e03102c1c03c3c1c40c00382140c01c8029000018080c50800180c1070000d80540103030888500c47c40411244c3c41c48408420380010461000354010b803210520381100d140100c0110404010051206c0241d0f0b00e0900c00001000041c4140404d6100e00b00407660000351a06000607030000e00c0c40031039100d000d00c0e41103582c070882c4402044207000440c4500d20525114200fa10f05801024a043c1c0e030b40e0200340540f051310403002035a007050a1140c40140742 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 363826564 1250 363825314 363825367
    0x40b1c03180e07031e0c0c110604120602090f5d0705040b18040201120e030c10061d06030307080c070611030a051812070803090a140105 60
    0x440d440b000300344840310081e40c6020000b0781e1016015904890540400038400604000340b048516042000701200540e01019003c1c00b50321050300e44030364a4000300d9005007001403082010a00fa400c00500030b4000d50340d12070041d10003501e1400310303142c240c010032100c089010591010351040c00490390041240104c4a40740b01c45000000d000703140c3d9070900108003a00c5008181c3d039000c90110181004819800107000b50b05043d41d4080c25501d070880030a0040240c403844c400d45d030b03a90004944440c0051400300e1560700e841101c80408401200405071111080300300d901d03040c14068a01d040740d8445c0b140070b030f008003411f000c2c644203042654459007043c0e0042c200c0e070401c10641c8840e065944401111041030780580020041103801038051040409800c1c050750a00c0191007001d4900d12603a0b5002d04049003030390703d1a11507580e60780f0030305504110000300c6189907180d00104c2e0b5a58011100584035001490b07000440c03000e01078040c491044107a441c0f500300b00c403100c18140300103a501076050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 363827814 1250 363826564 363826607
    0xb031617010906050c0a020c0a080d0810031e030f140405060903030903011401080f0102130605030405030c07180e0c03103305040f0c0c080c10060311040b1c03 70
    0x1c2c0455003e000c1c04e0300130601c602d10243d89966107a00039203041e4501814600400740050104526000400e00b8811500c05040c00b8082e0354030010004441c10716500002c0030300c1081d0140341c02404200c1c0700700380d00c6442a2565041a10750120560740080f00347c64105007100c0401c018001803d020300a855041c070094226414800c1100001c0c1c00c0d00c81c030101100034107505c5801000362001c100103204a4800d55802103141441030051000c0e2401d241c01508140480000450304212081003150b017440720042c02e81d09920b0321500e0040380f042c0e08220381300001e0f0821044070045140030a0b001e02414004000b01070500c44440c481010b042403003031241185580b003055503500c1140c1200c5606070440a82d201c0d241a04010400c000c80e154040088221441c0401c107503a02a080540000340715044090740c3e8450020404191600c0e03007038061010725506203000082080080c06100300a840116000c0c000c180701f020900100d240f0340d07041d9000b03210b018650350700801d003e5041800020801150340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 363829064 1250 363827814 363827831
    0x10902040f0f05060d08030f0402010c080309010b040b03070b121302090c091801030515100b120117030304020d0f051e06070e1c02011206090e100b03161701 69
    0x3001ca030101c069401003640c8880c404030b0841c1c010310415504c46000c984e031403581c0905440340b40c3c542c0402441414841600d0011070203680c0590082d0400950000440d5034910b4a40317205800b9003201d143c0ca502590400c201c9000d50310b8041040300989081c030405078105100c000344803d02c0d4401400c0c6881ca221404801d0b0003584640c0f0700c1c284505400d20503242d680646200344000c5221b406c0307080f0358a0340014014400503401081500e607101d2041c0303c40e0456100c1e80700303184444905500100b100080002d02e010210981e211843c12a10046912102900503501e895124401241d00039072000c003454031800080c1c8000000b0400a0040c0308445a40c02e2295007449000310490500140313502c514200301140d580b0450a4406c2c11301940c40340c0c400009602622400074082034002e050190501112003203da10f50f000b1802001c5180050240185101d074594880c00c006100012a6081008029030b03400c000503002c0c8082001c10b0101d4070140b41c00804481c001d0703040031a101c1035480e130142c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 363830314 1250 363829064 363829069
    0x60f03100323120f030a0504150e011e09080a080c07120819060303020d1103160f122f030c070e01051e0603070f090321080708060f01050a02010902 65
    0x1101d0701a00e1202111500b01070390007071145000407921280c04080001c0103004c0840c120501034070303001032218801140d940c03903a03d07042040c41100d070040d001803890800c00c0321120005401c980080828000500f00da00c0000340000290707202224003a12080c0300300301800045100e80d1620307510403056501181012940e1b0741d14030300c0400010340c880004002c0e0090140400811442c2c94404807511020400e40d80303103540c06521840048030000903c0544a90307113460080c10300c100c0b20803450920170000103650b01e01e46420030001c1c0c5281500c004e20185200d81c08980204446484503400c00e40b0a10081113515013409000034400d4000795070b02080c080b20b8900c58007003080c1c401038540c40e84079404540c14141404122803140002022440c4801d1014919842c0c0703004980d00403517240b500c821041c0c203561082d41d100c134465000400d08800624444150032030404a03610821499413030300d166440304081100c4549080c0c07a441c1d40500105c0d1844000d602490040040c5041070002140d2101c09400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 363831564 1250 363830314 363830333
    0xf010611031204050303061c0b01030b0a1806020a02060f0106080f0a090519021005090a090b18011202040f052512020a1101180c030b0a020f0d020909010f05060f031003 74
    0x404132090391003c010300034079103800c0340c41c078004810310402541003214a88601c05046410310000d49404000d0b000308036161b802e130304049014091100404440070361868001c00035404002c0030310050103540045200c24001c034510f54120703000c598900c6420344400012181103100503000000380c641c2d0f1069540090014007254580c0c00d1408005c159000c0309006010681858450b150100941000045219942d074401002070300e505460010b06c00341c6100119984c03039188038641d404d01239040c000141d050180ca80b00402c040c400d442c240400b9421400990a5403001e03659a0781241c01200703200311445034540e0a1040380c0203440c100030b407020361040c1c40d030490303000700054000140c0e214030002e1502803d01540096500d550362110b40c80300b02e270300c0f20600d107591404006c045620803030105031403080980517110080419840940c0e01c40c8112190b40096101001e55406030b4240000007403a000c03040628411102c0241c900d43c41c098840d984048070394030043c40c2c0c180142c800b4001002040c503014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 363832814 1250 363831564 363831571
    0x1506020d090b0408030a0c060e0303010b0706060e060d0204020918090f1b01020c0d290103110d03020309040c09080a0c0321140c011d061006080f0106110312 69
    0x80140c1084284608000d0404120740c02c40080301908010400054500104070381c0c6800b403a02e001c108000b09031a000c400380c080d1002103201031202100200d0000d0069004200c000e200300e400300403996607104400c0a841049800c150b2148a42a0040c01350505230014810060010142080e003041c45581c100c2001c0c2c06c0c2d40840307403070307002d0000807418520800082c00c2441c0303c09041d68800f00010700003940c80d00100030840c06940c2d02c0e06054100b124440d08850141d03100b29040c0203018041a807410903640910060b191801095211718103030401c0030b46400a01d0305940a1858600300c1c1080c0000b4008601240c400c02507203680026005a05219845650303101e2000110b5076499410101500310042c400d80100c15a51640388032002e03080388594048841d0101c0710390322012204e048500501c0440001c10300840607420301d00d0350f44008130380c00780b144003284581c41c102e9440e00c1c0125600c1004440c42e0052506500043c04200c1c01b07020070452541030241143c0c9421290707015544503400c00e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 363834064 1250 363832814 363832817
    0x6260a0209030105071d030703120c080c0d0203030403090501110601090510050a03050a0b060a06021f02190c0b0c0a170a0908190e090408180102030405030d05191b060f1506 76
    0x400030300c013091551b0b841d01559040700314000c000050441e114064030b5001c02407581d052111b40d6485004028102c0c0503203217464807050030344440d80c04408000c3e480c2d43c022901100060011500429150700509843c1410072000e40108203070384c203080a10300100b1029041507480c01c80b0000c0084d4580d00d1084d00c10241d880b82002e00442c0c002803078001c0101101928003403045030248010700031158000f5010384c8030000380d640c80e41400a40601c1e10000d2003a1a00701e070445044d141c3d000c1c0c0c91a00641c0041406214590107030595854a001041501901c41c1c0000062103d40c0c007203c120b0355180303000d0740202200d8000034110b07416555840e4950b10100810703860070100e66000c2489034002031040c0502201313075003032181d80c505076681022a1050034113035800f0010f03e6000240c641d100b0401e0b1340241c5000b90490799084007450016003203400000274050350300f80b03910034002010300c5070302070300040844070b2640300408015540c0c10001d000a0741216502c41e0380c40301c10000101205001c500140aa07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 363835314 1250 363834064 363834077
    0x90e28060603140105032b261006051306030b061204140609070e130302011407021f020a020a03050f0d0516110a031b050708120a0906260a020903010507 67
    0x140f886030804200140e0005200390084054040141c8100c0018600c1d9070504a068201c00b400c42402c0d0b4208000780840c80103083c1e1000b2913141051413040c0ca0f402124032a0401c6000d59541c0c2c01291640304500000d0624003c0c144200000d40c0a90401407207204000c040e2820300480200403501d00008807400da411040405002161381c50a100054001c075000b000740500034182507408414070000390031100b9441651001c002407501c00e60000a4803100702d07048060a04040030025921141e9036807602140c1c040500c0515058a644219003020070150050260842c071500c05a5003500711066544004034108514410100603115003841004c1310160601d003980c42a80040909803200b030491043ea00c20448840801c0d002103031035800000710880000142d27894545507083c500940d000310000d1040002520800300400041c03d000305165071103c81c00c0d551124112450045001070940003100005240c4600d03210b02d280c5a441522002c016103000710010100c0d00f101d904031110030004a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 363836564 1250 363835314 363835331
    0x7020106050a06090f030b060d060615030c020601080d2006010b0d050c130b0a0c02060c010218010503010b0a0318050d080103110409050c0904050a050307051b01090e28060603 77
    0x74403500b280d02a0056242480c00349003481e08481004625000c0a01500c101500007aa01c0e030340c4100000d4410b40c00301007030000e41e560b1040d02030708070b6220348000040303400c04900500040c40010828100c0d8040310003029002c1150030107a606156100710a1030400401c0442000c4d04020132801c0d008103104540b8940d1492504908800c0320006052411035110400845200f44900400d01050707550501c11300e941c4560540042e541c000c5a218000e4101c0c0000c1401c0300c2402040d4058508601010b10200c2999412401101c443c407090041d802010410b000c1078020074842c1e4011100540b01c812858458280e42d00e44e1483c1034880d418031800250140014010004e0140100e101c0c3d400c01e0760107000004081c0e0710305465003401e130040c40c05020301d40e00050511408002e84811181c201007520f5850000d401c001d81c880800d85103c2e4607500000c00079402a51080002c0000ca40c04c00311a071941c1d03143e03d9079010015041e52202a04034468909007240345002c1e208110040c0119100000d0340d42 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 363837814 1250 363836564 363836569
    0xd05030405150405090414160b04140d02090a09020d080d020a111f02180918010e0a020a0e040f0b090708060603010606020c0105030a0204031e11030f0c010c080c060702010605 77
    0x1100642c0c5940c64042403004011545515201c50740041d4420359403034040700d0b500d6001d4900301c400020008404401e0400044d4055000002d0040c1c40f004c0d2854154030b405613061104004190304000c3d0412980d00c0010a1809a640402c030118401014041d803420031b0744440364a0b0b045141d856000550004840c544580c004a051281c01e00801c0030788480024945030052400b041c00454108940006088080003260941006881001481c3d404103081554094030380c080350801c905210f6103001030a9a00340400990088050341c0184840720340350400d5242000004090411513040c02240c12010006916101c070790b00c9094144010091540b60812803450120064509400799140103400e00000758045a00c4401c00b03000e0034140e43e01d86880309510024851540301520440000140719080300c0601c4c09003000c9401604a002643c034158101510384421500c1d084680c2e01c0f2030718456030f03540121040000300b805402d00c5420150f04ea120a42800d100300c0d80b00700180d40d11442400580b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 363839064 1250 363837814 363837829
    0x60409020a121e0c02100501171204120f050c0405071e0c080d021e040617010e2421010b101701060c0206190804021516020609040b0d05030405 63
    0x90303004042c2030000c0ba003280c0001040080c40c2c0f2000c3c05203074035180116a03079070081103807400d40002c030101044150703500c480300351041103841c0c0c50040c14001c441b1150110f0039020151003c1c0c0f100c80449000614050366110a00514103808075014055402001f00b00d99661003128455045a02e50103603410300007008044140030850791009004d858001d001c04185003409840000d12207400050390340c80100e2496002a001c41c200403c1c03004006070100c1c0961340000304602c2414450f000303540c1a40c94502c50f02141324100c1d040004440f0001403150234074603464032500380c1e00011789400c0c0200c03a0300b810455990141d01d0100d00c2ca0703440e09110522424010000d1681130300e86d142a403042014003a0761074140c8018400c0704204008407207804255520001200c130b410020401101134035405241c0506081b1040720180d10425500c8040202080b80300d003220b600505882d00c449110b03845608100241d005403c0781074002e540c3e210445013035141c1070f1544d0307500b9000344021034071385241900f0040c0d007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 363840314 1250 363839064 363839087
    0x40c0513060e04060f060806131b08030706050a0213081e150106180509070f0e010531030609150b0f0906330d0f05060108040f060b060409020a 63
    0x5161802008000580d107039200c00c0e0304a44c3c40400420034500701184400030b0510b6070400482da000720818001403c1c40e210072000101c0c40303000d0807034022603203445402040c1094419643c0760f400402c16a80020aaa402543c0c0068114001070414140f01e1198100111a030041130055104080e1800200b00c01c034945240914807400030100303960a0707903d01d62021010310071481401100720808146202d101a0710b406407a0151071240389203400c0a0040a040d08190100c022443c03c04800e0030a51140c0304403104420841c5d500c0171041e201c05c0300b440c1c541340b4081d0700401c004426640440054070600135944a03d001d03015058198410800000c2103032a00c402040c0b01e020031075603000d11922030f83d41103980f0030307021a01d10110540003000c2d503581c6000341012a944080007040007440c010031501030f00f0341d003030b0800d010080f48805c00d1032034046030003c0d6203450106032000c002400081c5118541c900031445000c000c100301e4548400305515801c43e0700075001190300030440c00c00890380110b402c0324 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 363841564 1250 363840314 363840349
    0x30608010b060910031404030c020907080108060c0c0a05070306050702060109060e06090601120e0d0f030905120903070f0305060a05090307170c0a17030619080709021c05040c05 78
    0x501031800a82a40310fa50030250180d0390302d007090108580250b0040ea81590003000c90b01052416140040c000c18040303404a21a130050300c04560500c2c032492100f4140c0d8204ca0043c0500c1c0c8414826030240d81040350300040398440c0c1c84801000501c14402c4c0802113201d0400494035003040312020f414413205070850148103203080d104202034480c0c400003a1704400e06484081c0d203512583d00407680804540300103810f1600b000d05c00b1110b009c00241c80b0221000d5551045110201d0f43c04c110160341d01c81401908039400f070134070207542030080401000c4e41e6000408451009a03242401001d40c2d0050344155155080741c4c08001040c9010300a0b654091100c0d0040c5261905a40e5252018000d014148900d1500803620000500d01080b848400030342100d0400d080484480314003000368411640710b4021b404a188003010721400345242e0060760039603009059928140f402c80b00081d004443c002040351400105060f07810030521499000ba406a00c0140ca0f66081c0350611594401c4081e8441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 363842814 1250 363841564 363841571
    0xf01060806070e01050a140c0d0801060203090a1e030c080706080c0c0604170f18030111211906150311090a060302090303280e010201110301030609170301090c03060801 74
    0x41c4590040c010700400383d003400e01c1500d4034510b40044814110303030f8420742d038180c0300041c1035070f400100060201e0a100117a030b41d0442503030300d03101e00300c0c0c40380240001243c0100302d0020500ca420501048480c41e00000704554181d1307541e03511055000d6405030b100e80c1c03058005040c18005164071004080e03004014001142c40d051a0701070159071444000d0024101307a01c0300000244400c6203030100d84039000000661921120401d038407250306d100c02e821481c481e43c41e186101c0054010341064900d140060320302113400c404071a42064003d03d00414643c0000c62402c06503490400c00d114071400760400f00c03c021340122040c03a000d021142e03010100324100c0001d000f40245942c40d80400c5043c0d031042e25025860304600c0d40442d156000d40c1c0c00484080032a02c1d80c40501c5110300445080e1501a0781c2e461a01d4119079005a00321107031f0203107041c540d5108000500c0401d4154000700c03051441880004981d2502d006c600c03205801c2070700120002d50b00c5907424090140d0502500c40a084544001c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 363844064 1250 363842814 363842821
    0x906010b04261e03040501023307032306030c04110301090c020a0606060203091801050904080a0c050106150215010f0911040b04030f15020a1718030c0f01060806 71
    0x10607450300020004800310201c1080b104141e40140480111595403020800c150300000c100c0a40b640c115014050040c0305003018000c1000c2c80c280301c2c618100c0002d92241c00403030555442c20110100401c3d24051507126100000210507502c44505200206d0710011102c0c14180101814080c0f07240c030759072040c2d042411460000c0e00040860f03045458104002170140c100c0003090307041c01c5000c0000782c00c8510701400020081d0700400144a000d4088400d060050184000038210030004e00490b5048072150300010300040380c40002305003c0d41c060400c2d2400d11800d03580e407400c2d542d00e9000b00c0b04a0140710b0072243d090b5010040c0c281007031f01c0ea18400040f1b40c1842c0b10480c40b054188245000c05440c0d000c5021035486590886000d42000032640380d5543c0c50b41404a50306040200490380c139811030a0f0601440007034400c0c0c03a201c0119079183c900302d592444601600d00005010f40d008d60164901c26004000c0400c014844140d4100191840c50b90303001105084840e01d5000140780e81140d400c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 363845314 1250 363844064 363844079
    0x106030608150604153302070807030204020706110a021018020d0807030c080a030e0c0406060c02010809010209030a030819060303140c1606020c040b19030b040203010f0c05030906010b04 82
    0x10b6201100b134800050420700034003044900c2400d9407040c540f6911003641055991880032a07000d40d1208100e0140c0d600c604280102d0395441144120841900403110a000610302a0010182070380203680115102000c84580d41255001707200c0342002d44d20645a103032402000340106181d944e005020b44183e40c4554000c102402c0c0070b03d00c0240300c1c160004081003094000d5047e00d0801da040554161905d59010014000703100d400036032025071040304501006464980161410f46025549500c201c40441d80152131014014010f288107540900007002251410844c40c800d0600a545240c090709210203100510780d07036802d007080c1590034880144082500f0140307240e40c5114110005980d9031601d90240d0a1401804420040003022180000c0355940010501007451080350f00700309880c0000c041004142c80c4085451000303004140400100d00b03480d071101d41c41030001d0004100101020840400c07901c41d80c403500302040000c403e201e040b080801016000d030641c10a801d1409042062 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 363846564 1250 363845314 363845353
    0x40309050909300406020706021615110106030203010e07030b100311280b0a120b10030c03060302030303040308100608010b030606030405011d07090b040501050604090e0a15050106030608 82
    0xb0740e820110380010038200c1c0b00c07060740c0441e100301c014a00b03015120390b105d5200a450b000343d4810440188100c485c0104042e81340f4001d078048840384004810f5007191120280c503500c521244407161551b840c0c41c0003016846c01e0040036011210740024000c4c1b1410751a12651130700d00640400d041020450307042c0000f494290382c4115152003240c10344e22101030302e070040b40c00312008070032803841c0004c00500164482a204c040c0a40c5121502e8490540036141c0c08141120038500300700da4000e258460344001300e8001d600020a100180c60003240450301c9401003440d40d441030ba02100054000820807100c3c07106c00d1400c4024240500e0b1456103549400303000d07030840c08013900b80c903c10240000441d041010952059019035654000b54000075001e0030b90907221522442640141401d00800420303500d81031041a050b1540100f00505050622102000801c0c00c4040803940b440f40c3c90300c08011401401e00b8068001e0701c80c002254543c1001001020355406500c5059030f644100700c0010180791201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 363847814 1250 363846564 363846583
    0x806031924141f0321030c0309110108061302031008190809060d0b04090515010f080a060e0718150b04030209160e102606010804080a26040309050909 66
    0x3080b04211041448072908100c1a0b0740010a00170810180d48070748000307004c1100100c9041c0e1410010076a141101343c055a4440400030000f1100c040780303c03120b60082c0c03400c580110010380a235030100c100d201c8840499100761803802c02110799407800c100302c0c4001c000e070040004038244c505072145503a41d0307086014001c13404403501c108008201c1d02c030a07881d0356000701e010402c001e00038081500241400b030b840321905481440160010800804d0780768540b110042140e55070001804610403e4681d03c0082c5094920460107019064000480f00b028558087c1002c40d0000c0001d404c140501450410300c50a60000740d021106200070000360f62504107403035110203040d4a8030b20518583d04100c2e810f5100c07001c865403006203d00d0799540c956014041c0311403800c5110300d440f5000b0920b200c03031002c0c040440d215800600204d00041c0002d8540c0c0180c286140715040120515a800c280340f02c51102c0d4549021882080d04100014190b019000a0082c00c080c0e4490041e4100998401e48800909 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 363848920 1106 363847814 363847831
    0x20f090a140a0c020307080f090910091b0c1203200c0f07151d0603040303141303120e0a0c0305060f010e07020607080603192414 57
    0x14414020a88104c1d0025403c0c81c8842d5100401c40d803080e0440c205001d81403061002a48562554900440c12449028101404c1c15011030884014100c48481402004415840706422107031241c50707039030810310b01c0d80000c017420415000781107a500c0010440460094102142c03040c0c0014051841c10082170320030741b000400c1ca05541300700d0340c06003940ca078882121181e00c45004011101c1c6034541184003c1d54041c64500280b00354104031401d80110703071111039a6072007840c02510a0303404448118841480307101a1001066002911092240c459603002c401c6100c440401a0035449039100c00102200c2c2e48034606641c81e610203480c0f0103a06203510001185851007807900e14440d00155008012659a14008980b0040e0107071109805005000169100c051b200c3c423401015030140030003612340c0300440c80d02101005e0b490a00c001291400a5a0a004107084501034102c681c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 363669064 363848920 := by
  have h0 := BRFrame.cov_init 363669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 363669064 ≤ n) (h2 : n < 363848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
