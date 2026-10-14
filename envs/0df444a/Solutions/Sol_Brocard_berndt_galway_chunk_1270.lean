-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1270
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:05:45.581035+00:00
-- url     : https://prove2.me/submissions/6917705e-6552-46a5-a5cb-4bbc7ee86cda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 228237410 ≤ n < 228417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 228238660 1250 228237410 228237413
    0x90c08190b01200705030601030602031e070c0308040321050121021011010b060c01054807051e060903040605030705070c0e070201020714030901090512100204091a01020a 75
    0x100600c803d08025009122a4000807442c0104105001040043c2c01d0f281c0e15a500c1c02c001000350800c0300c041100c00149106801500080403000d4410813a43d129800c0801003524206c48000f4010011030a00c03960b824803500b00d41000c050719261000300880881c5640c10800c1410703880f90001c2e001d060741654032000d100141e899610b0040d0201d01c511300f004501890032045400344c22110301d0903401c0307280092084003020042d000148250155074087c4542a1003034246000d04564a4003290402c04481e400807141890060b8100703005008481c103414a400354031901e00f0319540b10704526014a2030402c142d0b103600d007030000c1640680b5650146081500e4400040e24521006007824108400000c01c0710810400c21072010181c6100c1c00311441619003500068000c0d44611800d039025420107443c0b03841c50800000b00c501541d010703540d844440d13151100b80618510b60b800c014816000300b40c00c03508448064401b40c001080400008122500360515400000300c02201c5a411504140400790 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 228239910 1250 228238660 228238667
    0xc03120306010f140708090f01080606090409020d0213050f13020a06030b030102070f05030a0912020a090e0a08070614010501020f0607050c010b191a121f090c08190b01 74
    0xd81c07001080c01c0c40c08002003000421a40702d03200e0a100c501c40e0001091850501040801401030303800265443c0703c2e21000d510040d14040022a00300307a1203c010008c0c82b41720304003034110f2a2000d10250510142c881c00d81e0006100061070071408041d640c0d50401c00000104040e41241c0068008a07001045a00c40d004500d40030704a0090341c003410f4883c011101152001d60481d10595045203851108030214a0305c1500c03544404080400a00003d038003203905107409444100270303a801448840c50381d180c2841038003e402c80f0789100e407645c01282a100045290300f0000c1c254a4401c600018800d030074420002003200040e0030450443d8007150100c43c40510008450350071405074101281c5642d417400c1124003411001000a0308094050014841480c2d821401380540310044400b18641d00725601001541c0120102c02c2c0d00961041c0208022814058505c03951040d00c1442c0e0480c1c50b2902200d0040d0b4807102507441c00111804100300c3c10000501c01c19103140707a07000003401f07001c0c40400000e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 228241160 1250 228239910 228239917
    0x3030604021b15070f14220e010f150c02090a09080f070804091d1510120302061806011a030a0e06070804050111040f0e130b0c0703020c0312 62
    0x18000e560008160030084007800d281c40841c14010103c80980ca281c525689045100340c48034004591100c15403085240980340c55015011030b600070030309185a2144000919640c2030100c0540c0c6100c004c040b03403210300c3c28400d50280002009031641103150084403818244420032400402c81200300ca68010381e290401d294000c003002c0c0c40422001854108104c041c0304609100000017400a001410421354502400c21241582c1e4100b01c1620f40d081c00001d031024401629605422084480c0d0650061400d2541c0242e45150f000b201c282d11008800c03e070107001c1c1c001394050ba029000f00503646241808402074001902c000e044194504132200d04000b485681c5c090b1748a40100000c1c00a52a96002d00004139000b000c455182c1441e40300a412060203a40c16500f41d4201801b091200354581d048404960040d4945201146003c0d04922104405025001d82d80707a282c100c44049806501014041c14222849a40d182c00500d000703032811111039a40c5029412180a85040300700100a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 228242410 1250 228241160 228241171
    0x9030c08190f170d090204060e1612020c120405030c0f0319050c1309030908030a140307030e0d0e0a080a0506070c08070b100617060f01140f070b040b0c0703020303 72
    0x10161041c907464109540d46603400d02114440d008130b08800c440c41a600052811030003503c003040116254458580314107800c869000e002c440800b100038880381b05981924500300b480c14018284540809614100400394548100c0c41201180502c6030346000c0c0f001051824045540c190390341c1c0284003103034236165061401d686480d04461148244142805681803680c0c004210b10326205010759540e009100e02c81050380002c22600000c41c085500104850707000c003054840300c46800491814000c00d9000030f00c41c2c002c05888500350200740f2801c00c000000c2c5040c1e034464012040e50b01d428000c0e2500b0741da0120056a021810042c007007000410b1054000c0c00510b0112103001c01d034200000c40b4420f840c002800c01e03007040c040100032403500b01294240c903815660f02d0080754610540a804410585445622206040002049600031003c2240181b234044070507080c001050a400c425130042c000644a940e5414200400c0001c0881e13030300c0d40034400744c445508004064900a689000007040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 228243660 1250 228242410 228242423
    0xf0f0909020c010f09050304210b0a150b0c06150105070201080c090103020405100519030603031d010207081e010c081b07020613080c030606031915060e010609030c0819 74
    0x1840b8100e28001e400c05022101001410f04c50316200e494800d64070b0340144100458a64207008801226141035150620a900700f00c1c0f07400c03540c075061810710080c050621000c480d103020703800c00188204244064003000b01404003130800f51921000000c030642513100340758100803040001c03000507a041b080c075642018000c08056118250580181c000b44950b030001c0e03501100e41650714416560140043c065040d19000071085407034461416000c2c0c03020780c0001400300340001c90392400070490754950750403c0014411155900e0b560b2208500b400b2804c0c40a00c2000302415186903a0402409880a81c8005191130398003843c001c81d0000c08100c0c4816500c0142400081050656559405403050602610411041c407540d40f0452070f90303001d820024074041e0140c40006105464080350b01d5201709401005074001001c039541b020070180d41041c0c0d00500d01d99030030f0041103441245d45c0c2e0f00d01819540d00c2c4c020240b411801c19008903200c6621804c26940300c1c2181d4942d054500820f44030f525840003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 228244910 1250 228243660 228243667
    0x90506071b03080c070f140904080307021e0109111f050f04031b0e10060207060e121618060f050d111302130b25020109081006060f0f090902 62
    0x1c2810341e412a80c0d102504140001c2940c0c001d103100440d85104441344184000c030201c2e0307201c031110640504003a12550103001a40050086100000115441000f5205851a000d061050600b44521159108850307a542c1c880003010030110340b031194079001c0b00312088080000c4c0001c2c050091403030510300404009010442c040084d003107206031000b0710789c45000c2a03001c10072040c0142c29080f8500c5199400100403001c280d80440b034440c08000ea4000394094446036048c400305544055079070366010703001100702105200d03000302800f00030500c406156a22007414030308802c20701c12005902c00350b01030616144080200714207038100b40f404c030f034070950340c017002c0c0101400c0c1072003900320108116800c914800b80c40403001c07195a0042000244040c00b854284c0d4507148444034074020100e40d8810a40c04400c0c0708400365909030000380007071051400c020381a4a03449018244140e020f1224119a1110003e000054100b50400310f806110b00c1c1003490047e01c4007004051141e1440750000199000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 228246160 1250 228244910 228244943
    0x30e030403060c1b050d03060501030c080f1e010e060103050c03011424030702061006090302030618010902060c010b0a1203080a110c010204080318040c140a1b030e0103050709050607 80
    0xc0d41500f0307a401101c210a04c0c0301c3c038039040c0f40e600c03a0040203407000080c1c9020000315003580030748500d601c100b030156240c06a50b5241d007401023071844040c0080400012249000b0421101d1140e00d80c041c0c42d040701c040c402824804c00160643e00040c102665505c001d000500c910324070210301c0c0600b40701c2143c08440c0c04044400c40d14400440c030061f100c4011000003000240391300010341714058401980203c440c00d07660001151403a6250000070340c99000400400c0440740007101302003005079180000500c506142d0700241e40c0c0d5114200746440ca94640c0c15803840c900d0840b5210000b41030094444a210041d42d4004020203802010103030032a030b07604c4a040d440c410f150150340381d420460001b10f42c0e40d0784138040355940e5004100e55101d105041030100c212801c09008290419509448000817003031901001403458002d00c41c3d0310100807802c513840d0003130342800400198183c025100ea0803500103c000040c00d03107800030082d1060200b102c8040000707464041c2103454483c2c000ba0184080c0700710 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 228247410 1250 228246160 228246167
    0x606030c1c0204080d120e0705040f0209031f3207030b090c1b0c0d030c03020307150e0c0f01020c0f0103060b030c0406021b0604060c060f05091c030e030403060c 71
    0x201c115446402d102180200e000000024030719600c502c0303510b6001c599440109044103680e042d4450410607001140d003082182059004440340d1250421302601309180000408c0c035000891f4030a4441c400004a0204210040c1c03007201207003924202ca01c2c03a0328005840c4505030765035141d10000040c1554000a0310548030340e10918103a6802420840c49091030707442882c19400c6117001c40e6400790b4000c1000c1c0c08450004d0f0005036408060102008114503131026507200704608402d60a60004000820019000420700c00160442d0580001c00100303004d092460582540702d440d000d000c01d00d60b407110b0344c2c6e0005031007580485d003162210181e000c891300407400351071143d0068000020100502a8486080001d003095603110390031115610003010340d0481020380c060b00c0c0358116204100500400d8840e10803c1c1540380159070100b481601c0d81c4040c021108121140ca0301d940045c0d42143c0c54641003c8803002005091a080c0000e100c020340391034582c4590b110090000c0c1d0317156a0030740410f01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 228248660 1250 228247410 228247447
    0x2010c021c0b01080c0301020c0c0f0d080a05181c080306180a0506090f010609060507080c060405010905070f06120c021504060501060906080f040312060504020705010f0c080606030c 80
    0x4150a07115012540e01d480e0441c2c0500f8020241d19008a07148440181814400c0d50704117601c06000307005020a00b0103108460032001c1096800584a0062a001c214800700915003011956a484c0c0c0d14405010b0700401044080081813184101d2034281c05026101c5001201e1642c105840070754035142d03040060200014002d10b6040e200010003000451209540198411035003a1400117680da160316007541048030900545000c44d161f0385040c001d640c400d13005402c4142c8544420751a0400c16809945032010450301243d040c0e4403882c04a041040900000c0300800c3c00040a807100d5080420103000171002d40346058046907036a07154030f03619200f00407100803407180c4140c070382c4141001d040c820701501e0700340078810205814060010703200c0d105100491180000110001454070f503aa4200c940b20100c414102640d45c482802044540d107501c02030800d18401d070000101203004840b96001d481010b506041400403d50410001d6100c9808480d486142c03240e0341580ca0000003803201c01d819 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 228249910 1250 228248660 228248689
    0xc18100e0a0303200102030c0403060905011512020a080c06040303030b0a0b07031d060304031725090905060a1202060f0f190e330c010c0512180a02010c02 68
    0x10884000040c90741100f205900c10402d0740b0103400015000e2409821b03440183e5150840000410041000c03881030b6020200c03042c0324200201b541e217104040c903610a29550070000030030441109210451070000c00c07032402410341030003400c0000b110400107840b0740200c0c80040d00380360311038008118682d41c0d0030006e0064852080c400b5181c3c0700600380204044140041c83c143da035001400e0019a01d402001d580c856a40f5541c0c040b080302200306001c0d10418003400c070000b109402d468081c488244040b07a002d00c1c0074141d68080c1e5052500c81c1e01c00c240e481c01307001035026104024080c084403440003e410046030f01500d040340d0354010307804c8a00c0c140c4200d16041a0f100800304c2c8112142ea440d100b000040c00c060780d22000010710750f0040201800005101c150000b007803030b11030045100644904070a1002c031201c0300b03042c0a1302d407c0c01400c1d20302c2c040101000582c0083c107400c2a14540203003035005084101124a4070f44ca02105603555010302c50060b05010143c4840c404642e140c9010a4014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 228251160 1250 228249910 228249919
    0x504051c140c03091512060402160b04060c031a180c040f0305030d0509010b0f101205040b160c0b0a1e02130e01060e0604031e020306040b06090c18100e 67
    0x40500d184003c0e26074010500307843c460030a102d554840d1944440a036448000303244a51403058542c402000000d620602c654030100011000000100d03184c0d92711103200b64010b86000c0b60030308111100030116401a002d24152a5401c12041103d480381e02c5140e0300080c000c00410103513100c00780c0342c41751400b6035031040c0641401d501d404420000044054200c0c1810345100f40039036102d12458a003a2203403541150f0700718008403101d40451503d5441c03e4900802c074200504114040b11003001910007c6905a039000d0800c1d050016501c05810090341c40045480c00d10030060b526500d01407a0701c0e003d030560034259242c011340c01c030280d0311988d0000c2c41d80349000c04541d905401740002e5803a40c514440d00784c0310009a00000703085c6000f0034030601c800a00801ca81d150904540d10b4402c4590951076280030b6403d642110f50044e10100300c041d0040d030080301440c3e0640b80103020899641e0008144411501c1d090062038540d614402d65402207000807501c4044d40f50b51030408036034059040c4d40c0c0c175a21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 228252410 1250 228251160 228251167
    0x20a03110310062306090a1409060301090201020307061a121005010510051209010213121101021209010806030a080a031e0b03072106020f0c100504051c14 68
    0x100401003654448608069080c2e500c0c0c061040b16650858007148540c1d11204481d030746581900e000c01140300071480d4010011414031041c0808607022260703030b401120a01c6581a00360b00c9901d0b100b14641d42c1300030120700178000e541c43ca90000b500c2c1c0c0190345e001070040b502c48900700304e0101c1181c0405200d0341d001e86491902a90404041d5540c2103007a141c0c0001c91a080c0041b4090400b50001d1040b514940c90f90707071400c80642c00e400007050b002441242c2c2954280300c5100e00790100e52a217030060940051000e20305a450130704900c00c10b41542800e044d90300001c4903e90341111035003940c0e460542401c005156035a20404242031210143c4020324503007001a443e0140c035015407200c204230581c01001c40400e07078082e904900700d8080514050303140d40130000400c0642450490130751002c4800900003600c003900c2d5116010303a04a020f0604e8400c0e03000c2554032005c43c00300071800d90580d928406000a007000d440d55a11228091918010310107803180303950701c09001c0d0040e10071550100552994 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 228253660 1250 228252410 228252413
    0x907090f0b0f01081515040e04060204080607030203060a12020d14212d220e0a021306140f160203070609081005040213020c011409010c0905090a09020a03 68
    0x14142504814030401e071002c4200c115500c0344543c2c0303100d40a54192104103101e0401001801d00306c568000c12081800c100101d0075080380e00c076641c02980704038400740c0c841e410880e0250070800005c1217542090302c1441003020503594080803604032800155041900516400850304000c1101805000c807411001e01e09078800d80092140200f0080040c01b18400d000481d5800c2030b0720901d1640110101b5801801d841000440e141100d07100e84008030754600328510821481c452414001800100b451000c1041000c510781681c991002c6100c2d02103203007120200707890b010b52041d405030f0300c01c00c548520036070001c0300c440c803c40c1c00311101584400c0c1c07140102d0306003101512001c403040f8040c0c014010009803080c040c0c4000c0056800c40340191030140c0150b0b440800810000704166808800800345400c000002c0c80240900c0c1c102d4000400e4a80d1440844040004040d2400403180e00d04030720b007040561322143c040c05031031003207420384081c0d00c40400060180490350406540406513940000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 228254910 1250 228253660 228253691
    0x11b02100929030c0a0207080a0f05070f03030c0f080f0d050604110703080a11090a0b0d050c0a0203070f060b030114041e0308070f0c0b01180e0a021008090709 70
    0x1e00b2a00c0074600261603210400e400c50a5901c0740301c4402401c0000c3c0080707012410980040c0510280ca4411500856a2154103610b000c00101082d190070000d24080e01c02e0080510050000d42004603030460303000e00c0c41e03800501c0f030780c10040003a103044601c85e00c0070b042004020071280030820300d00106031110310030b2008000505054582900c241e11300080054951081801c0d01e0360b1607015285c64402381d48a00c0e5a40181002c40e85850f01200c1c01c0000200c980d45502d1800040c1030700c00c03c0e02d51a024080e0481c02250360261451078500f1050006910f25a800000c8a10710740e4070424103648400e413450044058802403200030750550a01c4110f2103044041020a40b00701e01804201896039066481035840710001400580010b030000c0018a5280c0608180402400c030707031505480c00690744d10388800850080c0c203c02d40401418202c494011894014a1450844c80001d0718011804c8e50003c6c0441e40204440c0061107003a00c0042d08010341488078600401c0c1d07000c020301c03010b4604035411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 228256160 1250 228254910 228254927
    0x41401020105090c1807110d091e0b0a03020f0403020307030506070f08010f050d15050a0b010207051f0e01050705010c050405181003080306030c04060f0e010e09060402011b0210 78
    0x1540158646000650104000a020080c5060150080c04101c0e00c0004141da061301c0144050b00380240380c190320f510f505003000000a4a0499910120021708126403030380035050b42c040301c0e002c1c030300c008405005449642041358408102802e00580d29803910140380c0c024052035102030740c580605940041407000100d842c52050683c1d50b41c2c41100040a101039504140a0040412031760802c0e0003401641040000c1c0035149000341703404003820906501c3e40c2c0940d1401c940d1500402e444a50070015035804000c14030291a04441c0030802c8895009851010520307240d07582c04018094045072900c1c3d00801c00c030f40c40d05400a009104a040710310f0054501d520621995000d0310300c840c0940d100080e21840030b1300546012079480100d900e1a00d40900340d0b00060701c022f605005824880c05140d0b218440c12002300b5560984404440c40c0c941a1345021070140c1c4490360650150040041c14840030500c0c3ea442542401c2502d4094510014002c0b52103403510b0082d00183c8000750b40702d5040c1c103e07101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 228257410 1250 228256160 228256199
    0xa05030c0d1107031208071403100e131509030903050d0f02060105180a0c1416020f01020606010c0b0c120a021308070f050d0204020d02070311060f1302121204 70
    0x26210b60b000c091420350f650302e8562002a00303290030004400290351042e80341e6030b041841807829000c2000f96103400d0420364812741e45030000201c903581c00c2040f45c402d81c80d4151f100320543c0403005240d00c182c5032519088000007060f842159034a03140030825000340b01c16070107503804c0406c40f18a10070a440140c440030341c0c9410080503104800c000200c51424030b0318881c4a8145000041031520342a42d044060044042c844060090030000c03035141c1c1e4008405801000c070513031009010402103006000303a88004000d21030442d0003420401c5100d903040010882c02c140d110a45405642e030341e0703001c290180504200c4000c0f00c0c40c201d09104602d0040e40241600c030b410441d80481d00c690701c0c0c104a550b2441841106054000340108110b40e00d455440803001d2070000d0405441c1004d1a9692000c0b6030250702c0840c08103655501d841c2e0000400c001c0e40c0d50003044055910210f040802c1010807081c1c0c0c10100034810030700e00c19140081e02c41401824030000c400c00e902a01c6e103840303801118810300d80400307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 228258660 1250 228257410 228257417
    0x180d080a060b09010914032506080a1b0c14010204090b03060907030b0a0c090e090706120204030302070e1302031f2904020c1f02040314060402031e0a05030c0d 70
    0x60109488207582c00f100c0341c000050319490105464008084152841202c1040d45401003440341d80c55402d00c409a55889026030140c580003c0c107000b00a856228007400c00d04440303240074103150300c1c070680b07803108402c02c40035042002e080c031341519000c280e13031020120680c010b500110780000c002d20150484028920201c0c00d541c11603644420b616690700311441701a011041001c042031562649900c0404a0b02c0a0302d021210b842e21140034a240c204242c036544015440080d08010307056004801903546031007460107503d40b0f80344dd00d0084d40d03184680a90f94a00c0148404201e02c0c00d00101c0381d03a0380e50b5002d03041d2103400701160940e403226440c8545214565003084d040c150314481194041e261040301201c0c01c8a407040c000d09020080d0425800c0407050310843d8a2101c0b05020103140c550030408064016035514150f14080d84001102032119805034802c1c818000180ea01050301c40e440358015108507200469a038860346807010400c0061300364080010001d001590203d4105010041c030f45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 228259910 1250 228258660 228258671
    0xf15080903090d1119080c0a050a0b0406050a030f140109052d042904021011030d05090c060a0302030f1501020709020c100c1806020d050d05180d080a 66
    0x203030058591080030140c6600c40500881e00c030008164005100c00d100000d44043d8103100001da1019000585801c0084698008a0078090501d0840b8404002e4501559410f850f0345ca02404210b40c0e001d81d000300c1c002e0141c04610680510301c240d0103103448500200d4180724500c1011442046c84c10203014070f103982400d0200180425020120b02807010000b10200311500148411580000760046d0089940075082e2a0414601e40d080241c2c0001c4000c02c4801803417800c2c02d1040003400300c2c960028070f05020012440003640d0f0404000c0d1420814903840220702c5907902c0d440c04e400c1924071001c1a41c40040882c2c540c2e0b80980c594042e40c411848200082e00310744464001c46d0351000000b10490041e0300090b0140b0081e640e54010702484ea0b40d4408840d1282900c040385029640c884203604002640207610000d4943e001542d9401401c042c0050070f00150781c403d0052540c031482400c00f224680700c8000c68000042a0052444072031854250785550162803c005e20113101501c80304445401c18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 228261160 1250 228259910 228259921
    0x9070905030d03090f021f090603060b0d0b01020c0405090106050f090f0601051809040809011e1d0a08070303030b150f0703030b1807031b11070b0309070f1508 70
    0x22216002910001001044500401d510440c05002d8030030382221900d01032072000006848050503440144181e03501841800c00c0c00744002c005941c6079100030101400c0001c100800704100003141c00b801c03000b403c04a080c3d428140143d00d0300f01c00d0703418190818a04001c1210090041d071207102581d100710b41103402d034003140e020019480c4094459070818280746000c900c4a43c001c1c2e000341804185100c115100c1e4040000103015140100c0382991000c000003500e48240d0703400003210142e450030b81341c02c0008560310100281008061a00d130702003910481800b0440e581c406107030100401001003150340240d02d84c078004003c1c26030214038a000301c98070031080c0610503500060f658444c0c81512020700300807060b1005c1340581080742c0f05580224003100c4910200c4030700341d8030b948a40150b4401261000040d100d00d404a40c50510720401c002c0004800c108814005c00c40c40115185017403116140c0e00d42d0900c640c24112a640300003503040e041c00001400d40c0c8149140034401030b081c1c035514000d0341c0741d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 228262410 1250 228261160 228261167
    0x1c05090730030908030309010501051c0309030b09030c060108030a14040303051c0f09120807030c09050603040303060b0703030603050c180f04081e04031704030f060b0d021c020907 79
    0xe03100d4100d000341607291207240d001c0040d0a8102c1c020702e824076182d0740d41c11420b82190700a84940001e40d4440005000a007400d1101d0207141d441051024400c0307100d0b8500401c40c580a000c000e08094090300801c01c00c01040081e04c1d000208032094034101d507991b8002560302c0e88a4401e01c80031407140c5401500c00c2c038404050324101c0f509501d07140d14018181d170344c041510390030714801d4011540e907032035810fa81300e01e500c50b042d04e80b4451081450040c01180000d005000300410b100101401d25150108040d0300c503c0d1f850031a003080e03c01c0c9131aa00e5070310301940549410b4100030342201021a956080c103505402500880b4000e2055408180300b90060000c0601c501e441961000d100c18042040c1d04192200c182d4018041c3c107409080400c4405030001c0072440c00602e00f10303404041003c1c014400316090143c2c0e103d0100d10f856103801c0c555a58800100c80710103000d0030150781c0d240441d44507110f00103201d000a5000788001d402950150038250301c0e81e11000c0983c042c00085000503000c500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 228263660 1250 228262410 228262439
    0xc0c020a0b0a140903070b0c061b030118050c0c06070c06110a2f07060320070b04120c02030703030c060c020601030203120903030409061508090307020a1a1c050907 72
    0x45079503940020f680d00604200f81c1c3d034030124003a601482644030026250081c50041e01d14880c10360301034140b606111500002450500384000010441000100070f601c3c0081c0810700c400310031503800b050550700c0d64484412401042c5000500380501c2040101c1c280e8450180100c0f42d12804041101c1060f417891a0381c40d014005165001c00c0308010352290500701c061999007064038a8280c88091004000d446040c0840d50b132296010036100c0d409030f051071a081d80c80c40c1d600b00d50b03207c1850405181c0e07240c521402ca80500050107603c03402062034200361040c4035802407141c01078103c8940542c0c1c0d160003004030008030001d50320246800b0a020003580b0100b200c030704903138004009201d98103d115440045510512207180d040c48208000a80c1c0300513802040010032007a041030705011041440034025540040400d030b1203810070031018005175649030900d0180c41441042d5645801045001085842643ca44207004041a9506440010b050b048140300310381039015a02c45540c0c0d500708601040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 228264910 1250 228263660 228263677
    0x50c150405060928060e07080105151509060c0744070303180e091605010206010317030601090519090c0e030604060510170d02060612030901080702010b040c0c020a0b 73
    0x13004c1c400b4035112100f04002100b10364090359000600d0894a080a45803880b16400040a65150b40c204400c0000c060920440c480094401c103460301c9c4800a5250f90788a8882e50900c9207001007145d007000c0f00200301100140c0b5600c00640145598801c44d04e403448030500140307200c83e50020144100408404000d004280c800300182509821542d0503150b00410100c1628003584940c000140141460410740c020518400a019503143d6450251004003854002c54190740c04200104000b8041c40c0c040e803c40c681d518031701d0703441c0d45403100101c0b45140c07107070f1025074070850a041012000d495030851a0440c0c107640030800030320529590541b03501465007201d60341030304401300060220711b59401035070340540c0d41c80503003991689a02c402a11607088810b50b030f0039640119180901c0640412130240c000000700c440c40c101940d4070303030503644e20322401c1e05860402501030003164059000750010b00156038001e000f48000800c84100800d50030711000280d100e4259a100083c0b41003150081302c03500d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 228266160 1250 228264910 228264943
    0x302030309090a0f060e010305061b03180309040507050309070e01050d0b090c06040e010e07030207020a0605090d080408010e01110702010c02090c09060307031b0e010f0f050c1504050609 82
    0xc5a0700b0031894020003000441c5468448041c03200c0d0000034881d07040074241140104c0b4a5505604055241c41c03802007280c071010210269944d200c0181c401960351042c14404a40e128408000d00c0718110b0003011030294210341040c052007041a00000594030915030300d422501c6440c0c0d141c1415007500d1080c0300d02600100b0102c42200820340038603110317510000200403501c408078684041001603019602c4664214070300700043c001d8185005010303805c40518501507083c011142c0000e0b00d680c400c0c0c81900306000001030103500136141d01d45540e86403500540303026151541c50b12503034041d0101d462100029460264084000b44844050b04e08040e01a0b44003824442c441c0e0912004090192091a5903141402241029950f42005500c9440c00b40c0e40400c400b043c002803027800d02d50085200c0d040c4000c80c0c5036180c450f41e02480e480d81a200502e814490180104001c0c2c64902c500d43c00040c0501410500460003074420303c0e00c0d4051032042d400c0300c43c0350b600c5001c1036460344210101e42198 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 228267410 1250 228266160 228266167
    0x93c03020418110105070602040b2a06010323012406180e01141c03030c031406010c0605100504060b040e0c030405030703140c0109030905010e031605061315051e0403020303 76
    0x1d13522600213403610500c1814018070b0300746c5460340c24066410000d10940c40844618140c04950031402001e508030426600a1240d075065070f43d194420200c1c0c2030f07180c1040b40404003005243c0002d40200341000301914042450703d194840303c0d00da000841c01048045221348962482e00c0b41103024003030484500a40010185e42000d41c04140c801b042c007002540405103503000d14051080d80c0444c403441e0301c29280010000ea2500b0058161181901c00b000e58050040030010240d0700b00e4603c0f9000d5034017500020741c83c1d0f2080b50300e005071404c5400080d00145049004980684018010b1083d103008000e2100580d6401850508611040b01e005120303400520101000038080c1030515101e41c41400307150b08140a100303015084440390300041e0700003821038808010317a581080140740201025409040d40e140c1009440c11000ca040c40b5050103120000341c0000004409041400600402c3e8201c442c41501003000030048d0300640312000d104c8100c4e43c1c100d0503814002c0211403c03a540131300034504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 228268660 1250 228267410 228267443
    0x1020d0f1b0309050a0b0c07060906050316030e031210080f0a1122050a0e0303071b02060403080a0203130b1206010503060d0c2d0501093c03020418 65
    0x111101080d500b00c0a0116441000c107071555002d041c5409020f41001041e01d689503864158500f81e00ca90016050003801f42050040f00c0d403040890740d00034a1103c00749049900700f002100104101c0002c900c0f030380004100180d4601c0050380c55809504a002108280d5072030741a05601d0395240f5016546e998031005c01c603800030f4007190001890705401480008114440f4001c400140003800e004c29450f5503c40c20494803a0207489410100c070b01d000e0003907003946045000649800214060140c5070000e174001c0030119500d000844015560011240ea00d881e00b90101079a217401c249035040a000398900c0104004035018141d640cac144010720a02d10360f480703010040d01c1a50000e402c1300e400c80500c50300b00020407006000d5200a1074000788200560216458042400c41d0004e40c2e1340710f41d181b0040070851680e0000c4290241c074451604d1850194100c4601421715061807070200c40b00525030640e811000b21040300c101164000d4900f401100c210610024400314031000091440e4102001081c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 228269910 1250 228268660 228268697
    0xb1c23090114010b300109020d06180c090806100b0d0b0406031b05040905100b120d17090105090607050307200604031701140402030c07140c01020d0f 66
    0xd41140c11031000058261103202d858a800c84260050b14130501c00007103021460a480788a00203404800082c150440701d100d40306400c0180602c28102030940119254040001950001009007182410b03040100d1001c00c145003c0e02d10301c00340314081600d1070800110741001251a5214480e011845250b142c00d20b0440200d41d042207001130001d541d541114446902c1c0e910504000e58001c2c1c2d1000c0741c4100c030111040d00d10b211070300420f00403410001d4550003e000068022003005a802000c00d0285400000c00c05401f80054070071164454549071200c0c440c0c002c260b10510044200c000a0030b540c542082d0340c241e40301540c07420442c1e40054001030140384aa801b942e0002c41929007a01c0740a030b01d04c41c21900d0460300d5218a060381101c8180070400d030f089400c0f04052039040440400035031412a00d081009016030540d4021500003000828003550360f000ca0383d075141d001c1101c081400002061681d01c0d040e41400d41d02510544e060503807490700640c0c804da810405d40e0780f201c0170a80400701a2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 228271160 1250 228269910 228269981
    0xc070b1315020d0519090815091c091a070b010b090a050619031109100809010b030708100c050904050a020d0b0f2b240615200f01060b1c 60
    0x41704103c600240841c0c285018061011121070640075504182000e500d903600305040c00a003002c580c1e48426001d000c0302e40100c0b005c070485400902814400d8007200411005114600e80144444403600c00070500310902005048481e4003941d503140d00c5604c8006008031813042a1540344850b003641c410208403840b80e040314800440498010381403881190214040408828604000c03c1d004801c11191510900c5070109070042140100b00281c41c1c081220307100e40700401c02a2105848200012202e4060301c100c4090301c1d03014104000501d0401e13a03100003500220030b80b08249007404840c3c0590300d008081110700034001420300951502c21032a0740101111264404038188810251401040107402e00d02c0000100055283c520726070081500b08803140307504044503c04520b041c04500e2688a602e50280803040340441c070829403525000c1c0e03e055460b4401d99400e42c282030b404103040100d8805411820740c100704845c1201c203400f2405084d10001c110b00003c581c4000240807102c00c0b1041c11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 228272410 1250 228271160 228271207
    0x170a11040602030d0f0234050102130512060c0a050a0e030d08060f04050412120f0e0601030b01080601030b06040c02010905100204060314090c010305180109050a030917070302060c070b1315020d05 86
    0xc04074044110352300c00e400c0e070b0010010a120391002aa0801150804166400c0e080000754080c2803c0c0c945040540344501445000208001011810421140c001c04400550b408000c0403a010741240c0e44000b41509012100c181c040d51041c20200058103250281e40e010741d904c210400c43c1e45003582c074110707440b000b400300c5a14200c0d182d01700c0c80703d075203c540304a0100254501c0603262541c19402c2c030700d20000042e0b10440907688030300d00400114001120003a000401100d01044640074003404038050a480303a400351480c06141c030241d182d51050350040044a20075241880822112655001c56080c1180c0c4040150000c9040c1c43e2151b209a00c402e07072101040d4400001d0002280c4e1030b0b42100c490030720803101580032440f030105142d0404070080c014801c40815030340e00c150340240c0c0c54541074a803100900510303003c51001e1480606121460140882904913070b29036103416414011606103102c0d01100d0021107240d40000c40c03020034a82c01050303043e154640340c8141d01180030341e080d1b0071015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 228273660 1250 228272410 228272497
    0x610140604030204060e010302100c051911130b01030c0216032306240904020d0f0323090f1f050d1b080a0501080706170a11040602030d0f02 62
    0x40030005960300c0c4179800140500c21003c100940c15407050060752140c104982d014814046411400541c00107408000e00d01d5a1806c0c03482a042890440c512464541010758414206620282c902c060b43e4402010b0f1a02641c0612030b10050000990300c640c5807030920310340d20340a400148017041d421008808421140000d0403842e00ca900140703801e041d000c0e1040245020018600b13401e460381c121000d55000412649142c0e0f600301940082c0c402482d8820042a51440000754014540074400c415401d00800c0304403407220071014043c6485070b0000c140c15105108840d201c40550805541456038400b40021409111100f290195500c1c0c10840943c092a41c450100b159040205800e4080810441e1154000350810094550a031181604414826400404104100c6502c845004800300040d2100074071794071002000d0000e03202d1a203408105240004000032107680c000001d10703000e00c503011b0410080b14400ea00000380d00c100d8000e410102c03443d61014800402c50071208510240c60034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 228274910 1250 228273660 228273667
    0x1060f18110c01020406120b090606041412070f06080a1506050708091507140c060a030207031107080d0f05030f0610030e250b040302090a0527030d06060206101406 72
    0x541280c02c4e0381c86608020f001030780c803400c501c1d24042d4601076200c060404650b540090700c1d00002041d2140281d10407500c4003985140d940c90240c0320612807400e4ad14043c020303520403d80340c1740b090074207500a1185d00009018000050b081d20140d01c41c2c0b80340207078148509003500703191400450303040d04076a40940d051076080048403010383d130700c10f900c5942081a024aa0b00c400381400c00d0481000308c040150002c0e0040e0109072003a9481300c0c2142c030310025904006032941520701301160440060180d070800da2040c4240407035118800102c080c51001107590306070f803003903500b10308540340e0000343d1300b50700701712004400b0861500d0b1480c2c2d400740d040c1151030005620940c0d602910b1505180100303442d01c82c03403441003401580a5561203103002c0d26051000a01d0145180d002c1001e100000300252100da03602e10200e520082125031480c0300c0381f1000b003094a5040e20200d401d440354040032100140c185401d400184581c0040745041c40f607420070558107030707080c1b03011307214404441c4918140764003403000c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 228276160 1250 228274910 228274927
    0x91a060a3c080a030f0e0301090b06090a0905102a1b0611130303121e02130b030c0904050f0601050304020d03090803040f031131020f0705030c01060f1811 68
    0x10010b6200c140d000b5074445c41d407107903070b0b03007019025170058191180241d0401c804000415a4450613540207001984c080d2207594801c0882002010300c0c40d0010f1490040c9040001e0a2100790001e12010f00d0303d8591506210400b88502100c82c01ea803e21400b19601c200581d075000d080c03012100351140508000304446040c0c41c507100880c1d01140c00e885080c103d0403004c1c010316920540518010600da00d08102c681c2801c800b0795050011212034840d06a0006911030f003526100316800300820700390344000e459023400c0c0ca103c04240c00007007049000b1464640050442c22075504018001c00042c1c480c0307031858030340f9000d0102007291a4002d8051182c020400104581300300f004000410880e000131248509500e0f00b4188a01080c01441c403e07410340000000c4004443d4100b082c0e407142c1640c9681080c2441c001e28040d00035000c010342d041801003050810b101010000708040a0988020816a030b22039100c0c0180c41f9031400350720b00c0b08485140b0000c098440354030000301386000740040e03800d00c2580d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 228277410 1250 228276160 228276163
    0xc0612110705010c090b03012102030309030d080421201507050a090b0f03063304030b061e040903021903020307120c0f02060706091a060a3c08 63
    0xd1011140b5a64900300301d0a129408408400074140c034001c554515407500071214040300c0c0d5500d010a4140c80c6c400500110341d41001120a14180130341910b0740000148809040c3c11030484c0c1c1561605510a0b8280b680c0250032141241c3d030383e4549800b848251840e8800d02c1d007100c4203e940d1960f00c03445900f42c201c450444803007481181165a020350318200e40400800307401c2586d1144068800a000800141c071040041da54800ca003522002071004030050038907400700808049009122382c0c102c094216004580081099900882d100316254807200e0500410782d0500c0c46008100c6c0788584e2032030301c4c0d16050b001000024000d2045803900f100009915401090408080b005a44000f44120030080c41410504d0000007030300309514103a48a80b2140144041c114000740b14140000b644010081198030501c610f40c0c1080c0e0a8846400180d100221100300380c031501e10607a4001400110420b2249120042003450040000d05001c29120000040b2100502034a92070f40d005010079060030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 228278660 1250 228277410 228277417
    0x507051c0608010b030c0d080906041e0303030c0206060a18060f090b09070206040c06080403120519050a061415041502101107030804031413060201020306030709090c061211 76
    0x110000c00065071850400b81d942152107549815001344c00c84902e81d609a6182580030160746d0b00a00d03804d070b03100d00c1d05001441501c12900840e40c030325030105103142c0d41c81c3d050120310300f56842500d04002c1080445000d903a100007c40b28142d03c203140301418816059001d0608815001440c1e010135042d072150b14010081809400c000704a65440444c1c800e01c1c6002c0070420f070003010f1070010f0710740e90410b0b807107003070210005001e62014040da82c03022408161180140040b1030001200401c46c5080040e00441a50002941705513a079091801180c580f00d030502c100411904904a441100000d007014007180b03c0045902428100c010f00c00028412144200c034949203074168068050703041c0c0d1140c003c0403111505c05c5480703050300900c119400030350404103054009415050403249040e0014041156129000508181403c1c1e040005102c54054010310300800b001c400769154251500c4c41082240d0404202030701c0840f8003142002900d0140c0280f600742c110828000c58074001603001001e141c1d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 228279910 1250 228278660 228278707
    0x7200304060210061a03010e07020c0d11040f020f090f041b050d06140609040905210c070806040201020a0b040c0915170c090126010507110601080a020310050705 71
    0x2008143c0004420342c10b0b11803d0098011201c40d5118090340d0750200c041804140603035103c0401c204041004a8003c0002000051005094000707521852904078841142090200c0c09a802d055404a80300e040e4020b40b240c2e01120070303086090001c4141005002c22501615035045562420b40008406c0400320810182210303488490f51244600c1003003003218070ba907000400080c0784a00c14121695400300700d0f13249e440110750100c2c904141d030070154200f002030a070501d00c0e48800115511000c0d880b80c0074204203080700054501607607403500720f145c407031504a4000f801178010082102c00900641c84580d040303401400034201c4039480f00280713030850390a0f5004158614246400304403070740c0d801200c0c0070302e03001000c09000b001d00e100bc080b40519806002c0c0500d6000c8090f04081c08141204803d4000626040203105a0400032005030000d1540a922842030240d0000410404000a8017001142d400b50080803000c3c10034074100000c3c08098000410003078100700030420100410103015104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 228281160 1250 228279910 228279913
    0x1320c03030106032f0a0503420904050d030504140106060c0212191502070611040602060c0f07110105040b0d05010509011703040504051503030a1e09030b072003040602 74
    0x502c1248481000607880460421001c0361480740c4144a00c10076044d1148044031341899501c82d110465200110f042540c1320386070342c2181c0e00c8416102741402d15a110b0005071080224030344022041480301d0814111005801e90b03201c1492044118880c0d480507034054080c001484030b1010290071982503d8180d404280043c2c0e00444140c15440c100c1400040705407040c004081802e8802080b400340f8031005e50180c81c40500c0319103050309076041d80481e000707107601c40820440282c2c02c0001401517040360190800511170040001c014545480440d6041c1c2409900c01d82482141e61310100f4050072040c0d014100042400001410403001001c0c1810143c1d40b90f0105d032660500c400d00c070045805030301000e4484444402c1e0350244030301000b03c6069410651b804100e075607a00c107105240440d4107a800e6010b2000068501103560b001003020103d0300c8110b0f2440b50045c08480850304042c240c00050000185200440c000d10f00404400e2240d4002c8846101c0d000940245c030b0741142c202c0e61048015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 228282410 1250 228281160 228281171
    0x19080903010605030619050109020a0219060b1503041e02150304050a0c080318191e0302180a05070e0901050f130606090513061a0315030307030504080c01320c0303010603 75
    0x780d0440c050180501127a00c01141403061400e0000e5543c91946442040e091040c80ba1a00303001140d003150891030400340c59040d41002032030300513070035078421603060341c0c2c2c0385103400714041140c19400080410b0750014941295064130350b4403940346a10180003242c0e00d1283d0140480051070006550000b800540c1c051a15540808a00f075410000001154403469a624854611414407001c02c81540d44a209100b000780c580ca000710b03210501900007a42c09144005c491407801c0c02d000c603d9100b00e100d00780600c09074450307031015900c10018411003684642c00d41c0050045043c0b00d50702c10710002c001070003500d081102e83c3c007070b504403029034104030b0000300201014055411300541004400c0040b2790108580d61401040303546481c1a0040390b52143d03c0040030032500400007219160740300d07000381500d6403003c8600d005440342e406031080b20300314042c2006100c801c2d070017100300910702d01540304002581c4d01b00740d1112011411518600b0300b101c0c0103001628804d20100040c40c0a01020b49001a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 228283660 1250 228282410 228282451
    0x903010b0f100c030306050603040606060906030204050109031e06110306040c05030c030a0203130606151706030c010809010908070b040512030108100506010c0506090618190809030106050306 84
    0x291280651424000c140241c40e00d41140ca4684258150120314544504483c0d0f0900c4c04402406055101785e034000c501105004c2400007990001c41240d00310340350308029039035912050742640a648142c44c04914110f40400100e81d004407034950144c00b55004a810700001c0e5550ba044804a4400c50342c581c1f0048101701035030501e03109144944c6d0b2541072007030440c500003036480080d1100078180a9115008004168020b0190042e0145203074011004d00c40c090b01d660105102415098004001440c0d5080b401019008161003074000d08000d8041c00030b21b080000155504000a40300d6182d40d0750710340b15400441d4240020308039003441340c421013045c0d0410b0300300a8603000070040a0441d1241c00c0004002c01500050350025241d183e01d80451580d46500042e1423040704403074050300a001c3c800401180510100300940320b1100140354820000030b803020540d5a0b190140171240c40d9030030242c0c1d140403920b65409801c4441c802400851603542740c0003c24100641594802c60108010310400f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 228284910 1250 228283660 228283663
    0x11410140445230a0905010e100507030506090c0a1409120106030501060e161b12030e06070e06041806091d1212040201050c01060803041203020c0a0f030209100509010b0903 76
    0x40031021074207104004400da0403a5900080d4041c2c4003d05545d500c945010402000f0341020801002240c152405904012000d0010b414100c613030100080c5040002492858000151030040d03400245d030a041117502d00d003e4074400400c0310a007403085020301540c8000c3e036680c43e010b4002c0750004000319903035145103461800c1d09c40503002801c412005504010402c1c0110031101c141c2920fa152001c43c801c1c6448a06400c03011480000d045101d40590b20301c50b458140e000784001c01110411508144d650440071140c01c00342111191b0710000800c000c0121a0460340104071001e0a07000016040396504440001c6030f0304880c48a074040c1c881c0b20010b1103661300b44408c008017a81603244034502842c00100b4005134400500c0281404000314500d0340355a02503002c00c014066090032a582c0c3c03030b00c6001c40056241d13240c204500601c40c440e032288403420320342c2c1c4140840e0340c07800712880d503207045600700400007c00074210f05a001914100052035600d2101140c001d0a10f2050956074100100516 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 228286160 1250 228284910 228284921
    0x605010801020304112710031e02030717030c100e06070c08041206021b07140a0e0a05040807080d0f0e01090201020c120307050105011410140445 64
    0x852164414410000465034800001c0482c5600700c1b04440d4078400d440c884103840580c41c20b25140208200300b0000d800c64008026019a80100c480400344200400000034812035980c0080d01604010740401c1201101e060641001740c07500d09503401c01d080032642520380401600ba003141c683c1c0710b04145d40d0110050007050b80181840c0f0705141c1105e2551581d601c2071080e032050b55500c5110700201010700200d503064984d01000c140680c0c506095100c4e001d0758409090040906182c01200c04040c10f02e0410b402508032061500402030907954100d1400040100400a484801e0100542d50008401100412945404040000d81d81140c02c54800c212040c90b01c5480c140e80c036050400c00582e0b00000c042003c0b040031078944a9481c1c0b40841d040c15070041010050044d030a01001003152180781c038202901c5407054030741c21540c01075035408590f903100703203021148071200030002440591422404a05906070080030075003a090403200c5540400c0d00e04480d44284d00c5d0620b04c0541780140c074001c0307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 228287410 1250 228286160 228286169
    0x105033d0f0f18060b070b0a06050402070506040219240f03060e0f06011416050d08040f0b10030b010b0904060905090c0613080d11010b0306040f0204051005031603060501 75
    0x16110001d08065040395036054a02031140f600300e41100420440941d60859806006136445d60307606e80c0402d140c01c00c102c40b0306840c040c040e2414000c002c10141082c1c4295100140c010700240156201c07034090207040c01c0c004a80c10500880d52401107080d003004c0d51003001180c0500b045c1070b03031042c042070000c00b00d4490f51301850405040520401c12108001070380c940100359400e40800c96164540141e6812020311a000140d02010500c0d0f0744c3d0030410711145100901400a69404075541442100c2c105800c803001840801d20442c0c460114800001c000d030310150380b8a101c4901600d030b440720960188240e108440141b00001c000d24203040c940545801010050400c0c403a50406041c016140c41c1c500c04100c0c00f800c03021a204d00010072496a403802881901c0595103103880620300180340d00c4080416140b0717503007080751140590070300041c81c604c11a080075224155159a40c2080050f2401404082c041d00c0d600d1350110340b50340c0921020407844010003200008610b18600442500c1050f8071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 228288660 1250 228287410 228287429
    0x5070e04030507060507030b0a18151a030c09060d0e1c0f0f020a021002060402120a0f030311090a060503180613020607020a090507050904060506180105033d 69
    0x90100003034001c41540c001540c016030105d059074a4083c110000c19054001c5031340308413034000014400094000303184040e05668014405080361040c2c090070b80810b40b04450302c0410307941000c0b141c40400c0c0081c6410000340e0001c02e2800c0200c9000031000e0308140c10b4800140d0b41c0f11840361b0512810800541884201c09159000800400c0041c200c4028007480509009800e811005400c2c803d22901170403981c018907401c3d5626603480300940e180b008807000c03401000d17040308203803c0010000f002c0345003c0c0d11409092220b41c07265411030162510201000300e51400f8090041c2c00c0d51070a1045d80038101580e00c403070b180c1c6800d20240c000c9500c82e80004680b5000b0000388074002c8001450203100c075405a8080e60741c1c05003440480d60074090717507110100e003516100c02d101300d0350360007002000600b40032281400200d072034a041045904c2062940607480c195080c15213101e500482c00303164006480659036450700d00c07801503021075034056060150b1002d4591052100c004140c004003014052450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 228289910 1250 228288660 228288689
    0x30109060815060f030c040603080d0c140409020d0902040e010c02060c0405030a0209102106060f12060e031606230106080408220314010b0324090a021503040507 71
    0x40206081405030040d8000d104c0c0c240c8241da03a880800481c100144041c0c001c002060780d80c101484642c000b44113181105080003250003109120720a50550a00e1180c100f91415103044289402507006104040f001e545070003805000d65250b00c5140354070030b0841d002040351045504003c0c2001001000c07940301d000300f40010710180d1400500b00c00943d9064070a04000d40b01c510f01122102e09030b50140c50480900c407018408000b140019083c024403480042c080d1980318001c00d01c5254050090136811045020b001001c6042c54200003c10640c80003030300d203880054492030001c0506c4503820398600c1c1d11801300b8040c1340c200c0303081d44103011501e0200f401c880d410004024030104000d04050b00c401c60110f02d19241126051000032410f19070500102900d0b542c0c0f608826880300d1b0303012280203500c1d101c0c0c00d0f205400c0c0803a022000e86200b00045213480410802c045859201500800d00791041d402c05200523150321010000c0e21180f40c40b42c2c1d803203140501c0c0081c540321498210403e5802c941c2d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 228291160 1250 228289910 228289933
    0xd0f030204080a240603140f07060f0507020d06020d06050f040b06040b0c032a0f07060801051002010e0105041112011a0f180f07090603020304050709151a0301090608 73
    0xf01e01c0240300e65200400c02c003c514004d046144407400c5000036180036180880000820840280e02801c040440003901d5000c01c85024a036200ca00340e100e4400400d401000c80c1c1089485100189041d03880108214800d04503501c9503012a0005120140a04c2d5281d0080c4041d01d440180980701250444060109102e640c0100f03e603400f43e441780e041c803101e011a4503101400709100f5501508113200f45045907002113101406144c0540b251140e25001d0143c1a0030120717400300b80c44042d9803883c1c851041a92138007062056074010458040c00319547c40c9040d19071a0800c3c040e40b4095070140340c59a00c0140c8540800000d88018184030001d030707261440c4c0c004484c21118a400b9040801c840500c0b940d80d081020506211076414801c000c410746404102c0141d02e40f2038000d00501c070550361038038001d441e0001641288010388010340550701c424005c01c00c0703203000d03080701c800700741c00401581003180c0d03480b0b03840e41141100c01000710080010005004201c5c0c20310408000b1310300c80d8000c10710030410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 228292410 1250 228291160 228291163
    0x100809150115140c0c0108040201140a21020c070522051005120607120f0209030102031e090703172208100f02040605030402120f0d0306091104050102070b1c0e0d0f03020408 76
    0x19105e025042c82040c800080c01c0d68040c44250903c4c0079a290344a550325401c01004015001c4024580c2d000102240c03002c01d16800303403080d14400680c820080810318181020007206500e03031219400d041c810380103803818200080c0946405240c2c80c56135000c0c1c0d581041c00708003415030200c0540c641a40298100710040e6448800042c2d05000c1860006180c80c021643e003010344110324030a501980004107200b464044804511490080400d004a09848406086031195802c1c81f015004810f0b00301c20800c61007454000b82040020810740c1011505581c0140740b298113030f40c4c420030383c0f50820740390840200028000e0040741c241c451401c600d002c0c244240a0114007000d0000b0303001d5008a0012044018100520000303031400804959000c202c0101c000c2c05469580607031043c05052414102c0520700c25030076030b010742d0016006000c40a043c14500400360b005140090040902d02011044280c0c551050550802c001009007180303104040001c0c050502e852040c408140c4100700c1040001030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 228293660 1250 228292410 228292423
    0xc0607030f0f020a02040e060f09030c0c120f0a050706080703050c03070c020f0a0906181a0d050c0603070f110616030b06040306050a0606020d0e100809150115140c 72
    0x40c20250380c07920302c40340101d00e070070302c120070094126150503204180314000095a40c0314400300e85022485a83c1c03065201e0b224050302d8034182c1c00d070748403440c015071a24003101c00010300800002116404032641d40c05510b4a064140b040d9403a0b0810003080c0050ba40c8240415400b00700743c1014025410501c034100d03054031004040b1002c2049141d8010b00310b41d6440c0440c00c58410080003120310325150344142008010600c1049204203466134002c15a134124055002191a1801c114440b00c500c03c0900481070003450b4125080d000f404c290803202da40e084061805400c0d9540e41c2c41c0e52510b00c041c05040e00042d071f0031444444c5e20031010408000b07000c814cc0c2d11030000c10725010442004c5500814114002ca42004081a08190800c0101c04041c3e110304102c900b02d5003169040c41c4045070903204032001400b95030b04141071602030340350341e030040302505e4000350321000b200ca026900c2864514000000c1c0c00030402800030120010b01d580e4440c010602d441346003500c40e171501141e030003030680e03801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 228294910 1250 228293660 228293687
    0x1906030201140306030a12030e0f0109020303040311061303120905030a02310501030602180105030f0f041104021308070815041202070506040902030906010609181e0e0a050c060703 79
    0x10b40000004c0c0b080d10f09100707004040d584664402c0310000075800190140c6045280c0c0d100c90f00c140c51546503140d5050060701002a000f402031464035095031a42101d600100480c4c580020301004025490b038811054200258009d10320044120400380006000c2801c507032203144241d0080c0c040e01c015030740d04c1740c10b400388500464160b482054a01c6130040140d10514a0f0310034a49000000024410175800030720081030542d001c0500f281c0c05100560380740c0020b5455003250404900000c031104a21035000e900326002d07550660403800380500150680c0d20000301e443c60440c000b0780402800004004800c054200302016150321814000f2113124000b004001030006420448074282d103030300070b21186002d0310002e00215a6a51a440c40302c0280d0b00c142c032400000d10417400000380c814407405840c01990861201c0f0720001d6804949600646000325034421030300e5402c13603c0c2109158070300c1441c11042c074010180900b5469402c007642001e045480042c0249020401e21001a074060180007240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 228296160 1250 228294910 228294947
    0x506151902010b1206090f150103060b15040603090c1401022a031204060f05090a0605031b1b070504050c041e0801111902011104120206211906030201 66
    0x1044101401c901400c0719502250304003a0240a4903c61040420390701d01c43c040301021034040b1041c1c0c640d0740d80d80d030012441d0021140d000200520004205030058031510341c2c0180280755403042420881e013140d0081d48000013090395444681e0802103c544405c0040803804500105501c03140d0010351103000c8501181c242c10440000344074036004000700c000f0500f9014007140c0c940403d22800c061580d00c80d0007241e0106961881d0300d42c20750700c2a0300700c07140715101810103c421480c20a0075070301130f0805850b41002c2c03c4002003146c1800c034418090035004109032266480b000c1069202414803002e50071450040c0c1c01c003c2000f0100e04c480c1d04481c2110080c4c00045003103044d140405100290320f0308148515400c24048c581001d01c241c2c00303000518401480228410b0b82118240c1c221250716524510085c810301007004125021004029800d0000d070106c0e140c0ba01c0340c03014400103061000c1c00488044500188805104401400c00c04071054070010005a4110380000e404080d29040c1c15184 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 228297410 1250 228296160 228296197
    0x13021c030203030c09040912020a20010e0d080d05090304050103060f05060f0a020312090106090c05070213111e030103030314010e041e080d0b0f030a08040e04020a0b0408030409050615 81
    0x2146c686500c00142290000c010948103406008025101c0e0302c1680150b0380c5d01c070408003a00840b4520744250401c800161198000340a80c8c00030b01041c114210010307540b610050102030604240e40c045c1c0343c40b036a6910040c40d27486062000141c100c8034181c100c103050443d192024070294507514100d5041800704810309444102900c012032a5210302601071060000141c248405600d05400140607905a40340a00c000301300c44008072114001c51201950000401201107101000c640c840b030540354501c0360903450480f0064004603940d80004c111103041000100410516a00d480768968850214124244035494140c480040600c0a0009003400000c1000044521100b00090101c00c0d8400d440c103890703442518600d001002144405030164989058482061901042c203040c1741e035000040d2400c040c1031400c001e0b03100c0002041260443c0c00b40074085180c0401c80081c200901c80034006681c0e076803c00607828180c0e44060940382c010b001d04090314450440000c1074034010610704501d07104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 228298660 1250 228297410 228297427
    0x1e050a020a0813020f1509130e0a020f0415030302070801050601021f020d1404060506030601080606030d03110403050f030319060f12020a0e1501110303060f011b060513021c030203030c 81
    0xc101200911680100811511b408899022018181d61041115400d1030070400ca05580240ca20025240c0015000b01118400500c0c1003c403d01407020302a0001031040b8064840d0b0b959010140c00c00c0d00580c1c060310080211080074000c0c142c0c480001e10103010107020a8503102c03400556a960500d80d184c000c91000e82054840d4030540220602151120b080d08040c180100100342c02e6076208c1c004d0083ca800420b0000c40003c030075006820140041c1001a14888124000c140d2000b599903452400c20000000c03400401542d01c405d1011303c05107035281850701441009014407030280d01d800e4100003003008407010088421040b50640c0c00c440751000c1d4180700007150240c05411040f4248005c1087c4500500c1c0e2101c6401e9003030080c2ca80b0084010031090883e9640000c0b078020368060901e0302c4900e015480b52002000200c0c405130070200d220700c41d80d922019101c0440d928419100e54003600803c2d440c010903844074492013003440c10316840840e1402910307840000d0003c03445140024200e40b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 228299910 1250 228298660 228298669
    0x9181e1b03020d021002010f0c0c03020d08071209050114090607090608061011010f0f050702010605090103050d0302071e110a050603070e0f0607060204031109010b030708040605060a091e050a020a081302 89
    0x3010910424030800641464440150070030b960004150b005115541c52005000d004041490041c0940c0d00c0342e54307240c2645001071024103ca02c500f2a641d540f03400c00864a0503a0b041064005c01240000d0700061500560040c0041502d038000d8003000b28030801d01800d5102c045058803a60b5481c0303040700090b03001c0d4030b14901500340c1008800110340f41103142000c4044c2c0340c0c00207003c1c0e40c2c01d50081c024140e850b820001046c00a010160190304040a1400190302035401040383e02c0c820040c26484001d0010304070030640d00301c80169141d0010103003a01940c9081d00300e00000d058102c1d02c050179421304031801020000c05851040c00782d414803100700050b03030341c03802030b01c128541c88030080d560b803600c929100002c0c683c1511014000e819920011802c02038a8041d030b44144506d581d0440c080d80c03103803990300280c240900180c0d0024005400402c1804560051541045400303c0900140740e48400290413140010010840c0c141f043c080e800e061640440b0302604610080f110120519030b900015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 228301160 1250 228299910 228299921
    0xa0f0c2604030e09090105070e12031c180b010303030f1a12070f060e0a051005030c0d060b03040f02011205091b0307091d01060602061009181e1b03020d02100201 71
    0x41d03a104c21a03a0030030006190541160b071240401e5a14004142c0c0e558050000071050401502034980017408000b6440008060140740b45018810105004c1c040200061801c01c000001390b070180102c2c0014401d0581501a00c1e0846c07800380004c1000d40c3c101c4000340d2003405201e040394070481c002c542c07031415071500708121000f03401e03083d240549041e82c030351001e4609000d4504403406841c032084001748510f80032103101036038100c0d0b8642500d144c1d07445003801003583c461241201c00d255a2040030444024080103144210321a000c640d885082d03d0001400c43c1140c041d66041c0030741010100503400201056000001c294420340e00c0c0340c40e141500007400d020030380d08a0060300f40380117440000361070009503006000c144e110003007280c1174907860300326101c4030304850300b00c1c01000d1224104050443c13544402c80c200304000d212003050810b81d030b905482e20005404a9000d011500c45003052104000e80640e5088070b8807100c0742740a04c0c40e4042505c41c2c0880307402910825901c44848521070007900507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 228302410 1250 228301160 228301187
    0xf0f050a05060d0f0c180e040503070803181501090518070b0903120c010902120f0d050d020c0105010603051e100603020702030a0b01030b0f011e090209180a0f0c260403 74
    0xa00200c855114010508100c2800308103880350031800002d1147c2191070310502403608400036515240e1951140076103544050044030000c54401103c40041005200304100c24039904502051940b43c08502d0f41524005840c1444a400241c1e0b0300c15503a00000f881030440c0c1c001c0c0c1080e0b40b1000345500103802c00442c0d50002c0e4a80314000340e510119001903106c08402c41c402c440c2d020799192496942c42e41c40c003034403050b04044d070f2002000652080c0a10050410510420300252600f03030710b95103440c2590420390004000c6525001071080b01103036201440c1da03008102d81d40080c0e0f07103000c0c404505034208600c50542810f03400560441991802c1c040f064046400c00d50382019942c2d680341c1108019012696041d2403056a00042501c0c0200ca01d44480e0000150741200c4e01410104450001c0d8450101c0d1b6500c040c880540c40301e00f06450034600e100d8040e8410005416144a0041c02903404614482040141120060826250041d1685a1038501c1840c1c01c019540c1c6182c00c1d190035091005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 228303660 1250 228302410 228302441
    0x6140709030209341419030513142d060408090103141e06120604150608070f051306050a03030819050f040606050a0815150909070f0f050a05060d 64
    0x54204505212115900c401844d40e41c0ca0480c5001c000002d1018011720817488003001050f5400e2903001d200350003c0303402030700702c810342c4030800015078074805507007882c0001c031035143c12440e00ea41074803009004100d03202d0072108001041c03420300c0768010f03220100107200419200b030200d0400707503d074400d50011400c0107030454180f4007414a40d521a01c071080803c0c0100070a415640058402d041221100d400c4203003250040441e916266104401d022118503100c41e200e071364120005030403108101030801420380f0b607a456080c03070818041c0020b800b4000100c0d8041070a100c0304121a4031001070800441c4e130149416441c94607145001d03900d100e08501400c0c3e8003410b22007032101c81280c3e44151030299211300c17003c22400e41c0d40c000784074a0748000d04c01e007107054006000290402d00001e00d410780c080000c0510b001d140d0309802c00140d050101307903001e05444d4400c00050180039400211040a040c001402c072900502e403d00107000710003140504d50003080040f88900140c1c10540090403002810792 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 228304910 1250 228303660 228303721
    0x311010207081201090f0b0d03230d0e06010806040302060c131203030606120510050d06140f04020a080c0f12030705010603110f010305010b030a020912030a0302030406140709030209 80
    0x1c4620240d000f0a000e00429213250400c041c41e981c82e80c0c45041e08400d4040c2441e4030240b1191004e403021440c44043d60310540d0f039101c0450150494000901a400402c10005014000110003524040050b004140c1945c0700d0000e000100360001004c80e40002c2410345070348e4071818009003200d010440e5001102c2c60058410500070950190840c905450807a40c1e40c0358951202100c240c166001550f00340d143c808004420b0015041100d204c2d07914a0180a010901d55502822030396144030032640d0303802c0c0355003240910085203000108040200300c4c00006003a02403400c4001140000c1001c0518813883d40d2100001c24540c0038002d6402d090b030048001c008050f524208000701c000203040180c0b103484601010754440d0300901c5414141c81c1505800340c2140e80d2403200b82e0080d130226512039440340c0c1031502e058404000700000c20503013116a030096140d0900f03240070403c0e15501c0c0317010f56292802c842009210f541c469083c0742104c0d01140c5041c26610341e400c40035801034140104842862010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 228306160 1250 228304910 228304927
    0xf280f0f15050f0c070209040312150807080c190b1b06070c030e0103020708031504090807030c0b10050607021909020c01020414030a02061204080909040f020901060912031101020708 80
    0x15480107108011044100049070f68101d4848800c0c17151035402544550a2408103011070b20881c0d407101001480b40c400a110201c60425200407a00d0303074070031340450348140e10a20200300c00303100641b5140d5041e201100d050400f1040104504d40d02c1c0101e8110850104004080c0d40701410000c1c440514007041d0f400300c0c20311540040100c88022002d8000c214180a1100a941309200311080c054200d05000c0c11a100d10900b1034422202e20300503640282c80f005d40d80081807443c8000c2604070300c45c6d12801d581e58041e240059501d01c00401c25010207441c28010032407612103e0484040030b6048404064400c0106a010700680340c5421100c5424800b1801c124018015401403080d5011001d0b42079002014004265884103401e000a40240c070138020a01540010000f140d04644200041c5060040c00000302e0450b040454050b6808403840002c0300c150b05000007040e001d41794901d880c01d052401c100700c902ca442d072509801420005180c140b944801c40030340c15100c102d640040140d64910700c0c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 228307410 1250 228306160 228306203
    0x12020a0b0a140c1801030906060902030910050a060302060906070201121d0f010c02120a0309021305040209090d08180c0904060c02060a05010510030e1e0f280f0f 71
    0x149055844184030100101d045990600c2c1a118114813208031580383c91561801180904105c003001c0f00e8184d21118040303107241013400990300c038240b020001e18468018503404015102c1c05014010a580307440b03014400350b264101107940c0400180e466030b54034112440100d803071905280c903031080700c0c2c9030101100c48a100d00104006d450700a02c01c4900000c4410080b034202c81c020b0f2901c41c05a4000604440c0182480000c2c1212a0039801c0008a401d800c0d00402d04030031542c2d41c2419695598410802146000107259030426110001007050031440d0708054240000901030107a000e203140c40b1449445010407804036140800781480b400f82c281890108040e1400a1a94000d8012070000540d8540c06102c1d0a0403200d00074045104080d4068003070f03009201010026000d8012500d40c44022111000c02801c400407a800919882e01031802c01c505044844500044103441c150400d070b01462501c844c489482d07080380c800001e00c1c1c0703546080d000c0c0100f040b40040200b805c484228146129 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 228308660 1250 228307410 228307421
    0x5010c080108010c0e0f09100b0415030608010e07030312060807090e010605031609020a05040b030403020c031908090907020a0b0c04061704051b12010f060f060806090412020a0b0a 79
    0x807801e00030b22407018004030035610300b0085162a13401c624916030800d154130342006400e8010308d002c8000401035031240541c160030b0340039405c0140010b2000c0d183c50070007035152081d0002440ca0304020004402e030401e40382e0b100d00b258400601080310080c2c88500f101c2155001c5001091501c046030300085e5078200500250030300392000c0300b0329485c00c1c4000840d800c010420206855a92440e8000d09091843c0c04009400845086040000034007010904140ca00000c6004034020f0b0002e100d040103003001c2600d004564560b2038801c001c41414040040c002c002984c0005601b100d0200041e0340d00ca20480c030700440000060401031800c020320000c03c01c0e100040c070580b4610b60707a203202e1b00580038000720360304410760300241385910094111006048100040c0582e00d801400c1e207100c00610301c1d90b0350175120350020002d103c60b03403000f08000700c4a42c061054014400d038100000c1d585003000008540d407500800203804005a851480d40b818420300400c1c001a41c0300200e000035080280d0020000c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 228309910 1250 228308660 228308669
    0x2130e04060605030d0909050a021902030c010f0b0a03020d020303090d0c0e06030d08130c0806090708060604050601021f0b0904080a030515060a0f0c08070b09070614090d02010c05010c0801 83
    0x1480d102e404500c41c1004550201440c8281e214010441d2a0883d424002c102c010141109198203002035000402c0d40910805803540640c01161608845810b01d42100c50381200c40c0c184900d4080701c5025916402c1400c01142d4045800003440c16490003c40d00358460002c140340d10107040c00c400c01c1007164050644c01555004206540385650341c4003890765600d08038621001040c0703c000000d03641103a03d901d44034101d128000080e5901d50301e0114516141060b909001c0384e03006510240104c100c02c00c4560f0740808111800c2c0014104440083e440d0740f401c03a224420f00501a000b648480e215411003400c51034040c00311b90841c5441d08018a1603048120143d0019040c0000300348041e00c4104240d00c07413800148660328040700c402007a1013281d03d942c051003e000340700041a010401d42009420128022850300f4118a09012068104039050f044a010702203000301100742d05600c3c2050f02c060000c240c0d0006042902400166000c20801000501d15801d280700c410003e94001c00050485 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 228311160 1250 228309910 228309923
    0x61803090b0f07060b040f0e01020a1710120302070e07030204090b0f0a0b0c1e070e06150403060209041b0c0b070c02060904090303140106030e0d05180405040602130e04 74
    0x180e0301c81458002038812400352841d803050a10050001ca042684504a45800108005500b680c40740c0786170295280b81a1081980e540400e0351001550020340315100c1c0e941c4a03555010780d10304000c80b00c411564a000c0c0c0c1380e208200841803803c040c000c1001c0b01c09440c401d0550801482d0000c00100a980103000b410320380e078102a1040b589042608902021610080c418020203051402d040031307940046425007a03d21510880c904c40d40c4500590b0082561100301070200e0354104840d074000c020016012038011815020f4610400c0089019542034a500038000340c3d98a4180300001c1c007412080c8a4945401c00100410783c0181e0015644646180314007117585d0242e60701a01a00c2e5525268400b80d0001400c0145040510f440c0d400140000c1c464203000034011440c00c4c02626621098000102103503a4103119181c1d48020000452000400e1516a107088600c009200188100110350750080340c850f0041020083c0e950141c44032a9002884035a00719030301c21040403110704c00d5070701b62402c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 228312410 1250 228311160 228311177
    0x1f1a0316030c0507120e0607030302070501050c160605060117090d02120313030e030132060609060711010c120e01090506040b160f080a0804021306060219060207061803 74
    0x9010340a07500c2c40407001e46a2a040102d1901c0329510b110300c440baa10700b0080042c0781c01c102d5541d014040c010482c02681e0042e101c00107483c0c000e017140c1024001c83c090220038400d044d589440c080000c6140743c1d002c1408a551740f00c07900103a40c1e5007000350000c01034000b00020080c06540000d41d03c003c031149a400c680f1500303585e07842d490b603c0c442640c2c20100920b480041c0e1b07001c01c2c000c03101c428040d013020307000003a2250506440480c20114040e02010314445100f0210083e02c2c00c407540d50040e20480c1c50728503044419001035081c3c450807400404041d030701c025519242e03002d43c0001c0070054101440c09140c02860034010700c80c41030044024041785407a000440d0741d090a8056406640e2042c01d07542c0740440030b14643c15001c1c0041822240b082c00c5003a50030014401d000502100001078a910310345080600c10020300c1c1c0240d071141c2c04282e00e005010030907940d00140101c0234000041e44013500b1641410020081c2c03181c2c0101602e803030309040b8403400144040000c890708038040d0b43d40511 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 228313660 1250 228312410 228312451
    0x303240a090c08061005041205030f04030507050102070605040e0f04020f03010912030e031c2a02010f0b0909060103060218190e10030c1e090c0807120b0303031f1a03 73
    0x600e0b0340040e01030001b450503c8184000104a200d0340341c880e0140084034184061080404041e50154204860310b4011000400c0f03a540c040100d10058903042c20043e00341805d1520740510804001d0131184141c51400108007035480707400c41c41c0d40e4004090300a010b0000d441c1403e0f0000040b43e198600081d203041c1c14180c0d5410080142c3d0303c5142081240035000c000c0014440c060014171214120f50b265004000e1083e40c10003500c040224040d80021521b000205001070032035440c0310005002c1c2551000b080b00403180860b14a054a5001c200140c031160204100c0b1000d60792040c605402c880102c0416040030341c0030441c02c04842c845404c5515958400d07410300100c020901c40107001c084100b001303001140206840030079400d08442c0c400412a80c6000c0842030750846040100131400ca50309000b030041e48005104141ca40400c010b02c43c60341d82c000880c0e90781c44010010003144a080030031107440400140380000800440320060b00c0c030307034a070701850885a102f40c4860850b0b207084594071a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 228314910 1250 228313660 228313669
    0x8060a0506070302060f060f2701060813170906460309050c04050a020c0c030c0f04050408090301020a11011b14090d0c08010e0f0c030303240a090c0806 67
    0x160b40c190700d0b50145c0300c40c0e1912401c3c2d0401140c00791069510540b207080c1a484c540340c09001c3d90240070140d01400141c1c800b80040d039440314040c1c00440400403981c0030446c03115210140841c0c040e5010003c400103002c060b044402900500714026071208001626803003181c1411000e0f035080807000e820003480020502061036000c80101405440902a0500e00c826406a40b02c03070b2006005609842e4000030180c000b60440e48100d0300382c0c0c3c604d0750103d21041e604808210002085030b05800901603c1d6004000030b2402d004061501d1040c0d49a1000904200e040c0003030b20344842d8094001d5442e2003030301c90041c200e05001184d001c00366103405d0b41054403c0350924440c080031301d00d4882c0480300000c000c0345500f60780203c06140e00b22030b05903041d00028036034507502d6004011840000400100d208010f50502156034241606688071150f410203a55000c02100e8200741806801055406104d01f00100c41e200c06540c02d43c031100c003450002d207000300380d0086444000283d44042103540c4050411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 228316160 1250 228314910 228314917
    0x2091e1306050a06030c05120703120801031b060206190b060d02041d06090c07050309090a0c0210050c250b04030509011b15021b0a0c0501030e070602120a03110a08060a0506 76
    0x1421300c42d21401b0800180c1440c2c1002c800c0d0803500d00a42c0c0d502900e94480d4852100600410800603a402004105220341c2400001c082c01c5604000200d5034944100299110b4029160404d102d81e0303d00705901541255020044002002c1d040c1901d5401905c0c614000350013030720541003c2c00194844140581805410368411000288000421380f680000000c090304580011203552104100c41c2c030300c5a07070312480a40314409a6901048941120700001c0c01d04103401011410b4608103410b10041c5e10800742910086100390078101c203014605186900c071104241d40241c80040d0400c148400d0542c0500240144002a228114402401c0e44900c400c0c0394045006410241004542402c011003a0000c002c1d42001c8510740028a820390940c60801d924500c046a00d01400c0b00c00300441c2d60540106c2070101d10711405402c203a8913001001e900c0c0d00c42c0c1105150003040006481d0001800fa502c6a4804200c1070001511520f0356540904085401d8919900c00d034a5280f00044502d4403134102c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 228317410 1250 228316160 228316163
    0x106020303090a0b063705010323040809060d0b1509010f1202090303120103060f090c03080901120c08060a0f080309060c190807210c02091e1306050a0603 68
    0x8100c0c10307001d501d44070702c3c03441c001d440541d2214510b00000c1405900c00c074010307142414039401002206580300000f4009a043c7c1c090780c14141428100d003200016039070b110a4036195000b1002c0300d6030381c520b840001841408a0140d00460200314410075407040ea01015180005592176032100c445141341c160740d802100c03c15030018031000f8100003440d104180f1150130182c1c4450260520380039400017401c0d900840b20614406405038010018004076019400d49c070020090200101140794880040d0000c1900002c2c01039080096144006c0c0d102e9500d54082548195082040c034801000003400d01d0340c2a990180703c0d101130070f00030800911250b420011a0810001113292001c0f4009202c42d0703030010700003010140561001c1c00002c40340c0d00c14011415105886465440c3c03d03a14041d5498a11001c441c0c1400b840501031052144d082000211b156404030b802d88044d595114440001841c4090790308400380d000310500031008500e40305823840324800d0347c05006590740c26184404850b002e100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 228318660 1250 228317410 228317413
    0x6071205070c140a0b13050604060c020a091406060c120301140906030607080601031e0e0a0b251d041d0d1103040b09031c2606010f030b012d0206010602030309 70
    0x3001708020600c02041c100ea28800203c500a5840e4001403060304203030700050200300d44540300021403804081c56400713840403040400c007100188070480800302d0001c003118010140090310654103130081006100c200069900140d4940e107400070380c8114510390384054020703000800422014580800c500b8400c480a50310b101aa81c0c4100c0114040c0c20100c3c68050903499600c800e200b8070762540225201d1800c140c0041ca44d1240300c0c900100c51610040004884458868031300c10320483e04030180803100c1035880d0100041002c40c440c0a8405038034981642c0c81450b040061222402c80ca1101c12500d00c4402602c0c1141e550080a444866210740701c0c00560700308201c103202114056020303001c01e4070003804840f00824003101900302407405421200100c0d0302d841041d1588111040b117400b40800c0c050f0382c40e201b400c00c1c2c40080c000502c0c07401020700f41529190014034691245188a186040241d010411440f07104c86840b400400d10a042e40140200f90010940600000803a40690034250 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 228319910 1250 228318660 228318679
    0x10e03031308280b0402040b0f040504120e010903200a08010207030807020c03010b090126031209100c051206060c1506041503050a0b102d05040501210206071205070c14 74
    0x40c07c100c014507441861541c80a101450796026880300e202d803c0c4111300c103000b060a01c2180b91005442001c1c400800c0d070400490399030600c000344203002107480f02d905a060120000e210040064003403125504088401e610100310182810313401490ba0b4010b610719001d43d494440c5140a0500baa0701c07904415400082c0c0600402c10b81e0030a090015003040d070f000c40e0003502403250507281d0031070b40203007424081412904140850b040c414090141c1c0d4003052041000281a8000050918003c10150300f0348555a00300064154a95004981c000c041c0b04082d64100f11040b56161120403050300c0e45405103180c90400040030500703241c05401d80760460010444c079505659082d800e502d0003805085501004400060f0415140c0303028506215100e50700800c0c40d0a54000761402038090340028461303400c040041004000c0d4501e0b0f40c007001a021040c2184401c1d50001c41d01520400c0001018082204002001d49502c10081e040a44c40b460a444002e655050800f440d2140528195803100604 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 228321160 1250 228319910 228319913
    0x160902090604062f0a031403190911060301120309050301062103270501260601031a15040302032a010530100503010e0309010e03031308280b04 63
    0xc10248400402d01d100d0001200c03008a8035034010040c0110105059115006031000c15401501e4040031002d9a0205030039071410382031281041c40706949d07145c481550341621600f8000ba0901c0a044054054003141e66940e59204400c0c0e030110b043d030107500141c0030420103d0185018010041151005a8a010500740803a0b552040000c5180110b0510414881c2217140f00380345555041c0f0356049130741c0091218600400580f501c80001c181506400308541200203c1ea0a0700b0b00d55080300080c41e000a10b441d500000009030412090544c0c1e100b10001080701e5900070790002001982c2c801c0c0c0545400c0c0d840ca221500e0559000115442c0f1006031201d4400a0b502c124042c6c43c030084013030380b924080f2080c6042c502502801003d281e071031004138401c1041340c8201c00407510003010300742c0c020001c4007418500c035070b100d00035040c80c0e81c1044544c03200108965010416111440324140b1041203050340c604a444e643d0b446079030082c1e45a2542c841b4079079a102c55a000002d0640c00815010b515501c2d13 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 228322410 1250 228321160 228321167
    0x30f140c060412110106030503091215190f020c10140103050d03050402040207020607110a172a15070309060e01120507050c0102071a100510031104090e16090209060406 74
    0x2280b0f00b1404101603800c001d182c200c03090045c03100850180024680d200401c400f40030141c001c00d00154902d5106610501140200342d061030360040c601e240b0031540814a2007208050005140442022800800c1524940d5404610150602d290350390030840442f03030542c4030f2184002444003415a4209481c0441c805029421850f03101340300820041c9080348541c0000d51942040780c1c140c44400b104e035440f9450f0b003084044400548110f006014540035009070099444101c0110742140e101c8030748280c4180100540302104d6a0401044440c020145000c02c0c80d058110310f1080d0001403502d40001481400790049400c09201079560f0072001c0d0b0240300d880042c0101409410400c0010001d2030410b03807003840074100f41445045031520031400342c0d81d0b06e200e41070b010305010342c2121f2606040056035541010726407040d4403400d02044107100043c00e0f54203805180d00c640103441c00d20500645a40c000f2070b00600c03020306c4104a040345920f41030058200d000380c240003074000d40204018031100b0301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 228323660 1250 228322410 228322433
    0xb0a020906040e010608070e030102040807050d050a021534110d230f0c0319030905061201090518070902070c05060f030f010902071a04030e0d030f140c0604 69
    0x3019041c00d01c2c01d035403400015103051099220000181e0400e080c80480c42d0310a080b00b4040d0f0048000354105810503ea00b40c540e2014441c0b07600ca00010403600003040300900038140345c203800a000700e14030300d00901c01c0300c1194000102c0c00881003849004400031080e081c2c40035040b54075414003200e81001c035a610381c0c4010041200c298407d40359204071002890307982c1510b1515501c1100303500e2000700c030a00645440e100100300c1d4a030380c120201211464900003201c4a02c020005803070358014940c2d083c00e031340c0c0c6411504200d0b04010f000507c1c080b500c0015011504035280801c040095546192410320388070300a240b0000c040d00302900c10440680300d40c015107250342c0a40180481582e482c80040c0a81d4006010540c2202d404401c10110f00c203a03403105030040c08c40c0c2ea41075182c50703980c1c0d0b50141184082c003442d030b04805c01c81d80445c0c00d15119041c603050326000030385662142c1c095401d014118100c011080c500007040000ba481c29084d00704162881240b40710000d051030703100c6681c2c1c20007414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 228324910 1250 228323660 228323677
    0x1e070503070c06050c01060b03090303070503041403031e01170d0f030209040f060603050f072f010c0908070b09010c062d0926090405070203090a03031701050109030b0a02 75
    0x1100740090408a06981040002041181c07a05a900c80280e4000c0c0d09451031036010244201d018030400150810110480b03500142c00d10301260f83c0d98480ca42801d0071666060761000f58031000c410055040314480448001380f560800c2c00b01c41c2d80e42c402c41e26402c5c3c2c40c41c4070a2119900030041c1859000d000e00f022600203919400c025007008465030100f03049403025a08a0951a1954010008a0f40520507150007816428211100b840c10b8803000d890100c0811003090012103101642c0c01264051403008207103c07180e00280040002e840e0010f102518501408820b400346250008003600d1810458408442c180c555903e24a515126031005007086401d030001c401d5002101341d05502d80098850110494040c00a58032417642441c1d07000035500600d082da9421108801800c800605041d04d121586c100c401240c00c0d41ca4003001c030f00714003c1e80344150b04000c802d00d01008150300300c1c0c141e44c850f48100068150076a4ae5400440b407c3d021440054244d80c980c1e4081018101e06400501212 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 228326160 1250 228324910 228324913
    0x140c09011b0c080f0a1a0702060112030509041e0f0e15040f050604080d060501050301060e100c020402130e06030a0807030c05030c0304061218020306070e04140405060711031e0705 79
    0x40303507a901000d0400c9841c0070000130a40113903a52108001504014958a1400103a0598140750000000c0d42e107100600a03021843c01081080b42018030880485072183e0001d0300a1107200780e18100307030030004540c50080c00c8590038104502c05203401031013110b181d111130800032310010021214904c0c0b242405441505c441d080c0c41b42001c0400c2007044114041c500ca0042c0c1c075070f14030100350148110303692031f08054100301040004118003544104214440303072003242d003510744c80d0030a801924034807072010009402c58000315a0a059107100c620381030450f40e042405014a40d6818201511900c84450042c10600c00340411004284181d4004c28400e1290040f2894030744401c0456280d9045a4000e40014081340c6442607200c00c2da000d0144094014481880c1602d50b45c1c0c0002d4803500b0041600040045503064400c043d07556070882840a007445e003c1440ca414142441a1207030400c8072508042134106188021b490030000071981c0880c500140f40c030707038140c4100c1848091f41c0115416681e5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 228327410 1250 228326160 228326183
    0x50c0a0c051e0c0102100c0503040b0c19020c03010e060408070b06030a060e100b01050a0f0f0909060b03010303080f100603020f0d0f051506040308041e1503140c09011b 74
    0x2d8001c441e200004001c540b4004250105002000900c0c2000c9810050071480c240001042c1494104d01941c0d08560300c44905c4081e81ea8403580100c4501902d03600324410391a82c10083c001a4002c259030401c602c0a8000703205540e240e0103030350340d9000291001030400704208800400f16001008998024400601342d0f10103030b02c2c03901c40030140d48800341614103582101e4440000c9512511400c49117510a0030f01908040d8500c40c05000d03074000403115001d100504255081d01449800c2c8800a00300f5605c04010054454402141a4009010890110f82c03032401041c824081c042c00d480c412403108414100711420070008030040d404c041040303610b124082c010001d98030041d000f60170302070307412480000d01854003501504c943c1041c0321090340203440800c4140089004441220300369141001c8a8100d0000681e040000c0c0f25154484850041020111a44c2660603040842544800030f00c2039095101c0750003d09041c4114500b99021400c580940c5420200a00100401d28003030728150740b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 228328660 1250 228327410 228327433
    0x4050913050f060705130608090303041b0f030312050c0309030708090102010204031a06030106170705011b0203071d16050a0c03110f0109140c01080103030516050706080402010e04050c0a0c05 84
    0x540f90007500c6a001083c4045540d00b50f440142c403c95000306028a0404218142400d1a07030700e910010300083d0845071283c4009440c2000f0810420040c2404003100b070416030340b41070003030080c17440d103012001d624140310104040b031400c0003c0d00e0003516460080e51400303003250340d6a1061341c001d25001d41555003c0c080040407171101d02c0078039030201c180284c8100503c1c042c81050b003180c5482d0815000c500010404030074250001400605680003801c061441d1071045100301c1100501090095040c404d03118042100c003c4058032204e0960042c29070440d0f82c80b01072614407692031401810000803401e0040b00c3c207a0b440341c4082c1e11454000c0c200f100425400a00340d03414440d4010318100160345400e248010400460700c1402e1025109010b40180c240707800000b000417006100240c100704001c00c040c2281e558842804443c16800421241030b1130b03403800c0281240c2c80465040e404a6583c590302e94050509001d0f4500c20410500702074a01a0740d020140c1d4240011941a1024803480c186e011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 228329910 1250 228328660 228328663
    0x90e0912040b0a0f090b1606090f080a090e011d0a0e0709020306030c0d080906030c120103050d08070f3005090c040615020d030c030e0d1e0504050913050f 68
    0x742940b08038041da50241e695010301030444c0c8980c268104044601e0801c2043c3c0da0360151034025040c040001e5400c81d0034108400a40000480076040350781880480b4204015040207054140c1d103034403810007142c3c1e03070f80c03450501c0b4100740326800c90303102c402a4003566002010340c80c1d0f038410990440000d0b14141c2000551406900390020021a40c1c008244801440d041000214229040341d5600351040a039a0f4104e080c085d6405c5035005140c08400b00300c907100d5403001c0c2e0b0045004c022030580d00c0d40c2d5900b40345a542010307141820205401d000411000792050501200741911038681d00c2e04011600180b09040b607031080c10140305040648180c1505549010751402109114024400940c00600b00400c862866004007034441c0034841000c01d0300d8005c5102c03070400e441d81c01e0000703006024110560203091010990700f1940a05030a80c1001c030b8100c8019805076440b00401425800204c200b45c40d140b0803400f5680c0e005030340e9000074601040308000e00c03920a11071815103440c88401507609 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 228331160 1250 228329910 228329917
    0x306040e06040c030b060607020d0b0a180803010f0b28020c0a03080301080c061201031b0b030106020d0201050c042615070f1205060105030106080604060b0301092301030201090e0912 80
    0x40341d8483c0415000c00c28484055031284e0401c004587c0d49107001c002c3e500040c5810080040107246800c1c1000290099003554007590890341e40c19142554031000d460551415071090251803c401100500802c0007003040040e505110300440305803003e000e40405408082d68070003400b904501c01d5140e030305080e03240c0d03482c09401144948900c54595041c8003489080c4142854050f005032028054940b0b1200c102030f4030340c1184d4020314509680301103c00714510014041d0003130b014500000000040c9190700040d070b81c0c1d180d10254001c1100d81c40701402d40301c06100e00d100b40e19100e00c01401058200c503e82d554081042590f4046440c1456080c090610070202100e545002c103036a108800c4045812001c03642202820100410280c905100060320500040c02071800300440107002034031948481d8000d9000d8610469280c0e12503a6540520010b4510a09002503107a00e010040038041c1a29a243d41030340e40c140c481031000d500704224601204002403e2510078403a00c44102102003014005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 228332410 1250 228331160 228331163
    0x4090507170f0601150927020708030609061207140d05061008060702150f090102130f3305070302241b0a090501030b04140a0f140103030c02060306040e0604 69
    0xb0300801c030300e9940054201281640085d101010f83d581880c915903202c010107081d1014201d07000c05032a52502080b50303107414107880700d20b071600c0040c100c002e215615015502c20f000490703900c4503940c0c1d02d60038081c04100c581e8004035140d000c10024440d2034442c0240d00c10914001d03200b01c2074440280ca81c980740c0001913540310414149c0310300c00d000e114000e00000b948682c16000030010001d02050821940c01d0081180241c0b04600010a403000401c0d0100c3c0c02e080b20349a1081c11085e2549003142e0405440d1151100c1c0c0c1c1040e005044048070221415124088840c1291010a555031000e4403160310600b401c40031402100008008040c030034510584250020003e82c82c1d5290892100c40c00e04034803200c411000200303010009106601503c45000c0d15820328000c03c140b000c2c1c00101c2e01038800d0203043c6510811b03010810060a81507400740d241c03c0304400b4140701507840481151300c900c00178000580002c03200c0d100b500c0542881e900542d0003a402810007e8410000c2400d40e007005400d840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 228333660 1250 228332410 228332413
    0x501031e1a0703150b0903010b0603070807080c191806090e040b040f050a030309020103232a0d1509091208100b0c0d0201060f051c1502130303180b090409050717 71
    0x50b81d40287c242441150b4104100703858086c40d606085074003403c00c101c000e161004009032200001c00511801e010f907420352005903c8090b16000c1c84030054881181030110610314002d40a0002d400c0717201c0e501321021100310340c20f21001c98070399490b081e9036200d00030400c0c1c86980702d18070310800103a81003281c0034400d40640d400103603064052000600381e4014105505514907134101001c94103204034403880e0000101e000e8407042c040404e4020070140b001c80c116540003800401d010391400000d4100c02040501c9091800c1c0b01e94032402c0f410304aa140c0d81000d00149e00b4800e1840c03e1600a10a00c0d4002041c1120045c5159490038400701c41d03170140c0c40804a0350007141c0741c1c1c031280b90240100d9002e03003140d40c1c08400841c200004100e001030000b1100300202d00a0b0b08410500c0b4013140025681d0f814400e0556403200c00a030401019105444104c00041c0aa401f40034030600301d44205007a2440c40e0706192074500c090080001078042481c0c180e5080c0128500002d03c540740030400420b0100000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 228334910 1250 228333660 228333667
    0xc0512100f030b060a08071508060105070210030c110709060f080304030308011a0702040207030c02090a0903020d05070809040515010212030907030305180d060e121603180f0305010501031e1a0703150b 88
    0x42c001015109e019008606000c0240802d400595565584541502891800080f18082c90400301c40792210b50a041c4c0440c00760100114140070290070400070b54150802c00240f1315030302e034146543c0f40300b284005070007e0703040c1c13005001401034169008500c40300003d459007001003540000d0100e034030018041f004280d011f41200c0c114102035561039405189404100003448503614003035107592109881c54104600005e610040004c16400d940d4070f4000070340100964034210034111061000301d050300740944140c40d1030320300740341c00c400403a4803801c4500050020346145079820f48590b080020354411404003202507510f00d85441c50300c0000180900008900c141402c2482814140b0221402141d40b00800010740354900380e20040c0041545803030181e242c2402c03410704015894441c0c005003508188060f00006201d1305400c418182da0081c109105100c0c502100b000e105d0203003d1000308481c00d001d06048400c0e4000650741e07840f016606000c2000035001162020100041e0460030440c6000b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 228336160 1250 228334910 228334949
    0xa0b0108030d0509010b030c1311030a0f15081b04020705100501061d0a14060f0a0c030f0e1804050c062101090203061807050d0c0512100f030b060a0807 67
    0x43c081c0941029004008101100011000ca529a0050300c8501e004224940c08080703e030165070b0144008e035841444c4035441341131030000d50001e003116400c1a0f0846080054410018110308010030071075031803000410781010815502c907440c0d482066102e51103a401d2180b000801c40501440081c10350040f07000500b9030500344050001082040d44c08130340c000720203110708240c60b40181c41040c0c5011942c80100c0300c0d280000955a44110403c00e000100c000c945000015040001d41c000300d44251940c101c6c58a0382c0d58100c0e507802c014801e442d0b114a04004020030890302d0710401d500103008505039142400303603201045071907001200105203500c404030144a030703991b02a440b501400c1172500561075811319400090390303008950346003500d1702c0e030403008581b090740140c044403000c802c244410310000c13095410190443e0025500d01c8982c504005c00104008400804141520164403817503e50a045458100c2c1c841030041555402182e01ca002103003096003001080d0007840240a07000b41400517 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 228337410 1250 228336160 228336187
    0x1020609010e1902060919030b010e04080d0b0d020a08100608060c0f0d06050306010605030a0b0103140c091207090626100c02010b0a0f2111120a0b010803 68
    0xa029440ca64541200744202c86404211094104003154184039503120b64000100c0500c03545810036070240b4010511200d04417000c00d0b6500f22802552100d00a85e6511201c85040004407002001c0c240c0800c00300302014103c0c0d120a01403203019010180c0c50645501007420f4803c26041580c840d84200c0c02c8100d000503502030200a009610050812800c1001c1c8140c018016105200d16281d0302240042c040000b60f030041000b404020200c400950303658601408941c0140e0302500e41e941000700350a440e500a0245903414880307501035811541c1c1d841003980690f04954112035200f44030352208044003c04001c4040508000350380020201c1c60800c18070f0749002c50040e20340807441403811074141928040f4001c014618403810224007116440c0c422070040c002c000840c1d034041c540c900040fa05070882c00048041d140f0a81078040050404162101d0b014800b0000a01c13402c1c009000441d981440e4101d0200d04940c901101c2e0907000507030b07519a103003400741c0020740554070125400018014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 228338660 1250 228337410 228337423
    0xf0908031906050a03110111031204140a030c140c120309030c09070c0602130801090c08010c03091110200a0203060c0909070305220807021014120702010f020c0604020102 75
    0x802007010420340c0e1074403000c1003040d84148800340c45040d6058061a0f507900541c0350366503045039502565039079001e40c4000c800c44003084d601660400e80200f0f01c96012480092450702040e059220242000c03082e590f070844400c09107625a50714000e025990410352102150415500d06034070240d51190618001c0c075240c00d01150046100c0c00050342409000364025903d807126a0700b10b0005a0f07101c0524000100c9100e155020b048107610b001d1808040c8400606800c090ba0300c400c1c000c0c805594401401c40a40314001000f030300c80440e540900d20300e4034045c3c00c025280502410210b210701011200c844200050a00c00401b60300125021411072405000082d40310090000301da003010b4030301d4007003044041c0c01082d120505954501041d01c894202c11172036440c6076282c504840040c1945001c0c10303a5003107440102c0c0a180103641c9032588500074010840141880443c02d0308100008920070103c200241c144002d5541e00c0100048451140c00100042c04160700104018105840020300d441e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 228339910 1250 228338660 228338701
    0x4090506061801120f02010903020916031109030304060302130902042c0c0d0e120d0e0106090218060a091e0e0604050601270b0415120219050d0f090803 67
    0x42d00000600c904031010380d22045141d0030a40005120895100582d03d403121600042d5026005004100c0d80c0c01130a00a02c01c00c84055a0610410808046114260148404141e0705400510003842042c2c0b017603014299100c00410741c0d00c02075540341907003c00c0381d101e50040180c541c00c54003220340042c152030048100910f06200700c00a454140e880d44030038010f1008005500ba1141d00091680c0300800585c0c2e0b00706e00504c0050340e00c25407001140020706616142040a50030000e0000d0784510600c26a211508405800c81e6016000c070b0030085558807031400b0409101680c0c1e13022625007481c40349490035032403000d01c6d00c0300035080c003e0074900448000c3c1880e103c0d50815080054690741f00e402042044c0c0b24542c2c22490803202c06188207801066004900d50b004007080021320244042500501240292200e2a04440500d0000c050b8031440c503440c8641d001c0d00a03078540643c4610024a598400e617040004c00010a103490010f0711580903081c0c403031103804070501412505040e200036000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 228341160 1250 228339910 228339949
    0xd0c020a03091509090b0301090c0608070905040e0c0d1403030118050c070f080a0905041e1b08040803060d080a020a0b0106110601050603041407080a110103380409050606 75
    0x855a80e00700400304013460180c0310266848601c408420346007500044211680f200300342d800c0365101c940050880300700f00d8103400080c060b44000142c0d070809101e41d0409040c543c010b0b0010000c1601400310040d409840ac0799407402903a04007040c3c5105101440c003038084054440300c1d4030f004c0101e07c41981c10140200140702c204210490001c0d10f08502c840c640380c2d001105984a4111603029180411a640910341143c28040c0d034001c8101c855206208000181004100c024640d4803660350002c070000b1140c01182100000c0780200381604091680500300501c2d080703035009030703507100c2040b0380080d410314015078000c030125410480c0e5520b9280c0501894174020300340c02c81c1c401d0301c00e6a411040c0b08060050700000080b9091010001148001c00c07641d100300c0d4a080d580d40c3d0116035480030710700c05840c00480c0e0420403102d58440d0041c4204011121980c0040a45142d602005800e04c9004402d03030b002d611a458400351074602030f0703801041c01540602180d140003c184655011a0222079425 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 228342410 1250 228341160 228341189
    0x7081b0619021207080301030b0903030402010f0509041506050c010c0203090102120924030f09010b06030105093c13170711040609050108150601020d0c06020d0c020a0309 75
    0x103500d591003966514115a500607000005100080e410310151090700c0c0c1d40058009862014090480001c6040300d00c11b40c100546a40d03410b6103035480307000542d402030000b0140800d0008040c41034000d8a00c0080013003000504005187d01146100345c0c1c0c0d440700012030f00200d072008540d9002e2156062040250014502d4200c0e4180000c0d01c0c0c40c480c05080d50070400110b20545107844400e150b0b0707800c0d0880f180401010580000c002400d17003003280e4030003404030443d0019220303041c1800b1300c26201c0009001a03003540d00b403e04004580c9401045060514062914138220b21000e203008060b01e070086152011401031045d465500c15001440350083d640314028882c00070b01e140c4580c078180b80880d003102e0f40703d00306454221400f1850806031a4002c3c105100426101703c558031150480b202c2e081245d009001704114400c0b00c3c002103504601581050401354031981c090030b0481e450900c01c900040c40e040e001d2840008503803140003004016849110300e4030415030825580405420303c280400712 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 228343660 1250 228342410 228342463
    0x30b030d0905100314040807020a0614030406051e0c030a060b0304080a05090607060615030c1107170a020607060e0c060c0d030902120a11040f02092404080601080708 73
    0x1c0c4008a00c2070034002c0404000c5034007614400c0d0b01606880075103000c0700b801410241450140e03504000004d0b0b110361801840050140c0c0240001c0c20b40d64100c0e41c1150843c2e80b1900d038100180030041012032601c20070200710b40606801d510312403040078151001c03600c900300081404100d504c0e64000b9220a81c0400502009c07610050541d841c900e20b034500a5981e002c0b032800310709075004550008126509251000c111210f1800380704c0d12112807039038100102e0311881c01c02c4540000706511100340d42c000800512a440481d140c3d01541d2202100310707035040a055010a039190300ca54800da130195900c0b07803c140030b43c0040c0000840400225803450406000c0a44640c50b07150864a110505035036480c008115194104440440b00d400c0090354545440c509003c0d2240d25015030452240e850700e400311001858a10a070307030b56800094882080800061800e40f200d403103080b4840b1140000f80301c0001e40210400200e0301a0000d0005400c000b0301e0820745500d0044210324501510200030164003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 228344910 1250 228343660 228343667
    0x109050903041d040f0f0c0305010c050f09090a060f0803120115020d0f020703140c1003020a050702011b050a0311280b060a170c031b0a12060b1807030b030d 69
    0x283d012080c1c00140c1c2d0546640c03a1800350b580c0e811030004c05c010707003208240052006829100e000c50340180005e02021015101c1180e071403007101d440720b80032032042c40024004d08003130303221583c403000200d00000d407551100102460501c0c0f9500444446d03000282d031540ca1008101500c0c01000501e041c080c01800c4941d000e5241c00d109080d80d8108082003c10280c26403007005103000441d000301d50034042c00f61203800540c58994800116005403001c00540300c070307039100784212525903425030740e440e0a0050311b81c0110350b610020003800541440401641000c50f10074031108940c144262250418000e03030706002c60030180048080c01a1100c6c884d4401c0c1400c049810050440c0c0c1e2021509280790744a8000403103d90568004983c005003171110701c5015139001078110441842201160030391803070a000b02d100c00e40e04002c0c254124100d000d040006e15086030b03d565070180310754030205003c0c80040c0882c5010600d0304000000c50959014441d1a41e058401c4111420083d0082c00c802005450040e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 228346160 1250 228344910 228344939
    0xe01020a02072c0406060e0403111e030f09042405030717030a030905011407020d0e03070f05090c0f0f04170d09031e061e11030108060112081c05010905090304 70
    0x200d0b03c445a002c002020050141e0000014042c101b00704400360616080c020b0213207170010541d40c601d03c1203a081c402c0e034407903100d00d42c03550080c8030005601c0d10040e41e04588103a041084425006900c1d400d02c4881d02c0001741841c9200e190540c41101903d00d841c0c10185004441c0d80700c0310543d01c0d040d0300c038800d119010085549010060034082880381813441d002e801441c51400d08401d080042c4140841d040e030201d00d240802c1c0081e641e41c9208400e9104040e00c0f00c886204030703111844d1105040080741000d4080d140c1c400e00710003005052102a21002c04180e100f2500d10108900001e01070044000d542d2881100c0d11030302c4003c020368103d03040041c0c030051a50001a010b940c050503c031001e203103001c4100c2e4005510442c03e2001016280090100f00c04500244030080c1c20301042d00f110846840540381207954031401049243d103802c0030044408400c01c0145d030300c01c3d410800c041c4203440b02102442d2005d0800390024896150800300c000703c501c05004041c0e99041080200500300005060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 228347410 1250 228346160 228346229
    0x706090b040902031e0f2710150308040e0702070b0909040b150406091a09040c1a07080301120c060503092d010c05030a0506030c0d03031d010e01020a0207 68
    0x103940b80c54801c1d003000f44110715200c1d0185c0d29141000c01901c000302d1001c45d40500e800ca440d1125042d030500f1038404070307802094601081d500c20440724046024640002c46040c003103600d00c1c420a9125121503c0c19030064001401002c032035030034070485a82c1041020014000d41c5029400c05007040c0000344403d0b03014202a1001e24158003140070fa00258114000500c4000c0041200c2507403101c031100600000301e507440c030000307010a01c203d1504242011500c81d40e80310750700141503030070b0808211403100c0400d0f041500000610414000a01103c02103000e06540300201402018610300f040030321942c0d402040400c4014028402801c400142e003e5640d11001014082000801f205001113807120a03ea0860f40c00c0545a100080c0c005000350f0240810b440140700954900d414195620080180d07150084034400b20030700481c1c400c1d8000400300000b11149111a07030f1340c8601a0a564821401c810983d500050b025402a010002c9500030314810401c1e405400c454101d10100b00e00c2c0089 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 228348660 1250 228347410 228347429
    0xc011b03200d0225030222021603030e0c0102161a071a010e010e06180a0f0c09091409060103020d0c1203080f0705090d120e06070f050706090b04 64
    0x150015000e01d0810200140c481003022a4103860032250025524149450030450403440701c1900c516240030005480706503600a444400b203c0e10542c44165440c241b203c000140907800d215003d004807038200c58000700c45c007982e004511018200240303420604101070850542d8008650040400c0079070403018100c071901d051000d2580c1c0b402012a1291092140051000301c40205400e5640e944042c2203050324022000e0400c00d1b0f881e8a08206c5800054504e40e0b406001200e4a040004541c00690391241901a0116030000061030324010b80ea05070200e140400c4040005003c2c0e1440c030320030b03417002d074005011a000b18100f020102c0e450700300600010380a83ca5074414030003844404503441c4010110403209550031400d600300209040c0042c1c0300c002c000111080442c1a0f144100c0590343c1c80e95005102c0b105074441681c1d184000c0c0d003040781e504184035030b4a010303501d29620305025020042c040e252a008011440c40d0250510240d50410000c1c416104414086045258240c5091b03d00b46007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 228349910 1250 228348660 228348677
    0x140d260f030c0a0f1d2b06021b160b0d090f05010e06071b0212071a0405010e0607081803070906090b0f030601030515150607060f06050f011b08040b1204050c011b03 72
    0x501c1c01445100540c011b940d80d419140380d131001c01500b580140700042d0300c4010000c0211400200c1c5868040003096121401c551103000e02412036428010a03280806140005010625995503c03420181300e009840696540c01d801003003c10500c4590b03402a024600280c0b96548001e001c519031030301900182c00b440e980f003614144074500f040340030003812035540c0940301130f003901e5011003295001d03026550004850f0700340d1801d0303818400300f65411154000b081c6410011826130424181c4455200103905101b0040d00284034185c1d0b20030700700980b526100120380c0143c81410302c80041d0099080c98041d5101c10010004500701061524090392110180c00c0315031a40c000d00203140303c0c0b0245c0f43d035001400240e403208101495000796804412800b050000c6a5140d003001000407408980ba030201d003580e86092102c90000642c0c04415205880c0e190409032112000071081e005035500f141a4441d41c400c0c0418040c08021540b8a09024644000c4001d00040032070b01964001500505004950 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 228351160 1250 228349910 228349939
    0x20105010611030a0c15060e10060801031109130813050a2309040311060c0307031a060a0c050f0601030803041703070e330301140d260f030c0a0f1d 65
    0x42c804489001c111700b1b0705001c41c60715400400410003050354140101e1040150019440340034105280c12640c02808458104004000b8008015002001c0003440c01400021100017401038014020b120364140111540c0c608081c1445401401500903507070310680d8481510300520240031480030408140d89907038241c0c5aa16060300d1403080c00b40981c483d4001e107000c001e480e0303411001541c07061580766401c0c007040354802141045070581151041c1c1240042206404446c083e07101c07102014460003c4a81d1510f520205a0030a03100381c104031b644003000001d10003801001c0980501c0da40d05002d80c0d500e9401d100c400038208014064880d4002c64200c45403100042d0806452500b015003062541b203a65030803001c4990580c803d01541d00c9c00307070070244501c219040000c40034441c168020091902d2200d40b0380000800840c41c0c105c1441c1c0c6600304508680542c45c1d8001d5405038000346e00e015100c07112440003400d03007511440703a0420081aa00b803801c011400505070051b103007007651100c0d20344450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 228352410 1250 228351160 228351173
    0x11508011b0320040b0703030c0804030c1707050115050f0303031302090c09211c20121b07150503160201111b010c0908060103081303020d060c020105010611030a0c 72
    0x5018000d003200f80c0120f4001307103201594000703080140c0301c0d560400c6032403030480701941d031494107803800342c0091424486400002d00001030050003099081e642400c05605503030729800d440c442d90550f00b068150401c20031450034020040071003128218003030b40c1107103041d040c1981c042d219004082d00c06e001034804180791501c55000c8900003180038000c1071004000490580c020f90880d0803c03071051040310302041e245e5014810142210b407031a52070725500460300100c4001096468000c0540740580211124034442c100c0080c50202d000300b10807070b0f40c3e1201841003070800b0306603401648194800000c56104950000440350f0000b0a0046e50b0500c07094550308030b004105800324001c2d06000010141600505c1408400c1024100c0c4028080c2c070b102d07140129081d0000e441529a6035218000503c0041c0c0303424060041c007401510481c4140c0d94940000303c48091130300040c0d990300d0740c87c0380b4400e845a080c0242030240c0711500b000040201e441c0c041a0384d81c800c01d02e13048100500b000080c0d0403c5207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 228353660 1250 228352410 228352451
    0x70308031f2408010b0f1602030312010f060f08010e0a0f110a0309061b021504050c0604060c11030c13020a021501140909150106080613050108011508011b03 69
    0x6842406a214910508034030310b03407140c1007800c60100e9005400002c8056404003141c1c07883c101040e03150b0078034665040c0c01007050441d20302203071b050206002d038a140011407030083c1c3c020030300c080b132800f1514600280602a0300170f40783c18404200701c2d8001805800c100c449000e4100300c10410014600c9050324040700101421080c0e0140b4080004140c464140d160f0055030030305000740000c005518003015902c0c0264502d40a890250300466141c4090038010380303066902c10f0081e8152030f110100400010300300e9200789c002401054002040c0000e2000444d00c404403c442600244080114030002608170052480088185a0009800d03a41140309118040120b500002100144c0d6103a40e11010604807140003203020343e001034000380b03059200140b8888030680d41c0f8680c203181d90030700404448e40c0900a00141d040000c584035140f801f03d05204090003040900c0001030b2031840d0f01485c80705461158010140d6038107003142c9043c031100c92414001080201d08000640c1c48507011400384050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 228354910 1250 228353660 228353669
    0xc0a020601050f031e0106080f03040f0b130e070807090504050402090406020a0e03060103140c030604170d020405030d020706140703020615040612061e0203090616030b06130e09070308031f 83
    0x402c040b03025207545c0c150840c01c1910980c200f901c10508090300c3c0c03c2d41c0c80c091481028028046214200181003c0c00c000b8035058803404842034009840d140081007500040d903c10000581c504204424243d000740407034060007003160140101e040940010b00103004c0540080c2c003095001540c0c002aa0048074480d03c100710140c29200c0030b40e960705008205140c01c240010307260292030841100c80c540850503622503030f0b20204100ca5501c4445900403e90419102051920341c00c01010941d55000c0120403514142ca50081c802c59041a00c010f01d03880410006902c408800c5c0700e4000040d40124003603510008100c69040040d00382000038021b406994050610766082e410684107016280d00300d84c506100d03000d07031419040c2e0003c090307000b28802122614016041580452040d800005451403844540c0c03801040c1914a00001101540b280020075181d801c40350003040307041d56000c1840e40c400004406400c250307103181c0f181c80161000416004108a2440800c210801c50811110181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 228356160 1250 228354910 228354943
    0x6060f061308160e010f060e0102070504060306091703011503020325050a02060609070507080d11030c0d2a0810030b04030503010608060f031009140a0c030b0c0a020601050f03 77
    0x2d68400c0190b465143c40210b40a0004040b04041074001644411a040710024410400d100d4542001140c0c0b80c1e81c10090281107009034000082c01d962240102c074003075401f40d02c1c0000e0388109860500300854040c000107024003018801000b401d01e00f6107400204410906016a4980d1020f29002051046907500d00300d000d51142c0c120081c1e0341c0030020b03142c0c8128540840e80107886c0c8104001045804030b52110000b07804000a40003e00406c010b0f01c10700f09045400300390503140e41015207a680040700d01c03602c00c04020480042c8000e490140501a1542c4952220001c0d03400a00084080e16246504140f2145902056607944130100704001182c00c0043d060203420146401001a40700f80300750800540000081892440d0016185200c200020010300103000d01e5441980030b1b00c1d0440301510340c100c10075007103030000000703122014219104108944600d030075441c21030341000c40a0007105900f90148183d8064540004410f4103460040744e0741e000300c0e0404000a483e200c400c0c02003ca51 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 228357410 1250 228356160 228356197
    0x9070f2133141201020c280506011a16081903090c03020d050f010e010c030c0f020a140a02060c0105040302070614030a180813081c12050903040f031203060f0806060f06 74
    0x1030003040084030743c002d42c0d04461550000e107c0c090840c050700078001d0003d801941c0104520b40d01b5000c402806c08005c0495410401002500380b6100080310040e5601e40c400a5029190451200101540c0c0c1a5080801c60311110340c95482460b03e1600000b030096603e0b140060502508102c0084440b2881000f030060141d41e119260103022544250300c0400e0500e04102880f50150803072003241c450990017003407408515141c01c0c06070780d0300c3e5011301c09034007610300704802580740e0760000c2091540070350010455003040e24009141c030040b80c0c05002008148a988442e4851090840b80c2003074115034045202800903034410502c2c03e4240004040702c80029044072a05500b00d01041220038010541d04441d500c42c1c07040101510401c80a80080c1e544141e2a0300e5074199800150840080001c45e41029100c41105441c24015042654501c544491301c551032645402103c0c0a04900c419043d052450141c07465611900509124030501a44c3c0021800c0e0b2103442c1650f403c0018441c0443c41d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 228358660 1250 228357410 228357427
    0x209030a12120606030504030c03082203020102040f0801020703090308091c050c01030605010e010207031e05030a1211090603070f11010510051e09070f213314120102 73
    0xb408034060000591107060080004201e402031007090720513500754503011600e80f2503540440303090788014a044078102e450030b0703408050036240c80d0503515144603400060b562070408110000b000d07407079404a05035030300400ca0070000a500c175000004507030f803084500d5140c42d011030000390001d83c0c1070000c4022103804281581031101c00950310318090400e8804004103a1640011a010003c2048c41c07400750b40301200c10000540e41e0007000903104800d03148074140c000702ea600ca6003140d00058106000490140542250403800e11802802e204190340840c600524680440e01901000348a401403000e580e003502c884c603004100c81b43e01d4125400003080300d03180c011007440c110036560081d640504031303800c0d6001c1090f108030500b103002180284004919500c02c3e4013229030107200414581002085000c0003110740320342030760b1449403010b548085195581e003030000b100c044040b01d40312040d9280c05031540903100c8032a840c0741500e18031042d0900300c500c20400b0801070000ca040c100c015602c009007045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 228359910 1250 228358660 228358667
    0x80601050a0e09070b1305182503020706020d0207140304030b0a02030601051608041508130807030c0f0b0402010e04050403080a0216080403052b140a1b140d0912060209030a12 77
    0xf41c8104503018081e61682c00c03401c0c14001c80845840340054a4400d03d065040019445c492188275185809482d0500c0355071098240d82040b00d501c00d4182d00880d28100700500d044000b103817200454001e505240c40c40d200d03090740c1040648440003083c3c0c000046240d50f44200200c91031410303484039042030b00825180100c1c2c0741e4050300c50401c1d910044034050305024440c0700380c3d034003500c0b8002406450b0310041e20307030f0f1600760701c801001c405000c02d0744400c01c00a02c510b62002145070091940110525180c000134004000d03c0c21024801c901d01003c06c800243c02041c441d8210388581c01c0140c60302c7c0700c071254021080b03640c940a044481c1c007040001c100800002c01c90510085949500f4045400214004c001d142001c10030010920101c0b910500c12200006003040015034607141000383c00340c0702565540031507046c05903011664078110b02240842000110a150101d10700007105600d8110348452400007282d0040c0102e400043c0802140e0b4208551030783d4982040b49460520300840c0d010307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 228361160 1250 228359910 228359947
    0x20a032a060201110d0e0102210114100210050405030912031c060503030a0e130c050c0105100501021203060a0e01080609011b050a120f0c03020c07080601050a0e09070b 74
    0x30455840c00305408a4040e1040c040d010041c4001c0c0348003801c1c036494510030f401130264440f10b0301c007640d400d2080307903518003a8415100c0e100b810004202c5440d418a0740c1d1001e16003504842c24000e20109200700f4a283d400038910781c0c82400c10000241c151100d00c0c05074110701c540f0648540c80882e100c49980c407864080001c1015403211010400c1c8030200301c00304020780e2910310489600d0380003444030501543c0156800607050b44000d0141e002c418841d040401110340d02c1080d40f00042000c01d010412031003d1007055040b16540e001c01da241441d020000f95664125004921a09170100206030a40c81d60070104024102c1c0c0030b121000f6685810125a507280c046455001648c01d20340300e80e9640c0f1524228188416003951403500d0649900300903030343c0d5807100a0101c03910355204e40c0c03600710796100c6c450b081000c1495503000d0b13034170104c2240c003a1401e08076402038807040d0009030041009a440400c450219960820340704419500c03002001c0c2001020790001c5451340d000034400342034142c441c480e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 228362410 1250 228361160 228361223
    0xe03090109031b081209010e0a05010207150306080a060519110a200303040b06031c02030a0f020f0703120306090e07260d0810080114010603020c070f1d060108070e010c020a03 77
    0x4299120a0301c80c1027080e408480d1261a01507003103801d0501000d040c081861070058180d050105e00b5542c0d9000c0c0500d0b0124000d8255001680c4c1c0040c404083c059101d030010000c109002070206455007030f800e54183c410581d24809110a09075200f11900e03802c4990b600c02c601140136070351a441e00f8200b204885404035106486801005c800d9548410042d41140c40340c00180c0c0110b0400060403415904007042401803029841101441c400c54401084250051031003122045000b03840c008014069542e0b80d000407410f40d0904642035001d803000249503044a1074600e9201c035800700d000190910f210044800301c098040c4107043c2d090542c0201e040750090341c2543c100b00300c04da0382d42e00d00d07401c880c012581120084841001040348034402c0d0040c0c81000e280c40144c0c3c008640d6006101c031048582d40c01050f4008180c495000070580e01d00e001a805242800d01d42000c3c5454080201802d0b07101c8c8000703060215512000341951680040c07107000c1c46d4007002442840c8a001d03400018500802e06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 228363660 1250 228362410 228362417
    0x20405040f030912080d0b01050409090507050a050604120f11060d090203060a33090e0c03010c030905120c0a02131b110a02040515060304030c060e03090109031b08120901 75
    0x13a02820f9010086402d0f070000c034401d0804100d249194003800481002c141008001d00011800580c144100c42c074540c410b01c0104003151402092000c46559a80080d10541b01030000300860041801c01c9051290700042c907503205015071404440191440510907003094000c0b881e03a0403c80154440710703038580210b003100c403d0b944001e4800700740c41d07580380c012241616071150361100c034040410010403560240c0860040a4444014004032134030b40200204581c007080740094141420301c41d54002c00824501070001e507110b6254503540321700030541c2d544007130000181484600400d000060300b8a074002c081c0090b001248030090080c00804002c880f101c4d44408140244c140500303203c00c500203d40c0701400380c0c084150200401468010100b1300390031249001c00030503644080003076100321b100e074031504540329490811500303d0700c00c842606120340c420060110140c1c0c0001c01c501c05c50b40d00c140602c415200380940310301c0c5255140e108111034840c81c03c420302000302c41d0000d091001400c1e0b8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 228364910 1250 228363660 228363677
    0x6120b0604110912010e061302132a03020c060112110f030d030f020702042f0c06010315091226061f1e030f05060d1a13020405040f03 59
    0xc100842e0320040107242c0710ba0b401c1005030100c0c10500c0c030301107118503800000641c800500003640c1c14104112032040400c010320b04410110300e07100b194100758142418003000610351225141e1201409400001000f810b840f54801c1c0c41d510039012951501901c8080c0c4006594807110201d2190b1008004c46400c40900523950703042c20044221007006030024000e090b0000603140a1300100419080c900110340c0030401c0c40c0160f1aa401046460b5801c0d075600b91290007022403a150060340f03011807101c80d61003080004416200090003c1c1507a40264110f000031240f0704604006010445d8000c0c17036004150030409556800000f801914084018400c00e0100072408070304000c1011a1030942c0700c004c0c0080244408104840364004641d1303800c3c0b000d180250400300c000004196000480040c2d103845150701a515139004083e00000305489062000030242d030b80c402c0c0f1403443d580100e104210040011380035620300080401c01d5030040c1c0108103504142c01c0a2500e050341d5072054001c80c0c0c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 228366160 1250 228364910 228364921
    0x1504140a0b09010c1704031b030209251b0b090703020a1401080c0702040b120303060102070f05010e01081b0d0b180f0a0b0a0302090c07021005030106120f0e0106120b 73
    0xa00840b80c0c0d20405039034030031520070b0b540d4510002910020007500d805c6404e00c00800000c070300340c0b111502c01880c1d4074052189032640c0b04002d40344000911300660400f135a540301440d00019980e81ca00f45529041c82070341c8000214002690207212203024021103100002d02040000c0440c03000281d900a40e040f81801c0e071030700e45c0c074106256480c4980b40064402c0000410f10721000000c2d200b110301c0203001181c103e18042c009494008c40542d92030b01c0d508000140201507030104030301402801c0010a032001189000000b070a041c1d03505000e141440016030004030300b0824503004228103130949078070761746031170145081e50018000e081500780100c011445240700b4802c5840440e206003c3c103031440030581d0fa9100780002806c84038094070b40010300300c4000f100581e6039031803184c8101c944035901500c80f143e90040006075000402110f06011013000140026680000150344503450448041442500043c44a00034440c101e84803215528060000c600041000d4120040600511503444c031034070707103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 228367410 1250 228366160 228366179
    0x20418061a10020c0603060a0e040305042102060910021e0a03021e0c10020a02101106060a05090c090d051002031602012a0c0b100518060616021504140a 67
    0x1210b002402684c4080c0a2078a180750480046034000405820702e4440342e5282e00320b403030340c10080c0c03000c40102e08042000d00c12524001c984148002e05000d0849040801d500490f6452041e500306902810614019070316a81c0204410540c0d82c802c8420b01c80c02c00c00034500c0c2e5407100f021440c101e006024040340b0107142d264003d401c50b47c1c00308040141031140c80c248208101030380ea048204095009140c014401b5a890b82020000204180c03207100d54508294401c90500c480203207514460482c0d05da0a010588824069540c046030303481c14660355a00c0712000403c1c51000450050042c411003030076122519940c1c000c4c500034201190650300701100c19400381d00341c03038519104210650035200404040840c540c04100000010305004810480340e458240c40d00f0000c84403561101c0c0300400c100002e04000024400311840c6c00c00c2101d040c03d0581c00100c9a00c2001c849000810888804105550b120801003108000301803446503642d90340d0030260290303030700340c55020301c10120032a0010361400c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 228368660 1250 228367410 228367429
    0x1f020f0304030b07050304031206120c090e060a0e0304030b01090207020f01081303052b06140402090f19050306040b01080d210507051902070312050903030d0207020418061a 76
    0xc0c009100342c07290340e500314111307101d8100500c1501088100100b600740340d0702701e00ca024081d003002d90749013000d8811401c207422107040d9688144201c0c0d107800c0805031481c0d0301150b115009201240301089001d40c01c4c1c91103185010b29000640002004000040c00300a00d03401002c00d01e10940d442d40120314007500640e0021301c11681d07040c0c115030b40e185100c00030344200018080c16410504010301c0c203244207003e900c0f200cac0c400e107045542c6640b10014864148450b9001c070504000326010b42c500350600000c10044010741e60200d020302c3d251800680800d01042800b005040060308a4841c0e28050a02000c51780d02031250702c04070b0003150350900106105440082800c0c040000e51480a80108000307801003100a00d6902008130a101c2c2440034a2400d044902981d01341e4001c280c01d40c19801c10141e04040d90040700300b0700004001c0c008850b00c0100c00e5034003180490314010380741c030300301d0000c20050070246506000c44420242c07850200807540e03000d90086c501070452488154001002d212500e031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 228369910 1250 228368660 228368663
    0x180f060e13020a0c14032104060e030c0309060d0609141008010501030b0c160b0106030204140904020a0605180604170d0806030316110303040602030306190b0301050904030309021f020f030403 84
    0x4200d0150030001c0390310026081c0c0d03000005c40449142c9020400e00c00900300340922060780d44070300001800107010705401909a0120f80f02c000d107103040300e00c68105a480c071610300351074028080880c52800d100082c0d0300a030b0044c5410f050034082c500c006040c010400c0c1003100c0100380c240c61564007080c858414030600e8140c2c0e610151031210743c1c4030440d0541141d0030619120540c1c280401071400004e880c2c0710641c2c020b10646e00d001d070f185c505100422040c0c88494550b107014150000412007da92002211803c544440c141300b40c1d24070403903114113a0448018a80c5130402c07000240027130300d11641001d084d0003003506015640b40080201c0111441e003410744200394942d00070f02048010026001c0750b01d0003070744608900c20070310b0741c00c0012a0a41c0c1143d1b11003070150304048100009030505503a080300000644220455a5051a4090348580410700070700d40200e03400d500041c1054041c2d8888004560000d003021a00580c004520644010300000b140c01801210000601290700200b6542905d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 228371160 1250 228369910 228369917
    0x60c320d050a0c080904092a09050c1621050d0509011a151c090311030408150612151b070c03020d021c030206040b0c0a050307180f060e13020a 63
    0x11510b50b00c030310402d90080c010715030b0301a50310000d050000b81c05c050300030706031650f4440441b545511518080081648c41c0d1062004500702400c00441e0150102201c5030303c44c40d11094408030301d203418641024281004160041c412408602643ca60020080d114040c10759030700b40710340d541e043c4c0507a0a880720786044114403501c440d8504521304d041081c0d04c20502480302c480781040700d80c0d410051a0018a0503070040d05030f4501c0f0500034942c1c482a05806510701000952405240c51410743daa40c924181c00c2c8221071050001c58159070700c007205242a00481011560840003421400303030311000c1a94062041004034088509880242d02958a036a406c2901b00401d50710396020b200d502d10495500700c0c0e00a032110104035400c800c4046d003902140c0642e000340759615080c5401c1d82c43d1000a01090003207001032007603400155000088030381c0b2072a2464441d00c0880802d8201e00c44e1041c0c0d4000407501c6c0300350140824901da0044900043c4503088400b02c500131510030065049100d41403096000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 228372410 1250 228371160 228371177
    0xa060f0e04090204150f1e03120807020109080417070504050601050706021e03040c061106060609010e030c0603090d020105060a03080a2a0b0403030c0201060e01060c320d050a 77
    0x2034a040c2c0d1009038001c2c0080c201141803200ea881c1511002c3d51600b190020b150725200070702103400113046070715614040040b0301c4a19411900c0300d69607001e00840c1841000907a0002032403661007900400310081e400404543c88070340741c2064144040f42d07119501868407684600045628181c01814000c0c80c040c1c440c80d00d40360003a141e03080a90700508409030f543d800c205a944140400c100114031440c015100301100a0901c80c0050200c0c460005081083d8020000d000d17036a912a021030b81c1c0a0f400342001c0586105900120b4140100c40340d01c154000380200811402c108080b400c0201d20b100380c0d00800c525601d00080004060640c00702506c45403040c8464512507029280f41c0c0003240c030700c40d188203482500d4801660500001c0c002107601c6885103040c0804c16070140503001c1c001c0400d000a01c0098140b01071205114014455442001400c071441414400c5818000e4400901a28201c201c511503902660392a116600840c030140b0807078800c032491502c42d82c01c0d10b0603c0800c4d504c0e100c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 228373660 1250 228372410 228372437
    0x20d050417031201080109020112050103030801090504110907050406020f030f0301031106070606080102190309021e0d08030f010f050d15050406020c060406050a0e0a050c19081b0a060f 81
    0x7401c0d0035891110303612040248111145803441c00500800380c00b000071a0f0289148001800b045220034920189810300c1c0050001a0300044128156121240000391a5449040a400c01440401d00e550003144410500880607031005c003c000303880d030070303000c5070b0401d2007148103e0303680e2044034044010000c042c00184005010b0044035520313810010405c509251341ca445e803c0459045602c02a81a0b500048403138944070404031a140c581d8807400c08200500f40d54000c201091a07044940f501042c2c44111407031240d0b543c285070340c1442d4001030007a0700c3c0d19080e200c50703504901c01e014640500055140021f100e161410f04601c0b0507034031a080c2001075109200341c1c5c01803e4050700464000c1d4091040c0c1c14001410084944602e0061802260b035082141e0610100c1d0181d509111164001e9045540841c200050b003002c0c50000751000c510240d0081c4010020201c2500860810b0144544400e8101c81702e07080080c08102c11252034100b00c2d07441d181031303d030603156040041c0402d151600b00d51 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 228374910 1250 228373660 228373679
    0x903070b0610030905100c02060f131202071d040b09010e0703060c051e0909010801060621150602070602010c05090d0308041a16020715050319060302150307030b01020d0504 76
    0x100141d2190501250b01c03004c0f640d55030300f800c40703007018009a296500016004c5513410046103400402e5402d901401d0304080d84c00c500c545d000341901900d4000361146010b06544204814001030055107070031584881145810b0f02c0d0900705540980708404641e002c0b401081042c0701c6e5003010b0401e040100445850340e030302d0f40050258a141c600c1800028044201c0d0303540d00c1541d500541951443e095600c00c0124104600300e0fa060700000d0040e850724a0902145411501003c82c80c40c1c4181844101c4c038540b9183e9000d418017101203012103030520000280b840e00040c0b4a41911681c0e0001d00c600c00040307008941600800c01c942d988010044841c0000c04c0c00f84200c0d0ba0801c0c003565940c0e07600041c0124001c20389000f580c0800200f58621000100503a040c4101d2014107491144409030b04820340c0000c04500024081c0134210030019200070b0148040c6c0c0c4040010350340908403440028400c0c0d405a42c0e90400c40e81003001c40d081c00d031402025071020411405040060b00c0e1582018108458030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 228376160 1250 228374910 228374929
    0xa02120f0a0b0d030509120601030507090b04060803281d09070c050a032f0c090601020703150204090b0301050f19060e160315140d0602040b070b0f0903070b06 70
    0x26402030341c2e00c445018090301c8440c04145054001d4a40503540d0420900780001881c030740c10b20024a03000400140000b5002081160440b032000d100410740c03180010000b1300801c07290384411658400001c50801013000b80603641500d02c100460a243c0c410021815039a20301090300700caa00d0809502183c0042c60b004503050f401410070300d010155820039654845c50310642c224280d011032030190b03100d071009401030702d062450a1015100c1d8400420b03224a01d07680c02c1c1882815218034401800034ae201d91080022800854100044240c0448515038600c002c1d800350054114450812030041c41c241014041c082c000c030a0050800c00e26500c0a8130303e924108101188101181c4134032000410022030307505c0500904507a10031030710303510409901030121110240d910480f0a508003041045060711007aa0350321310020b6030368510301c0d03442e85010002482541c0040f91408070114025050185102c916031007004182108409511485841c0c1d56902680100400c111440b100058660909201c00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 228377410 1250 228376160 228376171
    0xb060a0b04030201051305120f0706050705070e04080c120c010507050712030906150b03150a0f03260a050c0d0206280204051002060a0f1e0915020c03040504050a02120f 74
    0x4551f00e44001510002c0200c03484002c5d54009a07400f402d6110a21204006001d2403d15030f107003007880e0303039225100d501e02e1150320004030252000030305220110085840c0042c840b01510b0008021920301412900214100103080d8038200016140d18001e40480e00e02942002907000d276242801c104174098200080d00f100c1c0552150040c40c40c1605140e5034070064038031400072a44901d03040100c64014590781c0e204921550000c0c20811081c0109800042a40e07000503100e4501a0001080e01036113407001080035080c4070000c1c0e05a01c8940c014080c009840c030410684202c2c01c52007008a0f074442054a00c0c0f040080d01034010702d04900d100d1529080c42004443c0582015983c2000071a080110320120002d41c00841c1089456000b030302c1280c40e0807001c51801c0001804001d500c0c180030856144026405517604507510034045084060001c0c0420841c00b07540e12101800306907142e4202d031042c18012814640401c0403841640256407038007040d01c20100196440d0010392404140c058403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 228378660 1250 228377410 228377437
    0xa0804060c0e1f020c301903210e030415020718091406150402091c080a030c0504080c060714030301030b15060c0c01080622090b060a0b0403020105 65
    0x49240103440d24000f800210020b042050070b80402800041d003042e66404100d407040120014121200441d400c40600400c4c4840490035005945515545400200410003044102200541e0304141d03110b001130020380034112421510109540511040e5004511002000d400600c0300b0300c60400d02510b5030301502c94610440b410255140c014541c00280e061a41c0c4c01151160003003014840c0d40011595400840760041205140800f000919960880c3c4c0a6115580000b01501155160085ca58036411080005080d0030114602845954411100c1e8004241060400c184260041c0140c0d81140c00440c054011101c440c000c1013000d41c07240c41c045581c400c1d000c010001c6860100051400b13140b282030485e580707040011000076a1034205401d02d108500c01c0040c029900da01040c180750018080c20000b203103480780800110103c0324020100079088548000b50b014154580200398042e000c2c85100d5041c3d1600c1c000d0203010070882c06a035070101c0b4100720030401544034000400d080350a196 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 228379910 1250 228378660 228378677
    0x20c1018090b040c0c0c0e04110301020c0d030b0307030b0c0a1e03090302011a01050a0309060f020f0702040606090503061815010308120a0b0a050609040e030f0d060b0a0804060c 78
    0x1185038010301056081041d41965541034060241010b00c107200a02c0c01ca130810b50000321065951030210f800e0390088441503050070000c24100282c2c804540100e040041c001d54a41c8644e1694a507a00c0c410302d05440020300380b164046890401041d05e000f43d81c0c204203508550f030b4800c4150b840c240d03c09103103d0108040c004600080300b00349640e0b03000e043c0300c070b039804180300b80300741002030a440c41c0580403c983c9225403854690f6070703084401c40da000702c400e0070040b5081c01a41031140c0241034010210404c00c0c00020041d2852555500810906100b11410805a500d42e602220140968080e880e05607101401103440309840d0030001d19411a400115104120403050941d20380c4404c0e031080311540c0c1c01103401001b4910001d009a4040020b500c00c0203d00058000640d200d03190744a8580038050010b000720150311160802c01c0c0515482c0c0480f81d135800b0801c040142a8840005201c2c1c1501d00f10020400b85038002c02c85540c5001542c44c042c0c95121a126403004041c00001d050038400803a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 228381160 1250 228379910 228379937
    0x902071103010504120207050402041d0601030f0e01090c0905040305030105090907082d010b030304090b06040308212a0306041b021c0c050a03050a021207051c080601020c10 76
    0x3d00a440c0709500c0740c00030101c8108114000780c03a0241940006100d2030052006005680314008071510180486c80100c03040e44030032005800074100c2000d86075015043c0828281e00c0b00301500700400003842105e02490b1595900b5010041f13845c00c1c0c80040016400308010022442d1007690342e60021009000c1d200380540c0d58401c646002d100705103000b011101c1000d0154605a0440d2580c80c504040000307002c44d2100400003600d0b0301c110302441c0180366590320341c640a0b846245c240c80145a108101d03070f541d80285a40c0d085884071490300d81607000c4e01e660001c1d000043d81c640e0041800344030070600300b0100c208040c8030031a40004001d01d03002aa43c80c00310280c100e100c034139004d00d0f0740190041c100c000b000040100e03404080100c841c05004400399090002039000807200161a0507150143e1200c02103c022401e00303140343d0b140500100b01091007c1880780c0480c00514105940240004032040e440c42510040d4017103880c64056001151908510b00f00f00081c1907210f5a9440c1000c0301c914030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 228382410 1250 228381160 228381163
    0x3010b21090d08060603060120031b061503030708090405040602090618031006050a090507090b030115020c0f0612040503040504090b040203160312110c100f020c0105130902071103 79
    0x1290725603041d5200080004003a03800804280d00301a082e14a41c3c554501040080c4c032420166140c0c403001400074030128140282842500c01da0007410300c01c2240d82d1210000f840e90354400340c0d0400410207c285801200b890008100d681e41e03603021048508101c07081e4100001894020310030355600c0c2d002c111100543e07451100030b20843e071403074403801e0240341e41c141403500d0010721000da041c0081c82c140050280740d5509100d08100d4060040c0031070556244031040f6600141030344030091001d400320002c0b072440b0752550004210030480d401c94600342d202004000480ca40d4140850300008104042c60220842110f02580715000e04112843c1c42c0d9110701240031500c030410709a03150b441aa09010862905208003120021040a505502c42c01d40d250784c140d206215401b40f007800301e4150a04000761003485580134640b0001c3c09446c0041050002409030081c6401c2c410041c018483c0100c102d41c021002c0e1140401594000d9174072908001582000b5030140d44150f941c14040540995950350 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 228383660 1250 228382410 228382477
    0x510150c06090f0b010e01060c02060d0e06010e0a0e0c09160306032f04090308160c12050c010b09040c0b0a020307020a0f0807240f12090b060a061403010b 68
    0x4200740c1907880f0565801c00b0b40c503656068020100c40611b0600421007154003d105009094044070590390b50456101035070010603413180c940e403242c040c1c0380002581207800c0790b40e60700c5441803100a100d4001d25040d1740d0340701d21203520507d40c4101710501290303a00c19107882c0a410445a82000175856881c2c1e100c80344c0701550b00c5244c01c20a030491440c0010541003e5500f10005000d51b0706200203001641e001c0c000960040c4a051019541700280321150f11400c0d0414109410481441e940140001c0041c0b5a9001105002c80e9600b0300c1b0034450740c0d00b00742c481a885140c0080e500b0340814140403036140316501c00b1521204610081c04203001590b2450103050082401c1c00034484820b1501483c81e0802d00c10b607014802c40200303450000034000204c451102102da03d490010080c20b0f0b4a401590840d0318084030110982c903001d0098108400b0311a0180240c4049424400d51542ca001c00c413a0980042c100c41c07032560090004010f04480103020700094401a00b8032081e0040d911100c01e0382c80c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 228384910 1250 228383660 228383663
    0x1030c03380a0b0904020a03140a0b0403051314090403140c0102180a080d050d2c0c0102060610091e05280f0b0711041118030d030510150c0609 63
    0x764540a0000301c80d22403150005540d401e8410300701a01d07140d00011028903107031102400fa40c10b42000c0e0000c500c07050080784000d0780d2164030303a0014101810f0041036a040449040e000700c50750240821040c5080c410818189002000f02d4a5590b0300c1d64129500e02141c14500c1c8d88110900c0048003801d0203001a0003001e590a481103900320020f170422491807296404144a80c01a01c142105158000d00702c410342d2030400d02c0494411038072644103011091000d1120107901d40105130700100034000c1640c00c0000f0b000da084a0722070b15198200b0481c2058480c00740082780000c241001039128805003948040344e60807248101035910004201d40d1940c02e00c242d40461010f140000900d43c0f041c1c1c1510162003035809102c00c260409945d8203c902c00d07804094070b15038000060020a5a03160810401003143e071903102c1e21fa840450110381c038a4500a1813030f100e40100114040710600c00e20900b0301c1208402c103403e482900d4000d049209402c54045041049442440035000c0781485c0a407200e202e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 228386160 1250 228384910 228385013
    0x1e0203012013060807090b16020a09051f050d020d2a0603151809020409020a09090303050603060f160e0613051c020109060e04200a0f0801030c03 64
    0x1000030550040741610250898418013802409100800d43e00008a0054a81290180d035441c0842604440144c40c9950020740c40301c01c0350404100e82400b500507500401c0318100301d2003101c4007031a071581404c03068015a81c024006208003c058604811443c00701c602036200d24004081d20527101c10040415a01d0a48585a10508002480c0e0600c103820040c151010000e240f0360030a00381d14001074402a41056803610380e4200700a564441c3c0c0400340181d40242240001c0307a44070322a03406403e0f0b180040c1d010a150000007109400c000c82c1c45449400048451140ca80d9003d214101c2c21040c003510800700444116003c000c0c0d02e94030000c00040e00d000c0002000c1914010070040c2404400011112141400100c50300607600480c80c4000c1d41d0140c01d040004c80c040b00c020800a00301400440795840410702c03018080c400784001803075942810b40e241d8000103d072920a4404407003c1c403008200e80380304101040814110000c0084405401c81101c801d6030204620300385900c440c0f590251301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 228387410 1250 228386160 228386167
    0x20f0412030e1315260d02012013090c090902030c03010e01082103090c0a140f01080103050a0f0204090602071103160602031204080403020604060215131e02030120 72
    0x2403809010f5420b8142012200b40f00750311960610b2840c070071151003542c1101125040a0340318164590070a100d001c409000c44141510b004002030203060b80d400402140c50204c240500c1c021b02400c100e40b02d522080e810441000d02d0a6002c0000304007440b11201003150080d008a020080c6000942c052a14204115142d50428112246544040c1d00c0119181e2140450070714503e00110041002c400403078146849039900040705050041a501250740540c1c80440402c04941c10050b03003440d000c040d180c10202010140c01515407090030b00010b0410751100100000103a820207070000c07803502c0988089080310060380c1c0d003030076070300403101c12030b554103a00c0c0048455040400004420412141500d00101d01c2d001d00a512803092414861030000440001410300c01a00b003100c0003103901034002c6580b0f80d030f00e5800a4031440362000342e010410070342c00480d0480540c8003021210a03005900001003068078281516920082d1004907015501c4409223a017400b113500c524440705400f049103598 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 228388660 1250 228387410 228387437
    0x60b0a0902041202013f0e0a0f080901021f0209040e01051e0c0412050f0f07030c05010503060d1b030201030506060301080d12110d0207060c0e13020f041203 69
    0x26118a54000000040c8148020032280042c1825445010340a003010034030388414240f0481040c1c400d0300c0c04400013807010b1891441d41200d04902c0071181010108110b0301c1040300c05103448141045000d4040482c014804001c203526100170702400c81c050044400715803040c4d2510b11130440219004c1c655070342c0468040c6160500340a0050181418002000b407454558404104c40e10346403030801c0041600700004036607202ea51f0445014261480e08104444444d25015640700440741c1003a4003409414848903003c0380c0042c81a0942e40c0c0414034000a6003450300460303071074200400e0190f100105003030361004078805003584482c41d161a000e0702081c80c2540005016288054801d500621007000100400c1a0116005004440920f090700b581a95040e00c18094007585140d0071040c4c4c00010b03048401c1c0700a5008260341ca2140005002d894500003050392071f6080d14005d00c2c1c2240840b07903001c0d510400707940245851081413500d2404d2a40300c14400b285d00d1412002200450740c00c800558 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 228389910 1250 228388660 228388669
    0x80610030b0a0c231b060105150702060d0c020a1208091612030807050705030307020c0a0501020114180a0c090b01080c0c0304030605040305070f03020703020909030a020a150e0a060b 80
    0x1907011280c4042800744000b03c840060014400440d5401414100d90703100744140118400c48a4a40480c1803c80340070400c14080c3c0d80b86c000a1280c58851044000760795002d14440c410b558089800400b114285501d8281c4100a00f900601d034030114001c0704200c41c005490340c1c0c1c0c0e0000240440da1245c80e40d2610310082071819240d0a0b4960b004240c12008021503503040c1c6004404030342c1498940e02c15250140103440c1030003200d200610700d0002100b005800760b0700190f8508401c0c0304a504908a681c2c0300016401c0b1040105e001c400084040001707100701c00681b0030313a086650f000c0101c41940016444444080039103411101080b91586070324400ca41e07204000c0c5e41c1200c40c50190a1500349c002c01c00550340e00c1544002440c681d1a500014241401081516140c0d604101516610706d818074000752100514082244204690b8012490700c181c008107641c5600d509800070406a1070316200c4100b480000404203501a840350260030401d04240650044d45100780c0c000f0610018000400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 228391160 1250 228389910 228389933
    0x90d122a030b060405060f0c010213030b071b0b0a0506030f07091b03180b0a0b06030a200a020703031b05030f1c18110f040501080a0c080a020a15050408061003 70
    0x40c801c0f9001c2c882800207a070b85208807801c542c000b208035a554050700c010540640920383c280b01d035001000f00000306100c82c8020203441780d00c0070f41d00d4544038140d00d01c59410f84006520080e15043d030b503800045818206500c40e035001400181150ba00b500d03107401ca240741c2400f0b038004141c0e0310344a03a0582003140d540d042414400ca07042c1418030940340b10700d11503c10701850b508003134051001c0c0342c04a07014140507030280000480203864180d580c80c002403c20040c2091840309004013001c8c103003000441d00c10000b624180300c1c055000d0701c2c5180c5503481c200d400030301c030415141c6021340d41c4001000054040006243c0140810034294440401544044a00e840c0c0c0000c0074045050440380c01c0b609c5001d050511000d640a6014176101103190041003025014a2a981e0414038101c004104003800042199045128072a4401080c1d101c48841d0707144e18403031900070b4003c0130341c203014042d0101e1003811014100d4246450307801c1a0795121700c6841c0031426520381030a1480c0000034418081d141c481c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 228392410 1250 228391160 228391181
    0x2010506030c031c0e06070305030403020d03111602150301030501140f070e01050c0102071b170102041505090105190503040c0e160e0f090103060b040b0108090d122a03 74
    0x381040002c0c0c1c2c2c002c2130f2150f40300c00c04400242207101d40d00141038000c840300340c030b00b040c09030003591580c500345406009680709030340990162295000700107480303200b4060150090000c030b69690070310000aa9050f5070b030300030200890380200d40c195445142d240050245009600910000c1190840b120800b11020406440341040205e08410090322580004603007005003000c3c41c00c9941c0f074440b01e440078020b02032a08002c090714507080c441e0189801c0d28111005803468803440061141c9070707903445401c0740f01300e22803102d50024118155160a0080300134042d000c4040c14510315021034140c0016046074501410408980048140420b100043d460000680460102c42c01035007015580c50309140c036240f420314100050345003482151340b541e5030003165010b0080c2503904256101d03e0403001804660b440c85000d54a40540c4050940c031a0040c0d41c003030000040036001510704103078101c0310011100072010501da03e421004400820300301803000840c140d0f82c10001d002c07101010090995500845 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 228393660 1250 228392410 228392413
    0x60c0f0512010e10150e0a0501020a030c061a03060f1f0302031f020408010c030219050304020d030c02061215040501050307081005041a0106171e01030b060120010b010201050603 78
    0x11404011616140907055410116640c4103a41e506151340100441d035822600d10310525190500495030000c212800c010300448120b1b03507003602c60004aa44581241d00640020505055030740130601d0740c2c3c40a014000341103403e0911019090109240c0300c400c2c0c608014800b0f6140410503100010626400c0d1140c0460000c80d0140ca16000a80d80703607220707952480c18035040201c00c1c426000c694100c41c0103010900084c040080f031500064002d4001010003100e111214124650349071281e801c030b03807141d03900400c40b10000c04140c401320b582c0070207001c040345c00101c10000c810071454075010741031244003e401e0f40c4080100000c00d100641c1d5040e070000d0300a5016040600824602141d400081f448010001600355100e05049242402c1610f141c4c5101b080e6400105140754401c21111610102401002e0640c46102d455025629401e40d4032404210f5a0010700018644410f1107820800514050910203c3c08800001ca4450601d03500f825031b554080b154a25602030180d01d900150840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 228394910 1250 228393660 228393667
    0x1e0606120c080c04051e1201060e01050d030206011a1c05060f0a030b0c090f100806030615010804080901032903010e0a050c091003050a0312050901020304050c0603060607060504060c0f05 82
    0x40c01c0c0c00f01405103005c0d140c89034014080c029000c55210100c8044046c00810350f0000d5540100c0c00b41c020f002c2d5007e11486443e0704000402c0a05080701c8100c0007561540c01041c260386001a4584014101c001c145203a25040101c13005490240c03403402452900b1071400aaa82050303810481070403040c500c0103000c0d4100c64420004288d080e00e69660040031000c07000e0340c0b41c84400004d81000f060181c0d4079404a078929840e4405948810301c5441158203a049a881d612543e11900d151001018024002650f00e00010300280781000940201c0006043c040b5100418002d070508401c0e00c0f00f0250704070440070801615614090081901c8809008042c04058046485040c2c60700d8044003010301a410b41d0b408100c6000d01c900e801030045030007800351920350400745002803032886808a0801e101b810440480d481501c18421280034991010040109940c1001402055040109206d070b0090051214002060b0b4038040c03070384290711407000041c0081c85004042d0464101c60614000c000d0180f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 228396160 1250 228394910 228394921
    0x131e0602010c0c0b0612030304060e0606010518060d0e010c080405010b01030603050c0f0f031c030516020c04110c10230f010b0702031c0c030306060809030d1e0606120c08 75
    0x480306409541e00110403104c60364070032012824100c1442c040e8072451200004100030f100e010360144805d0310703001c1d003501c605e515540b004545502900782e01003003028501c41c0c81e01291034500b00905800a0000c00440c1c042207220105007106c95808422002c101e944040108125080c85026072031503013424104581d03402c1d602c80c5590f5030066105940101040490740c405030b40c581c00384030000100141120f0301c0007080074800000707032885c2d10b000340406e0810b0b001c1072501851406610100500e0350080005460010411015044c0013045550b85081044030b00801241407145d0200c600f60a100410051100f217103c00c0640941e0084071100c202c07000c00c0c000c910780c0c201c42c5281100d8a8052894440e2901d00000e81048612929010704691054204100a41056109a026000361420000c043d903915003511180c0f0202e85091050304100b080703610007c2140d024412040c11280d044c5103901d01030715081c2c101c072102e40251010a03441c0d154409030100340d000300b000300d02e520318100366682440c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 228397410 1250 228396160 228396167
    0xc050601090c0e0d06020702040c0507150504020627040c0207080f01050601022a0301020409060504140609070516020a0b040e090a0206040e04420b180408131e0602010c 74
    0x1c0110213407041c16002103c10601c1220340690b40040d800400410120b008424058201c0d480b0712812143d00c078402581913074100540c841d1521941d00944600e01d042c4c10a01600c00c1400c481500307a030b0418118207241010340712845440186c0f1000e8000741445424040502e107070a042c2c00c1031004583c100001c21440d0303640460040b100a006442003212003003403114445490550017007e0750190703c04140001c0301c01e4280c2000701160000d540400903440804031170300d05600c0494a0980040302c190105965034819001848032400c0b01d00418031200c05540024400c80b0340784c1c8548070301e139800b00c0c080c0b10002c03543d41102d8011050030024a6002041c1e0301041040c0654030401490304a01c1000409201803100400409a02c4803158845500c5007070941d501101c1c004404032400054404039240d50240d48121927820000401c8034580c4080700d01031000c12a0001c0c4101c031184424044c4044c1c0c0f120b600c00c4c8c4001781c85034200c0b544107084410f6603481340c1813490b0311050031a81403882d01c1d11210f81 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 228398660 1250 228397410 228397427
    0x1103041208030402030715030204030212030903070b131703090a081f0c1b0606030c140d06050618090a0506070503040b070f020309030a0c080607031103070e1903030c050601090c 78
    0x740030003825201c1e42d403400080d09203516a444400802032801f02c100070300354184d000301b0176079100721030103902c0c07521500f400d42d581e0150103001a0540d0040d2428041d6103c40d40c0586200680f590056403815111203203071b4140070206ca4040f04551010a40843d20b01c1d00740f40c24400303071440f58000c2c010075003c01c04a180701624014075a8002d40c0e9007003031130b107524400c00448500d1119000380020300b601614180004140c9840140e4611065410100d008020391800d01107010000b031014108007000e4075108000e2001034504c69100500c4e01074458040d640348903c620564141d000f9124541c5581022400e05074010440c0003007003002c00403c00060b01d01c414941d04040d03036107080d111003e0b42c0b160503403075071145440d41d542c540300d40100b94041100c80c4c141c41d02640c940030149d40045d216007905400b40d8514000c03d18031100c0920015410707500c221805a401800100502190300d401c10030030302e5140040d04140d0009411203090800e010381003200303d0041c03c404508000507111074400030080350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 228399910 1250 228398660 228398663
    0x20f03160b0f040302101e020303090a060e0115030b040c0506070305070807020f09180f0c15070302010b04092907081503030d1b02070906030209010302060a050d06060801050111030412 81
    0x71808502c00300e0105041c010b850207168040c211045ea41108003010344040715984040c00031045420103900801d2010007902c1c010001440100f043c03d01940d21354000d0310390100300e000795642ea01e03050101042030214031402507001fa040d13200703030f820a070074500342c040c41d60740000e4001c0c0f01c1000407100003980f02080343c0149400c407044a44034011403002400071100e030182258040300640500c5100b00722555000120a014402c96040c800d07024070040d102c3c0201c40c0210b03840a81e8011000e07400a0311401403001610030310000481e5458030380020110742d82000c0995100d21020111011140380b134140b100b031440c20380b01d40c8840785007583c001015100300414082c10000d1035030300c02219440410544070145450b0340184a08080520080c403600c0420000100600c0b0740c00002a10304e80d244505426030341c0181401a4580c02c54081c4245984140038403820006c0400080e5504901d9108260280043e50b4521480d54500743c001400c0340a00c0201c0c00302e5030010441080001c40c6111800c9406 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 228401160 1250 228399910 228399929
    0xa0209011101020a020a08210109020c0c01030b0d0227070c030e061c0216080f07060605060c030703031107060f050106081e06042a02061006080906070c050c03031204020f0316 77
    0x100048c0d8046d1300c40c0345c41401c0220006c0c0001e0000302c2d216100341c02504040d101c140c1210180c074040c00044042d030780c03000d0b0300b40e4000b0242c864030030240c1085086000d8602c071180700180e890103940342e507140740d20302141c0d502c000130958050401019400b480e1010b1522040b20300900380034410b80b4560b40035850000e0030707078505d90006c3c5000100b0082070744005483c0d000142c03140c45032510718100c06036601590342140c85e0340c603151000c112841c00380309445860040000175030074a00705980036001400010503c1c4082d10003445240300151242c06800c40074041000c0c00706940d40740c584044c00320031000d1300c00200c00d01c48c07110700702c050258080d5043d4403000c00c4074041020f40000303c110310948030042208211501600d080c3c4135503070300050558040d1084041c0c40c10201e075075000458446070266001d00b01e81e0070a40100d1b214901c10b60202e141c09001d40259040c800540700003902e558000889480503400442c01c00c030a61038040e201801c4038101b54007038144401c2d645507403101e82c07a4502031180c1c10b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 228402410 1250 228401160 228401167
    0x406051902160902040503060c0a0804110f0a060203070b0703052a04120b07110a0c030605100e100e01120305040b030c040918150c09060509040f02030a0209011101020a020a08 77
    0x40c41d1081200301d060040300c0aa02c0a000e8546030740360041d610030b00480d0300a104d09004031b481180e031041207400c0c8080316602da840d40e485950700c2c8811840302c01c5019601c45a0042504603d55800c0c1c007680c01410150005c690b60381c82441c010f10400401408041031514001c200074000200544601d44880c20950f0301c96400030f120110f00043c0616008024603c00380ca034000204100249150301a90a40d160441c900d100f44110b690740c1c0d900f03010014030682c05200104001144d9410441d0403001e82400c100c0c2030b60300c951329450300d003c04440b203040300b0100c0344081040d00c0c0401410f80c0074016144060035104a1a00c000d001c80c07041e4403c1c0195444d0020004410740e58440070345010b00300003a018802039610182d0f640620300109001e507107942d01d00c09009a13203440380c4141245045191907a1003601d10b801026506038000d414030b40e4000f078440c0c841c0000c1400301d01c021271140b80c0030b400058413001010001025107060f103174044c20b240e1040148a08490700020882e11140c0e11a1000d07a6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 228403660 1250 228402410 228402457
    0x4090816030909090309030308090304050a0302090a0f05041118060904080a140d0f0f0524010302070501060f0e0105090c19030e0d0207170307020904060504030509091302031002040605 81
    0x20011803c0d8000d1460924045440007015880280041124020341d592021511086103140d1248100d10031180c0c0003c07070080c100300604115000940c4200f202c080042d80b050207807580e400392503003103034100d5001c1652241030000385010000000f40032807a080d181910319121020400c00306c0f0261010302000d8010540c1c0b400ca034030a2200c0400b28484243c0281c5a4000011402c0500040700000480b46d00709100c00742024058131a80744514184141d941c980382c21209491040c000041030301d070406408104a80c086402409200c00503d4101d02100744549409050140c02c1c2c0181c028612601b0034400303000160314040255408041d04000c0a2102c1c44200c3c8160002e04500c181c1c40e680f1b018a00d2001129070300814528100c840c1c2d600b001803100c045d50f1100752a8410190000d502c0b001324030100340411004d81c000c560103440703800c1c4a071800400c0302c00900681c03802c6506240a13002841c0300e10441c103080c00324100b078103003084095041c030341000405881030103a0858400c1e080a039003203840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 228404910 1250 228403660 228403667
    0x2031b100f02100f200d0524010c05011121060102010510030b0613060e06010e0f10120204050d12140a0e060319021804060b07031413030501060e04110409081603 71
    0x44c05d606010510729481070b8590848a81d0401841e040c1c0e440d290400144042c4000700c0e0081c2200018142207003030350f03800001525000c80410003502c0303665032810005000080003004000d08040f901c807130300304200c1d01c42c0c103551070f520001c040300c0c1164100304c1804020f5902c0b8003c82e09495004400b2661907480b24080340b20700d00c8141c40e91000600340900020f0289004046038011700081e83c94107a0b04440b14240311a04c0a401c204640201540381c2031400d043c41004d8101001d42c010781d001d460195900002a41404110025501110600c6850003140d8226184480319565002d0445c140307481080c011b01001040e005c1940210800400a03840004403c06031524101800d011525400300030010120380c540f035540a4055071a116000c030b01c1c0740240b81964030301c0354590390b81c5c514540300780300282103600149401d0154200300000030000030003e002d0b01014101000d4210654a00b504029040300c0850110a000e54940415a00030a0b400c000310b41150f00135011000e0b01020070319040303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 228406160 1250 228404910 228404921
    0xc0f010c080c011b0c061b0f0e130606020309010f09080d050307020c0a03050c120a1101050922050f060d030906080606070507080703030f090605071b0302031b100f02100f 75
    0x1007602a00200c035003560315080140a61042c4c0251b10070041d8800341c090035801440302e6410203010488608100014900c60b90007081038080180c402d441d03030f0684d206000252195508520003580010a01499a59010400703419242091503d842010b02d003d04007501c0d50b000350325203020003000100181c4028000c01010110001c0a0228203c00e507890900c15100d4102c0b110b11846050141003014990f880024010354180e0404070101400341081c0040d00c0766801142c0c4e00750480b1851502c020022402100701c0e201c0d400d0318501041e07500e40500c8100c2c01100042203680703c2c0200002e140b02180d8028400410749001c0d0502c00705985070f13440000c90b2400b5449008046108000d00459150004101d0101700c0b442515108100078101200351440c1c0034a000b0747d400a94180b243e80e000c00c1036003819440c281920010040c03140c2e100e40120b0305251141c0c2c980d10110700c0c41d1300c07000564102007140200703024640c9800f89a004540c800207440e10008051a1400d0b501c0e00101e03a170003000c56210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 228407410 1250 228406160 228406181
    0xa0f031b060c0f0227090c0301020901090909050c030604060209010201050106110312040c090e0c100206060312070813091d1c0e0301020c0109031709060705071b050910080c0f010c080c01 82
    0x84000c90b41601150382e020301c5c100c0300501c80740030310405000a82014025a80035020503142d43e2200b50070176609000030701d49014152801c0c86030403844902a2020301155014071b014023030260b0364000d408006070a40b001a4844070800c0070000d4041c1480d44d011040d681c240114045240c002e4445003800c81c0001c489030807581c41c103880c0081d00e0b405400c000403500700d2500d0948041862800014090707031030740421260250075402c0001e002070a0418100246207a510420000341010042e4004100405075074009043c8590f459000740749220103c0700c0341440711550401001c802d145018a901c00102000c8c03107000f48842d41c26006000d550a4060360021000b00000300440b030042c3c24001d01d035144e2002c3c1030201d0203040c40031500891011038284c2c4600901d4481900d40080740d079500a030703600c3c504d880102d48a12178001007009ea4400c000c1c180140442001d400e000790814800e1800c1c89403d900b9184100d0040c0a07031450742e6002698000304c160080445510351807124540e9006d031901030803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 228408660 1250 228407410 228407449
    0x50a0902060c07030209100302060304081e041517090309010f021009031808070b0f160507060908010c030516050a020f0703032f1203090c0a0f031b060c0f02 69
    0x340d0342d00c03034207000032880b0441380211107409184d1291444c003d0440342c2e501019401000410000e804160407034010000369441c0c04a408941c0c103481e1420607a40c100d50401990a0b601240d0141d001d03600000c10088801c7c117025000d504d09002e4071042e603030b20520b0a09418400465507005d20f0600900208c003261074a204240328411031132800070800c1080b51a9644404841e090100303002200042c10700076a025400d40616000d500f252120440d0081084003e07400c82010703408000620620082000301040e0300c034942c0c40f81c180703400c07107080d500e0301e6900302d04051601080240e045a8801c484508110700d0910790340c2d40740f500100328181107100107000f62520401c54000300309070780800e810348000b540051007000c1103803441c00e80c201c80340750f81e808103800c0d8010100300d0a07850001d0b000f0350300600c8840450702c54481d6000412102e05a50b44100f80c0205101d0b020800d024404507050b400a5800030790844072804d2140152942c0711204000d8290038004074010304546903480081120ba04050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 228409910 1250 228408660 228408667
    0x506011706011715150a0c02010e0402160609151a06030a020717090a050603041a06192301020d12050a0209120d020705060f071e080304030801170c060d050a090206 72
    0x18100c0a208600310744445c0102006a401002d040d03101e000e803100301800341e48907506100c080d0011a03410000120701c5503c41d034200010709125010261005140b8030235070011695880340d00b811086010004080d8400500702400c2c0f040360418030720482403800007101c2580e101c0c0c5980a4040c0240a440c0000705891800b201c070588080b5004041c14402c0401c0700c0001135a910344040c0000c5000a45000702000c03000122510306900d04420294445809045038541140c0a1b08483c0549255440301500d945400300120800d0109102500360f0002070004044450520b400100301e4030100f4201a250b0355228003044540290f501241e600c1d071001418180803e055102060302c400c0303104507403000740c403c411002a03681081e4060320f0300a4030410344e0307900f803040c00c1d16500105052180243d440410034550b99001031a100301550007580250b5036a14258109074151442c40d02032900500142c0c0440c0142e41280d94400440380d000130844808111038450340c4c0300304041c21903040001d5000c3c0010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 228411160 1250 228409910 228409921
    0x5030a030302160605130c0b07170c0a0503030705070314030c1c1b050405090a152601050705070b010801051308070f050a03021605060c0d111002030109050601090905060117060117 79
    0x1981c000070b01e1b50040d50041b042c280d031502c0603141845035620040104c0d08029881200a240002402003403140c0000d4808003541c696403181541d01c1100c1400c0490300c04600d0307009040c0d019184c41c2284030021407461030341c10005c1c444200c03030044020b01c0074402c0400003030302c6400380a40c010302100c41c91659511101401d02c1c6000d020b542150041c240500e06030030000380d5100c0c0c01d000300c901560000c1000343c0000e080c445504042d000d1000c0241409840c0b40301c001c0c0c03d820074070a840c031aa207181c2d40c1d41d855a02030301c0c14140c10b02040c5d22109041c1e040106019214002c0b0900404035680200607698551b00303460150f40046030791a0252803801168558014541c0124010b50400c00b2041d142c0c01c1242c0b81c1c0200b011a000e00354168109074400d10ba400c4101c1e014240300700e014041c400465068181d030008500c144ea000340c102080e0f03191103a06101e82540c11688000c0a00600c031018000c030304d0003500080a0307030b000502c03400388401d00001013150fa90050750541e0521021040f401f12902e040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 228412410 1250 228411160 228411181
    0x8010c05031501020a0b1803130e011d0705030718030227070306030f0b070315081b0901210204021620010509151c1a0301060f05030a030302160605 65
    0x40324410030030001c1c042d41c100650710201d980d61003143e00800380c8201d615100384044800c6403500c03600c41300d44070402403c60304040c80b07150307032006203c4150380042c90342c10940d699107031144400d030300145041c0d002d0501070201e40050a0360f5000b502840c11184404200b0503403003003407a00350b0002e504032410f03002010381a0080012254208100b410251081e200c1c00811130413901680310152808495402c500006040a0805904a4200d00e404200d40101c90744450f01350b00182c0c04070381580c0c0001c0861441d02d0054007035035405c6008598a43c02c0390324011891604060070400d1850010905003140c08540d51541682d448450644003107030b07030940924040c94983c0a40d03040a483d016030510100c01584a402150125103010301070001035912070024003000e40144210900e5401518000c218050700c500c03540480d00301681c601c0090800b060145821a10315401c882d034901c20300c0405000e140c40000340300205c1a850324005a072110224540e07508400c203003c00074162800d12040c096003040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 228413660 1250 228412410 228412417
    0x90309090a0207060b1009140f030d0c03020105010602030316030b031c0c050f01060b07082503050414030f03090d020105070c080a02091e0103030804081219060b04080a06051008010c05 81
    0x31030b80d41001000ca01c5c008014800c00c06140309400945140f1041c40040c160b0426031602010107081c1809901d007480029041c0501c070400c880025240750a84024540c0c24051030b03004083c03500242d890360411103450442c01140c000303854140740e240c22042c0d203540c8040003031180d0482d0403980c10104006800c402020720040ca0001e0341c10b445030769501c0c0c0c1c150794184070380b40440301168030700c9180070b6603070752402c281c1c1e0020080301c101d030400325545041900da0580c000110b58826502c3c0ca40d121b00b06110100b41c3d40b1802103180c001d600035040303802c1c01c3c84008103d4002070011120500031030080e01c0101c8651294580003400041540b030009182d040004212420314402c4619500503690200420441d000100c0903040aa80140040001c81c0c0250005038009000e103100b246421030402e58038004603001d403054032440041210700791400440c0c1c0300c0d810181a8507840130740f41915144415584080f28440500702c10340d0340340880c0c16001201034180041c1010310082c000030403c403202501641 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 228414910 1250 228413660 228413663
    0x50a050f061e19051008010e0c280902180a0f0918080301090b060904051501030537330b120a09020f060d0501030c060c0c0608090309090a0207 63
    0xb40206039500004450410385882450b44800100b2019001c442d00c201509002d003070b0750b904c207070380350000f0821403401c0c011564009403034001400c107174402206000c2c89210031021080000300e0418845001c0342400031540444000700c0d000343c2c45800c1c491401401c102100540c582c0600c0705a00060403500b0300340020304949031844208051403172042d83c40180310f0b1b0b00200504540742040144003081c0c00e03610580400a001d05014149040c0720b010604840f000e075032840410807402c14039042c56034540220755200840351407a0030701207c11500d4040f030741c03924035500681600485000e540800217602c1030321208488079030b80c504414180c0c0903070b140005550403510300c101e001e0404030340e048d046000c13545840326860848110b65994011b007070003001c82c0300c0d00302e07031203100e01c841c94003280e032428090b0105c281e0320100042c45514600e05030000f8000342d4031030340901c541c100d0481c0c081032402070b07044201c80c0f0a0078111071230b56035200e40c070b8114401c400d9100c0d0301900c95000e111030381c0015406444040d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 228416160 1250 228414910 228414931
    0x130311090c0a02061b0706050112020a06020c060708160506101805010f05010e0406170d390510060e07201b0f060c010e1005040308060904050a050f06 66
    0x25141c900060800e84102ca52110140c2d00c24004a25035002200180722003030304040b0800c0c00c05a05030345103c00c1e504283d000c04850a15141204c3c10343c94445e00c900c000b403c45000801c1c00743e0106001c103119008000014007030715804106000039080380c40c00d17600310a0b030210070b45409240172a1040080d41550081100c40c0380c20884034040e0700a0341c440c00c0d05072204282c0c01c10600340340c40b00449000882c41c0c1003d0700281c8950b40000c0d244580024206025030720805002c03004804e980013411207002c0c40c0b5050700c00b01e00311081c036030205142c240340001010003801c0200c200d21504040340342c4000340c518090b46a151000005200601c903088500600d06a9104084015039142044812200c80540107050b0480e6040c060380c46488014140d444e034002d80150510704228000581c01d400c240500c65059441c3d20060140c0b80040c0420103159a49030020020741c206510010500c1d000244070900481581001c6004d0080400810b00302c503034401c0c1110003521051032a140c5950003a1001c0018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 228417266 1106 228416160 228416179
    0x190f020618131a01050301030809060c0312040602040614131815030501050a050c04030f020907030209030a05070501110a080904050601230720030a17130311 69
    0xc9440c9a100000c0c150103c0300e0200481c0d000220450400400f040140006003181b0165080712905840b05038a07281462a180e1039842210512041a0628804c10013000040d070020004d882d49581c8080c000355042d83c031813465004a910001d18080c0710007062110074005901706100c1d4030080404510641801c0c281103c02080360000c1d601d9075141c00400c00c2100d014082e5507040101c059101e4034162031501d030716240e020401030080c840c20303485000c01c03e0248680c05456154070014184e4803940c61510b400340e030b58240d911486020032074801180300442408141203030304030303040f4004515101c240c07003c0000805008120701d0501540e186450b85c0d40c043c0245201042c20b080d1480c2c0d80d01c155034107000110348044001040c0302c500d010a00c20361610041091011141d00801c8404182494003d8101f0b074040d007100c0c54001d0140d04000814400c0a10490380c48500c1034600040 = true := by decide +kernel

theorem cover : BRFrame.Cov 228237410 228417266 := by
  have h0 := BRFrame.cov_init 228237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 228237410 ≤ n) (h2 : n < 228417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
