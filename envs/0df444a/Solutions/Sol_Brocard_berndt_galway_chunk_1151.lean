-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1151
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:28:37.773541+00:00
-- url     : https://prove2.me/submissions/86c1f82c-9963-4a78-bbc6-fe2f0b26e335

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 206834532 ≤ n < 207014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 206835782 1250 206834532 206834539
    0xb04141c050d2706030203130204050711102a0c0c0f0e0f0105060306240301080f06071b030f050d050408030604060e06030a030f110601180b010302070b0609060d02 72
    0x181400d02000080b00c4941c00c426884400200140840c00b0312100d5411401c0c00416042000c2000443d1080d801590b000c1d40602d21007016070f00e594000b0701078407401e443d40390009034041d0031500711080c10b200c41ca0b0f0749500e001e030400400903031201c000200c0f4800b01c44200e002c4040400c5403012401000f81c41c1c107060b80710f00f00302c1105458454059420f9001d006010004064800003001300201c101414162a0020502419130b5102c2c0108540140055071104d8203801c003021901d07250301c001c000b4602802c05840074103007030000207503000d1920388010010000c210702341000103105071225400c9600d840d09031920002d1200c40900560300b0f40b140c540352031000751518042006014030030000d1401014106c90a00c002951039030f0648081c002902c1c01c07903245c0c010461140000b0300510060007400740780d052020b142c0c50302214050900c83c003640032617903030014022411030b080710502c1141c8003004c0c2400c045040211a4440750468034004090174003c014440c042400e5958106001b1285540107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 206837032 1250 206835782 206835829
    0xc090203010602031803030c100e01060302030a230a0308060d06020405030d030903090b04031a1806040309030318062f07030f060605060910052a0105100f0b0414 71
    0x702e030700a6495000c18112041902248440100b528003c0111100001c0260040c8240500b0000da000180410082030b9520b42d070781d030800401610b0038864400520700a16030800e071001494071450001a841a41004c40d400040320700b00025008a490760f0041d40c03d8134540c054110b40e15010009105036003040c1d600d032041441d101e0009605411108205c0d202c0d07a80c001a4640e1140c0102603030281c3c0c08000c2003441e070070103035528068012040c13a502c41840520401d00300c070300042c280d04020f002c0e01d041d000540014400d00600d42c0226400450440010380d44540e1071418000400501d443c2900340040e20389000c0000e0f8801d026180340d0a03442c2c0c2902034900c190358914222204405c01102126002c1c10684000345c5c41c60844103071241208050150244007898100840e100d40c8115440114140c200c0b0700c1200994032085401407040b06507000007043c1c140130440b9034103403c59504c8001c031186801814003007032100e50240c03000c1380c3e60301000d480c98103c5840001c2c107000000c2e18054813161003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 206838282 1250 206837032 206837039
    0x605090f04030909180f0c0504020403031d1f1d060a0207030b0603070515030a020d0207060c1707050a0f020f0d020607090605040f0510030f0c080105031002090f0108040c09020301 79
    0x244400c10740035500c00d07200e940050b41e0f02c3e018030b010b44041508007508007000501c40c0003c1100100001b02d4039104002901c11a504e580008003243c0098000b600083e00004001800c180e400c1c0c07010160460846128180a01141c01d40c24080005101c4004014980c100c030100c040c034414086006100040005494812084000703503a400c0c24403054418058810208009041c0811841c0c10342d2000350040b0499403054043c00c560794400703040c034500264200610560302c90301e0b00c00b07411110310514000c00c4180c05124003d2800078480c000351104000d01c2c0a00101e030340c018046940c8060141003800801d41f80010580c1084d412640e16103150085e645610141940030400c144512140c0d2542e15026848040450701d600490184a03610075080c0420b000e07134074010f00141d203813249070710b40490004540603d00c010b94000c417044002048640006000d2481c0500440c0e01c07140c0074043c11801d000681380010403650070850518144401e4a0203e41405000e000c1c40e00988000300003513641c0d595 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 206839532 1250 206838282 206838301
    0x70507060b18070e0409230f060408071505100e060301021b0106090501060c05030307030b122a1c060207140d0c1203020c0c19151205090606090c09010201060509 71
    0x200d80c404001071a9807490000c0d840c0a02c07a4080041d0042c4100e4100c0e501c6c22040c0160740c0e110b11412025100c8e2818500c1001d10401210b485144141d031002d032501d86a20707003ca40340b03800d00e00549456007004104130104000e000004110762141c4e4070071a05072103190110f8020321030b5507007131642c0c501d4440e04212481c10540124040764003000081220340e03a19041201c00c0c2c110188005c0150b0020404a2160382c03082d0844150010014600c22194686120722854000c407110001d8410035081080004131040401c200c940800950320703c82d9400d404c03641c003c2c0500c40d10b00010010350340070030001c003800311900c0c3d03400b1340030400012560300940650b03000d401442040012100540d81c0500c8440c0b040c42030082e11401d0444500400c0c01c06441c0d4200130494100d2854120580d101030700000744800070400003107200141e0707254100301c03900c20708c04801a113400401900940d4000800c0c801a501e50710301c0ca540c800070360040d454a074040400100d0240c080c1d6445180c0c840c20007824040e9001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 206840782 1250 206839532 206839579
    0x10306090c050310080c090c0304020a0b0a0f020f030307050a0c0804030f0c09050a09030c060b2d0f0f0102070b0304140619140403210e030c07050126070507060b 71
    0x988044c4e10401c0e80e030f03032441a40d680d015610609034100c2006004194229120340c042c40e00140300411021240792540714140654001486000003e0084410012802c6e0144440813048070200301951962074811400761092007029420010071020185400c1031106013026580a554010320f00e2046030303a01d0820483c00f42860041851480c03170400450041c0000e80301e2035036483d600d61681b00d016440da0720b6202c0240743d10180c0b107421074502c440180303100b080541c01e0f510b0711400f9017800b0310106d9802c0500040c0d50071041c1507406060039208014050780c00140d54012115080c070040e0b0340342c0e15450031a9580c8400c0412000511500040c0850b40541801c050302c1e6145100c07040007102e90740301d50f803a8010000c1e18050b0218074525410841c01813111030350f40320301d51501004111003130030304582850740d40000d40d5025250070010003444151380c0140c1103121030240c49a0721061602e50722078103008081c007a00b420300388000040c0321010402c0c0c54025441b0100000c2083c2c400d000000003e64101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 206842032 1250 206840782 206840791
    0x305160f120903020c1206040f12110604030201051e040c0e06010522090b060918070203070203060f010305150c0a0c0303090b1009050c070b010504020f0c07150221030a0902010306090c0503 83
    0x490302c40c41d036071b20b00400026211788666007040c1c2214807040c5075140c1942c1c41c801506030208208080c400b005040038100505400f541c1719071300004a9152441070303104601c1c01c480c00d0504411040303003031101103024119904165440700f00c03090303100d840e20b2005039a14030910265a00c03e000425000e00c854402d500c1010440d40307501810321a824125040102a110ba0601d05a105102c8c0690980310046104155030184090040742e24250442d0002407400b801200c0b40750540f10b0303400051082250600204014541d40680c01c60607090014030409103024900480003000192801d020074584240c1104651641002c090040350524802942d040607480c0641d582036418080415001c0300c200048030381040d0000d0780c1022036420042044065440381c0d22110803a0020300c00341081150910107040249000d01a110581e060410064240501c245002c10054592400d0265034801070084079480030a2441c0042c1c0a4410301c0140c000740400d4103d516090320b89011100c0c40394100e40214000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 206843282 1250 206842032 206842039
    0x303020613020d030e0406050d050f15240f0406060806040c050c0d0309080415051c1401030206090103090b09030a020f07060c0b0a0212150f010305160f120903020c 72
    0x196600c0c00148006000d4840081d00220fa601800c00840e20030f0000951010700100003248050303460000624861148105550a41241c0320782020b017041080781c2108001601481300c4140340201c110000b1041d00b80c2c0540d21251000c10f42e0b000e550700d0040400e07100000400c100300c1e5035100c810040000c40d003121481d0007213181107085070005001e1010341d81c8841344440201406150f092046028000d0100f0890f0040750501c004204402d0350b05d180121525966101902c0d02d1200c400010402c41c50040818110f03c1c0c0894440703141191683e040c10349405a400c50341d2603000d040124000c2071101c2024200851000500c104070308040014501c4000701d508955000750040c0703200b612200305115003808503542201e1540001d0036081141d501c01d800364001420100a0b02d000c00503050210741520b0700000c2600207810314074042440e41030034a000e00e800c2089251030401446583c464800700c0040c850b2400031007100520580034041100400c9401748410300c1103140c0607540b0341080c100e1921 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 206844532 1250 206843282 206843293
    0x30311030a06060e010e130b03070302040c020606180402032e0903091403010e15060604030c0f06090b090a05010302090d061d01050c130b0702010302120f04020a06020d0c06021b0703050304030302 86
    0x285600c03800300940c900800420300390b40c1d081a180348500902c250500c8c0c5405000d0042d0010250359a4441d04404004036005008680f41007800c01903100d8484020b021229800347c14070025031000034031941041c454501d1081d11011400712400060100c28280b0034807070074a203065003010340c4440c9030b10032034000940200ca4190b4000426080e40e80d01c16004003503a101d001c0c600c020b04152210030381c00110262403e0314080e10790b180c882d042c01150b00100c0c0c5007003007400100070590f40105c81c040109080b00d686828518920001610540540f250504240c4c000c05c0894940e907a0b205180d80442d8012410080a654603908411202da8514070001552a260014851a04540c12134802c100003190661259007000c038500344a40000b40301b40e0400d5030a000e841c0c0d1411140d03141901410400e411412545403902c100310002c0070b80d07000350382103421441c40ca03005d41c1c0d004000c821045034031010260b1950214480c503111241031103c010061701c0b03200d5000040c840d0100040003900d029909548 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 206845782 1250 206844532 206844557
    0x603061d010516020303061c050a0c06090f030b060904060e0712050f160e0a06150c062901051b060c03070e040b090412020c0618040f0b1c030311030a0606 68
    0x30f9841a00030000d60410400950b20b440d200c2c6241019441c5606400700c2002c46071075035031524039000d504a0701030741840c03410b001590300104101d0007072454140015441d415950b8a07102c0e0607014007110300540c00240801c08010041c2c200380c5100c4103080803078022035500c1d840340c1950303480c0b00c6054440740540c0d000101034100c0440c15055480303044080003000b600c0c0c40c0040526100c004d2450240650380e900116491010170000e80958085998803641580a42003020485005044801210065802c040c407508243c0c0041c44007170b2000d0030315544407000b641c0c1d0030584080340788207041240500d10411940b61100d501643c0103041682d28101c07400181c03070502040340c0c04590b400e0b91040003040051f00154404600e18080c058910540d80701103078060104181e0f401008a00e103100704600140449400c0520034210074a208110a2191600c42c0c0301040b04c1d00030b0305031909960340d41c1c1da0794102414000d4000701207821405803469038030b240490b0b80030010b00303850089900040060300c0d41c0c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 206847032 1250 206845782 206845801
    0x605120706200604120c080706050601120621030c02150a11070b0417030c060c030106020d2c150703080a2a0509010903080c01020316020d09090c030603061d0105 71
    0x60340280c1800400d2542c079130341c4403050160384075010102004601d01020300041c034804058142d2a10402c1c0224031400c01c0c000150030311f4194020342c0c01c0d69251200801254002380c00c2a020100d55850f03801101600d418111560062030901a4210384481814480300903980c0007000038102d03550781d1106041c0d68894040c0c542102d44980c0c248840c050205200c1214480f801031401c098040842c2c0c6072800c18404c06040078000c4442448803e0080010058103030180700300b1040340d08501e010400051140403810354131128400c0303600c80234144075240c0300c240c031990290340d41e48240351105902c0f0607140c50020041c440880d10110440e0a141c1030008070000010401c6c0800d24540798400d00450042e0222010340144079410304101040100101041c2e90340010100340d20500000740c2c0e2817500f40b000a003030310080f0000308115071118550808141c0d20140b201d05903070903030001040c006000300d0214040c04031a04041c00f410300e8141e064009100381c031b40347c940424120009002a03605ca40a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 206848282 1250 206847032 206847077
    0xe040b01050f12030406051308011b02010b06070b0114240901021b031f020904020c0a02040606172d0a0c020f030a0e0d021f0503010e010e011a0d0605120706 69
    0x8020f002d40c401d0006020050060700a00343c1004000e66521556035134a01113030035211054140141805140d07200d051469080c01407010762802510600d2030305e4450343d2034012109051180702e5041102c5c1c03001251a035140f4a1110310080e0fa003002d228001c070744814031202c46d40714104035400b510407520b1100107080108030800004500402411a6003618003084598030a0b801590340102e5080042c04e0032640c0354800360540d115964001c04240c02144103110490b0b80f06d4011105000b24150070204264103c03035110f80c0071944020f19856600e482e0854190240c8100a00e04001c0e0010104a410082039006800340c100326800c031030031044103a00241d103e10900710146c000070415042c0121030304041caa0928801e20250202e80c40c03252410380c007680d0460306803030000001c0b8000300400c0240d0501c82c80c80d024000c0d085405806525103403a000c5455003802440045607c040b420b0a40341d036003039101c10020301024040e64124582c0d045013940703030700280c0242400f0a111840d200210a02d0703140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 206849532 1250 206848282 206848309
    0x11502070b0409020d060807181d062202030a030f020105161b050f0304140901080609100504061506020d02010e010e0c060304081312030e121011040e040b01050f 71
    0x1071940b40500707000318a8003a51124982e100c11544074400007440b41800c200c50f200402c00035081d00b400c008a441d021086d103500000441040c040030190211101001c140907412118050b1003008440c812183c036040404030f03500207503260281507429420b0580000018061864590080110345d1700d004c0c80c0c0c10a14512a01d003070006400145090084515044484140d03018908403800651520b445034619803150304a803101101004011845041c54503000c0d01504a000250001c2d10700b520039941ea07107860300400c610841d201c10108042c0f0034294440366923042c01022103040c803034a4280c040d40e03031b10860719007400542c60420700340007004040c800d9110411172074014007c11094002000782039040a0010f0754040b10410294106224101056004051406402002d0075a600b0040c1c40110014105030040b00710b44407003602c50401059940c1c098070303850000117200503e02045600e50085810610412804106010602c0420404581202e8080780c40d200e045014038288001045500c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 206850782 1250 206849532 206849549
    0x708040f0b0901060f08030a110307050c0402090d0605130b010f14090703021c0e1002180d1104090b0103110102030a12050619030b0402041a031b04021b0601150207 72
    0x103030040011004070a039034008029000108581d07864844004203030055601407001e50740001500d012850300454021122190781000d10700b44481911910345419603030709001d110715400264049140c0c0da552150001680182040209183c4880003a5601040b81c1003074a603569081d0000840400019900c4156019082c01e40c5150b042c81d82489400600039000781c060540034040c1c06c0c2840c1842040d1b60321051305d039001003410085c540d01a0f04161100042d07a10f03241c010051802800068034042e0900c0170240c941824195039810f242d40d80155000016074012b0421070720800340800801c501e810380e401601c00d600c1c1080d5200040e40c1d2841494040d602040a110503085c02e202c55602044e48400040c01c5081c41808410304000c81c00e140350808ca4a0f4460b10050106600701407042c2c1303824031400c10582d0030b0b80150b0b03070000380c0d60302020882c10f0041d03100c13940d1081d4584564041e06c01250203400300c40c1c00c146800c494035880748400d0150b05061001400c0a005141c80040e011301203c0c04c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 206852032 1250 206850782 206850803
    0x50c16030507060b03011103010f08070b03010302100e190e0a0603030e09040f0b04030c051015050d0203011d010603021002030a1b2a050f030a12030504020d050109080909070804 78
    0x3554180c03000d070050308050318040e68580031044640c41c20700400d6420380040c0491a900c0d0f042140c0c50301403191035007065a50ba44143c03014064914000116810369404641d0b103004519021400c50720012640700041e08060600c500040c485000541801a01d400700c3c149411540c410000d0800c8400071303c80900000c0980c0c100715103504100e12132503001030080900f03020543d825251120000f000360303000c900084218501405006061140c06140e40100005101f41c0d101c4025851900c01a401200c1c8504200040030046640949c06a0a03118002c0120751001160844140c004c102e1440180c4c0150204004a05618404012540542c0c15529029812164030710744010700390b1451021188103c0d0701c030089880780103920b82e01ca18a402034032400307600740c108400d00c4000300b00310302624025071060400d44001410090080101452840c4c00600f9544d030340000381c440d05404402a1071540b802c000311042c400c8803402421300131000e49200b001c6031944079003150310080c21207000d00440d000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 206853282 1250 206852032 206852077
    0xe010203071101020936042d0f020625050a0c050105120c071410060801060b040e010311011e0503060a0b210402130606020c0a0f21030201021e030a050c 67
    0x5e8075096440040c1b8040b6850209080007040d04040d6000e440c2903510402102803448070140c0c02c842c40d102841c7c1030070030203100001030f0b0341c0d41003108100728020301c00e4801190b5010070308001c60201444000c408216802c118460404907211032410340107441e04040700c01c001c15154059002c6406000d601800003056035140d483c10240750308043c0044410f019928005c40600208100c1108545018140040c1e40352400b0100341c2152016407041001000a120810030740541865181c1120f400100d81d840c5101901c004071401003407404000c0b206426608580050740e8880095442020140e8004c201991a004140824082e0255030070200100041c204250090b4117801c0760481d02c00380070352401e102c00034441c4040c0c84d510340010340181d001004204030703407601020200040c84c1c4cc01c0c46070030362420075205440030321011410500e0307c230300482d000c3c1c1014800d60484000e5901d5a00703083c0c0d4941010f40314009640140c800760400b908113404181c2082400040318485050148544904a407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 206854532 1250 206853282 206853319
    0x605070e030706031109041406040605100509060304060b0d050f010501080a120e0301110309210307090e070203160605071130090405090703050f0d08040212010f0e0102030711010209 80
    0x180d20203840d40c0110138851b0381020340300d901600c040c0c40183c503c030300c85a00e428000d0100300c840b00c1c1d000501c00d1924840300307040a070f00301013210b032648030549800b65269283d0525001420704058ad41c0d822680c0c00c229141407010100e04401d410301d946000f481940d0780c640006940e00104900030340b4034070340304030080152401a0002c0e203c008000c0c00216000701148100030094000300c500035099000781002c3d2060b1601d801040840004003d030650550800002c000c01e41c0703520380243c01c850403400b07010661050080007900d80310700d900d0702c1c2080800c210380b0b03002c40030f88000c0c0d9038800405d054058138280180045415541403401d0f03004920041021650807005100400316018075040c02c11070b030503103510b50f80a4a0322404084000b000800e1852804070701c0c0040c00031000340c190704a404105402ea9110380150b030041d40440701c2e00350080c4044407a030b005014441da04602e66141844880030b015040d00550701c1800642c8a0142648881540358242d224080c461940f0a11180c603400c032440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 206855782 1250 206854532 206854541
    0x2100501080c06310824150d051b1c0f030518060f04030302120309060402010e150d140117070e070507050d0302120610020d0309111c0605070e03070603 67
    0x1106801c62940000a0460581521401039580140a112081400220010001c5a90800022400b513071b4941e408a841c010918021b06038036640002d032911076502c0d0340c4204a540c04150490295020800d02000301d090300901c1d2003000c4d000b0b11480c0080e02444920711180194140c10402da0b00d5051680da404039016400190000790a0004041080480d11018050094106241c3d1440c0d515825420080c0c5800917a104a01e42d000b010010004600404115031307800c0359081c200250300c059020001900301d2050501107a0786a8080303054027800c0c5d02a0007441006103140c038440940d98131030384101a41080c0c403031580215844494100007404190f8101d030381c0f1810a1800c01c1c00c0c056142e82d2207040109108070040001e4011449661180d01d840031550404400c852201d0b40c1c02c94504083d440d4080600c0d85001e00d03903a165003800b80040750310b442040c02c02c0240b1101743d9100c50404903041c0040320400341e900390f00e000002403c080c0500000d0708010700080c010720706035140000031009007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 206857032 1250 206855782 206855797
    0x1b01080f0405011808040f050f0102100203060604181a0906100809070504050c040e0601030204120b04020a0801020d0f2306190e07110d081b1312060203040302100501080c06 76
    0x35942c54296a9000481350515016244120003c0c3e5403245490521068450b40e078000511448402e42c1c1d0703000c1030703800281d4880d00b081d0345c40d009a00d960356080054035500035903000c89143c0b41d0801808010401c19803081d160091903250740c0018001c0c80f0b060000e02d2204882c21074000003c003040750401801001d1040c4e01405032000c0b034040c1916000883e060b643c007075902d4a019000030905101c00d0610035040d42d8002000e2034214140380c6030500d606108100080080c04801d030030404034042d5120028050301414101c002036540760391b42003421004040c10381c01441e4030352500e69082500c540101030f104d52038841d4412805562229410404e4a41e5482c6021801b800e0079440007854503110b02d1a680300d1449a1540e51258200c0400035051034802c0300320a040064110400c243d07121400304070000d018034068020b0b220413800104a21550403600000d0350000940100d0042141702d400440c4550b200f9400d41340f40f00d403520340220558100b801803500680000f83c0d007001307500302040500181c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 206858282 1250 206857032 206857043
    0x6011407060902100e01080702030a17150301111c0b0f091e0a050105100503040b07270803130503030307050405010e0a090c09051002150c0c0a05060a0603051b01080f04 74
    0x80b080c80d540083e6590444076021004241826000a104d42e0000c1c200380e40101903001441c0b41100d10b80c0c00030020490f40c0c4840846490400102c1d44404242d1218015082d01400800c001306c8240000302030f43e002008442c0d142d0a02403108601c1003000d00070103041e494094000038407a0301e040100848010014001d1440c10b842030002031103000000185401204403140010b810f5040500b40646881d100507045c084c4041041032200188020741d926500c042a0700c0c141822001018080504103000010100040c14800d0301080f103507008001060225505005220341c40d81d107409040e05c9000849030704d00803c00c1480b08000950240381140003490005002c104407944900282d03080300c040700c1c0001e000130340041060210f41481030020080050500092a501480c2c14086150040050040f0214070300461094180c0808110250502d075001c01039409525111019100070f151a1105503003a114540300e40300c44850310074601d0721303d00c41079403450300d90341d0799005181e0504e42c041c004580 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 206859532 1250 206858282 206858291
    0xc030903092102090a0506040f0506060901110f03120f090a120309060b04020f1801020c0a03030e21030706060f060909051e0a090302010b030c180406020f0a03020d050f0601140706 79
    0x11382d02c80c82d07054841d54001c03a0004007410b0181c10b1008072900c880c2041400d519100510010380e4640f01603864821003440d06059509000160500749240164100110b2001081800041c00b0303841016105d0500d034000c010142c0e9075202d5181c1d4805460001510aa0747d4043e03000c2c2c0103100341c004410362805004c0101d8522403d401181c00c0b640010703229a000d90021421420000c10321202003003141c0300344024440148240c0005080042c184402428000511003003206a1540d0158020441c5180c12003d04542c10305031258a83d404860100c601c9450050081050b03c030355403118040c0d41c91540c07807024041c20041440000c0002030444501036410800821048000400742807044518100201c6e01e08500e250203420b4460941d0140e11a810900d0514502e450305461303030158000b030000d0f02d20b441e02d8501700000240b084400c1c2c1d0040314070000d88441884d07015001031240c02c8244108010907510000081c010900c10b490250003d41005c2211160030f80c4840540700c80c0380500c10014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 206860782 1250 206859532 206859599
    0xd0b091b0f070c030c0905370b040f0c02070801090c0905180a120e040902030a1101090f080723130b12030706060510110604030807031d010f0c03090309 67
    0x440e0000345510881d058040c1c010140080d0b2583e007e002d410041010880710295103404000040c00202408184200c0d00a20f0014650301242c00084207401c1c043c0c002c02007201d100b00b03000040e002c010403c0300540305061000400400504c83e891483d030300031084180c8642031000d80405810040d05c080882c0c0100c0e0342100100d0401c1c411596000e101c0c2119101d0850b144002510000c5a4100700f40309a261100b0100581c40c08074008803110750103485142400031920068a01c500715800c892036550345100f01044903040025440203640804166440c100441403800600f107035040d0000f5000407004900d085400f0113034000c2c0e012440003c21074003e200d0214121031540e0008001542e1481d1103510400003810500040144c0070b08600d00300c3d81c01d040c2c22003243d0380c445d0003500050821044a001400d0180b0983c41414007100c074420b0303206025401d903400e074040c3c000c58400500061500404082c5680288030f084031035130340758031440142e51078075a9503580c02e03641c900c1049500310541d8a11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 206862032 1250 206860782 206860793
    0x1214040803130509090c01120c090e18010b040c0c0209060307180203040c080a020a14150c0307200d0b041104021b060105090f010e04031101110d0b091b0f07 69
    0x3401c0003500b01482e101600e181000300000c000000d8115903542d002140e900503940d0380841001903611a1010100703d4203200344003118a186d1039400541d00040c054240300c41c05001820064036044480000c1c0711100c01481003000711654007241c86c2c0801d400c0648071005003018151554002c00003000d4480e03042c0c0d5a080540f440301c9002d891115150f0000420007000541c40400002e441c1d000300070104804a980030864001c41405a01400e5054040d0010340399501454450f000140000642d00d41c00040320320342d96034104807021640c2400041554104200148084501c10002046284908615180c1c0444c1d40c03405003080e1140060400e04541e292240d000070030040301580107281c42c9071685c100c95810b00c081078110720321400a003002c2c088149031030102181507480b00d50300c101041c0c5861505903085204285c140660b5420041840150325115010b040103408445050000c14498400c12030301c040d040700d414404010303507600e03090300c041500c0140c5106a2200d000514005058540d07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 206863282 1250 206862032 206862037
    0x11010f0204120308010806090601120804050406141c020a05040f0b04090f12080c0d0e030702090f010f0b03010e0411011416060f05040f170d020d09030e0d1214040803 73
    0x7240b0b1815800d8240c1c010150301042c003e00400000e009440142044150980c40c2c0ca0184200412020f104841c0b0050000c1001260001d00c0f00510400404e40d075082c107414205001514603110700c804c01802c18031192840da442c40b100781e0003010034100506001c20000100540c1800300841913450380048201e49a03032041084440c0109041907000344a85003100801d802a00f0850400030f4540610000c881c83d141079038020041200049458a030b075111043c9940a001c40c0694004620350612607801e21089036581a40c0307519050f80505074484910801c240f00038881c5000540c0240c00282c0401c401c0f5229640c4140b051606002e00940c60710368508075001801e5043d01300e070b4544800f0301001500c0c401c4403100b169580e014803081c91300340c551000341280014080c240e004104860800540c14074111006404010303011902c2d0320310010290f000b4003040c0303011030204100d800c02a10078a800b0300c20038007030381d0b202d2102c0c0304401c0592012158480058030070f000029082c800810a050140007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 206864532 1250 206863282 206863289
    0x140f091f08120910023007210311070c0b090a050d03020607031802010e010311400e0112050102070b0f090706110d0e030703050a05061614040611010f0204 68
    0x80064803a541e410404c40c840c2e040c40400401d42d1711008a1842c07101a004003006072520b1040482ca040c92030982c1c4e000180f060b50070082914080c1503044860304031964217004010303400ea030b00b08054100451030f00018070606002400800c1c02e1001004403407940d41c010300c1c49200240c001d18426035a4004195071021164045015800c04020002440d50510504010514600c403814484120f86c001030014400c03040700e02e04040d120b140ba40c0c5441042802c9440039036030402485840820089800da11682e0001c80d00020345d20100034581e03803040000d00c581951704848400015034a014a00810b00c100108129019502444010042001400c04503c560342c0e000c800082468405420740c200721070307a0003090501460900408042e00d00107208444000141003158942c0c85a0780041d207014041d03480202280300d87e00f6404100200401c1007030045001c40401d440581e8009801d8401c1ca41030002c4032003104040c0010030401d0f11680c0242d08064500b000024081803e403504c0c0c0c01d0b68055007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 206865782 1250 206864532 206864563
    0x80304050a03030510030b0105010c05070f060908120f1902010e06040f02041407051603020c090c1207030b060703030209040f05040804051206090a060506011101060906140f091f08 79
    0x107808070141a00350042603070102c0e228600c0c110490856036408090001030140a04000010360751008000742008860043c2080210590201c2d80ea020b00400d202d0250040400c4c5008000c0020840d00c00a026608900d50050f44581002c201c0d109903003541962882c2d4508640d01d0300240c031300c07012043c081140910b000e036050301903c0d240d600500003a610f4201076250a0403541081102c03c41d4002c1c01c1d0f400700060111040103050707041c00c0403440d0140c89603115901c00718090921080c0a01302001703205020200942440035a1104000e40840381e00c5400d00b900000d0400120340024402c0d4000e00c0e40c2c2e10020800126040c030042e448048500850f0125000c0200080032f210b40c5c80d000303000b07008000841c401030011340390030f03e80b42d80c440c4044407000307020350384074008141d480e80202d02030500465440001c000f559662242d070340c0030f00041d12410071010a501da0300211400d02d0041449100ca02400c008603c1c5c81c0c0704071071885162520034440c032940e103111002c01c0d115024804031815400c0350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 206867032 1250 206865782 206865793
    0x6071502130602030702010e12010e0f03070308060a030807080304080c060403020a0606080718090c051c061a0108040b07021002040f09060e0103050a15090221070b03010b09041808030405 82
    0x101c80c601c241c000c0740e08107605543c0180507140c0181e03402080d807801804c00342c502d84500e44242200e18054408007041503d01e0041b00c11103210340700000040e2410358040c1e41c403c013094983c10140081c0c04001d020142c005c0b1400c000c000e010600320300085400c540300b600042d01e03054610782c01a080080c165030440c01a0409a024410301c6480e000320005060741780e0180c03160b5868051460201450000103d07035013500ca03100f450501c048414401c00500014110600c4903100007002c2000c0f0710380e040c00725011440c28411004960f840d0003803881c03002041c0c683c0700340d03600c858031000c503444c00c024503030421449900e040880b03a121600140004106004034043c0352428a1b00c00c3d8151030043d0801c42240941400400c00700f078000490f84511900001c60074502110000b82e000601300300c100103500003114100744000c0036200c0b12640650500030341070f00d6005840f9212210a0b100030b200701c445401c0d040c4800c48030b40c80d040d0b21441003d86900a031128030000342d40c40800b01e4104590668113a00314 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 206868282 1250 206867032 206867047
    0x9031106090606060912071208030a0608011a0d240f0e03070201020c06030c090a03080703030507030902031c090e01030809032104140607020310061505070c0b0906071502 75
    0x300001900710303040c90003920581c941040400c4160003103885031486030210301d03c0714004482c24004000900002100050840c43c0c600304003c3c203500640c0d0810b2441c1c0390450000d001e140c10b10801440c0981c1019013205c040529007007110b500d55040040c1c070300c50070503e190009201807000d14441482510310100b2294807100001d012112060010300468004018100050703a01040c0c80791650421038101d9100c1d16421880e8460b402460340b000d4010318504004410b1084080c003420505d48a036a05001a984200040b019201d1100d030003901648219441e01a40c0e1740140c00c03640310400340c03824040e103540e22000801580407e0b4026150b070140082e000304103050a0040d10658500da8041085202d000d58601400388a0f610411034401200d44e00c1d03400c83e80d544012142c20303c1d0000c084540740036503240000000c107181c0c420700c042e40701001070707103040c49000d8000c0d00d01554100e24810320356850856292519404451141d038442c408000782e40005242e40786c0160402815800161600319 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 206869532 1250 206868282 206868317
    0xc2306100518010603090c0b0f040f090b090a0209151305040507080f0a0507050c0d0809060604151403120a0e1305160e030705030703200a050108010311060d0903 71
    0x1096005903004518021040074401d0202c400141140c9603403900003441c03145c81c1044241d903940e81d04030a1501c6030010744e0b10030301842c0101034010350715808200704ca00d69680b42c465040b40c511b240e0305078000540d40002882d1103019405442170b100f002c3c098528648610308442e24607440030502c5201492011010320590410f4820141c0c014514189190703a8244020140c0901c2c10050804c0501c5481d000080d40c80c4c1e00c69026552410980c80449403071441185024100076811503010f12207205001c00610b6525150080b2800c13040c2040c090307400c090902c000144001204030000d9050300c10f8140600d45800103e004005042855403000310390f511040401c100b1240d202500100c0500b0881800703c086140031003014202c815080c90141500202d002c00c0c107040303559004a50500400b80e000050051181c4c1107090368080d4a21a004411003404010325040d00e40292400280900010320004401c81c0c00d20001802c000e280300d04282101d1031750001e44403401c0c0110000380b03000d10329420401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 206870782 1250 206869532 206869561
    0x304060b06040612050421021c031109091b040b0a17040206090d0c0513060501121a0d0c05030304030c56040e010617040302030301060c2306 62
    0x100700d446034907080c58103c00400e02a40215101c0c1010307038502c045000c02280701c0c41c0303640020004081c070340c0c0d4840300b41c0040c0d1a9501c1c44504410420082000083e0794800c0c49100c0c003070950355a00c039051120300c1c0c09104444000500d8a11003254000c110246290103401901c014034500329950764031070b031040004060364a244030b0401c07842102024000165208026912061420303100502800000e0400d8098408564401c6030480048000011b0504194100070182c07207007a200d52100001060b500c004a0f425020940d141003440c1c0402c820304c0c03038500c07000201e15009071104100c070ba440350002825640941c1c130481d401100f0f40001c01500100860003202e1030006a107980110140c040086529802c50b40f415103421a003040300405012411480310302c40004144807a15245c036020707038180c02d0101b0f00a50000c01e141c6500d0482c05090b500d03225101c1c581c5030b070246086910b01442902c03102c07401c440440da804044000c074010200b41080c410a03001102c0020905420442140360040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 206872032 1250 206870782 206870801
    0x30207080309090103020603040218070305060103150506040b0a0203040306150f05010323130b0a1410031511070209070201052203090e0a020c2e0501180b06090a0b030406 75
    0x303800a00401c9003da0f5190741150460780c054594030f0392a590341c4001440900e45450741903841c8a02418041903e900d03a202074404d41d020b072030802401c1c04401d2580c88043d0240300707141e80140c0c01c000620002c50000040d01d611609801100c0c2040e84039030b030701401c0c0d400e01b2001ca03150802118007000100d01074604000100020f0030700704074a100301c500e85400089030100c01c1d2940031824003c00c0e08200302c00384140600d504542d000007182007035a001000f5007608518042c1e01d11444c0007080c4440d180d40d81460840780e0008c141c146424614107028080c0040003115078140e002441035001507260751100c4d1344030b00c003242d00016103447e050200d0280c2c400d40001240c0d041003924810382c00079030046c42c01819140c00034100101a951808920040d114443c0704d100030303014038408107804450360a030040781c10104250400d107040714215100c0849100340303d11200d444064a40c1108000c00b58400b0080d503c003d8903c40c07812403001c0101d07219081581c400d40789480008200030900c600c0b4441c60090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 206873282 1250 206872032 206872049
    0x30c03030a1d100b0121090c050909030301060f02030d0c021011090d080904090f120201050601020607090b0a03060308180a080307440c0c0a0503070909030212070f030207 75
    0x1040c94404242ea0740750707645035041440ba40e43d1132800c0d040d0781c045c9004190888a00c0c1c6c003071400740e509036240c501030a21010100c030f9442e40d400f0003244500d40b900b0320340d00c00c44400300110700b90380c42e00208840202c869141a015400100f00c40e9050500c80d001d5604244400c0d0010010074185c4109402141d062119401d0890070901c00e6580b1580d580c204031104d650041c102684400b1003000003801007200420003054005000c01e1103003080045a03072041843c071a41c0080041c0e0f6191401607803180012500e22001603084a001d0012007c6e4202510f841d107031a1500058a61b22a500c0d070403181d102420740c0414a442c0c0302d51842501d041e181100c0640040805507040003500d6441104002002000850049101c0307130300100c44099004042c0e1001103103910b2000515194005403a50340300041031407042c014030039400310724204080d030301007150005401802050718242c2d844005000c0c03520f00b141140100d03029050440c2e8000098040035004100c2c0450080b01032174068540010780d84606030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 206874532 1250 206873282 206873321
    0x70f0801081c050c150415050f04060203070e0a03050c0a06110c0d15140406050609060a09050c07020307151e0207060f03060306140907081209041805030c03030a 71
    0x2014030007140302c40c801804280e4402400e615030405542500445080d0a074500c0340507610407051280c88000340c02503014080c400c002800c61003030b090a4440888140580d58558408500021450703801140c0c800b0795894500c16420355640007596041c3e0340d5109460980c0803074000c2070140303400700303040004150600f054040343c0c81d101940b685410102c143d00788910010341410040c441300d1341e00b0311025502c0720810007002031004485004c000c0140c80c10340303e141c0f03403400041c0d10782441e903000c07400b03200300130a40c215140c90199403001903c0000c000340a00b140034049000142c90400045002d01a100c19907014640c2d1580d0040c464807004050103014201c4e807502c4040b00d500811181c0c256010340c1391a008100f409101500903190035030000301454608903011107483d100d4074100f4040c07581c0c002074403003c80d55140311070390b44d14850610f5200304100704521012460194420000341d041200140030061103034a426040d500501c2190403940c100008211034190a40b00d2441e82c217140c4000d0300c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 206875782 1250 206874532 206874539
    0x40b18010906081f0903020f06040501020a030c0512060f01120c050c060c070317060d0816050c010f0504050609130615030b09010b0a032408010906231902120f070f0801 74
    0xd100ea2000c152540302070317507a5410801410310900c0004021070b04001203030040d003007929009000354845c802400000785000e0554018901ca04101c0c2c0b05804803068804ca00e0325403404100c1885d240701386d9581480700c404992030250000d802030780741c0c20781c2c0c50700c1d003d461b8411880c0307240c03c207040146001d0132800100455000260414802400e122041403500010347e00c03000464100d020410025260080c0403070740306c001103030001c1c40078070061082c001d0341c001c88600001912081d0b4420000804210280014011410301070068003035141c004112000c445040e12604044560750780100203400454140e01d02c200d5050b000c4d00d01002c50564110800d9807512505643c00d00480c48020101a10340c4048103807610110f43c01c0358101d900010b4441c0d401e9541969500034140c864040301d10300c0c00e00f18400742c0122448110001c0c0c0b18001504121540c903580d03002174090307007244600010b540c24071881307505540c4aa40e9601c640e0295005000c0c40c01d06801c060b1100c002e842808041190120051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 206877032 1250 206875782 206875813
    0xa270c0f080a18081e031005100c03120905070f06051e040501020a02040903030e120307021e0a0305070201020f0d031a120a0602090a1e060e060307091202040b1801090608 75
    0x10341010380c000b1032158480d220103042c181c0c1103ca0705c0307404502d89804821b00002c950113280300d0084800807624070118903680c103426074581c0c826840140c0410100004612000101c1c1c009900c40fa1290342940c1c1f240740c0b58100e142010049402400002e503000c102500000040c51125206c200c4500e221070409240c040000c1d0b9460814000034000c81d25006c206d410940681c0004050b0082c030001d590440000248241064004452081c014461040051030800c1c540c5c42e0b11030440c06c18809001031103040e490640722940180c408a0461040c000340c0c50a0007400c2c801d061004100f640c2c00b0134801000814140d0f49009000304034802c5501e1524004007410018445c036100d6802500581c035088410001031002e812503109082c04203001203024102003400241a0907141c86407a80e44141c8018002c1c0685404200c4902012891010052110300c4c0004100e002440c40100080340054007580441c07005103904004d40f202d400070f0701c010310840c102ca0240070085e005040007003503c54402d02c0b46 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 206878282 1250 206877032 206877071
    0xd0b0d11040f0204030803090f0d110a021002070e0a0506100509010c030e03011e0b030607020f0604080d1508010c0905030c01171801111305030304050a270c0f080a 72
    0x188680e075202002d542031078182c3c054400464004c0c0d0629100e2612107440e5413151100c0c254485c0600038a441901601d026141145041820400a02080b0f00c00c1c3e09010030354141403010029441150700c001900f1500b030381d03064800c88940c000842c0310b00780042800b191140b0501d6070403d103e02844410910790b40101c940d8401501031905450150412000c680101703100c9920340302c0072120030702e038a80b001815081038101d1a016000c41e0f10694488038101d0f00c03075603102c41d80c07242500000e003c00e001c6100d8401400000c4884240007070848540903140c400305885611521840c0d4468540501d00d9030080d80a0000309809c0e005401960b4500c000200840b0b484c0c0d0070b00320101d43c01d60128110304010001d03d02c0c04441c0500810130102040f0340d4000da500403580d041c2d403c401100e400304007800c001c002d0314100d80b400b4004102c0c49007841090b00d9105c6982e01400e00385129035a0a050801c100e0188510b0708442e41c0707543c2c007052640d200091074000003e00c070032503050a240d0018407500d282c005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 206879532 1250 206878282 206878313
    0x507030c061e0f0f03060f090b1c0c03030f03060806010e0708070908190501140103060207050f07060815040902131a030304030c05010c0305210708090a02090a0519050901020d0b0d 79
    0x20301060707104e0320010507001044160800c101d01158504c010500c00c036107500081e1038401c00c40345504120710759180c4404601d01148001c00701078541c041000028011002c071005003110307040104040d52036a0302039203004026400409050b855405000400d07411005c000d4101e180c0d843c24100703090500c03020690752904182c101c50b03240d68080c40704080c05800c2d4042503010f0038001a25501d07507134904046000e0b4000d080c0686a5010700d170007c107801d00c0300148034400c60300585c8650406940d1801d2030002c49aa914041d5005901c0c0d45401c030040c0d50b0008000c01060302c032030300001d10030311662491f0800301c60304401502079842004140042162910401c0c00c1307840928103902c0d400c50500d0110703031a0284082180c1107461054090003450f603810103492040702c07603a80d2110b643ea19251615940c002042c070183d0403040c0f04000c80e464240c0b6400880d0f1102c05051801092540d41c110302c3c003114400c8407042002d03580441c5481c0106c646000e06402074104a801c40a0200561102c0201c2c16a280 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 206880782 1250 206879532 206879537
    0x20703062906030a091a0a06081515133801051b0309060d0c03110306010507061d0a030306030203060c090612070309080406020109060c0516140a0507030c061e0f 71
    0x7440001c3c0c0e6801c4218480d601098103000f000070101d444a000c84152042008541231010225139000d00045d440031104481880b4602d03611046100d00c0b102c0f0a001185410188140510201c54030b0343c0211111440d41c2a03c0700c42c65180c6407144030300c0c1e441c2e40e01c101a28014003403c000091782c0c0402a10300e143c0201c02c16288858103544540c6c6188218003400c0d4106201103000d1544003c103500a0b007036929951424014800e040c050403149110443e28175022403000c1c40300c0310214020341e000b1080340100c1c00b00010742c42607011001d4a0462010340c100d000a46903113045c0114101882036907000414102e1311410018520005001c4d80910300c50b00c2200790440c1700240d01c2034800d42045110a4020303075141c0e0740719181d1070024081c20110400b642c503681031122661801d8403901c11102502c490183d003c8802c41d072a030ba1320081300c0d40b01144d500c5601c00c90360b8100200d0003e100c0480290310820b801c441e66840c040c4080c121074000c99001030032144560001d0900390b0855090b440354070341171 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 206882032 1250 206880782 206880787
    0x30305030c090a06020a050f03040b180301060f091e0c21060f1818050c0d0809120d020d0305060117061201050424020c1005060607050607020703062906 67
    0x1070445242400b510101c5503221032003180005583d42c0215262440d580220300b61901c410605014a54a00c1107100310700100404001d18882a00f4425a802c2c1d4007400400114100d80d4034403500303008403103e8011081c481c2d5a41711010301034407490602c0040f41031030041804906181440070f0440070b0f0b110100a000f0000180b03400004d51194081005803000301b0600030300c503444d921010b012040d9118010400c0e480c0c100300007042c48404111501c403030740c020018030842c0480c60034041c07505180b1200300c851301c0c0b00380a91040c0783c1e141151441000317692001054042d510501c0285000300c2c089000c01418034000610106991111600300320221051007001d05840c1c2c0c1c004694186001a031a11145d4a0242070008211864088100542c2d00200d8100c2c8412000d010008a108000d420a065403002c00d52209004541d000b13194042401410b50b82080b56030b032501410004205c55540040c0c020540c240300300010b0384a03016602d040e81d0600b2039a2580c0302d9040d41031030246038090317106d680007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 206883282 1250 206882032 206882041
    0x5010207180e19050d0f03051b1b07090b030606151e0c0312041403090a03170906070609150203041505040212010c0c140a08160503190c021206010f03030503 69
    0x800404083c88502641882803c51a050864aa405c402c8000c80002c501c906e0480455100380105401045003d000c04075241740d90706284900d61009174080c440d0480c000a4281d603201c00d1001000500390303002d0109030003107013108050611800a107914404d410341c20400309600080d105403120144c02c18040d80016441041000d01e40c0298074101c0411b210000e4a0701406560b107000e00d0149100f06660f400c9030301e40c0c44c3d900c0d40301e0113a185010380081c0c0e09441000440c010044900b0304440801b00f0038506070035400803c081d540620020345055441d0300d4000200a901043e003028014840401c60542c2010380c2c2d0491440361220f04465150707203032008a4250358620a8071111040b000008000c40707100031102900d050708018087d140c0b0958100d42d0070804001085044005c6d5003c210140b07407410050b0312a20782d5a190009552a00c014080601301c080100410304a0403d140c0b505560480702c0e00c100910b41a4a120500c1ea94003d00010081030802690b48010750390b06080194880c1d64 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 206884532 1250 206883282 206883311
    0x11503060504060b180f300607080403110303070e0103020a030b0a08160503030c0705010f050f0301090e060a0608071206020705060f0402010f021c0f020a051c02070501020718 77
    0x2054008a61151510b90000783d0800140014403051103c28200b80300e001100c0c1c100028002c6e003001041d00268542090b0b06d446210030380b021a03030320202035451842c00d51107805a00c2d05400702c2c0c400000c942c070310090000303054200f14982c0403855000010341c41d51400110091595069420803418150003241098082d4000c2e044080350f4480030340b050310490383d1003c0315982da0111070100c2c10724511000000c1030a0030080101c030000c200306001006040e142ca40110b4190308044c5031001000028040c40c030310b90544e01d00960080404082c04561000360022003420080080c041030040d600d084d10403c03820202003003600884010103401d000418880c00c0013006481000001412405158104400381c6134090100d03004600030f071f03544204c034200c081060b691001c085000405c4c050340e506040300c000b8031030f00030140e4255092060b20041d2180b0b554039403a1509000c002d205001c24000048040743e4108080300c0182401d200603c1d400e490300d10a07280140c20b40012886035511794520710851030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 206885782 1250 206884532 206884541
    0x2e06050c1509011a0108010f030206130b070503030a0606020f0a0605070c1b06022a040504020d05030339041401051308070f0b09030c0f1c032001060e011503 69
    0x80003603942603903030714180030b2140c0240041082100381d01100521a0701551140120506a03000b621200d40881e055400b00411508080e820100300810302c2c002140c24000100540800741c41500215100e0a18228003001d0341c1840e00054119801038804510100300020002c038030b9500b00700e0000ba00c0d120544104c6015000d1400034002e040c400e2081381c0030040340c100200450300d00d0b41c240d64001c0102c110129a0111400b01b048001c40701c1c0c00d12940314a400c0e4001c6402c11301c014581c140000c080d82d02c060a58101726a01450001c1559812310568801c0e01d40300702c040f003100000c0040348007080c50b0070903c3c001c6000c0c015003e01b0191440403103900440850b14801040101e060006a881c01c05c284c0d600c0c8180a50b00340001107000004108070035074147c5510a40040c00303040429030b03103003c0c80f100340400381146034002d0b203803518600d120301c0030803130000c5213806546d518810781441481c0311640b441194424200e030780f400e9800c2003074600380010721303055551130b24000c110410300380c0c030450213403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 206887032 1250 206885782 206885803
    0x3110307083607090b030a0605070c140d0e01020c010f030e0304051818030f16111302040e09070e04080304080d05070c02040e070b031503071802032e06050c 69
    0x10120b058a9003807000016040d2a9450800c002c66012548441e503410075130700c2d40c07100281c01da4003541c0300000140341078006a60100c81807a1964220f503964940240892401200c11880d0b0040b199010b03441d42d010042c106140000e0009000b12555040000c3c80c0350b8442d1052400c02d40d590182d00036580382442242c00412000f0400c00001810321030404031284241d40d0a962050b41e07812521840101200366404007101d124040d092002240408202541c181c10440d0150b1040700307000d655030780d003250813040104c181000503152410140102d0000c0b07000380c404040ba912007007040086294199106600c55403003503c85071030351140c0c50509054043e042d1440b60030742c1003c0c1004180b0740d014000421041c0200c50510031044400d80b0079480da01a40501014014104001112040401c20055504002170200c80780c441c0d0340d00300c01d143c3c5a450b140040d4000d03000400e101c4040800398601c0f80100203403610f1a0754111a02940012080c144514400c1c0140450170010360f0f2418071010112 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 206888282 1250 206887032 206887081
    0xb07020319030201020a1b030504032003010603260708030a180b1e01060809060c0f091c0606270b01030204090507020a0606060905010e0409080403170301030c060311030708 76
    0x148007191502a0103034022114440c00549801d01c032803820701c62080042126501030721040d2030030b801e64894032054141d030b40c502c0c00d60b9004003c801045407001d00c0313850300440c0180c0b002054044010b03426001007500c800c00158804060081002055211084a8008800000c006600250100c0e84110880f0b0a0340c050306421a190030050450341c0f15102012080701c50300d0741d540e1a83c941106441803d000d4031400e920307a100c4400200c0480102000b0020f546250b580396042803a01170015100c0500502d0382c031801540c0700c4298042050178081e40c0003510030b80600d581c0f070418940b00da40c07100c0411400201129200c400c41c2c1c0c030344d90180d81118084d140403041801a407610900280d035461101c04201d4409241107000102d80d1700c07442e0340c0001e0301c2d8140d441c01b60080308081008050301c01e4104c180c80d0f600d0208030000000350204184c2000310001900c880e01ca40c55424100c0200105170300007800e00d8201000284114189012a0b90100d29030034105e440e81c9038407589482c042c090700041c400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 206889532 1250 206888282 206888323
    0x305090d030c0804080307120f0c060b010905031e101b08040c0b030411010e010e0102070b1e0406091707260109051e06060d050c01080705090306011403010e0105010f0b070203 77
    0x1117944012005105d114010008960003c811102c01c60303905251072036180000b01d01c004100002011741e003150000c0c0405142024070325440c0c030300003410071a40300404c12030340303c10101d9818404001d000001d050340d2014010040703240400c2501080325032039015a030420036803030006010040303c2000c0c1c4001c2c0440348001a240d02d01854401520414601c3d01400708600c2e80074030606611440c400c40e071510b0180d002d40034030f6141c00c1e54201c1d00c3d0441c010380050000d0000341e0050460800015100414165481c0e415591419590751424000e103a18260340c0d4100b10700902c4502c55003c000c1a4081c11180440e00121445510f28010240c030140100030b4010320307149030740e050380240c41e45403849095010ba030921b032140d108020703e1a004650082981d080ba1100203010f6014140f4143e1004060a00c985011000c400103428240242c021051021482c541501c090400f4800d001190228400800c143d505108411018400364895248201070000e40c44085407020f00011017252080c400021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 206890782 1250 206889532 206889539
    0x31b0609060207200310020d14041b060504260309120706030f050f070e06161209090507140f04090f090209061f1209080a091806030305090d030c0804 66
    0x8083d41c421030040d183c46050f418600ca140440810003c4042801401002e100c001d000c6994007035040607041c00d1a0503550304000c4c8801c9440e6101902c194481e07290840080c84820748030055164940000f4104030040c00b09015400300802c4010740164844c600a1f5812921a8000d04c2c40c800d42c01c86da40c21040010005042100c00903100b0155102a00c0512041180e652000d04952040360792208000b0b40d80f011812003401486160074a01c40038207a41c0c604060400ba600e0100b6884908655007840d2000520381254041c422002a00e20950140b000c0d04102d0002003101464090b1081042c030009120240040316008640080071080c1d81803103120034011030700006080c113040583c00340c20320030f00045151038a5040d1082043c2400081265003000610403900b464004001d86d6078595921140380200c0c881001504001c4400d0f81c501424038103000c40d851604840c440b1030304001d03050603018030009030440c080e248200400c0d211408d007501107050407142c4612202c0c000e406c800700003d011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 206892032 1250 206890782 206890793
    0x19050402120109060602030a0c020d020a0e01082401050919022110050a031a09031e03070306050406060e0607060b1c0c060203040b0304110d060c11070803030108030304031b0609 78
    0x342c1c1203a0700000100a2076584620503610f07032148408403030001d1240e03000c0310010301c3c14981a080c801d00250840c1c015903100c1c3c3c6c070b11042072020f0300003156643c04020800c61095407045503050095109103001507070351521002c201c01e508081c00c0c3c0348071001c58004001846109034107940c1d100e9030190b140c440101c02e2403000708000300103480c0c007200790016450100705401c040340c590040b80d0348030940e80709013500c014541b03140310400f034200c0072640810004844030748014143e481200044840c4c8035500d041064002e0222400f560040e401a03090460400c145074203c2020035030100196102c940e2441d69181241c010410030341000c0d40072301d50780c03004150f25001d500c2c0b0304007441c801d84180c113109482d154241d95a000301e00c580300c80d203142080041c000903808401000b0364000035100c1c8289044603640c0e2801d641c0342200400c002001c50003104242003042001100900194010710300c0c650410400c01c0e140d101c0244041c05001d494004644c042880c0c40c088905903400038403c122081191402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 206893282 1250 206892032 206892067
    0xc0b100609080706050405060a09080d031418062d01030c050114030105060306120c18060a0902040509073212070e21070b0705030c061f0519050402 65
    0x30040080c6900401040441002030100c040c4d07850b0b5218182007516000c1009a1a80440584000c11410b03010014003000f01300002100c081d9030391004200c0f5030944891502d003100090500044005070270103218082d81c00705810703802c000000300504030416030040c400e0700b403a2480c8801003a41d079074000000c2030112040b400000c3d00c009990b488880c0a03800c428404500007802a5940240c00f0000301c4d521385003982c10b108009201d0020780c0c13035a000d4800018a80486081e400402401740e02c2040018600501c131000a03059070f0300d08508080c00e280c00309c0c03c1030300b0041000c0c2c14442181c0700007030060141400411226083d001180317900160b4070031810250441e20b03d10b4000c0c0c661402080750036004440c4c040454601a02c02078034500c56290084c2d440c0010411101c95000780800411001c110708000c2200741c1c042c2008590321491080464900100246500e00c0001d8000480c81000c0d41200d0900403614103e4040d00d00c003131042c4402c408040e80b640310030303409840002d8089007441345150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 206894532 1250 206893282 206893289
    0x906040e0106180e0f1b0a020d0320030a0509030f18132703110304140306060904020d080f190c03020c060c0709050a02042d050f0d0f030c0b10 63
    0xc4541400d00d0b9103c0e5080009803c0c000c80590301d21003000034081004070001254021401030100b100c20312480c910307003055807020050f280103030449600d840206030107002d9550084039401c56510645507000d21044540400340c80039050613122408244200c000700300703561000700940121540c41400000d0030840c080100f5001740550005001d0300c100889920070300b0b4002501c41200d01e076154141d22030a0840780d64220450501200305035583c2849402c0001d44042e01c3c006400354825400202014900480201042c1c8240c454104000042c0c0b2443d4102070b210340d11203001078460201b0321481559010b601c00082e02c81e0124803002d98480e81c03190003070141c0c5000c0c3e026202c001e88440c061181c903100e000c05081e096409400100115039581d400301c1d5010500780c10041c101600c90a280c05001c2c2c05c0c42d502d15208000c0d1500180c2a2200c00380100240400c4a101c500002070b100420f561510421001d0310741c0e81448a90400e150050303220300b46040d0f102514501502e000041d0054510544c007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 206895782 1250 206894532 206894537
    0x911041e0f09020304080f070501060306050c0a14090a0501180801091a0a050f060f120d051b0606220f1509060e13020f030316050102120a0c0c030f050906040e0106 72
    0x210002a61540b610031240117981086500d85040c0b00d1009445050344401c4c0c040300c2da50f59a48002002c42c0d07040c4902400f6400e4501e04540e6001030103001440c4543c0f1100d00e2044a0003004a4826656203901300c2c02215000e0074a00c04019168900a0702c4100c164448038403942002c22510400c03004001581d1801070301d08002c80c00f921a00651021100100e4420841e8840f20303000c643c562900128203001580c00a241a241d080030024450424031922045000300d00c0120301e0b00d2581100034900000641c0601c002c0400d403070010000b03140f10440c10303c1410b40c0c0002000e20907c6941c0b41e08145d200c401070083c10b00519003801c0000c15000500c0c455002c91074588280442e018040a100500407018174422010040540d000c0180c008031407480241e06101c200329088590000d540542c62041c006c800058545072420010640c503900101166615454140028262a0070045041a698151070604c100150038074041d20648149480c540d40614041760010701080c25410041c141c40b440c0d07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 206897032 1250 206895782 206895809
    0x70e180d0e150a02060103030e04020c010e0606092206020d020405060c100f09110909190f050c0f030d18170604020f0a0b181903060c080702160911041e 67
    0xb9054100ba40c0101502000143c20000040021921400030083e085400800051070f044582c1d0801d401c44110300a141500c0d0000400c00250340b40030403005600c02d07403040c2071026030482c0d13445103184400e600c2401000180d000c60030305040d000c1c1d503056601031b0070090030550703460118034201d980c0c86c6640c2588409690501c2d15054240d0b4950103840825a03000e001499504c0400c0708001d42080010150b88051065159001d00c00e040b10680d0603585000c2d200d0941c0c9a406810000d0504c15401410f900505401c005e200380307030710009201240c0000b035180c0205041e02500040e00c4054030369103c8180d01c0c03440d8030500320300e400c04201280a54421264a1107036031001003408010a090301c40c0c881c004030f00307100c0440c0d04032000b40a095410310060200c84100f80e10f0b0800203200b9031a40068070f203140d4074504070101a0308070380a9a0812a10b00041081c1c001c2e052050442d000e080c082c010881d0345450f410310401a103071003900d01605010615446c0c0d11001084c113001c101c0c1c984184121300700301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 206898282 1250 206897032 206897059
    0x602010c0c0303020702030c04060b04090b0d120e0d050d181715130b01030c080f06090601060c0503090a090e12070203070608041406070306060e090108070e180d0e 72
    0x52144090494036610340c54400e15158a05a009400c804000d90300f500602d144000c0599451043c2030252464034055502d4508102400301221214241207001c2c60312038000c000441c41000e507490000340580381640e56400d01d10041034050300e50600080062250003640c4444d1900404a2202d81c403010390b5605500b9510704000312000404501b80702a60445250140030f04a15a6007a83c403002103080c1141d012565035481030800c03026401911300e4500d600c01404010000c1c841c1d4100400403200804842c1020407929803142018803408080c03201c01881c803810040c00348241c842c51000100b10080c05a0f45042e408040c2216104141c1ca0b07018000600d403109191405503007420760068001c103031071810800f003030b580742d00054002d80c0c02c0b0742d00c580c16043d6104100314007407080405a8002c11640d00d0304501402c00c0a03c180604e2041e0250740051081c0000000c0f488126801d980031840d82d61220314940d450046506540c2c011401400480c03005240c0185298404210569003c4482c0c000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 206899532 1250 206898282 206898287
    0x30f01060e06100e06030a0e0f0a030201020d0605180f0601030605090f01330503060d05010c02010905010c0e06031603020906070309050a090504081204030509060705150f0f040605071709030904050106 88
    0x4568013290f00c14420b00200c1c054501c0b40e40244c01000c42c1d44c00712400c0c4e241c903080080c1307031002e80401100140e400150001d03000703400380a820300401c81500c04040310b0307804030700440d40104014601c50400e00c01000207161a031107600300c0c3c401080050500c0d5441d042c00410380407000300c2405201541c090403140c68200440030098002107007408120f142c0c504450404c12181c5900103401c0c0f95200e001e00907003c0200e1402e1181141d058003940000400043c1032810900b900e881103505001d029003202820502e0301e0b5001101e5000580307a60303049680980c85819002801034844c91500000041000c00030182c000400c00709580d0b0032250ba1110f2a40c2da02c0001c2a2001243c0060000009002002c1e00250440b03081c6e8105100b414000c0c00d14000801244c40750308510025036069100030100b418002006002c66040b21180a0500441c80c004400f244003101c0079000526850799070300020010ba00c42c0b0328a8088020211402c01227003000c0d856240d894102d55a958401da1401000152060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 206900782 1250 206899532 206899547
    0x206040201020307060203072114010f05010f0305062b1103010504020a0608040c03120e0405060301021305150d09060203060117150f0607150c0207081506040506030f01060e0610 78
    0x140d05034015450500700713130f03a0400030750006403200e000c0c005e52001d0140d146240116505601180e040b00250207030b00d40d40451940b02c4182d100d9101003007200d00c24012030340d0003c00030312943c1c9641004284d0b501e41e10045804100c4036046000341d41e80991a0f00880f21040c00c076a142c450007030b4030b80c0b446032003240c08050895800b958025070183c0c04103400c0000303a002d82d0100341d100f4080c0200c19051692520b50328034000c0104000c3c40003c43c0c44d1701041040c44c1c20b114903500500150000c5003446080001c40d0440f0311503000355480f0706050500c2072480f076000782c100c80741c0b00d1200300207220a0240c2d05c2d00394041e40040d550a408a40c40e941c2600c2603408450b0300368403400115440700700072000350f030a000c1c0c0041110200c5810042c100701100c041014a1149101c54032411400549110042e0b070090a00c8080d4000109903007001c40085495926141d1f95a046001100e0016103600d468000034038081900500003171650070076400144044103203800520901e0141d0b00c1c00b040001004080340c0c0103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 206902032 1250 206900782 206900791
    0x9010e01120b07200303011d090706110f1009030e04091101030c03020c03070b10050909060109020918070c17120c0c240901140702030a030c18030311010c0206 70
    0x19101c415441d010902030026690441c203941419018542a500044100b168404401109610000c01004200c00d0050b41d00c0542c038804001044074142101c80300c0c1c03070740e1581c410607040100c40074840c00d072800144529030345614102e08550a50008941d13280291400f0384c1e081e000b08030303c05400e2045080ca401a000c0381036100030a0484900c001005400800c0070181c0c403000c160382400701080d0400200010301906000e980c078030415240142e868507101c00d098010074016180801807120510b400656141900c20b20030026840ea02003030041541106821881d0f541001c03c0020301a807140c020540f403a0080c01144502e032204680ca80c041894810303070750240e082c00300c0c40b00000c000c02d0000c0041c000024644042d5681200741c1e842e120b40000014000741a00c909800511010031024454a241e64a1084100e1700d145081a000394982c081d40f842c5000b03242e140d80d034510070381d4840d54000702c000d000f003109200b280ba12828020301c810241000000c840d0300e04041d2003d654000140c4078441e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 206903282 1250 206902032 206902049
    0xa0b130903080c042409170105040c05010e060d051b040303121a01020304180f05040309090c020105010e06210d050a1409030307020d0c03060203070309050c1f0c050c0607080909010e01 81
    0x310302c0c21651001101c41110b5a0381040600a004030301c3e40c80038000184c07c1a000300000c51300381420304204007080542d5001605114030545844003503241d81060302c05004a407100011581c1da201d000a5145640c80d0b41d40c0a00140000c002c0704141d040090b4142400304c01908221030401e4004280e0940d030080311031400f507031040c00304004c0c08852012600300d283c4428000f1582d185060251000e94605450071070104034a10000c1c410490244030719198262588000d000e69450810b018003059005821980180c1c104d00e140c01c2c40e50b0102e45120074408880f01110b80c07520001c000100303c1d03017001d040b800c009148180800341380c3d4104400c0d50764102c0024040c500c1c06410394204403400e40310441c00c0303540c40c41100f0000045519407000d0b510903d440e840100722209503282c0705040240401556115848012004504074002c40014a80910b1410045c810300d1450070050310f80388030b0495481c2d000100054041c00c104100028101da944180d0715881c0b5640c8484200b14640b8003406400e40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 206904532 1250 206903282 206903309
    0x905061902011a090c0903031e0c0d09030804060e27090c06120604020901121a04050105181f03050f0715020d0509010c03050405030114150301090b0f0a0b130903080c04 74
    0x8061607640c000c0c040710307000804427880d08800e90b00c842240e103130850401d0305400000c0b60072054580300307019034280d6200c2d0745488251981103682d019040c0c004d41c0112000c00c01d035142020300036291581d644400100901c407444c0310800002e0501300d1800f040b01c0780c03402c2d40501010481d15007070080603100a10441301100c0d88a0382e9080900000750040340c0b61904001c0521b00b607800c4e0018910450b0311a40b03811100710b80300c48440003800165041a400340c1c0c055203090315074941d01c02c2c4004005410400c0f0100c0e0484400809100309991001c40d00050501c0c00f07615107036000c500380090340b20100c0c1c0b9286405407990071080d0050361078941c2c844054021031000c1003503130515849250b8000500b071080c2006400c003a2200003027400c41d8100307060f5980c1d042890b0140701d050b121020382e004039040102c0003400401c10640d640020710710b015000c0103d00745d187d000b040280c210ba800c890fa10fa50b02401c1001c40000852411010300f00806081c0c0124002e60041401c085003030781240c1c242d071521541000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 206905782 1250 206904532 206904541
    0xf0c03060906271104053c0c04030302030a0f030e12070614040209070f02100203190b03010b060a1d040e061905010e01060c05070807080705090a060e0103120905061902011a09 77
    0x1c080c040080c20707010100c0f40b0204085e08031400c4804000c000143d8400072500215241400b0442040580500d09608089c0300c10000640d0010440340285058079259426200c0c252080d00a09031030510615103008642c0c5440801100e000030340f80b07250040d902030103107492140010f85100016540030303422401d0744001880302800f42c01036010511903841260f840320315800c0d400040360025640426000a0544103500e50401c0707001c1e070315407000101c008102e0120000c2c00100300b41714180d100810702c0219032000c0d581078144002c118070309001a000380440030803500a00d072a00310480303100c3d0511003600901d1200403114400c040c1600c41511222107542d00304801a00c40b182246001c682c039103e540404030b00d0b800180000d00040030108000d203945410032007004040c003801080da0303c01703070710380381081205104031585681100e8200c41402d0720f074040c00320308603008841904881e0300840d0004810900041601e98558000d0603603000b04040c2c03408200100e5040100c8100310380c03003085c20f030104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 206907032 1250 206905782 206905789
    0xe011e1a01050304170301030309050907031b0f111c09080c01120509031b030d061a1b10050f0f0a0903020c06030601030b12030706060b03090a0f0c030609062711 71
    0x3e40d0010b0054030300e445d46826400d844000d80d48242c100b00d001416001003002582011201103400181d607080c00d0020000c41190404161071121300c1804101e114550400034901840e00d400d400103400c400d559542f4404240d14030f2010019590000003016510009003441d004181c0380e20b8440e0594688a41c0d60004c0c9240024007409010055a400b0400c1110004215940c01c04512024000516120004466030341c1c1162190b512403410342d110004050b450303030f003c10101c03081800d40c0175030129111910400e251900300f03c0312079840c600d803604044c0001e034803900d00c1d217510038a0f0503c0002450703550721107000e0691b42c1034900180541c1c407101080e6414580701c1c0156500640600d070000380089a080020414414811000219080003074100c2c01d000160040801400010712018a1400c2c0b0000040c1d5074803e0200c0500410a11708401d001c0010829800c4000c6400c4141130102c403c00d0b081020003007641d000d885010260308400d4480301128615003c40d0681c00c540d000301c80000741010b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 206908282 1250 206907032 206907037
    0x109080303130809090906070206090a0506010b0a050f1b010c0309110d080d091401181a280f06080d05040504050903090d1202070819060c11010e011e1a0105 69
    0x44a4661040c01300c0100d40e2600000c40d4030581c44600105214204040040d041444c0031b000c0000b680c03c02c8454a0100f2000201581104c0b00303d040e10b951040c48500c02c40381e42c000c0c43c00031900714400180088545908a1601c0c2031042031100070004c0100d80742d0240c003144c0009038004c00e60030081324841d10500e480040b110903103000e4003400c0d21b8145000c01c0c400495148003005c65a4040003600320705101424403a1200d610304d16030a884105005485207448000caa41000c403280d4900c0c4000303540ca08298203401d40440b0011480321180d00a21440c1025003c103030b0052629a190240010745c0c481c0005d014080d0079040d40b10740c0d18287c04c1005120142c43d00500c40d49803840208072040d003c0c2ca40940f6a030884d4000d1042414425500d40024100381155000c8196640f110b084000f0805c6030000b10030340c244d0b1144002481c2100001c0a40301c2030040c51801c2d42a502c0c056800503039500641105440142113001810040700b4210700c0c00444040c44400d0400c140c0315003559441c2c0d4004c100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 206909532 1250 206908282 206908321
    0x5120105040b0111030307031d07030b0f07030b03120712020d050306010e0103180f17121618080601062c150f0d061401031e1d03030103120207050109080303 69
    0x400c03160944c4011491841c5a1041d0b030700100290303030382c0101441340700e4031103200049500c078070b020b490708500c0d503103400d180158064031169400c0314820202d4503c50196006504009002d0203490000300100e500700b40e203030407000050703e6501c84ae00401d800b0a2021030031071440440c41c0c40b11400c5440d03100045940c030345004811070525946508400e1040c034a40702c00c10000c8d100301442d415148c142d162180230000801900307400503405211406400c0060f100155101d0080740c041401d000390b41d8400c41e1107410701c00c1d0072030b4003c81c0300c0c0c408112918045030a07410b035180350b01c4143e00307908415100c4014550580511044ad0503015000340703103140023486d0000c1280c60003002c030b0401c9255a1503407a540d2141d880b13030040c1d543e03580c0c003082840d454090700241c0034030034241049003141d0040f12080001105004004403030f500c50034138040450581060785400381403011a80c5940e164035007003418030411f850300700240c401c0e018002000d40c403e4619034103a4180c0e00c05582561a01585034180c1c003202a07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 206910782 1250 206909532 206909537
    0x3030f080c130e06031018030f0801030804090207080f0d050610110319031509020403023d0210020a020102070b060a120b1b0f19110706050904091208041205120105040b01 75
    0x282c6c0c00d1b45c58102c2e4001d8640020004074400110344181c40c010340b12150703460824040c000700704010000704000714280ca007100c5104c1000342c4d546e00e95240c000c41d98440d11003032a00c05480401c48200e40380c503542c86548030f60026202c1c00104542e42100341c0d080300441d14007002640c01000380400d0540c4480d003a00001405d42400325002c00400e0302a40d00352a940c1104070031a81c003080800030340c40d0204448d100030780c909103003060504910030200c41352214090f052030380d6100c895091400c6442008464500c071a24001151101947e1100034042d520441056820110180200c3e141d840d044a03130000303c03040003916600c180500d50f502c440c21354004103c20110801c01c1e0007000300084840041815802d150030082d520000c6100e15000c0308506030051080000c89a11000354050000b100c10940c0e055050844d2034140303a2001034007808080e0320081c40302c030803001c0080309240c20540040c0903510410350000350a8070300030226198025804e551079540071000041126081c168019010f103403062 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 206912032 1250 206910782 206910793
    0x30c030f0d020d110a08070e10052809051e030a0201080a140412030c0207081b0a121209060c0201080f07020a05070b09120a020f010e0604030c03030f080c130e0603 72
    0x880004211011126811009130300003440180295020340707075a5014595003022408003d032540030403c0c45500039070400c20700900003402c000003403803010041d4941c596202d865030508404100103089030f0311481070710700030541c40307001c504840c4801c0e10400c0c40e10b401030001c040a47d081c1c0c00454800c00c0c054a0380d003101c0d07a0340c1c00c1c26003407152542c00c00b80b02d43c0c01440300b1200d100b140d1000070111007a01c861403085410604082c0414580400c401c000403400100311950884002c00084040030260b1054207401c0f42012030500700b01c0d03e10307990300103a40300da1940030040b07584410503519441d410300c000f0700080f20700e4000f8401d0f0028105240c0c20022901c1160036613211603440614010041d08410355080000c0340d00280d501d440700320505038035002c40c0600b24441c00356002c03580c000401100d59060044410807003030701d030326000c05590080d42c10202a03011140d480c100503050304401042c1d00005048440080c0e90034280a0403102808101e0582d501031600c0d1207194024100f02410043d0b02d4080ca = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 206913282 1250 206912032 206912047
    0x15040c030b0103050307020a052215080105040c03060b0108040c18020f12060307051002061614040b030609180a020f061326120301091104030204020a030b040e030c030f0d02 76
    0x2901e03106020b0b5100e04019643c6903c24010460b915a180e0720070b52080f40da141d200c0f9085d01a072042840102164100812205119801d0050801d4181c008280c43c0d0b03e841e08000c144400b01880c0c600b01c81c000c080410011040e0401103500c4607003250b02a040352010602007000010400e0050b04d640030000c40181000e04040c280e200c10740c0f102d00740a0061002400740109864140400300041404803a60241e0250107030029481c0e80c001030890b001c0080440340302a805006e44451001c44060550f055a20798407104001003941055544c6401100c1c000001001740c1c1e080d15105c216607044100070030b9000c5465080002401e002d01016420020601400340031203e203070a0007001d00001300250400c403281d901506101c00c62080044815884070101c0303030502641000720307070564020103008a0900008104910b0509caa544000c1d0010b200088101c00f80d40d0540c01745880c4c11085405100a11405019640d030b400340003180714060f0002c11000141b20094030092000e84103041c800360a0951 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 206914532 1250 206913282 206913293
    0x518010605073c0c0603020301080a02060325050703030f060b091212030a02041403150115020a0804170d020c032e0501080601181505010e0d15020c0d05040815040c03 73
    0x104003c052214100380d041c80040056207003e10024200600d02142598540f1080d01d54510400401a010380800404035040e204901d801c1c1c202c50801d00e4400e501c01e049100002c0203503105010980000f03241400f0302c040d40159009030b10071203006800c00c1d41081e0b161002c0180c3c603450864122035910030b0082000302600c1c04400703580725030b105510040c6c403540f801240d03181c0c1c001ca1064507446a00f204c0c80e980144c0c042078060a0640c0e941c0d911826080ca20f0310340592070200c0d140b00290030300340049400620b1207080201c1d8030504a1200a68885071421002130ba80d074507465440c258940c129611550003030714000031802404003031408400c00303590441194400c9500030b800c2142c80b504480c00600142003c3d41c0d2032440160303289030400c4000611606910045040e010313850421000020803085a80d80e43c04c8840c500d90080e610008104103299030f40001c0d4440400a801030003100408250980100182c40469002c907010b8410034405010103440f01c80000e04c1150719081c2c03030b08040301042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 206915782 1250 206914532 206914613
    0x1603020d0c11010c0507021309020d060e161d010b0c0102090a080a0201020105010b16020607061b0c0b0a020a0203040b0c011e0209040501050a080c0409050c040e0304051801060507 79
    0x61264903441014000c000311070342501c10313080c862400e206080000030016101e010707104c039000041c10b00c005071101d050b200007140c80d00c0d000d501402c1c01d0b040490500c1d0b019804603601c04030894035001001019a00d000c41ca134100d0b200200c060600508000410040e00450001d1482d031028900040ca41100d05000440304600390308820701d9544214101c1c070455030240b14507400b4042c803112540c180200601b5070f01701e549400138024024000412070300108040d50700f00ca0484007860050740c0c40c0703000004004042d0b401021054079228441c80114101310700c06d00c2164a000240e80c051071400f0f04041c265186a0320140d4403589a40d62a00341c44204403015820b072101800c11880035a8030482d4108100070b6500607081b184c4035040120f0100000140001d040350403610903207011500c0e01b018203120741450384400f50190410b00340002c1052200002c0024030580b1001c440d6400c8688850a4001c0301010034011140030170010004a8041600c45d00b01c50300c411942c8811003c1c0c51180f003000f08011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 206917032 1250 206915782 206915801
    0x1501081b0d020108071b062906190c0f1113051014060d020c100c03020406080105010f030e0d23040302100507050a1b0914150103020f0405060301062a0305031603020d 73
    0x115981c9109943d000c0b00700461003810350751001901040c10700c51001030158810b1784003048030400d648ae660044603002e038802e484d03069080202e401600300242000414840c2094080d4802c00d62040340202c590420703c80d141c00b4504030b400107054181070281100642c10b1039603850354010001e000e404030400c0c082c001400d0b00c1d4803501c040e104200203541441c00340d55034448254141801800300380421607011080f503044a509103000c0070020280700060f402401c06031081c4860380502c90080c00401d400001260742508142000d8a14509001400c0158012400000d601c14640520404400d100d00c0240125900a0055801040044c0d403000001c0802c2c2848400701403d02404105d405410300c202d55800d80d035000c103d800b901d4034100700540340b40521900384c103041e400b01c1d0080c0c1100c011800e1320040d0101401c0540d036940c68900251603c000c0d80f50340c0905960091101c0c0303c400c840c18802e00e0555050b1602ca086449551207441d07181c0c074180460b41059800d000944c945600c60240040700b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 206918282 1250 206917032 206917043
    0x7060e010b0a14150d02070c0b03072a03050304231507050a120509010609020319050c070506040605071101150e070e0f120309031501081b0d020108071b 67
    0x21104110522060030101d0303010880d041207280d080c09003503c1c2c1d0850b040b4100d564103504c65440c1000f03c07a0000a0007602406802e000d0042804031300d48401000031070140c0400d0f11246410301e201680c3d801400d42d08032850840c62404059040000d00032409076812078402c1c8014018404404001244a0420920a002030748400380c0d0151440301031b885039802501c10700d4554540030020001034080d50801c100840d95a98075000600207440c20350060010b0300c140e02c0e0542d624204115020401504a646080603d20709000310b070b080c3c2c120001301c0b51150791000140c0413a580320346900c001071a000302840700388140075280c200844801e1085200da40664071001d90380d1030804540e01c944402c024011400d1240003d04140c0e15555000e440c0c804040440700c20030303462740d60b8200030304501034940000d4052040328a9504500d03124580e560588031084102c4032030100149031050303504042160203420040840720440135500c180a581c0d80915a402c0401c020174554808810541e0401e03030035280c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 206919532 1250 206918282 206918291
    0x50a1101051e040f050f030c0f240909220305090402070b01030f0510020a021506060408031611090609011211030304060314090601050a1e180c0e0102070e0115030207060e01 76
    0x54070300c031204924060030b0292113a54101ea84031020a0348e8003141c502d002d20440040d0600310315517891400078021114608100c40c4864024814800250004101c40d4440c2c2c0ca0500084e2500504042d00030440c4002d801d81341c0e511605407030503130350790b4048100300d40c00c00d40821250010036402e54201c0d0003544a40000a0301c0003160410b541814422000c40d01c2c164010401d02007280d90005042110b151841e04040054070b030140010494415035220300341ca40004184442a12103501ca6001d100d405030b0f480c0c0308009600001c12007802d004940507603112568a005000c159040c9004140d5144114608900008a80e00082c0380d50425405040000c1c6c4801901c0c003c110607015450f046100e4a00030f014079414100022003001c2ca0b8010a024800f1107240003085031f101c0f1101390020f10b040300401d25403280034114500a40503c610348004100000c5502190794030000e524402c5500e04941c2691a90902500c42004021403807024105074081c05280080b8407148076a00040841800002d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 206920782 1250 206919532 206919539
    0x50109080702040b04090c1502010912020609060a0203040b011205010f0908090a050301091515030b090a0201140a081603020f12090105012102131103090d090b07050a1101051e04 78
    0x2d603503c10050500031411b20640c4400501c1500309841a60310002d5402c0500c800034004900601000101400300c0d822031407840405030300440c04500401680c0c3c295540c0f0740d48e4601c0c070411f03840705440041c030070414580100444040c10352000c81940c03040340041014141051000141d852004044e950700c003001411100521b48080304000902c0103070000d02400c1215158585607aa00a05c20204561640400869004e404000002440c1e00c4000b00b030342c1d410803401c0e0b50307520070410604034042000141d009c002d100e5948141d403510720480d41c481d1400c1d500c5482d40800280d090011005040d02403110200d1000c29401074041d0034412050303400f181c41e0061950b0700751601070f03002081c1d1108400c2042d1180c0081c4001003801034056414100c09002c40481400901c504021001080d002001b40304200c04003189914102210740d07510700c0715a8031460064100d205200c0002d14a612800e0744400064174804d40c4000e402d4141051b5060a101e0241c4800c0242623501c2c80c50403980008090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 206922032 1250 206920782 206920789
    0xc04050c042d170703080a0e0a06030204050f0409231c021c0302040e01030308060307050406030b09010b0901050f130b0405041212020a120f060b0f120610020325050109080702 77
    0x1100608441c401030020700e540f1901c4544900440c04050b0000034001500310b641401403201e051002d0300540450303101551558010002d40080c00758030b220b1254180d412801d803926010300c5031840d400c40300d030b0865903d070074042d948103541c40500c401d11405040c24800155100246a904021081d0044c103044c45000c41002405c1c594a591942070603c117110521503c3d411902c0e240c152035050034900203170340f01c00001030300e00f585c95406560b00c1404c0080110400109841d8036024507030031740090001c50b402c00204000c1c24401d0069a130803181440104a0502e010500074000c01c1c039886000030390141c40d00110b07040e20000c0300c05440780f06030101400600c032b9004c1d08502800c101940c0c02c41c00c040e00304900a080c0015000c21010941e15074031039186000041d0f0141000344003050115680e41520f1101a840b50080020b004100c103103d80002c0d55030500303110320399105c03445034051450000040b5055101c05490010501e0220f81c5000c000001a0300f4414010501d0084030405d48511807032042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 206923282 1250 206922032 206922119
    0x10503091612030e0d030503070c110301111b0d1d060c061501080a060503070306091109040c0504060501030204051003020a0c05070e010905090a110405070210051609170c04050c04 79
    0x840c01801640c8205c1e021135444015240c00104610b0075241d810510f00700041d65460260000e503265207820300c1e078614031604d9001401d10210484045460b130000740c0300d0701c3d1142d0b484940b501c04500c0140040d0030407107090b1021502c16100802542c1021001c40b0a9032424404543c0c54660b0f00300d041d8040080e40e00400c20b140c3c410142842800000e0070180400d40354881807100401d45500c17242c001c4d04014401c5d424021544010b40240090310b80303801c1c0000c4406440c80b4050146240c0000420ba651083c000c843c1580d00c05412038a060461103001c800075403010410b8820403407244107400c0099030610501000341000401003c0a50400084204961014010101c1d0340e1002d0003510014a2404071410700d50b1084900045540c1c13802d5080e17080003150a20f10411502e0321040140310b50f101c40141a0300e469560764a0041529218490106420f003858410380340d0014422941c80d10b0150030580c1c1c05805030b11b85604280c1c0d1290b040203600b800e1958600e001e8501c0002c1d180707004a00c0c40c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 206924532 1250 206923282 206923307
    0x240c010c020c0a03031407060204210606060c0b0c0f1902030d0f090b0622061707090c09180b090405060403020f060613020310050a15030b06120601050309161203 71
    0x204501d0f004e14650300900710b440c9a900c0031203d0b183c080390010600103140d042e0740c018140d0100e1100600c400312011540c207800c0800c1101c0881c5051008150280302e0000c1440303169000112146c035840f11145405640c112501c030391781c0003004002481c1489030b00b0703515851000d9540c00543d1a420044100004c0e29500300380019034910b000d6481012829400707070690006000c1ea141c1318003449035a0882c0754100090103c1c807805040000004418581003100041e08460000313940d1901d469a60100c02da072520301c0180d001585c010014402d489907003082c05080c8a010f10005050201714000c0b800c0c2000c1104c05503084d0b0003c1c0c04000034143c0500104006006035800741100786400b0303000440c40302102100d90100350b80400042c8000d01c03c1821a0041d040040411030150b5441d0503007104410f0810404000906001c1c00600d40e041400a8a654208040404610f55903000046076150001000c0d1a820710643e81c081c1c24825808041d54007600c1d20321454503080e0a50705000d03140650040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 206925782 1250 206924532 206924539
    0x2040f0c080a1407050405040507020f011a0102061503070314100c030633050a0309020d0c17030a09090929012102030312040516060216140a0302240c010c020c 70
    0x30104104c960b84001120140c50088400180703641341c018040746400203203c40210650301e80421034210450550050018890903400c0711096075501a4010018902542d00c0d038140c4d11804062000400c0c01d001072808085280071158440004598502903441310001000425034851040c03180100c40204203044440c03010001900c2c44256030700031603041541041c402040317130200d400f6446920941101000790780040c55464130b0f10040c1803400c030201540c031800d01e6444a561030184030410110544e0f58a20f0561034603800b1500d0840440d015103c02c44088440c44001506455001000c6000031a00c4620300b10580741581412a0003100320004a403030711403801020803000041c0da0000840320110702c640c44440d1980c4983c03900501c0c013500c00710305d488804100c50001c1202540000c1511503107800c0018501110b81d6440b4036503181040b040c0c03258100a03071500c144050f0500101c044405641141c0d122100804401940d483c3d0f000030200d002c207651503001e80303403803d51f040000790812030084 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 206927032 1250 206925782 206925821
    0x50a06112703060403110102041206150501080c161401020c0a110612160207211101050301050d06200c100501090605031903030b0909010507120e03041202040f0c080a 73
    0x700001d42d0b60000400c010308100c10358140c41002402901520000c1c96000707002000980b00f49044405042e11850444800700c074032a00188540c8148807060103080040ca04c1e6281c42c0f000c0080c0d40c0303840d44040041d0703445034155640032001344091000b03250f514059006041b003d55a850440f10f40303d1802c00261096401380048034400c1661040309400101d09031090800c039102c200c0581c1410000e070b00c070760760300410801d0100803031242c140507005c618480e6560200c0480c1c01070055a00780001e0240a81241c480c4280c0c070000307022a4041201110142c1e5100e154120388000e0b03044c95440804007260341e4121400b014403a02d01070085a0250801880c1400003a040030082540d80b500145854965000d1007485414180607510008070340901130054811071814076040342c082c0c0350031740707440c0c00140c00040d1200e60381540348201c00744611507101035482d1a140c441407240c0007a0203201640e1099490b000a030f032411031442181c00d1440d40340c0f03a19215103810b465070b200311101110488480e075000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 206928282 1250 206927032 206927107
    0x70e0a1a31092003040804140307060c2009070507050c1509010c080708071a090d050412020310091202061605030a09150606030e010b040204030b0c0304050a0611 71
    0xc4104000d40b218180c001400811003090112541c1c40e64894600b00307007000080c070041c0b08200004000341e510a1a00c64000401c001c00e05079034164a204100005000301070400010703c085401e821508801e0680300c0e044803203400000c0340004180c40010120340e00007446410054207001c500d280748004c46a102902029026a0b4a00e214a05101d13041090b518001d200b00007520050340c1c421600b000c00b01e500c0740e10700c2c9030035101340303849000104400310020002050030000040c40801c0684980e0382d14140381ca0b00d001e00000d500c9485040703a044c0200510680380003c54071481c40d46502811b0151a85549140060b08004000d001400d10b100c3ea03500c03112025800c030040701e410918081001801601608150f40404000004003030301d2420f00e007000a036140c2c0b58020314004903480c8001c01143d00c0c04001c1000303c0c499440020b08015035400020b100c0e40e0007501441d0704c00d0003041900c1081000d40d440d0001c035034504404558451003c02c8184100405001c903000340e4034000000281c0114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 206929532 1250 206928282 206928367
    0x11010e1f0e070801020a05040317090d060509030409020705030a0e01050a080705030601210c0201180c090b03010e030a0f090e1e0c09121005060a0e070e0a1a 69
    0x40c2892201262522001c814907401402c0203070100420044000b19200d0102c50002080c81c4d000f0302c41982d80c800f812000030200004a400c5481b15038000304203090103011035079048040e00004000710740741c3c0000c1c80006038540d5140028404a44220003850b5540701c110f1014040181201e841070411031300307010b0001710039040000e858012400e41420b98580d554000100d85c070f454114246034607990303044681d024942c2d603a0050b41414a042d00240101501088a810719040c240c4010380961045002041184401d61103035960080140c00403e49a1000c3c688914580c060708500001490051a50100ba5841400c10000d80303140f5000501c04d090203030300d0110008404000b180d03a6100d5502141c401000e075821107011007000b90809918598402190f501c60b812803e001e8070703050405000510381d04d00001d1440591b0701c6080280740c0c64507901011201c0e5441c082900b904410344080114004a4009003185203032403e01c115950341c0038840801d848019178800c5c08100d4405c1c4404070705d8180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 206930782 1250 206929532 206929573
    0x2130b0d0e060702150916180c0f020c040218180703050603010209210a02040609020d050105030a1a0a06031a040201020c090907120501020d0c0315080d02070303030b060c060711010e 80
    0x200c00561005e640c480d03003c05400c11200d0304416001d40070100d00056140e50805008454100b09041000780701140c81080d40c00c0c0c01d200910780c0050b005506030300710600d0264040c00c40030b01c045400c1e0500480403408180b881c40842100000810a4010840a0369160142503802103041e002541421818000700d164010400d996a5001c1200fa40c86502d42c44204689000c00340c0007402070088030703039030342c80c4100035403080200328021030600d00081410b0070005401c07440c1c0b5901120622910203010020300d05200098845550320342c4800000002c00d15241c2c82c442404141c01d0b407080c550a0500c00a8500b103201d8084600600c031301402c100c1c40e21000324981c8101d441e28140452080f41c3c6141c094020310641d07d02c00101d0385420000c00909600d1341c80401082c284404a409a03a1501c88060750340410440900c01a44001c1c0e061002074030a800c1418141c0b0040c04031801d151041c00c070300d4140074044502c2800500e642034014140a001d008142c0c02c0c105610240c5100d10290086040c0ca6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 206932032 1250 206930782 206930803
    0x30515090a03140705010f1109010311070807031809090309060807030905060105060a021212010e10080c0103020d06090504051f0207020f06131a0307021b2202130b0d0e060702 77
    0x200d1004c550841445801e400c44120126903040030803654250005500c05508100da00a00082c5010340c51034801e040403046036141600044c0c000c0c24000e055504a802581c0140101d08030070200c10f0028042c0a84c1c007850741a240709498105d0102d003040700007408007a00a00305030816007482072203404103902140d01c1741501d030183c0325543c1d50418218181d103450026851509078800c00202031004405800c84c0905941c0314804880203a103620780140c5012040d0702501c8c02a402c445040b48003503010754010142316080030f00206040d0354403048101114002c80e81502d0381d401c04002613004201e11149484400200c185c11402c0145a40200701010050342c94903014010014010070b6900b1000b425200030152070411080d09051103d12603065001510202c01503c51045900e04603100d01060798029140900031007622110b2402c90307400664003541c1a01104d5003003001d03030030a0302c0b000b0504028010640708c640c0e40741c40317071980e80c07040b510703001307011807040d044103081c8501c095001c00d03040c891 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 206933282 1250 206932032 206932067
    0x110a0c0312020912011a1008071803060504030302090f04020a0905010c02040f02130815070c120c0819110613030c060216030305090606010201050708010b0a090807030515090a03 78
    0x888030040742860080c4200c80046a000f414608103903112079054001c4488808406580640002d032581400910129040d82c500841c04401c0091851480703405010b43c00c541d000d012082865490721b4141c11960260703415800030341c0000c0c2c9071945050180c0e102540b031a081d502103180c000340050041461581d40a40e60400401c405d25005540d255000a0f548a8509100319598211180b800103070f058584221801d134060405041041e40d00160717081e128050680300d0310b00c82410b031f81c0e1b03c1091109220500b03052024002d510004074002c203010300241e10b411140309030000321071031024000614805644103140d12502c20094110118038200c220241e1501f000080c8004500d401400b03401445000103c0d801070134500710a06505800c4a0301404850303056800689454004a00b40d80f811103900010071600030040024003070b03401c0185842c003c50310b0203401c00d0341c07541041400c20340030398400e072503030740c400d03004154034010b42c40c0c65035080f942ca40300030078903c1095036020b050045049000e000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 206934532 1250 206933282 206933297
    0x610020a030203030c1b070b2d090607030302071b1707030809010305060a0905100e090607080117010b030f10140907031e05010524010c0209060613150203070303110a0c03 75
    0x6c0015241e0100741d2403040038152007000343ca8000011458100500c00640340030503e4884403407a4030b0140b05003030420f01003841c51606180700140700042e48012422020541c1c00c003c02d9022803e04142d05601201504840c510146450446104a504144042c8003500540e00800001d450182160282e50080c200807038985d5038400020148a490f5210400b99030a0008001d00310a04003112000c1d10346608801e20203443d42c904455a8800c103d4504010951140040c0328614541103901d00d07001c0200c0001c9450758401740401e0510f00c0392700040c1042d601000c59245e40011134000c00002c1c401c41401a90703146002850641c1c1c50f0b219200c040d101449840701710780c521415205203040c131b0350000001d0145080581c801c550700352810142081c04103059409200b0780d03218000016000390014104101d5490300c4080010b00c0c0d2000011442c4104c0501000901c10080780e188041d000c2c1c00c0d0040c5842d03620a04001d001d82e501c00030380101404013000340901444d0000d071042045905031130407c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 206935782 1250 206934532 206934547
    0x301090b010c0b01060e030d0309030c02040b0a0b04090e010b1002060127060b090f1e0909010b0312071a060d06090c0e0108010b040608060105010804020d060b06120610020a030203030c 81
    0x2034a00506078409440c2c90680c3c4000314019802000c84110307020150115400801c1d03021003282221161b00c030082c0040c00f00d44a840c013602c0c15403c100d0055500403c52000030b0350b200750f000300641c056404011910341301e0580c041d49400038071903d80800415541990b087e4041c1a0080d02c60205000381800503969000380c2c0ca0b195030400d01502112400c480810800307486404111258100401680c480d403005104020ba40c2400c0d000104a4820655290b00385440e42e41040300d01400106030000d559601da101c014103503000c00c0160b00b0742c400061300e980d50b88030a0910703030750310001d50240006a220600c2880311540390b100044c004950480d1f0b00050142c1c1c0c80c5440c0e50034a401e07a002010000c940c000100d5030504c1075201c1c0c55250011501004000c3c0d440002d00e0700ca1009104884c0410424000180517050002c40c2006062250b0130000303840072104001040e540044100740800c20a40c000c00005040c40801e4003041c41d22400284081c40140d0b5000b59684001403108407516004200314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 206937032 1250 206935782 206935787
    0x302010306300f081810090b0a030f180b0106080a0207021f0309050d050c15060a0b09011b03080a060e040f1101020a021c0c0b0a092306130303110d050301090b01 71
    0x400041d488001302d43e07154110f4203965464506110024071400a849085403403500600a501c01c65155a41983c240310880708194000c1480c42190411030792207a04181e004407031684042045c52051900d05580c0d410100001c04804000305862545817040100d100503a6038100301d44180c0c689071031101c0d142410100b04901a112a2100812074800d000c0e0041031aa0090040c0004049080c200d4240351511800704160005c2030b20120340068400e40c0c2400800c00407001404402010b05100d10440c1d00300c0c0070440d480002c84001d800081c1c411092054481d014025000140101000b200081c00c09071603d04010b207165500404007096a0001c544a900a002c00290150020040302d1880e0220400c2e80c10540221400c940d041015000495444146002c2e915104c000d07179540046a8188100c940c0044042c60300c980780c44000081c4100690f455100801c14800d1000c1c080500358070318503002c2d0070710f051900030740c81a800c80500c641c03909038410b058a0440702c0f5000c021405d451200d005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 206938282 1250 206937032 206937053
    0x115030615030902090601020109031b020607140102071203060b12100503120c0c0108010305120a050f0706140703060605090613030206030c070b070801061d01120f06030201030630 79
    0x559541d0342550480e60890709940020801c40c000c0e1000045540c81c2c0b4012800c0b5140024000c01007903c2c0002c400c401d8064401c4884903505c00350017a071501c00940c460045806070203400390296034001400d1810481c000c9a40502104070f41820f200b15820500c0007070190007500703180000c6401850001d044442c0b58803404000b000d01400383e400c405140a20a0b00660000139451007a118039000541103501c2052240e048a811001400020710740c3c03554800b4990014000304100101440342e0022100c8120081140d5481044001691503400a6110750400700408142c2410300e045400c00c000f580180031a2221407007260b1301d03543c82400400ba4665806550000b9400c62004001c0040144414000348a0540a500b0070807540d46c0760101100c01060901a41c000182040d1a03050b00c42401e1a10405d0414141440c0000c002e0301c0301500111280d51102651464440303000300103650f0544502400350681a03e800b010304130900d5944034802d4412010807000000b001c5500500100004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 206939532 1250 206938282 206938289
    0xe040b0114040b0405041506020319090305010c1707021506040b03070902030403050405130608030f0313050d02070f09110a110a0609050604060f0504051e030705070312111501150306 80
    0x4655201c1e0f0f260740868005070098068035000c1d41c0b40510041840c04204680c10480d0a594000c6150251400e4411142c98540c610001401070235500400000d900f80650001250540d80b0422100c606c0e818002c0d910708041c3ca400b0654003d9083c1544810106003842c1d03000005035004161242c080d40802c2c500a42603202c00e042d68400b00c1403004042d800741c0140202e0b182100c4001c0e85140d40360161013150b0a6203d81c40d042d500400c0340d035201401c040095940003808902200ea0a42c0d10f031070b601d044c800a80026801030b044100c2c00d2003400e00000c1c0c03602c0501400c0000b04100da0919948540d144646460743c001c0c004034906807078210104108480310f10b90720001c103100c0104a89072403a551a029602191403a0900e410201c100d1801c0c41140e20440d040300081c1031480000c040d07200e6062518518a070036020810070300010a208201c02d5000b0342c030a00800124240101c0d0040a68000070460741c075503003200000140380e2406007a99030665401c01001030020194003070079001132000d41e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 206940782 1250 206939532 206939567
    0x231f030602160c0503150a050a0b0d030e03011d06010909060e03160203280f080c030f07020312030402010f0f020102130b0705060601082a130e0106120204060e040b01 73
    0x6480000e01c0d0000b02d810740e2640c40ba070800899181c40f01d04058580d200c541c007a40010f07000710001001d0a103550003803030700034a044000103880c100090100c1c1e13100170b40072003e5001c954100c252071003d080906c96000c0303521602e400141c54600500609854240c184030f880c22180d114001c203014405141e10542441040c40220b03030351440902c5c181104034102040c00d9220340180075000c0c0004004482c03031001c02c5200300315040c62006a507180030740c42414500960f0301107014001c1c00190401000109a6040c00d40c4041c0d440741040c3c4100340c6058410818500e900c542031080c000180d8110319280208150307400c2c901483c4e18808070480c0280141d420444a44a44400000e8200001001801144c2c000c10649806542d13144c015a00003100f928400142ca030b004012007000304c04100548002001ea101d20703403500c01c181c106174100c0413a40e08811010040200104943d40d003114040341c41c0f1501107002e505291512401038a0304100c0300c041d074003654680850303c6c41c80e842000b0800c06c4c0e40101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 206942032 1250 206940782 206940787
    0x5070203150f01060807020d0c030f020106030b070302070204110414060a1701030b0108010b04060b09100e0604030b071b1524030b01230a1e0801020a020102030703231f030602 77
    0x10010b140c0d80031000e114190101d50440e01140440c0d2000c1401c8401c50f040380c0350902c180c1d0180c1c1d021101d80322440340c10011556104800f100103054942c40d18091011035402684400b61401000111080070300100c2180034204030410001c0800c11003000c40440845d4402c0d11143c03541801d0340d41c404000d0b5005c041180d950004030821400d0400c280c180d44501000b0030442014800380021140349005424280906001400d05441c040e031180002040ae80b820140030340c01783d804104607400c00e800032640c1400e034404000308a9480310f40c0102720201007085e501081d440d601d44068142868019114031a01e039000c030141c203016124290816078035500d540b0582a582e0a0209c0107020a000d84003030a02190101d07000300241200051902100402031485a0310740721840010119018000304410810040002c07441000c0c03026002e091135540000d40c3d20f01d0425002012552516582e200d01d641c6038000320110381502540d2075002c0c04241c000c4046200c039000115461099a0000702400d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 206943282 1250 206942032 206942041
    0xc01050a1a040b0a030602030a020f0721020a0807020603060d0b090d030e0312152101050f01050105070f031101020f040609030b010503010e0607030b04060b030106170121030507020315 81
    0x40c1d01450410400e031034030040c403940c80c804020a84118540596115200c94018808526503500860704480c02060061038194208440045900a00c10548a511161003024402d25900170140e04903002803024020b41504c6079142d0f1007500459001900450000c40055244c0c0c4a8080a844030390704001d011025140a546099641c4100c0070201e0009003400ea80000410b0000140ca64a0352000044641680e5540040c58000d080c01c280d180d105d0200714180306c940c44a039041070300c400001c100201d41880c0c8481440701e8050180d01c2a810400700300700f40d0002c540100128640140c0c145001c00e20407a100a0190280c05482c81440031094001000a038040d044510f03042101c0c480c9250006507030380d400406080750503e29000c02690802c0d4005841248264069258000000d200250880d00c9201c540196042600007a012401e4030b01620041d18507903c410b030040440b103048641c41484108258000c1c40c0841000302800790104120341155014805001404e50404040032145803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 206944532 1250 206943282 206943301
    0x30209060409020d0c050910030b0d08030f0f010807051c0c0504180b06040c05072603010905060102060610020c04021308011401030b15100503060103020d0624020703150902060c0105 80
    0x2c901903201e40300d80f45c05032215180340140196a40c0070001001c540c4a0454640e0503000b50000300c0c0d501d584409500510000a87d004014500450885a50441038900009060070b040410b03001070071290f1104104010b1540c40c0c1c0f1080303aa81005800d11404400e091404e1103110805400c030b41d0344207003440c00555040003001d414403e514020b00c0d805101d501c2d80401c0c042110141c0b5101c0c4005403042100c8800300e80740b1104459540305062800502802140780034075560420303044000c1c400d0f207a0090002c59a8100505d64200c9021140006000d0300d41d140a5520240710031390500a43d000b240455150f268000e100c8003c2c200300e070003400171100c20b030324424021400340821030300c0701e20030000301e250b14808440c0b0544500c0e020300b0726609120422401d5031150402460981050340800c010300303841354540a040b00a020000050310380181351804041c51170b100310079585c00c6512004080004c60384103040c5c0c0081d0388090f880001c030295030b40040368103446442010303400d6600701002c1c4088c140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 206945782 1250 206944532 206944537
    0x80903010e030d27021c060905010506011103030721090206071401061a030604020f190306030302071a0306040510080303041505061002060f101e030b0a15031203020906040902 77
    0x11400040010071002c2001e0800e4048600d5003880c00d4040c00156130040c2000c940c2d4021b07003111b110180c4042910f5644400903200308280480c3c40d83d440b601482251f5030850400e0390200b0980010b0741c118903101c0001004161008054a403002d4203d00800b0480203a6000692254016001d250f4541c8682440c5000a40900c000c0d00c10358a4000e001480440150040c09902c04031072100b4516200d502c1000040d4015012103942150204200a0900c4610080000b0240d041e01c1c0401c485145040190500c85107503c641d0b0380388500000084180c040d00120707076004000b2500042c150f103c45024034211103403900244131920001052200f4082c0540580d80b4003031004600307102940e02c1200b0b001c03040f20304a1404015a00c40e1001c6507828038402c00103a48110b103010929000c1d543c400c04c4c3c070381041350702c0003080c4800c18180c410300034031a11022295103d4072040c002d009a00c0d07424400001c2d0085844050308520803d021481000e2003a0126080900f008010a4a4076202c024000096 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 206947032 1250 206945782 206945797
    0xe06041d01050603090d0c062c100c0903031b06090b100b04120303020307110d110c0603040f020919020307080601110706020d050c1005090109020a121e080903010e03 73
    0x300c40c58000141c2d0f00c0c085048074441c420f48005404507241100c81a15130031901c1204a601a03160030711503409440f409071000c507040c8900c0c5075008440c8940480c50602c2110044441c0c0b0b00c4c2070140d140500707508440329104496051030217100340c41c01e200740030701004481400101002d0401b0401d2051200e507256090182506c2ca10401e019070395401070b205a8881d030b2003034184c2d0f60f01600000300840d00950140d580a02d41e42030440c002846080080d05118142005201103400943c03208034800040151402141c01a42e99500d5405e1940b1307040c3c40c600c600c20703000707100700f2448001442c100a2034080c101c8540403c0d10540d1641010280a40b001c003088840c0380c006010405a10900b410006900c4200c400b07a8000c0d10b0140c5180c1c008507010343c407006000c42644286403030080f000c84c0d1485050301c51441c41c400001e00466500c1004031010700361b40240300c40e0280600309030101d1a2030007020854020075020441800007403034403030f40500074142c40c1603155180260815140b0000f000070b0800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 206948282 1250 206947032 206947079
    0xb0108180309032b0801030b0411011e0201060801060b040b030105040b1206070f0e0301020324010c0206031e10060503010e07201f021305060c01091713090207031209030e0604 77
    0x151484007103c1401c003d00c0003a00d01c0803d1000300327000c10301800d5007084510041c503102000c0391490034501916032040c3c00ca440141e5455108007c500002e12514014000c80c8040526085c540100804940410b0003400d01c40d581d14102c804141c0c0e10081c41c40360080040040c0c91052800c04000760040101150007804a01c03242c08143c040d244c10b1003101d110700c900e107541c418880d45d0501c40590710420310341018103000c00588034002590341c00e009148100c2101c451801c620568403125850b0340405400210340d014928010701804d500001643d054a0034140b2032078076551100c60854844404998030034030b01c403549000300d59801010070705199510f08038060807001910000074104034850010000113407280c1030020311452405000a080819001c40003040c070592070b4a03030140301491015800c41600c000540e540c02080d52044a8000f0404905c085003028036607140684440301021b074000c942c4d642c034000b0320704140c000c03a10880000f801074286500c8a03115580300d10801a500c220303501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 206949532 1250 206948282 206948353
    0x60f090902091305031909050a080102041e0303140307030902130203160504060c0b0402030708030a050705070603020a080a0f060b030c090a0909080f180d11090a0b010818030903 78
    0x6018141203c00040b290300c01c00562412a50741b01c000072040340150810200b1108040000e12551803449140252402800059850786402c4160707007817541c91510401c206280d4802000400d0308074004800d1900c00c034601316940d1317894101c104c0040400e01c4000350b000c404418034914900155000c0c6d031043c151002d01c0d54409401403010783e40c6000e41e03c19000001c032040c140c0030008804040c0c01d50428400f82c2110b01641c0c680d8040e60035600f110704640300041c40400e00302c0c10300c04200000401841103040031854407070300b041c005003001c0b0018803210101e621124003440c040d280364001070041c80c0c0e413041681ca07800c100104113116400000c60b580b02d12484000030448070414410990345076841904181b80c00590034800c1541e400c01c1d40744403500807002c0404111034441d80b0340d008101d4840c0300d011203400d0000c4108030b0f400350040d01c0124401d02d814028521a41c000d00340541107080c04558500d2500098003983c614130844903050303014010800d100400c0c0f4503040c212041c1000d030402120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 206950782 1250 206949532 206949541
    0xd020c10050402031903050d050a0c080112120305070c0f03020309040e070e060d080c24090d0f051303170702090601083c070c0620091003060f09090209 67
    0x3401c0d110207a50107941500b1001c0101048190b076092131481e144a03040180c20061a95017000480f481101c290b00c010b505e0b003000001c44d0b5880840140036202c0c040c850015800107880b1080d150030540b100740241076981e008170702d0560045021006a590001ca445001c92280c5802500da4200c2c02c00b00d4003a6081c4144000c00c0400401d1407010348004904861580c0d4504080104140485000362403011040211039206c0c0002e1000c40100000441910b40303100d40d040380b00381e4190300200103c00c0c1d03030401790314001d4165001a416508015621740349455861215044900320116403006020b010900400015000c00b90080c0910f14002c450714a4242ea81000540d1115001c40c3e1041d40d14150040900150000c00b40c000c68501607410000700107000700d100301d00710365016940350300810204003085040000c14000e03107013200d400e0107084000401040c0c0340c40041c0101b0100511078000c502450a040744a80e00c200001e1601d000c0d04004280c0c1c64921100401c403010003680650891800136 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 206952032 1250 206950782 206950813
    0xd0c2a0f05030c131d0f010603030e0103020315130204080f1f060303090e0907030209091006080708030f030408191805010206061e03010b030d020708150606040b030a0207080d020c 79
    0x20a89820080d204e00600c40010144900a04100401070b00514075a0001c00548508020b489030040d10a0000a1000c1c150f0074080c00034500003050038101341c01001081504101c4401444004dd81599070744800311030403011401034000c80d041043d00e40302d0120080d0480c0c0300001e031030f2244007400d0a1341c248850403440034000d03641d039404007401051087c03e0410a110344a88010380c04001c00f400c2d140016203e500087c840748044c6c41d065259403004081501040c045e1040000401201d0020700e14140f0300003841d46c0741c1c01103104080d818200800020280405d0314111340064245d40000c03903030903801440290a40011503008060306084400100d02940001210f0303008660040c10400410765140809031090800d0100c80e805540b10465014140c44c100a1132104201d6034004d4024503003801d001501d092a04643c0320010060f190501401d916080200ca0030b0f00d80400085a4035961200303840060300c80c004008004a1001131104111003c940c0901044c10000082d144000401c0241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 206953282 1250 206952032 206952043
    0xb0910062006013305041706150d050a020316032906040b130504080316050304022107031515060518060a0e09010b0703090501050c0d0c2a0f0503 64
    0x3148075030780008014055988050f0452004094560102e107a8440d040d038281c80c0040e803010b0032804620040b43c1886445142c020b40300e000c54481008007202e190040455040003000200b0710f002c1d90100c10b610302400005d000e030383c6c002a000340440d030f521500c19200001c0300f41daa00c410713030380b003200580010800a00683c400b65600c0c0d0700c81c4040c41035260b20082100a040d4141400c1d886103401d19000e03101c000900032588228001c0d211140c030381c5030860700c418000f00f842444608000e402c208210050390f40c2901c2c43c030030302d12168000000e501c40b14160340c9020416040a01020382d0030701084040700c01764002c0a00c24020300d6114044559808081d0368501404404421440c03541c0ca00d041c10782410000744c440410145040d01c665043c1c000071451444e030a8001409041c8002000404d05804c0100c1c80000c00080c40d025103400c0222440d103464041c191030380010003d0001984051056400c4e0500896603224800b1041411200c0c3d205160310380e61150b8000c010031842c00148500c0d01158 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 206954532 1250 206953282 206953337
    0x1807030507080f040201140c19020102010f060f0306020c011d0f07060801050117071b060f050903120c09010309140f0607050a09031719020607080f040f03030b03010b091006 76
    0x1040b1003130304c0e15030054400188500402c0d03000d4805000e48520f8280070000d03412a507541c501c0c03c2c0c01c03282c0c20b8000242501ca0b2000d55900050615000b04030102d03000b0065002c90350003000042e00c1c1e030143c0031618054000401055000030400c00c1c49586120003003010f801803400003049502c02552040150340750102403250a0103c0c202e0302c80c020842500c5050598880454589200b8600e40c00320900515020403030b0640741941e03a5594203600c007901c2d02c540c80c1c018002200540c140030614200408032003004202d40b0151340c01003000039690b4060340100c0016079001200292055003560b80c03555906a02d04240503611881d00811841070160046441c895001e0b07490ad40c17518150b071614001041408015011000e0400031f6995108140d041404444000e9000d02107900b401040144041e8001c0c03c1d5030f402c4521a024000024414442004000e900d030034080b032441030b40000a40140300d0013091a804c000d04004100038644d40c101404141ca00646a10246400d03881d54821b8040441a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 206955782 1250 206954532 206954551
    0x60e0601051204060605040c050705010e0304080c0d0606050405010905190b011e020708070b1207090b070308151206060a2309060a030507030503090a05010f0c1e02180703050708 78
    0x10801ea20b065a8202e250b20a0068030041400b640e40c20101d41114418445030000134008a40030f420403a0078000e80c03002c0d0f01c009000311b00b090b091003610750320760f2002104544200940c901c8041041929000200209802081080b140d0b079151984005040b084400f00780880440b0faa41d030301c4080500c101c40640a040c0d6031110504c40b0960030b40901e9504030300300b40651242c04e000040c0b00d1402c100d00000f0300000c90003503481e05900481c0c01503643d40175100c0018443d2402d009e101c16400302c03080c0ca8015405281601803511010140512880c20041064202b034800c644010305c1a80058800d002c0e2006440365048107541380c402903d484141d441c1c003080d4103c40c92107061203262a644c05500500c0041014501c940c0d1b940d03d0501e4200103500868054001180d20f0501e894428810001000203003801000480c081000400c55070303040100411034200042880030050009110340300003135020b4a0141c0c074880e076400c15042c1c614120368020001c1c1c1098001030301d1034070500c076590160301c04a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 206957032 1250 206955782 206955787
    0x914010c090b250809010e0111060f1b0a020717070501050405060d020c0d1706010f021e030415230c060c0919150905090108070b0d061505030a060e060105 68
    0x65261950711004007a01d07280e0f090203010036295101c8044010840c07181d0b00070350317540d0309000004d4003008008030300b28103119469109892019010840359408224400340000d10707a91941102e0006c2c41c9141104140c41000c5961300303801c0e40026a60003039410341c0308420003a00041120542c0c1d005c2038001c82d40090b005010801090030010084d2846840540d0098181020900090f07c1e04201408000000e03c01a182e110800b00036082290801c40a00c0c141408050008000c1e41e580c5081008482a0b0302c0e401c18a11409410300c20f4070083d102031110802d42030348041c0700400d5803000b04000c0c907030880c80444156008034024229040c002c1118040d0009903201101032107140c03c603a5255400204d58540703030f400c1016489a180c06410b0803000c40454a0705280010108a00c0d40c0101d4020402040180b0680900140342e004464125003d15525038001500710040c00050780003480c041d10f151000c02c0c0740c6801001541c4a0315060008102031991003030303104007014040d00c8050100e10304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 206958282 1250 206957032 206957039
    0xb031303031a0910030605010e070c020d0c030c090c080a0207030e0904030513180b123c0136030302030c1e0d0c02070e0c0703020703050708010914010c09 68
    0x342c02101c0040799481c01c0b082c505001001061042c2401c07940f60080d49103c000500030401a40300e810301400d0a2a038070180c51400c00c4020b8400c180144020344103a810314100400c024074820140041e42e8029088031841e903403225650301038030a290020022600d5040001c1601610744280c0c0ca0040d09660341c03a6240e034500c403c0c082e202802a2094041160420026890300040410f0a00405c65204214804800309903102c040341c0f03201c6541841000c6070b40b00700f80d50803000550303202150b4842d422415040c4a4600c000150f88070160303080c8098403054001244030308103500803150137000b101c2c0c6544070504007030304241c092154400d0194007000b05030014080383c400d0b4042c2d980302c0b00009925141c2056030a00c040e42030f032080d000c80b41c0382400080390b0000d4101800b5000c0020b4190004006040c07d00a00c042c01d081c006014196004000c10420141882080700c90000c41d000b1066404480d2545c1c100c40c081c0c0820780c1c041d50301a801c100320000c6500e0511400920146590360240050309 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 206959532 1250 206958282 206958287
    0x1120b0607020d03110115051c230c0409050c0102010e070303080424021612030603020913020d02091311010f02060f0604020c0d0801030204060504050405030f07060912020a05070b031303 82
    0x410f0300382a4100408050403e0425001340710706428045907140201500e413600f0104803080121b021130007500300044090308001501426122031140151200320860300008034080d1510015840640e07001d402c1c802da00007444000f01e0f00d01c101d14000ea00034031521034549a410b03520442c5110040004961500144c08201aa4403261401c0791151801d03200c0d4101050b44000d90708920740b0a509081c0ea0600b01041110441104164124605081c00000e00d10340005004030300060000080e0040400300d0f0f4219075810000400300355000f00451240e0a09803449403651401d40d0301154198591a00c2c8070266000302140482c0d00741c0c550040c40c6075a80d00c4801c0d4043e880180000f90055000c1c0820028a01c00380f25085040e03040f03658030070a6601d5801080183d490307a80c00039020f2032510060002003040441207910540b0307142c1d101941c580c05441c050000303000702d03d00507246c00e5190640e480203d50224a10040c24004c500315451991591005200c612041d141e2054203080600901300190 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 206960782 1250 206959532 206959549
    0x70501230c070201090321020606040b150309100603050f190b01090b0a08011d07090b0105031b0c0709020c0114071b05011b02010b031902030303070c150c02010b01120b060702 77
    0x2d00c103140801446660380d40e078120747c1c140c04032000395581e030100e10300c600980c1c1088600e070b000300c007101d003030004580700e2012030b1113001c11030941d0460340d90000c00500c1d420b804201408410542a10800c004c40c0d03a400d0840c3c8030350288103524042e0003042c040d054080940c048078201d450704155140c0050740b1389071020000300ba04091b40c41c0c00ca180d078180080c8000007842240c101c140d005145034110940035103c24107000c650741000040a16104440080fa42e000302900d030302c01c5009410103c050386514920f0150b01884000118070b00c101103000c11082003d401030041a484040248240500724025080c103c000b2207030400003452840341c20110241240600071070b2400f80c00006940c10105501c1d050054484038900c0141c2e4481c082007000d41820441a41035000b058041c040945050380080e450b4480981101d0400500d40c65481c18490f0b03981100801d190501c3c400c101990030380c2c4001c1d02030445007901501041540090007066039590140302c0580d20001d00d103d1a080240d42080b00d5003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 206962032 1250 206960782 206960797
    0xc120a02161d0702100f0f060503071208090319050109120518040203061201020423030d0f0f05040b0304030c11030c090c0f091c06112b0b04020f070501230c 69
    0x1881405c0b4190038800b4548039035504001800008280301107140c0d041010380340703d40c0c04107000e03034480001000351148900b01444801d03030008240780c1d40c0060000181c80e01d204403540902e00c505009602c010000c056000b016010310800e0a9404010410783c180d81b680625004440402c0c0d00a070141007925040d40110381c4084020f21031340031507485d9842c1c1c2c0d003240c00c950400d117a8904800c0d0103409003000fa0100407401c5800f00c00078030300c204002800400498910030880c080c0101d0040744260140160296401b400c1307880803498030ba00c0d0a040c010281006103505640c1182e01940941441c06d01140c14030f000f0701d000e4082409900d941c0002510365001102203039000400340020310481c1c0d12030350900781c05000c01c03800c03600d640485c0c00c251089421251481c40700700010840f006075031001c54001229500b0202d091139a2200d403c40c44400b410000d000309501c00c3c40040c0900d150000940500181c60107800200201040202803006081b90f1545c240700440c91200028100342d00a4001c1658 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 206963282 1250 206962032 206962037
    0xa120e1e0709090f0b01150c0f0c050904030503070e1509330a0e0102010b1809010e0102031f051203040308070501140c0307020c0a031509080c120a02161d07 69
    0x52a80c1c841c2c0c04001c40d040d6100031074181e01108202c000340040740000070b02400c140301000621003102c14001d8100315803844001d01407440c41805406206003105903800401c800341c0f48a0032403400d890001d0248c0e004079090740216062405419880c02c0c068011b8443e4440000240d00d000ea55800300000d480c0440c00744580010071001c07904000203e514468000c8403c0c62881e912904111000350100e405420442c1c116803400442074115600c03042c8200a2140102182c20345845140c400707805803142810a000f10340c0004207006001008110f0100c1020201ca2415812611078003005079988485100c01d509500a08c0706001080300000105400d510800c000981d40e21f0b054946803022500311503e846020001c010001180d03010302c0300070300c120401c41d003031501113045070f031068400d401d10007500d0000343e9600254000c0100c41e00c01c13203010000450460745a201ca03a9a03004c165031198080a0042c001c2c0c00d400c8a400101324091025a01c480e9100c840088543d5080c9100e5800101034404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 206964532 1250 206963282 206963293
    0x20030109150302130204050901210204020c0a02030d0f0e06030f0a1e15031103030a0f030b04061a030105121203040303150506180a150804020909010e060a020a120e1e 73
    0x680d901c0d0804c407403803543c3c4a400360302c50303103440b040012807a416070040b814910103050218445000032005c3d40e00aa04a80068590303000c0c0d0720062402c02c00300c200940600c12940281c03202070b0442d14115007a15503513100d0002c982d103030040c0002800300380c400000f0500040045001800c142e00440703504a14103201d40c0c1c1d1016216500700584040c21401d804600402006200b805a400340b4a40140001d800a40c0381c07000c1c41c50010002001c01509104040d51681d1080e0640d41d00d410100081802211140e180c400317007414605241c0c428450548a2150350035010301c3c8550104d2210030f40d0a0300508142503503219107090f009402f030144211122160b078500441d135980c8403409403544045070345d510b01848100d0300501060111a03000f45140d18403c1e84803100743c0784e00048a50b8000d030f0680320f00402d52900508207025141e01404201d090042208100101c40c5641c00741050a04643d6074011520929031400203c5030790140e54030342d90b04089000424803084000740500100100100c0310b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 206965782 1250 206964532 206964539
    0x52502060705031b07090b060a080703020c0304030c0815130308060a151806050f04030311030705010903120f051b0c15150f0a060e091e0408030a2003010915 69
    0x41c20b6030301154500360303640c00c100b01c801800304c1c2c2007000b0401b9203041c4504001241d0b000700042e126000e17401d041c0003000020000240301070310170703010b4a40c603005050407680c0700c0c0c4d142d00c1d104400300310034010a101440359040181203401300c0803e25014081c9860170f00d5190b00d40d500c3c21945003000074162a04a0743c104400903140c0302403269240e00c0702c681d6450301c1c1c05420041b0300d161805016032101d41040320900140e50300010a104039800c985c4d150810201c084800b2944030b0447c040c070600075145500c0e11104c5000e258000120000800b074075003040054141c500510f50890310700f501c0034400101c1c0c6054101129006000400782941d804007114081d5940b200c0c9401421411107403071b80b20782c040c00300301280b40c280391034010034402045502d44030090526000409080c40304484521603043c0c040446d84551020a0030884001c0340c1c8010803482c03400b402d0200c8140c0c02030700e40c004650b14081d006000380040d0022020700200c103030095440e5900e45020500505200c00d00840080f503040c1000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 206967032 1250 206965782 206965793
    0x120c020f0a0f0e1f0e070f03090c1e030503180108090a05060a0b010e04060303020304090609060b0f07080f130e01090902030c091f090c08010f080a120c0803090a0b070525020607 78
    0x8001131481454503e11783c9003104c070040004103880202d00a05042c1801d11001030003000d1484c040d10206110799400d10f028103506100c13801594000b40440c0000a402001e0302d84843c1c03002c9a9940031380354a141a20790600041e911100201e010b88260005070100f02c8034082a044030340f01364014904140c0342161100000d0440325a03601c201d015a20029003080045240c0c0154002888110b0702000010302d4103800040d0362241200ca402d1740480060351038104000f0105032229203100f24403164580c440c911000c1848071560141801c0a1030b214000100300c4a28003849406581c00307030190034150b000005110001c540036040240065811840004205807080904020103005102081900c030ba03003006003018006822018044241c1c00c81440304210001b511010f0540c0650a130141400940044030300f80c46400009006a000006001442c0f00c000f032440030482c020954001c540d01d5021040e1054030510606001010308104001c451400100001951030700161010346003850a540d030303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 206968282 1250 206967032 206967091
    0x506070305130206121b040303080f0402060f0c0303010501020c090c07020103091511090418050d0513120303020a0306080106050d0605060612040b040b060307030b1f03120c020f0a0f0e 81
    0x160031019401d001b000000c0c107410004440300c0c41c0401d00360b4501421510020070500c8020300c920740c101c8005e0042821901c2c2d000846940b4003003c14442d4440c415403003080c1d00c9600030301c00d050061064050054dd02c0c6003d07141349018a800c03040840c588425030740150050310000c001900c2c0c013050f13440c8028003a9070500548280301c1c00311007040e0b41c4100b11400c2100700c8061100510b0341c0032600c502c400008a00180c00c01034520310f810f02c00e4858582894030040c0c4200c0780c000002c24400d0309940e100f0140c06030050300c0d1510b240d480c10b018103030300c807002e450881c1d01e0703446210ba11008215140e804201154003103908280081c0006103424000541c2c9621040190750845042d64100100002c0c401a42002d6402c02000c60107131143c1481c41c1c6410304045400740003041000c20000e0404e107000410703283c010003540d01142c590200039003480042c000c948080016030103840340c0d82d010980c61800c43e500381c01342c4400340703203074a6603d0810503c556010700003089209518400003001c0080604e0701017 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 206969532 1250 206968282 206968297
    0x1090506070906140a02030a0c0819080a050f0f01051201020405040501060c12020609031c0b18010f050d020a030b0613050c0a030608030a0e120709020409020405010206130506070305130206 83
    0x40b544095460080014a210f40d4518066500d88060040343c10f10381e400320880d02e450308507107000c00c1e25425904204400d4440d441c039941c0803c540d8050060281e070030810031441a5180001001541e9400001c00c0c50328000710b5198025040e5000140030a1500c0c1a010b00e540c0484400107041a441c5c1b404581101d074280c020300042400c10100b6410032940c8039052030301000c1880540006e080c4142815070701d000d50304440900442451405100209590050030303440d0006110042501115042511000c001c0c01140e40da070fa000381c004983e03410041c2c1000800381d070145c09400720501e580c03681500c41c02c0151003640c2c00074100501c0f6003a001180511400780100700c40e00f0b65190f460b010080c0c21150b070760703201c10070710380051007003140090b00100d0302a110a016902c0f2095048000740c0203080015a410503a0a00e20209020030b45a00aa0182080e41c0d402c2e000c4691580b55803840e0810080f80c0b00004066a000d1000100e80b148a9000341d908030082000d031111461075640002c805400c60311 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 206970782 1250 206969532 206969537
    0x109080d06030c0b0703020a0b060f1f120e03070f051204140109050d0b040209040309090e0a232a10020a060609051308030415151502031306110109050607 68
    0x810910070b1001c00d107800f030000d180c8010401c0c600082554082d44a161890380a0300000e040000030710281c40d00c010a1151034002881c0000e4000c8a58074018175400c0700d51403800282e003202518a8070611403044a0700b45034218015410b103010390341d9030112036918410843d454020707255001035200c000d002920280020010340c06031054108001020320f074a13640301c503200e5015041003201084004200c0303600f041c0c043e9213085c85580d4508055984070a0b075802a08c60038a02054604620b002103200b0440340e00c58442381301c041c001c41d800140480c1e09002502e0741504040d0003140d2020075070048011140d0310702c070043c1c8010796a0002a00042c26100c0c0d00026801c00b1143d00c0402805106a00141c4a401020055030410010b40251208071f48401000c0c00c1b00000400d040c0581070703007415444042c0c02d02c1402610704d500740d1715015002c0d502c54035130a442d8000359081d080740040706680360300700c0c09004185424644003040f0b800102011005d000b0395a503807241008140c040c000f00340320b002c554 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 206972032 1250 206970782 206970791
    0x9071703031b030115030902041103070e0f03010b1807090b0f030121050304090207030e090108010b01080702010b0303120c09100e031018060213090218011704170c0109080d 76
    0x1807040303001800d00c0350b07242100300d03420001440540b000200341e1004126910340064900c4181c40410000d0802400101c5a2100802040060759104400e400000000d40d5010290a1000203050a941da003003601c0d9480001040701d807912114503443c1c00e40c4910245494804196194040c840590000d07050049984d4000018041e840500c000240601c1000d41c00707485843c99525920f85034080c0e40504529146c002461005152151122441805000317088206559560000c1402813405210702c90110300c280c400100064010311500c071445001901641c40c090030740340f01001403000180b0300024030707205205801840d201c00c00201020202a11009042c5964070b04051901600c1384043c0c0314a410b1038a0710342e0200441000707180710f940c41000580c8a4002d524501a020600d41158004510100d026982d1a244130b00b40c2e0f400c82001c0e00c0d080e00302801c001001ca462081220b029002400b42603800011140c0800100890310000c00000707148810b950342c402040d4000d2440580c002e0300e5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 206973282 1250 206972032 206972041
    0xa290a0f0509060f0a0c022506020d0f2f030309010b0411072301020403050a030903030306060504290c0a200402070506071103070204090f11060f120907170303 70
    0x81d20074182c110003010028502e0345094401d0404104008110011250700c6403003940c0c04a008005003c5072814410b8069801d40c850382d03000c1d0400b80e00b403203084018401c26082c50001802581c803070b03010921a5a0700340169044503040c40c60341c0c2009250180f501e8421004610b2010b080c409903024594110020408160340000c200c1030b070b9000310340e685100030200b1044000402f030085900c0d1000040b209168002030292041e402401168000380c1503003d08039140742010750000d880401d070380c46030300d080220a03102c841c00c403042e004078000e045104204207046120145d070303100c2e000029000c05030058513040380c9a2400e82845030050044a8861004c5940b0042190030003404100220039201103042c01d20648170660742c0c0e5805040207050080704800c0e0400180d041c01182e04964001e0814006210a45003000e640044200282c50010041c05034201c00d1910104030f40440700ca803c1c0550602200c8188540307007500c00340082c5403503c210100010032030360701801e0b1012100644055503c03841c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 206974532 1250 206973282 206973311
    0x1104241d042a09052406090405180703080c19150203042a0603050a0506180907050d230706090b0d0b1903050d020c011416051518010e0a290a 62
    0x4031a4280000c04000140c401700310785501084c0c4008080485000c40c5035140d14403610502841000f00f00e80070300862502005200c441c4005160305e180d1003044940110791034070480091820150002c0095022104d4501455a180c010b1a0024040e0760300d0741c04141071022031388202404440c039080e981070480c010009250540700d00340e0305c034018070010312291800800055001171580740010302c0d401c551000c1112600104188006040c010300a580d1100281c1464085094030348003289450720304000c003408202000c1001401ca660076101c0c3d0242c1414030b00032400c0c0e50010b110402d049541c0b85a112915520340039900302c85170300c041c0e104a240b0704508102d424260303442c54403800c0d540300300f4040505991050015802074400020f00b038880d00c000158407220707031076044042c01038400c401909041a0f1441903803401001038009c02ca1217240403c0e070a0342a00c0301d04603c80ca241d04181c04441c041380394850104514a02051103102944141c1c2c03600d48152401d60b0b500c51200c0c0d41c2d141003c5441c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 206975782 1250 206974532 206974561
    0x20c0d1209060503040f060207260304120c0210110c0a030609030305131716150e0c031612030203091c021905030d03091104241d042a0905 61
    0x20b8603c0d0030780ca5444c0c0340d20b6828420305060f4004050541c0011840c0c10300020301c68030361800155448206404004400119264100b9201582e40c2603150480c84160f500950382c00c2031031035024050042020003240f00b0b4620900c40c000650140c017138034400b480e59540d944110000b4521421300054100c0301414020b084a60082c0700f02c3c04041030210900c08a00d00440603036005403e18951551034607c12460700e040010200c004000b481640c0b1802440c1900e83c00021506008004a0b10004c042604242d981e0164400300809542800300910000741c4800207001c401d4040d0041f2403a0807420340c0820350020b4080c803a00c5210416420260840c501103e09258852415070a2217a2505200000746c480c0951044003051543d901e0140040129a000000304501c00502c10490741c47e800e46240210780945406680701100c5000204d0b0380000d0b4405204811a1b401088074140d5450351248103c00c140e803215130f88030074130144241c1ca001c9a02e20b400090704081a0220f868100b0640204828 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 206977032 1250 206975782 206975789
    0x11401020c0d06090611032406032e0806010f0810091a04111f11160e0702070806010f0501030e010606020d05210106030c0224070c03020c0d1209 64
    0x54200c41d400e00c800356141a502c1c4081508480006003148035450403400414054006200b0300c1c5000c010042d5075070050101c01d80b04052501051b2050515030100000d901c0101c1c0e40180c0304030502007200000da040c645504106000c080e900d040c003074a40208030301e000d074260300202540507860310078424034905101409000310404400e2000701c110f0341e036044103000369040c11458140c83c04005000e0001d0134218101024018101d00d200341c0c1342e0009002044011103202010480e0001481c15001c400a2807004110f5030038106031043d41030016090070114090b0a840442c0b2131418003140c250b0b000d0000a00030145100b040110b00d00d04400542540d000d00544451a4903085040000580105803044001000e2500d140c0d6000c07500c541c0400440315948180c00d0850000c004252160164011009490a9000ca40014000c500d0100b03103854400c030ba190342401440301003135126000e20079685c0c099210340181e170100341c0d242000c00d0b0241c0324864240c0d40941c0c1054403021b443d40146101029 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 206978282 1250 206977032 206977037
    0x50d051e070e0a0c030f06080f0d090503030a030504030c12020a02131416030e030d0b18091209010905030a05100c030605060f160c0f080d0905030d03050907050a0e011401 75
    0x2180c82c00e400820401c000070304030000151208102241c0b10720a41c030075140154000002c025094440308941c2d681c1c07495242a0090340304044450194500800184084402c01002140f90100c024011070141c08003030000c90500500c1080078000807541000e1074945401c42d0300401074400c0d540108945421010038540c2214a0680510300c601644491540d00002260442a650320940030803002083c02d203004001c5408041180030000906402000242c5030803641514020b8214020b0302d1022001d83d032241041c1d01a920280d003d440180191203582d805040c01c0100d1941d810110f814100a5142229035803c940080365407204244030b11084060f40b45410410b031820711002c10790701e02c101d0103032642d050402b2692014400d1521010141158014512807545e983c8801d040d0141c8031034018004113008a058110b00d003486076001000326540180200b00131200310030290010440075103409841d00460031301140b207480e0740398440000c10080c0107150703256240c156456040c41420321031030704 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 206979532 1250 206978282 206978293
    0xa0b0c0a1502070f02091801060b030108010b010906020d0c08090a03060209120607091701021e04031505060d08090409060e0d020c10080402150d0908070614042a050d051e 75
    0x1182c0c90315115013100f981502c41c12110745500800c00281d480702d0426514560800d6400720703191001d10041c5040ba41080003d0205000e900019030700809180601401039004100403a021403007448a109200e0180f40a60b00d041070500c0411564600342c0c0060365441c0c0c0000f21032a2a017000b401140345103503880042d000e40c1c01c01074401491981ca0b80709038885004142c40b004989802035044662110300941c014290002001c00440950050720069881c05800310302c04a01e40154060584035010040c080c48034142d0650728215a0b81041541d160000d41d90050000000c0940c810803a460400800819012a19183c000e20708041618000d00030f00c1881103444034503400400785a0442d40c11640305d650f445400c25802c981d4019025450b002d00d04110090b414404081d000f0481c4034040d081c01d0080203440002400884420382e03000b82180b84019241c41d02a0020b0712030410300d00b44c5081c2c0e00f255640ca400107480304100b07850a0318a508004144a943d00c0500c4040d09086020360113040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 206980782 1250 206979532 206979547
    0x30712020d09050c040b03030912010213060e030706020d02030d0203070203071506050f06040503060412020a300f0207150c06090b09010b12100b041b0903050601171b0a0b0c0a1502 79
    0x3c0c1c88e4011020040c4c0220f064040c1700810b0602901038850342041c2c0084001d0850799840010845401c03003201d180030b801ba000700415803501c0400e01454102e140e2300214900254010010300a610003400802140424005007000984000502c001c0030b4211001107140b42c1400e0402c4400640c4c0c00360648038002c20001000652408100107a205410131032449000c00158800e81c10104860070090528400f0202c2c80030501161002550001d08030b8100c44007034200e40c00c103031032100d40c0d240008096804207008100741c0c4407140d50386010800500d80022045207598544084d5024601c04503001101c5108011181e80300b40304407581b84000303c0e04101500582d1004030b845101103840e0380c120742d840b030130124441d440e283c00480c01c01190100a14100012071001400a039113400b007180c15000d1580005610540d80000583d40058031001d015410381d61380c001d00381840e1028055802c040030000000c3c49100300d40203030004501410103098003215501e0302d45030b041c20842a4140b854814401c85 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 206982032 1250 206980782 206980789
    0x301180302100513140303010e0604020a1e03020d0c020c100305010302010909020309030f0406020609010c0915080a0f050712060b070b04140c150c0114010515030712020d09050c040b 80
    0x1c41e24959684000281138441500e00d6aa181300100f0140a848441c209000f16000000c01541211143c00c10811151211020041a031003220031400c00548101c44110340010a40b10305a082556424010b140c0f41c00142620241c40207100e5501c00350704841a801c04600745902e604920321001e01e410050742d0305550010300484c449018282070036a01200281c84a6820001c84021a00c0781040e203890300e0f03407484000d58629040750303030150365400c03c006541c03070790f00070907030311054543c1c08603071050a00c0340c58001c40d8400c20050a08880940300c92040041007244d102c0c6500440c452b5499100d000203505001003602e406500c003801e0f00404101e64004107041101482d005540700c44611040340b55110010310705808020034541c04455010441c034821300100080000b440c00d0002402061503a00008900031424425141c0003900191960082d1070300c50003c5038411450700708035030181d11851100041703800056404030a541c1d950910b40c01d0010420400038061001c50701800040c0350715020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 206983282 1250 206982032 206982043
    0x504020408030f160203100c1e230412030c170310050f030309040c0509030c01020307050d0c050a0b010602070e01080606150d180f03090503030f041401090905070305060301180302 79
    0xc100019101090242e044c101800d80750f480f194008040380d180a050700a0200100032412912002c0303000600210407940314001c018540480c40c3e101da064000c11444200c0f1800303240421180840e00800c00401c80c0c0c2c00904041411a0099a030b20420b038005152040e208900603401e0b42c41850203104006071001d042043c0016524151010380340c03080c0201c0428514040c41c20380075442401c2102c0042901c2d448800b600c40c00742e0803030480d00c10f40d95004c01661a48030b504800352a40d00440300281d4500c6c068082007801c2d40c89482202c41d001960b40711054118020b0f040000140c025035010810082c003101d246026083c1c40000e442e00c1d081200c0003e4005504000d29441ca4901281c511311150b056805415404171351640b020f00765105181c420356440b0000c4040700801c1401c4004116420000142d441914903032101901e810f00b80000c0c0c480a98081442d41c1c1000101900418034548034056240182c2c031944005c245030400c0c8003018203481030760301400c2840924070000b401281d80040c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 206984532 1250 206983282 206983297
    0x3050a02060d1b08071806020c06130503030304080309060f0105010203030f07110106080307021305070c110f041409061501050d0b12011103040b100506030601030216060e070807050402040803 84
    0xc6081c0e540d120844030324040c01d10640c00b0f0043c0c56010041e1103060740c020000c82d100f20982e94490341c26020051000b450b041d414069103005a1040b5211103250819400411585442e0b0302d0810815075a500001e241d83c1c81282e044913501408400c0c001c6080701042101e03080040c16003895000e46c10240000d40c4d81c040240b400c2141e90380d030404100e0050081c90111807800411000340907203900e404100e6900d44c020b20302240550368a500003078031040a48101c1e8003415a40c0d4842004800c15101d2410403041d82c20a15480000c01c01c00551650b101c0c41405561880300c0800d00d49490524002ca040800040401407003041c10b440c080780076a030140c21641d070200f4040307000655000c001c001c03c1e0b41802c814000c4a940d071909943c80301ca106035502070343c4240c0c8520500c800a51300c0c90f15802ea442100d12070180c01500900200302550302070740207090f014040c0c034600e485262089d01c1d440e0a07074901c000e1071069600001002d000c0640d044c041040a0901a6401c0d8a068682001c00303640303100b03038403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 206985782 1250 206984532 206984539
    0xa1d0613031104051501081f0609051201051027021b1902030606190e09060f012301030906090c1e090e070e0711030703020705040507030b010c020108070c0816060507080103050a02 79
    0x2000911135002a1052340080701c0c3d1000c104071803980351034028081850a00136244110f04204c1030301c0c5811014040e191042c40034000d1300340c142e498891801101440800d02c03040c0e0200d98001074050718914401780c80083d400084019452408040702805c003a610040001c3c080f000e2006e01000d6100000c4c0c59070081c4050311281030b01422031003130460b101c0c4540c0018040140140900c0164007000901a0069403855030303030030850343e83c1c9440880f9480704406140d60001c00d00c000030b103c5e60103a84240c807020300406000c22036000c1030b80c0307045200c0e07402c2e0000d0100c051540400030ba40b00c48440d400000d800454002c000e07980d010307181d4554400c0c0c1482903041e0003641500082c0194410305e4203801010030a02180e807035080d14a0f02a4a42d101c5001c0c95010340e00d00000110079511034000c28440d40700603191041c0d440d03065001143c50300300085c0740c20207005211800c40001180c0e00e0060003000901001d0301c40104040c501642550340240c4500100003c210051012031000328056244c1035048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 206987032 1250 206985782 206985797
    0x501080901110c01020a08220f1109040302162102041a090408090906011b1b0b0c0708070b1207030e1e010b0111010507050a1d0613031104051501 64
    0xa4100c20301400603414002d640711400310b441c0110707820540242900405903100c0450690340c40c40901114403203ca05810311030003440400d00480e00c0940241c54481c069801000303070b01c11080c0840e1050100751011401a403022400f000107440031016070002c3e110900410b00491b809100d0301c001c0301a01400a44241e81d1a84203210207000f10b031140d0140c41014005100500d440c2c282117000b500100c0b5654014040b15001809541c842c20b001c1e01481c03448101046c2051031a191624000b6070800d242640802009002c9110501c400240a03501d10f10802011968144045582440d00c50f0380003a017000c01c10300c60150318858018400381e1000782481d00007070004904070b042e0314000942000d118992200000c00862007819041908601005e0b00c49521405a0300503241c00c0b200f00301c500e000021001e00030314401c248106424440c0301041c01d0141d643c054000c000504030340c00b08800e9031500e01d20b54010400c20040000d201c070181c0040350704110b6440d0869801d41c540040c58a02810400d40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 206988282 1250 206987032 206987041
    0x90b22060306051801060509040b22050609030a17070f050a03110f04080d02430905100f08030301060e01031e0f0b030c241c09020f0f0901050108 64
    0x80364000001590080e5007400715040c520079007500e28600131203034a0300e5400e04c0c1c800706090400700030b0240110b60181c00f03040346655190800341c032802484065101040e4103c80100803480c00c2000038060300483c7c0c0903566450b40d01001400c005003241054116010140800c5101c40c0c02c00780c00120305100c0c1c10403d9aa03100d10070304800030000800354034523540c80410240301c0c0508420140c0300f030362071000c120307800b070840340c03800b070341e50b54000015010400e051030a465820325114005440312210208100c80c1c0804424640190300703059046801c14541c0c51040050b41c4000003504002402d03034100c00b200340e42c201540c1544070f100502541043c80344c6c545425409912070f6203c0701500c1178040900852069040d40e0002801c41d0001030009641891f51200f40c038500814000b200070360050622403a40e0042144003000c440300d41c509410301c1814007810400032000321680c419443c07035043c001044c91141c41001110110601594090700503205600c1e5640c5500000e541992000d0801380c480d90346 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 206989532 1250 206988282 206988349
    0x1701060909080d0222030c090c05030f0103020f030f0f060a0c09030308040605060607020607031206060513050f120607020706091d0601030506033301050d0201051204030c020d0803060102010501090b 87
    0x48034900003071900f202c0c1c5d5002041c8401c0201d28420740300e400009110600c2e0000c0c046a850106480144908400c1801000140b52100303012034204006000d80b402c0303840d10030b002070170001c2107450f44000d504444100401003255104004030407129052101075242036441c01051420b00601c0144550340d120041082a61240151810243c0c010311141c2e80d22001c0c6802000c850903106620b0640c2d0405c44045a5139015809490403c0c0c62540003200c8640303000100a042882d100d00ca94000c07210004000040005020706840b42c95590010071b50b141c0340400040640115500064440503440d0780d81030500b416030440da400400900c3c3c08101919014000303400d00d0340d500b07a070b1009810381580790f8018100010fa03501d505144132450601c0b1b45c0c0e0b14814000d042d500003000a0000ea81000401507001d4004201e9401900901e0404c400c0c000075800710f414107104540640e01164007004021082da424010640503000c001810303c0750752407020100d1980d0440544003100c0a002c15100f90300c085 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 206990782 1250 206989532 206989567
    0xa0503041a33090a0207030807030b0d061107140a14150a15050918070b070b1306060b0406031b0207060e1302130905011502030c120c10061701060909080d02 69
    0x140c0042141c000f80c1494800c1c0d81c025072048400310046146880000c01c128083d02c22104c0319480500f1000304181c480d65214000d100a0041d02c80e15841030241802184201d55205200c2440301c0003004940644e05205a803011842443c2000382d10000890142ca800844a260000404180828180486501001c0090b900c6e0003054015074141c1c20028003e01101860104500040030f0324140d5840303040381210751103910800340c01020908085400c20944412000b9114041c6500046054450085001950042e8000c0c0002901c0e01c100c0f042d22030481c0c0c0741c0c10354103c290000b4084103203010b10203081c5241104110b4464080c82081103c0814160101c884000d44003601080540c3c4480c1d0110083c202030003202d104201d00003032041030314000021200d100030303040c0040401d1044502b4640440c0d10481082903140510000c100410506000e64006040c0203e074010490342d812040030300311180303039201682c1103050015030004150742c07104a5000000402015030303030340e500c11090724503003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 206992032 1250 206990782 206990881
    0x60e0307050a0305091c05070311030f0d0c020a090506090c090d0605010e041704030b0c180405040c03150b0105030a0c020102070512030a0c030501180b01140a0503041a 74
    0xb40140c09003001010780c484c0040a42c160100c80120100e150000c0301c0f800d40804040003455580030740d1050000c51000341400d038907854018115000f100c0c003501010b050903d00d00e1400c002c00c028080300c400f1032400041c070700d0161641040800192070302d100010355010020342303012044200040c91041c03a890380f040051800390403440510003541d40d03e03020400c411086030183d0300048202c4402361007461039402c0f1012650490344c050100e0300d8091419549511030f035460706501c042c0169860b082c0d00c80b80a2544500d01560000070781034a942049040075070a114100c0c103483c078010841c180c07a0b8001c015a50004204500021401503c1109074028401c0d007501034090302c541c02140a68121400c0250300ca42c10920040c042d184003810140c1c02d41d0300c00e02411a1a41c1c44611086003c0c0385542f01842c2d0210500d80000401c2c600c00130242107a000340602000030f1400010001404034540e100e4518001e640510303115407908011400b080e1042d0040580c2039001e81c07008040f41d019402d146202e9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 206993282 1250 206992032 206992043
    0x6210c0d060b030f060d0309030b13170a090501030c02191109090601080c0f01090b090a09020307050a090b0f04031506240e090108061305010e010609200405060403060e0307 76
    0x3241d80382c20210b04580c01c00c540d44001c0d10018800907810341044d104005010b0b915403070746038050b13045a0b14144220801411940c0502150b1344141c081060040c13080708405240801a035900002c88006005d120f058000f1818142001c10040c40b440e4002288143d5401ca000d90301101c503130511704501903c4441a0407540b03c5503642c2800041c010116505040325054012142020200000c2c08441c0440011042c0030518031401002046c6128008200711500180810101c940b1085203000702d030401da447e03200142c00800c0601c401e40d0804130800203003008a03030641c01c100020302180d04c41e02c070f40d001c02880c0003400a01c1d020b20020b41e401c0100900f13500005030040c03401c15030803840c403140f100e030210300010030807100440300c4c0c101240c0280c1600d4840d4058440365690070000407a0004c0181d04480310f42d038600f070b00a000b000078803404000d0250424082041c03090151208080c4607400303110450140e04200c104901d0307840c40c007260210b035441000840c1c0c9035204003e40d4114010004041c14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 206994532 1250 206993282 206993291
    0xa14030307170a120e19030309150507110a0b01060c17030108010b0906040506030607050a1704050c0111030a0815060702030a06090c0f0605090f041104030309030b0606210c0d 77
    0x15902e040602400500000c1d13601ca054000c0c1c01d5220000380d50300001201d0321354201d5268807640e0701101e192003074082d010f8100072420b482640e8940f42c0340d80d41c4440080540d581d078000d10005960007010510031100c4107004010781500c5448107101e0000c1880342c0014400d10024640402c80003020000402120a640300d80365a5182c403450b0107800500d005500c200b004400180040c0b47c180b141502512012300200440c1d995100d082d1145c0d4003a031110410f100740f0440300590f80540054041c8650701c1380b00a48420b0307451200240508040f00440c01c4540c1090180045899020315003a40c020600b410601c0c00015101c0031078643d1003032050294040c01841807000c00d002031a081004044c0c414003280e4030540d6160b0040c09d20120600903840080d404004558452800320416071a0040061001031420750520800301c0c540d01035401140800e081d14020028044a030040541c020002d0740e403a80f810908000d036640da444140251500c0b1054140401c5a819034242a528880d0f0405000c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 206995782 1250 206994532 206994563
    0x80607080a05070f0806010804081b0c0306070f02060c03190e0d02070b131404151e050a030c0b0a031410050f150913020c0a080d0b0d020a14030307 65
    0xa220410031a081c403405414603000c119107620400d18401114081d5031440030b240c465200441d40c008001d48240d4280409118400a842d040c240b81c13181d40035404000c103a110014800e160400307500801e102e09000011680702012900440d1035075100c0c6581c1101c42c0c0e00d581d2008100700a46c414180307400007914040c0712100c41c2c4000513841c07402c4401034080740d41c1a951001c2e9100144580a9515140401c5174020011111841c2050320010341c000e10208401d000b01c05518001d5401c0ea01642403403041100644140c2e405c2132610010741000e0310200019801c41c0c0302c3c0c07008004240305564050500090809446100384d20403c024110800311500a0034089616507920515010702d6118800e0319030134440b2807601d1075200300c480881c008001c0c20300741d42d1010400b20502c3e203100480b8440e000c001c104155041403001c101507a20a210440c1c03030782c2d400c00c2c1080c11180c2e41140701d4014201520210b0150761002200c0c0c1c115014016855040b2258101290440c050301500070600b13110840700f40c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 206997032 1250 206995782 206995787
    0x20c0303131109090c060a0309020402072915060a0c05120405031621050708120301150e010c1401090c030b01080c1f080c041d010302090109090209011e080607 70
    0x41021405a0341d4450100500070400c80365007000c0c0c0c0d0130302031540508981d44542c20080050400102e45040002c2d8100780364011070305903407009104036100085a1000240d8540b41c8004c400910b4484049260ba4a4044140405d40178903032100c5100328408241080ca9601c516003000000f0741c000d058800030f0920340c0e01c11220342c005024982c0310340504002800c010f0340d001040812111403c052001c10281c400d0381403410700d080142961140a0781001081000c000c004050800343c0304074105a8030361426000c800900800c105460030405a500e400c10607a0784034980c015400e030440c5490f220083d2a0708181d0041a0040c4000d0140510300400001c2c00051001103040368004810307034000180d81c1c0204004038080c0200d0181905a6001006813148250710080c0d05c040310020042c58030b0780300e80d14100400088036142800c03081c03040062085040ca8501d8a00601140c401800304410301e5000501c3d03030805014a00e002140e400c110801850310356003d070001c02011040d110107040c81c2000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 206998282 1250 206997032 206997061
    0x30a121e0b1509031902030f03030112060605010c030807120612030206040209010e010806180313030501020d06050627030114040317061005190905040c03020c12031018020c0303 78
    0x8070380c414010907580a20800da96001c44056082c0107000d010040c00d220b000958100300d01409980503c11040300b080002c03020030085019200d040c0002c40c41008914162042d0b03103840c1c00480c104400001140002608035061a401194500313141303c0c0001c3c01e01010004000c40c0d0301240700c254001100500340342c2c0200318240034500a503170b124000ea80f5500d04100301c003000e1150651a0b803044c00011140c2413850003001c4110b80c40c4c8103036403810400d903003908500b212075041078400d44d44c00070301211403203e44d10407a0002d24040c0d41c00750800c02d01403c01c10b40c0c07881d4070390480e26500f803090000e101e90398203501010070031480304059001802d042c10014044040d62a501c40d03501d060300c0201b102c03032034030000c019180078007681d401d4601440f0003085c1c2800b20200c000315050004035140424555954000d00b8458841503500507216070f500c1d407040e441c0104030799610169a03020014403c08050200036501a20684400f001c40f24111020046c003e1003040062036880c040842800f04100c4051413 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 206999532 1250 206998282 206998301
    0x9020702011b050604152009031608060705070c0503070306200414010507021c1b061d0f0604181b020c0109210602040305030a0f050c030a121e 63
    0x300ca0324070544065102c1e600d09602903010300954843c2c030020300002c9242c2c020005228034030070003041c50b201d4048070b540201c99030311208808200c0850021100d04040081403d00e500703101e4040d080914221005840704d00c094110001c12400142c000e0500c04d49031050001000e0107002c50307452503540d04044000301100d1700c2c0307124003011602c1e80e1208210a4403d89041e2148101c09800345141c0d000192103652184130201d8219603005081304610000c402d121100601649290074400b0301c45002c1d0090401542122041c4040040c4a40c1d054100c074110314140c080c00e0f0794400c001c010701c1000070b41c41d002d10b030302c1a51040e0055080c2a4442e40b90f41240720140c200c01e1448100c811201000d0382c599100898490019140714410002e050300481818000683c44e62400328403102c075210601640e105400c103681c281d02c001001e85da01c590100b0f5442941c54185001410701c00101d124136180d01c0342c81a50020010390240e02d060001c1c5641c40020b4030f01500a03070050132007080b991071014241c41c52 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 207000782 1250 206999532 206999537
    0xd0905070509010b0f30040c0609060e0607170a02010c0212210406020c0a0606050a080601120605150d05010902010e15070212010f0c08040c1509140411040902070201 73
    0x10000741c14108188914161000c20051500b8660559000420340d04503071001950100212003280d030410080d400102c100c50707004150350840c42d0a003032088544030380c0d90044c010004480d40030440c00d94400b000d401c0c840401c645642c6e8504544c02c018035010008152000d012100080c1080c031290154080600c4240e160282c03101490080206c1007140607400e0702c14400991300c100c00c0e11444900c5443c6034842d1150700b0050501401d003070716914050240c00226029540c81c18144964501038864000901d4808018030703896042c0301c0d000d65094000031000340300a03180c0c1c010840300d0030305e542d90542e40c05002d8038407403200310b0a06140c2e010f414000380070b0740404e510720b440c18103c1c18480401100c18402c001c42c140b030f0140395800d100121101003c0b0b4007195585100304406560240521546800c0f2179a0343e02850409081480b00c04119511581c0d1031991055031140b190b40248070300c2c089880068205888801c460080383c09441c0005d020444403100160110720303552660301a014a5000381e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 207002032 1250 207000782 207000793
    0x10b0301150f0812090103090c0902030c211308070507082d0d0f0e040f051003020114070b070305040203030d050117010b0114030c28020a060b060901080115020a05030d0905 76
    0x3d511158443e1040c5403841031820080114901e6540250018420315118403544400d9075540c004070b03412a003042da1050801c40380022419041c55107103809510f0302c950311948011038145803250000708100c0c0000240462001f25028060280030710042004090070340546036004208900742c2104540e00c5000e02032041722002005905100242042041d11b568481201a8900d420140d078254184a1015401519000140c10350041409118010343c0032600060040d030862002421031003e00a03031128400c81801403c0104100355002c5400c001d190400040c191140d0011078194490100c994128a00300340c00060308803605001c50002c6900e00c4000c002c0c5410400c01100c1151410811000780780c010300104441c0d4440d8401019282c5030000070014508d034916503002000000c1c041c900241e00a0344a01092200030b01800751a883d08403540e5150205003000039180c4107041c001d0071202c0340120040121303103000304201000560001e00700d80e260020f4045003400351003000802c85050289 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 207003282 1250 207002032 207002039
    0x20070b0a0606020109110103020d180f1223130806100f060e0a0902030a02090d05070501030f020403021e040b060d0917030910090f121d0f06040b0c010b0301150f 71
    0x44c417900b00b41982c0035400360085c54140004401a40140704481081a07075105500c0640000390501c3c070300c25101c0c102c039680150180c00c0580601c900e248540c0188a040d980c101000f440b451041c142d13403c400e0701e81c2c2d0b4641d110240307c0c040c580003e030002c40b174a10800c2e0500443ca840040c0c2103040780e42d9816051422900c9000840d401c0c907206495541015201c0000d000c00f5005401460b031100c9010401401c103110640011460544400c0545540d08810020320003542e05000b411000452818158030340b81c40c55021628203980181426107449040c0034180303890769540c01422003803600034441da882c1d400009990000b4521a00b08541a03509089840105092641900c1c8182901c0010308520701c0e0211115000d030058010844880300d28010040014100d50303014080000c040e601e114003460034200501d407113000d0042682c442d40c0c0c3c0030101041c0d552404225010364510308920360704c424030b00315401e001d042540b13000c5a040d4204aa00c01c0380c02910305a0302c1c11610728072420010341e07a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 207004532 1250 207003282 207003287
    0xc030c14040506030f0c09060f060f19020304030c06081e0109020c010614010207030b04050c1008060108090a0c050415090c0806010f1701050904020105070c0906061d090a20070b0a0606 81
    0x104200c003e42140c2021b074081d562880e140380c2d559413040b0060900d00030110004000f50b21036002d11540035450201064007904403410007022420f10b00c0754001580b410382191250f0485c94918404c540410800c00000f660011191111201c800c60940e0301131819612158020040e40041c40000c00640c03074000c000a09007821509941c07100c0d81a000350104508640b224269408014800c0c4c1c0e0f284254101081d40e40c4584490703a10300c0c901035980f020704d400c1090005003801d40c00f42034008158840f04090001ca030210314040300f240d004580004070124023500452910303e0550018111382e1420341c4801d00c440c1c10101640c412103090b0b842400c804034094040d0b030802c190f5128154007034131301c40061085040c0b000303c040d00302d801418002d042c210075070344210b181e41c03041e00203401d010703190030b0104191900400942225080300101007022404100414044103005240c541103548803880e02000e1511100058160f840c054500d5603680d010b41024000810b0640e46190303107615041d00011a00c0c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 207005782 1250 207004532 207004543
    0x9150f150b0f041502060402150304051f110d06050f01080103050303010501140d0f0903080c1c1104030b070c02130506060313110d0311070b120406090c030c1404050603 74
    0x15000121045850a01d02801100d400000107042d114100300804101d40404003d04201024a43c0c000c0820f4506403043c410081032a2805114000c014802d01c00003550200f03a4000803260040810000d050018426000c0c081481014030003d00001e43ca40f6a1151a0040010340d0400d94003000d400725120011140c01c2e000b484050455007051006010300d620030042030345400080c0c41d590381022046280142181e1480601c080204e503100401030806400c02c510941c02210021604e00306107a11200c0420f03280c0103080034042075070301c00ba01484001032100341d40c09150006000311076031600c8400030307242075404807040c4d1082c0c01711b10002c0c0b204462800b4042c0328003c090080d13411502e40d00004140c401203101c2c112842112030329054100e4941701311042445000740d40342003011410105060800941d42c00504e03d8000401c104c641e03e110000350036070410f62107100010384080340e08180104c4403c60700000c201c050303025000540307000d9443c2920b901d503008503410469626900304141e83c84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 207007032 1250 207005782 207005801
    0x18120f021f0e1b0d0f051608010b03100b0d110316030507080c030723010c05030a0207090f02160b0705070c0e061228060e010e010510150507060f020d09150f 69
    0x101d9604e42c0381d4005004689003640003485001107a440c000c5a0f90007054804064000421981d9940d4001e20245000c00c1b0317807040d008180030b08001080191020540d0302500c101e01900040d0a203a4020036038804101e601060420007000c3d021294880c0341c440d8450034039110b40b6a90348039101c4a0101c41c94049202021600034400d000c803800d01c0d040d0b22030400405480030606200000d4030070b1001c10030500041c55081400c0d07000d8204181094280030440d0721202102208a01c18005007505400001203000318a42181e030b195441e6490040803201445807610041848100c084002160010607001e0790188204580601c11009498403003942c4580848101b0f02c81500f00da0007107804100940141d41c024020307a00802c51103800416142503550f10209102240c0d075410402c80000d9080030004040d05100000302519100d0745070007801801401c201a0005030340e038008041003d03582d0b0444148188866003400406002c0c1021141200c0301c1d4120981d890a0049121403610284a0755020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 207008282 1250 207007032 207007039
    0x10e07080601060215040b070302071b0609060804081806190e0901051f140903070e1b0a0206060418050f0604050105010f0b070809030109081b0118120f021f0e1b 71
    0x11765032a07440d0b4807504030024064005140e070801100c0007103128089006070320000c201c0b48203100341c90108010000c070242d81c412803c00002401380800280e1400460301140c0e44900c03034041030440b03c030019007240301301d600401c020013414010303071a01a0040d641c45a088001c0781c005a0340d0f80e96405010b40000c0d0130f022003107080c0e00800150032140c000c6d8421101ca09141c0342c1e0506004560700840e2812605802485511758180e042003c00c1c944078294505080a1100903400c1c007c048030040c0d50f440c4060002480703162038a10803048940c05100561645410000301c9a50740c00c19103d0b60384bc0c1205450584480d4203003030020440645010b4201c04132000086081d02e0040c0503207a050b21034100554017070f40755413566500b00104000030060b020201d00340c407030b0f808814041d4948508481d44001c0d02c00c0c0e200212a42400441e50300110810840790720f003003070602200314107000c904180d0f4034400d0349c00c204007007a07203002e01c41c1956000380c1500e4410130440b9a49041e0700c4611100c80b01003a40e081c0d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 207009532 1250 207008282 207008323
    0x412030c0509100e03030414040b0103140c07060b0402030f090c1e0609060417100c02070f030204020c0705121614060304030f030f0c0f08072a020d0203010e070806010602 75
    0x1150030440036070b003c6411285040b0307425010040000b4107590040d40312591075a01009440c51503d801d125564424409003820080802c000902c00e400b18402440c140801002007400030500a541c4c004c02c0044900820442d42c074134182d45901c0c030401d01a42c004c017042c401e000c481300c1c1030300386415210043d807a00500c02200d06420b00400010781d1002c050340790003c40a21000598803046084100c0c1c1d01c60301c038081e210701c5011091280c11035020075150300440d800340d54200891440c040c58201965010307a0007507a102100c603207480c07524410350712180e00610144c6440610040101d00d10141c100101500c034015075072000400c1c9070030700f01d40d0060b904c01c8040002c2000139020f00740e503100c0c058407410081240020341043c1002c480300101d500e40400c0c4007038116a800c40d1701c144031683c408003a05001034010462a207408008040007004081648416096004d55484e00da510b60000c0d8014020710141c1000003206031600014842c1480c1845084000315a030b0380013064020700c24500500350b10f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 207010782 1250 207009532 207009547
    0x60a060e0612030c0a0501060e2511031e04050f3f0703080702012714060c03030a020414010c050a0f0606051207061b053c01050412030c05 61
    0x907880c09660715031240391004100c0ca0501900500445c950355006070000281c2903d45141d4201210005050410710301d5144021011100e1501c040d5002100d103207080410100d042c00441c3c0b079440b50110002d00c410720580302012196503040100f0549500745c0b450112001e269040c41026403400c40700c07401081d0307038240040f090001c043c045600050381021040c02c80d8608800d4600b1b11070030350000e07034095000003180b40c29540c01c8a1a41c3c11480f00310465540c202c03043c1455060010203006d451b00d103440c004030340f14241d41c40318281d617040340454007a04c2d5a4280f1440c400002d50151013154805460030b0454030031580607542c0358811540200140160340213545c2c4240500c800e2290488000340d4520010402e9100c07610080302050f20f01c001062124100240508003c28080c0c0d190480b40309050f02c2400280302050051006c034054080d8000b00c00c0074000002c14507030410101040039560b50740c00c40050f20540005010f54000c0d094841c00301804682141511240701442001c07440421013907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 207012032 1250 207010782 207010789
    0x1404030804091a09070f1d091305011508060108070602010e070e13060204030f0309080d05120a020d0203040f030306060903031d180a02090319030f1b050106060809060a060e06 77
    0x1100304182000c3d0542038501c6000810848060718960005500d94400d4884940c00c080c4a594205495412a52489080c070008000f000002c2c00120401e645046000802500350040100c0d000516580031100381c4454125640312024031440b00f580c40390802c0042c10310f006100b80c6034042110f4000c2c1200320304000c1250044900a00b01d0f11102c9a01880c280c04541948050000340d403003107148510180d03c80c18018103e460941100c0640d40166241d10320740b507040300455a51070400c8030700b00070b00e5840e450000000e001e40c0d910b8066040c000020002004890280c07102810301c0781d10200141600c0d15022030300290300f8017008003ca43d401101903010035a00d941940881c500804c42c1c04422005001c180300428140d442c1c402c172a07000325122500d4501801007695003145207039405500c9180341c0700200040c4102d00c1d03144c140003180b5109032801d05c0a000c0c001d20a078210009200042e07645c0300c02007031040300321001714480c060140403c0c903503a03141c040c0c401210100079400c40c13291102001c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 207013282 1250 207012032 207012041
    0xc17281b050309120a0815030c0f0d020d0c0f0302031002040e310c080705010804020f0405040f0803011203090b071709030309040f020d0e061003030c020f06071101140403080409 78
    0x9115440f444c4020402805104001c0090601c0d079a102c5010f4100b06540a04ca01d5087c200144250040700001182d0340f91b240d001003007041b003180c0e10145011903001280b81c045403108058400312514402003140c140448050003242d10036800c40b010400e60a03240f601f203025900940c400e1501c41070101d1540801400c0011010b400070b5050704030000480f5210340403010420003207944040c0c0400c20030107c0c0e02800003000420080c2484402841c05a0009940b03100445803544a15501c3c4003148c14415218450207206501c02c0e00d42c0d5484d6180d000346094043d02070000c40c0010f002c000f010680c5080c01050781c2e400d41e884524140e00b17031681c880501349034108011154043c4402e11240840da9268040c4c4220300000381e20050f40c0304010044401030f0382c000c4000305c003554407030350601c851255100d901d20101c030303010310308025034002d1032002880840c0300d6101143cac03080e4007103450002d02c8005661154400f500742ca8102009040207040381c4039001e14400030300754480501080108511a411 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 207014388 1106 207013282 207013291
    0x20115060906050714030c060906041b08030714030d110408070f0605120601090b0a030c0e0102070b12090f01180b060a0510030c17281b0503 62
    0x3d0040d203d001c0000b0035540c1c44c04807030b1102d82028400d03070708080304c1002690340905041c00c0350795441400342c80a580001c264501c0d401d01e0710915081508640001000d1814010561113880101d070304140d07104c2503800b08001b09803012031b140c031922005e0b1407008030081c2c031181809681850203100b504198440345c03080c0d1080c03000fa908041514940e444421807904a56a64401220036a8030f40e03110f10541c15020518441d000d4041d040030403280e03425070311951003e2842004a9480700e940c80740707101c119020080f0320407074003110360007a0348400c44608480c0c244402d4a5081c3c2100c4440444490784a00200381c01c1c204440031740059000a01140c4000659003054005a101401c16107101300340769940d211004524011540901c0380360306480320340510724042c4100e2148040c5c144000101501c842c01410390080e02c0d10030042c0d540961550401510b107211002d8030300e03a20141 = true := by decide +kernel

theorem cover : BRFrame.Cov 206834532 207014388 := by
  have h0 := BRFrame.cov_init 206834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 206834532 ≤ n) (h2 : n < 207014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
