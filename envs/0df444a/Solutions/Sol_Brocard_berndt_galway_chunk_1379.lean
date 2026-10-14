-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1379
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:40:34.214214+00:00
-- url     : https://prove2.me/submissions/cbc6fea9-c491-4db0-b119-1ee658a52490

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 247841726 ≤ n < 248021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 247842976 1250 247841726 247841729
    0x14070305150316050d060b0a0602030c0115140f0a0b03010b090a0506030112020d03020f062401090b1c060b0f0903070801020f1207020309040c030f0c02070503060a0902190636 77
    0x211017195043d078075402c21901400c0c2c0301c0001980950405030009019400000070b051015100c070080c082e03940b0300010000710384018450740914900710180627032075180441c81207140e080010300c28202ca0380c40b1806603c0c1a0001d80200c140340c040042c0310303140303132906601c604c0c0140000c07140c5030314560602c1c880302000ba4070442c0090254071119902d908160080c0a0090340300900d408488039440c1c40c4030a441c0000da10140740d00ca900e101c000780354540d4420b8074000141c8080c100c1081c682070102c1c60140b020104103030f100e5889681c6160220301e0000c03240052000c2803062011548868141080504043c0c456000070416072040040d00c15046c061000d0300c4032124a0014494290b5403400207a0561007500e22240e40245481d030f00403111600340e170055255514040b03003000350711100758060740d9640c01405280c2c3e15902803030016440c406c05410240c0d110f403019103640742c01e403882508203040300744641004011510075100040100303030340c2c2c00096422801c0e8001149600f45500c246800803100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 247844226 1250 247842976 247842979
    0x40501110a0804030f150504030c03030c030e060601050a17040c03050c011814040915090b1b07120912030302040524030609090f030a03090b0f07090b09041407030515031605 76
    0x102c1e40e417000b0b10406810703290000c3c2c9407500c2480545458580100441d003034880c110040b0b480d008038a1100d0748a417040400307092851000303102540351180190b0f00e94000c2901342003003118a2111801145d421080103010314415012045980d0071464030501f40700c4400e080305d040005200c0c8004210403002242c008407042010f00448411009022402901e54000702902401e044074800030100990381c404d54003580211040314160701c030001884100080c4a8480c20350030f01c2440780c0703c0440e100300b1140d0032020b0103007404408681d03180f004840d000704200007500801d501040c200494100146910340700d251101c0312409651840208440302c0c000540003d004420000020380032520400c00c6a4081da405002c40e03407a0400d40d88018058441d201301115007800030000320326a01c007901141d5000388050f841e04d4003501c0c28440100c441d60401c0070700a07480741d200d400202001c0b5281c04614014051940d0105a0380b0b03260503044e800f072701140c899074000d5200c003070f2032208200d0030744012050318030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 247845476 1250 247844226 247844243
    0x10110f0c01060b07030804050601050114120a06031209030c06020a1505100f080f01060b0705060f0408070b01150206060f0a060c020103150e06090702060f010302010e06071205040501110a080403 85
    0x400d109564010540d80e00300c400c60600c0081c3c10400d06400403603052095102c2d40403200d20340c2c0ca540045030b8a4a8080c02c5c00d4125405000a01100940d03942c4540d214103154000500d5580d01c2d11000301a01c420118100810324516041c400e005100f00c030b58014000034001000074001d160380341c450045140070a45c0e085550b440100e00c9207030010326208028100d000c5803807003a540710417566455800000d05400550710705500080e0040700d203030607a0f07c0f103074000b0302821075955100c000754000100104101c03030a00f41000010001012030103843d028160f00030800300707183c10b403400203450148040c0c400340c4a81c1c02103171070340c4170f940d10402c480c010341d4514a0082101002403006a0240c10301d41e0240031005440300f070101d082c0c140b0403c100d00c43c1000701c034000845d40701c105d8242c1c0c440800340d43c0c544240302d03104010f0001d54003c400d85c403c00c4401600280c54441c540d100c1c41c41026065100c0170000700d00240800296900072581c90300205000080c1c10310248603030381d00d00948181c0c0300040442e003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 247846726 1250 247845476 247845487
    0x504050411030106090b03011a130e0a050115050a0e0906040602090409050f03030604140f0a0903142a01060609090c030912030605130b03150c041e0810110f 69
    0x2040400d00c01074074901800074401e0a4898070440050080451030b01d000798070307101035000d88101034041030711101000b43c00b0701c84d4071503c212010301400342c2e02c1d40c41059119035014000010400d10610b403026040e03d5114512030308000801103442c0c00c035404002c5000c1d1190521401802c04074120f50015801080143d443c101080070070040c202c0204041e1950144010210000701c0210055104e42d204031001c00c15400d03404401a103034602500c200380c000013030720005122450240d20500c1c2c11401b07420601944d025648201c05035030f220100541c0407001d00e190300d8541400b6429154400c0010074028081d060034800010000c2c0c802d0320034000000c2e21403090400340c80c0aa400115441d8001e29104500024041c01a015001502c1414010040c004010b81c5070030a03441541c4044900038090a603041c0310300220a40c140d000b41c5031900322002000000741800c4410b0b202e043c0c00c1102045d640c2c80c9482c040141d4144018040c40d280b6031801c244d40c0b80ea100c1c2041c002c803103101c251800c20a860340c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 247847976 1250 247846726 247846733
    0xf0c080a0c090503121206030105370e0a03030e010e0a02012f0715020118020d0312020c01060519060f08100803181f14090d050d052203050705040504 66
    0x85079283c1c04a901402001115051540030790000c142000300c084000c42d054035010b090500703e1b94100c0744008800406020940500490341d814142c0c492880318030354140005903d01400c8514902d00c070840350380095028420160103028807082c401c00c8900801c100320488034003170f0b101c0d800200000d04124600c56004c00c0d403580004480060000300040401952500c000140d950040d40910000210402c819005041c81405030101840400d1a40c59850b502c0b58248504201c072043e040f0140480680d002d00300304128070103000c08042e0000040303081443c14003440506c0c450889441e40000d40003070306029068002401d40410021454801c00b80d079209600021849a8ae40207881e0324080040c43d440c03500748041401c0d000c00c000b113541c000940090310907000740a2005541002040c640c200c40105000018054418098054a10300340b00100f583d80c1c50620200e1040c000100c0c03400320f09001c1e54044032091425901000d03000340c04090840e140c040d580c282c144910380c46140c03114002800c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 247849226 1250 247847976 247847987
    0xf040801020c0a05070e07090303050f1b01060f12051509030d062322051009020403120e030703170d020705010c0903020910061e1b080d0f0c080a0c 65
    0x41085200071034640d400140c5540e11905090030a84152003090000f2030b03042040280c0c0c0c0d000f0a010303218001301070302d140d501b607410b50803070912041e10800034041c6084e000c554003800c0080c0c065002c0002800ca0408094840c165013035000903060010800074440081c00028002e141d50a0507001e0141944d21004114518440c1c02088261141050f0002075038800740d40c41100301c9203071898500c0d030b006450002c0c49080f1124042082080003019550101c2c0c0310140e00250700704441d07a0316038151545548c2c010b4140e0748682c2c02128045500c280721400707580c0c040741407a0401c2040340174009451564994000a00740a140000d004100250b05c00000d0791981c100d85403036910130020b014064070400c0181030300b003c9201c143d004003e10000500006280c003004c9090310581d8075404208206541601150785203601140d085c4400b01c00008036029080e0500c10440e88104d14150f07841c0b0403408160140c0304181c004480490900c0114005250040007655000f030b0a40d40000705002c40420423900c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 247850476 1250 247849226 247849229
    0xc05090d0c1802031501171308160803090c030102042702040504060b0c0d020304080d0804050f06250807121a060d090b0f040203030702190803030a0902010e04050c0d020f04 76
    0x350b400980d251114034485074010754495560403011403c03040e000401503513101000e1184044a1006400140e02c0e40b8000b907110a1143c0103c21660400c0d09260169107461007101050b140038401004010385008200b05c0440d2261042d0700030741c20a460800d042000481d400c1004442092032103403903024588990651300200402401405000da440141d50241e078001079104005008240c40595010300000481d02280c01d0350300206000201d68008030f4188002800440d007600480814145c450800c004080c020300094130304154403191103041c80903421014001c502804846420403080a400c0042c400c801d00080d080402d04c007501008519028001c40842e0f0f5000c0004a454401303004540c0c04000f2083c8540803552450319621003007010200c0c116002540f56004019881c0103003048000004c1100402031407048064a070000281103400c11200514038a54843c079050656a11000080c1d005000390380421860400342c000900c2071040c90905420705400145a1002006c00c00c2201e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 247851726 1250 247850476 247850489
    0xc0d0209010b0c031c0b040c0801140616060f1d01051b070f0204050109020d06051f1809060e04030f0813030e131d0c1e040504030e0622090c05090d0c 66
    0x48281802c920b481c0c5c02007440941c0940114501030314002200c1c06684868140c46a403940c582503000c807101002129802584c00302840c00d128a21100001e00c14011011403000107007021841c01c07000d9866041e030780182080188107a0400702889521100010942c0303d2400c0c25140d10fa07100500e0401500507150114000d402034030f0103000140d28a5240e024280c08004500305003e8140c1c0c81080110301c2c482546006000302034a00114542d601460300030341c0d00b032643c0c12a90b90107030f078501c20001103e1890b4095041c44050f1320810040540c8119080040340d807600b813800240c00c0296084002051a0100400344045d5141d44e01c29503907004903511000e00080340a000a00110504414182092000d48002d02c14020180b85929000200359410006207000c4c204050919041002070800a0010340501c02a5403403481d860316044010298401160307a81c0d00811050014107100c1c00080e80a4004a4030305030080307259a41c800c0c02c0b2441d9640071240c1d61031120650030070300141c080550100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 247852976 1250 247851726 247851757
    0x114040503031b0d050c070902070f0c0833040b04081902011d01090506070e0f1c1b0b2d03010303090906050307050904060203090a0203120405030c0d0209010b0c03 72
    0x85203041c001c0700c3c01850f8940d420035138182c262642d038217841c0340c0036601d0040541e4008190502070404154003906140303001d0b81840d81001040d454404003442581c000103815045603a50714503a0003000d220906404240a00b02c0c5c1d0b80700040c0403405482000752005040801440214051154000c00e5880c00c41991540b03400c24104440040c0c02000600c441c1c002080d03202145150b000c4c010302c1440c00c2242c00602810007a82c8003041140d010b4010b80001d030f0710200d4040c002645445480c40c45141548110220b0101019401d008003645036000ca00d040c00c600c0300c0340c2482403800741401d5601420089050342260740030030b500760385032303010115642d229000b012000100303060340f0600301e400326021001c0400c18151076405260302c0d040c0c140640f6802c45d11304004600010341c0c642c01568000c901c0002e48007900709030740c002070500c03105807286040d020011600b4401e910f41441860307040708044805c0010521302d40d010035149241442002504140420103504c0c0007401e1044809004210494 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 247854226 1250 247852976 247852987
    0xc07150b0102120c0706080f09060f0a0608120306130603031202091201050f100f0605190512190b041b0e0307120b010603140601301b02010c08040f02011404050303 72
    0x20a6645d8001c4d11581000840240114001c003900d508690b014102d8800500115950320440c07002501c0040c10302c1d0311582c1d869900003aa000c00748040c0100e2036500120301ea407800d0010030840105220001042d60368680002000001c2e0000520031000c4452003001d6200c055800015000300f00300c49260640394200401c02a1798510443d4581c820035400760b0f0100900d031500b00c000c10b08800e5016000104030104802500350740d4104a4101540541c034240d458071004645440303880d84203803204c240560200100c0c246a0540e03028410500d1000d032810402c1030070700c0c0d403480c01000b05039140c007051003080f10305800b103030b1400d04c00390002d400490ba00404445141c0380080315504240300799070000c0c0c9005101c01588030f01d004494010f2105940740740c401c505441c140003201c2d80510f01500b5110b8004200002650300b0302803880500400d100d10700c016100148040e0a60340310304010010000700c00f04100020b84210741405011340c080c40c1007100c07424240020411481603401c00c541c54400440d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 247855476 1250 247854226 247854247
    0xd0819050f0403080906011409060a0801150305070918080903150906070206070905030604020103150f060903061109060f130b030f090705030c0d0b060f040c02070e0c07150b010212 79
    0x2610b030281d0700c01e07528a182e0703940c0c014403207803074180038014107a0b801c240640903141c0389007064a96420a60003030a05401641e40c80d001070840d480d5100d100a01840000c042050001c1072004600034601d065050040b090410303840542d80492080041c03102e40301140141c900d4400300301007200200302d0340700f02e00306003040c4902c5650f410040301c40b1030040c400d0350009680300c0e200300034640450b8400340003818980c903264015800b41146c1c3e0240549076081400000302c4d00c0b130b0894104010201ca440e204c1505c1d040d42060001d50700015540c1409403c20004c1d5030182d203901301140d80703c6c0c50784414643c40b001140d150340c901c01440d83c80704403a42c0c030100a006101c075014030a076008554007005c0b1042d00b5a00d0b011305448a07046410150b01091581180b000318406100c1c0c40c0d801000201a114070120060003c0c0c11a50112005001a4400482800200c00c401d0005800c404c9036000c483c10040541c1d2112108500301d1210300c2e20b41d03200c000e1212664000c000703119245001e5800079840e9450701c403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 247856726 1250 247855476 247855501
    0x13060f080618030a050d0c17070f020f0106080619060305010501170c01080f150f06071208090604380a0515041112060a0f081501050f01020d081905 65
    0x1208000e00e02802c100e94040711038000111070340c06101ea1a01402d14250050040045c0002106c03030080c454070103101c01c45000001c1c4000c2c4584010b0701c4100310400317800030091500802c2c0c1400c0d8000e0389001800c0c0101a400205554466200d565602102c0c82120300c54000d00b00580c0014165820500007240346002c2800f2503020f115031004a50078081e4040044807961000d50748403139500c942d00046101c4a1151400032a20103019210842004007103021030000c1d030141c1400e480401c3c031040c1094009620224481e00220942e00402d50780c10140c40b04030b11803c00904010740100050f161604a103006040f1149501c0d45072860b418529202809030044e00c030031203a070008240f078a1074405035464680301c4d007560881405440740c201050300300d09041030f140c00340142e980f025460b000041c152040d0403066003d00300c240c01901d4039001103840c8600b40304068105501c11402004454034a983c001050b0403410104e1504001c9500d442c54420020040c0311108440341e8280310402207480d2400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 247857976 1250 247856726 247856731
    0xf0b100b340201080601030209060906030f070215071e0912060906061203080103020f0a12030f09121a270a05190503190e09040f0c0f06050913060f0806 67
    0x1484295541c601c0c58906500c0c0060000e02041c0c3d10000300b56154401d0740641581200944903900d00f01490001440b150403c9904401a00501c1c042110143e13051000b9081003102d1031600e21319080286010b400c01604c400444486c280b015030880784244500d800a0080c5410201050140603a0615402400010006542c0b05044c45400503080d110152580090342d01075440500716401c0d40d00700402109003020241c0d2140c818480070450000181400710420311a45841030749500309030303000c0d22440c1d943d8270400c0c000304110300c1031020440c4042d0007548001044240085076680102c03d03903c02c840841042e02403561003c841c0c240c204001901681c15029004480410300c00e4201e400b14a0740b081c0d0001c103075030000c2c000e8801c0c9030807040100c41064100d081070b004071114200481d0340c0d071104450548552000309001c8090040c141d691402400c0b9640702e40e2190360030800c0140ca1441b0b4280510700039100504850748800301030388184090003a4010100f01c40d40d4420340c00307a58000030b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 247859226 1250 247857976 247858027
    0xa030f020301050106020f2113060c150212070e010201060b0a030609140403090605161719020c030303010522050a02030105011409010207053303220f0b100b 69
    0x1c0000100303140d400050f018543c181048028002d44486112a50080c110300c9140194500309001e0560110080007520000c0c140940cbd80141148080c02c01c180c60340c90310405040320310b10410154001b44c0b40745c1100c0360303c580b02c0d007001c16400040100407401000a5400441028000b007803501b12240c0c1604050125050290140071212200000241400050b20000c0c080b079040070003002036502450180920300500c84c140604010541c0352402800b500e42d51101000000155011800c0e0020904407084c001a05c01440040d1030a000f1959a10040c0945841142030302a00191003051000d020750301c120204042c003080c103180c0c038000080e4200b070145074041032909484220100406090b2400800b0503130040403814034200510240c0540c822207281c0c5448681e11401180c0b00d643c4481ca070030492140d12590b2440c141114004000c4d0402c10700200a108018440c0403503142e0480c2c5000c60340000c641d491340c3d1610490301c034062a15a0204801190108603030242148000c0c0c08400c1d00705 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 247860476 1250 247859226 247859231
    0x503130806010810150f08030a14070201120b06160605040209010b030415050c04030503071a07030b03061815010801060f0909031205040305130e0103021f0207060c02040b0a030f020301 81
    0x4a0300c0310262610424003034104207a104000720704000585802c103a208108030f85000080c5a100c030b141c100d5045c1560015503260b0700020700b401000386d01031180040c0e0401c010342c250501003e9400200b58100c01c1a20007207a07902c82c01c0102060b9929022100b100e4204400d035034800b481490118040c1401f1502607100c0e1081e907000081e0707003400ca01100e11550b80015000000c0b004501004024000680403000b080b5040c400400000e10030170007440c125008540c4000b810030f500340c1602c40d00d00b0085c80d60003010b0600c2c851030b229850009440750400101403400010704c0c401900b03d86810603009400c8041c00e64400005107840040d4400c0007034420404145207155191a0700200355140008010006031102505505503a520360015800c24440e141492804524801e103500060290f000b400025140b08010000c52405080f01c0a00e0501120704200500010501075210039252051605200c00d40c1007050456840f5400000c07446ca000701442c1e4459100d040440041c1e001c140100d00070361 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 247861726 1250 247860476 247860479
    0x7030c020a120201080406090c030b04061a060f0405040207051203180d02030f07021c06020c0309031b0901120c030209010b0a0e010c0203071502100c051306080402060a08180a050313 80
    0x810001082c1c0d040d01a11a022251143e5403000e0061407103500650305020010004000120210000c50080d801000086030305884041d0308220b0b0319a9007a210300c54001003060b10005441c0e64182c0c2c0880758219001600e4004071f0518600300b00301e242540e0a40c02001007000701d1001014040c01c0320440620132030b12000c0415409a99078404c00d169090a201c0502c04000180b0307227005480345460f2281030a0f20040140c1d6287d409030f0b0407007403503070781982c002140c20034a509041007240e146400322510310580308221800b09402e61018000c04280403404881042031041e040c0d4500011940985041619030b035900729640711303030811050304001803c81505428298401c0001c8200660010060802945840d24128005095050101c194020a48200d0a20545124410707820b0307256214565034483d041c3c19240c0e0305d1001d0f0000014000c0403030500000da1540d81c01d403074180c5600d040c010f041c2d85030000000d0204407039010f200b80c107218254a6100f00440480508811104000c401e003055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 247862976 1250 247861726 247861739
    0x3190c0302060a0216061a030a060e0c0105030f150102032b0f0b400507090b03070503011202120105040c0603150503030906162a090b2107080307030c020a 68
    0x1e200d1405000b070715070001071509020a015520a00c2c0c203070101f0742c1c89407408102c40046400d0151003003099510300d56036049210211403d00030b14030b201c0c000340303840c41c51440c0c1b45c030351045905c10140c54401e00700c002c241c2c0c500c2c099008104a4010100749848801c0c0c010021034610341543c1031524000c030181c1020124483d01ca500e018444050300024451207600c0382e10465802c112000515a2081d00c3c0a01515480e01580d20031035100c400b0128404109454070190203040fa0a140e4030040c0102001c204010145a004061700d0555540c00c08107a089521800000d44001c104613610446520305030500040029040b0801e089900070f48061040c01a060040e40e01d40e01103114554142d00b0412184405141c07110080440c04c0c1b400a6440c2203015544445040009400c14406a00150040488400000b00c2c0c100300501c0a040c083c4010401e020114145408081d9864480100e9040300d0087d42c0060000401078444c117011241c4a00481c14000c21603403034104240e0107110481e201007040d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 247864226 1250 247862976 247862981
    0x328020309030d0905010b0409060506040b0105070209010611031b06070e0f1c060204090203190e0127020301091401060f08120f250b061e012003190c0302060a 70
    0x1454418002e0b40c2882c032814020406450750810880b00703550f85485101540c1d85502c900140d087c0142e400160078900700c414403040780c40641007581480414440600103990391080c403815070780240ba20406017071030010041d246006034400d101c4007400344030190a0024001403161300c191010f07a19140e08400701c0c000d2008038095140b010b608030312510712100412a00c011200c10603441407000610b4190f5810030181240c1060f200c810011185540360200541680113810ba0380008800800c908030494904190225020720b25130051a004902181959029804804055004080c2074031001442030298000c0c403150240800f01e070580000800c20a0000410441860b0300700103841c905808920514031a4016032041407404407554007140300214614001014184a05218606800e00d0010014650341560b000718103112102801c081d2a07034880c40038444d4007410111600b50148000e1401c0c114412300d919190207103c440c192000c200c0c1e10290314025140203a090340c44540310740b02084113 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 247865476 1250 247864226 247864231
    0xc0e0103200f090a0f030803010302090f060f0f01121d070f0e1b040803180901080a0302060114040e190302070602030307050409020d090501050f061003061d0a06050603280203 77
    0x65000c41440b4802c801c1071048000c00e1001c50040c04100900d82e54030304618034104942048804040101c010011402c0c070200e81900721076820341c4248140341100206020f2092001e00c80c0c8609240380100f84564002c810b0101070401074441880910700888400440504002200300248152000020303141452180c3c00c3c1642c0780c05000d000c0279180c1c0c400044070501c801d03002488003002044002181c81e400c100501c0c91105204600307000c003060808100407008168040302c00343c0c200051040010764046403141c1542c1404804074020703010f240c0403a0003019440040501441201a40d0030040d0b40c900c1c50703410083c429421079442d04e84614007240c8a000a44240011079000c0c441440407410365000351880c440300c010b001030401e50303a0700c0d82829110705036074a4943c1304000e024804a414010747c0b0250111140c00c1c244202444d01039a4021f40b94510120602c40400070003082103101c003900002d000306001404a9183e0400d100d0b03024107201902d0f1500d00031208500030940c080228001e807031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 247866726 1250 247865476 247865531
    0x609090615040815010807050103020406020c01080406060b0c0304031707050613051203010e07140f040302150d020415020d080f04121e030c030e07030b041707060c0e0103 75
    0x20459100c400c00d00c40500580404980d10100910010501e080104444540e080d0708161091035545045503803401c00e030640c1c12560415004010070300c940b0360006903e8001150078603080250b80c0e074a06004005004c1908010711481c2c00041241684030004041e0090f40d001d46021412204074180c800b0341071041c108000e02903007140000503501c8002104e0707156018080c1c000d4030200700d9130307800030b1100703a100342c02030090108850f080c00402a800150080c10001040b4038074030384101d40d112161036000e03070312000780324080150764928013004071000c1e90310518442c40155261502c07101320070f4071018800f0980c1c3c0148280c10f0703115102403142c40c40303074001c01b00360500c0a610b0300c0e55141d80f80c0c2d031101c1840d281d090003e014881079254038104000c91240000350750000307400c4100e84000f02600ca201d41c600742554090681030000c0b90000d00205e0300f10b40d00519114440041c804107943c42d00880b440130704801e1a19034520f100e1900a8030810100784240c2c0d0411401310881c030340710030f09442c001d0340381c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 247867976 1250 247866726 247866739
    0x1b050606010c0812071e030e10090602040306020c031216080601030f02070c0602070f0e0907170a0602130302100206090d03021b031309200708090103021c06140609 72
    0x80c14a50041120007001801001d00c0c61500d0401c080340500d40c2400c2d03a4420014007101810407a0050085803e078841895150510004041010055480001003039002815650b0703039490003004010790454000319403242c004c0d521602c000e490551203812207120400044007540019402c02042c40814280001c103440300740e05611110011401484050b00041031194208101e002180c0c00c888540001d2045900070190701382024003004554238180d00413a2080189400c2c0b05a00c640410b0b402c041d91a121449d400c450441d0503401e241c42605540074144a20000301c2c022581c4400c5004000c0c2c900913036500400d816030b00022a66580d04840d08816500031901115a8520039002441140c403010f0741c0405c0c86511210643c1076601035005803041700508402005503001502540400b107009e60b1b407204001441d410b901c13802d8810284001c0880c0b400044120711603000764150307010340c000285000400c0201400322402040c50f8081c00580c842040924070452074660211110030030050144c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 247869226 1250 247867976 247867981
    0x412180f091a1c030507020d0b0a0507030c090305070b09010201020f040f06090609080d0c0804080d050c0712240213141e1809070902031914131e0204020a030c1b0506 73
    0x445e0709800c080b00c100d07030060b0208226004500c00c4150f190041c4803060001a043c1021039000e01200c000040c10828080c2c2668200003054010800404507850181005d5403240c085c40100e00900c03581c0c0140703895100114003c00e00200115022043d9201504c0f695511500c44e80300383c072000e400788039090f40740c0d0008100501c190321400c103e0b88054851000c490800303490b0541300f410003905489000c00500301041d9460980c004000e40002070100380843c092081d4070f51102e0626080001880099214407002c2d6442c410040c0d045030850003101e02c0c00410035864402468502901c400b4161151600300410030480c55103819401381c84400506811a03802d00c004401034503031004104201070700407240d0000f1000740500045100d0050155520148004195075030100c801c0c05043c2031300702c0350f000c08004003200e840c460848860740000c510b100500401c202003002058040000390002e00100340b0b40920754150304040c1805429454444409000b46d102c54407003c0d83c00400f5040e680440301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 247870476 1250 247869226 247869233
    0x51b060f0a030b1f030b011b03020a0f051504080a1106150f040b0d06050105120705031914100c0905150a0806010203070602040308070c09050412180f091a1c 69
    0x30800c1040e0140500c074000c204c05030072a61110400e2541c802003522021200899a4814403150444802056102c0407212a4800030f50f2420000c03030041000c00d143c001c2405015041003001850018054800b480785024580451560403504241c0049101131102e00a00000480e080340308103840280505881c0d069000c012040c40c003034198540041d035414281c5c50540300e0f075120b440098000c3c1c4010803a9450071041c4503400c40b514482034030a030050360040c0415903001c103512102000c2c0c4001b603480800c65040c501e80c030103140b8480d844144203000403107501004941180c180c80003203456121000b039640040c800701501135a0090808407013041016001070140d111075800c0401841240c0c104142695070310107e92040d00259007000011401302c08010581030a00013800e01c203c42031065040c165030f0b46a06844c1440c6c0801132064030121103841000d00c00004000740b03889200f54883c141d4a00e0001e009020408a000c41026815102d55250422600c0d4078110040051541000d10032900c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 247871726 1250 247870476 247870481
    0x901080708040222090614011d090309013504020103050702071d0a02130f05040b060f190201020904020a0314150102100e0c060c1c0908030706090807020d051b060f0a03 74
    0x155148544d981c40343c1e0400072135020301ca44288034005400a0920754180341359107501030110341402100000840400442c0d800120a9a0140200303007880307400d64041400070303020344040100042d00120340554064024154807042c07800389000ba01c0030407041e00d620004a07107484040c041d83d2521205490582403411982d54041c0c1c1c00f0203600340041c00d2040e0002d80a0201842c0e0703020300ba00c0307401848140a207103071a100b2079901140840b49645014680710004a140c0508140264440078001c80000610b000b0740403503103e03c400034400c659541c0522000340c01014000424281c00c0c0316840042d440c0145405203050209058000740b0905452624910280844140d003600034082c250410750651204000f8140344030ba8800505046404200c0d1401d42c90302e00000d900401a00035000c0042c15004400c4510302904a140451380c810381d42840751080c40741503002500910a00b55540a00c50003044080b2136000701e10075200c00910b070314108101401039048012a03020308202804c4614043e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 247872976 1250 247871726 247871779
    0x210c0301291b030d050a0c0801050118050a09020d0509030a05030f07020124031208010311040e03071b050a060c020f040c180305160b122a0f09010807080402 69
    0x10098500d0911240d810074008002c64944826a51000c00c030708600d821640680c5600c40e9128204201c4108000381c001d00a40041c485c0d181132049448a25244500011821019090240c0f00d503124075a0343e90000002d40c0440380c00400c1c02e162a001c240081800b008451543d0659a00d5030f0464950780000402000c000c2d0681055642e201814803000c1c2d00c070b10507454041c51003041444030354514140b0b00c04186078010503100300031160005000090302c070308820304520402e44001842080401000d45144500440a480c1c036070051400c0452290b0281d020041d01d4080c0c031840031303d5994080c2602c03244007000b40207620090000302000c1c903040c241e2003944a92124a0451252040c86843c0c0e000c41545070420355064001c03203030703040e24106090217140082c14015180b61070054501a0101ca88101509807080001600324401301000511810b040031111401341c43e0b991003554101d0720b40c55101070440c1c1e000c254035400140e8820b0013586c00324840ca402800074802101c4143c1500301880c0c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 247874226 1250 247872976 247873049
    0x20a0605130305070312030507111c0203091315060206040c0320041802040c1103040b030907050a0b09030712050c0d15020403050a020a0e1603020a05040b210c0301 72
    0x7a10360020205108109500040d40102c141e00030107591a50010142c0340c000b45a001400701200b80038016440008941c1000c900e000320038051454003480490540c0b20b4054040c0d800400880b42029101c03003a4880c08640d00100103224900c2d94031901643c0b6448102d6018017040318000d020408542080301040040030019040249030780c41d500007804445400c003180000398074900e0002c04500f002d10604110407800e0406243d15003100007090781e240310f01c0c024940d00c424080081507854170100000005420000c01c16200d0a8a07441c0042081d00110440b0344680b04140b030000b80521212140050703160420050180d189505007803005401840b5070440d040514a03401e40d03602544c0780b0180c8080c1d03101c1c1002d011600c0c524010440300203031076048041c0d200c0c00b42d8180728243c103822410442c3d0800b241000350f200c41695900b0b480c2801071b0b6000c030003800c80014519080301c502456141481c6d00600a49500d80c0310400c50940038042405542d00c0301c05101c6044c80411450045946c95042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 247875476 1250 247874226 247874257
    0x50d031101060b070b09010b0303041a0706150314010605010504261002030924090606090c070602070602042102060409020d0207080d0606140306100c020d050d020f0c010c020a0605 79
    0x990f010800388a038860130f000c0e01c46851340740a0100c940d400380a00f441002c021402541450f0601c2d226a2510014403510300310444001030003010440d481c1c00c9071035441e240540f94080e4560b2420441c101144400d9204c41951a122002c11036600501c10303a410360790350792a4402c0107070b5014070203640c1200001c0c01b90002e00c070300542d0705041d50b03403070004501c01ca5054010300304880790011890511a481003800d10840001800c00104540020b0682d174400d200703e49600c210340b5a050540c400d8400ea1001074042400042d2000a108494005100321100d403140180500300650b505030007965480d00081d440b0a080004000c00c240719005070103048031a01c001441d1100a43d0740c25920340c45145503105045c3c80359800c009068102410500000c01401084d10710b14045001030208034005150405120b0b01c442c0030b60030741d1600c2d07250502d190b41c050201c0e1002880c608000e5610080030021684910075004122465486060500c0c000c036805403860314994180032055445400c4400848014907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 247876726 1250 247875476 247875479
    0xe06010e0d0b1e01240804082b0e01060e04080319090809011d01020714030c06180910080a02040c03020d0c09170a03080a09060b0603010315060b070506160909140105100801050d03110106 82
    0x61104904c0541c2400050111809d440e4401c8080103452074a1904015a4500740e020000e040b40c4c8200e4503030141c0e00410042c5c0d00e541d40150b510f02460840c00e1950880d10307100d08002003203070f01d00c014103c09900740c845250002070801810325001d00010075500581004d60100b183c0c203a290300f660082100102610103240010f00412100d41080c01a8210020740e2070070020b1509000303c0d80c0c1d8100c0d0300705200740604c80c28900308666807941403130000d0181d41e4580391304582900c20b0f03050b184117140342c0c0b406000c1d8101880c0010b1024159026099101980f0a5122500351000a520700e80a03890388038104540d071503104601c0100001001130380c80c0780d15a07142155550718200218081c51144100403115102c00180038100c5040d6000520700c0c2c2010001000840c0c0c0000300a50b01800308010015002d10b5448200e440c0b140d941d01207507195061000780c2e035042100e42c202506175202603034032a001452050084400300c100307104854002c1c007008210f02c0804d11940c40e22406000b01c00010031000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 247877976 1250 247876726 247876747
    0x3030b0607060f0e030c1b03010f110a1101150603050414031207020f0d0504090c2a0501050a090c030b042f010f02070e06010e0d0b1e0124080408 64
    0x341d120640407200300e40c0d9103c50035490710403403180100f41c5418000860900c8021068556103000a1228404840075149100107d54007500580d4106400900a00a4003068081034001c0e401c210400c9000c10201c9180b2051128144525231103608011000c0f0301c1c040c6007071002d400524015005580d88403000d0503820501c401040100b2003104c0318185484c1602d0003850081c249001c8046000b41501301590100116a10406880a88105810008200107460010307162900c480090701d0488104d400281d60200340c65071810b0740c05004a00900c0300342c4c0ca108072030040707070f505010003854070740194400d0000c21000d0101540c03061007000c0e00c82c8034598542c40e1800c100c0184513450144d1031940d41c482d590303581c058409495506540000c0c5043e41c10103000514101008001d1410025402e03000d0009550f200811002541c00003020745090416480d2204140c1a80845100c3e0042040001540000d4030f82c504100c0c101817440041d080b14243c404460074180900180d40001061080180c0c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 247879226 1250 247877976 247877989
    0x30603020d0803010e1006020706050c10090b1e040c09020313050304081b01021c12060b12013f0f0b0906040227061002030c070b040e1506070b0403030b 67
    0x90b0190311181d80740d614080c1c44461010004090102c65a088072003000100d4000441c1d01c25280181069a2504800d004461401c010040f41c0c03e801070801ea0350070140064100c0082c043c540d900c01c402164042100f10940d5601e0641e00241481c1c400d000c10042c82940c0e41c007864000203640c407580c4510019480e020b2960b0466004501550400c5c0e1106d0742104285154141440b428005821203803015410050b80d040c14804000030710000202c0709010701070380c0e44001c01800002e130f14141c03a8101080c550911510034062381d0701600e1003043c08040d0060001e01050316100c51005080038a030342c1015034280c00017911003294400c801c4400304002803d0880c802c5e11038284800240110714040c01004078810005044500c800e8030758080c106800f1000c285254040c500f81e8100c0c2e2000b640e07500813417841c800c60f01d181c03a1901071440f003c5100400400200708840e64617103040c07100e44564140c000d0310040d200c5415030104040098100003201c21a02c50b500500900b000141c2c00c2008001c100c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 247880476 1250 247879226 247879249
    0xb10060f0c0b070201020714010515040b0f0405091c0201020904050a090503310821040503191a01060504090605010e13050a062d0801050601020c0d0c0f030303090b07031a0d020103060302 82
    0x8143d44ad4400c00105003c1c040e04952080411038050210050300000701b40240705c0b50200501130b9841d400040c01c030b15010401c51241c410f48074000a0b0404a02d60024000e420400c1301314812810320010400c03c0310365001e103030035007a0000091840c0076880001d0b501c0340305202040d041c580901403403001e660120140c80400814240014000000121740b020070115103070b0740c1d491601c560601090069480c00219101c00e078000c90201c0b4440c00301818074080d441d9081c00302c0500302d4880c02c0041500ca40c4070020704121a0034680903c186500d500040d103046003416144ca0b002007030583d01d0000001190040c94007c079480000140b09501e5560440c0500b0b408400303d00d51004544804130a1000f0750030800003401d001d00200040d04203800000c5d203c01175135990310300c50310400c42d40301d0501213000045002440c0740000c42142035a40d1402402500c1c1904c0b0076918900110b00040d4041d01038000d0b900c0e001c030940000d8805600304030801c440810010342c02d90405656607004801a100c0320005171 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 247881726 1250 247880476 247880513
    0x608073213020406020105130b0112080702030307050c01080c030c030a242315030a0203180a030206190507090303051b07030602040e0601020321071b0b10060f0c0b0702010207 77
    0x160343d035041c40d5010342520704c05420321141c140c907041440d0104000c034440703a06658600e0034074491002d80341464050350280e500d011f0761501000030b40d84100000081c00d480071f82c2c03007130b00e48403016a210410318005000450b07809030290710400008401400036030085450040c8010103070284000080c1407401c800b00340d00a880c5e14040c03101c0341c0c581d2071b5160580018074441200e0030050758410f0b140c401401c0c040a080f240c81d464000c03010403110001c005a8070a4050b8000460354000c0381030400039a00c41003a07400307a01032041c4902036220310609005e5103100b81300030741303d1152003443d565007111958840400004030311065161003500b000c00784450030045010300009070f152800c0290314807886102600c81c50655200300008030f458460400480540d2081c026005200d586056003a6410850001c41d8403210160001900802c005090f2240c0a9450314180e1072040751510400e841d4851007a07484230220349010a04000103000c410b03007a40c458442e100150503d4456903038604048061030a11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 247882976 1250 247881726 247881731
    0x303060f011b121e030b090a060501050904020702010e120601060311070209040b060103061a070203100e060c03060409060e030c0705010801050f12030d0c020307050c012309040623040608073213 85
    0xc0c2c0d001c7c070342880001e030498210070b002c0260b00d203072100180842c410703a650079024a401103210415680185101c1031500e40c0500348260100c0c880f030070552a81340074002d44010a02d0001c4010022103074000b40c03044c0c90b0b8081c001d00450703183ca403039a2191034001007400d4105500c9040101d5480c648219514160042a82c01c032748640c4148101400d05089a4025040f0703131920060080503940010840c0e0040132010b48196030340c6540001c1340145c8503400c0301415490601240c8020490008014581c000840c000d541804d516140110703a5900280301f026800800600c11103031300c0c83c000203928001034442003240d10741a035039001003080d10811400c0401680000c2480028001c2c28000e50402103000d1914051450039182c4800360724010340d90320504440c01080000130303a240c070782c03001003e003144424007070181500b000141c4142041381d12880c0900c0c24054000b5800000194170010750b202c010b101090708840207601c044807201c0145412400d1094030714010702c3c0c0c64401c0003910511503550301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 247884226 1250 247882976 247882991
    0x103030228060504321e0d0c03020c0a0b090108130206030703020a0203071a010810050f01091a03010609022113060b0a030b0901091101111513140303060f011b121e03 73
    0xc0c03c01c203a004806521010b6526580000d0341e010462958100150808c21105200d41c22300305d00d801800010381c2e410180340000410003001c11001303413241503001d03030340d200d040ea45286500305401100342000b5000324003030000c940160701036005042e4580080c8112424007116803902050103200c450412902032000006100c40c8101340000488030442510901c110701b0610800d610303040c414800c00300e0b100ea07035800081c111200b5004018201c3e034010000e04c400d039110f4a41c80b000b5440318546040b4005c03018034540c12200030902c12442540398070300100e41c0703040c5c2e900c614028000103a00d10790701114a02c03010000a241c84903080c0a02c00c04800015966000d00e040b44d0f08414940040e4140f10489402080050000a903840c00d450100000c0007e43c561680400001019400060024982b003079841c94001d400005035209110031190704002070003000054600c0350382006226407400401c0ba05101042440804c092100b90b28034065045d040c8036140355141e2804120f090002039103070b80c072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 247885476 1250 247884226 247884323
    0x30c0628060b0a03110403050703080901110d080114010309050c0906360703090b06010311090307080a0b0610080c03090c0d0b1014101202090a0308030103030228060504 74
    0x40c00105d441d0020858500b07401d544985560707a2541c44003e00600c0b0000b102c001e980d1080000750fa08060000490b0300c48041401c024103001424010855950340420030040250702c07031f00402c2d2109800001a1001d6050801071201e140e4000745901c1e00045011503003003507030b80e080c21201c808104081e9801d003030001c201c00205110101070080003c08d410007007854081001403061304d1700300380c09081c0002d00c60003c1c0004082405003071600d40d0303d400781810001b40c405000c1543c03198180b00300b020508a555101c00c1080300740002c82c01c6400114401c3c001820721180704002c5801c208414103e0b40d0040100c1d001825518003100111100c200080510907021440c61a884c00f5009009142c0b50400e01c040c0800c8040007110405010404001085008140130f42e040341e000c0c04019103064012602e90078400e86591080c4011801842041c0685c400081210001103404144c804240c4864029403901c80180001400985425200021660004031600117100b0b1002d040c1c0d040e80d20f040940710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 247886726 1250 247885476 247885481
    0xa0b010e0108070b0906030a1410180c0203191407060605040f0c020309060a0903080a02210f09040515040e0c01030e03031501080408070501060e0117030c0628060b0a03 74
    0x340100c10643c002c0c0403d0044040a60070380b6200d40080c2c411079101e6444400d0600a0701e00203020302c030000c840700c0030300c480c43c0c072080e80d408240e03904040440c1c5402d00f040903020031104071070000d60060304280300c1d101408038802d6102500d071001e480c1520703104003000c04020300c2d0351020104485090395008108940e0515000782c071105a203201c41000103928121000c0c2d1240300f540c0c04c1d0f03485218006130141e444d80c01060311001468101d5035040d1140001c1074040e5540888013001900e1356200654a280c0e8034200044944200c3d02000340b6060a00306011f008c0900f000ac2d140c0d039180d403440060b2000c103460383d01c252100c1e690310700020000f00c0100d4001404989031010051140c0d041001001105104042ca800b4403520030b2803c45425516401d20b92554014400002e005508011001480300070a170000c9040e10701e103400703204000e004001650303501d00c47c04951284035000000080c506402000d4035100480901603800c02003000b20807500e04980e441e80140d25010800301c0d18885e1241e052 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 247887976 1250 247886726 247886729
    0x1022205030c0a0315020f0d0b01170411062b09020108090c09040b10031406100f0303080403141308060906060604260c040501120302060c21060409050a0b010e01 71
    0xd4018104180d184030206284030560300015040c0c4071045246101e17810307541d04030364268100300742c1c49403078040402c42040a4030300c400840b800209036110405003103010110076400780350710840703614140c00f06105121490700250000e52401c0400000e55030241c640000c609081708a1150016980300d003803002401e00d120141111100d60b00100314540d803500c0d00110950410382008640340540d50724407071800080c05070380004248075011000e007a04400001202801450801c039540c699030744500b10300c400d950762440060006034542c00440c0100e4004c00e201804100e940f10703400d14045001606248401c0c541d407200c490395104030104003280b103007405420f4010a089402c24a45443d000c8180f02c0440c504401c14010400300c1d403c1c007a0104204802041c20310003501c180483c0d03946000130101c1c600070f940c090b4054040e007000940b6902c036010880342440900c9030801413210085200c500b00e554010310b1142c00c0b0382da4403000c0000c00c070204009180c2a128014000c140d60412642802303cac40c06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 247889226 1250 247887976 247887979
    0xe09030904050c16020d080d02040b04030b0a0c050702060706150b070b1303210605040f0b0f04050f1303020c0306041113140a0b04020912011a06090d020d02011101022205 75
    0x14000704c2a42108040b010208940454800240140a040400d02032051444c450880c1c1c2c40090005011032102c00600101c274012803814074507654000b01c0e00c0c00e0310a240201c40014908011080051900e480548481400b42100003070f14071134561ba400d100301d902d420400e190704000c5159801c1200c905842c99100c0c2a4020a6030303250060750340600035081040d806030070350810741c859400480213644204001d090080060055070308201c002c0e0010442807007261b00400178154100c1c800d04240c01101d01801452404280d984d849060034424090280000c504500404a08000c691340400010f07000f1802203885403d1442070504000340090341800f6442c0c002d0a00a592920b1050f0580c800d602c02107050000c0b607080d6100300041d000740300b0f0045640c0c0c0020080c110911440055205c4482d407003031522400c110341650810003005000c1c0080c85a405801004810018100516a00110391041c1044208000c03094003103803c0ea080050030000b928021a5000c0700c0714002561140200380 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 247890476 1250 247889226 247889251
    0x6380102070e0730020901080a050f04060c031d0c030d180e06130c0314070c0203070513090c0e090c01050322080f0d02091302040b030711070e0903090405 68
    0xd003010450003184014548021300c82000d0040d40841074903440303141441462805a41100c440b00041d400035040469560f0002c1c1210b0300003004086240f14481c0a03042c100e98441c0c8550325a5502d030050486ea1140324101034480582c0f003003084101c2e1084441401407c040c1c5601040c2100b41441c3c0120601900200000300c0c8101c1110484105148240c92a8000c10004d540e150f03000700750040f000c804c081442500d081d410a8109505a0000458042e16030400c01240c13106c84040314060a0242d01940c15000b00c4010005450a0000b01200001c00403001c64443d607103480c1c440340c0d0740322a4001e264441610040010613a8140524400c03031100b400c14a003103040000884038020001244240e0f1842498031103805d01140c0f2003601c0c041c141d6080815911552107503d04041e400141c0140d01500c000030710b200504e00d20303000740c0301513070a02282d140c11f61390360481c1200c0345c1c9100e4004036824003942e84041400d210b80070700c2d01e00c180c00b0707000110340e01c0740e084040c003085550040c101c400c80803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 247891726 1250 247890476 247890479
    0x120201050f0a02090a0302100807031d0d0309151b0206060904230f01060618090917160507030303090b13050d050a0203040905010608090d0504080307020108040638010207 75
    0xa040c030301c1c9a070300202c0c200340060301c84004002040c00724019420295100d100e04134070038641a4002c005900c07502060b5810b205a6400d501c0f08120582c00702c10611040d045184ca03104114401e038894003900f4010340c3e1400c0c507258100c82034400c4503210441c1410911841043c2200c080d01084110340202042d0703682c1115141c6a122103861100403d090420b00801c2843c040d0110020400c00f807042c524940208441a540c210181110140c1908011a02c0c0c2c507180015054040b4400d8059094200d52020340081c002d205c3d00350141d01440c1a141070b01714441c1c0c1301010480030019031000d94841e4031700061441043c1000c0704403002c0107066001245a1400100007e040400d80404100c41c0d401e195480c1c1003e007101741d04500807a0003290b01249454000510780d6880120540030300c03c0d440544281d140817180c105c03440d104600071001c1a034000c00a610040d40b1507460760341d11a018000c000741250307175020030324850355620340c24465011406c490607295121640080c03144c107109000801165 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 247892976 1250 247891726 247891741
    0x210a0c1d06040b030a0f15140a051018090e010c030f0203130215071a0f0708090304050d230c01030e0a0b1305010b0a080307030314010602060a09060e030a08010312020105 75
    0xa00c80c43c000e40401c0500880460404203640c2c100d406032200114042c481d40f81009410340c2c6c24a024482c01907600d4119034a1030460401030051001e03554050402090180301c000c0664092011413a0750121140484002400003458803802ca119000440042010301c04080c0083c15101c10800094400388108244042807030241c84061400d80d069a005110030324070703859110b4602884a0152800c032205001050001d01420b5061142c0c00044005256444403001190083c004030b401c0e01c0d15500420041c407040c0740180f13112407800d00c00c1d202e07140801440c8424032101040414035072001d51084000e050780d980c240c02055600782c0078100a240c029406c0d1156840103202510583d40c01c0c00b8103040c00103228080d048402620405420380c400310f5a160007159981e4444030007680000d03d424004c1751180e4840000c81d040758819402400039403101642031000700005d04003140c44075074600316222824030602c040c003e03811854450b1030307281d891070810701032550181e0030380d5046915160412009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 247894226 1250 247892976 247892989
    0x1020a0e0103052202130e0c03070602010b0a14030a121707021c031109093112110a0506010b1b0703051914010f0f0e0105060f06210a0c1d 61
    0x7614400c0ca06600e12004c50021480d0300c0781550525650303c0c02d018401a40000004100c81c03050401e404880c0d8141d904d490072404c991b21a03010b154404441c0300c0400601d07050448000f241d1100805407152100386685080329800c11644000c0850020303044c00340c0310019040119030044c05030010740003009200d20082940e4120b01c1c0510285540c489198842442e0001990f21441e4041c10010850a0040f040d80390740d1000700036000d1302200d151000c2c0000310026600c0b05540d900048440400c0e40d04bc0713040c0d0300805900c1440580344a03032002c900200d002081f1113030081038914802961001d680b208104c5419816450408940c01881c00b00b00141c00000c80211100e404545241e8040441c0741141c68500400c425401641c02d00000e83c0c800001503101c4800c4004c440020003059070259513241c243c9800302ea10540c8070346841400080c5003020801000c08058030800ca00003102c001020040c40c02058420b181000d580b61814207545811010403000150024001480e0700c42c0d09000550 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 247895476 1250 247894226 247894261
    0x2406030a0603051c140d090206131505070b0103030e040902090709050f01030509330412110a0b040308220b0a20040308090f060724020406020a0809010e030f01020a0e010305 76
    0x35038000010003110184047d031002549580c01001c4541c1c0d01c1c1c40041d245448804d0b8001c1fa08440040f0b0922a84540600215020140d12403070100680c1c0c0707503272015030b1007000301120351360002d40342d00200700182d598001c441d2282c41a81c4841022500f02418400326a05200d0301a042c14904014045466000542e203004100c07000c204d400215280c60503000d0340009000502000711149080c0070401400e009180c41401d1a03940300a10280005481c030b640d401000d1004c2c1a407406200400c002c0381c410000f075940010001140b4080c030341400c98420700900c07140002e40d0a409240203222207860240902c404413078006c44120148000742c011004e40340310398400100411000200c28105803212501d8480b905070042c0000d80302c29070317402c102c4c2e5440a11110b010b1050004a19140348085c00c1c0709913020b82d00f480e0700a1011602d20f039100c03082a4000a0407a050140822104241b643c08002c4848802521000580c8521450384040d0002a80ba10400c1c107050900081018000d1030954400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 247896726 1250 247895476 247895507
    0x405161101021c1a030d020d12020f16080915030915010e0c07060f0e0a0204060509070c0312022b0b0102010c0e0415150306080609070308032406030a0603051c 70
    0x1e400e0f00d034007401c24130a40c90100c1c10b90140641c411042419802084903c540c215070340f07404208903200c400c46001c0f032180c00030002c0302c0d940c207001640c0d981c02d01011b0301c800c0c948148030183c500a081d5000400c0b45420358070350004614000704101c280b00b000d01c0040c061545100c8903401c5941480d0000311150001031200b410700341d0115001050183c2030b040f10790081c4003008d00300840c101001195440d11b0041005900580c10280001603a0030020151071046c003581d6111084250305580481e0121052050f0948a075024480c0700600c0c5500b1352110044000302c0c5e801c40000900c00302d40d030183c41d400d44c082070540e407604006400d41c1d40c00401c001c14108084400140042c03003003480c40300e113440701d80210001c002d62415000300207405501010a8813a403100311022070b0758802e002e80c1d80d1502070000416400342840800d00c841501002c15501d500480e00615140b203044000c22043d0704129000c0ea8001c2e00c90104100b400010b100c5980c840c0d0031140251802c06416501030b01c2c0e0360b00c1102c40e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 247897976 1250 247896726 247896731
    0xb0a091a21061803160606050108360309041103040308010803120403050a020f150105031b0a0501030c050408150a0c030506030a031206080601030b09010c080915070309020405161101021c 82
    0x40f80e0040050040311200441c6681daaaa403080c9400c15070018103150140c03502013401d0f5004191b00d02c1021090495000d1404500da04603074003442001c4001084540c400300e144000d1005810a6440c0d000d0311b00380c40c0208041989914003404d00600500c81030740254000d030030400108080703140098807598090b406040c0165900d141c002c4c1203241c66024000840c2d14040d01c00d8040c09801c000200d1812100110b0407201c1070b03440c0740000d080000020799100c0d44003d02c103008110030350180c7c01c91001403440d400c056003802c0c1d403110f0311410035040c080d400e100c984c8030bc0104a080c1041d88251161100315180800803441c040300800e5075645204005810b201600c4907040344c9981a4001030098200142501c4455a492408811b108000c2d40d462155500300100041c04a1107603007100e100e046000024622200c0c0204040c2c1c100001810000c20952160390143c00340c1c4490283d6070240000c44a0401d1640c0f542100610f5001008585101c5900402c060081c9111040b50394160f0388091000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 247899226 1250 247897976 247898011
    0x10504030b060603152d060424020307050d020c040f0b03030307030f020408010c1d1203040b030712050916060206100b0904180c1409010e010303030b0a091a2106 71
    0x43c004c110b80080801c0d40401543da15050f140185a820351b20080d964054100e88030a600c100002e60066010b0003044002c001601c1030071610b5880741d05090201d41c01500d2a003084c0351120b500f441c0140c000c48016903c16034000455042600c1060301c8542115420040d1608030702c002a00c0e844041e103402c08240d120b0702600e60314903182d4126401814240000c2245590594010f4952111422007a04a89810382401200d007084410074810754000b4000e0340c40c0c10706101a69560f50406030250781000311a01481034442c0c980c0c800e8500941030034000348101070f4a020310444000f01500600e007103402c01814455025103000012040d1442e80c0042d0b41c907030740000c01040003010180c04140c2c030903115404800074000794010b038405403440c0488140360401c00c3c02c140521943c0038820400c03442c170b4050042000c40d22940c86030814410080483e0280c90380c0f0761040041d10401c80b1800c0618005685540c05072400314548081401090490205804042c48284d103078040205603505c003041400300d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 247900476 1250 247899226 247899241
    0x30601050703110d1d100822021c150606092309010609030b0106050405060d020d0b030627120d0b06040b0f0a09090e1c020a021503070e010504030b060603 68
    0x204410034400c3d9808640c5103510f0124020f21000c29200c1e0704c621190714200241d601d082c01d6010740a10358803916104040c1e280ca114002a81802c4182e030140b4000840d035600040c0c0e15016186040c0416500250fa0046282813071903028032400d941e08200c41c905202001400d1b001280f070b10455410941a03c03040c483c0114950600c0c004030038095010b4114000030410381c0e085481d060691f030045a400e25180c1c0c8580003601d09204031b0080f1507102d5800c0c480324502561701c1d0003c15240b5481000825172110600100745005001c2e500c03120320042e070f4030010f0a01808140d5803d1256481b030003c00f215072841102503071034800c820448034410f0315081800c5d15902d070041240e0041c6000c40c40d0580d5500e01c1054000c998000c00711810001340b085c44001050b803500c0c02418403416103c0094425950b5440c41c1c600d9107460001c1c1030080d030144c581d2820269680010301700c120780140c603074240d603490318040c0140070501242d08107061041c14013040c400324150004c91a40440240d0f105656a102c021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 247901726 1250 247900476 247900487
    0x2010e060c030d020301090b010f0c0b15041406040e01092303120108010905010b0d0209150109080f0604050f150403050f1606090203010b040b060d0203060d06230108030f030601050703 81
    0x40044a110001c2d60796640c0c0c8840c4d004504035612400c040203945085001119415035420081c0000742c005515800452801210503070811041080e0004c0c141e02c41012600f0f98540140040c4003a00c4182008801c0c145030040304500c3c000003008008221050f51802d032110020200f065031b40008101d8101c0c00c140030070844090310120301c074440981d17a49a10042c040c080003801120154240103411016003821444003180300d900802614060b50b0b1446118417480c00c0ea598141000701d418030010741b10a05101c03010080c0c1e040c002910042c90203081040c03070803020005c4903115600040c50a00c04503803121002d60030540c103117004c960b81c0b1401c0440041d58018448141240e00c480140d0004206003540030300d1900f0300c02c0d4000e2220b040c10204203c1150065413500790405c03002c1151001800d601d41c011640540011f00031500c4c0600c94503040c08892501c0c0e000d00c1440e4845000000540b6000707402801800c0e000010b51400c6072940d800b049900000e0401814840c01040700b80805020301d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 247902976 1250 247901726 247901737
    0x31a030a05060717060a0302040e120301060c05070803030c03070f02070b04090606121b0c0314070b040b010e0702030403030f0224010f0501050915030403140703030515100c02010e06 80
    0xa048809990301414400d44a41c0e041d0703680d00100c0d8280034401c25801908a0583c40342500500c0c0d201c403030780756800b0711000e0300d04a4000503031405640d09058140780b1400c0a18003030300159503503610b0300341d21349031503481c09000e40c10000c0c896100f40100072402c046a03048a07030003402c52400e209120380c0281e081c1c0c5040016000240c01e0000402c020803941d80300c0e80301e042116a1b0b170f41e1322540c1058582d808402c0b14420074510500100c008003640310a40034188403000c10740b00349400b458042c5d0865012041e0340001e041204c100314514140300610580503441c42c05800d00c0300940b102d5040583d80070b0760b40d01c200c0c030006052109401407002114000d1020142a5070400a11540040c480d908054001000d01981d011101c41c1103010413954810000e0307504000c0b0180107440d40001d091404141900010000c80030040024888046e1150b0b402c00307080340511a171404a09420300581501c100301c501a44076014082515a901690794400e400040068080c04c00d88122107800740815104e1284 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 247904226 1250 247902976 247902979
    0xc1a0c010219030c0e0f1e04180b09060f01030f0303140709090c0c0c0b18100503040203101107110f040e070f0603020c0d260901051503010b0d03031a 66
    0x4030360100300b500e4001404090201c2c65408204070004010103690b40408130654075040b000384c00c8003045600305840319075090084080941020351400c000242071314005454504c00e42012080303d81080341e001d68054101841a014000504d40f9207000807203500144000791038031610085a501303050007035004002d8000c3c02c6c0d4005078203140900b000b5046400c0c0c5e104800d0348031b2600d0b4032104854070503c243c030059540b09900d100382525020b05054581c0081e010340010100c44440c0500302e40d140c0b052803408c3c40807078540d40d4407841d11340101400d101d1307403481038607c5038103040501c006201c00400b2107050960103015543c0100d80040400c481005407030700942c0003071410b081650070f1000068107a0454102201404d42c040d02c03408224203038001c2000303c001076440002d48180e000c0c05862903818404001e90020301c282c041c180000107045042c0e07900c0040780d540d601400808480c0c40c5441030070b40f9013035009101c821800c0d0041000f4003480f400180070180c0c4e03490013001040703000c1c901d80b5030381e0310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 247905476 1250 247904226 247904231
    0x22a0f04020a03020730051b070611070e041707030c06051e0c09030303010509090c06031519031101050d060e0106030506030f0c0a0501050c0102070c0b090f010306030c1a0c01 77
    0x2d20001c041c0081d07009060a44800044004411b000c00c10100d040d840143e03820f4802c80d90041d0301c44140e8040c0c101403000a40c41454024815421400300b03e070707200500403584e40d4101001d0b544000c030704144280e00700c1c10f0418009010480420345241c40b104241038103045681d5105103604045414144181c0000c0c451420706092140c1d911645954002030010b05809000d5030b201c0c5a0b40e0040343c818040c5013900b40e0000c1c001004986401042580c0c0080c12134203a44070010841d0000e00154022244a8407401c00300c290804a401c0c5610b00f544005c907030941a8006a00715110b44a034400c0f042d4000d4104200080c20f2038100e415900500700410381003003a2183c5d540c503004050b02825045881c0c2d40030f80300308000c000d06a00002011790b0003440c080c00302e02c2220300b481c004482c030707a121095a07907646d0b40802c641070008240141080040080e0b00c1500d8035240d140e0100300140713001d42e2143d4105818046c0601c042102040d12100312210100d4800410000146000843c062180117030001d52 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 247906726 1250 247905476 247905487
    0x6060912081b070f050306100905100e090319020303060d0b0712090507060e0621070c08030907031403250606050d03091a0a0c030c0203102a022a0f0402 67
    0x140000343d0074140c03071300c62903c2e264540e2290203040c2d40d1041106e100d000103007200000c0080c0304003070f0f20498100c00500c3c221080562244d950403214034082d04c1703d40b1681d200003280c503c101c1542d0164462031041e031010b0f42c6075040c0180021000c0e044170070040c5c03880c41a8400710741103074040d2204402e203094080d028170520f001428155214405440340c40e005c940004100e454034034100c0300300c8012a41810500720070705039602e40301703141c1d1a00400c0701091107091501c020206229102552241e030014005040031400c51410307003081c0e848210006110307401070100e280b0440100100604031000d010040001e44180c0c00d0440c040c12843d407055400c030031054406002c0c0b5501404072029200f00c0340702801c0a01c200c14003005584a060030600002d0400301d106800280700b02d104581c040d00090481c6d120350441c10411007140c0d5070400fa024031003102d5290044041c0d4150070b900c00d00b48240041d040d00c50060090700b060b0075070002c030507078000400b0002d034110b50f030b030340e0001e40f14200064000c64584 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 247907976 1250 247906726 247906777
    0x601020f0f0109111903060f09080309060613020f04030b06030a06021909121a0a1413210207060c06090501060b03150409030e01031517011409010606091208 69
    0x1c20110105440e15402010070100c035051030072031000418503021420b405c007491030702c0c2d000051013500005c03002c060302c030969000070450390005103009400710809041141400f00400c510141071841840091380103012080380003180600740c40441c1e0b00304011240c95540c03000040d080c01040003000b04144c1c400300b81c0c1c0c1d0311203c0e01c0180c046599010384828040ea5103c03101e210a5110251008107d020031151580c1e5080181c0d60300c40c4c20600360500411b00c03c07040d0705100040741c011685445548840321012003809080340380c828610500d02040504060310940003500da04035400380400340122000d1840c00c20000f5489481e08a4001d80204003031a203c601261540e8425100040c501010b11444521403034140700e2100d815516072507612114998000540191032850381070048006e00c01d0000032800d400240490800c0f4480c400010055044004c0301140358000d012003096a00d4210700384040350300003a041059504192404810f00500e107400c038243c0c802c031000380340c0100d034002001a5a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 247909226 1250 247907976 247907981
    0x50402010e2403130c0e040f11010c3503100e0403020f071d091b010e0604031502030601080f011503151205160603020a1416050a03050702030606090f0a050601020f0f01 74
    0x12512891080d5217083d914206a995408152405450300a0b6404560001045a9025a2079101c181047d5030700c80b03207c0e100d4408070040f80941081212092172400301c803a2601314401d908003850341d8001d0940c10714180c00100c0307940343c3c051125440985808942494000c01200f07483c01202030031290460f0301c540041c048041c100745001d060001080100d00c006401040c14031149014944030000700030848011100380147c06c82d800d0f04a5003c01c404400301e080301d880d505a007140e2000240e6a400d0000c0014010400284005001c410080040c4400940180b1403454014a071601041c4036090203810784510003194420803d14000c0f152420412030082988010b240b0300140c940e0145545207802e4043e4070401c00c5107400500da24500c60b58030040d500103010400075070b4204d00640c1b1030750781c1c2c6c503898403a01c41c9068000c11004240101180340400c0072503400b01055030382031114100000715846140c00070b088841002c1d01d800000303c059208018041c0c401c000e01c3d08551001c2d0401040320b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 247910476 1250 247909226 247909261
    0x213020712080702030a031505040c05030114060703080106030c03111206010206060906030a081c0608030c010c1b030507050a050d0c0302060f061008040309270f050402010e2403 78
    0x1a203841c1c00d51910141409480d4261140d00c507500a14134141940000728020606010030440030f01002e00c002c1102d89072441240440303084c0f0303228640c0da5410250981980c400d1015100e119160402c8410700080d400030032141144d82604000c40c4602c80070a00780c02914044085109c1d100e030100340c03005036090b00741c18a0300409003a0207580250f1502c8081c001c03116070031201c1d103800d544440e14a20005070850003c02c1104600491209191070905072401501c0d05580081c2180c1d0000c41c41e080150002c5c0301f40e044a41e40b6080c1080c0b0503190118200d80360001d182d0190a02c1004100007081c42824040a604564010151020000000d1010348485d414040a50042c4240300000d0442e1031715184031401008014100000411008030803a51500700410840c00c00c06460030001e2a00000b0b4044620203100b070501000340107041c1520740450307a00020a0105604040a2001603604a0b0011030703843c03010f0311350b401e500b6200986040c2140300e02c04d10340e240490010801540418102e108030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 247911726 1250 247910476 247910483
    0xa12050a021906050726011a090316080d09080c010c08120f1b03091b030a050105041a091f11070209010e060f0d05030a0c031e0207080c0d0f0f0c0302130207 69
    0x50240a2840750000c0810400c5030043d031909071b0001807002203036030803c031300c165400c1041d4146040d443c080840c0c01c10042621840300b90000403024090000d042c8004942400185451820a450070901c0c82d552401c0d90720701d038103200c2408003072424840d6480843e000d20480390343d250080d0810390130052000108507540c2c44c6030958050007000380c20682c3d0890b40901012401070181c01100c1004a040240c5c030545103915228440d00000043c600380101c80c0f25a01800301400b0ba102da80c08010198131000300b402c17135941c00902003420440c003403012800c65000700940010300d200244060076164030136101c01a5103d80001d0002a0a11b807003440c03540b181030305444007010844408280010340c03000b20802800c1b6042801241040c031f1142d000b2059890192400410300342402c2803a1401260684070000141c001e101c00f485220420040b28110600030b0703a0165404203991602c140d540d40f15100103042c1842008003409205014660601440c2c000f042482015245410600294003000d0100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 247912976 1250 247911726 247911737
    0xf03030103170906030f1801020708181815040c0e01440402030106151209020a120b04020906120c1509040c02100e071d0a110c010204170a12050a0219060507 69
    0x1001f81100600a59070301c1584541074905003080c030009072100c40805140c694021001800b8070704500d610702c4480d07002c1c4d4000340c00d04542c3d50030301d010321083e10b8203d48401d0600c0301c0b03d43c1b0b4070850790307021144017180c5200081c4001d641d14102c2942c40048114004041c14402c0410214662241c4e0302c5554012403082340200400d5544002008070382028424440c04a081811003681e04611b58118031039407072004103044215a12096000c00816400c00280d5030000301c01c2c01c01045090111324140c02840441304071107100707100401d05a503121200003ca0003981201e410940541014007580d140346c000400c10710925400c4a4003d43d21214941d01803802420200110020380c80401c400080c4c415028481502020905102040c0c0201900c651405070b52040110b60018907007018029a00181001595407480c19001d40842c0500d41014005600707c0507002c1c0018098003404401c919150a0040d110581408268100368140c5070804400c803c0c0ca18900401041d9444184502e25030f03180c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 247914226 1250 247912976 247913011
    0xe011506170106080c031f0308030a0e0a1502070305040906080313150207050f0f13020301050a0603020c281401090614451b030f03030103170906030f 66
    0x2000d074208020b104602c04100003801190203800702500856009046200020b580ca1002c1c00c1ea4146940651003a60307010004020f004d41c0151500510b4240440080107015507a102e0b20745030350301c6c010261b041540070340c000303068400c042c001d1042d2402042d00c0b420410502c0d030384503811501e0794090b44901104113101c1c040440c0441c0856062000c0c41000e034010031030b050502041c80003510001d844580d014442001c840f00a5640200b018002c4901d044096140e51628080c000100400d13040340040c18010f009a5400302400507a4600c07484000800076503843e0b03e0095400c0300d48141802904182c0f614034080500941504141ea03400d2058104011052001205000021054680c103030340e0a1808031004071202c66124030078200010812120180800035012071054401402d1418140c00c4064081080138005c8415191488141c000e0862a5202d0303641c0350702c91005001c01010448104456400584e405065401503840641103c2d500e051000b60500201011120b1110442c0310110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 247915476 1250 247914226 247914257
    0xa050607170403080606040b0d06031110020a0b1b0408032503020309041d0f0f0607030501030206070807030c1410150501090e06040e0a0b100b03010e01060c060e011506 74
    0x344100c1c0d60510821280603519280d508458010b070103030180364001000d120100ea210007000c0201071604d0300c0740780040c0c0f2925528015681c50505141d4902c145112000031005d960080fa0000103140d1000801c1d4455503002c200070003203c6503d050b00c011301000306000c944500000024550014030790302c205071401c00313014503062080032508014016007041c03001005905040d003203480c005101e24103009080300c405000b640343c0301e510300400083c3c0d4007942010711002014044160410400e28060040d0b60558010a03030511503050000e1400c2c0000030845c0505108408101e402c50340842020301c061000850030755950f5404e10114403440c03500100c002d00c0141b560900c130407202c0684038a00081d103442174144140300002d00d220342260719241d03540746d034090070300c503e244440c455142140581440e4180002e800c50581012250510802c014018181010f50007811207450f440d101d040301002c0d02e055000b4000380e0449840f25800c0c265034032458400001c52409803a00e071383d01c3c180203503901c08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 247916726 1250 247915476 247915487
    0xf090b010f0f090b011707030603050d0f0311030c09010c060204050405070c020907020a050d050915031806010e060d200a031110081003022e020c100309020f04050a0603060e0a050607 80
    0x104130728041002e5110701d01c1c0030401006083d910400780d080c0010b4081e0b490b100d050900c140300c0980c1d000101010801001980c1600c22110301c201010b00213425032500950408080c4a8a000b05043c00035074010281048003640480c0d0140c10003420038465420305090207004c2c5d40f818682203104080c000b001500b22031001a0614045801c04020191080e80c984151025408040000e40080942210503600e507500b400540c05500c200101300f0500b900400c00a00f0404103801800b1000c52100502c102551030000c1104225084079442c0d2002c2100010300b801c44c0100035007550810880075000081c4030306540c0182880c1f40503580b0b50325101308036000701c0340c41904480180801011305428030150410340c00013159402d60303141d10a101485c03600d43d259001481012000164405004403140d802c092481007200800740c2028040007074140c1c00503491140d002d94446c0242e03030720000904506410b400c00700066400050420030411707000116030726401c4405c4156268462400400d1280e031050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 247917976 1250 247916726 247916741
    0xc04180308010506030907170c0405090703030804030f210b13181211061303031b0819021903060f0b0c03250c060e10020d050d0f090b010f0f09 63
    0x1030795000d1060382040c0c00c01150745c00c0504404420310848002107040f21120205421290007030000f0084c0c503e02100700070990700010007410964016140030000270b508044c0c0a50000d070f15080c0819114600d55003140c0480d4101907151601a0451018100c805070340c0c040e03410080156607581c00340b01c0c054820070540f902d0368a015030f20440c9a07140d0001c00c0085440d100000c0032032074a901c08003804140d41d071802800703440c00f04d03155142000f4501016050b2080c00407544400014000000c124030f0040c207102802051180d4001071080751100c1c201ea50f60444904039060300000c5100065804000c000f04450701602d02400704203507003c1427140340c135400da503001500c010045250509036031482c3d0601c880104ea403284a4650f00d02000050340303070300f007010182100d40d0f207a510603103881d410881503282d0004c0d1041550001c0d8202c42c49a6030003000c42e103900402c00c202288030060311001d4801041512400f600c2c809540b8000300300a400074040e20b0880740015003d4049a48440542e01200e030380 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 247919226 1250 247917976 247917983
    0x91b143009010c021209060708120a05011215020c0f0303012d050a03140a08070f1e02030304090b011806020106080f1b010e040f0911010f0c050606240c0c0418 70
    0x2c005d11981e11240350005002c40003014101906142440d69060f50580003030540d156001102d000300103c3c00b40a2081900400103203c2c0307140d8400c01621190415141481c1d07800c240743d00001c2c1004041001c00c244941210542c00303ca6803503030749012002020441e00649003103906040031000440b0b2100b0341c4542919070040c680c0080500d0340ea200c03410003000542c80b032614000c2002c01400706203141d0103030000303030300907000b540100e01186068180c6049a10011100030f082d94417250141e10000182d030242c403030031080020070f0100000140c6540c40a102202c1203030403195004502d0940c1034200108031000c0004446501d20000030f8151240804103020248a0356090031045540c4a0b6291400ea1000078000180070303d0552404401e56590350740a4800d842810035514465a118021000003200c2d49083c5407007040f10360300c0d50749420003d08028070030b8049030881110310080c2c4000116500303003c3c1d912699880340c1e01d28103413940307800142103119914003483d00b0200d000451400717156592 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 247920476 1250 247919226 247919233
    0xc0e01020105010f120314040807050906061227030d0c0906140a120f0c0305060a0f0e0a0906020c0d08040b0f040b0610030e010c020307020901091b143009010c02 71
    0x804615164a03040c4540a408004d107c1a0502c0d685901100074005030503010003a00320f803402c050612140800152845005007001c0086940c51517400f010103800450080824001820031500f0404107040810f104030303e8040011099005074040e40300031034140003900c41c035001c2c1c4e99441003030741c154609440a02c62003a00b0010400994402c40501d0708221004200007510310507078110100301c882d08035841c1d001c87d9907402407155078608880600c00030700c0100e1005903001d0900d07407180381d0b103e0048d105000650300c803d110810030040d6011396860f00b000300101c50750210180c0004040708001c1d04c00343c0f0244604000304e0071a403100c0c80b07614411034114104841c65110078045c816040320720080c8504040d40c600440d1400f4900307029855203c400c0e54000e50729064203004100740201d041e40030102e2945094001d41c0141540749503051407064505000300703540e04008201005215032141100e0140c20f03941e4800c10580c04000241d811054071084100c0c80c0e0320a14143e08803848a80b94101590 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 247921726 1250 247920476 247920479
    0xb28090e1f060f0303050a0914030717070515070c1a0a0f1116050405010b07051906110f041503090b01140406030501050c1903090c06260108010c0e01020105010f 71
    0xd01d40e820365600380c940c0d4940082d801e5511101061000090340045001030302c00071307005030800d600441d0b01c0003038800740c5416001c40310924006503541b03206201c0c11100d05c114410081d6904030a124200083c40094a4403800400760f14025403258010300040b50136046955020030b109180c1c41c501c01420340340c8031b9880e00e4034000c0301050f01c18441000500c010440800c0300000c0004040c8030762000c03001d414010341e0740242040d04120565905822000a03a8011f120450200b180041d4100d07004241d81070081811a607030800c0000b0b4000c5040309880c0c10340004d100e001c003c42540040040711108644041c580400c04421800e44106020240205510200600c5164096048a000040000c00c000b60955981c0c0c0c0d45805d640d000c03030f00ca1040c03035804580d0301c10072501141002654002441e00700300d8012150345100701c410f141d0048500b0088914807085255580303c400d0b6441162010141c0ca0a6a48440c0d4a020f00303c030b041c2c95400207510794100c2d90107500500456040c2d604111406400b01d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 247922976 1250 247921726 247921753
    0x6020a12082703071a0601030b120a060209060f0703020a060c050909060103180b1f06081006030b0a05030105090615060f0d0902040204030c06020d021e0618010b28090e 74
    0x2e60040141c2601d0000b0490480003031510100e0200c410458103006015190100c0054202c68000712010300500f02c80c00c40500c10b0300042020411503501180068030b500302e03080491214041d001c08400c0101001950006050b0002807008805218803c10b0084180c0400304581502654003402d0704802c0710404500c003507009400c4800b4950741d070026800240c1c102c0e01d03840c2c0119026159a03401c4926404140307000992038400c2c0025040c181000d212a090102140b01c804803e80303d41380030160b448103074815960712480c03420018500180288854142003950b5602c500007654080c03224552200345c1c82d0b49044c0002581c81840030000301d10f0500402280b0240a030411040807684079034204004800214003802d03850103422030703500030b01d80050300400103803801c62a0040a1b840060000c260800c0f08000a131003903010800032a85008040214003180c00341081d00e403a96804400706200b8031240b01e02c036114041540b42d10743c240c02803035035400b441412074007007500d4001c041e080601d02e600714 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 247924226 1250 247922976 247923031
    0x1503050a0b06040906081018140c06030a0f050105150d090c0302030703080a0f02010b0f010c05150a150e1b1c050a02030601030b0a0b1c0f020406020a1208 68
    0x118521030408079140c901c01c000101143d005410882e40c2c6a43c581c000c1c03183c14000c00c00c101642010810400043c0da020105091040d100d510090035654500d1284100040a00c425071010002030f2005889003000c0111002614820407100c182d1441c000c00040e161406c003080d0304038192000541450401e881d4180d41c050692403a090f16092143c01c1c0020058404020703c400039409081d8554807a088104010034248042c20854210380c10108105215640c0724501544900d0034207112116079900e2a150703003408112008244082e100004211000c95903800c40342818202240d481e40454880501a000d61816182d458a1141c20869404254203c6006007040e00b44041c03040010905000e404013070f43c038200c13904080c042e004005c0c020556050b01030b22050b04e0341202d40d41c0e196802c0138a4209c0b140a9050608048860030301005082c148a611405101c805501c00b555255125a0007030b46d141841c4000b195218401901d40e18264850148076014010790050f5028049105a541031b1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 247925476 1250 247924226 247924231
    0x1006080c0a020703120e01080a05040519061401030b0106091a030a02031003050d02070e0f1303050d0b031203010f06210c2f07120803040f0303110d05041209150305 72
    0x40d84503091000c404254006205d81c00c120207680d5004000440700001401e11201600100b2180d08000a02c0001000030074100c0103004080060500144642041400313070001c1404803100119540000c810311400d5205141a11005d032550400e0903900d041c11104142d00342d01c0205400e2050000c555080b0841e00115000547c924520907016282d850303160a20080350000b0001da0b1040c00100400c0030354130138080d8000340216100c401803030b068100c401c4c410a001c1c0c008080102c00511070185554030741c0030b40400a400350442d403011100300c070429407680c07081c00f80b0150123015901c0060403078807a540035032824100c0e88101c0c41c7c1c5803901c1030030809007541040100500c610801102640c035403140c3c985004104444200c803440c01d10141407800d01c3c1440c0c0142c400f0000024044000c11481022a6045903100c4000c03000f622003418110020b240d443c001c408040d000203084403684e00160000d50080b4026050340c080a5848042902c1000c810b218a0700403401090000c04042e019501166 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 247926726 1250 247925476 247925497
    0x1a090103020d0c08070e0702010c050a0c03080c0c010e010f0b0a0f560406052a0303040812010510090e191509050c21090a05010c0f081006080c 63
    0x4441a0722000c4245c00c009141d040a5044400c110810003d04e0f03090007440d8441c60f0900f4014505100000011300416010700042c0078402d0b004d003c5480000c0c801308684145010034000c0101d480d9600049010303040341d841d208811401c1c400f5204442c9040340b80b410881d91f0440391182810300e018410301000415801c000103060101c440d10a010244c000c00da0b0f48803c45c08803172500c40505d00c0c1504074802c41c101318032000650900051164a4110040310041c0303440c1c0315441c1c04485c2641028141e560041c0706e40d1103c0c0404000e00c010050010040c00c1d500554865000c001d0ba01d070800d016030b54900598840000fa0180c1c410440d62080701803c5401038020380040d40c4410031500480c06070307050076251100c4003c541c182042078440034400c00f9000791386904103c1c0350000050400101c26004036400340c29040900100d880c0c007504209051900303502c80000e110303007500d0070f0000c1c04410701c2484090210301c410001820004000794483e06803089a02c4140c59030b00c403030002141a0300b05d8507401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 247927976 1250 247926726 247926743
    0x20408070e0f01150e270a0608030f0d060812120a1401090209180f0702070611060c130f03030305010e060d1212060e01120c27020a030915060602011a090103020d 71
    0x40d00a6103039507404400011000d403034100c03140c24003c030f07509001d40010b291f000e9813454400e041c02012004000c8540d15420702a07035517240c400203d000001040c443d44000f0a62041c80c10b10062408241c000d801540322026a610081c2d45880c0c0113800e54400f0612410300c541000b0051280510590143c503c0f00d0000c2c08103001810f02e8551450441c4007a94509490030b1001c0400411640c10450724002c0d110625010004130b0b0184280d9650b140060b04003010b42c1000708800702d10030881c240480c01400d2030700750035038030540d60f04010780144000e00035941c1c144544030010303031076007068000110204c3d404030350304c4c4845107020812940d07551640684e805043e01e4090000352881030f207203058068440f00940016110303041ca404891903c85a00ca200c0d020348120260304161030401c22004d400030072841c00350750f80c0e0001c1d01c118000d00d80700314020b0101d50040c0c0d00c81408040c0d60b0181c420f480c5031790001c00c4560840045080c0c80c0b240b4011903980403050400600041c20052001c82c10320344a0360b4003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 247929226 1250 247927976 247927997
    0xa0c09050301050a050108010e01090201140304030c0b15031009110906040b0a08030d0c0c03020d03050406140108030c010c020c0609190302030a0807110f0a0b090d060204060201020408070e0f0115 86
    0x207800e45505444c40e4425035110401800812802c3c420a00c90050450080107003401c15070002c1d0000041c5504208500f90200014061500a10708440d0844c2c0c8a00344548918111280c01e0007041e41d40049400303489081c60104441c68075100d40125030b0f400c100c002d9901213450042050210000346441d41141d102c03151448161180015900640348410185858071220188901202d120407800010001d04031080000710350080f820b007980040626010a41c1c2e66a402c1900140443c0c031008951080d88000001e1140400300c05032404a01410003800045070210040740d8a1460100280c0c0c440b40c10000c1000500d000d0369000b88000010300394090a42d500c0d000603091a40307020303080d02c010100107804400c0007211070044140600c101c601600705528070010034402e861902506400440c00502d84405550702607041420743da014005540c3c032a1100d900234081d4005101c0c0c54000e22586902003000030303510340554400c1d417151070860300d079a1824640004035040c18004c4010b01160086 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 247930476 1250 247929226 247929229
    0x60c1e0706090813050f190b0a03090f0f0623061210090f23060f042604080f010b0f06030c0d0501090209100201051e06030304080f161502060a0c0905 66
    0xe044c0950b50ba00c00c204000c1d10b48000d11103200a200b010500c604d0203110301205c0465400706c50000e81d04010003480c1c6402a115060307004184458000d0720384484c0c9200482080384240500210768414002400701a0040e443c080008004445001a401100000412904000240c420001600800c0b54041203c0c003206c8404c030b8205210550702110603034403034814402d41040c003050048074540714100195801c464035440c4c14001e00004c00240b0002e0200e400d21818403c411951900c100c40003088890005450902d80c4c0644070f11341d8540201032408012a906200e80f1305201c401512402c140e02d0780c0342c00c000d800c1d03000600c0b141c51008180040600c4440500c10140a401026001aaa400035208004141b2048452801168107013000c124401c4d240c25a4480420115070044845803204000070b41035001d1600b00e08454858103800305111480010b861500450700103180305815203480440007002842602c840242e880140480c00b042800c1c0c1c00760803004901e15010b000c10782c0311030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 247931726 1250 247930476 247930493
    0x5071701020f04080106080f15060103090c051e010201050a0605180703021204110f101e021212010e0705030402010f08070c021f0f0503130201030506040b04060611060c1e070609 78
    0x200310304545d80d07441c4002e019050042007541500f003000001041034421008030a5000f1000804960400da1281001d03410052034946101c02390800074860040400010760184c2d0002140c3c401500560078840400d02c101c0f80c91007040143c840141890000141d40c42e140441d20310007400400405a003041f0070520b2800c0d01c0580350140c0e00c02d51425189915110030007490384000507501c1e01c55804041d0b502d40080c0c00080b02a202c0341440c14180b042108414240d0410450f0680c0b4450100f00040366101002c0c0701e11010306841c004203810400b5240d1181c111514041150700a02050030300c000d18215901030040258003020614041c0e030006200c1d1301180030800a40b42c10145002d02100700d0200b140c11001411600c2032a1505078118a00b5600c0c1c4840043c0c540b01c0a81819a45c90100c0e055440da40c01c0000754010161003402070726581c1400900b02c0e45510382d44007890054001140280901070102c6d152405890000c1c0d40a06c1c041404074015030121208482d1241c3d02c2d1240c1c00090810f1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 247932976 1250 247931726 247931729
    0x913061d0703050a060c03050c090d060b19050a23010c0519031706040b130b041d0601031205090315090c090117071a1206121f0b03010905071701020f04 67
    0x180c000e040d4184d000d18060b410785914501481c03e040c01d00c001c0209160310403081c0c8815500c12901620f14a10130304000d402000b000c00c509070041524404080c011902242c0b40040720020341d01101d40f00d585120304a082095400c0380410070f4030a03000300b4855071190401d43d0115000b4800c1c0c41d4600a0401240e0808a03820b201f01d020130307068048250b9220002040651000098070203200d070005a0b40050600350061540014190369030100003c152190340c8800b10741c0710381c403501600762001e0007215662203c0910088403459400c1540c00c0b0041d128a040c0c5452020140041c45080e00c0480350b0300d0f4110004000d5552485034880c07154003680e40031380160083c20074089051000b0300b4050000d090a64071f0300441c0350311680000c105032100140c41141c21050310364103501e9858072001f000940350f0020408003550340c8591010b084580364441d6900b04820482801041600c0c0c018040c1800c0e51004100074060340c010348010031070703a6890f50640101000c12400180703848610445070302d150700203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 247934226 1250 247932976 247932983
    0x103150801140f070e030607030e1002030c04050418080403083001060807050c070b03070c1205040501020c0108010e0a0b061314120f0d0311130b03150913061d0703 72
    0x14446103e000101c001e801001a2a08003101c03480780020950314100078040b1010540c0c0c5100c070002c0d071101402425001c40c242c1c00295540e0400c01d01e0300c59560031074007460740710358a0701d481c441c0e104903215401f011691f8030040d00c42c106807645d181c803220707030308004086940455a21005507550414403050084035010001503195075041080041c008400140345200b4030204010319204404006066811102c84554082d40c036955240112502c5401040003054100458912030314290441b0182090b40c20170317421250549640d000450ba03040007131203040d501081600119204240980040e01c45482c0940021314044070744100f10743d13001455008035041420794440350603e00c1c21054484907048140024404103000c07084450f201c2d64448005010305a0301c0088000310f84850095600cd0140094407002103a0364405901d51307544100c80c018008030445080c1d409500d0803101c1c00340a28801100350142e10f61584d42c9030020881c6080340001c0e03040c0c0102150b5004c0c1c0030010130303010314070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 247935476 1250 247934226 247934261
    0xf0206131e0509010b1b070e0c030103061107030f0c0303140a15050909070524070c17011401060309021503090a1208060306060d141002040512011107020103150801 72
    0x400007490406800301c0d810036407040a95400402c982d4502d0016504c41d000d0048051345a04903000310103141c58002c0d800104441c450008108131100e04001443c1201d02400742801080c0f2100c0000a007403040c040001c020401e0b07a501000010311428082c0503d9100c0e040014451143c11806101202e04a91400038142c4402c1c00903101b1000c4904400100300a42d480072507070a151040da40c0303881d201d014041c015030008620900640841c017401d42002c080890705684ca4289041c951202c4000303004985250020b007a00000168051003580c4c2003030403188200500d42d082c503004401400b15802c05a91143d608000030701100070b101e005601400c28400148440411440d00c40841c400c6602c140090020350001c211141c2c03404144180c0c0010211201e00d04880700b0318003201020400c4981c05101c0c45407501108180c3c12076402072007034460803195400c0c03004a00410a080e108521000840018280003440055000b0b030411420024010100700e1215282c1500e42d08450380c0e1aa60b07030741400e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 247936726 1250 247935476 247935509
    0x50a06140301090b0f0702100507050d05010b07020a0b0c07080f060105100504080c010c061e090302060105060f090913020907020318090103050d14190c060c0e09040f020613 76
    0x280352511800a1030040d0020300800402e0780756404101e100504054021303110b14000781d049031090050741d0540f150720000b0002da092a1310000d002d600310b018180382d0744d8a41400440c10a44050549006e1940145192911400c00050104c16008040303a40081e2003001e07404213000c0d00601280e005030481c8001400c09600d010100104000609c260009019040100b4001190041420b080c584800c1c00d12004680c4546090b00c0146a41c6104003030912001240a400340c074a500903200141c0654201c6801e0b03600c910801010340300700e20315072182c420200504407990a006070040c2d0311480084010f0494203990b00812000402143d200d0010303040044d461019000c0c00404001100c001d40e10404c0359130640da1a25558071211414000740600c541c1c09543c074610074001c44114041c454a0034951a134107900140c0160040b5400700d4107641084c200e4040c80784520451f4292000060802c18141c85644500d400c0b001c0c405000e0b40c10940c00c108000c04002e107a500326000b0518642d5141000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 247937976 1250 247936726 247936739
    0x16090b0a0c0b0a0513080711060d0e0105010501020d0c020405090a0f0c080f37051605030c0402250305130e0115020a0206031f120602070c1a0307030507030f050a06 72
    0x7442c02040a040503240906000788414002490200554400644d070360b42c068034101080320035610400941d00010020341800c25042c0380c3c0048003800e140340c0081c42141d07210001662111820a100000201c4626504015161540009800506047c156403d03000a900c0b008070711406040f054610348000d19041050a00801103004007030600c1025015800e112071070707040316404c01e40c10038070520011030403210303109640c00750a031489a1040c12920070113000214440b03014a140700b00e9219015001c0e0303002c1241814002ca82005400035003480030050b03004c101d0300d030340d100c00345042d0104041400b4004500c400004018040d0030f21000900480d0b14042001001c0000450300000b19000720040d500161520ba0035a40c211206081c014100580d000881e04042a661301201d54600d000c0e011030140324250b4010200d250190500450183e110b500740034003030303980302419101d51808000107180248a0781c042608101d0524001c40c00c1c405008a480c217507035050700c0640c01142d41c0c0c1d02c200000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 247939226 1250 247937976 247937993
    0x16030e0307060207030f14010f06031b0902070203030a0f02030f04060309110d0b400b010e04080313060e06091c020705060d020903070509040c0315050c0316090b0a0c 73
    0x4280620084c8212400d5640d2600f6a42003881e004140b081d1281c03030310740d1070300081d000301c001590040030410125070350782404600500105d4921410741d494807070200c0c8441890003180c101b130340c014004610308007141400b00c4800301c03030350010000c40c0010b004070f1f8042e400301030050000701081c2e90301142c10740007402c0443e0034082c080001482942c10b045428009a0201052030f44840400b000e001040b1800c0703006c81202c0b0041e200241400d210b8140303219104001b108603071304540202948910b0380e880d40310034105c1007010345020702850020300c00111201e92002d20301a015124200c080b420f0719a24083c2d510f00303a010303141c4c4219600083c0343c071100c2c185058241d220089161005001840c980350110705144511842c1403000ea40024250384161420031209000b024007a200560b01e00c0c1606114140c03c10601007154501420b5504280c00c102078000e09004820b020010b61541d1240010101500c05080071801030200200000a00301203000107025049441e072241d080005052908805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 247940476 1250 247939226 247939229
    0x5060f1b0307060f2f0c010903080124020604080d0b0607030c050115120f0204090b010605131508180c060d0c030e0a0512030a0e010c050d0f0c050306040c0516030e0307 74
    0x501c0d031038a1707800da055480b507500102044025140f00d145105484400c05083d00c91908801c00343d43c200b0075203104050b481130700141201c00070411804500d0060400c4811120300ba184d0000507806480450042110880103241c2c0b945900300008109031100003183e01c030340081c9001d07400318820201110034408203010310f0b01800030189440841d1424203a444410000c10180030f0031150113526490215295a44805441c42e040b150b075007041d40e5100d000034810382c0300907000e5900d654000d0000a141a000148142281c496220800d2079598003001d2880c2a01c0460300c0442842421a040050749608009100b05800117401040c158002140602551052204042c0981c003481910010a501142e545140d1280c0d00c0281d69a4a40e41c3c1c1c800c000d40061004403440c2c0d403070120341c00fa50540100003002c0041c400b80060051450150489045890002420340070a100300009031b01071a25a00c607000e0403805081031810640e031007900300c6091000c00710481c04110001039801191604100080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 247941726 1250 247940476 247940501
    0x70210050f16020f06010e07090b040b2b0c0306051905030706030e03190507030908060f07050904060305070e0a05010b0c19020f030a060c0806041505060f1b030706 72
    0x14145403107103840c0108020169040b04031101000d400309442032050308004030204d011900c1d5540c40d05101c04642506588001c0450b61072080007441854034429501291b410300f10560411528144407220b0510000c6c6a10b204e0600c0c441c0c00302c625170180318105c0001e40ea0360b40061034509000c180402d040c10000c1c80c074542c1071449070402003960b00140d030701c050307641c0741c5001301d050920f81e0459451400f40604102c14120003813182d0303810aa111001d494080c1c041c2e5078500810faa600b2180b40c0318107007502c6110880c00300200281c04980180c0080c005010044d0000030340d20303a01c0d01c1d81c2d130070014141c100100c4180035009000c00c10f409805030501400980043d6031034030300714070701841ea2142042072452400890700000340566030b07011401034001c0e00140607a80ba0440902c0c2102c01070000d040100c022501c14000b00f05c0c0d42c28184659541e0a10280118404e0381c141810040d01d6040000d0800c5d008104110710800d080000500b0000d0502c048002c5854440d0391510809541c02520a503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 247942976 1250 247941726 247941731
    0x50307081f0213080a0f060f0504030f0e192c010b0a030e070b030c0c010f050112061e0e030a030605010c0b0c03100902180909060105010c0803070e03070e070210 71
    0x34901d401812001d2a42000280340060b60f0381d0b0403030680000303065a0f6010301428010491004288005403103840a80e44c810329042200c0c0c40c02e14003080031070740c0c01c1da0061300081030360055160b09070103a601e00c400340d8002401c520881006003110091307003155030020b02000d00311100940c00844243d003825130303544002201850640c1440c01a04150003a041032104050300e6030145401001c0c14402c10018124080d0a5a0740b071a1850b5a06803d50054028508079881c04240d02c01d154050b02c40c20b41603411030600f0110106690321160043c084503064060b880f43c915645000301801b80c0b07d91045941d982c0041c6031510f091407006402c43e445580710f10305001a90002100060103240016440300c421a8004e07200d4031002c96100c01c50b2000d801c1200b20b1440000c050200c40207640510000580440b0303c8131055450340041c0313448000a03c6124045442d44880000142a01015507400f101da4580000c20507011070009180107016481805290322641c2404a86c41c2d05000807514080c0d0720005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 247944226 1250 247942976 247942993
    0xf040f140c07080a05031302040f09150e0318010201020c0a050a0c060f0f050a02010e150a060603090b0a0b4b010215090109020409060203090606120a1106040513050105030708 77
    0x9207800c134402c0e0f4810200f0004000002414203006a5180e005290043c4c0200041c0060302c00001c000d00000c0c40c04d0721011071001c0c0b91a08110b80d40a060310601184010b9130a1919103d00307880380d1044502d9140c10340d5001d00c46400c07040d204010240511307000e40000c00210381541810300210084d50854010401c2c40c120303e91509811400d00c6001408a103011551200000c100b280142200254500c29014402c41807001c6540301b0303000740c010606003100f0000260340300720035801c4031070b0040c0041c405e4843d1400902207121079803050540080203031104070000b041d0700064405400d55611a540b07107680c1c50340c4100502400550a00d4051000310000c050505000041d658019002034400407031584070000b035118500390080003801c0c0c0d000c2e2080c0940380d842e14005003c0d402c2202d940300e0f18401c160000300c052074125803e2015982010207030070094002d0311042c0b2a903801100c0c3e6900030008000c0010b25464559100710401d42042c80003420394101401c05040c0807842e8029072883d44240c66 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 247945476 1250 247944226 247944233
    0x504060b0f03030a0f0f050c1b01020c0f09010b2b02070605011a16030504080a03120c050a0912170d05180c1305090f010603030c030806010503010f030209060f040f140c07 75
    0x404070320305c2c250800c0000d80d00c6e42c1c40d0880e010b210380c0c0652402c9006242d00e8a242c41d000d052014240c80c1d00341c0035aa0507034a04402e0000c1c01c01540c560652000944004105410381400104200c3c21440911a0160401c044c10781d200700074502d10450941c4d00090390001e000703042c403075580540112800485501e525141aa001c0e009a0004d00040404030b0000000c040c00f5804443c010544007055944064240c00d029050050090080d03170810708060083c441148510100e03100400c0540305ea821032800c21035414441460310034219018890002c15415003e5050040e201d450715030035000c240c9103806540354410390901d07080651030f42c1c4620090411176a0300e4000380502c081100700003519644040d01035150082502c103131354865181002c08814181d2200c14601000e009458445c817944800d001100c00c0e2009110384003240309440702c02e00040c50f02c009200c2c2c0088004180024440580d0006011110041c54050640d0b6458258410100c00074845a40c840c3c01c000906040402644 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 247946726 1250 247945476 247945487
    0x609131b1404050f0f0d0b070903061b0504060c0809030304030c050f0102010b011e02072d0e040201020307020103090302011d0601080709090b43120216150905010504060b0f03030a 79
    0x10768244100310b81c0b00e08082503120710540c651b45ea0f41201d03404181d400d2034500640008038a00082e2101420606107200701e0540001c0920703100303400d0341c2e02451306107403000403100a10b250301c049544a4041142c08580ea90802c082c001450090207050300151520040003440454400f2107819a410f015444c1c0c6140c0c1c00141c001e54081c0b880500e4a004801c000d0100e01308041c0d80c0084c0c82c034512180044922581300fa5445e0b0321010030000c4948011303102d0250880004d002c41d80280160300400100b001940b00c2d400043d044d030301c03034000030565924405c03203103900a0219840040c1071b408640104654513003005590000c14400d00300700b01e03031809501e4041c0070050041c052203094280b180345d00c01c154480f074124640e580e85c9110b020000f41a00c151419412000c071030380c200085003001ca5041c0060a88201c5031002c1e4101a0301c0c648190640e0b07003900309003d44001d840c8883d5900c0a10000c2242801100d01c540d1145800059291140f0100050403160b004440e0003035009200403d02a074009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 247947976 1250 247946726 247946749
    0xd17071218020d060507110a0c120611070f0b100e04060c090b0c0102090117090a060b0112090308010e0a05010b0313080910080f010e0705090609131b140405 69
    0x100e001240301d4140240140103100100d4000790040c010340b9001081c0110b83d0303c118020001c0d5030742d03a0400e0100740042c503641c00601e0400740c500c48112604202c4070650140c0c8045192082e03002044079040401040866000004280c4205c0c13020400c2c03c0c204000c1910050b80803088001e940f50305424040c150a0100005100a0403d070b07480d12131080c00c9000d00d800d50010000002020381e1a004a040320303010f0342146807031074045030018408560488034121040d00c10f070540303c001d010782d01c1d440e1200c20103484000310060500441c500f8000c014502402008449400b948440f0029498140b5034455600c0c01095180140d1a000040c000350309540e08480c0c000140d2458145910042d0600501c03500c01d05840550240c0744102117000a0740120a140c8240410780304413815a9070b81c4058010a641221002300040040290010b64540000502035105000e0540c1d81d0b0300c0c2a0903080302c100c45111056884403528601c0307141d403407940403515000c01c1309003038012400e180ca403001007074800014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 247949226 1250 247947976 247948007
    0xb040b0c0c1c050c100f030f060312090806010801050610080c0423040b0d15150f0311100f0807030518060103060515180402010507020307090e0d1707 66
    0x1600850440c0030000649240c40080c00c0303100108561142142040d5040002c0b40c040c001e84941e00203600c3e102150310300011043d02e074007101103c0e0050440061108814442107039985031004000f10b0802da04060000c0c0d03954179820410b604001e96640341c404141e0150840340e040078104403a80c0c5500c011949a1891030601d0440d58403590402e8500d0300454100c007030761580310316420100403c008040e0031204019241000458584c8007880301d003140084024161440d91100b42804142551065001d070007441c0c141202152541e20b01c00d88650168000d80b404800342d101c0030160320348484000c40d0096503003000c06500c0400300000d414202c0007800101495070302c0c40013400101c160f014030f0011074001d80545040790f840b4508034005040640b000d1080d41c071401881d03101d9003044c60007010201c035200c0c0301e0000c40ea901e070300448450744860801c0f038042c050003100054008460140c11310702940003001d04191100008010119201d0516044160000c0403d00032140d070000c8004889c00031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 247950476 1250 247949226 247949249
    0x6090a08070507080d030914031e0d0b0303030903030a1107051002160501090507090f02180d110a15080c18010f031e0501170d050d050601021c05031f0b04 68
    0x9900b0003500303250710390b03000802501605610960590341944a13584282c42090450115600c400c3c1c06c0b0b9a90050070707a01004032100c4655901c6070403070040645004101c507400070032044141000f1908540054070b100c00b0320350010003881144100d034060010706213902076132642015180d440305a902e02c00b10400f1440c0940c0010b43c042141c520301506600550000020f1000380e43d54034000350781d25494842c101a9916103204020412400e00031100b00008904100e0490130450041040b45100501d040305c04034580180d4480c29110980c0a00040c020a406805400c890b0b00000c3c1130184000d0100e0803002041044a807245508090050036103001c2c07030042c80c14100e8400c164001c22504040302c108068665141c00c1c1140d0740d8000354140c4e8074a100e013415240d910a0f0450f40c0d000c01794020000b01d0014800003152001d40d50045900500c144116013050b00003103a42c041d0303003500c0000003000450020400040020480003035241c0d0400b180e034100007a00c0c0c1840c03841c5034080c80c0128031a02c80b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 247951726 1250 247950476 247950487
    0x90e01050312121b04080a0506100b09090c0d050f070e044110080f0106060903033203060316060905010f0201110a09050310020406210f0905010e070806090a08 70
    0x1242e40f01da99042d41003402601da911390b15803110613520f01d84410200ca203272082e075000410416a06000200325401c103020241072080304000c0184d0080b0040c0103400d0918103004409043e0707058001e80d4010041c141d08460117042c5004010008180c0c54040c80c0130f281000000b4078440340744c2c0607015006002c405001e61000013410040503a50780342031010009005081070004603070003901814102d40d0a80c044a50407414184080d098551500c01d0b8000f044c101c000420103c0d020360040b482001900c1c6103101102e40342d21075400790204445100c59112800300400540c1c2c01c080254425059400b001010558602100209402110700609042150811051402e917000350000c60700c1e0400e045445480760383d400002020580d00c0c0c40307914800e00c103110700726103603450520849007551103030f07a07820800000d02405045903040e40c1165151003560f80c000301c20516014414100d08038030585c00401c1121b0b0043c001072800708a50403120760340d003140b0140300030200c0008981d01c106501540498541 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 247952976 1250 247951726 247951741
    0x10e1c0908030304030504050f0d0204050412021509060106110709020705010603060c050910030c0215130507060f090504090201050706020712140f18190602070608010f050102100e0c04020a090e0105031212 90
    0x802c0c0c5140290070cd8100403d00c01001442c00929035043e80548c210f811469461510790500700d001d46014030780740c000030014846a445140010041e001030700031258040c0d9202c001c01c04030390003204143e8099655000910070411980941c0050300c505180c528180600507000480248468244806243e65042844401402404000005504851a95580e2134005542c00ca400d801503411030701030086160201d112030041080790a01138a0395150311801d402c000900c0020001d41c50140e040c09024080380c00000c3c041e00061507580d00c41c040303545003204095400346c942c4505142c2c000c1d030000c00340241c0d0041640e80d02078440076030440c020071181000c01000310300440141c000040351a201980c011a0641d000202c4004641150f65010980c0ea0ba41048010548050040b5401a00032803504003d405040d0003450072170012905a0743c100741c140e400101207900045258001c10710010041014560f00400580100b00944c00341c080c0b802000c00701d02c0340340315590000d1100d035070300f20224001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 247954226 1250 247952976 247952989
    0xd05071b051008060a1d0105090106030510210602030705090102010b120c04020702040608010e030a120b010806012601180b03010221040c03020607080304020f0a050102190302010e1c0908030304030504050f 90
    0x4100030b10700c0c034900340104003001041da06d090146034080d89006000042d600d21911465108420b0341c81c01c50401410301301300e0100200c03010b0b00001d404600026003000704425100540c003c003d05c0d140c0319034403074240001a0035034880007180740c415105451500c1058001003590002200b0481d0010783e950a03510015000b403403160041111580f900d44075800109000006004419280c0c882195008104449074195901c00b035450380000c42c2c11011074090350255a10851280520548020002070ac1c880f016202500340e012881c2c42c0c0b50000b40300319078141c910407580384800960003980350a0504000b940522403111400241488982c0018244491a400f2501840e401401c030f559804107820620103a800913a0107034440d20007948049094902600f40ca01282c406130050410300044426610400c008032005400b5552210b03141100300c1c0c030a10259440400401c05074009007030b01c0031700410031240342c0c1007401168410018000800d82100c00c0d1801c88104852800c00b80c5080404980c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 247955476 1250 247954226 247954229
    0xb0f0c0d03050613061206020a020309100207050a06090f06110a0c090b040b0d0309050f06121008120f030610110d080f0907141009080d05071b051008060a 68
    0x5940910040c010800da41a08510f0040a0848164002c892605204000c44400d8480e180c1c680041c2c030754400004000c0e401510300380300d4500540741040c6010012030740c06900b0811080068001c002c06019500d4607840c01d1000e41501d1030014155400c1003c003200d0003619010700c1c01401196895580c06071810880d003196168801c86d2a03026607a503c01e03c001a245103000c00348520300f040340c0c41c40c0508004880480c91501035540b442c540c1d290074203008081c80d01d0342a0b1034100f40200100c0b600808039060031401086601c09940d240343c544940d0750b0528443c019414541d8000300140c4001e013110106480d0890000c03510303d50034810325142516210b000c04040482802440305c1100d6694009200707071300c40e2008419001540d070b02c1d01000d503240e60031406842a14041c0e081c0c245070360f0602002c80302c42d03070100d030403c2500d0680b507a00d5285402e0080b020320b07002540005100e020800042c00d84400941400451a1028180f41c001110003000103814010030140c04000341040e51042c20580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 247956726 1250 247955476 247955497
    0x3030409020d1805060f04060209120f0f1618021306020a120e150f0f03040f060b18010314010b090c040603050603030906070b0403090e0a0b0f0901030b010b0f 70
    0x255116900d4201601075009407448000305032814081c0e400a00e498014a0f103040d510102401107540d44010124006001400584055070300340722008140d00d42c070881101c0c1140c80310040c4614a1405140d40c5071150501404d074441c0c1018400140c007185c501401000c0d101c901d525140340c2642001c501c800fd02a0704032400860000680c00100543c002c18001101402100301840d4080111000d86941150341035141d0408503080b1065845075400c406000c0b04498004204e24152110b141141c50307801c150f42c15609031951038508420882c40d0311421080307030419141e42c04403d0703501f180f9418510701484083d02c0b083c4030780b900b056034250a41c054001000e008003030903030b0350030704441c6210650814020000800e1a01e8041941858004250f4500c41002044103103403038555039034140046005082141441000600411100301c2c145080340b01d0010b40100091100965080264070000c038221709000724001001800410b034203541c02810f603412024a15654400000c101400d40700d00d0341401c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 247957976 1250 247956726 247956733
    0x2220203040b0f070914060901030605030a05070e09060403020a02011d0a0e06010f0207050904080a14040b090414090606041a0a030b01060206010b0c0307060b0105070f060501030b07020a050604021c0203 89
    0x708101e2111075003401103140c0d6102c52429601d8031016201c21015028010b03403003d40c044400001c0c03626100034500d00c2418035002c03881c030b940c41011070303c0c0c440903030300c1203a05410a0800344900c519009219500c59802c2c0f00030310560900303440103900e407016100060304115107200c501803015045500d40e480101c0240280c1032043d61810070f00b802c100e0545510303001545c0305607208030492000401c00180e82004001f50401d480d00d03a103000d120fa03c100041d0045c09940d5905a07400105c0744003507c010803001280c40d555520600400c4201c8822400b8035030400840002c0c802e03c5400007400d960300900a8a0018484130601d40009840788070034480c0d0703405090034138040208642d081e4054101c51540e001c45034140d8a403426040240280d51906009038130601805001c525036411003500e02c031060400514200050326046d0b48507802c800b054900c5501e41c00104104890854030343d82c08240d902c06449000d4190b901c880c1c0350308010f800130744166801c01c0342680070303406800072000381c65004044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 247959226 1250 247957976 247957981
    0x11407082809150504030b06090604110301060206010305213103050a05010c02060c0313080d06090207050d081504020702040b10110c0a0e010b0c0133090608060402220203 75
    0xc0c02e942c11400303000d801c0e07480003c6035000d407401181903400392940b040414080da9255414442101c0008004070740c4140c81c0c5481c1c042295000c00154064004c81d0b006d4595581507081551812100184040010b1800e1454081071a0701400f038030718000000b2111515200c580711080701d44c0300251980300051580c800004108180055455840d130720071b03002808007800c00d60003a80c8410f000c40d04058451010000150107400d0071040109181c0310360001810000e041e91000f04650007a00440901c83c1e0010303004052010400403425080342616220b4044c0c54032103210004000c7d40e80c0701c4d5001c0c9030081060011540d0ba60851415010003410400c1c03580903200c40141241280d0300b0410180c012201291181d040581514040d50004560700031030b646030149442040c2c0c0301044611455507101c40e40164103079020306441416040c81100542640f112416090305030040e80030b450001d140c07420400c1148404500540d11540488118915034500c00c0b000395001400144044007a10001c00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 247960476 1250 247959226 247959307
    0x106090e0a02040501140105040506074d031905100908090a080307081c0905070305030d0606050301121218080d0e2e050c01111801140708 61
    0x6035010082e00840f01889540d903951603025100081c0280f42d0300040c0e08220610a80c14904004c1c4a01481906089440345107100d20708082903d45581052440c2900d68070307900389070044112180c100110744034044480108000a5507881881c2403028850b04000000c42032280610100c40700489205040c030203d4034514100c2031039031140c40014030400001402040341030f400420b0b190a00c0d4421180d45c6051070741195158201003a81d0030007903ca8a68031104001a028051200103500ca08000c648880642c94107005554098000404200060004010024204445418a07a0801c144411041c400c0004030f455041391043c1d4003214400b8000061070080000c0c07110a0700d491a070301e111201c164203081041c42000900e00100080300000d804050314581d40d1040302e50003444c1000c134601485040e1076800c0d10000b8130070781140b51011450803541c081d03000720f80414001c01d103000d000400c07000c43c1244250240c0540034103d050085018910080342c0c190405100018404500d000d886148 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 247961726 1250 247960476 247960483
    0xd0f0606170106090306020702150a171302030613080c060411031002030402090411030705121606050a051804020403060f05100e01050a090504110a080601080c10051b0106090e 77
    0xc1140001080c0e0309490181441c8400c0080c1a16100c0e0350301c15485107540c031038030060b4001050030390748255840d503041d003a107520b00000c0046030301c66100c00341c4c811009403412003003010043c041803003002c0d0007101d4001650042403065008034802200309001c00c00b0b0502610a00510f080d04c4c1c41485140c01340424003030500616140e41800301c0440f1000c074a5a00d4a81c08d070302082d60002c0d00070003014003040000d084420600342c102c1c03016044a01c802d64030000944000300381000c1c80c046030001c2d9882008070a00100310f00241078182841071a02c00010380051261060301e16000340c81d1068030080e080c550302d47d01140c00454014205001c4046a00c0700c000c01480c1c26240c101d458210050002540d4000851140c100e60b001001c60380c040b031034a030024014140040c41200c0c1c044000c0c0025a0340e5030f440f42c5030005444410f00503d825810145141c4c5022030000c460b0f4402e90300b26043c01003907540f107002c6541030340303050b5413504c2c0301c0711800c001d03d0240003175400c00302240303003401d82068a526001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 247962976 1250 247961726 247961729
    0x305120c0601060e01050901030209010e0a060c1b03110603090a0c060503011415090d030309021908070b1303030e010e0904062405100305100306050f0411010e01021c050d0f06 77
    0x108141c5000d66640e050986204031000d0401d400b041c02800700710142e41c0254081e019404040c1404004030100200141c0c2850f0503411910101700e0198104082c801085600203a98844103503500407103043d503c43e0b0701c40f0010907007094458a800400a50f441d58140120004035500c44c0400d181a900c40d00003074030b20f4109010740706070b0118009001036107150107107500d00c02c502c180310708514080c01001030207056121101d080e0207160b114030b000070041c1c64825002901208a00030005c0c40c0d13081c0420542000c3c216881140303d0107052202101c40c10f1070003000b0085992504140420940050050351103008070382819910040c2042040103026154100e0b4402840c007200010710740b1100600c0844c41c000a001345900520490b0010002c80d001e9400310f600400200048800c1940d41c1d130790309040d54821141e004841c007840e824801000140210021344c041c007420100d2817000d6540c0000d43e0b5500c0041101450124451202d44040c06a001c9480440b10b500082c0400849407881e43c000d440c10713 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 247964226 1250 247962976 247962997
    0x70305060f0f090a0f031206050307080703110102030301060518040e010507090905060a030b0f09070b07060b190b0a0f05092827090507050a1202151e0c0106030512 72
    0x141c0e0300040240c20041000f00900341d200c0c100308006803294904446189101d2682487c55994144c041055901004007400914103400205185415840d1403218000c2c5030000505552040c401072080030342200640300000002036100c0c2c0c510980740c0018010745500b818a24555181c8014072403d9035102503450107440c20314005014684030041400340c00701c92880081c242a4008001c5080c9480140c109a0000c00020446002d191909030781e1000c0d52012100300c3d81c0655495000703100b41080e0410b0f6500407505e100c03100c1014580030805419110b0311185008020740e00203418906401107069030038200c0301816050a2102005040204500014403000c00820713002d4001170440741100311001d58141d04002c1d0081c880c10041c00c00240c0103c24040740c0c94020b00c0310101c2c031038a503458500c0040c2407442151222405c5401070220a044040341c0c854a5901000140c0d10b011407031050303840409403692460364500f411025140180300f0760308014954026805501c251440c54005000071104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 247965476 1250 247964226 247964251
    0x60e1801181a030a062c0a15090c141324090c0e010815060307080f071112090d020d0501050906100317070311120d0f230405070305060f 60
    0x18601600d0510b1042e203078030360350f140d8803144000c40000d81540290b40040c450780701280500003981d04200800c42581070ba07001030742c0310288100500030500c000001c03501109230200901c0030980c440c000c0703a0f00e16000d82000b003860903054502c540c4401c04041346105041000700414414100b0144110b4900b2000004041d008100800da500309481202c08110386900c0e0410095a2440199074102000300054000f054425140300141c480e10000d42c481c154564030120589000700c0103451344030f03002d8100d90410040403180c2d6036a400010360b00018405c914005c0c0d2b1500840c02c00030b00442c901c0341c402900710710310860200412005400090284041d0000e507245592450300b582020405842301800d1640b11100414008141200401c0a14040e2610401c80e10b0103040c01803425840785460542c2040026044120904e18442d0340d42c22841e00c0f506000282d000b00f151903400e05113038080ca240011120200381004000c0104070300a42e03001c01582d415207003203c0300604026007103a41d40841103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 247966726 1250 247965476 247965491
    0x30616020f03090a031103030d1806110703120209040209030102040e0103060c08090a020d210804030206060414060907020a200901090507080f070509031501050301110a09060e180118 80
    0x1011069a0f60840e010780144221803850f15400f1810400e900806c0d00741c0010845100c00440a0040124401040c2c11403124100c075440e003e001c95807209000102d15038140900000664881c01c40d86030640740e0740d001340e11150400001f83c000c0c130078000c00c164158400a80010380003401400181200d0103454104010080c031002903d500d0300032100090700c3e4110b10f421000602d40459010302040c0a0007644000400102042e010440086903030004540c1231000c000c01c0540c10030181e984980c09540c00e00c51a0007407854104065400f900c000e00c182170460014150610800002e00b07800d030088034a0620b0f5000b00040c00c80b1120b2109090b0050203204004038107031219010306402220b199481c11800d0751038980d8490a8400a0103000030002c0420840605507000c000c001c6104400c1403880403603501d408101421645020402d0403030742014022082e459400c043c80c107081795400d00b42070800002c56800540b1084610000404816004002140c40703002041d80b030307180d907241c02d800f0018007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 247967976 1250 247966726 247966753
    0x30f0606080d0504061d0607150e010221040f05151005010302180d0c05060a02030a03150501020606010f27050111070b040b070c03060e010207020307060806032a03061602 75
    0x8044556400b000304000b00820801540300300c42c45082600c031078264140340c2c1c8810340066120307482020140d48400b8010008040e030340b40c030302c11041e41d005003000851408a03800c0002c12140748030b0b19410041407004000509001c004641c09072883e50000c10b6a003803108100d0345007250300d41699070484281e542c200224295000b0302c01c6941d6160044140115804800200b02c4440903800c0c04485013003400e900026191a520090013801c4500d40103540c582c684180014100c6154210013400f20360403070000c2105036008100d49400480c00c1ca00b004151000070743c01d4441c00d00449000f8003030503211300115801c3c3c840c5186401a03d1007680e4110b810060501d030940e42d02110302840161240400081059030102c0004148182c49260f02c041825560740742d8508880c040f0400003542d03500002d03600110b1a003845940090203d60816080c94209840404c0d51245a002e4010070400701c2d105401240c0304110800001d031000404852032443c01d0529080c13556200900030340507104d0110000d0b00d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 247969226 1250 247967976 247967983
    0x109080a0b010824040611160b0601140702100305060d0b01030506060907020609150709030b0c03061f02060705090a0509091e0d0503040f06090f080c0c060703050d0b0a0f030f060608 80
    0x3105030075130845140d241d0f070702c400c030041c207041c1d80640e00041c1c104603003189803d000e0034103285140141c90a0383e00745420000508049450002402c0c055010062000141d0388e20700e02910061103032030005016590340707010511410800e0800b60001b0540000042048800030f0070b1441128142e480000c5521343c403e007a0f0707581e0b1080d12041126003090340c4019140c4034940420780e00140520341181c50aa590702da004210394190b40700c50600000104000345070030310f01401c0904120f49441d00f5a0360386c8982000f034840710003078020340401c40e0000d40b00c4210394401c00301d10050040100113613681e01707003003160030b94510008600b4028580c0c1402c81a030607107800304160f900400f0685a0b0303483c0d5552075503071220802810703104880103a5140d01600200d9041030ba01c2c0c841c40c2c410b402d0150340b4080e40c1001841c1c600d43c040b5107071103a40b00300700410010341d208040c0c4401c81c2c1e100c600810825a1100043d28501c959004406010b024050000074010400d5100703142d24001c000802a562315000030a44 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 247970476 1250 247969226 247969273
    0x81b1b1008040503090a06110d1b080d2c010506010806010e0f04110a02060a06080703150504111522050a121106130503060a0c1d0109080a0b0108 64
    0x1809181038001201440c065207940d58014802e40030f0f80c1c58144007000060404207160420000030304624410705203020100094500300c071281c24090422200d4040410604207044802006480007081c0e2070b1000060360003904d240c4005103041e17115080700d42004100c000500c04003580544c00c00011030701039405141481c0c041e03170b4180d40b800001e0402e1024440c0c0c5492041c100ca8001e595041c6520310110031340c004e04207204095020348194103002d454403040d10b80700e401c1500c2c240c004000400014006102150007820b000c030000c20190b45d01d00700052154005110b26070000240546016164407400007411601c4502c01c6101c100d4010110158200341c140c003903075800003407400f07040c000b0303d550044074034010f4031481c1d00642455500020400d140c0101e5521080c0b6146000107012501d03040c024076a000681805c2000210413002d00100b01c0c2d0030901c80300388180d2001350701d007a45074401c0069001030540300b03048030b1003000c8510f8a22013030354007481503510b0341c09010300c95003074038102040150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 247971726 1250 247970476 247970479
    0xb01030e031e07080c06060118080304050904061416090e0c030403030527030301030212030c1e03070206031f120503090418050604060f0b030a0215030601030603081b1b 74
    0x10b042a11159030b451500d5545100c8030701d21030050040c00c002034002402070580d041040c1c00340c05c0c00c0c1403000014098002442990301c400014000071b001c0004008261400c460040700c0074400c949075404c25a000700040e41900d041034042d4030401a11500402e0300b51602822581c03910600c5503122001024143c09848950081d41c080000c1004203100340c007c140c10000c041002c00c416240c1440e106400c144100e03440820303030800300c010000e5140485080d0074900480000c0c500d443c1199071107503164004516080e500d014403801210300d80d02c6c20815194502d50161143c0c0e564203120240081d83c01594100341404603c1102c013041d40c1303102e0001d00100903407003401142804a4002000003802c0342d101401401124501c94401140301000010300950140c10001445440c4049060036a643c0c41c0003240250b00a00384100161503800c40c00e41048485404c542c0c603a12568012005051207030320280400c1c501041d001d888003581c400b10303034080d00b8141c1100c445110804500031454038002005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 247972976 1250 247971726 247971733
    0x803070507031b05030601090507080f0906040b0a020d020c01021312020102030f09130504061e0c09030303050c0f34030509090a060e070201020c070b0301050303030126010c0c03030b01030e 83
    0x400002d0040a901c40c20f84400b03441980015488901013850300f8002d90040c40840d85030014820340540016500d03400c1038000151181d00e01e40324030020b40d94480544000e28000200300000c0481c450382c1d0540d20042d400d900150350351800d40b080b032800b0b500302c004521940300301600000b581c1408802c0c07104607254180c002c0e605003451072089a1454014004580c2c1214458010b08144690352243c148102d11402c400622112003020110b0088170340d401210f001c0c0e151860305400180c1180200080f2a032501c3e010806560b80b4040c41546e000d2a00c07240810035020816801c40050359104000d140c01d600d04007a9803c2221130a01f1043c0528100680812001c000d500e0060401d480c54070b5014003101000310742c0c0341d0340d804c003006841d100703c80c1900142d501042e8680d2241c81030001c0ca008104402c40a411541000f0000b030700c0b032206210f2a840c0c1310341c00d20818108d0300c01d01640103c010303441d0002c1184081000d80074004483c242811000039180040c3d005581d0300034030030220a9001039004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 247974226 1250 247972976 247972979
    0x311030105010e1f030f0f0b06121023040b070212030f04080703031506050919080c06070203070b07060c0e03060910020c0c04020c010e191e0804090c02070503070803070507 76
    0x1221a40c040c0a00554002a91340e5004c030100742c850f18100c4401f03110307803185041000c003070400406811001d0101031058070551048c25482d1000901d0340742c502c030380d20000681c000d628000316844045112011111150034070400040c04480c80d401446103840d90242c0361100d4504a20700418802222070451642103032010501043c01c80002e8202e43d032107070400064100e51901c1071904070140344d01140025074000f4807030940e41082041c20b100c0805004192905504003c8095116818029014010303400070542d40300359a803c22409000b80340c10047e513030740c4803654207000000c1c108440349c110104010282e04a000d06000400b2481042e070103001d00b654400300700e81d05010358041700701d03400148586450f05055030341e030748004c00b45008041d00000f81500c0c1d014540d800c15007141c0709000646c5117010400e000ca4481c900583d80d40088840544ca400094036201005000719000b00c5980c1e0300d40b201c0169400d40010340801660342c100c0881d4074150740c0355100d587c3d9100321800100350f034000c61070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 247975476 1250 247974226 247974241
    0x2031608070201030e0613050106080a080306060f090d1101091221030f0c09030215042301090b120a0b150403060e0705180f10051e040f0507090311030105010e 70
    0x751800602c149800f0908000710b1021074030380b050130741c0c036156900d151002810401900b44201390041070018040d003503c440c01d4450f102c09003c010151400361100082c0d0b0000341c1c407504116070000c1401000e10300f551400e410919403006600346494082100440080b855594162083e1304440c1d1020622481840c03a650036125601c036280301d00c0905441c0d0b541554420340d140504082d13080740ea591001c0007403542c010015060050550000071440c10441409804da4200c10a001500410030b00e581c105036000048034150f004c0c0d400010380e002c0100d4000c05a0000c020140d000350529141400f4800466080118400c5458100003040004200400008001c1e8101400d50421241039a044641c2d540100d0100110380e554020358072012820003100080c0156855002411544047c10710b50800c0c01058032070344101c03c14183c0c5c800503a4540581d50301c0e034100b0025080c60361014041d0341011280500f1940060104480041048506603075901301442540d040b00c0b25800c0300300054650f0702 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 247976726 1250 247975476 247975493
    0x60f0105190503011e0501090c02030306010f090e0c0705100b0907110705090703050403110c03030901050c0a0609060e07120206030610180320011803080f0903060c09040c020316 78
    0x80c1140700814100340c000406641c288540c006000d1241c800901d0700c180105240201c0740b0580100c3e130764502d0086210001c550002c240e952025083c01c01d403030850010103054501c10b120b40d00200c28024002c08029501025101602560380309108907040649a96036000503205c030320700444c1e041110040020100d82c4100008400900c50b00f00340c0e1101900c0d03101042c0510400c40d2124003207601c80d002e100c105070303001d1725000e040507000d00600402c8d6000000240c4034800c0540c0e280c10804003059100302201c007400b032103600ea5130201c0200b01081035032610f0805031a62a00e00c010500600300e00240800c0c100c1e10080c0c2c29170b0700400161071030340c94004000d01103d2800011040000280750381c01d60048686044024500401c41c1c2801500358601d425490001030304402c0c1000300c8218190420035020200d034050760341c400c0360a07880c3c2d9400304070003070030740a01c1d1801681480707024103010000c0c80381c0d001080d100000740d40900c00c5800c04402030b40e40f84070701c1c0d4080d0310402420f14020041418403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 247977976 1250 247976726 247976749
    0x6010c06050c16080c0c0d0f061e020d0c1e090902280e040605060f0307080603030913090506010e0105030d050c0316030e121605040f0b1005030f0108060f0105 70
    0x70b81c403141041142c1c600183c00f0706083c0c004441d502c4000541c240301440820400092003012a954228036107541d0360460f16a440c950010700c9540c80300a16100a80c0305c05020001c500c4200c401c41d240c0c0340c6003d01c003001e00201003440c008500018165200080040c1d441144502181c5401101a01c1d1400200007584000106220743c40903a0558500e240a441001e20900c01681c07003659800701074003040203d0307901c0d0b8001131040f4420001e06159003003103020f40703510401600f080101a5500030200e401c5200b2103413650752085449002e6444004941d111070400c41c062401c071003a60380c8500344964107120a02500f540740e40300000040c000f03407051006052b480c2101054906103285000d41e0920119031003c1203002c1111207403896124107241c0c00b02c01d0007598803002010107645000302450190010f0007214051501e412401c24a143d01e41c0100001e20405045441e1100024600401503081174581d00c021858800002444400000c3c1c82c2c3d0060540018400c403507442c0104102c4441d581 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 247979226 1250 247977976 247977991
    0x9060705070f0e0109060b0412080c150702030c1209030a080d0f0f0504051902280b031e0702070518061c08030601030c03020301080a0f0f06021306030b060306010c0605 74
    0x1800808140b08808840c614000c0c00801070280c00340d41001c4044080e1107150304503a072a40000d1100300f0100d2003e094501309140c100e544150760b0710410245908280c1c00c1c44030804412000310a00c504a6400401480242c205006490700000c10291286061092580f901c1c0d0550060303940e1404035150800900b16444030b40000146040c19030300700ca0644001006c07540788030f0796400c2000301740801401b504403d403d000c40c1c00001c11845500064030301000c23190605549030390040b400300740319503800c806c03000d4070030044520f07181d1400406e41c1c260440c580c0c004440c0034884a000c178604600000d1314100341c40c001042440c0d0014501c00d1204201c8006012a6014000f84140c0f800c2e120002225074040d4010040320390f6a141181c000f43c20740d4040300600e0101841040100041140410349400480c0d00c0a03480e907580d80c5e94100703c2103500c203905015204910015011413200d4258140108503100f58400340181940502040150b010460742c0030702141e81000d5184c00541c082e0301c8960301400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 247980476 1250 247979226 247979233
    0x1111b04021b0d0e010801050f010c080307020a0f05030c0d0507050d03051005100903020418020d260d0c080a1a121c030b0f1c0b0c071208100609050609060705 70
    0x605542c07a40c40c211602c10a6804900c080103c03100745e5070310400c42e901402003602e10000c55101d460008081101100000c3c10f1b4100110104610b10302c28031a80c080290030054000c11000c1c60b0170115100d81c45490305403124450081b0307080445000d002500e40c41c0c0c0e0028090728625810780d40a4000d030100801c400c2c1d58103038800000c04c0c941d4408426a03816000345d628401d0300e40c01e510500c412141c1568401c41c0d0102ca4800b8000140e89954100c0c1d134003a8042c012500350041c0d60581c0300c0300c1c5041c15184000f284042100300d408021070b40b000c00080c40350b0b40da0a1240d10343d2040301d4215410b9405e4202142c0c000c0c101c24450341059040c50740d06550100840b00c3c040c41d040d0855013607541c4003c0000c0041e03161801441c1d40d03c0c1c031f2340c19100b41010441ea80d0980290048005410302c1c00c0400092160b47c010300003400c1714110310251422190030201401e80f48140d48001001d000080318500d00454050801203604d0741302d41103500640f10094600751505070030004008041d00300c44411a040d10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 247981726 1250 247980476 247980517
    0x1051314041515080105090d030203010f031106091807092c1017030909011a030106200303160206150f060706020409020a030203160f0c14010f0e0c01111b0402 70
    0x243d0032805004080001c000113050420400881c24401c50901175010580180010b000b00d2601c0e100202c110380e0f10407800456030595801046041c0501c00985030b0101100c0e500c4a0055802241e01e80300d004540c0d11022404d80b212041b01500c072510560180c04280701c401603054081c02c09083d0342001042c40101607142c1e54955030b038a11092007041c41c00a801c0440c1d0041d0b00e042a280281c050481c0903401ca14098030601d1060042c0014850102000101c17003010400e40c504403800c0004d00b400b10181c03507681c034220032030160031030f00001a00018030500002a15605201c1c5040160307000041008074180a01b030104069504540010345804d0340c20040000d4080082c8000c109445107601c01507102d02d1b00030511551104004000018000e9401c000c070240c603171000c080f108150f0b00942c0c10b401d94148010440c0100866000042054504000c5401c0700200084110101030f00760383e0b2004c001c05440c411911070382c4c02041241c11805840241030285440c0e00508555100c1080110402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 247982976 1250 247981726 247981751
    0xc030103080901051e130506031b16060207120f0c0c0b0a02100204121110080f1b03091609020405210a05120703090b18010309021314010513140415 65
    0xe44946000d1a51140005074003511b0001d03100501004242c211001c905519201c0000080c03441003190380301d10320748001000305501e4581c03414541010303008034045484808900d005425448541e074a04042000340c400481b2a500c24101d5071138070359012045a0001b1f00e460385000e40c680002190009502070b0070a00010140244081c1c40280b406203c030301c01c18181801c1c000040340b4410396081c021580182401c0c0c1560700074401039005803a144107989180e03643d040b00381c0a40145410a03002d40000402d011040b0030000391991140b40039900c104189a880c48414124880c61155030340000702c10304200d104038036048242a0503648801546d2460390350356251400d10200340034114030604041001424540d0040c80000600021064107107084070070200311b416072070f4005c400790425407a41c90700c504540b1188040c81040e141e40100748030300704c402c111600c152002406020f0092800742c08145200f8201c0c02100e8130966411110442c6445989840100320515155040b0b4142c42d1441050714 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 247984226 1250 247982976 247983007
    0x2130b04060b070c170f190533090106050a05010e280e070c0309150216090f11070c050d1a07030b01030506011103090423090d170c03010308090105 65
    0x36403003110304c0c02c495414000344813500c5880481010107540080f540d4040248001010902d18003c3c15003c0b0901e00c05181c1a40f600e1025402e800c150b828559503614a000f0150f4401541003840c03842c400140c1d1144078050803618144256076004602600c10051940121041031249001420062042e084919403010340b803108102c03030000c642044001c128012601c500a6008501e40c505440c01c1d4000b61002001002d203401883c51484181050820007402040800b1408000404031a4619900d4880c00000d0504946503e0141d0410349001c11041141040f1b031280303544100110b28440c2000140214009281c5040f50588048144d446000081c0c6541c140710f80040e6801168100c081d10004050fa4005032810381800b1169412120180011058801035101950002a982080e94001c00341c60601400e41600d00c54110034400712a03c00314501c00301d0140ea0b00c031511240068410303550304080c116082d108a010034401400021900001800100310500d07000c1d0401410b011420b01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 247985476 1250 247984226 247984237
    0x11030405041505090a1401031106070209090d0e0a031e0c0b0c01090c0902070f0303020a17040f0204051f1e030206031302030709020a020c041d12030f010e0402130b04060b 75
    0x90005000e4010411458850b074130550102d0309550a104051584c0382d0702c044000103020007020440704c04084a12a291041502c0300e60340c0003050803202c0d091a506080d20380380b0103c650800580304040001c01070800012240440c3c0c3c2c000c1e075012000182081600c5400460b14003280c038603880c00c47c0010034004440182c040369990200002d051812468111000640f585c0420032080c011701020010036405040781100c950517003030241ea5116514411241516561588007418942c4401d1100380429030451842d454400d4504000300e440e15081d984c0f500b0345500b24000e0b9030b02890420b20216100d41c41018a0702030623204954015140e900058440e08211400721182c1c01c400c1d5100c05510302040843c0007020302000441c030b480d554260080d160b2050001d11401191030b0407440400101c0003401102000a040684842001110340d181e219803050300c0004803a85a9000801d00d04105c1301054090f540c01000c1009610310611030b00050f121450342c0340d034815a118000541040b6104c010103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 247986726 1250 247985476 247985501
    0x317130b160e0f01020a12030e07091b11070308090301090614090106060311270303030f090705180f04150507090f140612090c0613090b010206070f1103040504 70
    0x4440c0004075000384400d255007803240c0319a2001003140001d07600410700070729190b0000d4031895103500001054000d400b403400034a01c24400d01100113103854070b59004055010809220803804500072504940358606d1403040c003025000759a04000003103a80b00180400b80340600041341115454481108487e81450071140c03900c880020441d12000138480c2c44050f25035820204840f9010b2003100d0418015101c0320000c01070880b0a0114400d4001c080340b160070801000c0b6544d07031a103e1004803c200040c1d4060742140b10b031010204592400d6440010300c0e85d00250030124035540c2468048400341c0150003500c005540e801c803942c0091260103024460145612200f011230b1070095215112a4990300c106141c6800758505481580c43d0021103d08141000c4100c3c0d2a46072041d1103414a01c0018050394070610000c1c8841030101c1302c54014085414042e030070070a0301940001a138594508803a40380c0003403030902c18040c02e5405040510302e900c9000c0b04507421f1907142c0c004034049584410842 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 247987976 1250 247986726 247986751
    0xa051908030f04061116050c0d03120b040e03070503040302330a0e090c0408070905060901060507020310060906050a0e0f041407050a030c080d090f030305090f090a0f0b06070317130b 80
    0x1f072003c00c1014941c1c13002c060f00c151024409a440003020107c0714020314606540b100b00d92a22a65280c10900164207c001a60380c2c444051819643d2a400741c07004134040e000c4d00074101000d940001013480c4000c0d0802240810018801e101844c41d0b0051351a4010b102904110300c0041e1648082148124020040550348a007000c083e545003030580d0780000c0d012130901c8104a00c0d600e84a00f554111078003800c2c400c2d1104e00b94400641810005003480101e20314111002540c25019080003003100c0c02a81c000200c0e035105c0300ea01f60300c400221000d0124811601c04500012601e2845003003450180064491aa80b180001048108543c0c000c5d50b40004c03804060003022001d204540034903425003071420140340341940341c82540042d071101500344480481c45078031070740320000040d500980c0240214500d00c0c11085010040240e59207009000346004100306c11030030200102c890a0f42c1544945d00d178041c00107a02c1c1c28040c030082100c0003044a01e440c510000b12a403424038025174400800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 247989226 1250 247987976 247988017
    0xf200d020c130b010e0d020109081902010e01110c0f060c19050105010603050f07080907091107140c0f09090a061e1505010f1209050d020a051908030f040611 69
    0x10030071203a01c002c0040c9281441c100000c43c142ea00b0200f003002600041d5417445048079580010780303004040e0350042c5107601440c030b00d04402c2180319030b11724407041c401d896a0304000d0300640115442e202c01800100386a00c080b401c900d50349028484400f8402000f41b21500d0308440d00b2101d2b0400784040000d01c5e88404c00340c110010840f01780551400741a040c60308100610300b030903e4a44040d07015080030107200b00040030444c90381d000d0000c00c002d01500b040602081c071710500c1001c050380c045881501c1817180000c0c0280344400c08110341417000c0d401040c1170045c003515804c02040c1e0348064400d1410344035515012000030094000c800d2020300200400a0002140c0060b5003503034190002c01e03503c0048002d00f4040b50fa0040e030f007208001c460307140c81c195450030f503816100180003682c4050003900c154020001c1d056800039012a04a00c40c0c420f44007074030702c0d00c0d286504007002000c0c0105028001c0c00000c24141806d9102e035403040c0205004280802003110030407090b80302a80d00b100b0740044010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 247990476 1250 247989226 247989229
    0x2040f03061d070e0a02040e10080d080106050307051b15011a0f0d05041b03050601091d07030b091905010c0807020604151104050303040e09010e0703030f200d020c 72
    0x14429442240c06103800e02c1c02c10401101d03440304028010260340000346804998128a1030381907501903c140f550b0791005003071000307001c98191100c1c801c0c0038035803003104100b007500c921800a550488040e038490504546070801c082c2c50039080000a144c000c2c02084100c20344000c1000800030b41304c00e0117045c1880c0d5060a00e10703280c640e01c0001c0070520034410040c201c04043e0080407620b004c80c21000c001001e482e949010200b40841030100c0800d07034404030002c414810040350060403035940c200200440f406c88a01c804441c1881c6500d1112034000c0c65080001c540d080a413142d010511005407210702c0d00e25020749d1503d2000701000e0b130f03191b0340d1020112540c030340040c50720750007a085000809a62a06a0f0742c0304023803494403402050b454075601d0850f45071039000169006000c1c010709598841e40c8901e070703400c8055012550020290b084c5501c803c82e903400801e055081e04e401d44d0300e0400c0c20365000e5040d00e440035074002690800154590320194000140020826030300140c0c090002d40c01d4400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 247991726 1250 247990476 247990481
    0x603110306070e090c0408030d05101202032a10050403030207050d0b0402100e13091a010f0605090118090207050d0318061e06030f03020f1f1e02040f0306 68
    0x814040c0d4441030500080c0c40e04030b0000e02038680c0c202c40c000e03150743e00c4040e140e103a0b001e2584080550f00c03000ca1035100c00061031700582c1c0b00e08442280f000e486e9035035003240c210280c108000079402d0b800078400482e8078484070042021401d1200d0340d8201e00c1c520000812030f074055a09034032000074001300e002c0c4101503050110340c0007170808841c065621803941d15040d011100c09040280f04c2c02007402d00c540403d0040e03101c107404800052030a040b07841d40720803501c050010503c040300c0b05207480050002455880080320705954100700400816410a90259180da0000d0005418440c910400c000f480c1d000b4441c89001c1c00b90604090786405280c940b5620b80b50f100c010001c10b0508101001c10000c05942c01e030390720250000740209100c4803c190700e11000040d200b014180302d082140c0071040c0422001c607411443e11035821280001c5802014903250603c04000b0065800941003a050030003080d00321007100d00205048092000c116945c034002c980c0306902101c42d0703901c505820010b000c0b461 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 247992976 1250 247991726 247991753
    0x50f09210601090e0114072d05070b010803070b040b04030e030303040f35070206040f08010c0f050702010c031d1002071a040503030403030804080c0d1205090c0d0b06040905100603 79
    0x1b4842042030b0380b0341044100b0000c1984c000c1080c00b044504c04203c03501078031000501c4446502c070080d40d11900c010501e50001c2070580743c8070b010500008454400000b11103449821000000d02526580ea0350001a83c000e003059003080001c150b00c03c1507076018401503002d14030504140c102c0b03003050329081d90890664100c60701c2464041401d43c0c1a489a200b00420f45100c4900c0d150f5030b00003610000f8030500454104c030310b415040313850100d4140015032001820030340ea625401d02118241000301c845104004009002480ca0920a00020700407419104807010400510025155000110b5001d80180d00c810006a014240030040240b441030b080007941724040300c80740303000e04008c0425aa8403032417100070104008000040d00340080202600d0401181d0b0090362001d40c405038005010200c04402d48106525050204100e0034001a521034110000b1b0305840a00d40107444400101d20f0003400d4680081d1103640e02400980c2c1844004074901038004000751460440c01c00250f455000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 247994226 1250 247992976 247993001
    0x60109091217040209090712060606022104031712040b060a06140f0906040803070602030901050106081306050406020f07030908060903030403020312040f0803010e06011e050f0921060109 82
    0x2c40b55007444004402150b142d01c56010745007654035032205200685003016552108030101c0c031050a0a0801405800c41d2003118203e038200c5600425084440b0120112110441d2005004000400c00502100200e0b0320030584200220309104800603030461107102202d0885160080900300406031400b100c4480141007903107090111200c0451002012f4454660200c104000c0458500000d0303403041c0807a8084e00300790303055030b4a4001070b24011010750001d6964121035400c0030000f05039a48511001480342100c00d14034401d40380262a504014203002d402610115004c000604500c001d580041210604c00d6580440381850150354500b03000000d00241c010350000c000780400300e03034000241c51000d003554403104900d0302c0d146003481c0841d100c0c0c0c4006200718404000014083c48180020f44210000e0300d0b4500c804c40c004020002c03003858840040b0115906114500e800c2134503502030f104480d406011209442c600c0303100b10280d0400ca406ca0a80f590100c00144042c401c41d0240c202030448 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 247995476 1250 247994226 247994237
    0x6030103142a0a0e091005100b120114010806060901050904060e01150e06192a03050301050f0a050a090b06090904051e0c01080c0903011b02030a0f0908030304080c0304080601090912 80
    0xb09a070a031925900c03001b40b112442038880021542c4585070064240003000701000b015921000130b861180800c40c02d101c0e10f91340d90580803411f003455004540c0944038280080c21140b600002c40b0064030710b6001508656045961a500441d0000c0081c0d101406080e0a454450440d03041c80300081446a80f200304c1d9002d01418001c8040000903a010b040e0224030f2401c016030070310140c103004104100210b0441c14a042080000024941c1140003941a0758058604401c1d0600500900007102c1c04e84c803581e40c02c080e41d048200b10285107036000310300c2480e000308614035141940300082c4034402d0030303501034030305410592108003141c9a0500428a20b005078010306100913070140003030844003000b0004485680c0c00a04050a645c003036211031855242c5507100780000581140003135690f00f02007503050100b9070700d030031402c0f096026991030300c2115252070044d46540e88555400880d6084000c00c074183d440240004200c0c4c0c035050061702d001c0c01c1d41e5a40010754000c5428560500c0e00171100e41c205215 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 247996726 1250 247995476 247995481
    0x30e0f030708070f02150d020d0e1f020a2c0f09010b030708041707060b0906010309150f0b090c071a0f0402010c0809120606150906030103142a0a0e 65
    0x2c080000b6244803039000030b481c2c40b0108090000c03881960a001001c602c40d200040c11704250f070b0703045d13024281440e0221410000e1444070301d4440e070740c1c1e0301c2500302c1c610b24001c1d03a0942c80100c440d03030001c0840001c90b03d007d0b840c801c801c001d65002c0303442902d1202503c40d5900c0d00348201d0300f043e01a000c0e8480c030490300721205500d0541c846203d80310280446041041e01d500050501810300c00306032075a00c00e1554142e441c2c100d130400701e008001c545010b62091714604042a003643c800e004440c2c0039904001100050311011403031100400d8154043c211103500c62161800310b6640c495443e20070394450907045c0da280014509031440001c00e070700313041400200c44184a6020302203130b5110b90059081c03c1c6040151b100c1e040c19200b5010350801e00354850960700700e00000107008110b040c0145000d49070211500301d00041d680d003500134139040a0704044140010004070380c605061025443d4030b4011346500034049180c809085150000035404050030150b90181030a0410f000b100900244003909001e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 247997976 1250 247996726 247996733
    0x6040213060525081c0b061b0c0d030908010e0703030903020f0103090803010b04030506060f09072312040221071202060c030a020c010906030c0203030403050307031b030e0f0307 78
    0x8070701400781007180208829000003070b480180c49045914a80e9088040a54a072408840d4001106840d00d901080400d0000c010140680451480024032107820910703440101e080c40c49442400c1825403261241e400059146c442da005c1e0401e003c2e1342c841e00032906214540f825181c182c00002c24540c0444da003080800c0c0e05c0005102600d130b0444802004080640c012409400780040c06800c01c0c2c40000005283d6038400000c0007240e12900949081d99507400800081180d5074543d960403004180000d0002171148011a018a40076054100c41d025050442c140540018141c0d0300705208440501095290145684000281c01d071120f2485921207515603803a00c0c29441201804081100300d0411551948240d07100c08113030108983d00c905041c1c80013540c40e0701001c1c0460204842e80c2000c6000c9221b806510748042c0300b80c000b9440e40d1616035041302c956200400f04001c0540e80c2904c20444010507285408551080da00420b003161500c8031142090084212804282d200b0083c11002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 247999226 1250 247997976 247998007
    0x209090f0d08010e04030f02160b0414180c0c030c0d030911060c0705130f150306151d0c040e0405070303080106050901080a0b061c09050c040501061707030e030708040905060402 78
    0x12642c5464038a00c481c54031f810691829008103500443d60010b50740220b0102903100144c070494020304640b0488052000c188881c24103c90850031580390700400188050455000034151200365600320392510710f000c0000b0f800d0a61a01d0b0742d40000c0d0703d5110100c00c2c880c88c850000d05c0d204007250f000c0c0c640040345e4103007a9a4600ea01ca00360041c0d000c896040305002c5d503980b00c1020214500c13420300c103141844c8003250340950540400c41e07903249000300300f03511f41004a90040a4403800d0701c030405455100c080184100500401c001e020b00800c20000c901d9040d581c00c1076000b075104100030000641141f80140a54070305030400401c100d030900844115a03071000c01a900245204c0b40062a0b5915074080303003035403140780f5031074265081986003005909101d034045400c40b4080c0060b100210744140801c81610303002e100d5200052100d80380c8000c11482c40700071542000c40c505000608074401c01400341140c00078081500c11101c0403030200f050703150038007805c0e52001c02281d0451801c0d00d944000b122 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 248000476 1250 247999226 247999231
    0x306100e011b05070911130812070b060f0406080309120102031e040804090501120c0807120227090114150a0308071103120705010b0906130b0103090209090f0d08010e 73
    0x140306062080807010303c00188544005004500f8052204040c48841d103c0198066107141800c008031000000740c1032408a4041164007030001d03038034a07020507078a4040390074001901581d0310206001c00210790707584030300c2200d00411518016503102d02900c0c0c1040040b00c50380612080ca64010010445401000d01401d02d41080580c4c000172146c80380e00b488071090240c1d4211440f0300345008004901c40c00b10000c940d500510400903141c0703050703d40d0401600c501c10342c4640481421018030400052814075150079240d03055070320752486888041d82c3c03000b0005050390a02e01d40d95542c00d0700411008038850349d50703000300d2500011100803451808989203100318840549029004141030042003482c140200340460000d0860355609540203111500d079100d020304a80a43c81c1c04200415030410b011201d00c905401000005500307040d00450028001e00c000041c105035440d045080143d90700101e090085031050b004104804500d07280c6440c0402041c0c410742403041e070100400c401060700e0181c0e603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 248001726 1250 248000476 248000507
    0x80a1109150d021201081c02060c0c0a0b01090c030b0f060d0b1c0305030a05330301150b070506060d150209040902060309060a0c090b040306150e010b0306100e01 71
    0x1400201c1c100c21070203180161890800c9182c0000340b0740d912624003001d1141a50b2012080d6082a19100c0300208000a42046600540c10a800052101d4011406441c2c81940c850540b40c64507015035403a010070809801c40c5002e2560340c05030703421041c6d00d072142a81c2000c041d501c40e007a50706c0d910b00190030b034064001850102034855400c81081d440e60414040505205c0240c855114120301c3e018203150812510040101e01d0070000610004d540303031101c03440d501031a01040440b58010210b0083c0d88080a1242c1c0640d00e408070007041c042e07940e41c40401840c0c1c0c2580305031134a03001c5c0b41142c28500081d24440c4a4080352070010007040030100317942c0882d00038005c0140d5034100754001c01c020f05041d00001e580302e05c000c010411005804a42d071482902e00c00c0b41000024030b252801d9408400718090000c65031001c0c40240000b980b00c1c2d105241c42c19272800013180c201d544520004180c0c100341c01c00c58225001009110f520b0400e040e0201c640901820003081c011003001c00245107860981020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 248002976 1250 248001726 248001739
    0x2060f0c040b07050f120301141011031b010b0f0108220c030506100608070f080a060902040303120e03090105070204020706060b160b010e0720011104060f080a1109 72
    0x28440c0d000d2030044a008004121680d6211041d508146403906150303e00c01559004440780801e00c0031800b002c072170685040110710032010048400f800241c2902001d004103011011740c540b804110300f00b01502174030081d91071240c00e0f00d100000d42420340e140101043d0084100e02496401c680c2c024040703c0d07000c2c005040ca044c40d0080c1c034448540491200c4000382c80c2200410011003840b102041c020300c5504ea900f1200c02c92075603106c04590100f02118614005a80040c3c030031102032159603825007041c034460000c80c2d0a5210804a0102ea00c194011404500c052091030400c04150103481c0400d6518406942400038220010301944980c00c4c0007403182d0b81c0001c0c00b000300099503000c03030b004d401c25000ca182ca640500d04c021078a02000d840c00c0d40c1030304c04103000041440801d16460300ca45440d81e11022006034040f030802e030b05100681000c0c030f01d540301e4400100202100000e00014041507441c0342a00c0d03a2544c001d0050302c00a0301c0c4075045030078082c0b5881541042011520310300e070300b031310207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 248004226 1250 248002976 248002981
    0xe0412080a0f050103030923010905011b0501050c1e04050d11012705130204051804050712050601060311071205030712060915120b150f040c11010c050a02060f 70
    0xc024000b040c000b0140301d00e007800110505500c40482c1064a81a440510380c180c1d801c5410102601e07800340c0d06000903150f21050005521440034020184004624198001002d41d106400c0d68000c07107001d40c0042e4041040403803005060090950340130703a602c1c1e0320301d09420304002c5500380d820300402804c02c150300d00500c101c0380d00c1a002030034041c00147c001c080601c01c440c05120294a18822a07210750720002e95107000580744e201f1030b400c68000030409003205840012200010900030401d407846c0c0207040002a01407100c40118161038461405840c0365814804082c0844030003110401c01140300313005010010f4014000c03861008860f0411680f039558100c01154000d80c0001d86607043e030b0500b01c0c001001605074004441d041401e80140d2902525001d9865480b030924102030142503000380403440c0340038020411003154101030000c14034506110041001d44a01d0205180001c0700b900300c08640721400e1040365112042498018909001044000e54030fa0340502044c0800301c00801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 248005476 1250 248004226 248004241
    0x7060804020d05030a030603050c15070b060a05030a1505010e070806040e030c070602100509060f13062009030105101203050c03160503070b1506180d06240e041208 72
    0x201200e065480404c40380e45c0c03a60080010094001c500c0304540920900e8080e0b00585014040c80c84052414811103080280d90b803104000b20f9800b502d0150008000306c804070b10f40d1010300c86141494000e078602c841503d24041e82c1011201c050348082200d01064046c091001d610401640c2c0041c0219400302c0e01005e8280c0003070851250906941c8684180c8400184440c0c0100da4001c06030008103082140c2d944580c1019141d0508848036501007003e03800081e10440440400b181e05401590001206200342e40482084c507402142a429a00f01203445082446c090142c42e80c01184401c041001078a02420350310020300c1400018280500030a96202024040058a48520b070310f2050007001811420103681702c1d8802c1d003007921101181e01c0040d11580c00b02040101c00e81c07024103010b141a100c002800c81d012120040c41d64003980104220002c51428040c004204840e07411146515002c10241000850030381d2090552020240810000c85c0c20425007020003096410304a1f429640c1c00c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 248006726 1250 248005476 248005489
    0x14060711012f01110f09100302070506040605010806180325020901030c1703030705040603020703020a0b15041d0303070c03020709090803060906040915020d0f060305012406020706080402 82
    0x480d00c0200d02d0040d26281102c1c0081541007801c0d480c4100200030140442d103c00045124628042170300f41c42c200200d2819051100c900d0820350f80a01e4010f040001c580d4520382048026a000c1e64056111001400818814003201e030b008055074040d40507503801000301036124040e03080d06084801d191032210103258100c0b00300300c0314564020441030b110741c0c5170300c0e00e43c1005029008000f050100207043c210801000021640104211340f5142d050500e400001c9000e5404420120f00314000c4841c40400a0385490f0304a0117410550701d42d2101c100804113200c1115410b110314000104d507020000c08541d008000c80c0d4020300d841c5006003440c1001e090503032511a49905ca9a14540340802c81c4082c00003d10145020304800c9a5401164a500c0b04210580e2480d2401605080c80a41c05400c0c6495aa00030700414601000100f40c2c1c840b100c902c441200c40992003074a640e5100c00c020509d00301c284030001c08480c5002e0014180d0790601d40000d68401d664058201802203040101d0b0a540d9040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 248007976 1250 248006726 248006747
    0xd0e040204081024030c09110909040302010b09100302090105060307031b17010e091b0f0a0608040c050d1a04030507020d03020a030e120d05070c03050303040b040c1406071101 77
    0x940c00c850b44005488001002002107404c511114102e80b1805810703502540c03844401c036030300b05154500040c100b0119400070581c035681c10213a114104060b210548a0b84006c07840785000f42c000040a440390818480c00c0b1000428114251040030f2003800140c4d80c010f815410340c0c0c0b00355142505c6e0354501400350024068095040e007a00e000104140e41d00340d00c001c1000814200b01083c13002666141c8680c005980c086c0c80c0c1e802990821800594804940549205402c500500b0b0640f90a0b100c00451002c00e003070b40041000804003004c0005100340031400c0d40040600741c032107031080741c0b0070380725000c40034645c0080c4003e03040d640c804901072500c28425504907a800070100710764901c0c640350203951030152000c2140401c0da6540034203e545845190703c819881100f0103050300f00002c040850f200d42c01080c080b01c175085030a0001c00803907000c01c0a18800c520841c030120035030a0034140844a0800e42e400b5a46008640802c0811a1107190696018a61005250703601f814003200503208403625 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 248009226 1250 248007976 248007989
    0x20d031d010603260910030b04110d06060206010503031806070c09060b0403030210270213060305030309060a060f050103051314030a0e0105091f0512072f0d0e040204 73
    0x91200210501c0306180e034500d0203010130501600d041840c1c218000d280d0140001c2d080d0300002c2c50000c0102d0324007940045110010040001405103c0c1c01444da140f60464516000794564845091000c9501001a140505002c40c011414070084800743c805606010541c0781c05141c0100b4030004006030b04400c14042c2003600c0b404d0003041d490301040c0d940e070b801074071081e8018810b00715038400c0c1200e548200042c0008995916002e4030f1100705400c0c0301c40c080d03402280c010210b0510f41440034168442e000142d441070010755903a05120744201e01e090700c080c0c1a0b0f001c00c0e00e414006c0000e440120105d2080312001c1c05c02080954903442c1c441c2c500507100307201030070500030007450390980400840107210000b41e544586404900340c6004503854005c1c28041c030340004402007140310600c0c1c02c18840c2c0003c07e20b0319003030785041f4142c1c584000040058580388007240764211021a0000d0302603940d040812085418041000d01942041c3d0780c4000182506c00c0c000c0c3d100c58190301d512a90105ca001c0e140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 248010476 1250 248009226 248009231
    0x12070f17030a020a08130b0109180204140109060b031905060d05010e060601090f0305060a05040f0c0807050117070215040c120c05360a0b09070806030105070f020d031d01 75
    0x42c036011550103940114014000200a00001050301c8810101c04501680220201c10141c5c01c0c01c10aa0003040304049401402c04136500020059541d40945229100008503040c490751500282d1415908103410071030102d4018400c008042007248a014100e020f40e10b03000c00c1c2c0352580008035014480d94040a00107500b0724103610200381000035068085d400031317a038509078240d446084011003d01400000d086402180100f140e9803001c1e00010313000782c0078442e122130349981585e07100041459680001459000010304020540e01b0078803054054501900c0c64000e868030000094689003814136210b00500608082401e01c501c100124010b851b40d41485c03070900180d41441c04402c80d86100c1c03140b1840611400c550320643c500741d00414016415164403042c2c2060a1001c11140002c0000304110342c0e8a08107031079540c3c2c0240e8940201610348440c28241010010f16007542ca0041c40c90f41804103200e04500c16550000c0c1c4c2d0146842039150010390905034078059007180c181442d040c071084d130 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 248011726 1250 248010476 248010481
    0x3060308250c06080f010806131b05090405150c0906030f1e0108010608010513032a061802030c041505060702150408160602010603050d1101020c0a031d0312070f1703 73
    0x94100750114041d03541088a0b4001d1382e80c1d2401141d58200490b0312407109c0b6021002c0c4000151000d02d690004811501c00000d03550b2204003084900000711425a082d90000c4e20703d401c25500c1c110007682045841d540c140c500b0310b40c440450410702c80900b030800703403222500020b21308600c2010103c841100c130b601d09006e80e5a5a90703002d8080d080c035014a403400d500e00301c007143c80d002d01d0000394960584c3c15140c59038107001e48501c0811981c00780490840c01c01650010300c001902920444040903401144940c0740100d03030060618024031404858000e41c174180320040c811010491640c1141c1040b0b40169440702c0b10720200b16228000d51b000720507804081004580c2140200e16156908642c0c0740980559a80c0c05040707007030324050300c005085a0444c0311001d40813807040600300e18180c50310700054642184030380f10034981182c040c0240c0c00542a0124881c8100450801440441c2e003180100351340c9007902c00904642c822420001c09807040c500000f0200205000c1c090b14408010110946a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 248012976 1250 248011726 248011739
    0x402150c060a0c03060e0415111e070c0605070f0206090d050303040b04030e0a03111c02100e0108060301110301090b010207051905030607030c020606041e090602120703060308250c 79
    0x41580c08140d101003170030524003003014000e00500e41d10540d080301380054544200d052240040401015a13243d000081010161542408040c0c3d14038081210302150340b6095403c0003604d00c480c503044501044801c121203800b24414052402407550100c80b1b03d5070b162031000001e114021400750060090001108200c1484842c0fa0301d42e0ac52030090301c0d0300d00c1d4141000c00300010100e5600004120f0350080c0c0c1000140e00f000201400c500c41f44a5891081c0c204070b0300050068507110300c201002800c001c14064095901039001900000258000d10819410101880660005015140e5015541d4401c10714030780c4204000c4004040190481c07000464440d001c0c0389150250007180c0c002e01c1204049024a07103c3e00c2095041d0b4261740c054203240e142c8404200180900a21100d10210b403800080d451300d20341c0c803c2a0005128010040e900e840c0d40e6003c200c3c0e5140200103405151505000704003143c40442211902c802c030f806801070310343c8900d1401480800c14440603282403541440480c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 248014226 1250 248012976 248012981
    0xd051810020c0418050708010c120c090b0d0c09050a0b0f0d1103010b03090606010903031e020a14030a02072108070602040f03061a031f2018090c0f030402150c060a 72
    0x75805002606c2080340c46940060a8801840641000401407510030811034101d42c03114262110900c2c0680c00d069442c041001c0c0c3c1c2d00044800b0a01568030082e086440b60000406001000282c4104030900c3c80c0c04041c89042c080c03054900500300c00081c1805415007103500c40c08005111f4100c072a16545c4840014402e0b410031038046000b4403900001c22515801400f10383c0c22a40d0595944c00c074001408030401d400540ca10f5504c0c10b51081c190480005a455181d080000c1500d0000310303165814024001e00c1c04000b0341c00300020b149500711290b5820301804003a10496001b010302503540f9442d2401030001e02c6030b58400403400100b5200030041007440e411281e0101c40240c0042c00d841554810151a902c40200e0303030070f125a2203190405526030f2504129468400200d8030351074038400f0701034492280d101d40d08181c0c21741132401144034540740c50b00110784c1040140c02014240350007101c12481f1840040c2000e03100303d09a00d42202080d07107480850f4050b502c500203480300d0303050040c209000b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 248015476 1250 248014226 248014271
    0x15020106050a120b012c0906091009121407060507020a1109090c0108060d02030a08031e090a020f0411070303050412020d0c1101090807030804080d051810020c04 71
    0x4182c00a000005072950f4100c0381100f1a030300400010718591910648040c0102c00d81810710740240716030388a089004240c041c05100d20102c0001d800a0700c1c026810508044803192401d18851a02940e9800b2612540b00996044603608100c101044112100d484c1c500809a00400040c04c1038100030341140e01003200305580b481400c40740741044204041000b804021600c00106500800c80b0a101d58401c5132065044078003d06100140c000b02c2d00428140010305405641c4102e00000f44882d440305c10f003800c3d407141c182c101030810905140c6051074846002c114068460072032140002901d0740caa90011000d4403401c480d455403800c0a10740540502000c850640300350707051600c400d0115002103598070100311a41d444558451680d65800002090a0141c504020900310041025481004271802640c01501d06c0c544462804020b940340c8401c0c80c4141702084000d220352443c2403040b081414071060110f1745405d40110741d1000720324200039501c0d4540d00c075051100054001d940d80c1900300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 248016726 1250 248015476 248015479
    0x40b071e02150112030c06050406020f04030b0123010f050702031606020610080610090f0207120503091009080a3b041b05270d11010e120607050d02041502010605 71
    0xc00da60b03a900203204d4140c100f0000500403442c1c12130b40381c0c000350590b80190340c0680b00380c4005062030100c2d2044281754025400464000d00e640e40184003039007035086103080d51035011b0300c001e1880d642140000d05e08510100341100740071002c9030760402c66405014101d00c0c01080410302030007980d1900025542c43d82940e036262201e2080d900400d0511010038001c0c440e58441e05160046407801c03c00d1030041214440340c0b40e180b40d00703125010018070107a000145107442c6070359407500c0e814460b51380c034280b1201d590722005a0f0b01d800c3e40c036030001c1d000405541910703d4a00f0055006041e4920765220b441e4601d41c62030044d483d040c02c0215200290950b89102031040d1001c1001001d584c840d01c0302d4108a40b2040e000c203805102c20038140b0140c0e100301000c0092090f50480c0c0ca0190130201d0460340700341a00311800c0c3c3c02d03910070011175603101e8805d100780c0c00b04a0b001c2034045001d688041d02d40101070242802c200000034025240c5941d601160000c0541855100d00c0c0070390940d00a008000900555 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 248017976 1250 248016726 248016763
    0x506091e0d06090210080411011101020409060b0405011101050702100902040f09080409060e0f060f0d0507060503010e06090f180a0b1009050c0408030a05090114070f020108070f08040b071e02 84
    0xe090717244200310891055034070100000010480c1c6c4015501c003440090361183d82d40d020080807a007c201401448014810f038003896480d14104800075001d00b01c40688503130706030300d4042002511036001030811036010b00d810001aa0000381e001013805400c860b00241c0c0c855003452060020050380c0030040c02143c0701c1c14002c00041d03407180300f040c110402c1541e245802102030b0300800d13458581201174841c5e40800030141441c00b0440c0ea100c0c1e00300b540c02d601410104801000400041070b0500b107880c0d2104045076500203a2500381d620101d4044040d1540c02505800b20340142055010850b201030150000d845902500d0503100c0142d10840314000c0e032944500f40004501e80000090988040c0c0c1e44110185080a1410708106d40caa04507491941c100001d142e8201d0110b01340c1001009030704e01800c0c1e080b14001040c00090725031200545540c0802582c5144800c1d660341c0900304940160f4005c14003401ca88404804079104a03088210b0410303007080803016500c19400046100040c0101c500da03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 248019226 1250 248017976 248017999
    0xe190e0a0c08040209060406150c060b01030c050a11010e1005150307030302033420060a120504170c0f06010b04060c0b0703150b0c12040506091e0d060902 68
    0x10201034411000080c80800e50b144041070040c5042c01c400ca03403151001c1d2000440700e55803003081a50400140000c1d006c28090300500342070101600402c6070490080c01c06110582401c3c100800b00d00c00e0305504020880302110f1007074000c10a4100d4294604e100c2d040310600d0401c5d07407646004120603111442881007001c0e00c0107183c2004a81e1780e00b03c0742c154002e035017040d901d004280b554000c0da0076000c00111060180c42481400400d070801e00b039000e20102404040c1c0c60002c001c80e01c1e00004164841c403000d100300200700341e00c840541139644401202081c01d80b254500480c0e0030300c6c64003e20b0038800340814002601080040c480c14071084010460320b031030340c1ea00480c134080c2c403550040c140002c0d450051000400e500c100c400d60480140c2c500042c040c40c8100e201250014190030441c0002c000003002c604e001e5040004103660a80034400f580381c2842c0030002401c51090201e164014075032946c200420010303490913684200030107021000000c40fa0315183c001000d112804038440c455040781c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 248020476 1250 248019226 248019241
    0x50f04200307020102070f0b04141209040e031c0221070f2a0c140121091703040f0204050a021201061d03070305010203010509010503030c100504030e190e 68
    0x40364402112400c00c120100c0d0411011825940010402020766400300f00c4900012048004243c0081c001c0300c10054070f04040c40c1c000c0d0302d8004c0d0140390503950b010802481e210165001115803580c0304490024442d01c070000d9250031405100741c0c1c65400d0720400c0001003a407035690000c20680c00490f00c54000300e5110452201c1c031000580e050f200180c10b03002d01c41001070003401c0c00044080d81d481020003100190054190869651038200ca001510200030040c11400003030000c1e8180e402d0034840904040b558505071600c2c040e1355440d07600e40c2c0380c3c400081802800788600da15949514600355880c40c050900c00c2080d401d1003401c83c0034500d072000003114610107200f500c00d0300d48140102180c03a46001d8088a107412000303200c109044d0000048445035030200b0000700118469000540c6a615290402402c500c0590040d4002e8208105242d034181c80801d4400c0c1e83c03865000700003201d46460901311090694801c1140e04959500c22241d994a1084048411189100f0102100f540d4401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 248021582 1106 248020476 248020481
    0x504020d0b130e010c09050f060a030608030747040213090605010306060f0303020607030e0705040609090b0a0e0a111503040f0506010b1e0304020111070906050f04 72
    0x405180e02000f00380680d1004440d94140302c41c41514240c045842900440c607444d11400340060999200c0c0d021390f11035030143c200e400c2200e450302150318010042038800c0203461039050340f0350185400c4441c840007240b119001c07012031200901d800c0b44000d280c01406402281d0220300604035100d0a0010b100f91010360303000f89804a16549507050840840d00543c0050b60f61000c00c1d00d0501c042600010760a4015150f450b002408159001600e801c0c400b9030341000750700c14148100028ad2520503007007102c13300e000d8004c404180d02d90100c1a401c43e5100b80414034190482c0400602103001c88103000e81008014107405401101c801c0d6900700b0390300840b0100c0399441181c0d851800e002c0304009040c003400316404000e2405407070603030780741d440d000303d4242c219400340000008085900c00c01e20f0406078040c3d08215840300e5280c50301c244c0900107078001c40303004059845450415113401e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 247841726 248021582 := by
  have h0 := BRFrame.cov_init 247841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 247841726 ≤ n) (h2 : n < 248021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
