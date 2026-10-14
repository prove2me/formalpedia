-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1407
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:49:57.385463+00:00
-- url     : https://prove2.me/submissions/191b930b-7428-4899-89e3-d60a8bd4f1a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 252877697 ≤ n < 253057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 252878947 1250 252877697 252877727
    0x1101030504150b15030c03180d0215191103180d1709011b0c060b03010203060901120c12030f08070c0b06100e130c0f020303010e0f0603010f050c03010f0b0415 70
    0x66011010441c580d44d000642c4141d1071006002d45a00302806069944625007401482c04d401070140d600b400c95001500916481c00c0c0c001d048025201c0c54018030440340005c540b203008a0078a101507209c959400d00440c0070b14451541d4100203541c2c00141c0e900c90810480e05400607000c1c0d1022120544940d0644c0d80040050300005020003400c22451320005a0205001c04640c0c1088000d003800060312550500c5482500258078601e05240010b00c0e201c814064030315020214442ca4090060a480c80c102034050110316015a050605014010124592070340c8001181000090b40c10342c841d0303560075615a4007040e11800c3ea1144002c0007540c20120305d05808014084020325a035580e44804c0580050450000103804028540300400b40c0404c1c80485055500c20001006621400d40705180c3c002d02505501c18030341c5960002901400d140049025082d09010a00030542040e20085040f5060701101c001c000f95941c50b1000240186d00c00c52040e00000740d10311a01d10f00420780c5e4120002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 252880197 1250 252878947 252878959
    0x204081908091e030c0a0311010807020f03030f010e0606090a050103021602091306050f0906060409060207020d0b0f060d02090a180b0103050a03031a130b04150e041101030504150b 79
    0xc50b02080e20b45031644a030907100d102c990a202d40b64101071245c1c010704003080e1902101ea07425511603200060303000300700e60304002d54680003812891090002c070b000b200894040e42d50301e00300150040c0361030b030b0280107120070082d804c404942c107850403200b04c0d220114064482200d07a480c1c14010f400a4212040c05800001680000401655080000c51090070048103001d07803040942403040071900018100d00718201c4d6501400120080020106d503c202d0440d00810314843d1490030101038024444000d41083c081031a0000f082015452240300307005954541102da078031501000405c1410404c040e400440d4540131842608403034101829a24210342884035400e500e03503840101c180241d100f0f48003500300c0751910040603414000c034140082403402c6007000280900004009480c0c0741507400030300d40d441c2e0f90354526072142e81000307815074260844c5a850b5a0b48044120311890112412172300d000089008941c1903000344940d500940d00320314500d0ba0b100d13028051030700038051503000545c400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 252881447 1250 252880197 252880207
    0x5150a020f04030501050f0a0c08010b0306010309080a0c03120c0906050c0c03030c03070c050405060604050607111003020d0e03070f0803100801051e15150d06050301020c0c130204081908 82
    0x41e40c2a4000c1c001948140700000d01072a0103400c02d030300000041c0401070481d081c60520900d00c3e60092446043d11440c030707404c56403503c407030340143c0c000d008400b801846641702042400c21282c01c845814441740c000e8480001c3c001c0c0c0815848211465240717003002090100e042440307000e105501030110080c52800b1160301452000009207150840852201207a00002d0364008010340901c145000f40740541d004d01150070078070005011030140c0e0044c81c1c060580400c04000340305148914140b50396000c7c140120b42c00e400c900c018040d500c0050b9840d030403800c0c034603e444090f40c000300f03c0e020f00c0d401052141002c0440d41c1c0b031410315400036080c0c4020140600300803900c55028442c0c54002c11016020417448010125100b10a00b0300500d90081d80b404281050301c0d9842d4420f107100500b9039030290942d03c17000c9001c0c81d401043c1c0e9820403500b562000c203405020250004640d150460101c400700564949406001c007070344901d01400c0d013141c00100c00c1c40100289180c41d0544e6074840c4100034102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 252882697 1250 252881447 252881467
    0x61b030905090a06181e11070209010303110114060a1203140f0315030d020a0605060301110f04061112070f03140c01050106030b0411090f012304050102010c0c05150a02 74
    0xb40209072640459180d85110800007141e8202001a01c43c000c01e50a000c00170707042c01c1c20f01d1060205004c0e5124180c40380042200c0140700e8040320000caa00604142e800d58483c00c00420200080d542002d6540ca0401405800b4541c03164040c800c101c004c01060f002410b1100c800d80080f00c40000300d05111101c40c0c0c0f90b4896624101400b4041c0080d40d6054507880c0008100b0381c0151240c550303d02a03000300400b00a0b00e41d0208800703c2842e04013001082e01d44810002c2030041c0030b5030140100382c3c08049407020b11001c1640c0204102d5140343d85101d0314994030507100e51074120200100c0348842c4208034440000d4041e03900c4039481070103410910826142d80418045c80d034000c0030640c0c1a03035556401840700903094800d025154600b5036080014030340e0010022007910610b10850b10810403010364071080d0388509103a0300318660020b4021101038000001014941041c041d8a000d942442d416842c0306200307054030b000c1e00d500140100210310340b04145031180740c0050b003102852a0200a42000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 252883947 1250 252882697 252882709
    0x207050f131d03071104110d05090c040c0c12080108030d0c02160815070503010f1205030910020303180a080315010207031b060201140c0910050d0603030c050c040501061b030905 78
    0x2c40340d0203001643c1d45408a140c030090720140c03098a244210b01d409480042480e00406680310450086c10000310b0751244d0b103c4c9072030402d80d42a6a40d02c01c1c10000040d80d00707a4840000c0c04503912485401d5000806040185c50580007401480300d00e034010b020318860f80103a5004601e0070100390054405207211100d140084020a0f0490001035010107a0100051000010345912402a140240c1554108040c2c082d03540c1c2540b00d9500111001200041408018022130700c0d001402881050720080b48400a900c90300704403401d41d404124200c52140c04540422100307003a40e80406c3d02447d59075008400e41c2004020301005045128044010000a050340c55511840300310391102d1111500e8030710700074207403540040c0b891582814842409030225104060b1020803a04440502640c2924581140c413400750030300b00c0081c1d500f4580008285500322129080d1180114141d0745120394500074041660000e200d00400900c0411107002202c07006010a5203240c032900d4400115903a40c000608 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 252885197 1250 252883947 252883991
    0x90d080408160e0a15150801030b010807060c02040c0315080115081906050c210f010b0c07050103110c03120906130c0509040204090501090f050d0207050f13 69
    0x4250000290920001400704050720200180c0604058440d040610f007041d8010042d06583e50f07140c44604049901102c044983d01501e4000c002c040000b07003000005101718003c1c40152040720091002080e80100496100161291034440c944100c20300d6003400000c0c105036900701e04150b0307541110b140c070100720660711004154860010444c80d03151000101024030700d920180ca1503100850001c050b03501201d600e020b00e030f04014001910b6945a4400e40346214040000000482528846c0305120048038680d00070303507084001c4074450ba26804e260446114403d104901c40d48101c03401c00c441c2d8407a41151010690b8a0340c071070708224401c6021031460b000301c06206800001001000442403080011345e82c00200c82d4240748440d010f68544c0c0000711045e00503a4002c2d000c04000800790f440c0c03600b0240c11154810000c02400c201e9050059240700140800c45540c0200132503200d0180c40043c1c0c0e1015158000d00a6001d401848100f00007600c0c43c060240000f91103948a815400300250445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 252886447 1250 252885197 252885203
    0xa0b0d031709010e120a03150603230c0909040c051c060b0a060f0503060a1715062209050a050d020609060f1023030d0905010e0d17030705090d 63
    0x40c14080046601d211284010220b0702c080e8540644203442060004107228814041e0580c9569102c44020440141040a64250b4400462075000400c2d40d419846240d4055200001c0c2d00044251803180349000c00c1503c161a406400b480070144030702c0e00706160754002c0c1c0300350070501c40e069842011418494100a0007442c10340811081c0701802124080c03403220080803154820b4007800e14901802e200303000402082000b6020000030b0700c0e5110310b281c080260802181c0c07101d54102d41c0642d56903440a49546401e4003254101082d15410140b2461008505a5450f081d01d200050800c1d0000c2240b044c082c0d40364451468440e02084003480720b00800f03c100c4d400ba142514003103900500d003c42c081d00e2502907445020401100318841c504a1054881d02030070100c03007060f41030401b600c0030f0100040a03498000c240302c2450140c0c000c0d0500040380d02c2030700c800040c1d42c80c0d0340410903120300b1103401500710006100c1012100c05403400450b40003543c2c1c10010b0034104528041150031080d01021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 252887697 1250 252886447 252886457
    0x3081804051e090102160b07030e030706091101020604030e04020a0e09180607020f0303070f020a05060f01051003110d02070305040f0f061106070c021005040b0d1506020f070308030a0b0d03 83
    0x4900c2c46501c2c11250302c0315525000b03501c0c1c0458181022400310a01d40050030009184012a0595110f03410001e245000c038000c80c0c0c1ca41505c0d09180008181c0408c00701e03200d501107894000780d54000305049106039003503100c2c1c1c1d2101e4500300c02e01001c0d5004041c0e44081086110940c0c0060b030300c0c140440d000303946682d041110418020011851700c1d80162000c415948400700f0320f8480d09000040300d920110300c1c43c0c00319490000050070303482c0500d44d6000610724000d000c100880c149180d10600c0c102d840c11118075a0200c1d071b051003502110205600d02c46980c0f001c010318512104c041d002058401e2291408500d00b0359510002c010515403904003e00c115120381082050799403117010140c100c078181000e842241402000545201ea081c10001e02994103144c602d08858015410b490007444802c07146580d40c1c0b441c0303401000034040442d01c5450800c60140206d020703440044e901c04906440802031440509584808ac01a00001c1c4240000f07078949200401300c0d00c81d2104150014400c0d115 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 252888947 1250 252887697 252887731
    0x1009110f04030f0605100e0a1116030c0b13020603040605150d05070602012714030c030c0601050a0f0e150f2805090709050904081b060106080f0601090308180405 71
    0x4c10556a01074038482d18003500318014011003886040e0250803a141c200c0009105101c50078410090244172510484500760501c45400d15800104401c40c003846459049210360b101c01c0c880c4c0c80c104510b1000b039009901840040c000400c6c1d5400a81c1084200b100e140806810000061540340d108008484580040100300700a98090240210903c0407a102024103102c142104c0c000e000c0d00c43d000391042142070a00d000981c4c003070040f00ca01560a074280d0360340d1003003c0c440035076412081c13107217074040d04400a0008044e0380d00c03c11202540e0030480601c050742c480100b500d0340708144003c010350000e43c1440344030256440900071144a0300f5044c0d0403a510300c401d1802288070816034040b501a0802c1820410165440b20101d01660011141c510050712039060010032030007508800c944181d100409600d07002800200076040700c445985001480d6039000114100d0303c002d81310302d400300d091806d081c000a1300b8031010b0300314001160781801031b00350741070001740c15241d058401c9450000d80000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 252890197 1250 252888947 252888953
    0x506120307142e0b0f0406090b0102070509090a0b070e13050a05070c02010806061c09030c12020a020a1502010f06090f0c020304031703130b15181009110f04030f 71
    0x6450310b441c00c05140f01d00c20004500640108030030004401c0c58403542c030b0314008080d0391041c06407201550080d000308661500e940c1008000c0c12880005405441410070020f490703d4007049182c403864528014001140c1960350b4541c1e202c20251008003401800a004900358642d582c0008400000c1702c030118250a012b80c0c0a001c540000d070410041201d424500400350341c00003440da802110594440da516000b100c3d030307580000c2c20046022107840c20a075503942803542c06000b10000394007400b200c40490b50040341c1641d0f180c2036618000e41201c40d4007000c001c000d40079461042c54108600001c40d189402d80b41c4d200c11200036402214120b640c84c00e40e0f00c0100540c1c03095072a8500d89000440c6031500710380351812344548652149002c0c04000000842400f2249060b4079495800080081c29003071148944814031141c1141d140aa0b02c4c1d101e0305540700e0400055030780243c1a0325412044941005a4800941959560800c4080c4100070141d0422075510040004500031520480455030743c0c6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 252891447 1250 252890197 252890203
    0x140d1e08070804150507020907051b0f0303091e1506040905061f05030106060e090a11120106030b04060b0912030c070f09060e0c0d0b0a0914090c0103060b0706050612030714 76
    0x2007613000c020040c85482c006860f1904000e8000103541401910390405441200c051190b9140461081c0a080891000c20000101450003000c02d10191506500c4851501002080036124444203900c811482e10500025221441c2c2244c0013410105104d01d407a25610b1030903500b55011040d40308950000c0003102c48803107101016200840003131001d21f01e04540206404d0380080790f00d00c90903510011070b04040040c2e100b540700190f20180b050721061a008803001100d02441440301003810700500e00c0341441c0501c80c6009a42e45182c1e1b003801c02a030076041c001c108401c1c0101c50f84612041010300007200c0200510b01c01001050481050700341041e1010090310330302d52000c0d101e4000079017800302c2c412191b030035581080c031400c034002114881000052101d05280d48840c1400d460200b210803160100e0741400d1082c00e9900c116608101e24600450413240148204030403204c00780300300f00006485401032900450002c00c0308a404844110507800c40c1d200c040cbc101c50f1507a4213078050701c10f05014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 252892697 1250 252891447 252891479
    0x12071403210d240905150d0c061b0c090b210703110406060f050d0615050d0c0207060503010504020903070b0a0302130608010305060703090501021210050a140d1e08070804 75
    0x803d49010741031202c508404004054080e03020080d4903000060000d041d42540d401c140c1c400101007a1f006152030800750046007881c0100400982900c02041804400f130301160f590a9101000740e2940303103011200402410303203405289c0d000700c2c2c90f08145a0020500000313141c400340e41e4013401c0740c85c2c03039860419050001c180000c0d00131410800100515900610a059000702c2c0382000365450449009800c0240f020390042425000c0ca400d468508035401000350484181e03811040003c002040026a0364444a210362800210304000502c0701d030905030068800c40c0f00103070480303407519241d5a4842c01900071040040010703602080d14900c030403601c141071000303003c50f042656455046480b01603ca0b00000c146400741501c40d0021020000e0941c101d0741202e0110207003003150b00f40a050302c1e211003420b204061080c031f03031880085988000d00b08801504040200b032507003403611566560035030038041824442c0b8140e041103040c01141c1c0c5107009080030b610948029640f98184100c19103d2010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 252893947 1250 252892697 252892721
    0x9061205130b0618130b0105010804111003150308070c17060a1a0d03020d020d03020a0e0f0a080a0b01050316030827030a1a010512071403210d 63
    0x400e000d00546100411603000180d4021401105581d01c02002c100b0600e0040c09000840e1300950800000b2041082c007549224411150168180da0361801140d84034070035100034003590710b01d140c040d060b131407c0b08003020b4881003803c02051031021000601e032004210b50080d50341c01e400094110801040042d104080c01204001c0f0002003100d01c09990b4440c8004c1c07050018130340d2035804e0441139030300e541821064080149204d058016a14000791600210ba43d40c2c8094460010006815402402a1103a00e81650382e030f2100500e00004102d140c10b2511030840e080480d0030313800301c1c9024007480392281490103044074004652401c8207041c501542803901c4021402d40e503a05100181c026400c40e01d41000340c0f090000c0101c4080c800600d80081d000508d503052044030408010010703043d82c850048100d00e20500120382c2e0350010300141c00701001c252400341e004044140940d603400220701c291080003500300c0d03100003101c0c1410210140c0b00c81c0f40c4500500041f031000c68081e07282c05070440c0255 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 252895197 1250 252893947 252893951
    0x3060f462405070f080a0e0406061214060d1b03120c120503010b040b070c0807060216091b14090406141009031e02010210050406200306060f0a05090a06090612 70
    0x40f403922448800c05681d1801001d4400024030b0944851043c0e484a000c1e0714001d100704402951004080c001c43c02d40d00f40c11048506180c0d0030081c01800100d41c030305c5010041c2031403402542c0c654402003945403402c84070191464070b00700130003c90024003a041402c40b4503158000712540e5820200c040035000c004c040308011080006218244010007520700f00e45101c0d29081c0c03160560300e001440c200860304000464800c40b900015010f500240c18030800400b41103803d8410b844201c14415114041540429161495268061140304440c40450202840300090500c400d43c400201038900d2030f80180820b28640805c1c5040e440c1029200a24610342d0800c6180689182d6403440c410000000300c00c01e26041a0801c015a4002c3c81891a40d10345954104802e24007490984001d10348110181d07404085040041c1d101640c05003140d00404006040d40d0900007014810400c0d40e008103550010030009024a0405031180d00d6100090205074440340741603800d08400038144a4031308070401038a8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 252896447 1250 252895197 252895207
    0xf0402032e0209060c01050a020901120b100809031b06041415010b09060d0f0207050c0102070608060f0a0509190b030d0504180207080304050303060f462405 69
    0x140710300207080c40c400c1819002d601c481c10000082e1031070042c204020400d5080504010417507045500030540c6040980721101105803101a801c215500e05020301c0d08041003800450030240522400f952002455049a16000310303146010b0601e140040b042c0c6042d44204244030811156080060300419001d0041070100240e00f10f4080640040c07007840727074082d0001104001c644403641203800f1100580c1040c880300b10701e002e2a030000d51020300203440600520340c8580e500e40c0301265030400c50780c40b940d030101b86849800820035042801111507030b004080c1400007806403120341000b03100b503913220398900e40c03828120080825194800702241c400c2d00900c1c4050045c0d80c01009840a580f04a80d0b100200d00f842c55160f07009205d0210041c111640c08020003040203000030045104103410307207548105100440c10301c8605969585480c5100b0520781206003000350480035a91040c0588100541140d220a8243e61441081d00f10000102c494140800c1f08036000c0d86c028090034062034843d00e40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 252897697 1250 252896447 252896503
    0x1518010c02100c020a0b0a0207030c0b090102060f090a0212060a0f0618051005280803040b07082811010b09060303030420031203060306060904110d1a0f040203 70
    0x102d0204000c00080c07000d014008810f644514240901030041d820b4400c0d500c1d1404000690b03600303001d120071941450325440c00f044024145050700c0c612981170b0002c000310740340c0d1181846803c2c0c005112640501c80c013585e043c0907980754461140c1c090716890141501d03041000e03200d0305407268208490340c0c05040081c104200300310741c2e000e1401074114140019180c0c484596040310305946601855014030f100f490401142c11440072585000d81800c45540499511a0140e4490013a84501405079a080c8405808941084020301d05c484105141d0401c00442e034051240c41000810300c00d00054864607110318226003481b40782051401281c034140c40740780c4280000d50307174400100002c204451502d040c0d028440051150408514021305450030070401c0c501d40466a0411500142b29200300300208045091510500d40074a40000710481003c2e500700901551007984d0364201d4402084104101d01086845a043d01070303081c00c01001001e0401d401050b140440c070030300300f04196240c40904404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 252898947 1250 252897697 252897709
    0xa230a110c011b0201260915070905060703120603150c08062107081c030506040903090b0a090e01030b01030c0e0910090c0314060709060509010206061e1518010c02 72
    0x40322440b00101c52071262030310040745d4100040304a20094207040041c4400c2080181405101d800303442d003182e4654083c041c0323854400038107441c0f2802049440000703005600b00781d401420580e00a00b8038203224044080394904441c550751041e10364028410107a040403003580154a00c0c005140f42c110610300341100000d40080e07400e214811040c008404810750340b8801d010060007024070364290350013049100c90409186403140c5007100003a2601c00002c0003481e040c8965201d20741c050b50b5829041d4101030020f040f5500844040040c000311740f10000340391149a40303141c00307944540260383c8294514600702c0304c008119000320128880e44000c10000140008030308140c85040f03900490100309609000031807040d5500080e200d00e103034400c0104a00700c0020743c2d6004a485a03101a400c0f5a074910841d400d004055545005801500100301d480c908402041c681c03d6180d01c00c0070304180560700141002040c140c04e01f1103400003054441c440eaa490381e0f565403181080c24012124501c1d87c1c0040d517 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 252900197 1250 252898947 252898967
    0x118050a090f14010303111501030f030c06151415120a051b0705011a09010f2601090f0605070509060301030821090c0306010902040b0f0a230a110c01 66
    0x3105965407034081c03000c40c229008004000348041c520f1000d542c41e420020210402920052418400c0c04008046840310300c9040b81200c1c0c102040034000c4c1403596040300c4001145109469043e10b40780b00300c1891824081d5003000f02803602c0004a206000307002e00420842646a00740d10b18014022403203111000a4200e5002e00d01c110001000d503101c1640d40d803041c000d622120ba640001003800c01c10400150711601150030700000460007100c0d4441040b901c80d409008400202c26424000c0020b070b00f103800a100002c1d03800c04010041e81c03041c07000c2821280c00000c150303a5a840100d06001303120b00303841601d03003051705460849d203032294401c0403481da40301c10710008007100c0d40090350681c03150080d00c03840c008042250740d450050500d4890b65075a0f0092034841c038401c2c0944400060707100410310840b030480303020315035150421210305a105c1194010315016402d014428500354008900c007401030004400182c2c19a89032503403d10018074180c0a88002040ca500003500300c030480e80c204640b10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 252901447 1250 252900197 252900209
    0xc0d0f02180d050f150a05060f151e030c13080109030c200409050c0f060c070618090207060f0f0b0a03110d02090103111203160b0601030608061003020118050a 70
    0xd10928583c43c0051070700180f280c80c3c903100d00071100c101752507030300c0f81254a02800f080c0744103110700d03240c0400300f0901000c010740060380300105064070f410403003d54014208000c5000c0c00066020303400381050031503900407149541c00500025030308000c101d02608504c0a440c48030000c024503000c9680252645086510151024104c083d510a07440c40204011441d204094802e000b4008140341c0710b0b0f914005003600c00c1c810640340010b10b015003810310a40e9001c40c00c4500404c10340d440c1030029600c00c680801307841402954068085a150300398001020a00c0c41072000013415045080071000b1603d0100d90b000d0f516007460410103440d62401100c00c00d03650010540300108a0140010b0300100740700500079048a407a000010a0009142400c0c01204003542d0303903900c10342d10708450707502e80c4200204040304607142694400070900104da516400103041c100014950f03218540c0303d262040403658065003c1d1600800e20031035074095802c1404416032805824480e08100c00141000b40314040c032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 252902697 1250 252901447 252901459
    0x7030b012603210703090c180204120507080d080c0703030515040c0207091401080307030f02010b1c020a05030102031902070606050d0c0f05060702060307080901090b0c0d0f0218 78
    0xa240c0c007540540031a48440107041202c0da5610b5a042d00e0707503034403000c520410b034840c50140060000781c020f02070760202c01d503c0022000c5260811070408800903646040745030f000d50900011500850400d601052180103000808a41b45002c1c1907030710344030b90348503881c04001100c41441244100d202c265a84660b0504002c26980e890b00d820b40182014580d1440e403044c20000c291000d6500800d80b181520044441409640365248818035101428071906146c5d9004008180107c2d03c100c07410314100000c1d10012032142c0000c0b00103180c00c3da141c1281c1d07082c02e2600c1441411860950f0301d00c00204001e400a41c02d52030400d00d11041214031456544060382c0008103541001496072080c2b0151800400c0074401400c1c50802821201d8140180318011040700c01c00302e0707546002c000b903270b103c503034010f02091550340c525104441801010380ba5420070764a41130040000382c00350a406208581115440d5140c0f00742885590075991650041030103e0710410000d405944200c1039002808026601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 252903947 1250 252902697 252902729
    0xe0a0809010305071e0302040e0108010504050a0311070905100501020d0c03021c021c0807080c040b030a110c1f11070b01060f0513080309010e010201051306180c0b090a060207030b01 80
    0x9441c000d1107170750208210511444a80310300c61701580a807082d40d62003110201643c0c0c84182d82030883d5000d40c1d02902503400b40294a00280c4141024001005c450082d913000b42da03944454400d80c1c9007541e850004209540040c40076503810080c245c00c00340c092400b5003c1010340d40740a0346801517640391a8299040c8114402001d0080000c0e107420b04405181c1c0500103400ba0300240045000e4410b0000601020042502256040b00380c4003615911000c03289541c5840000b0300080c0181000b401c0307044010300c04000011018099042e040c500e440d8061642d4094070603803011034002c01a0b0300e651a9040c00b42a01040003401c01e141550602d00341501c00d9110340106543d240500c2da4000c0c1003035211f44d00814085004001b03411244000e0300c1d14100142c02100680c00d8843c121087c1221409050042000c18965001140c0902030040b50006a02658890802e03502850704078140c1c282000401c80114288200d10a00405892001c2d0843c00e04565500e22030217010300c2504190704604031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 252905197 1250 252903947 252903961
    0x10f0c0806182d010314060c12061c1212020c060c0703020c19140409200103110c06040212070503100203060a230405070f050a12021204030804060e0a0809010305 71
    0x925919036000f40da450034801c40005001c151092400d00045442c0284218902d0340d6640014425005443c2150003070f0038581c00e90400014900010b000c107074401c0c028524031070a00c02494400d5642c40c06648518099036801c64050700061002d00c81c2c0d041030707104005250f040840800c040e41c210b989916000c0d40c8004a0a00b00d2602008510349a404140d0001c400002066500700314102d9098002c0181c11081c09001c00c000c0fa148260b02404c001d80840a4034440760f460003d458890700c0506002403000c0004000550542000c0b020800381d5001034140f1080d0710b06002c00301d9040f030041004004660501c0d02003a1206803100741d4861080d00071001c18044d80c0e40980b12400b501c0d0300b9000f00d0300030f140102900078854009010720f00651514000c0b03603100d40302e40350b110200c46030f9032200b0f4500040b070300044808804060080e078000340d081c40344680c00030348036990f0b9009901035a81e92026060234104202190104880c030001c1d42d00c5405c104c000903540b40c3c15102c4410003420700040e1780c0c2d5400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 252906447 1250 252905197 252905221
    0x301060203070b4503090a1e0305031908150d0f06140c0306040b090603060c0a09032003070b0313020607020d060c120b1909020a1b05010f0c080618 65
    0x328080f9410700500b02d03504003003140c402e001d20108844144520640300000051381d264030606100980107561b1070b0b42030081741e036000b10728030b0740340d0010070381220b02c581d40e0f00c0f16401e58000c1262001c0244121a8032200c0b03aa00c90b6049270020300c042011201681408006044001201c00c001c04040c41ca81484040c0300715680085118001402020514580315002070000c1c2d2086500c4c07803043c2e14103041d4650a05024055600c520b03000740003454681c551000412098104a890008110704d040000c03002a5161041c0f0311111055910349103455103040801d8105810f0360040321500030300748100040740c1600c0d0350500d02590140d5060390342e8040d07800415030200341d12402812490400004200196001403264a1040039100801c01c000f0504104400210b440c1c1c900d8180c3d5105401c02e00c0015043d50040400c0c204500381004412405480510141c0000302d080d90f01da50340303080c0b500c50511240179454004c0100d24000d400c074900040010018481d08402d0800d05022038005511000c0354 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 252907697 1250 252906447 252906481
    0x140a0e12030a02150109050f072312060a050d050d0c060b03030711090c040311040c02160b07020306011401080718120b0121051207020a0e042003030301060203070b 72
    0x180d041d2a56510700000196803104804034103c28002458000035006445100c0e860054090141d0310f0141d450701001144c038a00030a81010745a0351059000f40d4084a4400a040411603200865160b241503c01c00c5060300741036000d580100b0400c2c0d4080c0000f680411042c6103868241021142c40c4c00c0d5041240c014411170b00c0c815094400080d422060040d10251030005040c219080d68881e9601d2101a010340501d100061400d010500141610300e030603040505580e00d548111074170a10200c0360030a4625140d4010000d440c40018940c00f0f43c102482424090708003180582486a04c0000080c50740c04014003110400000c1c039648401074030340315528070081400540c0a8407100e40f40c100014090700a00c01c1c101c071400101441c0c2000f150511502060301d41013000382844070f140441c2c0341210703070051204030380c00702140a02045d4109104a25400f030f50090101c611510409616030328082c40545c0e45921a9205100400c1115800000c58644550001e0221144e4480c4a1040c0e01c1c9011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 252908947 1250 252907697 252907729
    0x806010527180a06090615140c0106061d0414060105030a060306110406030e01090807021509040f0c020607020f0705040c02070503010e0c151e07050f0a030201021801140a0e 76
    0x1c1c250000301010441410b80e001d145041e80812440d95910300c0a0b04480f224400c4101101098400d000040d00030031140703803030300041c100e2645441014101c46085960039002000440c044000e05213a50f0303d00701302c403e40680141d504000440440c4141c411008008100034104140000003030700d014000d8200e10001c60f4030500c28040c3c00c9a9101c50300c0560894004c3c040003d00d07040c224084201b05024200e030061b0002c0090349001202c0e000e0207a00e50a032810840c00e80000c0040d0040b5407102d20546000503142130002030300001a140007400e0550103058041194001d4136503411518002c0340c2c02003102d0040310001155a0480e030181d041820f980d00903a410352825400385051400420301030f4000f001180e00039805241c5460111440c01200585481603a80e2140761081c0e044c824000d2800b54040d90441d807141c0080b0442919100d103130f00080300181d401142e1024510645621030a4010090911518112140009503010702550712200e04010320808006044e44a85042c0200569 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 252910197 1250 252908947 252908959
    0x100e040b041b0e0106020c0307030c090213030c0801020702040b1207060f020a051507021507020a030c06090605070e040506150f090f12150c030411120c0418020a060806010527 77
    0x159078038464101c40f100740300d00e00240c0150344640c2000d00d40440c0e0302d0141c9921901e04d01c0c4040c00c014064000390440449174440b80c03508940800800d4480d925400105004400175a58650502c1440142d0340c144c00000d02841044c8104900d082001c6428001e580d02860001035420000008925140c160f8002410342d00951484210305041c805010b40300b40525000c4801f103042c0415040301e000380c1200d080340144c04c00c00220002911642c591403580e40142c001040400a070f80f00e00c0101c4200350b443c400070a9044031801c10a0070307e802182c2e80b105040b600118180320302002c5140d14800c10340705180900300000c0707040480e030301c00400d403c06074000f500e82c841004504110503560b0010509004032045501e001801042c881000c90340305a034400c0c0100590201c0e0824408040d04000c0158082c2c0150700354858641c5a6101c0c1102900c2201601401e070b003403600500c401c08056420460800600c0400c0040d2a40c00c001291741c40e801d602d01319129250703a45c03640e00b0b1100002c1d10f455880a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 252911447 1250 252910197 252910199
    0x603120f05130b090909030901020601060c05071d1008030f0412140304120b1515071109090a0201140a0e090a090803070507020405090a021e0103060b1908100e040b041b 74
    0x3501c3d600500400c1c107081d10413034019100e01024a80e0f0380500c515090040c0d0022005100700c52007040c08009103440f41003101e98103919440c4002008028295502e0080104010000c28034074805a039002418840061741c0307081152103085602d4455030141d007520454041c003402c100514000c09441724841e81c03082d207460380d441e961031460301540130400741e80c0703020b402005c01d009520010780820304250090105151204060f14001b1503005036000380c07082d04104c100c2c10b65503210140d546125003e00390103015062021710000d02507a00c1d0705103000308120140001c90145410014194001000b107a400079180d60b0503400001800320b6190090034034001009101d001034100e8043d25000740f00316014412503840c1c0c456141d0701d42e00074102a6010203c012003000c0003c2605d0119030408042c5004602580c4482043c1da403a400203095010000d01d01c000010101d41c02808240c00c18050000501000c2c03030900c2d2403c02d940042d002810f00c0c00314001180030045120341c41c140c0c140070410491581 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 252912697 1250 252911447 252911459
    0xe0319030813262805090405040305090301050405030d0f0e0303062b1a07032003090a0c1d130c0302011d0910060e010507020307031e05031b0d030603120f0513 70
    0xe82024108401685824800544041301c0c0f4101d542401c2d201c1d603416003007618240410020b00780c0900700f502403004c02c02c10b2400c035480a01174540309500035001103541e94000e40440003111000c0d030b410b80303140307280440c1044003400110807650040400ca43c03e2641c4100340d43c4a8122191240044a012000b0306c2e45c0c8040007203207020b801105012181441103981c600c4800e9051b11401c080c04800e80d010740f180c0c9940b40760010061a040032400003129035600c420742c1c0d003d8142029411500c44025004142c1c0e6118000e0f605070f070b60005182c0b003d0920030002c1e90b140540140b07640070080c180000c105103051008000104201100c0c0000c00409030340c280380030350711460401409000c001503103000e03443c08103502582c115520301c1c0e805002490568034584030000ca01540c1c85c00d07501c420192492001c0416010001743c05c85407400241180200c0d502c0240900d0040b81606900500d07003000810008141c03d0500c0c0ba4035649070381010004004282c104440a200d800b254000e40c0f4180d15001c290 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 252913947 1250 252912697 252912773
    0x120406080c1b07080c04140708180709090b0405061810051b0415080603010216080306060c010213080d0c031e030905071d0114090412050d020a0e0319030813 69
    0x2007045e09540401120b100c13007000e9081241c0458034403000c034281c00045440448801d01140c40329104030142c0c1c00311a26408c1c2c030400d0707031140391056450800170414081800f0041c04115000240d40816500b0034000342001c2c0c0c1c8070344001042c2c01031070741d0f1000096030400040c2d00d11041c240c0c0c04d00302d4503625500da5075000030505035034000c20002110030300000e5041c03d05200719040d040b10328105800c24030450342c81644c40d510080400f50004c4051040c003180f220300340050100c040340c0d8961070f00100c3c02c00000516241c0005080e05c2048441800302c40466000030194140c0d140c0c604182c00c1c500780c81402a00a8803098400410030311601c0e0340090300e14198510450740380700c07900705a000359a884c0c141081c0802404645c0354480a400c0110700050a0504003442810450801074181100c48402d001282c00014030000482c1194049220b140740c28040701c0003c048e81281401c202c6500c1e00c0c0241882001440c1c02a14072001c8190400d0101005500c00c1040541c1a0070744100340001001507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 252915197 1250 252913947 252913963
    0xf06070815150d1514060703020106050927010c0507030305130b0906100b180105070f0b0415050f070207060e0307180b03191e1113060305120406080c1b0708 69
    0x8161031912900b5140e13050303002d07500d208070340c4019100e1804054401c00c001c003541c0311900450035990b1300c0c903000405440300749469200b02c0180360200030600003603942007041101444a0400d030b9140c240c400c030040b5085020748011170341502d400a00c075035a0040c046000421a0b070058011030f07070401040302510000034164030402d200000a422240c0d5880f030325074140103002c0e103109040920480d0820651107a40902106801120400002202501c0319031424105840c16144040c1880e03c50ba507501c1c0138010326801200800700b180103482c190100945520890040740d041159002204c506540d00700b00c3d0720b015080311000000000b40300a4003000131b043d100503960282c01400c08940d2010a4114024060b03500445902c0c00079192030408601074410714002c9a49031210040d246580e114030006440e00514482c000802c1404c4d400c1107481c104800a41c0d103c174070001c1000344103040c0c1c01840795420402200d07005498a810100c4069031885c0c40342001d4044c8a82031000401e082d000400711 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 252916447 1250 252915197 252915217
    0x80f060a0c090506040e09070e0108030c0c011416060617010209040b06070b01090c050d060b0a1403060d020405060f0418030e0108070e100201090c06120e0f0607081515 74
    0x100e1503140c0c24068510880b54440d03140d00103001d010400c80b40c025010320550080500b13041d210b000b0384400704150103074000c0c1c10200300740e44080382140d050103041200600094003402c1460102001004d130f40c41920400310480710710300000f211041080341d40c0c0c110101070060f500180d1081d09800d50030324000d40000016030b118502b42010174500341000c008030b4053140d42103104801c079682410b10910190984c03541903000c1210030091082442001e21454014292402c0407681c0c49811200c02040302581403483d0780420b00400900409548030f80c11100c90507070691780860140d0364840024090101c12008030b41060505140c546800d01e0030600b02030007407198840c4406e500c03c5000455201c602180e5907030205004290040081c0b03004618000842030520021820f030182c3e507a6071510000e107504c00380100c1c0c0e00640a41034800c81d8000c03c1160710102008010002403462010f9a4542c050010005e004039000440c01d0b12010041c0822580341c00341c0000c1040590000c1c41c0c2032a070110f1866 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 252917697 1250 252916447 252916451
    0x10908030a09050705060708030711120f030901050f3102150415030207021c081c020c010f0e07210f050a03320d02040f09050103050c010c17030c04080f060a 69
    0x101c0c046ca000010f85000c1c5030007540c603d0950342c4055003507444030383c0c1d0400d4003d02d01c550185142082190f000502c0c01c0d05408000c140c881c103000c4105400e451014048200e091425010800c042a0f5070801c2a1018004500100c2e202e1303c1111002c15840b035800b001c2d40110013204c20004c1841802c000307100301c9100140c1c41c0c150002800d422400c074000c075000250301890300c606040644030703c0d0800d4058070340901c0080d4940081c003503151040c1440d807154811551b802050031800d281c820b120764101880074900c00d01c40c540b645007415858040c14000c042c50035901d22604100140c0911822940591001d00190021280d082099590003200c4c400c0340064146010032a0400100c2c1e580e40000c5040000c220880b0520304078540c0b250010210400c2259092000041c1c10852401d0799004003524000080c40d54110b041107428003420040143c14401129200340000b1701e007a40b20010311071482e08d021380721348036420040d02034030583c0d205103450320400d00c1101c0703150742c04034203540107203141002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 252918947 1250 252917697 252917699
    0x60e043201020d0212090a03081f0506031009050c040f03080d0608030711040605061611150a0309050f01050705030c0c1c17060307050a180605030f060106020114011a0705010908030a090507 83
    0x10b1a035562071f0a0400800184000001c80c01190308100c1101700380d0310495010381d489890b440400c91030703002244c80e04009494650208032009051041a8000035468500761902e400c00b5042d0385505d909200c0140303007040003d06204440d080340c0c4181e000d0009201680d948030700904204081000d00303428603100380d190150010303031441c10000315400c4443c0c5101401c01000903031a00c212400784411001e42107240110425580490761004201c5c0d4a040c2d1000a0000107600301079250050310700b141c080d2a032524050124080d00202603a500c400c48500f8a580e81d000c0004039400c019015803c90f4943c0c101d00c1e001400319800031100c0d8100d000101001d5038564400003050307540c086520500d5001442d5010078414101440c503002781400e0746890104e8103955902c08685024815a0710b0309450304094014800c140d4280038007500300a44102184495062886881034412000004400540d0009140c01001070a4014180440d04502c60316124505480c001c800741c0510141140c080c011844 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 252920197 1250 252918947 252918961
    0x80609010b0d020f04020a0c023a0317040302070302040504110f030d0504050d21020a021309050d1b0b0916062105100807031104060e043201020d0212 66
    0x100b9110b02034009100c0c12441020b58240002513200b84451800c008001c3d00c82405611081d980300a007011080f61382d501c400c00350f9060740840001c1c5400c002c4220448410f000441d9000584440c59000180c8000441d2510300e81079260580c5548003d4029081100700b0051100d100268140c0060039220030f003407403520b00304250726104194103c1e004100c042c0414452820542c0131800da692140c9244024240d26000d09280c900400301c420340182e100644c074404500b003442c0b208544d00d80d40301080c0310300c105070fa4483e500c510903103416404000014524100300b00280c00b100d13151541015551a16040c510300413521141e1605041911a409200003e42c044c0701e40e60344240c4484038141e84900f00da0707080140c009040041c007504444440c107100800e92240c2444540c004510411001c4a0649240d00b40400d0b12120b40c0082040d00743d84040101090700c0c81240c2c0d030419994560070040b900c001901c80241a00d04280301c11540c80401d00c01003000f5254000c010b02c460b007924443c80c5a403502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 252921447 1250 252920197 252920209
    0x105130c05030c01090306020f09061201082406100e0402070b010501020c10120905070e070905090a020301051e0a0f030f061d030f130e070810170c0105030901060f080609010b 77
    0x90f0185000030400300381000860b01543c058003400b014104000d10b48030041000a043d500005110030707007c00320308010082900c0400c002078004840c0e0307406110f2182c41603070380c0400f4070000f4940e60003103070146944030f41c4c1d07072084464030344040c40208119110045810502d01841c02401070340c1c094030481c1c5a00302c140c640078008191a5000350340c0c010b4074584a0010002400c5480d0040b6542e100b04440441c00604030140c8501c41c503181d0781d980540c20b2400d81006011040900841c000520401c0103219030b03180e040a4844514000c540d0035143c2080d0b001040c0314039004d13880303018140705444e004000c2103814914000100d004040500c20903d00f0800c41010082c80d50360b0554540c0200443c0c2c0014050b00060030740c040c4400380074109103556004541c181d20084501c2d400040480e0708006046080101c0d031000b5010341d5801c20783c0510306030803040d5110003046583d03051000200001d02484005d41111003c3d003c0d0302e02c0d4054640d07850240e1b6941300c80c203644030291942880007444d842e05203d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 252922697 1250 252921447 252921463
    0x5010503061012050307241107020a06080612060a0b01020c0301050f2d07050c15070503130f0f0302010e0d030c120c030e01110405040b0a050a0504020901110105130c0503 75
    0xc01244500c1030718014180e0003c0c140e031101180c0d2400107002c20b0300425983c8000c00303044540c941d840c2c0184506074001e502254243e040740040d217281807000c01e0140c1c541c1c0a440080d55220f041000c41900c640d0000740048841d04a1510b151007403104011084003d070308903000340c920030703021101a0352401c0c0c20142a038000303c0e80001030001d8500083c488040201c071200700c0b0740c00781da0702c0e401c000e0342c19a58001d0564101c41640c0031a0740041c0003c5102c3c001c0001014407540d402c4181d149080905c1700500300d120140261024010124440043c840b801055094240d841ba40000101c1084d140186c00703070009240800f00c9000720004040140d00074001c05009420310f568068880c603c0c5407051004200000048080603541e180740610201c0c01d1080c81c4004140c2c000d0141ca8a261004100a481d078921600d8080c6048520400c001c4d240e003141401039650484000d0785540f01013004807a03111422000c032550b0b609100a002c4040310140c05445524064280c2d5030f120b40e2501e041c551344240b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 252923947 1250 252922697 252922711
    0xc0a0302090a021b0607030519020c0601140a080f01140906040c260d0c0606081504290403050409060f08030d0905010e2b0e100c0201020111040b030a0501050306 71
    0x107110000c0c1c1481c11070b5005200100d0203400d940f002e00c8961032401c0c58020110b8140000c00c0d80c8000303201a4125018046030f806000c081d0a51a154108100700d1704c504040c41201c03c0d080c1800c0d0400c1041c1e8403540101c0c0603000c01c504582e090070481040602070a1001c14000381c00c065030011802c242e10202c1d0081c072a070340004600040324a40403031321001d00c0c103607070700606140c80040c018203162038103001034441c000700340d0f5449010007a1805c1c204210740c00c41c0e00c0781403990300101c88816100c4c01c013840d050340240c1210160b1222815144102c03051004107944004158042040008050304040030f0800d4940d603030404c000403034071140d000d00c03030811901910310715600c00d0019862510054100e0b20406118400200d84540d041040d01d1404c188050704a0101d00d0304181c1c3c00d07500c0c6c41700c40041c2d104000d91500030784040c021310200d2200d0892000d10010403207645480b0f410369000350401081c46500f400c4c07240d6500d58a90100301d940d0000e90b0b03000b02480c100400007429140010f01103000f004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 252925197 1250 252923947 252923959
    0x30118090515061507080702040510151407050607020618060712020d0b03010c0c0614070504050907091503140a061a0c0a0602030901090b070504030c09020c0a0c03030201020c0c0a0302 81
    0x84510303001c032042c60020011030303000384203d200114855108000d8991140304403d01525085288100016035000528070707610348520705d88c100400d0021010003164003140f4241109071600b4410811100d10845401424520881c81805051680060024030030305202d000c00480b64040c000e0142c45e414180c4283c80010301030f881e04925088603900911003e05801000a501a4a8800b007802d6420000c41d6001041c040c070181c03014018140981001a11006000702042c5001000600140901c2c05035a00a101440000e5207050040030034901504480b2901001c611466000402420130391003256030120980380811804401070143c4815900501c07036095010b8126502c810054201c5d0306041c50900c00e940c003080104015100450040c20810004181c1080c2c0d030629100500010340711320204002004100003003108146424250360350000c015036030b569140441d500d411040100a8503140c041e01c170000c10590154000d054204464040c1c84190001034104000c080552201940040d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 252926447 1250 252925197 252925213
    0x3020f0f180432090a060207020307032406080309030a03030b1c0c05030c01050412060b01030603120201060e060a0b160516030f052e0b06041a0301180905 68
    0x11040301034141405040101040072039000c000500360b8203500186441544082540200c8111860750782107901c8500100c100039081c81d4911540c2c0305001c0360b000d410990f0202d507810440d0703018030004000310f8002807107019588000310713a5a8003510b107038071810346a132422000160843c4040300f0740d103018400230301824444507140c80c00d44c05030611b03045080d880051084550b203041c1c1c2440c81e135000d807405000c24403a0242010285880d2810103c07180341449401d1000b0480121100c1d501049141d00c80004220004440e0042e0301418450304010710b00c01c001c0025000d50340c2d056006c0313011504000c50b641d12649401040c85600d401a0080e000d000000304140b12020703014685c2481001d104808550304113140118a040903512a0000c4480c841e295542c2c0092100410003048022410041c803000200c030000c19070310b074080e04060085180c2d1248031309102030b51100c0c00d0354002e14030640c916210b0f8a080c000e5035520791013401a04105031424440921107102846041c442c0e541c0000148252 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 252927697 1250 252926447 252926467
    0x7030c080f10090c0c050709050c0304060b0d0204140402040609180308090705030f160b030c03010311030c03030307020d08010e2e1a09040c17011701020d020406020705090703020f 79
    0x7000200a200d2040ba0594000380c1404203215462103030504e540c5042540d4078901c3d015082600350340c803c000660604c400c0c00b03150301221048a400660003072000490100100129082070000d030000f030351017803512210061500700d0340c00046c070540c402c4804016458803040c07250100c3d00b0b0307884605503d00d04080020006030252413841e41211440f0b08072015240d0319800280b91000000f070501a0341c0000c40b508004c40042d071a9003000d0031842c4500740c19464070113000c0a07039002c14407018158011046010116440c24040e1041c2060044c096075642d1400f203402075a41d5007040000400100c100000190511042505c18016280c61b01e034440400c00386c0f044441341850044240441e00110000047d07400c10400b1001411100303800c0d900d444541880401040300e900350200c80c00d206010040180e4005050380c2d0342d040d41c4030580100c040010305008a4024020303028854090343c40083c01049190300095480225002154141000d81d6218411020f034040d032450707003143c000144901d50702 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 252928947 1250 252927697 252927721
    0xd0501181514060d060f0e01140d0204091e080414030a02100305040219080d0908011e0f111204020405090318010f05070501091202010b03010b0a091a06030c0901020607030c08 77
    0x40042c03c550820000c0e0100600703c034441d43c4030076241465600c1c108007640c40f50002d42d0042c0300d015030501414601c1b0303001c141d5200c62251700034030036955001c000c810020540503802c0059041038010340100254541030102e51321500a2409482240b002c548113480d000802c200002e078054142c04401314070a1054024060203003080764003034140c1080303ca6108074144080014049a40103000d41001890082e0143e1219081929641d0400c552520f601c1c8441c605040c2c0b204840d4400200208012600070003006861110703d4443c0d40046c021032001001c2702d059000c0ea00840e010005034071180d0200b541c0e03100b01e022031201042104111002136000d40d445201704041810024a08240341d590349003118145001110f119410306104210b160f42446140070703000b0158020450360020400003041a02244141e06506032100c1800543c0300343c00c42c2c0b2540c0c022014000c1922410003030403126907a04230801242c0117100b454000744100b40b203070143c0a000800c0ea00c071035419403036075010509 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 252930197 1250 252928947 252928979
    0x1107031104050421120510051807030204050d1b06022b020c060a03020a0e09060a1703041505030f0a090f0209060118080114011502060f04170d05011815 67
    0x2128007440c0c02c16811200c1d041c4c10554413010603034545040b040a000860115480588181c54507808207105105c19101e1141d0140d00c0080b00c0000d004d030b90f5641004602912032070b00f140c0c2d041101909002c04005404d24024403403482d010b06c1c42816030711000103d81c1c44010840c28005805113200781e44501c80504001840c840d018410744035005581408a07405900c00203021001903400101c2c0c000c81a80303c4070320101620221984021800d2810009103501c1080c01583c08243d114080300c000002c003001280c005050180c0c0030041038508440240c1035420403282c111f54052030100150035608240308480f0225400f40b82000529070b01d40a00c00710410040a0300e040c001c0d43c040d01c45000c2c2d500300c0260010303c0d60500100d884205494100510f04040c0d2041140480720303550000a9500814070990204026502481d40c2d036860400c42000305802c400c0544c2d0b15400078040c203070601c81d1340006041e204182510030074440c144112404440d84003c7ca245070b004190402e1144c2c0a509907281 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 252931447 1250 252930197 252930203
    0x80a0c051605151003020405100e060103020a11071205061008070303141b060109060e0f0403081003150203010611030a020607050a0e090f160203031302240a0c020111070311040504 79
    0x84503661100f01007038145500381c0c1d2045000c03950003410000c45c43c1ca4050303c0d600821500507010031503d00f005002418401500441c140340d0089001c03044c2e14440d106030480740c0c4001d0126003d1075560248440000a00e1201750341502660000880000e0381c1c00501c0b04032044003004245c2d0502d182c03030885011400300003030715400034208001c0440342c00c20f9510040140f200d001400d15949000f030700d0401c895646d403141e411003030540300308030a5000702c0d04000e41c0180c150501a0540d990365000d59100c66050704001c04c102c04040c034030841210a81d02550680e12552035a1035078500d45103c40b90b0700d02078043d82c0710041e84440009902207118002405a0105500308600702c0c1005a00103410003c0845000000042c01e400b040120004a220760048074000d0010318030710704003001c1030385030340c180044042d0254400c40d0301c20b420145000804090540d0f100310840d26080414001005111070040590019941c0046500c5044010815204403640305900882c3c00420005010140c03800400136 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 252932697 1250 252931447 252931453
    0x60e060f130f060e0321090c0f040207060204080a0b24030322050310020309010c11071502031308060f0109050c1c0902060c250b071410060b040501080a0c051605 71
    0x503420413000c00107007104106240b810030003081e0707009100a40010080400b00e203644400c00300c007001d03203900042e168251000d48002d6074070203160078504081d10840d0f02c200d00520501c1340c00707030a11010f0020300d80180d105078400b00800841c00d100c0e1046c0030032600c54681c140c02c10440114100341c1842c0525000c040c948040001e01d580b20b00090803c1482c81081c035a15400104100003072400380b00e00303001800c4604188150703021980700036956001900450b03810600e070314800c1004600030002d4403d002a0440d0401e00c480d100c4000c5601c03841c0555600a03499109070020580d426280101071148601d0a040c900300900c803e100c2c40c81c100174040c0e034081d16039205229070140e11048000e1500314a00d00003000e00852141e44c00810304180c520441c845a19040280030701c044010441d5007036a0085182c0022000740010b4a081c2006c0400d000105850440d0009001381c00a0140017180e1003601d4042083da05e42d0781040075a02407144141c0020300410003501044c201c1c0d140003104900450071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 252933947 1250 252932697 252932711
    0xf1309021207031106030106140c071e0306140730150608010f06020c21071712040302100807110d23070209010b090d05030304060e060f130f06 63
    0x82124031012103a00c0c81541c0160b001401440031811644c000c031081614242d03e55854148014800742694003030411016001400c2d01d98001c0401c0308001130b0580d81d101c20720820302c0a00346170541050784411103145003000c0185007401d42c0c51000c684200599150b4441604001c0c481c0d070004040350390b2401100180410416440000f481444080c1c400c0c00c00c2c0d50245410420b026088a205074041d00380e100c10303010280013003a40426100560f607020341e44103c18402408602c40c500701c0c00440507001c1c3c81141c0c1c0016408602c1c2d5a1042d0446850065500ba6151024034030404d20a9000281d080040ca0184c0c03803c01e8816806540d00440c0d61030000082141e1418041c10440d200d2089030000d194800804403141080e801ca40c2d600141505080c50b042c03059000c58100401407213030754000b201c0802c140344207440b5400128541a03003c410380e07a5030715040c60400c00030401140c14409920803000080c0082c0e506c0c10003280a245c80071104040106180d6980101b079040803c101d0311692100c40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 252935197 1250 252933947 252933949
    0x4020a021e010209010806090903180a090c02010504020a06090308031602010219020601031a07021504060b031f06050409150b010e10080603060702060709030312110304210801050f130902 82
    0x22000e000daa488000142c1d4a25813071000610300c0a000d4200341c0328042003424880e030403800000b00c41480300c01c0d00e42c84640d04940c4000841e10307910350340321003011801e040258504c00e5065210601c103610841d0450304039500d4110031030f0800e03080c0c040181b10803002c1002c03401ca4a40f0400080c8040542e10000d8a4450920134081c1e010510420030800f40e841000140104540048000840d08010550000030301e401c50009540d0714492225000e048080c801003000e114050f008070003c008054129900c07104100a000425014611251101d610300140031a4600c0c141c014140c0c1290082040c200d0040520200c00040107030880d45410700201005801d0b1a8403546d160f0802c0841c0d070344806009190000625007030400083c4590119041041006007050308a0900000c1d250140b804d096482180d240d000010094074400c501071000c080304110400c442c1112a00494400c60307641a44141e0303401c0296a81c4c2c10070b001e00d80c0c0c00000c8100e20704040c206200c0c440c403c2c0340340000224419040b50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 252936447 1250 252935197 252935233
    0x111090f0a12080a09080102120a0509071e060e06090a150530161407080d020301080616080f0a02030c0702130b030106080a020d0f1b060207090b0303031504020a02 72
    0x1102200e003d9804140d0f0000c080d00301c80420004d05051000307514080c0400c605040d500c00042030505240d40e00c1e004550100c104001c040007900c1105641c6016058494088242400383e12800c1d0004103610480c1c0d220303041010507201109405040c0842c143d0400a420390400307940107801c1c0030800140030182e00b01c42c01c1440c0b5410001c101c6000015480c040d080e00d4880e0400038000e400b0f002c02c0c0c09000c51619401058550300542d00740103140c0303440103403900b159035100d80c4080b40100b0340040000f01d108540410400c5c0034050340c0e1030b108031481c80e0000c2980d49180856160388143d00040c0001c00c0ca04954004580c850092000346150181540c00110fa0740d10900102e1200c9568034aaa0240e0030244a00e4000d40301000003813001171410782c0000c80160055100900341c008590f198010001d0680310246030307107203101d44150340b00c1e00c03040c0003541c031030740340c414011224200807110400707040100440340070f49820a01071000c11f21240612002c3d41c4000c05500c11403217411041404072014ae = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 252937697 1250 252936447 252936479
    0x80309100216030e040920040f06030b06100206040c090903110109050c0f04180611040f031119080d0e010e1008010305070f05060703030f06050d0b180111090f0a 71
    0xb15008070303032622190600030582a0381003c2280500d00e4110400c0116541c4000c2c0c0b0300170000c020700318891140e000007007000381c01415010400581081004000c11000400c920f01c100300568051031a6210320008036561035094030b02400610000c5800d119651180d080710340418060705100c2001c002e800d610343c4c212103180b84241c2e01e680000804100d40d11302048406410b0b401101c040c03219106d031000c626512185101c000b08016680c01c5030441c01e6501409480003044038000e88403d040c1d82e82010b80040c445840060310034002d980c0540e90080656407003000f61500a0700514040454010507140b03244014400c506118810b000e441a079a14820080604292a600e20314035514510303040d4601b0005811030340d0200c15001c0709000c562154000e0350b165903090300c1d01103100800940c0c5030b00205410380240b500700041c5030098082c0a968103009002c3c40060300703010034810320303607404074205d031460508980c100c0720400c003006140ca010003540016401c01050400c2a5036581c00b107420201390 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 252938947 1250 252937697 252937717
    0xa05040215180a170d08060f0910140306070903030c060f1104210831090b031c05040b0c1005010801090b1e040602030a09020918070b04050a030803091002 68
    0x840c0c0070b4640d860030306180c490300901001c00e80d51a990804544d8075203501800c00c03d030040201440020300d050755610340300214160007814160090411500e076503002c9080c0c0c05042d086407a10440c5039807034140014214171418181e501d882c0204c5c21950100c954009102e400e40c0c0560300c2d5900a0440b0925100d404811840c007641c0a03510340c50b02510503001c1d44940e040e441a20542c5200c1c0b00410424001c885c00c580009503403052a860443c020802840b000e0010780c2c843c0340184000c1003401c195403040c80404004c504a0f1101c035000b0381060b41c9041c401d80c000c07001420512080225002d40009000e07001203010030748448a810000306d400b00d40b0241c1c031011041e034440d54020140000424450307040141d101c40c24000104140507d05d030f403400544028040d0340e0000028150b081c4652103034020503070082107290903052100150714600444404d400460098860005040d040300048800300d49001c0c069a01851468842c9001c0c1e8000400302240c0d8010480e035401c003941e041c4014808140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 252940197 1250 252938947 252938977
    0x50a05010f050d1a060a030c080a0b010b091807030608150103121407301707020c013203100306060501080108100c021603050615030c090a05040215 65
    0x301d408808000000c4640c801402074041c0030410700403a42103074000071042c621162445454580748081382d00c0e10383d00c0c3e201800f41c05100c01b0120301c20901251030b444060007032030705e0380480c2d80390510201644605541d03180d12400c800e4503d550880c0200502d54840d1241c10b0000d000307a41c80707080904140c8400214a000400f0000510410010203401000200e891500c81c0d101050300308140c446100d2031001415022404404814502103590103a00380c04c0c2e07070042d040c2082c0c0120310240c02680b00d010740d21500c48a120000d94001d1000400e045503c1050b550f0a50011008168904100c1d4110801c0c020543c1310040f000c105800c5d01c0198010203811840031011451800c1403070494a0716003203681000351002c010401140d00245070300041100c2d0301c00084a10600703000341c0c50b00c000780c00032020303117400040000240100810000d129a900d54a861700d46001c03a0101a200c1d01c02d1002aa030042070f05011400700b001650149600500c045c2c2081c400c028058004001d503000074020151501d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 252941447 1250 252940197 252940199
    0x120a030809120405031b04090c1502010b0102061003080702060409020307050304030224010b0a02070e100f09021e0706060b070804060e09060306010b0a12020c0d0206010611060406090203030d050a0501 88
    0x90300801000b0040b08006031190b060a04010000e91036280020307607403109010116242c1641d90351070340428080c56024528079101569560b00f00c252621030010f0360b0142d403920100e034030994000f0030a140705002c5604400c00990455440600035003200c44242e030098818000440d00c0c410900c004c502405c4241c440350744901c0c051800a00d072200d8a12041007402c083d03900c0110706807104034454191010303000600c2c1c4034030005204a1030700030f150340030f200321480c82005c0c40008854800d60380140d410001c02c01c2c0005072564124810703440b4070007440d01c0085186981354101041c1e64003425415100e00b1001c40d00580e1812004043d800000064940c100300060801496030800c0103004940026038544e401d0307141c04000240c03140070521410180d00030005501e0012032046030400f00081700e425045403038101180429a44145030444d03840584204000407a1540c0910034513050108054001c084942e9a030b503c207001360500c18000c17a09407109000e084880b4040d4001c40c0d11a1003007200004180d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 252942697 1250 252941447 252941461
    0x904050f04290c07080d090b0a06060206010f031202071503050a0e0a1101030506030a020604080f010605060c1002090a0e040b15011803110d0b040b0604050601030c080a0b120a0308 79
    0x14160000380d8944100c42c44240b400c10410003031203982c0103540e480500e4465505052100b803504c914102a0385c0b10789429403c20402038500101030040200c110100202620346c98141d982e130390301380504413108107120000c01c001100101c0c03480d17500303800c0d00c15611100d6a840151180380317002c85040d80400e40f900704000b212030a074401c3e440c688080d94020070348240700303071924055009000100b034100343d102c00004605072403c00c41001e80700d6024144940d500c1c3d5a903589919003454403900e880d03550804000080340d00e8903d05a070000f0480c0c2020349038900c08160482c00035400403928941002c4803000c0040c1c0200d980006a1040740284011001403401103542c11003500706006060510461048903042c003520240c01070281e80e400740844c1e001c003242c500020208114408006c00c840302010802c07041041e0000b000f0702480781030740c061200c4e46a000042d0151a82c881000000070511400983c04601036000f00c203100c5800380c514181081c40c1031465080440c0700c04c05801107003d100604c910 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 252943947 1250 252942697 252942713
    0x231c0305070e0603010302010503060d050111070f050d02070e0a0207050120120702240a112a0a020105030a0c09180204140a0b1606144212030904050f04 67
    0x401002c0b43c2682c51076044d54000781180c0000750802d805402d503c2008000c010f401d45c4450040d10601c1e4625031904d605141680d100300001004491501494944146d12400080d000d020b450107a05141e040303969005011000b1742100c8015600741d0340301c0d22945038041c888843c0d05d81811000c01096500c4030014078108942d04c0142040d401c5500840103440360f0a0746040b48200200030207070401040e124494170101800155401c0d000b244000a0106c2844000c480c1c009031600d45014040781c1d008600c528103442d03814100c40680400c100300000b542621a540c0440e21041c45800c01c07100e41c80c1c4074009600903502850a80c01082d03800142070256920358062806440f80440e902c000480c200365601d00349004540741c400540d205d2030724100c200302660300050b08079600c40368034444920305155a041c2030100c0300c0d082411a280441e40000b0400d45000c0c000510401c0c894198505442c0e00c20302880703d281007018841800240700c9110190365600540d400ac031101100380c042414603090580d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 252945197 1250 252943947 252943967
    0x207030f030e10090510051c11040503060901050106051b1507080a060803070c030f0816150b03010c08160c050115051f0c030c03030e0a05060a0b010507231c030507 72
    0x203103d0040340c10042507558240d40b00e010740c0545451072300c1c1ca082c1c100c80d09200d64060800b00785d16041c00903012059084002410440784210116a010788a2003601400c070747c4280a000005082080f07014500005034045c40200c40401013107a000078000d205030132140b00c003610f03031100091208042c00030103030840c01000701415410300a145450b1280d590540748030300c14480100031225801145007072007a240300740c4e1140b4684040e42c0815015610b040d0050b0760f07071590041d00e5240340495051840c05c0502c543c2d4480503960b15454119103031040751410000c1d0a0b920b1208004004010500050082c043c0d03021031400220f50751621404d08082204601c602c07803030344807103400058100f03484650010070b200e002d50300750611680b01d4003035041c104c010b4940d442d000d407064031400320954200400060f4141c8a1101410204404c00318200119030601c175603c4040d101c3c00740c52a00c400246403c0b101e0300d510a016034102c2c0e541a9460100c05802c400d00c840c1040407941d550200b100f03458100e20030b01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 252946447 1250 252945197 252945229
    0x603090c0a14010c141c09030203120a08063304031e030804140a06060303050703021204050303040e1923060a0312081306050c18030105040203030306100207030f030e 73
    0x11219030b2100c03000a0100c4825600500b2250180c2e44401410f04144016942d91820700d400a001960f5610050600803080c803089019110b5000c5d1031140c1402c2200350340d1a1a0150303a000c40540302e4104001c112004080d108050082d10340310700c110000f0040380035110048800440c2c2e111403031410030200314a0540d80040e2604c8001501c440000c0d03020b0b01199100b42e0142c0300760000c1d80b00c00855464007259072001003060386001004010b16030404080c0c40804e129a0855811300d9009264200310701840c030601c3d4141e0300900c0144100442e0a001d103501030610990305094607041c02558003640c0540789120f40d61002900340d0000c0c0b10b00b104070340b603120740d06880d0031403003c1c99075a807069a43c0c200040f810801c10340c2e2000c6032190b820b16062401050300001c043c842414004d0000949901c070902440b0b108401295480d05170034180139091040c2e070001c4c0614150390300c0400703000113401c8040c840320440c0644180440000c44d01f50880307030100e00135501d48002c42920814402c3c0c80d41041181 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 252947697 1250 252946447 252946469
    0x603150608030306060705070b0f0c100b010906110111120417070804061b020a0602010b12070f03080708040312090306050601030b030606060c100515031203040c12110603090c0a 78
    0x74800e901d000001c41c1d41000090700c21540d2444282440d600b441c1094024403044078000456801d200e440c14090904211114103842000c0c02c030501560844020310240c40c0400d80d0814108085802001e007030000d44002400031900402c600547c04080d8450021400106c44134030600007805240448502314210428400b480e08640340c5508000340181d100380c10401ca460030288940e1050166a85201a8050103000358a9228000640680087e48055024200894060050190019980048401c1401c011100030b040d51100d008a51244a0642d0070444c204000000622950100c008101141d51040b83d07a500318a0324005440300039155504040c1015859846942c0100d0050b4200398210b0362599641c142c082500d0800130240300901c03400d0f25080400c140c094003101c0e4400c6000c0e08900b500c1401c802c00940c1d85890005443c0500405243c034030074454440f070744220703c1c8201d000d1503240c18106030000010f200c40d07008490710783c1c4030340083c80b0043c0d00d402c11081c0d0001a210f02d2101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 252948947 1250 252947697 252947699
    0x80307230a0e01022107020d08031503011b0c0809030111040605030f0a0b03150411130b0306010905010308040e04020a030804030f15110d020d0207020a06050c120306010e01050901170a06031506 85
    0x7903112480c0303070317021660003080c0014000d045540e8030440c02c510035800079419440c0e240120000c1d01007215641c449020b5401c01290f400c082a08440388007040c039507074139906175100b1782d903c1e41c8005030042403110380c15660350b02c181d04500d0000c0001d4001040641c2d101940c1c0d282c400603100102c10301a140e040c1060801c0c9020201d0340e130102d002660b020026001007103955590400c0e010100c0d00666171504181030b8201c0031082807194014104d080c1095080b16226683c2d20001004c5403000d2002404c204014030060020244404106410078002006450416103e40f55603055170300540c0122030001060341410200040c48520a003422480e0600f0002200103401e14240c0744155100c01c003040d580012081c14004440d4152640b6580103025400b016480c3c1401510583c0180a107401912450a034a0714030f05541e03080720310411042e5940060b2002e0340006513955000340c51500e041c00640e0040142140702c81e0706141c0b2681060f07501142451940c10304c4002000c0400705900d00500f8008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 252950197 1250 252948947 252948973
    0x102030415090302070b0d06030b090a03020c1509031b130b0906040216060e0102070302064b0709140603040203061b04030c090b01030506030d0804080307230a0e0102 73
    0xc006001100740980c0440e6082551a080303040c4200c40d00f10000b03e02d008030305818540c44a0780044156480b03440c02030800d44a0032181e07951800ca95070300400503031180c059a441c0c1d08016607070705070714162001d80500300200540080e08081d980708820007805070303c4a42455614160307540c107100803902d0004010190f80d41010507841003009003402d00454001a5165001d1711611068000701e030065800c209003124254614042c3d48002015001841402c000c181101d00f03075490b010000b2001c40d240e110805c00060b50380341884e074152540d140da0000686021140444400d114031070305403a52160309150130610084004001072840d0360042e00e00303004210058400140c0290000900c0e00303000084580c6c00c3c52083d661007940c10041c201d014070f040006845000b03402c006800c590989090000366141014540e4415070300c944000000e200001260100d2403010056802c085d80e4074201c40605154001081d01200b4003070700c18480040010700d42100e50340002c94040c0c10600344043d000080d1640 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 252951447 1250 252950197 252950213
    0x405060f0612071e0e010b0706110c030d1b050708030105090c0c0f06040c21060504050c0a290c0319020a020d15060b030c1b070308040e0405010e01020304 68
    0xc0240c2a000004008500300380d0b220700380401c42d40619003c40301a02c0d15445942a188030070315602c04601d07001c29000ca0b6949003801d00c0c9050328014560f035401e010341521a000038002000700741484034030400220080904c01d000400420500c1e01000c40d80040120221310020411a0f100007004010301101d0001141e00f412241128001c80300c0041035210306688480d54403885000c1303034142c4039504510000ba80d000c50560310550143c031406030203e64950314121848600c8034040840c1c00700351081000a4110b500c03143d000b5000d102240c4814040e100071402040080e0400280007001304081100301687c0100f070b64241c44910308280c01c20b2854034083d99280940000d08140c00021b01891100c980308000c03e10046070000c10700f0b0121040c0c1e0828840401c4030300e0182072440e003404c40204640d903d8400301c0c2d015420403c03241d0301e07144450340d11a0109482d0781071040203000b4000000f01240210001d8405040c040c0c0e010340f07280c01c01e07140950031130384c0d01281e244e140e900600400010030442 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 252952697 1250 252951447 252951451
    0xf06030f031818090d02101b0c06060308040602100518061b0f1206031b010509010c0c030c03121701030305030a0c17010f0f06030902310e10050f040506 67
    0x8802c50b003251603000800541c0240703c10030b441c903c0c1d180d6a401c01c1110b450005400503407848540039140c1b01100c052010040d525142e00f915204c040d8044030714071040c4500554180b46015400003e40951a41d0700d84816921603444800168803207000c040000e070a80c49003030303000f50b005a11501100780c1c42c0105034413600d0042110341b049040014144405240504840360000a50000d82c0c0d070b0580e44414003d0f01c031040e19150300074482c1c44032003800150100a500c0401605031039050604048134011140014046000c030780440c07440308004000b444c801c0740301c0040c504c01c40c1c000080d54005040100031400c0b408105002c807203000010400302e500141165000821400d000c103442070135400a60700544180400c8184000050000402c00d100406010645814404655400d81d40d400d04500395402104041c1d80503264201c4001c0740941e1520090b502d2191030500c2c4d4242444070900d00441d0a499402070494003c40c211141141c000c1c400c4a074007403242d00c03c0d604541401d40b2816916000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 252953947 1250 252952697 252952717
    0x516260c0103020f0d0f050115050315061c020c0a21090902071e030801170102040b0d0b0a1a0309070f06021b030715120506010c081806070204060803030f06030f03 72
    0x80007030700011004c1600308440202071001010310200c140d0391007800003060240b10b4001d4a0f400c0c4544034a10343d12074001c807401201c3c00d055420340c0f10001410003400c2d41c80a0f486164910313031408814140b10103800a001004452400b603c402401420b203000c07001d160300d061050587d5555000e00700c442e084a1001c0a42d031200301c006840313000c036281445031250380c038668900c0346c10703010846010103a00031401c9040e1035800c91410094000d0b2140e440c00c0c0d000342c1c058011144400d00200c00aa04c090b801a002c890f4000d220aa10b039039144400e0404002108008950b4640001002015042044600f00131b0032890b642e008128a01400251502c49154645c1080e604c601c0008209580c1005035602512040c80851008901701e403001d028610004c00300710768241008001030b0150300610007a0b04003500200d540e0710f0080d412440903452901d1510041c3e00c04018400e0401586552213094060b100010065a0b2420085075040021400400052081d4449108a090441d002c026607110200c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 252955197 1250 252953947 252953951
    0x8010e0703090b090c0135060a09020c060a06060f1b02031203010b0a0207170d0f030e010f09050c04050c1902011811010807390516260c0103 62
    0x19503060403005407400c100c02030002c08484042c402ca500010072607146020090701c07142c0c030451040c0420300a400707480502c80c08603024081800c1c88294500f8403954042001804155016180c041c2c0408070381015202884e154404000c002d5164101d00c210000341600341030107407a0aa048000134100745407580201c0c0041c0b419160714045407000c0000c0400034440304002d039141d40e11828400c001d500300d114000014440c90384005400c0c1508135002e2008a81840542407941419100350390200d51611240100b603035804680d0f900c001b00f8030903400b0440010102041119040c184079140040b81801984680d03e89001d204100c404e400450701032044081c6101c1282404c107205a005009522000d01c110a030740305071004005043c2d0b04010514004d03243c4c1c9002d601c404904441c60800c22020403810040b02184440081103004501000038180040b40c44501c09580c606041001682c0c2644154002c91002c3c014040d005040b08040720b1528405001504420740035a51005201a5141455 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 252956447 1250 252955197 252955201
    0x60323150121090303050a110f0406030c12060b0405090106020c03060a11070213020d3611030a032a03170411090112020301050604022d1b10110403020108010e 70
    0x60720b180000740301e640901d1003040310700500d09000c1c024050840d0140d0401d841e0480d4590800c000310300b42c465083c40e00c40b400381414140781d4145c004094200e5018148040201250100b4801d801070303c0c0a003c003001100d8840f803801060000640060300042c055400c481c000304070540b0005032040c2c1c007078012031011507500754420340c0500f28071a886002c3d4000c41c0c0c0703c41002400c07185030010001009825001c0285c0152003a6800e1a00740411001480034030300200306065030141da030707455012030042260141c142e60a000092800d80041d030124040b032150344454140880424400c4e122003030350421642c0c405030541e40201071003540c001c500b40c0407241c04041000d01c20540305002c242c80c4043e10a5001b07503151a524564183c10304400c922a41c00c150004840703040c140240d80e142d080c00b480218516001d2502400040344009540c0790381e21003800511403940780280c0214010080300302421490321419107030004c1d1048491200c40a000c10081000180d034010300f481d0451381150400039040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 252957697 1250 252956447 252956477
    0xc0f050306220e190c140306040303050c041211030f012c030c030403080c12070c0308090310050a020408010e031623160e13050309010323010603231501 67
    0x3c040c004442036103442260f443d41e04c1c807802ca0903009a240e02410099082903174502c0d00e45140340301d07284880c2d0076400075008140024005d0f04800d03048590880340d04d040580740d024502c0c00540410040e14490586c600e0a14141007e1040903200340d00b4000a00c200440d0401000f6030407200b0074210a00304152203540540881130058a04140c240000c3d00e990301d07540c3c10400100e400120000145000e44441d84c00c01510700ca0485001592007046042d465145447c3d01c00140c200c901c4450b058003c01022070348003039081c89000c1c4a42201d50005032103500306842c00f42107031076102003044640c4c410010310060031082e9084110a0781d200c0d040d4401d61944400ca001c0f5400a01070801041c443c00c0c001d242005c14140280c016a0200329912045580d003002000e5800c20302d607409070480d00100213076400d95100b6000b810400d441001006001754900182401c4484268800c0c00003c2c0d0301c4540b80ca07410390070703407144201e00251a90308046080c032080d14054040f83d00d121f503050041070720000e580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 252958947 1250 252957697 252957701
    0xd0b120c060f0408070605030603070609050306060d1e0813050301090803151203040b04090e0615040e0106050901081507081608041103010e01060626150d021002010c0f05030622 78
    0x42c04c07894080c0c4c3c03c02c0d591100b014080d50000e850711f034441e0003211804104144280651030495900900031301c05030302c410092045180c0e08200030395603003200b9219002c03035445040d42548980e100f446000d55400603000c044003070310b03000d4010724826414052a50080f07004c5a05583d049904082d400c003a00008200041c1011492201c07a189400003203000a0102007586c0a801110440e903402e00400718644900380d241c00d022600914408650014841a420980d00c55a5032005c84000090400d443e5000a5520303c003da100a206a000040e03a41c0309110703092003a9005180c0b402d00420030300705103007110300800132450244c0030000d40d00300181c184000110048100c0001500800c40e0200043c1c0850107440a4010301c00031030040781000500801c1400302d000b030704503003454850040d00d42841c09600e4076140004240e0280d851442800940c1d91f58407503203a402880c2d0000a21494417400c0075008001c3c901d0000c00744402401000155184c1c2800304001c1844001c084003100b0440e414000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 252960197 1250 252958947 252958949
    0x5070b090a050604120e04140718360b010801031202030f0a08070806031207060b040e010608072904050d030210320c1902070513020d0b120c060f04 65
    0x4024800c1400744005c0c05003840c00780b400c1c2d5009075070b0501d601c0c01c1b070400e2000b0303640c030b040d280b4000001c0d0138001018640f140004200d10803001c00c0c842096640c900c0d1201c0d2030070080c09500607000c11a42d428032440101056848084203110007070100c02e4000d8006001090b0500c0080c2042c0288403804030310520074801c4800c00b004a801103034990802c00001490100c04440710800700f00b04502064003483d00103140c110410040450700d141c48490764600018110150595030015103030329001600a20070700030070025051817002000712030f05e4850005031030003640309001c44004c0d81107920740e1035244400464095039416250100100c3c42031a00324a800280c2107280c40003481c01d9a007520100000d410340840340705440e03200c141504410f00e4182c1c40c2000340d41c5805c00b004100002003c80b018403c05480c50403050040c2c2d00240d81c0e4a010440d4400c4822501b8900c41c2e000a4003140e00480d4840e20042c144c06a80001421400040e880d558404000c0b071148625808240300700d2003105401120 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 252961447 1250 252960197 252960203
    0x20706020310140102011e0903020a05030c010c09060305060112020703050d1418011b0809030d0204080105010e150306042307080a0209090d0e0913081801091505070b090a 75
    0x40d602d14001801c9607103486a03010703100010086001c0034126610501071a002000101a00810240040900401002c40348411803d5000d5920890003144046c8040c00102580a0021038a025080070040c03550707855800c030006041c6072005002d0182da115400b112a0139a0020050740c3c2c090f10b00701038800303000744604031213007500302490410103d65a02c852800340306001c0b075401c1c200801c49000380c281c03000031640f60f0010245005c1e440070310303110750407090308403000390309880c40c169580705914103031390143e04007050503034441c1c3c0100400c0f41c4c1000302e82e50285001035200588220200000d4948901410281802c4141c0019130380f01d003d01540c2040d40320b5250101e075141540c032251552a600540c03400c1e4415082d20340019003200001c188000340d507800350b0350582c480c5c1c0c0d50003c00c420120084c0810002c5220000f20000140b0b08600070002001001034052060414100040410750316803c000d41882549000d0300c011a0040182c420711036200d810420542d80384404c071450081d03d001c003d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 252962697 1250 252961447 252961451
    0x503100e07020d08060303070b0c03060a050904030503011a030103120f030b03030a0c021801031e030314040f111005040b0c15070c11090712090204240519050303041503020706 77
    0x4071118940000b0815010101504c4070b90782551800200350b2640030350072015120748039000001e0403500c1e02c00001c40d07100e0001000c01c0401a207500c04034410380c40440d01100802d03c0000140b100e50741180e120709004c00c0c1150324030316641c1160796050b04201d03000140c4040c0602c01001000141c002e8000c121150300140072203880d41c2039030b00f004041258541091740150f449480001c0c400305e4000c041030590340c1101104a0720b0011500900341c0c00022072040d02090303aa068402c000e030204451560159000305201c201d82202800c007515118400c0b0245481903c8803d0fa198045401605403812101000a01c5480300321101c401740c103280004072411541000a010401e5054229210380440c501900000d02240030305c000b80319054400351515004550000c0c40c2d081150030f25000200558800740011849132001d0b8000b6600d18032446551115081c040c400b4000c03801c010310744440361403e6800c225070051801011946a10840c0144a1000940c011070362130b05001c0d4044407000381d442802 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 252963947 1250 252962697 252962701
    0x1203020a0306180906050c0f0a05070c03020d140c010806030705010c02060412080a0207060c0201080115110f010231170f030406020c0a140315100503010204090b010f0f0e010503100e 80
    0x1c0f40000b00380700b0b074003250400c0c0b400001c5100b1828035415580b00f02003c141d035511b8280003410580d0103410405044030040c03817401c40400142ca41c0350307a1034841449034680702d2040107c00400382c207044030850310a0400400302c003040125540055013000301e4000303082005030b00c0e1442c00419a0341c4a59048a0346481c4005403080c2003000f01d800614115500b5801d030b40103251107000440c2d030648a80e00c007070f000403000d00050041d2030450079000070790051030902060390650380380258108901c3c81020402030b5070226612103403221640b030194100c0b603501601d41d40c80341c007602c160002030f0690240d01041c82c10000e0320131110740d080001e00001400542141c0d01c59607104802540d03510a04003081c0100c078102c80002e0105075040400c890070000401a00404c5c008140300e10032044014050000314481240c0001d0585003880280b000c0e0003844c0740071884150801c00501854003208208040040e11007440410f168005104401c1c42c1d000d1074690340d6500d400240a400c00e81907041981c8000030242 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 252965197 1250 252963947 252963989
    0xb0a05061c0b0a050705070b04060b06070f0c051017010e0403210c0e101b0501230402040b03030c07090506040f05010602031306111e0a0b0c0d050604091203020a0306 73
    0x84841c0f0a6124450a0083e984c40d01800c50342d41c045c00e00001c7c0740c00006004600000c40355042020f0030138010308010704218054a5269107420414000d4034166042c1a00344454180342c80c90584000342d60400a08440e401c0b0796448000354148180000740b400c100115003018454040c241c801200c101c58040518160350907840100340d815070000100d1502c040c00b0f8440e081c803c0d018998a05a9243c0c40304c0003540e2401c0c1a00719103480c41c00c0381c2c80e560b030710041c804444044c0365230b82d84c00100c4110031540346058418801240c840b200e0b49442039009108440c02040000381141c01d075143e1507400700d650780301d0b04042809090001048642a400c001c0007140700d80e800400340400e42c01d11501a01d04a66485054800501d000d0f4001c2243d049004412003410a40b5030104201c0d41d0882106d5645405885450348400141c40d1181c84000008403943c0070015030080c150081d1044400b0405c03000d003996105034a90040d8000b4042c903401003124243c840c000d500280c0205406e407800550490000c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 252966447 1250 252965197 252965213
    0xc0a02040519050a180209060f030607030b09100b09240307030e0115050319030504170307031107050303490c030b06040b0714030c070609120b0a05061c 67
    0x1007400e2541d40b0b84400519000c03c0d50154503624880085c050303501c024940c09010303c01000415054000703105840410580e1010000c01c1d00c1641c865034001517840707101080100209010b005442042d5100c2000d101a200030401c039860303c1001c6030507510080e801a17042e03800b110900c800104240d008020002004c1c0c240d0081045514004001c0182c40350111750290038070301c64002d40740c046d409292046100c6040750004001ca5000b8241981450b540d2210740640303281f034035030118441d0000b0625030101b581050b810b00c0246458005040c2c69401c040c0401da0301d004040950024004640c1407031609040c02040e2000c80080301c1090b9001c0d4160a07100c0c1c98081403400c110250b92405040c540070303034403e10500300c1c0940d000300410302e01031400010b0078442e040b2a400740d40400c03c09500c40300d5540d00700b00501948098001401d04545000c0c0003034214522a07015640e84408001e0500014204909140d80042e104200050507100c4001003020056902d182d0310340d00402200786c0c2d06001c002c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 252967697 1250 252966447 252966481
    0x1180203420405040b0c09040207050109050d09060c052d06040b240108040609081921110304030f0302040b0a03021215060307082a1201050a0602030f0c0a020405 71
    0x700e1034110000c29440070322085039000c0300d001e80f011029030302180d2032440310340c0100981c01c00180094100120342e1034150855028904c12940c9a00122000f02d80a402c0b40400c8000e02c090304010030b440f00c03c0d407281911100540c0b583c4626020301c0313030042544151440008200742c2044111501d0349418a0480240031098684001031141408000710b9103040e03030100c070205e030b03410b07074540655031165660807020b005504411104082c05000044407480303588031b21800b09020fa583c050020402e8101c003040008000d00c510782c1503052000750415075050000700e07508681c0c1450048011142d05008400038022a00200807060002a4540b85150b064019001c40c01030302071041a5522000c4119000d0a040509a40c02a4080c0300040485004241c000c0e842a4000d01415010b5440e00034091041143e0348e01d841c0611000c111041c2c521010380299026100c00e071503c1c280d441c18400080e640b405140c1c40c05624042c0041c078902e46c0d5409025151704c40c1d601800c280141c1c201804855240014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 252968947 1250 252967697 252967801
    0x306020a08151c0303050411034204140709050702011a03012304140d030f0e0d080112030302090306270a020105190e10120e0601180203 60
    0x2400c1e90009031034440340e41c04038a10403502400142d8040d136002e801400d4000c0c4252408051280c801341603482c180035031038942051500001c20300c4c0d6803102003510b400c02c540008501070b40d10403803a9103241584100c5500583c00200500501c140000754500d408000d4000b4409030f0704103428041034580541110009a0354907840c00000800c140c141400c80b8107610350780c169034081c41c0309043d0b551889026140c0140c094410b0b80040001c44804601d0030041018000010781c1e41c00c442d114508032882402940682d00c0c000d05810011004010004075040c01401d641c4203890448070209800395040f141014405020703078806260070880041e55016520300b00010301220b41c1145e00c600004034091813402d5058407034070300b403030040b01500484c5a0f07029016020f004848200800340e41e90080000f240341415034483c038a0b82051009081520603c1c05000050b40c031800060060444010075104040e480200041e22627490051040c01d07480c1d0300314005c4190310620b49046440c101070b41901c480b112 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 252970197 1250 252968947 252968971
    0xc010603140c01050c0d180b030910140603060601050d090b040b04060606090803190c0813050a140906370e010f0302030c040f0213090204090609020306010915090306020a08 76
    0x10b0040107562a10603aa003804079a04a5045038041500408455550318849210fa100d042e880d544074600303940c8181c40e000a01e5014001a400c0d81e6020300490561007168011030065080c4440400d99440000d0191070500c0008100c0c1410890154024107007640c20515109c03450401707080141c070000e000d50342505c00d541404408a5154001c40c040c008640d82600158582111051903410030410605400704021244487c40082114000a4840081c02d002c081789030034030305020400c250b070780d550103001e10341c18034207012035541d4640c002650700c00c8040d030380c03e0b00c214200882e1609603203400320302000800c9045060058090891801c00955946486a1001c0d90b01c1e80455001082c941c80000d40c1948443c401146e1401d203034000a41c800c50500c800350420712400e5406c5070f1926a50002460f09901203010411805180600340c01003202d110304600c1d6003019000241849950701130b0080890700d1107a5005c0382880344040e1001190030090440d02e0b1121814010200482a111454211 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 252971447 1250 252970197 252970213
    0x1f0b040905070e010206040f020d080c0606010e041e0203130512031006020a170c0f060a020a1b0201050906070503070605040b16020f0d0e0402040801060e01051008150909030c01060314 81
    0x35008003e2034044020507001000581c1d12983c0392088419608000c81e0400980c4500000141440004d0052480c1101c00b030001460141c000510422090200c184071340e0030108a8407d41c0741c28414080b51040c0c812016990741d44504c010380350b101c02d01c01700904510400c44031901001d05200618081d4041281c0c40d07000c02c0d80c80e0401c07030351100b100c000507288024402c628070800301300e00001c1c004000d02c40161040c070b611080c069401d0084c03c5440a001e20340000d81c004100e98000b12141105414880120740d0950360780008085000c2c020020340141c0c00010b180003441400c00546070311f107a001c841841585040c0c980010100ca040e24a00300c01801c0601d2404030a001040300d0200c82c07101d81c010010150a040100c40703540440b070700a600207a0070040400e07030060030f015401c0a0860f522904d105545440b041c04a803051002d41401046100310a0000003000510001500c4004070b40141807511114409401c521400110a549618020b40002000441d81c3c0c48000400d407030096407494 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 252972697 1250 252971447 252971461
    0x10e0a0507120902041407180b1201051903060c2c130b121608070b0a02030409090606120b060103060614032e09020c060721051f0b040905 61
    0x1884007500c1400100d40d603842d6850003949036a11000704140010004110100403500040310b80d07030259020300025030031113228011031212454410080660000b210300e080000004441004010f0140500c03a03118103c02613446002d24a980c800b641d0042c1003008417840345000a005178082071241580310030f0034062618191405000030f41d407010060a944e144907142d001d00c5000f02282982c00e0740c07101c460540ca041c1044100007007288003420b0954442030760f0070303c0d1503145459040d80c4058688401009101c007000d5011017034030202e5410081c00b098480451606901400c10b681100041e000022112402d010f0101b000b540102800e032000c1150300d450341170484070742401001c5002c55410401c0810f00405403500800048401a10300c50102501c4050340107041200341d000e0b4090b250045007403030301c1410600405c0e8010080e8204482079151300c10b041084914840380b01c6007010f50350030010398a0085041300c64010142c652540c05081e0700d901c0d10b006250800d0184040652070400004c0301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 252973947 1250 252972697 252972701
    0x30317010501020d21020406030504020f04060501020a0b0702011419060b040506040302220e0a03020d2102030a3e04050f1003111602240318030c15010e0a 68
    0x607900103074064201021032110580b800c4200c031441440225003944200021070492015101512550350301144500381401002805503604070550302c01c510f04a42000160b80000b10f10364584da200d607095480e42d585d601c1c1a40100590303c40200702c1c60008003002030382120200c09512920307010508114180c0c6a008003c464001ca00403140c01c07001c03c100c18409032a01360703a800765144000c0b0600c0d100c032014041e07042c140d8808000000c0c040e4000c0c04c090003015010701c24041c1c005a10b2406410101160b0f10403895003454441c0181c1c9a9400008100f849030a50400c1855001c012030020f0b2a00c408585c60001c6014045000035a010f0354141d43e41080c4d4140854003190f00c010b007103011001c04941000720b03e848042c1c40c0c03014540d81e80740c00d4100300441d40241036221030002c600b610500090041c420384039110a0845031039800b8120704103000b05140c0c00c0e42c3e0012181624043c5c08080f010000b0324510035a00e40052038403496414407800e00700245c100781030300c880b81500451070310385034140c2003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 252975197 1250 252973947 252973949
    0x40605070801140427030c0c0b030f0412030902031e0712080706020a0c20090906041a06010507060e030c0f0d05040501050f0d090c050f100801140102010912080103031701 75
    0x401143d84103003031000d0b1070700b80c02036101c59085440e10203009022001e01094544410821408a030300c40c104202807000e040100e03002800780d00c41036499860070582101403405e0040005144804d22180070700a07600c030384c0c01082e1080e80a0103d490500041070020812003261190801c0740c82a2800440c203440e444000300c0300c01d43d00000d9503003048026540c2e9406034008120200030400203030301c02c1d0301054185800c05404100f19600c00c1e100c0d4000000d0200034140240401010b5000c1c80c28840000c031511408146071107070050800c019103c55004880c0c900c600c600140849040c080209000700d404801000c3d2000200101c41c480c82c10050301039100c0450700d08800200760107101c1040654041d10080c040200360604061404400100040c122aa804010344a9881107981404181025403c03800c1d98801100c030f40462402206005000c024140902e004555413541c0b05440c59000b500001112a407010300d0142c0c1c1d1000c16802407e2500910041c3d00180f00b0a5059800c0c062040d1914 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 252976447 1250 252975197 252975209
    0x21c0905161d16050f030a0903180b091203041d0f010510080f0a0f1a1014090d050309060c0a0b0609010b040902070f02030319030e0102090a050d060b04090803040605070801 76
    0x1e011541d45002080303000b0035418600060090400405215070701760f0300118130903843e4820000d00e0700f0032400c2c010403000030100109003c1c0c4015005220170708000090321a0b21208a804110b43c01103548564118043c5038840c401a84a04403460364034003000d8815840b500d403007a0b801c00c0982c0c0c1c40b002c010364110108040e0001c034200802180f100d02d0041c00103030b80400d0018000c1401c1d14450340030001c41c0c48003026a001c03418400c82400ba685010701b84010081c0480c80c084075204804062a03a0030b00c200d038103107445204110304500403c0b40602c161400900d000b000c180e2030b810b401101300c0e10b980c03d00d072049508515039000207446d0710301210498165203010000905203070814040d81e000b0342c41100d0070784101d0b4110404c400160341c104001c102c1000c039a403500c01a0f450001d00a81929007580600260340d006201c0400300d5216280c00800700ca80407507003903010307250a081410007440120f000a42250a0040303c02c18440303614011030242d8422041080703a0f80d41c0003c211500c40c002c0c002c907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 252977697 1250 252976447 252976499
    0x6090e030a0e060d1404080a18141003060308160b160203070f02030c0415050a14100f09080114070e0904020108010324140105120a0506010504021c090516 68
    0x1000302d0342802000341446440e0b04000096810040450040c0e01a040341d0448031620002420180729500c0001002000007170508502080d0400310f0340c4601d001c01d008401e01490542040d52031076407081d04610010350b003000304190b4505004411065400050005441141182c1e0208205901c10391100002d54450f13406903041c41c0045c1e50f45108900c2f000416640b504c2030041034001961240728130020074038112482860381e407404090000e580340542c0622030a00f1507010540749622002c1c40707201ca5540502c0e0045003544080800d6401e804241c100a5580d0f29001c0181500f00c0d11281c0c49000e442d194451000c01c0070745008102d034800303003114002d001502280042000441c1c040014003040450038918070072040301c500a20480c0c044070b41002010072102c00420030bd05006402400c3c08540340041e101403812611102da0f03131081841803500580e80007030025104801c0c199600c1812800203010b009001140c180a55243d00c0159040301141044d0000a101010340c144240c4a0100c04a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 252978947 1250 252977697 252977717
    0x70605030a0b3610150e03010213030201080711120c0102040f090f2a0e01020f0307050c0a0f030314030606070807030305061503070212090a08070305150c0405090a0f060506030a06090e030a 83
    0x1814810300305d0b40c800d90500c0302882d00e0301c0e00c9940c28005841c06103024004160103e16600004180c1c203409400c0b0303000e2006142c40c6202c0324601040901041010000c41d507940c40344070030141d00a2207a603100b1481440e440c00007050210154100f0100d00308901018080c9940c0403518135480080304120030b00e80c1303601c09c89000c0c1d0710b4014490400c0d03c10050054500d01c1341c0e21040c0600719804000125016003115820800b20f180c0302180001800520110b8107036182107a40251000f580d000c04101d1403000800000c40659604007191740169215064030b0b105c148a1170064042c00c81680c140d4818039203c0461080841044241e80c450600d640c000c1551198a070038071852a40000071064120080b104040340c06141040200015445880101120b520400540d9080c400240440024003020402003055503144017120760008602c0400080c0700d891100c1e118014551540102e030020320100812001c41d500b0713404031046903061034051064403288004c6a44a01c50b241003800424000d40b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 252980197 1250 252978947 252978959
    0x105130c0903200103050c0f09090c0702131a030a0b16030e060f0f090a110f120f0102090307090506030a0303091e050a03030b01020d02070605030a0b3610 68
    0xc8080c041c01c041c80c840742c80391100c0041511070040c120740281a061a21003950b4140718055024144026890801000c040b0040041c03084101040c461602c1b440400c01ca000c0e0350088404180d07005104142011200b0300c10070240910807034203849010f020b004001941400300e05200d41c140c1c4404c0c0c0b41c0c201d5039005821794824040d414000d0406030340b0b85030380460260800049004048031140c218240c945560a5825140004d0075072015030444180307400000c00c441034916040500311492048204400d000c070711003034201c0042140c940b25880e40d0144104041d07009103001501a000d0f40d01c084e07201c08428054806c1039860307942550000384c9003404607200313038082001d40340310f100100c0c8001c9240d11010050341c070070f0000b5222500100949010160544640040c01030203002408608000c890040d407202c102c3d219103418400c001000a90546003903010b2100c04a0041c80c2c1c2d80c0401400c007800040403880106c030030071007400a055440182541c20200d2042c0843f00101c0c440a060039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 252981447 1250 252980197 252980201
    0x1170901060b040e040c061106011401050d0f1b020106060909020c010603080307121b05270a0b0d061e0b090406051309020310020a0203072a030311070e010513 70
    0x184800295580c0300004030300582e5a40080c0000e00d103424002c19141000d0400f1034204541d64010002c1c01141c40d40c0355032003103000c1221411616205262200c01c102d0b43c00684151050700010020b46103443d140e462280c003250f00507507000510417491440035042c0780040e4205c0e426402400c0100b42090810840c1944903002081e03582034410012520a0344ca948803e583c1c1c006644103030126200004d4203c2c0e034101c0b446090f51206180500c0d1020308101e0303001800c0b40c0710709161a400d0300360f95888040c0b000d0203c003000042e298013034010038840c1d546540c1d000681c0c000c000350700d698034104403000030b07151400051080074a40761142010514601040c40d101a803020200c2a04036448560026030341d80c40400746180710321603640120700101c1d140304050800c070039405052000307441480030f90318881c0c5c0042a5000b0310307403100040300b00020090300b4590303064000105d051003100c0307480080101944580c0507807020b1160400c5400468603403240d042400424022103401c0120004452100720942d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 252982697 1250 252981447 252981451
    0xb011704020d080307120524060a0908030313050105060d02180a14101e1401050c0a050601060201020a081e04020409060f0603060b03121305040b01021e070302040c0507020117 77
    0x4021690000d255a20745020b600119610800b14a9020311003a05031b00501a0360780c84400310081d03803180705038461101310f070403e0000118003440d40442c2a8a20034080d6503004044d120b041d0459881c0d10b00040d000400d40c100700c02c120f0780303942090040303a030f0307411314007209680642d004005c406c204400082d030b4143c2c400000c1c030605500c0d482d14161240c008084027280c0c010740f01d544503c1c060030306110400510b82c0d40c00b039115008201c0c0343d40c204540702031640d021581850900e40b540d56850288940c40c501404035001600d903000e41c00002800303540540c014400040c00d5100e19900c0e65518040181c40011000d08581c04500040001c00524040d40701c100018824400003d9079080f6894100844040da0022100556107002110591904104041c81c3c03038008410146059200344010740150502d00c1a2401280c4481030200280c2c0207002c9105000c602d800c141054210810b4540d64890607888203901884c40c0c204101a003d10400c00c4030341260701a159595040004410b00c4440180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 252983947 1250 252982697 252982699
    0x14060a0507211b0312021303020307081b0904080702040209060c0a0c0611010c0516050c10080124050909070912050102030a0f1b0507030201020d1b11010b01170402 72
    0x4011180c0060a440b600703149000342005050030588984502908107911036201c0e1140941c1c088542c0c0c0007a6120071090301103900c003440540c0302c0c03039100039a050b00d43c04c0360002949400307a8403000c2125500004e0403080040309008281004201c00113001c042070f81503c01a02c05c401c01c1042c10094182500104514a00030380310a150000003d0024100280d0000c210707502007151740c040040701c0c0d00055a88800b45107100821041d03a60301e00203401e40c402c55941e500213541d0f900031841880303014054a207a0301405016000e05c1c0d0300d4402d005100c40800d008510000300201002d41c003c2003000850030040710035484992424164004000105000800e0319003001034802d0701141c11081080c1400003284902e00150300c3e41858010141034403480400091690700d403d44558884d031000310b100c0e112804c182040740d5034802030300f0304030302900c1040032000b042800d05403c0c12224140a60071100d0000c07942c0d81d50380d0450f0b243c85003401d031031440317a4550000358240c80b23250050714507100301c1d604944 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 252985197 1250 252983947 252983957
    0x60603060605031b04150302120903090a1a040905100906060905090a05100b0f07021c0b071d0406140405060103050c041a0405040504061d0604050304030b190608030307030c050414060a 81
    0x35440501805c86e010603542840082c0c0c01044d0100c0b40c48881407000d03003111291010f5810498540007240034248284560030a14032040076003a8112028000c5070090704540301d05011a14140c10349070a003044a2150580f568601500000c403e88142440720035036030000c0c141c896949440c058100600000760a140c106030883d06c2c00204510303400000c003850204c981c0c0e1207031608035500401c8424059900c2c500380960004c00140c0004005008055000c082410300b00d110030501d0035040e0018601c444c034150810f1030403e020412409810b00324145600445050240780d4070000114242c6006a4524030f50420601084c171110324007004840708150208961400c1c542c1d0303403002905941050700c040c1c0c1d0341e0784e4900c0c81d0804006c540c4402c504940cac9840c01403503203041c203a40300b950700c0c4103911000d01038030642004102c41050648408940e244405414800c03541c44070720450300c9074419030345000400c0c43c10812042e42c074040d00c2590100c074101004090f150810006208950380040711440800c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 252986447 1250 252985197 252985199
    0xc030f060402090d0c1805010803070303020c0f070e06120d0f030b04090206070807060b03061303120617010c021c0c020609031504110a0918110312040315060603060605031b04 77
    0x24a500c1c0e55005001c5c09040070401082c81c0c140400ea480100d14110308619003450014082d4035800000c07100c403030384c1c0340c640141e07103112400d401c034242811203410a10034028818002400d00a90070b006009980c204c07003004d40c0407680300e005a591007180907180040340100c45544a030501a83c0240c0d40c0ca81c0160000c1502c400c80e07400101306611400703040b10702400100764482888410303c80d503501401c054000701110308106100c0d0210031469a801400c00c01041c80240b4031580a4000b0790051840308490b4065220404d0228081c04907030007164018840e00400e44840011540b61080c0c0355010f4441513001c5c0070540a128983d0f200c0001c041d054401d507804114503200b4080460304c980d0141d02d0700003840e40c0d001c0410030680042c1d40004071050508480d80321000784460040c9030f0300c1d0f1055940d081c80828901082c00c0c4860030000c0340b9030f007a003c01c0000a205840c9a81c189000d070a2071f04001c400c1d00d555007076085914a00031480054000d1001507601d0030105040d0a071000e42051850a03d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 252987697 1250 252986447 252986449
    0x4020d05070f0b0304050d02121e04050607120e0f33070f03080105032107170f04090b06030412050a020705030d0306030b1e2206021201030c0803030c030f06040209 72
    0x1040c0d1680642403d500000402c000e00c9400d0100f880c04160600c040c04080d0101180c14005000d40703c0512140d10005141c0358250012000312802400701529654551846060298144803d1714100c400700e2000c03603002e1038614029000040204000f001c1c0854403c1400c1c0000070ba406904034240c110f11880000d03809030000c0d0340540030591160034a111056040e00d4001c0060790181d115034026440ba405a8000003511291a110001000720250700c2c1c02d200c0c03d001c040000384014148052000060318034018118500400c141c502c0c0384d2040c01034800d0a002d0100512040300c018009a0702c4410180d60544200e008180101c228411038180d107454000103803d10145440040100b55101420410041a056600d901c10300294403200500044090300c4d03e1660f00a001080c3d41900c4400d00340c0c200090003030307210031903003221045464113408485090134400038002030320342d059440c0c400924102e000040368403595400c0411800c2d511100c105010310180a07040580c016000e02c644a01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 252988947 1250 252987697 252987719
    0x1802090d0c0e0906240604050418031e080112030c0605180c120303060105130f061206050121150e0c090306090604030507020f220609050703090218151201050609070507030804020d0507 81
    0x741d200c0450f40303000388000601e0040c22100b028065005412004c4620310100c60700034dc0d00c14111a1281d5919242090600d01298400200000200058a8130702400609240104469140c2e01040d0807140c40250010400c40104215119139803168400c000107181d6511440140c4040c50060b110359400300d1700c9078040c51a81041d600424006442208411211206405494002c0600f03003850151401c9904c403480000c03041c9200310031551744400e606c00425807103120340710083c01090307401140d50810f000400015841051458442d10800001c1440c829003c190107014580c15245c151608030a0350034810802c0e0031841c442da0024a01c1402c0103000c0040c520070fa0004d8144500040207030405100d00b085400141c16001018030b8030b00036a0058803650100380500c0c0d840d07004103480f42e03143c01721103250a90722411b040e00300708945070034004850305400c528010241141c040f15039030b80d4030030111814042c00c0300180009a0580114002d410524520180240940e09640c5c18a807100d01a0700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 252990197 1250 252988947 252988961
    0xf041a070803091b0f0612070e0301020a020f1b0a0e060f0d0501050a0c0f090303080a180b0106091e17010f05130c0b070c1802090d0c0e09062406040504 67
    0x100e0343c011800c012040c0036030054060301d220040b120003002d485c055000c242d450089001c00504113061401043c02c00b402a46d20400c0584010020b5584280c0c03404003e441d400c010190000511a101421100254105000d6800b441c060f00c0001841c0c40c04803070f14242c00c409000150030100707a03102480c0c0d54566990300c44841c0c1c02800081480d080107840107089861401d4140d04100c080c40010310101d50114405088030741600c0c06001985800d2680c00040c40320786089101c0003012001e010400c580084a581203829903103da6030b00d00e540d50100080d009510326108907502c482c103418080003104102010303110f11044000107040d00481d140717200312442075401c100701d03100c4a100e0408000328201001c010340200384601d820900182d559211200341d9004140d8410b005111110b11318034907134150381d0032030320080004420742454101080000307000c0c042c13240e040984130006802540000703040d034004c4119a52010340e03104d044014280041d03c0110f002d0744010704200010700b555a501600e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 252991447 1250 252990197 252990211
    0x61f09050403090e09010606020d0e011b05150a0e15070c0b010f090f0b0901050d05030f040b0a030c0c02030c090a0209040218040e070807031e05030d1e020f041a070803 74
    0x4103c0741d007040c14051543e070b401800382070036a06001090100c1540032070386142d02141420300301e500484000060368080603402c160f11242868a80000501c01c00003803101c0847d21401150040d5110061070205442e0010365840745070f0b10040c110b418140f480ba1900e076100c115450015660325541c0c2d030b0342c540303003800382d00405d81881520824025400d903403042101d40b4412200800081c0a15008070b03c0125052050900c9003081030a46014401d00b80201e0b035659128004096556485d40e40600c1690071030311104000900c0e01c42e100305010b0042c00d10071000c540050040040441c58000c02402e00001840102070030703004c1c4040e0542e83c40c0d0b400540300c14601d41c500381c1c0386581c6500620040702c40356881c0008a91056004000b10400412050305983c4c000d0405c0343c8844560001807003070750700c4580040c814800040d40b07156000c1c155221900400e825884a47c08002c1488035400360300035210010f24070740d81040200008480303010380b02c2400fa0095052418030500d9140c2e641960002c603600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 252992697 1250 252991447 252991457
    0x8220f230301052a070b0123030a050703060606080c0d0c09080f0102040e1021020f060d090b010945031706030d0e01030e010603060e03041a0a02061f09050403 70
    0x407030813007841c04022034100e850303500700e00380340154480c82800401817103500b0500e84802c078041c0e80c507a411802c603001070201408031030405903e072400d44d9a4004074481a281d035840c100c008030322184940880f42c000d0300000e401d40e04044a601a404c001c0c1440034502e42032055426000030301e101c0c01d00488030920032060005803902e2412002448c0801f00030b00070080d6a01ea00b900303020f40c0c82201058104500784140d02075001d0314070310104103003211109420b507003c0004074900d110000c0b941c2140e80018410b401032609641da407454041036548810034a40150514040c80051300150b002c3c0c0c40d0003051807006c0f8a541c031a80c01e20f8194120181e5415000907240410300d451200e200b602464005d6030a900500d40208201d20040401403500340700d604050b240c520f240e0200c10250001e030041c50b0402400c01100b0780c0502c0c02c556940c014400d11210070b0201c102c407100c00340c3c8141070300e40010064001e8001c44c0d4031010219185c082d00700c000d00392416181000f00e411042840740074461417003900c030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 252993947 1250 252992697 252992731
    0xb030d02011505030703031b080904090f0302010e011505100e0409060b0a0f15050327100e2b020f070906051c050a080c070506030408220f23030105 65
    0x1082c2070315542500300b98000d6100000c00c10000e6402158654113034035151880c00344848516058002d4400c81b10301c01c2e4403905240300d640500420f00107104003144a07400070860710b06400301c054266405a0901900281d240760200120704040d40b07078a800341100c1c44c2081c020362403000010f040781c4982d030b02070f11015503807001002ca40c14041202d030040c00d098046a10000d10742202842e5402d0b80800c07200803c00c02001007411807a04100d21002c020201403c0c0d8107006460b090300d42e4074014541c00e010360506004083c014403402180a0207004140c0e00003105030b072800c02c5608200c101800e401c008500c6150107a0607954000c1c0000000b4002c001004103600c0d140504010b612940c00c00b1101c100001580210005080014007074426544500002d403607404011070942450344940c44a5000a03000003004200191880141070500c41005000300078820040d05401c0f01c400c1e8000c000000741d01090030300c00b40000081c42038450301e1808040781643c1d00f41010030f0a4070026954540e08c2c10545030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 252995197 1250 252993947 252993971
    0x913050a060501080f070f050408031b010c030204030b011415041706161d0406090606020604140a03050a11070f0e06030114331804061406130c030b030d0201 69
    0x2801d008250920740300300c03a0306010000390800c0c1e034003a10b0201030141c070740251007110b0300840540340104414816a5140c205241c0000030400c51001e003841e15502c0c1032700340e03003a01d400f038801c0c1ca05407a0454800c607070686c20914106080300902c1e441c0e603880b40024104000c400c1c1140c0050010b04405a4900c0d800405080d00901d0310101410522025483c42c648066081d8045920034509030f050410658070101e480c0410300820440e0000c0c0c0450381466008956140c0004400340254030a078140300030030018885080d00d03201c18000080000c2da0400c01c0040d0184a00d00030100d0040c464252030440b9540e6403000150f036515070241600ca0078503030801101d45820310412900705101d0072610310350314004c142080b4200e2080c8441060780c1c4440c0c80b03039042000c0c240c40c001641402a040d81c4440d03200840c0c0d2288a1012201111000e0600384808030110161004034010b25000d0003940240204900070741c013604202c01d2480c1015907400e5180480d070740402c0b420001c0401500001031a42e080701c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 252996447 1250 252995197 252995201
    0x506041d0106020c01121d010e0c091e06010f030209041415010f020c01050a0507050708010203040213150302011101140408030712060807170708032a0d0905040f020913050a 76
    0x10388070400f9900440c510000698001105490003050004001901140503000d1410003101a0204074698a0000b20590441c0300203034407403a0007001c82d00044103540d4841845440c52000384a420303a80e01d08008110194001c500c10302402c2e0480c200941007011740300c041022114401c07840880304a00c40300344844521005880003003443d0030301e01912408122040039680d1080e0702025410007500040d0301004911030720946044a90041c04c0c0e500700c5540b819564040d420a541c00c1e48110091811101c0003c1d0610881a0341192010440302c154503640040d03608e0020301801e0b00d00c40d529004414511420084074600c01d610510103c2e84a00745210002d01c0d1605481c141400c0501d42403051140d203400050600c00c592a003c429a072007061401c00c1410021039902c00c0c3d072940b00206100800c02c00105100c07908403500c040d5403003e0102078079507503610000094043c0c0030403201c00040c091420709420028480101e0f14000d49000c942c080131842510f14030407000081903591090101800c554 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 252997697 1250 252996447 252996449
    0x702040b0616111215040308010b03010303080f0c070b04050717070b09090a0914030c15060d060c0201060510080615070b0a0b241e18040e070506041d01 67
    0x162005400e144200d04608124009208003409803008a003010f5903a0f507404200000c0301c2215410745034945008618002080c40a89080740410b00710b0001044640002c01581d0491f40c05669021f41c0f6150f2000e50708402c1c038060405a1581c008101c00d20200b100c108041c1e000f0391050004113000792038115400f2a2020510383c8240540040100304041c1c44400c0c29070350000000c5804c00010f881d44c03603100004095a41c00100700802c0705400c00d282c2c1c4d401002074043c40310180291400241620b19404500300308071030840d4841400c0081703001040c115401184c0b00302e0705000015050380c507000020036500700e80341020009034805042096030700709060b50508400d0882192801d16074103503907400745000010080c00381c8640d10200c160160b520340c01e903412803460644126072410403400302221079502540604c0911401a46480e5403195104201c0e00022218806009403500100c10080a49940500c104051041c070401164969800c40108008e03c5003450703182e003030361406c100d60000c0703001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 252998947 1250 252997697 252997699
    0x30030615030f0f0c02070312230304170c070501120c05121e0a0203090c010212042c0702070501021203040201170a140705030114090105030312070903050f01020702040b 74
    0x429504104911190540151a04403030a011428900e510400801000c1603001001c84500303115101112135000300d004420340e03004000084410403c2881542d410090100500622002d10200621007070000055900684220400e040c80301410b4983d40c4542c12190400c401900801c0c803c0005603004820345680540902c0c0c00d004e03961145402501074000c0e0300320740200103144400526910041c50070101c1c40c0c41540c1c00305400d400c18900c88002034000301d640280342e214007100c0c2002076000044454001c40514001032529007400361402c83c40c14010151042240d0014a01d051000900185031290030554010007000d0305e8a0002407034814000f0b01184610010000d010140c0d074404103800031041d50312082d601030348a6045080c0101921682070f004403d403e03041c00b07170035907210300294100d1702d030355505003202c91a080c100030202c40300703205840e03055100300704280341d4050410303103154070550a04200348907556030789034a070600318208481c0e1070341d9600080050441c54584500704000310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 253000197 1250 252998947 252998951
    0x60f02160b1614030409060501480507030b041b0e01030201050f0d0f09050c030304060206040f0f021302041d0108100b030c15030f1b0d11073003 64
    0x125101e0014014460104540c1e24910114030b240140b100f200c40b0701010800810460340e07201d542e50319400c028030311406000e00250080450000c0f00003160f1202000c1441d02181c06040349a80f005443c0091040c2600842088440b40385c0e8080b0f135041c80030038000c5002d05a07509003481c01d40b8018011049501104a80c03800b41d6005002011024a82c0f0b4196a07080c20419500e10941003150545d000d00e500d0500e0341c504207004d030002101c441d04422003080c441c0044886107840b0100f09600d034001c6010b60001070b48440700140124001c4a00310081034001c02c3c5642c5031400680200d55604e08800258500c590000b0f010454544c0400010b040030041506d0a10703107504002e04079858401021551810b035071a120b021a075581c090000c00341040c00200081d90500e00340f20400550b40048817007a001a485000080160039607000c103046401840b1400352a010700202a54000d01a41007203114000b024050a030000b0112810b080b5403001c8070300b40880c1c2c0c3c0e8204104081d028241064001014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 253001447 1250 253000197 253000199
    0x5030a1409061b040f2c090c0618100f0906080103020a0e0405011b0f030f05010509010e0403020f0d09091b0203040924090501051005070206090607080d06060f0216 72
    0x9600401c445820981c600c042c801c0340b08034011810414040c5801654402c5104180000c01030409002168038004885200c00d296454017140c6c14944421200c990981c1c01040c000d0880d40b52142c02049a500340d80c2028490f1444030b004642c40644a40280f030100301c10740b400d6111550040302e124000c0985240192280d1305507804a45140018031401c1c0c540d441c40001b04081000a4001084130504e40c072864841e100381c0d80d4004d09082d00400000003191900c403004e140354101c0c0c0201416540301600103a100c0c2d18001490004000c0200103038118080c55031100e028003400c2c0705440003595240d031000c0b880f80c10210080115005409001040c0d0f05038244d19020039008400e0300c1c1114026100000c0300451f04001580312200144983c1d02c4108400b00410018041d81c0024140c0d03005440010200038000d2080c1c0c0c061090b008060f500a0051040040c14503240700104045071107202e440d800c1c920141006000c2d1403a9420040100d40f0b10103808010320350401200700d01703500981c82c204000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 253002697 1250 253001447 253001461
    0xe07060e040213090b01120902060f030601051228110702120709060e040606090218090a060f08060a050708090a0f0c0b0d05040506221b03120206010f0f05010f0315050d0305030a14 79
    0x51180c44502c1d2f000410200020b03121707030b0149060750314210500302c0781441c03454001c0d4019004004061030304440303840e040802144101510032040a5000305c2500c500c0d0220342c1d000c105001c071004521841601c80c015000c5202c0a4034082c1c640101190b05424407141058600002500c2c05600b20304030249c410302c05051040f140d4030100780b01401c103941c03140c11134907a15051000f6041c0d80d00301040303480d210300001030344e2680045d61a11407034640400f00200e481d100002c0302c1602d402d5448a03580c1d417007034070074030701081030346e800840f88074400d94040039019511314600003075400480c50300d01c4865030303003080100748102448804c0e0700510842840040240f00711104006051074280504440c1000008205030084559410040c64110b080d801c5441900d1400030740c6c070903090240d50030807004001c00140c22240c000001e000d0b50700c141c541c01a803880800302100148009021246260010300000480d51240150032106600941d034040d980d02e4020b0056041e6580072200d40c90741e0010700c00300070751 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 253003947 1250 253002697 253002709
    0x1820030a0504020303090d15060504200a02011407110706020c0d0b0901090b090a0c330c12030207110603040807030c08090a0905040b06040e07060e040213090b01120902 74
    0x2001600280c00140c0340c84a002103803a600a0149040c0c0010707007202d8890520200700c441c20b00e01000305d20140640d5071034000344030544440300390000e1031030800036107070034001014405400e6100c0f02d0720001852040f80e48190000c600156180800314101944080b9203d40900011002d002503000800444040001141c00c400900c1405007214101c1c41c080784100c14207410801a00d504006007114500f030480d1940d4407040b52080450310000d03201000504034a1441d6111182c03071b0103442003014420f400d020704440ca1902041c410400c07038100301c0600003550781c48a0381102c003111350b00182c58a5443c6004840c0d140b21000991040f1028403c100000c0d0000c411108000d5141c68051481c04040c1380400300e40c02503400840e40407482c0e07980408c0c21400f0b6403180380b1482c002c0c007050081d61030303d00900044a4108885c64500e421801041c40014007510b50b030075096501800051070a10001c81d0703003440c0007090708824903aa0710340d84035500669001ca4030458101444104110f100782c140d0000d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 253005197 1250 253003947 253003951
    0x1021c1202070f0c0b0309070918020d031815090b1608070302210d06050f030703021908100e010b0102030c03070f150207050c0910050108130206070c182003 69
    0x684107400040c940c2c100007a041c00381c41c00d40e62020300b0303010460b1640700f00d002c40c0e001103600c83e007140301d00c2c2c100240c14080c1d40200c1c41e580d6640c00c03051181304001d800740200d41d4440c1308240d007408182048000d20780202c100040c02000300510510101c0c80d00c40340104240710a521006080340103000c00101060030b00310b41165207a116003e03a941310118981a03060270100320140041c1403840e00403c0c40304465000402e0840c1c0c0ea0201081102e46a0003005115882c08030724035010341c4061418001420000c0c6d2240d1136004600e00c900c0000d0b600c100051400e000b8008080d02a5165008608116030900036000600c000340017641c1000300c21020b26582e402600005030201204030b100d0340901c00e91012101502e03450900035907880e170303035804d2990b600c100708446035008000d001c0005125003c182c45c0e500c142d0740d050351031407165111303c0c601281c1c998800c642a68001d8040180c18001010505020028908044d6141d10205881d00020454030941098020000084580f100c590100ca007129 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 253006447 1250 253005197 253005227
    0xb040c020c06072a0f05040606051e0f070f02180402061206041104080a051b0d060b040b12071d010e0c0c07180b09060607023d0c0201021c 61
    0x158540e0740c141420403210b2011811183c00340c2504e50107040e00c1010120700000da45803044c4210b6100c2d65482400103c170028802c140000301d0a0280840400c64681712413034100c000c24030b95040101d0900d188940b944520000c880c0f03c1c20301420541181000740003001800c180f801441a5450141c01148031480f0b82d580d8441320300c0020000450355501c13944400402d550031510300d81c0342c9854509181d03441d040840c0a0714144502705500003003001980e01c41d114094041d082250081503551100003a144072060f084d4055150004940e0503195090a001c01800c81c0000b0290326103402e125283e42164010340c0b40c22107042200500c1004600d10440c1e4101900300310103a51206500051400c0940c0c1d0b4000451192600107160784008407a00b16144840e8105e860143c00d490340802c000f4244514000290041d0141d94514107a10726482e104281151195000780c68901d9040c407480c0f640e981004800105001100303000a550b4100810b1050703007a2420415030408100c5000760000104100030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 253007697 1250 253006447 253006459
    0x304031107030f0c0806090a030f030e03070f08071707080403020d030203090a0e060a0f1217071e03030b04050f0105120a0c0f031103150609060609130905010b040c020c 74
    0x61003011000708a2600210b400c0300e140c4a034050b10f480e0002c810401c1d403103141c0c5680700725404241300040110310f0b580e50315815210764142c030741c0b10b86081d03000d4070004201c0c3d030103030006000d003401007202c111010307280a10503103040d0703601c0700f291404494840030001003140302a030902000b0001142c10007154262078040718140e07600c190a240480c914418407495a80185444200141e8032003180030302401340744100e546220312a116021440c40991902c181801030304d2802110000c0344140904a0052048480080c540120768440d8845150b8001d8841d4034180940e4184040c594940326044580c041210240300781c0c24100310010300d010060084038410a44003203c016410701c2040042016944001440c000c40c0d65807480c070f000c0d02414032003680c00b800d409000d0b003070301d240100711400b004400708020b040c180c448070f041c0200840300070482c5070024410040d2000558808004032090a950580031175081d81d1403502d5030950710301c0311905015038141000e02c2d04654010581d60300d226010b41d84 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 253008947 1250 253007697 253007717
    0x1240e0406020c1e0106080f070e0c041e03030201060504020301030f230114040212030c0d050a14030c070314030907170a1707060e120a05070303090b0a020d061a030403 74
    0x4160000c3c424240055424810301912103003440103c07510200002c1900000c00c0348036a20300c070240c2c84083c0d180410035240c10010017404007502e100c44580c0c0220840aa460400d40c03905d8000007441c2a5052150956115000c10001c142c0d0901554000d0a01074a09500b55450340d552000c08102c2250000c0c4580c01c0d47d000d0003048440c501ca503508412b801c034001d006040410050400206007914207a0041c181c0400441e40d5510000440350703514a600c00811100e03001c01011601508805c40a8040001e044c0c0c0100700c00d141103002e0b5008426460307455076a8040d40c50040d1881c10040c1d000100c000e418001c0003902c0c10701051b403808442c000c101086e2207039100100c1b14103000082c10000c1484e944e003c1204008805400078100d11803080208221a410600c01c00b907491080e80e500ca0f0002800700210383d1110312460151108501c24140868030f10659600c29003201d01c02c071880c40329154042031000380242c0500429005100103018003044000a2111030624840100050280114006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 253010197 1250 253008947 253008953
    0xb030d1d03101505010e031606140d0507030c110d0801210f03020a02012703150f0f05060a060302210907091b120c0c02090720010c0201240e04 63
    0x402c0100c200b000000c11815030751600c420000c0c2c0300d43c0035403400107640001a202c0c030304001032022a4460010601904035280c10002c0311a030f0350b8090b821600b00000d001e003108200c9180039090281c601600c0c003059610300300074020032810004031060001e50010015119035030b00800c400d41903400415403543d0541d00345510202c040c203a003200404c0501c058500c00c0a040c0d020444481c0e1901c02d9a0b0b00b0140201034462040c20302902906044903c00e80c1d00c2040003995003c101d000700b00340d054011031800081d0b28800c085400e54000c3c448801e0300d034010041180f40007401000074140d05d0804500305445042540030b2004608810b201d4107006100ac1a0900001c103d000d008088551080c815403403c031290a05143d00d601c44103001c01e0703120b01c1d0300422441d06d0180143c00c41040c3d0750300c0040c1b000c54003041210b001c05041c4e201444081d401300c204019a15000d0441d01c038212001003000e1400b00402404c5a0b041e035030710200f40e10324407c04058202c0d250503070801c840305010b200c0559101e0341 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 253011447 1250 253010197 253010203
    0xc120c0d110409090201020c0a08070e071e02150603011e050403020c06030705070b060d020303070210230c28080d0b0a17060f13150b0a180b030d1d03 66
    0x789503070400d00310100d0005103802d520742241181602c02c0c0d0a98049804001c2802502c1c0d409000b803066a0704446414007204038030f00c4600f94850401d1501c40c000310505203c00c2c01080e02142541c005800002d440710803150070800f025002941500200200d800411070320040c0b481c00440761056a445074041001c0c5031080055440386040103002d41d40c0c074240018007400c1603101040845000e001c50000803500e15048804d9144545c025016502d0000607900304045207508044c40014000c1c01c00c00b110051040c146258421800c100189036125910410300b8034003072818000702611081103109040b095641110060b01a0384011000d803101e0511040c0405801c0301c060300350b04054410380000c2c1c45644000c01a1918140506888440d1242645004400d02c1282c0d42640051605903010004107031888a219100c54070400060300e8001b500000c40c80c0b00568407003d420081c400c840524480300c0c0c410194a80012802010391400d1058050654640c01c40c0d840103102c121240d000c2c0b161824 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 253012697 1250 253011447 253011461
    0x4030b271e0c030708030a12020703120b04110a020304030302100c020c010c0c030b070905122a0d020303030f070807020d080a021c050109020a030b04090b01090b0a1a070b0c120c0d 79
    0xf401c3d0b507142512006000d80c0c0340c100708688400610b104020245102c81807085681d00b60b0956240742810710703080086000f611102d520250007664809800003900c40380c4010785031081b12603019503034481c61414024640466954002006407802c1602d00030700350000f40039000c5890a09001c180d0000c941404074441065900282030715a40c00100411703150b01c001502c09a0b03030100c5505034000c002c01141c507079034804c07922400c2c94060b91030f003201030100c0340b42c40501c29408010f00503840200a507000c07130306681049c3d890312075120107503040c080c00300e030014403440e4402a2480100140342105c0001005400007408030050650300180082140c00105003540c0e82421004060056595a000c0c2c40300079402005007000291030661210160316241c000c081025810040d041d44a9080503501c0005100d11880c040d444012400b000030140c85624500790b0329005c00100c2d5455006d6070811451b41e40b00104103500d450310401c0000d01488014219640008a02103070503160004001c03e00010805 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 253013947 1250 253012697 253012699
    0x5240c0a20030742050606040f08062d0c031e040506010509071d0f01020f0703030c0506130b13140a0b0a060909031218020604030b271e0c 61
    0x1078030a040c80001800303510784000f0300e0307144030000d160385004414900c414024141e13208081c0c07840c485055216041144c020741c4c010000b615041d51102c4c0020040440e600140e9990024800c01006003401040e8056014402030200b000c1c01c2d0b250310100c1c45100c014184a5064000300c04203ca00381105504180703140f01444071500f80c1090700300640d40d00c1092085603c901c240000083c07507a88140e4034171100c10070056010300038250302800c021903482d2408000781103100d13556102e4040c120070082140118000c0d1600021458542046424900020441040c6080d034001b040b000500b0740008071b500040d007040d101c81d141c0300f40ca02401200340c020351400c2c00348500c0300002c00380401c03401118021550540200640c66950003003c054a24803031000d40490f502c24010091904142c0012240001e2469a01e050700b503035a0000354150040c0d04184d03200070070541004100324240b0b280020307032420030400703039110241008802c1da18151701300c05c1d03841c00d51820340c02c8984000401000c11000c038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 253015197 1250 253013947 253013953
    0x2010516170711040c0e0a1205030c1c030e03040b03040318050907030c090e09120c07120309090b0405150f040b1003020306030d090501020d05030613060305240c0a20 73
    0x260030501c20301c41d00030700f249101d1442c0100c01101940030b95807202d02c500380600014082440c0c10018080800c90840a488901040054400010302400704c1e1600104c4040c00890b82022004020200e80c21a150b01d15075a01c1044140f0000342440240c0c0c1d4050b034146011034500c5c03103150041120441c00e5100580000000c002c4c00880b80c2c241c1c02018400043d82d031400d807a01e503610007021040b01c00340c81024441e0030492486100381ca1a00041c060100300c2012078030030503560100d0ba2903022007503074180e002621003001030103e40c03454003803c00150300c01c9505000d1820585045200c0100e0342540038420135802101c1c004a03111a0065202d80c100203210018282c000c05018000e507108075440c030b01c1703402204d8040922034014004041a41c0b0306a000300740812440009071003507400944040c0d8021100d10005051900a0040b1005907201e03102504040c41e0721840e101e540c3c01400d4040e811a0003d90030441002d0401c010f0750f0740d0300c91914000e030030b24031503040f420014140c081c65920580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 253016447 1250 253015197 253015207
    0xa0c110709050a20040b09011e020c04110a020c0402090f0409060906060b04080c0402031302030a0f0b070203070305120718030501060e06090906061212040f0e01060504030201051617 80
    0x1075070340520310035000c8003400c0c04000c1d4080902503c9560141c08071106203001e010910581180b2405000c1004040c181200b04001c40c40b03007045080031801c8031200583c03003400140510b0401c0d00412001c1142d090200d0b080048500f000b94841425568060141d81d0110702240990750311920101c4d5414003030401c10122051b0704044001d8901d880043e5081ca00b0882c0c00605001c0340011141200c0c001c001038913003003089004000203036101030320300e00a07207015081d1400560390901400d58501d10400c0024003400c11850a4002d401e8002c0068056400522600003c41d801170200c8002000980c00b50029655003402a01d0f082c00d040d80040c65007010190200c10008158000000e43c1c0c640041a195138bd82d400c208540060300711404c4140c0d030070990214900c0e0910703081a8120606480a8480c105482c510803203054000d40c2c03007015100c60540d02040304401141c20980904060314289203042c0c150740010f00300d0b11400e8844d41110680220180504c0580841208400c980d80b080e65070324 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 253017697 1250 253016447 253016459
    0x2060f13051212040b0306030c040e0604030e09150103022104081b070b1602280603060b0a09030b09030d020706090b0f0118021b060915010f030b0a0c1107 68
    0x301900d4040e03a8080c10018148510b484000598511190040a4254a00b60409121005076000030740a141c0510503091149207550b16800b903544403a00390310081c402c0b40f519050051201404083c5035004003400800d000a0300c42c501400030600b03070282000343e55030543c803c0c80403c05060050100660360284184800c00c183d08006201098040310700c0080011031004098840b0142d00c9035400240c0f00b0000202d0304002004e1800da420700003001442202c40940d14040c001c10b012201020b400d0001000340000b81d014444c10000d4004520307118108001d03104058a02e1004d4040540030300c0d600b2001452180081040b204500450003065448081ea481c091008d401d00b54021a941c0d0112000541a120000002c130304861102c24a20341c403600d203c02180003503002d81240144a0728400322401c080408202840c040d26843c401070149011002d800d02c0c9115061f0000c00300402aa278041010825a00455070004a4007000107450b01001c1c03020380310152128145001c40c001d030303c000540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 253018947 1250 253017697 253017727
    0x70f05070221070b030115031d12090a0806060904030302071707030c0b01050103021306080601030204170c03070b13030b0c0c0a1203150303050708090406050607050703030f0801050306070c02060f 86
    0x204001480884510903100e0704c503520240001d005010040c080380442000640c0701e07401080c040d442148541a00f039042072410380c245140b02407030103541d00002800310221309003000200d00905916010340f0250070180c00290a4440190011f02055000720303411061186402401d000440b82184280d035a41c1d140c1740240c55284c5402094545103901000018154000d00856855803080c0101807071070b42c10070300c2c01e8801c210058071081c1010390030322001c141c0300d040c02a0108041c60050003441d900728224209480c0030800d4100320303e030a00610107080c030002d102d000202500d40c86180c02101d551100140e8004d0702443d0564011886983d80d500305202c24010718803a07208a41d58240701c40f5040c0c80b00103058160038400100001c900f045841c0c040b07600d10000e403a58010080010510700d60760710001e0200d800c08201031700c00d9004190100105a000f0052a694820f2410700c109998580f0000944940c4c004041d0402d0200c403424074000c641d20541165000021118629141d02d0003001d0046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 253020197 1250 253018947 253018999
    0x806030106060905010c0b04060e0f0c040e01020f040e0411041a0415181e060b1804090b06011b0b1f0504050906130302010f090b06090a0504030206070f050702 70
    0x4025441c111001c120244035620301e80c04c0d500181c583c850818140d40d107031003180000500640f140c5e943d501801946290900c1207021001880000f4013920701c0030b00c20401101d06001480525070300c104045d800c1c280c00c05064400715036031444007822955481c18007004102c505007041e42c1c003078641009440010950740b41461044410f403805c2044440c202510721507903070a4010460300c04848040c80365000c0007900101c803d4050413290f880366a012540c10020b4403da504498030b030403004220a40303401180c130b8003515220700c11541409002c2881e203880101401c040c0089040210b28415000c0085050505186466104c1048022882c04101c00d80c02c0c888070388078018002c02400000103143c900f034010f6034060079500001d0101c079258114050041492104120295501d03100003003e40e021511400d00c1c591700450010100d8503001c41004030061004100c41c41c0c3c585000e007840f020950002d103183d481601e90801134070103a1a98406d1f103944c007603000700a51100700020318654442e4004400c0c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 253021447 1250 253020197 253020199
    0x70801090c0c0209060409020d080a0c0302061f0b03090a0c080303010801060b2701022e0507020a1505130605010b07050c0619050f12090105090f0109031704080f0a0806 74
    0x100d000c1001078100c1e41c9102d007050283d4402c9049021901c02d02d4113030700004107284001c100110003881541c174511150851003038280070a0244100e0030038160107000041c0d0050103c0c0290066003101c40001d0044e0030b140c040e5814800c800300c0003500040b001c008000d1250740000200b0109503079502800e07502ea000740143c40362542018000221090200d0075151000703481040c2c1c801d0b404000c0c00741070302c050349092a02e0461003290540d614210010014914200000d680803850110f1140f913030b015200090140c80c210b50040c00031001280c506544400e08180601001c103040d102d00141c41751942502c80041c103072500d00f40000682d90b107400014110301d4840d00c00c1c2e0f40035030100000c10105000b011401076455003802d0100c1c840511502c001c100b41001e04441074100381d48c804600502020885449076a80e6681e02413048a5204101c1000742c28140e4000340620071203607900510100891402d80302041c1800007040806c0440c100380c0d0503004010b0310054441303d10b204002c203100c0d0b06540003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 253022697 1250 253021447 253021451
    0x1419020a0f0e0c0f190c03030510080607080a0b030f01061a04050307031103010207141b060f0d05130b0907030b0f04020906010e01030603020a0f0603110306030a0f060e030307080109 80
    0x307511003011060801c603103810585030203940e030302c2d508040180d01c00f142c6580c0d0b40b042040000c1180844003103812500c0707090317614800b1100541c40d000e0111480540007100240e6084010070031002e000901561000807481c00300d6041e240e0300c02d410302900300f6400c6264140211105600c40d04015400202103071071080e0051103400d5001040d800ca407085000d41d40c1c01d500f20040c140042000d074250303551210ba003d4001841d250064540d20580040e100c3c10100d540c010990030030b4075040b04400405d403a40304540340e510381000071480b400c484c0318071542c2c0c03e64551a10001102004003550301042e65804c015503d82c03910702590100c1e21107003107010881d12046200045031102c0c028507a528071843e4040c0080449455040054a0b80c601048405040603101d001c040700586a0200f104018452201c601a40504210004d0140c4a001c8400070105405004108599800041d5410510303040092044410140d007082e1014001910481d5024880082402a07056200c2c140c203049036840d81d42 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 253023947 1250 253022697 253022699
    0x206091816020c040c090b0a180e0a0c1e1d03060f10060e030703021c0f08090f0d0c03240c02060103020a0905040b060103180c140306090604050a08071419020a 70
    0xc0200b25482100020002841503030103000c0300c1c42d03a0303008083d23642050070004281c8074581051040c03165a40c02091101043c0d80130b11804900d00d0089004d0740c1c0403410160701b0800c8084480c0d403514951200042048800c440003242081d20030341060100002505460700707881e00b03203001301055800340c60f040d03100414101d000500314070451001ca9040c070000c0140035220f24503020005a580680122031420b07200e600c2d00f038005004c41c040704000c40e100d00c41c0c0315100c0c840d050801c5141c170071809000d80110401a03c600000700f20100039000d881e07019104400d8103130b171124a400742413500781c0041c03415803408400007001030300050018100d074800c507100e8416a8403162128241c45d81074074006d140c1100d0b100494029802a00010301e550f0324081c90b442c00202da500c9090410b40c01f1f5005510121026a01170540c0c1002d015160b131150304c0307900031f11043c18140e45a03651241d9910000d02520000300e0058200401c4110310310500c4007000480e00ca0030102c13040f141090214001c100d10074903407000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 253025197 1250 253023947 253023949
    0x12010b0301080a111210050907060c0507050420070f0506010b0406050a080c0c030d09020405060603010807062609030c0d020c01050406030908090a0f210b040206091816020c 76
    0x11a07042c1e81020300545400c410903541c0540c1c1e03500c20a21507134000c2842d00c403450740d041c1c10090000c5c02c070306849000c01d0f5410010b41207818580103401c808208001c03043c089010032000103e05044070015200000e8018070041005c103100740380038a2104112000030000180180d00481c8060540101e05a07a200c5e6607031221100c0034400c500c140c03404200b0500a404205000f00112036000008918892901c0e0244a0840c1140d003e194501080c1d5500c50b401740c04e50a0074072031598070078025500185594180411350781c1d1201f407480303548204149503080c044803004100c3d4031700c83d0160302c510381c908070709140c0a180d44a030802c01400c83d151054002e0b52420b2480041c88400701681130716014a0036042240132800b4100d5044107581713040c0200406155078660700300c00c4c0c000f041d402025142d81418426024a403903881580d80388402c11044110010614082c1c0d000d030802c1d4112089070742d07443c00704003150580440054104090a01c8000c100d18040c0c1d800424608503155801d6640c4100080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 253026447 1250 253025197 253025219
    0x190c031b031e031d030705090133020a230613030e0a0e150d05030307020304060f0203090f13090f080c2104090c021218090121020616050604081201 65
    0x120098005154140d50640c0031407130300882400d2032400303410380d8403042c1c5030b0000c42e09a4601f80e10000e400d21140303500b81d840070300c5881512428540d5200c44e05800308070040080d502c1140240150080c00b0503414902c0d203201180e101c01e403600c012015100e251408807581009100031610980209140140406441c902140c500d026203000184c2080c030350300da00d5681e0101007001d02486da00600049003000200f03408001562003500315500540d5150300302034000744020f41520700d540135584140140341244d030342c00c00e80d0319900e002a2000c40079400d40300c1150020340240782018044001400f101400c1c030030700100614030345172403c0445060341194103900341000d00400c4a6000b0030710a00c0240315588064000c0520070f45144120341d02c0700d5200d178401d492503001a291504445020020b00507a09040d4030041c0100710340314000003951141c0860480304000c403007000f442602c000908600d01000008a22586900002121034030f00e014903081c01d20b85d0102e400b8580c0350500e2030000500500709 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 253027697 1250 253026447 253026503
    0x612060b070b070302030a0e03031006020c0307030b0112021507060f060f050d02120a02030706020c0a0f0501020307022e030b0306011a0d020a26040309140102190c031b03 75
    0x41107880b01d9038403880114000d41010b0314014007144c0303c0c202c17650524170070005035002e20580084a82030320301c0d017003020f0700d06819050038a000b40c00c0b40e10104003150310300321030504440c1441044a00340d4820307c0001c0c000c0c012071140b4044c071040800c5220901105500144000300246400c2025544a031030401801c00d86100784c03640300105248410040c14070031a550141d507040c401b10b9400c12461781c0024240300c5590000401a840085010301c44d00e03012018000914152401480050500380000c0d1288a03000019001c0c0c50344100e800c0742140754480b1070304008030740c248a0341903140420b0001d019014000e80c0c544603100740b50001c10410210021840000a01e165041c5400341038980400130b500a102880c007030006000101100e1071710b0301c4a90f210034080441e218541c0c80d191030081c1c03030f500c1c20703400944000780307455030441c2070766000180302901080c500d28402040265240944981c10325410042c060181050074040e0400e00d0544182542d10070204c030910801107619405c2c0b25261 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 253028947 1250 253027697 253027703
    0xd0818070303030f0f060b030f0609010609030807020109091e0b030d21020c0319080a090206090402130b0a0504081c14030402010c0501091202010c090e0f19060612060b07 75
    0x8108100081c084d5000c103450080c0c0d5079001c66003600c9094007401712840c9038030400b202100081040022050650381e10741c0540115110f6240d5414942d0041411455020081c18100005050005d5a01903d44880206540b120a208000f2041165400c003c0e0f0300c0b004071409403e0110070101c3c1c0c5000f150000c51180e11b5610031032042c1c002030440401c0d003035001d03034421415402c100214000009100034003042001c0c07554161101c0705010010b0015038020030b044005490070080800590395a407c80c0c0701c80500316009a210190701d607445008030f000b9400070401400004004400c00e8000d000ba10442d44048203581c4e500e600d902c3c81440d4203080341006030002d006115801c0b0038280d06805140c00c00d0041c500503003110701c1a0b03551821181454415240c81ca803e0440038240c550900480320320048a241100300c0920b002d4032003003a5800035041c50840d200140c0040c1480400c82a5420f400c00c80d00020301c0000d50300c0703401510100401045080e0f00d4200040400c0845000c02101c0034158 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 253030197 1250 253028947 253028953
    0x3051b01060807080120031b0a080f060301140f06030c031606030c020304080d0c11030d03061e050f040c02150c040801060b030114100201061e0e07030c09030f0519050d0818 76
    0x41c2c03046d040c00d003031f40018144480c684554010025a88041010f45000c05a94403603030ba4909000e00406040031008111521a0381000b20740078801d240c50500941001d44414400400e494410000341481c192116550b05403150762040e5000e84400a03141b021a030300c0362001c0090507007100007262a8416030198004550117400c1c3c80c0b03030040c486d9441e40e480d18004d15040281400100000b4101502204540700281c1c90f080140205402285c0c4e113592800c01c0040340300c0040c81d040103d1000c000e1550402c3c4100c2e607440908840d240248004500201c60301100381141c50201c0c4c82417595001401031000d550718040000c00c1041070941103034180c4154a000c4080700e0700450401035104000c114060465403503960006804c402c00500d0000410040014400c141c03d0800340166100700030421000c05040500d107464141d040f20340030040c4d80d000742c1030f003246154030b0510740e1503c2516001c50380e10030080001d01040c4080450f44403049406a9540586038686950145244040041e601d00740c0e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 253031447 1250 253030197 253030241
    0x190507051e072103020706050a020c010e040e0d05130518061002070e011403150105091f1a040602010c02121c060b0c0c2706060703051b010608070801 66
    0x44080d0880395140240104840e80c1c15210710249071a000c0038080c0d1200d403e41c0082c1c9030205501882800c01400e80f42c41c0aa00300915644025075606000310018144803c44184a2060b00d0300c5d044040c1c20701c580b40c2207650200c1c142070300802682c80380c40e401000b20b00d26078000c40c00d460b100d008106001000440074149803a05002c100020140700443d0065214919000507a41d0550211342e008007007030810001101e00082c2414100010401200341c0342c01410014060765413103200d402e80042030841d942a81e00171403140b02415050b40c0e040640912002c00c154200c005a010080c01030310b1003a40203000608d848141aa07075044003418840c7d4803903091040c602c2110308440c00c1425120801004121284e50f140c0b054159482409000700e1508401c0102601d411b15003050300d81d02d061805100c0e90b002003a0a04021004083c00c094031501f40010502e0a00d84248151031141a545040c01c4030140514010760083c2818410301c0a98001e80c0030004040a062207800d4600b20044840c02d5a8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 253032697 1250 253031447 253031473
    0x10809011e240303090815090307110a1d060a080c030a08031018230424110d0b0a0902070b0a0b0a03050f0303090106090c0509101209060219050705 65
    0x382c40c086154000107001486070040d6201900c0d075040046000751174042c01d180c10001058101203540300304030b204c0e444c80d2050040e4420004210b980c10b5401c00000d140050300200028000f01560b0301c1503408044c41080c0c80e651041442c011402000200c942620711a5103035412501c4031042c00303000354150845e005e01404110708100a5610141c0850f01c030100f6500c888580c0c95a016101c0d0008489a454004031000d8206840e0403c165030341c4544200d06282c295114000441f60000e5403001c03200d9560306188402c000c0c1c011412200c2187c68040d110302500c07042c00001d00c030104600740700c0d8010001c00120036160303100300c0d40c41980000d40341c101030707840403252405031410f20310868024200290000115000f4407007441440c09490240da920306052410034251007064020a10980c0f17000c8a0421a41d00700c1c00319408840166409850b00182c0101950760038a600030360040c060030401c00308100040340d40140100781e5144000c000007207000e10700711150b004a810040186e8002c517100540303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 253033947 1250 253032697 253032701
    0x30506160e040537020a18080c060d0c030605040e1006090b060f03060a080109051c05040609060e0d0606080d03050c2a0c04091109130b2d01030809010809011e 70
    0x103000f4590241841340c1450140001c0341d000a541d00c000904c5031320171462450f00a05c4920040c280040102400038281c2e00240c05840303860501100385a80d064a485264001e402050003000020010032418007225881e9449040c030761001480030b4a03000010400103030383d201d000180f0001515103030a0446c800703001c62071a40090100e582c02174150038000b640880034050300c2130642c4900082d01030350650300d60000070325032164801c0c820300c10f081c4820301c00c055002054100300c60300391070550381200101d00840c002c860043c00c040c2c141c1d4204000810101030009801841c94995602040f0541d10010b6003581030046910402207980e08000031010010760301c03c0856000707010030503a001c1c2150000040c007120f0700610200d41e003e25005442c00c00b4035281c00b68a41c0514002c114201143c01590f65250521001b000c100042503544186025040c0f81c46c41707080c100050b0301200701c1550311380c02c1802694000640b5107000403034040001c0c8100030103000e03903103410303107004d102910850a12a030900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 253035197 1250 253033947 253034011
    0xc0207050d08120a0b13060b09010503040f0b010b04180b0a05010311040b040905041509023a050114070504080318010302121504110c0c0f0109030506160e0405 70
    0x141e80c081808680350303044110701450b018003140b120020300d1580610900c0781005c95100038006c0350346041420031401041604850290794246400381d0742f6511482c0c061031903030b02c490000d444030400000204148600340021310644841200c1280c040031168618800c2d01c00c1c01102540020410354100400e5019400c4800110542ea42c90717070425843e05210001c1e9005a808459459280c005001c00d000600c0381d81d0b10340701403070001400b00c2d00e0580c01103610140503080218506803000450082010f00e0708e00042490b0300800199183c01c803070b050040c007806850b5040701360720600002080b01320740500300700c40031a0100c401440c10b00503483c1d0001d003107080340701d0220b042c980c00300840c01c2c890052003030b1544140d203120030101055001405003c1213612404007401100f02c2000300c0036840c040080c020440b2442120b0490f43d042010340100d404035802e5100504d6486010306200601801c1c050382c0b0803d000310342ea5021125580810401510350598450400300840c0451001240b20041d0b840303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 253036447 1250 253035197 253035203
    0x90a0b151c032d030c0503070c0f032105040b0705030709060e060f07060504060c050903101a121c02060f1302030f07060c0b0f01060912050703021009030210030c0207050d 75
    0x3c0c1c4007000c920016006034110b0241030b070708080050041616600742c41100fa07806000d1070203038118501141c0260601d0307500c0201402c414685654401010304c61025400845a0100c0c500642e19400b065207006e4107040d40d081b96007401400008011900c00c0094900c80c0c0000c1da41d04c00010300d04282690704006024a558002200708541700380d1103041e40003000300500c10b40c4005402d142c2800e260081b65080040e203010030000700040032003990000b90140317813a92a44400101c04802c00f0780c2032044140d2460340d070b03040821030603446c80204002c9584070035100700e4001d800d1540d82d4880100d80300d10b01140c240d4520340584000c619000c03041440b03680c03414806402c8503803000c0b00105591034034480e68407240c00070700081c8980003008103ca011903040b00c018003d51301a541084c40241c8504484c2c012003502801a0045100f1300c01d00308442002190040c04204111000d950010a042c8683c0070903801209444204521350b0700c00d00c01c801c1600085d0f8040d00c2407905050420043c44003e040c1030f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 253037697 1250 253036447 253036457
    0xe1e0f1903050c0a0c030807061a0307180902042a030c02030d090f050703051606020c0d020907050d0204080d1b02030a1205070501050c070507050108010e1518090a0b151c03 76
    0x1600203114150084080c500821a0070b448d4505407521000b1b0b20401004800803030100d0400380c40c0c43d240001c00f001070f12610498030303118421716110b139801000c1c00da0003c5d40c8241001030b0701c0c03c1c01e00440704105400e640c407207800c002c0204004054041d2003070340d1006c2005074030401200d44040034551082e50568400c0d040c4c200151301076141e1500d03126040d0030988a03500305448090025150580700002020540050601364080c180000c181099885001c0d000300900b40020384194421400c8404560703c611045442c0c0b03440e807501c2c0342c1e03500c10401c2140c08501080300e510400c200d07054100c00c100d6030080c0181041210380d52060440146c81c64080107204040c04110005074080c00381034490380c0c107201e6264446d4103e0800310301e0401140e0125041c000220014040c9484542c101540f000043c0b501d111400e00c040003192040c40c07200460007113001c246044c40544640800c1241c40203014405c1000f10f40c4a100711a2051000c40c0103455105110060804c0d070715030755120080f030703481c000d04003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 253038947 1250 253037697 253037713
    0x40207031407050706020f0f1c020703020a0f05130509030a030902060d0603050109020910060215220303090219080c130b09130b0f10060309060e1e0f1903050c 70
    0x140c000c0754009074022101c9400c08103043c42a264100000d00381400c120008200d000451000d29498000542000f05028440c003400e0b1a070368000c01c00b1000659020300410516541d4150440000184e8061207208204141960901c038030319012365401100070f14040c502d000d07029017054000b442280c00c1282c11071400d002d01506c0200520444000b94020070012624102901c104000c581000300000b064907000e5006010069001450803d403518038004024141c480c4100e60340c220202200200040040540080800d0340c90b03000803413600d1084d54801040e42c00550f00091803051401000f5513503104030104010780c640800507949681c1c1e0420001800c1c00d0007808214001000c90f0741005009504c5108030401c002c0b19551a0b0102c0e510400280b142440f200112080307a45200b8581090b4446281b10b042c0000c9502800070030340b0b440c0494441000d001c10f9000d142011402c80f00c054014140801c48010010a010300034602e400c14003550315000d0b40d000e852913007003000740c40410300c55031399 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 253040197 1250 253038947 253038977
    0x10c060f1803020105010806040b18070e390a050f0403020a27230a140a0b01121104060c1703040503070606080d090e07050904150906050306010308030604020703 71
    0xc5580e40840465010480c015102d00b0040c0c00d441040c0c0c4030703000c40c4c1e125404200100d2440b5440c00c4d000300001c29122050002440d0103454085540c10244e840401d0400380108010080305c4a254000100030143d05c415940e0040030034040c0020210b904618100702465406210720001c006500802d10072a007020789035000714414006a400401c5428504d422424080b608d941c01610051000c05050018400d02c1c0d820382c100f5106284100b01d080301b0400810703022403040d00000601400001101e61615110440402600070202d215012074410102c80e0700d100141d000e002003460081d03c0281c40e140c03400508480700113034110140d401c151348a010b21174015411004600850080c402140c48040a062003403c4428a900c014017a80c8840d0522203e59005450401141c081c000f603095640d40c0c011003a00c2911905000036841454501d11001100d08100380f0b000340d505004003006011340ba00207040d502d0a00b1300010b0548503043c00011001d1629400901d18144203107040784144140c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 253041447 1250 253040197 253040201
    0x608090a12091802040914130803040f050d1d01022a120d0509040605040902010e0d03030213030807051203010605030c0a05090a0b12061c061a03030a050301170307030905010c060f 79
    0x8443c074440b01c3c0d000a030800c849403460064464900040d640005541410340903010072070000400142021000301c0080d0a00030f005110000070754010080c1e0307000034101c58006003c0013407480d00c00c1c040011801c56050b65440080d078010070042c030740d496820581c14a03071703911014101070b410558802c02c1030000304511142808041100402c0c0c4d1945526401c0c410104001e179103c0d80c0103907004034500b116840160380d005035602d080c441d081e501ca01305c000e0710703040c101d0280c402c01c40c0b00421102d00310360000802c0124002030281d240210b003a10101950900c008050344002c1c4a00300015200340040b4900b115908000c0c5110013090400034900940d4002194042e11a5845529201e802042c1d0004480c0c80b9070500ba03010301d0490700000c042c26040065203546400160140415964186c458a030300c00b0240c10000d07201004040725141d802d50f0400503e580d02c2401041001c5800d0002102d90381780000c251112142e054642d490790780d0420004440300c50801c54140d40c0c45447c5d01d020f20011040d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 253042697 1250 253041447 253041479
    0x405061f0504180c0804030318080408030903060a02070b04080c07080d0801030210030c050a110c0a081c0903020a0303081f061e17041212110d060608090a1209 70
    0x5600d506440703519080040310640141c80c6000225410720360800c1341c00e81c2c015202c66109a050900060309621005840c841d0801c2040040002000003404100c3c00c10002c094484440203e007166825507400d220202030b1f00490100418101140d0040f40004030b10b030303018295041c1513108135100c059070b0303040c0245084240003040c0082941c0340018419070800300b1441503506000c1c1805d01406080d40c0300142640311300b8a04500308921811600c80c125401d00000c1c0c641c06000b0b1590f90084e07144c8aa940d00c41d00d00100d6003080201440c0c0100f00940244e00c140c1c11030750001c0c0155410b501d50b441c00d84081e01c0017007280d06000b000d0720181100b107541000c03c1001c1d06042d502c45001e900722804154820483e04003407014405103440c2140481c82d11024250b000b84e00403c914040c102140081c0c031041d0307095059074080c034104a42c52014126039000341015a8007018144441a0745003401d403a8508141d81c03190b0300d90040c0c1c0c020f030045440038182e108c0c00301c102e1801005051351440001000150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 253043947 1250 253042697 253042759
    0x3030c0114040c0915050f0f0904060c03050105190308090105090409031814061605150106030f050c160b070e0312040306050622230103050307060501080318040506 72
    0x29407424001407150241c4403401070052414104a4060b8100d41180080030300d02c9070b00d101d0300ca4207158190329122855810f100c1e40e00230b4501401c2e410700c1d24190300500003100145000905d0a000020146004d00c82903c0d86c00940c4400c0007101c0c115101d002c555404080d05030705021b020001908030307450328403d1409443c040c1d640c00d80b040c11285803070208a005076000325181d0741c07000002d01c40f90f95410222546030b16080740c25102104d203841d06c80c0c10036001c4000c4424403543d00c0000036019800d500314262890812400f00101d0b0303074400743c0413000d00581040c3c03000d100b1440840070010791083d803042e40001c0d942c140081444c10310400246040c0c4034089844107004081000c1003000034034040d098104100715030301c00200c482541550145a040c24102d2452601c401c0f030f048906664650304a003c1901244440c030960312401c29603a650b108841c2160240d1400740001118100482a90001018800c058041c1031090080001038000603251940c08080c00d80c1c00940f13020554042926805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 253045197 1250 253043947 253043981
    0xa0b13051308120a1505031b0d12020609070602160e06030c0303030c120a05010602120a140d020901020f0105010308190203220f0617070815120102030109150b09010c0203030c01 78
    0x50414104c005a0701000d490300d0310000c0050f400d0080c0d50700494040c0c80180c60072469248144180000f41008070600303006811150780e12001d20440394081038180c4502c2268088070132007503079184200c0c0e03608a0010106641a031018082c00143c8400f2505d541004005049030461916280000c0c00c580c0103a400f040a02c07400a1000400720310f00c041980e001c0302c90902008030390301d01100030791600d0b014958030410400c0080c56080c1280600600ba49080340e580503580c8406000e10080025481151441e01520892013885100001401054141c07903120015a080a0f600200101c0010005044000b0f5010a01602503030321006080c0c0715109454100b86101c1e240b034480d2000d03403201590049070401c2150006014580c034680210b940203a901d2030502e00c2c5036920115010b042c900c40200d0355005060340c401c05506c03101500518140d44915404204121030800c140f00d8480e031605c1000d6400c41e0900003514a50302607950070140c58000380c2640e242c030000d003856608441040560b054040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 253046447 1250 253045197 253045201
    0xe010f14100503070f030206030c0d0e10141303110c04090605010e060319020904030c0f05060130020f03070e040b040c1d06040b01021207030908060a0b1305130812 72
    0x307541018110000c2409401038080d4909060150680300d81600000c1c1c000c0100101080c03c04400c00100e804450b90041e041044070b41202d13800ba201d0002d02100c118003400c014a001188405021143c05000e00d0009202a0189603606413681c060032416107400f0301824204a0854807140100c0c0310052150400055942c140044107504402c0034104600940c0300406080003080c10b05000081d60350111040b4560703584618040301e54880108008040840c280096810000001110342c141d6290808210b410307443c072136008802d415440e00c940040c500a0b0608000343c203109030540400e4002400b41d490060301c1340140300148500fa10110790a82000d4108410f01c04111140400780c1010400b6038071305495540004407440f0007078076a46c803070380d510801c0360a168000c02203642c8250480d00b042c2e0701d41d0b80c603040241c01d02110b032144440798064a0005000706415110381d494030900180440e04a440c500b92403001804000d00302d074030940c580707228407000c45c1811005d04048924540342c280b1038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 253047697 1250 253046447 253046461
    0x60506180615040f12060e070f0920040b070308161b140604030203070b0105010801030b0105100c021210060b031b0f04030c030b0a0b090907060c0204090c06080601020616050a030e010f14 82
    0x46000200c00042900311f10012701420561111000440301020000301d10000038030542c1051501c07465000c41c815600040c001440880c010140440d00c2c080d844460050b65002d6040b03003107122012480000450081c3e0014050410b103903003815190103075030301232402c20030160442e15010b01540e054015038008a0081c04100c0070170071940c090702d42171804640070f501d141c1e100280c000040c0680352080c000407080005d030a115120041e84a50000c0000c1d48003400849002e44642d641024503095a00700348020641c9440201128020b424104a150501c4440000d03510660814040000d0b040c004010002c045180f03403444401850281904a18038180300d41202e00700c03005155800c0c0140422402c0000c15800428260101c3d400340c14802c056403d907100240061200202c010140a02d031900410417135803140b500c51080c1e10a800b240c1c031546a21490609040401c03142c030b00050070401c25118071500c2500b102000d8041c10002107854800c990211003550854183d00c0c29258098041080c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 253048947 1250 253047697 253047701
    0x70b07120e0619020706060e010f14010206011a0d0c050418231008070305060709090b011d010e0a080d0806012109080f1b2103060d0c030206030108030403060506180615040f1206 78
    0xbc0507103800501c004030b004000070303480d03510501c0f0303112005200403450401e500c004801c40304410b002c2c440030400540e040d500940b40d50400d0042041c1510b014200000c07181c4148214056241d114006091240c0f1241d4141034503440208410420880300900251b078a108225503000346103c7c0000d00924904001e00401903020340d441809030b43d0406000d0029640c05c191000001c0901c24580f03a60342d6440c1e401620525070f28000d0baa00300500740c1d400107030a00003280c0d40350900100e59402007a91a5100112511940ca5007440300d2140210381101c502700d120313400300241d18401d140c1142042d02c003510030742080d002014003c501d2158604e03000c565030030500a0001040c0f6250b00d90070b00d02c110100989180c000202564007494461481d0010300203005241c2c002036a0040000f5600d6840d00c071801c0d1242c11a10045400c0ca0030500030525070314224001c00498903141c0032803945a5500c10401c1000c0e0141041c040305072108000128040c03901c4000c050103411401d4140c051030500d8900082 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 253050197 1250 253048947 253048949
    0xd0218090402061b011d150601020309010813031205071211130e100b0703181d06040b011106091b0d05071712070b07120e0619020706060e010f 63
    0x1216540d5030301080016030300c44040d81c001c402c000f00d0715032034850000100e9005140c0d1600c0d0100781a118000315803071010020720202090315a80d40134101d5150200103982e41d0064103802400308035003d0002d0120016040000ea0807801380c50440c8540014258030012100240c0c0e0740b078006510b00155200004041c003070542c0c0e403001006124600044402204110100d60203000c09070304100b000305130404040b4040c580900182894155030380f6061a01031700d200300c000c15203250068035420006980001190344401c09110203850280303a614142000010100103150505200f06c804100e507000c10100981481500c0500090a42e00d20071001c0100c1c3d00c2c1c03a806414030440f910010040007540202e4440700302e41030410f1404461000380b40550418260f108220f1074441c010031003006000380c2003151806154952140e442d2411003000090565041c80c52141c9150720040118440c00a4201003050080e604007005080c1035035541ca1205640740c3c1d030711100c4800000001131200c1441e0b99801e0b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 253051447 1250 253050197 253050199
    0x30c0c120b0f010303270e0a060303140301030201120e0a0b0906070e0f030c01030c020f0609070e0a290a0305030d1a0123030601140a021e0a0302070b07060e030d0218 73
    0x844150b14541d40146034485006c00c58125180350130a1151440a456001c1c000d40903401041846180007540040100041c1c030058002403d06402c440507210300000722410307a601a0b442415003181403424034090142000400c08510415180354042020b030030869000b15450301c050149402c01c0c65000340220200c01d401441011a0200e000c41c0303980c00908044a903d00323084c00315420404250903418407881401d81280c901a1404100000e10081581c5060390300f600c0c500755542c5c4803094900b04560111942014240808800131914035040d03104141115005002e0550152290390711803c1d40c1004103070302c090b00c0c0c032a0080d000400b41e00c656940104401e1818030040b0741034004149d21a00b04460309d42003440000049125039110341848060a240004101e81d01c00c12000025a10a1400200480d11402c1d0464410300507000c25185155038140c0d00403c80a818500141d285a01451084403801e0386c6140c8003c25103000d10141a82100754640182c0b0717016030300c40181715495029411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 253052697 1250 253051447 253051471
    0x90503010b0102121801020316030f1707122705010905010c08060d08030703020d050f180f03090603090c0406030b04150b010504270e0c03070801020a0e0d030c0c120b 73
    0x20000600756241605d41e0b66503042c0c0803005000d00400140e05510449401c1000050719071880810f16810108102e509602030703581903400c2d620b8040b1402080020348440c4001048480c0c00149150503410600741c51480f002e22042007001045480441306000c0011201c594640b80d041d028001c0030700c1800100400340c10b00c0b91291070a82d00041c0d162401c400000c01d50303507021020455262013641030311010100504200210300b451900c1c0702c21241c04440c1030114800c03502c40c0c00056000030610441000e0b1400085003040942070800a56130002805401c0742c0c411014004055600ca002da880150300541c40c00d400c60905041c44a40310103480c900006050404804182c1d990f802001c440031912082c0c01517411950034100400340aa103510301140440c01c0940034005002c0218410391180c030214100c03030409544071030003400c0c0d004044104011079400c403140a01c07810034200c0c2901a511900d45418040d034182d171030090340e80701900560014130180c07017154200198400e4040d008181d110035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 253053947 1250 253052697 253052713
    0x6030a030504030209040302010207020d06050a18031209030e031507021b030706030c1704030306090b09010510050f0d1b03060b03090601230d0b060103150e0708100e07090503010b0102 81
    0x1e04148600c0c44001e02582c003c1c40040d0030f061007035046e01e1405034014001145441607091510242c0000e841c04103c081c9462803080d4049200540d440000d80d0603100d008180240b908940c0041812100a90030b010b20a1101d0b4803540c1c0070300c00402c400081485801450a000100900c3c218050301d096445c040b03103030083c40c1981d1300003070740c5000c80e070b514070300801c0e0359180d070764221107c5510007201c6441004030f90a02c0105501600141c0554901003420030031603070440b0811400040a114942e0401d034a400c0d8203d0444c480d000034400041e800c164145004140e0805504036180c040d240030f401080c007e1241603c0341d041c0540c00c003c000c0c0c0d090386811400c00c2c505080d140d19041c13240c00d089507860058091441c05100c940603038002d004041a41414450070108203026045801c28000381c50400c0c808040d90f00e00d0f006105a921120010700d5550750303030105540003180540314000e0103510810008441b546268241e00c541e00f03075520080e41515103c1414251110429107a0640d04040c0e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 253055197 1250 253053947 253053953
    0x70312050408100f020d0903020a0201030c030b060304060f11070c0513050c03060d14161701110a030504031b1505010b0313020f0a03050a0305040305061515090307050a08010c0806030a 81
    0x43c000e00e40340010800001c0381d2482c40900ca0017442410050311690f810801c10605054001c2105d029180c000e880c03d016000c80c0e03540072001c44001c40b82c4a9840749007840810003103840e55101d00c10101801600051030790648002c6445070708120b03001c44e00784044032414003e6090180a240066401241c14095820a450400036030301006051502031189014150180849410210f42903074910702500c8101444175050f0940d55080d00804a81240444440c5da01c030205109640ca0f0b01c0a031302d0810305104048004801a0101820540800041c2a45442d00700400c04080142c0b40c8904c440d10300c096086688103041c0d4005a02401c64800284208500603003820590f0301d040307904179444801248080002060200e15800240043c460500003104240d08800200240c0780a0300444500d0f0b510380001d607407070100e0103038940e401c420b03545880b1004845040190142100050907118400c0d16800803600d604016803040c00d5070b030b44810b6140300346500080c00c40c1c2c03c200c0c1600641a5070350151 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 253056447 1250 253055197 253055203
    0x70314060705040522020310080606180c0f0f16230c0d0c0f09050907090e100e0109051b010906080f07200102030702031c020909150f030609070312050408 68
    0x12040e076000b080d445041c031700703084203402d0041c0c5502d5044034215142c0c1010002c0001101003801501054800c4038081000ba14101c99003c2101d20705209810542d0f0350388000c09465089404a0f050805044c00004400410305d00a0070807103694401c00d00c501c0c140d07420456180c42071200c02d9141011510321070a9078281c0400c20001050f025200d6801005103482c00c50344141c0e040d84440c1d0101d6182a0100300c0d154190000d6018104100807144400d4461900908580848881c1071640e4407603500300c003c0c5c0045411800054100c0000000c00414940315541840c00c031170003480c80da02c2a8030282000e0360b003082005010341203d242800651410020303d000110010308010b0501c008888400030907982041d0184400500e10001e548031b08000c0ca000e0350fa41c200b05980c085520541d804602d48144901c2607a00f2040014801416500c0b5000ca0b503103061101e0992030703000400c2c2c01d00000542c500700702d4a800354a84000400001345903040c03500070b40844880300c4080010400040080311400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 253057553 1106 253056447 253056449
    0xc0f060103021f0906180b030406050402131107080304020301060f06020705010f050c0c151e0c0f010912051303022107060201110a03090c030b010807031406070504 72
    0x14003000c00c0c400c2c1444000500050000ca0100171841c805c8072002c01d100505421505c4a586410745518164000c13601541c0c440d031502c051204504021900d00100d06241c2020005c0924107400b100051041180140c401c010200106041d0365081d0f001900418040240c0562150b4442000e900d43c01144145c81c08100101c4062441c1401807003140c8510082c940034081d0104420200980301c40040811940c604050011032416091440c0401803012a10701503511204090601450440d210803148030a0b410010103c000901030022458400c07510700745181c41742e500e00203452001441e640003943c0140c214401c84c240103d0084601c0324120000141d0b0304490715001c00340e080e106041c800001980d410000c007031b07080f0700c40c0d845501c00b207203e60125010955a5280c6885410003030b0003406c1d050700840c0003002000004404054403100c540b01900280c81d007104080d20b40c3c016 = true := by decide +kernel

theorem cover : BRFrame.Cov 252877697 253057553 := by
  have h0 := BRFrame.cov_init 252877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 252877697 ≤ n) (h2 : n < 253057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
