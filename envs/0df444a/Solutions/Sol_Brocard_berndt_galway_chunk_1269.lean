-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1269
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:05:25.65916+00:00
-- url     : https://prove2.me/submissions/b408fbf2-ea50-400e-bb92-f198d440d0f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 228057553 ≤ n < 228237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 228058803 1250 228057553 228057563
    0xc050609130906050a06170d080a091406010509010602010e1c0e090a0b030d03020f0304021e031510080a03020316080708210c180409080705121c02040b03061c 70
    0x1082c0605125001c0d100603500303407461a241c100042071902043d80c0608500314403d0080003e03050800080f2401d00005064030700340380c1e0340c4040c000010020301d003d034004180003008002039410b04041148460301a0300000540e890271030f50303101c001404600e20080014455201e40e0080b004402610190440a100c0d540148060108080780c005680314169000050f0220351001c200d18105038224403e03081404a0084140002001417070034060301b10040100980c0c80041102040c00300b8030b09407603c0096954260b00d0410040d48250800c28240100121002080c2d0003940381c4020f5168412080940b6032100206aa00103003c0150110f50703c0341c2c0d0144171180d070703100c01c8507242030040000c2046890024810011840885800c0180e43c01c140d041070603505414181c5040100070140105d00300c0d0911400e02c00240415414030030101210300001c1020ba9408556081c00244624040305e0300802e0302c14230040c040c0d4082601940c0d84404251450950310210301c4214034150303002900108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 228060053 1250 228058803 228058811
    0x10e150a0f0311041409060409060606020a02090f07081b04120606080c09071b050c0301050a0b01180605030414031608180402120408090612040605070e0108040c05060913 75
    0x31801d501c00103a2510201c0e6541c2001602044078240400f4400d030310441100d040461781110355403070519181508010001c00000300b55004d42d81740c00503141d007079020710003581091b240d90080d403c150160984c018502e608040300c0d8a4241000340c1540310142000c8940500700410311485581d41d01250090b000000c103d680501961902d0000b424481c01a095140194003089007907060051485024926035200c04800c0b090409010a110312000c0060b034061141d89114146038a080c401c041c000c00162401050384a80e010000d8100c2c03010304001c500d400b40a0310100059603000d015030f40c0190b48000000030750000344104501d94001c07031060240700c10212088900304540e0800a260102d1541c080343c182035400f0f82000103c4c0544111300418074004030019002412080c01010603400c01000c072070501c200b40410260750482210200d032120750321828460b03000e4000c500c104481c0da0910b03085846140c00d658219204406204060145801007003220490340c81e08410f40b08030344860801c01c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 228061303 1250 228060053 228060067
    0xf0606040f0e04120807080406020a030b09010b0c06010602060903031303030b060d1401090b060f03060a0f03050705011e050a03090201020f030703020105101a07110a0b0307050a0e1e010e15 83
    0x1034402c14094400700c82c3e04104011045410f0300502415108a4150300c0b4040d4654854403640c001e540304480400c00c2640d15120300506030b991000715406400e14112558980030703501c010601d0b059060304890155803100c0f00300004118000101c075400b07100701503032140005492805601030527a28803015800700d00454440b5200886601103402c0721900c03c55400c4a0360f9410132081210b800108603a00310798200185205400c1140c0111b40204001c0d0020100703e544075001d407036500840e003040b502d64204070302c104455a1f0081a11000e01c680914140c0d6840c001c02018089104400242c0306158803400000309680c024000c51002400c0c20042d80d58984492400900809044490b103401c50701440000c10040d49a004401c64001100d080900d0190140c4400c0c90500c07803410f12603072010030880c01140448010016601654007034690545621840b10058490340d8014130444c040c6002e49490078070500307a40c21403041140203090508000031240e0210f4950307090440004030301c06e0300103000e03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 228062553 1250 228061303 228061319
    0x1f06030b090a0b010501030b0f01031109220501050910030b070c08032e0305070b0c0a0c03030e0915060915090904230703050312070c0f0c050a0b03010e0f0606040f 72
    0x41d02c9018410100d0122681c0ca844c01581113408410009400c646001a4003c1550003540032b24652002000240d06181d440c0002401d0200d5140c581c64034921600d01401c2c0805143c05124017400003103070030f40300c0d0b498015158220703030806220141031b0007095804a0252401004044001071b04202480da0382d00e041040322040302100d10a0760211031901b69400459150441c12009690780702c2d003d401d8007864612011940e400008401c0d882d0300800b0342540005803a00c000360b00951003910344010f864000d00801403034280041010400d070000d0008240c89039201822280005000c4075582c1c94104a503a1052050042a101c00e030030101c0c50007400240440c107102500d100c043c010b0804002554105a9500c403200d81c800102035134014000d0100032403c4902c8550700240b0703481c18106210b103949840050401e05002512a187d200001b07000134181603d0b448050002500054070315450840c0b440400036000b00f128524012200100d4426680d1104460040070008a0184d02549030005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 228063803 1250 228062553 228062563
    0xc172205030d03060b0f031b07051509061306050702120706020409200a030902060708072003010603050601030615150201061805070215040c1d010503010c030e1f06030b09 75
    0x186600c40c0c4292042030b40c029100c3d006500c15102c2d000042414a80071101100d19900b0141115121000101c0c005d0500302c10301c0080c240c014041c5000b840800e2000c808825801c0c0040c2010ba401c0c0c02010811481034404441d0140d1650320510025039070ba14840c0803400c19100303c541a03882c650014120083c0009a0050010349145000030059004d14190350840e20f151810701100d5020140062407406d4002d40c02907111500103041c442c546402c9a0b280c0001c3e0b8003000e42100d001c030014100101a0b07804c0103500800361010b070000c1080728110784580c5e5075540144002080d958483c0154111580e088107100300904200341d04d026544101c00010703010301082c2c026621f0071002e00e0407480340e5050301d01401e4042d10341e42d00640100c0e02075034403400710030700001d000f030300d0600412000044189004240c01c148001120a1003229410102003500307482611500e0010981003404c1c680f1056004203c0d14480b03003031010901c00e444800300b8014054401c0c0e500180c078490219040250321100070132 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 228065053 1250 228063803 228063809
    0x50130060311040b03031204080a0201020d05130b0f091e0109050102040e01090c0306140d03020a080318071a0f03040309080703080405040e0d020d030c021914060106030c0c1722 78
    0x3002c1c4080450740017410350700d00601c540c4699030044080460b003c80c0b080c2006004c0c90b12070344005413800d81c6040001c81628001d03113045488030002210390050100b12003101b070b04140c08c44003d07840d40c1041a209c5a5811f4040e19581090302c0d03c1c84641641182503110a0a031503201000355101c40c2d41724034a1400d05024451407862505064041001c18824401d01007628880f5001a0311003110006128865078411400c400f503210382c40c0d020002c40d00040203944103281e6810311118100b41c5000309818000c0c294080c040d00c40078007000e040d100c11001e00b910801c6002d8001c1c00d4580d035490808480c40c1c0559030000d10140900f06000c070620001c100144180d50058506101b0034134600b0f003495580081c41c095a0060300b180550301d400c648650040d210017501c510484480790701e526000c0c800032034450070486400300164488006003100380505801464139090801c40002000006010300781c40300c3d0020900724017281c2c440709038407070141600c00d00c0e4400c0d0403600441c103038081e0501c10361240340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 228066303 1250 228065053 228065059
    0x521010801050f010f0609090b010c0f0606150314071b0c091b1107030204200f04051906021510081c0e0a031a0c040b0a08150109050130060311 63
    0x34004502c428100d00b91904851b869035850f0f1903585407000580051010000050400100b03000100c0440d11305c01500c0c1045000c0d0400084591500400304030600d1a51001e009241c1446131040c055400d0865150b8429028180100c803001c5c50641c1c801449103e4500030103000300b0f0071000c00e907024694019650700142c85c509581250009805444008200140c00710b26440b20405000509082c0c0261010050703c0ca000b6800c00034980d00654503170004c007141c4c050707041d010504100310701d040300c0e1078594604161000c9009500b00034009459a641e142103003022801070b404110460f101384c80540050019005945007003442c600c00d20621380100c12030030006220501102c0b076901d425030041c01102da2003803480c40d0540d070b071a007104e81e05a0000c00580c1203e0041c04001810414240240354003001d40d990039000d482c0009010542c0e401500c0481c1c100300e1408014005640c0007000182075040441950013983d42207000c14070b880341c030382200406007070030014000b040261034100750301c141d0030071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 228067553 1250 228066303 228066331
    0xa03020105220b1f05060f030a050703020415050a05161b0b1c09080910020d0305010e04080301030602030a060302030f03070507230120010501120212010e060601052101080105 77
    0x160b44401c00c40501c42902500e030148401c0801c4005841c04107000f4a03516802c0000074440e07542c00010a0342d0040c0960000100c0004108800064940b04e440e0b4468024241141000e050210050a102c0c014404000344080010314a00c42805401503c00c08282807100031740000c0f1a280c07040d118101d401501181180340308020441d0b440c440d0a4500005094400001d016a01801d4070083c1c4511102a620500c00304880c002640350400c04231200e128680003420040d8589034008e080b01c034140c1c00400d41e95100c200b07000008229500300e904498100344090307100c3d11150708500c01030149910003945480307501d0040c03c1d11074010000c2c10040c0c1c0500c05848030389a43c1c4280b001480c1030340b8405020302081080200d05980541484e000201c490707448603002d4a0103104080c21600300303820150800b50011805011450301c114610b1040c00c2143c02448105070075811140d5808014140d01e040c81000b09554095500c1049902181d83c00d5413070401065a41d0241240244003d80310201d500c40c40c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 228068803 1250 228067553 228067591
    0x1003060f050411042c0d020d0302070b0601030504060e0f0d032a051605010c020106030c090e0604021212030a0f0b0117160504080607170907050a030b090a050a03020105 74
    0x980c0705803449550001c28200414080c03a0401008001c9441c142400108000510b450305505408403094014030000800c40304080d03084c0603103042940c1d010b03102054010001d400020f201a04002e4200c1402e0a000c28180c50380d20b4140d004d800c140b41c003280e03107200c3c691012030034803400262400441c0e01358908101d6111941822814103094040c0402155140c1096181c070341e200300024050842d02c0c104810007070b00165145803c0d181802d00960060b9154a414018800d40c1c011780401010780903801c010b401c420b0380b407180d1174800c01400a0b00c107501d03829007030308072020500941e486120f80220482da2854036070402c4004043c035111072200246010301c0e60640b0750148441000c656041c110107445a605d0755030100040c08041140380420400703100001d0007440410103980105003544a10a00040c6400007410380c90004003c144c0550100300c0801c0240ca489060a054075002000696641c0c2d4030001c2a241c1011400014840c0c481c103203484045c5075066020600450202540c0c10120b00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 228070053 1250 228068803 228068831
    0x30902010f090506030426130e070f0806010e2101091407050102030417011503050619200d020906040f0e07090501200a08160c09020a020c09070c020603100306 70
    0xa5409003d070021350410100700450071441c0c1e001c034546440720116080f0340114850312065000691200080c5075105024032508421204055000095140140318180e014a00624450028210a040c0158480c5a032181d07282c2411543e81001950f08040d4441e05a4030f00a0007403001c4e100c2aa1f81401d0b6205000043c500481e540003180d205034000e50619040425605c108045800150701565a421091601e01c0710b803010200118042c0740076101c5840c0a1b40c0c0318030f410b440d62640d041c00743c0c0b90100840540094818014000102000d102e48030380180340704074020321413502000ea000c280403a0014400390a048087e0958017400030203907550300c50301400d5800e5506800703554042802c4d42c4a4510100d00c2c004848101c1c0304880403038802d0949912100c1050b4082060071642c0480680694180012210000001d141c44d0504510303080c003400300207454407222003510388104d030402c000c1120f14ac030503a501d441c40e940040c601a81c905210b288621801d48a100490b80141880322290900b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 228071303 1250 228070053 228070067
    0x9050f030d05040e07050c070f21120c030201021210080f010b0a09051905070f02010c020606090a0518030309010f0f09331107030216030c0608060a0510030902010f 72
    0x10703070721800c0c1001e090100124110100400003005c1200c2880000d00c80c1400300041e0005049070100f50b1031460070403442548502c0c0c0b0f0b04680c0300b11160740b250b020000e1000c0040c5000b030380c201c1c0b4100d608041d540c58124064400c50842181c4036402d04140704401100c0c400c00e004603500c00045030803201100000500b65154606215400050078104001c0d604268000a40c0310821449035105c01c4041980d140444000380d41010005001c00a1800e8140d024442c4215111060008010f64601000099188600104012546070b110804502503040911103c81524452401c2e6600c81c9803d001c1d01e4000c080080080350610b00700341c080c50740c41009209985d5542d8010305107445a80001843d242e8074081080c1c4181c2c20000c1d8543d50419100354440c48642c9111f105600380c3d13890041c10000e15260302406d0103005e040c1d100008000080da000e0782e080c1100c041d270404181079a5030ba00000c6145046501480e0810074294950440941c0b5601640200341b00743ca8041c12007002d01800c48c3c400f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 228072553 1250 228071303 228071323
    0x20d060515010c1e06060510020106030c1d0a0f0207050d02101a010c14100f02091504081f140903210705120603010f090503030709060201180308060a0302040c09050f03 74
    0x300181100c88904004150051341c0001d00405000ca07286e5130710804110841540840080141d5684905008000354108500e00800c3c144454030400e001480c2d0204000101403d00480305556107526000703045d954042c0c5070b03969008010740b15003420050019458136860030411000d0342c50b01080344030740380001d14010b44210701a0342c0e907800e810859407121660304082007110007070703c01d02d000700d40e80303030070501403499211541032026071034036002001e00c18400050b00005951040500003840450400a1200d14403540d11002c5441c0c015a810110000d0502d0680c00c1603201e0280100402514000014010840c181d0207074031680960300659043c403c07058070b1a00019004003d44c40141d650304991541140000380006040031050020500b01d40040b0001c645030707040442000100c0c0c1d0422000d4000380350600081c404503480c0104254058807030345c002010b02400704042486a11245c1c0620095540504100700c004640c04029140d0304680c82805d00c00c12000c0700103a0541008034580d000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 228073803 1250 228072553 228072563
    0xa08070c0b010311030a051204050f03190201140702180403081e0c1315020c1903020d08030405010207200307051c120c0507060e041431020d060515010c 67
    0x250f4255901c01050303040e014031031175062040004080214800b0311600310010342c90704440f90765a1034107041c00641180d251702c0d01d11075005040008009000303ca6080704039542403a12a9442d036020003091654052500041e400400c42d03240c03916080ca0702e07041d00b03000343d01944540c2d110f9500c00c0e400c100c00f481442900944070b04074901003584007140001610b51242200307140010b06d600c481b641c00c2910607100480300140d00940251410703003452605400d42403540543c80d564141541c022a003aa000002c00810b110360000005060003000e5058440469000410f11001c90200d5160000300c8084005507110b4028008001b50351b1500a01d000f1400c5e950b101c0c02d010001d4981c84444040143c0613820080c0b004020f22035001840510440001e44201d4444034029100c003418401202c00000d03080c0c0182c5c2554050013203101c20100c40011000c8080901440132400b884001c6d2400e285d118025007202000b10b4110821000d50003240c032400d07000a01168203184c2d000110b8241071f82c3c05010704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 228075053 1250 228073803 228073823
    0x405060403030525030c0201020c01050c040608090f19030c2301050702012d06051512060607051e070f0e0f0609070c0b07020c0a08010c090801060b0d0f1d030a08070c 73
    0x250b6010341c02c040d106c180c00b4000141480761000115080d18021a010761880d48002400c1c0f1007541c000c142d423a0405007550003406003144180b295541c5030501b008004600492542c00ca0405100d0029413482680c401c3c1d01000b0950014041d807407071080079010826650804c0c4c0010107051051081c04d030944419101c50610f004002d603403098941000c13070a0858292a83e601180c00d4803803205a0030002d1840329081d0b62888904952020035401404c400d10944040228001280c00051001c100d5040e50130b403180145074026001d850840079a00c800d440507643d050000e00040314565092003060001c4509826685500400c9808003003110146c0200d41c25200090102c0c4c412a1940d078404481d00407100401004e00006401c5c20050340030b650a41e4461201c101a1070b400400500201500002405941d0401881008500486840c0c8000c00e1f510040340c10100b41d1900a443c40c00a004208140101101462078403948508000707070201c2c0b80080854601ca200e4001c25039200d80201c0a41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 228076303 1250 228075053 228075121
    0x112809030308060a0518040507060305010501140d06081b0118060915020a050105040c080c09010302280302150a08011202031b040902090f1506270310020304050604030305 75
    0x1a48116010f0000741d040220b91001040d19100c6200c00300c9000f482480145c3d561601d482d025147c001741780c012100301130404004120698001d00c0d0205540c510a81440d1102d4000a0741002821142d0000e40944281c0000159a401c000e82c1c5c850b60010070fa0300c013003000c021880301c04148403082c4694030005103000d02c02c110a0120400e4001c13a82c0c581d10541e0f0200c01d042d12110f007501c1055500b03640319408408200242c0c0c000f0084045202c006450941c0c0b203626540000c0c048130460702c4ca8420086444402e5140c4000c10f001007000b450b40101a080c83d124243e280031403940026400d00c0c003148400f000030410300d120510310f075480c82c0e00500809100c56840004941049207041c841d4100d91186085001a550003500ea0300c42e007504107604c4881e160111000c1101182c009000340287c404020700c8660301c200140c0d412505140d800344541101d000f00119182c0324001c00317911011031010062208001012400d01d014a01940d024003003038a8000602281040a254460040c4048000e036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 228077553 1250 228076303 228076307
    0x90a03030c0804030f080405040e0616030c09080609060103050c01110d1404090f09060b011d10021c0509090a18060c030605060d1b0504050901140a03061128090303 72
    0x455030707191044001c01d04050392560f40420850baa0581250044000f003820303c81418039104040c003809801e80101201d05001c81c8811171121070602080805456091411486001d110103d0041c0303403a07800c45419161200d4240d49032482800115102d0003000e00304002ca40c81030652147c00750300f04000e8106001d0300c90b030555030141c10300060340c51448c051100251b0718100b481656039140d80818082030f41919450084c0c02c680c0e0380c800c0d040c18804048802c1c1d0018802120030180188140c0d8103640b005802c03030050349400b401c8041d0906100e0030340040d60146911001600c1407510940325418140c4410003d03005548520501ca0b01c826600d0400344007040c1d45030008c2d45205002d05001604d1070f04da10216005910442501d0354041c0c480d006c80890304440c401a400000c91341c41e00505103400c0400082c04040c1c10312034042e890780c5a840f040b4041d5140040c900045600107030070407000c2101c41d500203071500402c484207607a8802c102059034600d1a4404a5403aa0155541007000c81c1541e4003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 228078803 1250 228077553 228077567
    0x50603120d0c0912030c0203010c020102030c04030609050708060c0d050603030a080a05251106060d0803010605030a15030f14120405130b09013302070303080702150408030a060b090a0303 82
    0x110b01c1040b02c800000590f00c11519181e0748036500a603200001104103006160035515406441001c5a20401c100042c4a0030082520280c0e603024401180c00b0b007403810503a290a02c607400030000c0c0c3c000c0b103042c00080104000140000c581c8054280204d9540b02e0070142c1324080c115280c0003103070183c0c001800100b580d0b4020780d40080002084400d107504442e6110006009403040c0e000704203803a84a01c0e010608010b840d038005801c80d14004842100e507240e4280f4041886241c2c148000400440c0741c0ba1604c4d04001c0385890341d245c039024026a82e052121400c003841c0420340e402900c0c42d150800150740814041e8034000c04080a515151901003400004200707945103002c41591121207191681d1510183c0d030090070228000810810214042071611a1031150601c42c4055461100041ca80104111040300c0d01810026080e0f9106001130303041415460b0a40c0141120400304401c000744400954003a02034402d0810010b611007624000710b204000545a0041304800b04100203841402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 228080053 1250 228078803 228078821
    0xc0303090201021903080a0f06050a150c1a0402011205040218070c021201050a0c11070e0a020c031621080c090303041707140a050d030c1b0612050603120d 68
    0x1044401c514007490780b196401034004c10480c0042c1600c801c0c0003d500b018010001640c00b07107141004280d14000018030f0300340d40c41c490110600281c0c0385194055001c1d81e00c855619811400c040ea001e00d049600001a40048500303c0c0030a20542d8202641c0301070f8030925210b958007400010300b04041d0f0200c451480b90003402c200800c0f4003c0d03803503401601c0e40303030f171800081a0080001c1041d0800303000220654403e40401e004101980c86500740d00c0300e0005078a000c8070070030014000603407503111400e0040d11410518089600c0009180303d08c0203102d58401013800e001c1c4521000c640a140f4101c0000d820000340d180c009401440401c0003040b2900041001c040d004085a14041c0c1e9015106450038404500a01c960052902000320a4085804650b030050803641503210720701b0100014100c0c840454050704000ca259a107604111407080140c90b106600005075442e240d42d20401801548000851481c940c14030f0041a96400c1c0010f8a00b9847d0703502c030402d401d008071043d1040003815480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 228081303 1250 228080053 228080057
    0x50d14070b2a0c0307050105090c06031b0409020403110103050f0c0711030a0b01080a12080103121115015324010602160602030a050903070308030c07021801060c0303090201 76
    0x80342d00119a10400002d10048090b00c001e56211440c50030700d07500311840104465003a401845800000d95078030b10480794401c0170381d918140e00e803858180309581c40c055a000103407880d10004011041c00f26100f480c02004e4001d9a041c07001da42c0d82000240188030550700496158014803802c070000b8045883c051030400302908442c0000b180741c403508190322080e40520440d80142c84540144403080400c464440c0c00ca06054009d07524542da00d1a8084161030305004010002181d4110141c09100303e13030142c1c0c1610325a600550319000c2841901030810300e40850410817446603101c120719403840d4003100910380301e078103440c000d500400031a404400c981e008023030090896070301c1441e0940b82c60340d030340c4138401d00518402d6050541c0a450211800c008124264001030104602da500204035030400416281998443c0d2007100801e01c0e000c02c3d90401400d8204c0070003009900b90b014000341803803d000b11018586c4004240306403030100400c0c021040004c005a010202090080d04180404c62044c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 228082553 1250 228081303 228081361
    0x10207060f0216090606020f0c091501050904090303051609050901031205071407140108062b051e0d0f0207030f02131e0b010207080c090c04080307050d14070b 70
    0x40164102c6043c1641019400343e6075450140501a810090041401641c1e4001c0500d0386040000410308180109003074074460518a00800e40e034450b00c242c4d080c2d100064424000703000345140c00340242004442da400b10b40c0d10704803604005403140d441072080b1640034001440590841d1105213030240316049000510204221072000146210b0110b5030240a10000c0c5c62802e080124502c0884d0480420504103e0084144450799071101c00c0d503041f80844907425024810903081d12803d80f50500c10280c024020403000e0361007000e104401d54414082441a20441b8641c00c0081d1003446600d810280142d0042c1024800a80a40b524001d4640003c2c0301c1c41c40381c50b803600d403030003942d220011407095002c505051510300c140501900c107020009002801ea80c905216a003569408070b440300c82e02c28070604001c5940701420000b01e07409081130205a036901e1800d0300702160f0303030448100540c0008940c00b860300300882d443c10680300d5203030f40b000c0904529103403003140c4d0301c6181100030402014080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 228083803 1250 228082553 228082573
    0xa0b120703090515010510080603030909060310090b100b040305070e070c0803040f020f0a05151305092d0c160303060509010f1a0a170a061d160201060302010207060f02 74
    0x4200000301134030020f0b40d00c6201030340c105000e100d204103940e0b120109105151052000303680d008015510786c01000d0741c0d1942c49179108400245004000d041154a80e4980700300366040c001c0442e00e0034810f1441084903401d4a50b00c003039882d07070742c4218800500160449041800300e282307030441c2c16401c12414908174030000c5003921a008541e005640466802607400f80f46030440c1041050013280e0403080325000d00711032034400458040c02071801c5071207800b080082c4455100100724420b030003811020301100150b161071940240091103490281001d0000c5402e01c194140042d20858400c0c00da45000e1810008030314580f528070003469400b01c00b030540304c42001c14146c0f9a601e4150091110040720300c4440d2a14800c0c0305601c002c0503901840600403c641e9030f2042c1c000c040c1420030030801c0cc0d0714185a070354500303e030001c0c081604000050031518103400ba45800201005008541391540c00200e030120001c160b080700c0c0d00b8031001b0701680019000300803640c041c2c0c1c40900b242020b40103962202d01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 228085053 1250 228083803 228083813
    0xa05030a0f12060e0a05060d0b06060906070b0907030506130f0201050901030905010c031a01020610030308190507030f0c020604020a06050d02040e040606292508030f090c0a0b12070309 81
    0x2540c00c0780d145285504c0401010b0851406455000481991902d0800b400360700e03800080800102140c0c02028002907050302506c80748126101c603030300130540712090b00b00285020b442d00c0261006071340390710903640454a06410002e01061051707000c02c00c040c0d01c0c0c40a50042d9050303044225403a0601d0795070b0340032402140081c043d071405a00c180d80c00041d40d02c84a80c031031003401916500c2c0b50456110204009a6006e1900130a0580e80c150400c07400b540e842ca00d000110164481140c20a24104005d00007043e416400002894014000c1030010703205518003241e0300e860403078002c2d502014404040140d140150000e108142403100e000d498162107103a400d44a00068138101e40c860b0391030004110a90035032040c1600b00680f6812010b11144150a0f21054050800000510100b603403190800da0390409002c0360055200004030744a16106100a036290f908481c007200d14003070035800840c00d10f41552090143c518001000342000700c800802111080002c0030b94042c10765030b12000d00890 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 228086303 1250 228085053 228085061
    0x605011e0e010c02031507090b040605031f03020303040b0a0e0f010c020108040203010e011505030f19060f2007020a0603020415051305030a050a060b03010218130f020d020a0306080a05030a0f12 85
    0x79040c6d40b000c411608000074010302080306d5500ca203041c0340061200b0b010559001c0102da40182800d4280084842d140805020004040d800250306101c005000281900c00401400100c610354a481c9030721102d40052200030442524490700186140b507a034001907000d01441030700140080e000007034901d40c4d0910903084403c03a1680c07082c0703000c0d9900300304941d240030002505004102c101515440400c00400081940704050041440e5111903200402c00301a038401d00000a024100c0129070215040250b51580111020b0b80245040540030958602034022201116080b26a96103070010003413084031b1603044021902d4042103c910300040c5590104041c0700003030b00030350203088842511300c0d190040741c0b880e466031402139006004519600f40360b40183c800c0e400c425641c00c00346050500c1414001e081c0080040c04951020862008410b150340c0503041d607450366141041116240d0715000d54441d80305e00020081c0c0c0c0104107582c62148254a00703610310800d801e05000050003000020142c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 228087553 1250 228086303 228086323
    0x3021908030f25030c15090501050106050d0b04060803030a1805030a02010b01110c0f010c1505090c040e0a020a0909170a0203280f0302030910020712030605011e0e010c0203 76
    0x1942020075148400c036079250290f403000c0f40c0d040c000c910240f0300d41e070040c1c424052010b010b008840302008000710001150044200395912400270071156846150103403240d00440c0e07607032032082d1410300411790b9030801c1d10801c400d813540500110b0a66950142e058042d21812200140200c1c0c0402d100700000c40400103045440103540021030062890000103280131049002c82446e544a146412110703181c4021070480d07a1070a1038203004a510301d0801050381d0001c90700c009006403501d03041015600300410450751205c0c00b00c42c00e0041d00c01000b0310341d46d80d01e220b6002a5210124040411140b03026500c5250960b20550101d46a0050714880c102c40c0d4200d083c01501580000440703032001c000c4010078081120103000b00ba019241e410900404100001912105040d40080402c000c401d007048441d1030f039040c445096548a00d07514000401140188181c80480d00f80000440d06602501c80d80c25403803428070744110240c00f000000c41e003480600b080035041c01100603c1c00b025880c01c0c004031400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 228088803 1250 228087553 228087577
    0x207080109060b0f150409020a0e0910150518040c1b03030e01060b04060c0209060a120501020403060e120d020a1b060b010f0e01020d141902060106030b030106050a0302190803 77
    0x90502003000d001c130003c0b204009503c204603034540c8031492251201584c042d900d41d20001604e602012506850191031420150b502c64103600c20000307003280d504001c005441c1d6010000405601000741560280185690088041090b420301c4c0311901309a44900f00e400c04928094040104003240000b02041d0160b050b000240c0b1803c0e00d20017042d09005000c01010100c030420310381850088010580e8600490017440b510981c00843c1740d0350b484400504c081d1021003c025005125858010b000358014481140e005080524052041c1c001107141c0b11060b5000010a1802c00209001002580214602030900c1810a40303940030480c021441c406e520b220b641c000640b42401070000d8043c1069a03412410032042140106403a64040b0301031050110a04000c142d220440f104440e490042070303034143d010f41110440300e030010740c0060440e04a40640d281005442c807030318180342c280c0c1d03514001c1d95004003c0344001c00050404003682c0419100e41d0303000781c1e519a182d05a0701e040d0f07413012514070b038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 228090053 1250 228088803 228088811
    0x151b0b0708041b030305070303090501141e01140f0111011b0309140c0109050409110d03030605120a02060307080a15060201060609050a081207031b050a1103010203070816020708010906 81
    0x8100089005025608902d014807010f40c1407843d0b4004000d8030404000608054a40b02210704005003504400a60101f03081803003080e01d04602c0008104040d003080b070001814840001a00c0304c1c8000e4400100d00c0d025050940d9111181c00540f2110b038083d02c0040b1540d41c8140b50500305480c171071130740341d100595580410b1040346418010340031358192444000300d402103031110106a80280000d0111281900c012031010340a061801282640c24062500144442140420182d050f40a2403d480381250b81c41c242148111155944d204200002900008100040b44446009213074403540014030b000301140c0310506500130103505009500c1000541c0d180c0c0c5044c000b06811000d004050301d000d860000b070940c40c24020799a03070b0b090b69030041d1000e0b030005210b0041c14803c0c0d84a040b10894606201d06840c03e519013a076070f88070211030079550541d0504085401d8078046c02102d00a182540e22072000b038490b410819000d04c1d02d65921400e5100e5083d000424075401e000707085019010380e030001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 228091303 1250 228090053 228090061
    0x13090b01090f02191808031b07080f0d05071113060e1803040b090409140303010608071b030e1210140105060702060d0c0e151b0106151b0b0708 63
    0x6819100005242c0e00b801d0700601c8507140382ca43e0034070b003d0850710051a010307a010b0545000d816542e800d0b50405021030200203090508048440c403542c0070700c10990708841e5440d80d90100d0030f07202c030b4607180e03419040d400500308044494440d1000c1d007911402020b40d489880780210014407140b0b00848100d5640b030300c451003005034007003000d81603520900101c51a408103281e49866901d0784124021800c01c9840031455800c55162603101926056100780301d0381c2c1ca4503040c19050f070340b03410074071a003400140124002040c541c8034500101030b050084101c03411640042d9419900e1241c4255015000100c040500c030000c0010080300040040244002680f000c40c07005980d0701000c1600203900a0380d0400820700141c49800403a050183c540000140440e8a8602114840100b440c081d03031101d542c440010030003221a005000500d6180241c2c0c50020002d10307400e003a5442c903c80d801040b540700c0100d5010300d005200000301010301d0f440c04003070107217140c2e29115114002c0e1002000a0460b0f8104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 228092553 1250 228091303 228091319
    0x507030b090702070515040909030512090d171e100302010905090108070312030b1005030108060a050606040603020904110c06060a08030c100b061c02090411030f0403080613090b01 79
    0x40515140559904041d80340850019545500a2084600414200d0191440f6000039000e88015001c014002c0c03060340c0303c5040092080c0c000310f20311003055140002040c0300c1074000030781c840b4051003078482003540503e244080e80102002818007000f440d401e030b0f00800e030070031005170148104007914403202d0050a600005084040035004107002c0c0b50304000500c48400c1c00507884049907880702c80c4895031113124404901901d1240b040f1504004100c00c11044c4a41040c05513040e190071304c00b190003656402400c9402d440050380c2c00d940050040006004140c82500246880e11018002040c10010081c030541c0503800415642c3d5603070006018000b079032820071408001010080c0046043c030442140e13044c0c4611110241a004a0f035902007004076450f03807010b403441202c800100c2c07100404280d11400180d031050102c24800c5282c81c404a0344165031a0a41c2d008801d170300c0c448656696107580a0f9102c61020b4213980e88800e0707400014601d45024000c010a45204018413041c80d40f600c414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 228093803 1250 228092553 228092561
    0x705072309190507110304080307140307030e0613170307021011030d0b010c08030711060106030c1b080f030a0207020906010309050604150f11180105030910021305060409050703 78
    0x1500d44604101800d110141c81030200114503000720301c00000d440d884440040d103035148844a0302110b0b000104000034004004800380070b00c13500408025040758220300c9210749920032000010302244000d00d5459070b90074060054281140801030ba48004d9495035400544601032000d890401d900000c0c01c0801c5040c84911000102400d0500b18000c2e9000d243d125124000c000030115000c0c1e8880003110a0380c070540e41e6200d130b96000042e8130350300d08145100903e208034440c540002da120f0f080001400a20074410900d41c9401503440043c2d940707408100c101600c107401c406072141d1006000300071000e0781400017075019040c59080181c0d5903846105100004900900d5103040c140752850100100b58003041031903000764000c3e1504180c0301191240001400c4500d19462214500090a284d09984000410582e0082c80f001c1001c41410b500440e110b11013160b00b006960041c0f0000c3c00e11001036000b50605203409100103038002e8a0701c000c03903c10b400a90100ca0201d41384c4041c0003c45406120b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 228095053 1250 228093803 228093869
    0x61404090201051c022701030e03160b1008030408030418090b01050f010c05070906081e1e03040e07030507032412020310060e0601081f030f08070507 66
    0x26040c000d1040c035400107442ca020303115480080031040383c0382807000c07059581200c5014211501e00303c1814010180121446040031401d03002c20314020050f00c0c211400810b0350340315259010385003e1800c1b640e03a55520070740080c0c040003681c05112001b00b103805003070001c0d00151a0722001580ca440c581500070b80090804281726000c03c1c54070010b000400c95140b00b46064403000e841041d828200140100c41500311208040d0840c021a00301007810075042d000038048400c403000302c07210f905054442e5920403000f40c030404041c0d485200e84030720034444030001d48803625a0700d041c4ca00306550f40909440014003100c0260000f0764440030042d01d00d0f09442042246d10405012200c0d00340000761005019000e03008410030b84c1041d080c01811075600304850b181c1750050030b030280310043d920410042c0c5d09400761601c0d40820740c040005400c0980440d541c8801505942c0d1306442c007032030341d19003140104486c40c0580e1860070070400321001c182d00304454402048603d000790074410174a921403890f1500341c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 228096303 1250 228095053 228095059
    0x301140103030f1d0a060f0e090907053604050f030703120516020c010e040f0207050c10170402091305030c0d02010e07050f090907120b060102100e0307061a0a090614 73
    0x2003141145031170700c15000c41a00c01c181001480c01603030203800d0b03d0481c2d242a00942c4138030340d00d0070005502e0003c142841220410f64001084c10349034130741944030b02503203039090702500c010b030041d4003c00a2410240f07420500820540f40e440782c0309442a4116880088141d020828180350400381220603c0390f1580040e241081214809000000940320100905094100594911041c4e95503640b94410700c000700305003004564034045440d0807a29540d0f5800281d22420714441c0010030b0b180183c80c0c041e05410341440100c007690340c540c200a000340c0054200c007150031081c0649000100108018800c10003030800615240303100c49002800c0d1103900c11040300c60341003001e00f008151102c0710394140500007118a440c0c282d50380701d4034900e00380c880d600240300400c0404084092142c1d1925041c00340d0002ea00351070407601146811025039005509581e800c0d0f00801140d404160709901c901c940300a00c40885a0103825200011071181c21030304440002c564070013081100d14034014081c20042e00603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 228097553 1250 228096303 228096347
    0xd0501050f06010c052d0f1c0e090703020705010b09010e0f091b09040812010f0f0e0c0702130603020a08031c0b01091809050102160605060904051b0301140103030f 72
    0x240e500d2075110000701e00c60482041c01e0106089592403206000c1e030f01800144c3c102c4180031800d4808664600840c0c2c10050786921410740c0d40385040c803e071500c01011304c01504c0f02cac070262604042140254420601078825540e110101c07281039407808803090003096034400c0401c2a041c00101e0300b4440300c010b85a841030354000c2040c007984c2c0205042160140c10304603014031450b0342e10300701900c0c81d00c200d4a01000031801200042200f034102031003e4142c90900031034145081e103030003036883e09481c192440819402c06024403001854014a084a0725a91860110313151303070749502090002c40141c01140b81600003081c03003c106640090b200b10417047c0203405001898400c00040d0000c00c85008008c1003a88103529000c0c030500942012200ca98084001c568078008000d800811303044400007120700d94149170204a1910340700c1c02c41801190800d01070180c2e4000045140f054140301c511aa4040d500e85580504521000e07906a0003140070f1f84a44e01c1b03003008410020a40500d21541c080c2401176 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 228098803 1250 228097553 228097577
    0x2301031104090b1b090406060201020406020f0703050a021c15020c010b010207030b070e0303041505090a1d01090f060b04090b0a120305030a0f020c030d0b01021002040b03040f030e0d0501050f0601 86
    0x2c20110340d500b110702084a0000c0f04d8104c0013540c09445a404039540190a003000014240c1d81540104111050782c1d09403003416070b038900c072192a40d001d48006030103a03121100c0c003c09443c08031002e1401000c2d00c1d9072104c4400d681d035500c40c0c0c0955508922640c1542c00702d05081c1c104028098680011403d101403c4c00c0303825542c4102e4140c02c0039056508001c486030401417030362010001c86001c0c1c484103030000260300302d90030020110b501841d0141d0080001001c00580882d0318400106035404103034050085a09042940e0000c1840071207200302c55440e0b160006481e22503c0080024040484010803010302c51414030160a001e81c1c094040b04001814040100345c0c07207802e40340c000700c2040700030a9015400001d000a4001d02021141a000016424081440d20ba1044503200421303000c0c0c805440d94032242d5400c2303000740c1c880c0e059582010070020307000071851304098100d02d109007441c8100c0c2c1c00740c0b008152068041c03401100d041c0e40d180140050550401c44103588007400746801420648 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 228100053 1250 228098803 228098813
    0x402041109030a0b06010c02120705010e04050c0a08071e02100e030307080a020702130606181e060509061303030804060b060712230d0c09090b0a050d0501230103110409 74
    0x4083ca015041400041c00b1401c03580c0304011b0031408580081880c06000c902c181c040342c4850300d620800d404524405180180e9003401d01403a0b120303144018480c2e04000f010031055401c2040107004074100241030349460041c14022240d00d210a5140c2c2c01041451b000b802c445049808065103503116038028400c100210b0703800111070f580712060150242c0c90300218800b190b060140182030045550a00b840400c002e5441954011521104158001900d9442c10200e0688071100407802012a0114044c0301c000e0140b002041c1016004d0942460124900c450f0010280c1c150421800102000306000c14410140034610030614101c4525203004825030710380c40f64100c2c00043c1400e01520301c242c62504488100c81c050b07203940b05400d50b9520120881844010404c089404011a00303200c400b00e05a1b51600c6200304004010700b240e0030f85400d0ad81004240d0211803411245036480b0f1340300107918484020454420314520b00820065411841c080d1f038140c0400401d903000341d02e880c0c500c44c0412 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 228101303 1250 228100053 228100063
    0x21e031b010e07120c0b0409050402090a2a051b011506031a01080a0f0501061e0e060d0509030d32060906040f0207170408060603030a020d03150815040204110903 71
    0x10111280c086000c4d800c1d180c40c064908a0b136024268401d008a0005090360141d00010b00c82c5108855401a45e9110100b1004542c2900314440d9070b000c89112640488940c0c1e58107445640a5040030350520b4168450031602080420241d00310780d46490100d41702c0c2c0e00c2480c0c180082c08107400c0c18040e00f01580300e4580e42450301003982c0c4c104090781c1e01040481c14694840300340f400d8143d906204560711004003030070407103e0100c0300350400b440742c80c03508005108840501e004e400003851a40f810034100d0680018180c081c000c203079140000c001c4440c00c401c0382c1c8a81c10040d860034814440900c1042c0182d03400e01c0d1a1075036062030307080180422a66680f02020a5441007040710b000403000204640c0074000e004038280107001600c0e503494280d0700200a0040d0003101d2442045400c9a5600d20030302d602ca020340c2900304003503480102d850714030902a812407038003007004a14016a1941e1410b40516010038082d154192045200c1800207504090041c0010f02070316024003841c115031040441d5540f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 228102553 1250 228101303 228101309
    0x120d050906070305070204090b01050f0a030305040504051509041202060c040524090604090b090606160803060409150e07061b0f060b040e070e0105090402100f021e031b010e07 77
    0x641c074001682400c25010703405490100360013403c1040145181d15000c055200213010b018031a80041440d0001403620000c880c05481d41a40e4481c107140c5400b0902016260103080e504402c203c4481d4501d0f10340300c101419200b075010304150102c5410030b003030180c2403041c05040e00004000c208400c1c0202e40b107103120415414000c18600001404894018045014010946034050310002d00010585229040800c070040d00b103a540790507131140e00030015240302c0d60816241c1c01402c0282d4801158054024546c131000c0504049000c1c1c059946007c00c10350f200c0300d1842c00c599035000c0c4452000c3d041007114044c2446041441c4541903000a195071411350040081c45610b07030b0300c248810400207800207812000d025000b80400c0c24036890300c035180c0b203403402048440b08446000255500e401e6501740d010326006011010341c80c55410b004c946021141c40204e09621403c0900710810f5091600103e2040514001d5030703c071072908152036103154461202c10030036070404800d000c0c203072404104003040b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 228103803 1250 228102553 228102559
    0x902090f1f1713020d0203120a0c110609150d020c0a03030f0507030b01141e03070c030f020a0803160c0b07032301030804090c11010c05040302010f170105040f020708030411120d0509 80
    0x1201740741d1001a1814007502d0460130803160106000402c3d540003800003d410b80f141100d061400c0041042c49400c1c080c114010758800c0201c0d0740c0c802c030b448800d0003c000701c04848074050b26210940a10741e29100740b101040b03000903510402d5591101051207190740007101407034107101c5a103210f80001c104152655407084449130001d1480d03103140c41c02204083c1d4910081c03440b03440e8605024040c01a540b003640c15004680c04a13030b0301800398404101d64080561080203141903840d002d00d42840942c8600c0d83c0b0080c441c4421490012610b00b40b0140d2084049980c04609004114407042c144403a910391504030341e4032000140300094145065405403000c07020000340d403207104801120328107034040003c00f165192122280c1d040e5403190041c0b041d03e00030707210012041c42e42001103e420042003080c0c524088100018003140c5001d030000c885916403108003509109840c2c650302c0c041e9005a400300c0c6e030380b68030302c0c000e420a0a04414140c03071030b41010040d214100c12600041c242d4429081c0140c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 228105053 1250 228103803 228103819
    0x3280804020f03010609050915010e0c04120c0914090f0f0c06090a0506030106020706140a020d030509010b120703050111070506040f0c09050103110a0801020406090902090f1f171302 80
    0x10b2141c4003540640c0090000780001e008904180038025216044c05210403a441c2401001081002040003050b004603200c0440b02d01e042d160250340c04034440f4072402100d507420042c0d800100c04140c0c1c09114040c020f0b8a0103500710341400c084203440e101407480d00f0308807500240c10b2080601c02c081074040c0000c80540e440b6a848400d40009460400580c0140f54001e002000109489500180c04019980a5240c1c0031071540c00101c412101d004444400c40141d1000c5d800300101c030b103e60407440d0002d81c010300120710568008002400300c404100080030540c400c43c020003d021007401100c00084000a43e10b1405070592500d5403900c000800203003504000c11880300c100403201d51090000d08160380c040081d540c40e840d084c4c00794076040d200d0038030034521114003048031441071007150104c3e0030a4494090720fa143c1464140650000021642d01c000401c00120711a183c0710f4102005091b0292500c490528868001d005100c82d000e03d200b0140038502007046442d0501c51211025404861241c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 228106303 1250 228105053 228105079
    0xc022802030c1203030a0b0316061805030318030c18040f051c05040303030b030f030a0e06220329190e07090507120e0c01050a02031207020328080402 66
    0x80c60400c04502240c3c001e81c850052250342d500110165000784071045046c0071a000d030310201592055503104410012080c0c80c0100303d20350150080314900f001600e15804242d030b440e80041d0940e044040302104900c8045044100361400348454210b80200310380800c0440241a00b6414034880200300410b940100820078080c89000c2003248860305044084e00101c40082c0c800400342d4010748411400b00e805d04004c0304081c030300032407658401e0321500000c604000e0754036000c0751011f100440c90303904601f003000030b00003003001c50344541c418003250302c3c0d80c00c5001d00d98500010001000b80802e2411540e02104405585940b24459001103070b080700074212503440d003000c030300518417404500400d2042030341c001020b0900b60000c902c101c01c681c0f130f40a207046056400000740d501c0c85407407007a180c0100d00144140e600407000740143d46105d2045900300f0202c816042e0b1a46016511100941d00c0450800258500006d03100d24ad081c00e030a141010380003161015000120107440244a8034142c2019 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 228107553 1250 228106303 228106309
    0xc080c241806070c0603150503010b10030f11030a090506010f0305030d05070e0603130209090d08160e13050f0618060f01050d020a0e040e0d020a33020d0c022802 71
    0x3507405140c010303112643e445c3e0b4902c1c0150091608090500c03010740110400034043c0317010303c6074101c4464040d1202e11103400c0700a08074001d050b4243d8030044143e545042905881d0390f040a180703e01c001400c00210500f040c00c002e450514140d1241c2c1556514440c1030000910100550308081d81241001c00c20307840b01d02040e1382e40c80c1401c4030160444004002c200704903141010040c04240255800c100701c1e03d50500d201c0e16022051003040201f44480b005c1010400403040c404550201e42c41c041c0c0d0841804400200601c1d605080030f81016220710501003504920b4036460340081c0210ba9580b00e0605a80a181c50b0034001809903115100b1174500f040c3c00e90180040320940e20070490119625920504080c00c11400c41464034000c620b444c01d0000000000141500410850f070024400048255100c16071210050001402030402c003025400ea11082503510317041100000d4050b84400f2410ba4030400c031454000d81804560152a048003140001160303c09811600070080d21841624008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 228108803 1250 228107553 228107557
    0x121308160303180f02040b04110403020f040204081507030507020303011a1b07181104030203071809020a030c050f19090f09021008040213020a1403090a0c080c241806 73
    0x54040000d015014040c10400000310404d800c0384201e50800c00002001e00340400c0701d00c03801c4640c0322a03001700070a1002d403030310100c4040c0380d03000104090301e49034940c950f46003865240303806401d500329030b0800d20003042d81600485a006040d807000b03504561400070000c00b0103507812030304031140300b00041783c2c00e007000900071041070061300c00c0848080d96a1180000103030454003418510540c6441c00c1844e4004000c0115001c980e0010300502c08135080c031000b0400400181482981c0c99940d400b64001611000c521800650181600c1c690440c0303004103105c04020b61090492051605034480010300100300c15410648400100c00603d01d40303281080e00041050100283d0300c942045642d0440c1644004801c0c400c0780700341c560109894014660609038000c10040c0804201d640c02007041204440b0043c5600003250011505ca12130301d501d40b043d02400726000b07509283c1000000840394146060a01c00142031951109901c4020169040c1180075130350360654840d420040d43c0c8000d07912a42 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 228110053 1250 228108803 228108821
    0xd1b0f0204182607020f04022110050112020702100807020c060d1505030304080307020d030c02090a09170702030606060c010212090601260c0f0a1a121308160303 71
    0x8168a907051060415036101240500103030f512421440001d2080c524080903030708055030250007100e90788030403010080650007095460725003100092000380780103d500c4c01a0b000300610f00700305019030300700000142040705984543c1d800c0c030300411030f00005032194008800d03000300ba441c0c1041c85885802c022410030420040d0150b020300046401305a04000750300401c5851111948814903550b00c3c3c0030b05031280501c1c0708501d6113070414042200036041450078644143c0c0700c0c8c5065840000780707500280121a042e82c1c0d07000344540c1c1c0c40b0194108401171020000c0000007144140c1000c809500081e5141d2008000b5402081d0204450b4021103094054460904442c1403c1259240a8010320360ba04000d01c208000c210b070302006036207039280041c0d82e1445004020050302038080d030541807280282000205982201a07003600046081100350049210a5130b00c40e4190b03a0382800758050000d41001c4d02039100d11290401038400150514111890b04520703903410b66450b40141020380c000c0907140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 228111303 1250 228110053 228110081
    0x11031b0f19080a06050f060906010818030f0a020303070306091503061d0f0d0206010603150b130e0901020a120c02150c0403020a15080901150909020a05030703030804050d1b0f0204 79
    0x43e140001c000c11900300512551444440040580d141c100300001c0700b0042c0d0340240440c000c4404582900c0784000758144a080010443c0c2c54401a008100c0c03407a480410a8801604080140007080307905000d00c0000341f40c00c01040c4031824031000071034a511424480100511303542d0411840006c0c001380ca03401c0d85c0c010f88081c0c400403501d588030507403220066800707000103000303240c008124240a4801d101c101051442441e8a503410100d402c00c85600910400b04544051200011142c10007561640705044510001d82c8840851001400e11046941c1001990b4100402504c443d580000c0c41c002140300c0030000401d03030b150b40c0826a964440ca410181d08800070402c00314048520030f40c86519010a03982d02800c0e0755030707a0000d6089403540c84001642c1c0360071200400c6030004540021001c03e0000b410050300560300d00000f03190034003075482100841e03c01c2081109011051150710480106410700d51860a40d0790f540f002c00030b055101c014801d1408200010070764070b540c1c0c0a80102940c20f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 228112553 1250 228111303 228111313
    0x1909020705010504020907080f0708130b0a020415091202040506010504030f03030203190c0818070e19060b041805130b070c0210020f0304050d03020c0a0311031b0f1908 74
    0x58140729010380000c840c10b900801d89003020950061107030445034400d110400012129032180a001c071180380c0d0150013040c10200c0329009001103803558103020b003c2d05004200503511032030803200129061013184100240203403030078100100402500300900c6980e040b14000f400d5940c2c480160741f00e00030380d00f01404d001d04509a410070140c15500441c001d0076080500c0710007004030702c1200f058608014113080080d00107000300c0c881c64142107109045070b4455041d900c50f80d445202005ea40745080340c903c4100381041a610000105c580b081c1400b40c00c840c0c28491421b8106066860020100110080300359929400034000c003090064003d003031a400380161000b82400e40f4000c00034850020240e119008807046081c020f4000100100c0d03124030354000d582000d162008100041b01654000c0d03081d03004580c40c042c02966540c0320310000d11311996904d2007003441503003458604050341003020240416080010807907030352105030b1907005100301c030070488180100968051542056011044a12030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 228113803 1250 228112553 228112567
    0x603010204241b02061803120706060f080708060705070f1a0406051f0b0702060c0118120f0806060a0c150e0f030a050304140703080301030602040e1f05190902 70
    0xa207040110b00760406907100d028410414400080c036011a0030003d40c4400d040240941d01224001c41c41400390004060f101072030b185010091581d4802c1070122000303591002c061150010200341d0202074451000185080c600f41070302c0c00d648503c06084441403290114485040000c5090510740e0141c3c0140c080d1000c440900c0415410482900c00b251554101400a0342d21100b10011400c07210751042040120780c540900141660302008050783c10140420810005800034000c6200c82e1516522171a04440c0c1400e056090080070202c00c400c2004032031004640300d07070042070180c11010446105a4910700038506a40d01404150014250080301d03942402034480703540b0120b06010300d0001e8401c0849004070290703d80c42180c4042001c00c00500120b40414029a4000280c800c40000c9403406a100e440707080150b0400da2045801d0340d000507040c0085080d10220542207141564586602d0220f1103840c0c03c620000d00500740a801c040c090341000c5020704010314000c1131040340031961040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 228115053 1250 228113803 228113849
    0x70b0a050a030e0a120509010e0411120c07030f120e011104060909020c060f1806040f0c08010902090f0a140103080c0c060406080f063705010f0206010b030603010204 73
    0x1007810001c01d1070149500041c410110b4040131103a4800c1c42d4240100d038000c0292440d412180d0598100f159513141d205440d1258854004848400101035445200000207080032800044c6201c052030fa081c0a1000080d400400000c0a4070b1542403200d60480c1c80e0101c1c100608060941480540c00e041440c1002e901100c0240144c1c3e1642e610b046295841c2c59100e0705034810307140c3d00003081d440103000544040b40d544a40d6004007507842e03498050000450940c1c07908405560542d0440348240e55282041500340c203490003444d69000a02010f45150001000d050000f0705800d19003068900003241c441c01d90b449030070405542d041e0300203556141c0c2440245a08003010340801803164101c2d4100d1403078003900751002c840700c0f83d65211b01a82d4541e994503681102501940c0c100e011050043c0d249016004025840e40410a20703001044102100c14060009948154103004082c0c01340c4400950104541c1e041d5040061556501e48894002c07900a22840e40001c4c03158810701d04c4a5422a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 228116303 1250 228115053 228115057
    0x103030e1f092903010e0a0e06010308031e09030a0c021c03080412050f0409110f04030b06150903031605070308070503120708061f0311042603070305030f0405070b0a05 74
    0x42d0308034a450040c4220700e80704440ca03c140d40e850031881c94041c40108451031016030050707404050364201103031840c00c800c2c010303103446000e0304201c07441c03040813040201c078084a010203003504030700200c5150b01d070400c1000c841e141c2c42068080c108000b203c0c2c0c111030030354035500583c00c0c2c0b50b85501040e0500c030b0700704c2c18010640b0b10181e80032a640345e011090a404640710303c0c291400c40703001200b0140b400389018040c400810065000070f281900c00c1c0a04171218240c403002d000114011002e101a610303001007080018031100c1d180d00500102800000e416072000800c1d11801c034041d000d03110b10005c513030800b1450851a54001020750000060503c100240030000d00f0001e40f80d00186002919144420781e100c0c1ca04680d1030b504140707034903421044600700c1d8400706250f12890070005207030000705031040e046500a4000712a441501200e824000b00c507d440e94400c440c68501841c1804603d55006200d448080d250b840045d031400c01250030300000b844014010025042400d0b074903280040003820b59 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 228117553 1250 228116303 228116309
    0x10060f06081b030108010b1c0302070b0706110d0b03010f1b0e03100c020a03090f05100302030717010b0a02072c0c0f070f0c081903030e031b0c03010507170103030e1f09 74
    0x902d04100e403101c40c0c6080a88c43c178201d02d6143d005080c01905110348c988054208040c1a00e003540c80d2051100c41c500c1201c0189013051039404081428105001414255011012403014a61800280440c129041450741400892626100101c000100c0000b40f5005c06000400c100c82d00c3c208110391865000141d00071800d01c40e88840306081e90720350920b1f403c064244656600030385400101d01015100f540159404403190034504018051011000c0700302c5000d0b0403100e04208001007244001c2d404100d2070000340100d2054042d80340022100304000702281e503059030b88000d00804180d507800340f0416074040c520400e00090f110f42d0541480350b8038010303d4a081d074421121034004200004042240065000c4100c500740c90804242e070214024010407040c0400f600090200243c0c03411442c00c07281342038010a0041443d07801d020109421558044c0054092080c4082e11035405030001000702d0441e034250400f402d8507a500700224070003002d41c1d4140801000d000c0150600b20ba00041c01e40c0c15 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 228118803 1250 228117553 228117559
    0x20109050306040809060d0906050906010614042405090d0609110d081c150605070b0108060601170601020c060c15060301021312050307020405041410060f06081b030108010b 76
    0x4503669682410380300d041c1900c01a240d41c1d020080c4605a0030400001c10800040407000583c0171059103e00c0c0c2296000d403542042030b0001c6004201c40c5920014030540a8005103a183c82c0030b207850161201c0070608a072307050065100c03040144180e0f000b081039524a940140902002920500c0d001008160302c0c030081744c80003d0032048817801d0500142d120304880e406a85036140641c900700035240400010720324401140c40340c1c0c418800303204862188004100c01c2e20790030340302d0300145031100304031105821403901c0f13501c5441002202d0380c0c00318402d025004031900013140d039250180101d050103007960b00301e5040500016401e8480d200011407101c014400c00d000712850320745000b00b5090b4403a05110200119070040f00b40101140c44007501c64180c03281c0102c131314080303090380400d003516000c0300c09076034030b080118203c0d130001401d10982c1c603442c02c042d030b041150754141301400e00903c000707000701400c0003485000540303000303100c0040c060f01038100c2d01d5030364807584d581180502030b01c2440044c40c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 228120053 1250 228118803 228118817
    0x19050d0c05040b03070509130f09030801150203040e070203120123010c02090c0c10140f0f070207090c020307020301060e0a060902040b0f07020112060e1e040b0606090604050316030201 81
    0x444910503402e840944489114443c07030364440a000f140e0130b07080040e005034000415146201c5a0403030307119045054154000204070780c040d9040107403400c42c05030b00c41100080742c444001034580d40402283e0035210b41800840640d200d2079000c03407841c02042c140c41d0908a096001082256840f204808080ba00510144080c3c0012004484080320808004d4000484601140320118581c002e05012035050041350f022000c01103006040d51000388425445007081014800100c040e004132136030200c2d0800140f01d003401c15801c000e69480b140d20491002540d16070103860442e100340700b11031141c0e8008000340080d0341c03074100504012000b5500084407501d80040010014070300d009a8007111925040c00c1d01705852141800010351295008038100540c44812580c0c07403c41e84286400b9060084c1080020b16085460b02d40708045148403000c204051707010800000e444500703560b4884d40c10740d00c95440f9201003002c1201e074082c542260360b060080a1414040741c820754038100881e4001da131010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 228121303 1250 228120053 228120071
    0x32215060b1306030c030b031504020a06020d05030402010318081308060106110a0b07020102160501090b0c1c0c0e0a0e060312041d0705040b0c010516020304140904020619050d 77
    0x89075030301c5aa21502c0103008600070400c0303101e000e540440928212400d010a03901850000a801c01450111142c03c1040c081c0501c4250304012030544045d00380f500052514181c0300f00301804d20300000300000d0405444c3d4524030101c40c0c024a12641155005000b10707180c0a21641e04000e511460040c1c0c0e0991241d00000207109214801040c103480c03503240a0130032614142c0720b6030032214005054806541d001c114071820052030070303030103030a450141000013110307400c900d03040c080c1d180007400001d030550b800d02001d040c905550b114203030325440141c4001000722158000703a032910403540c015a44243c002000140c406120301400b4491071007281645d602e60b9511a58000c00d0007540556582c0d82c070b41a80405072800c0d0083c04c0d582000342030500d1828a41e9900e0012950fa000d40d50901c07050751140c0500c44d010142c07555000704401180090740c140303424400c01c042050441d940c141e11a581903c04038055450b408100c03112500e42041e06000c12603801405001540503004c61208649001102 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 228122553 1250 228121303 228121319
    0x5100507050622021509090412020d03020901090e2a0c0715080f0c090316050f0a0b0a03180203011506080708091c020f100b01030b09090307030503221506 68
    0x100041c2d880010030400c0c083d0a50203003c2030403c60512640c451a0070044c26220360788000e500d6118621580c0001d6481d41c0345100203041000108600c001d244c014090400c003a03801012203000d071040c0c0041c800640e6954410045502944861100306201601da00d4510b10b400b84010300203504018221112981e6400c50369002900c417203581d100080000001c00c1001101950041d000012103a0150070211900b0000c6d003003d0700300d006903070040c81894040101d13041c80003803a501c0040840d0441c06861a10100141074411101c40e1b0302016a240c4507684400130300c0588210107038014000300080c0800c80c0124903000204d02941021440e00b5000807040c522804245102c0c02601014024903140945180220454044654158001d542d410507080d0030401030908500f600c0600403030195080300000d41120000d60000b030054a05030308010140310700200704e812480d03040ca007590b5a40d4807084241c100038403610007102c80b03030307074550342d88050014203803116200d00244c500411110350303a0122 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 228123803 1250 228122553 228122581
    0x10090504060b040320032107061a1509030102220e0108030a090e19090c0f0609030b040f0807140f0613020306041104020f120a0606020102090913020406051005070506 73
    0x20042003035500d901c00c50600030040c42d05d1200c440380036089450180c030039809140c4107a691f07440c840d901d0201041900a0086a000d9462070b1040c181880c1ca039031040c02d01080301e244000603400c1e01002c00051881e507940302541103030784c0f04500c030a000140c0c08071440c1c00341880401c3e00c41c080d81c00c408031001240300500031040302d40585c440c5d16907640c030a01d806901c50111f040103001445960800a0684450035140103800041d4401d408612001d03003800481da21220303da401001c20000c812405200203440e00600076041500714101e0720b44c0760414544040c00e1711408a00410b880c120080385241b50800080d110a0310b00308505a90b003558403840781c0710034401e80036400307989680308401140110f01c0e0040061140c1401070700151600b4940303000c80c50140d1000b100d2416101040040100c01074140c4100400340207180300035880d180c070703100010b02c0010001d440c0200f07690340813128800719540da5100000901c030240201d490302031030120140c06900203c0d41524680903200024420310840b00d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 228125053 1250 228123803 228123809
    0x1050604060b0d0c0507060c032004080a0b2203020a050601241b1211060c0406020d050a0e0d0605040b0f06010f0c0302160b090117010b03010504020c010b10090504060b04 75
    0x10741203061450f00003012024007003010400c42481410090100402c02034000c0218880b8a5100031901418040307042d00c12607103110070103850300c5041c8424482c0107001b05460003501d800440c0d1900980351503030140300c61002d0502000000500314105820150049000814980120b050706d100f40e80e5040c4682d10003d00d0501e280384d84481d43c03203013100203000b109202c15180440f910b10b40c60112a980c0e0040c54581c0c1540300c40450503d0309208080c1004100c055804800d008805041502d402e40285d40d50303001082d01024400c020548a550b240700310713400d80700c0070001030282008111906202d00203003070540d411384500104500040e0040c402d2002c03a0300589060b55502d0980a02000481e124804500d0890441c00f64040c0080700c01011890313030020300400c004445d80e0302c10000000d01654005014107940101e8000100042d10200c420f40e030445a05882c0541c0d50711040488500400340b0f841c4080e888140c014070181d030564003e11540903103405517410001c07039441e050031020758001e80c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 228126303 1250 228125053 228125069
    0x1509010605010e010809010f111b1902041e06060806150c060c160209010308040914150d0f0501020d0c120b0a03081b070b071e080a03050910020c0703050105060406 72
    0x3803c40c1c41c0c19403217100810751200f06100005040e0311030424010036124584030b4520744101c0414601440450f2107121034039651420300030071030040044140740c54050700e131002030300c1183e507805513250074401500c00300000c0740c0f01d0b042000b15544842002d0a00c4030103a840e036019a82d48190303982540318040860f01c0f41c03840040200901e54898003684400d070711a00d41483c00400b1b0700b01400040c1c0721130114074083c0d4032695917252506d003000611012a409107a806940c80c1c001010701c05080080f48081c010480140c03000381e4282441e0a02c0c0864501042c8010010742c40003401007a41d170320640c400c0c0b4460940303684000059602c0c01c1c07502d007a2051200c140740c2c8030718048010000a079210009084841250368003118414110540d40e007000c10b160b014885044000914070300300040c850201d0382000d80c41040010584d407540300c9103094045c3d0301d19903003459912030115840081c00c000b080002081c40da815903503800001034150b107400a51200300e98035802c01c0040390346841d00707000c3d12050799412 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 228127553 1250 228126303 228126317
    0x30711060304020904170405060406050d05060427050309090708040506251b0204090c03290106120e0105010b0a12050903090d030e0a120218010503030313030e12150901060501 77
    0x42e840e1001074031b8030b80c2080b00c0c13400b504200014a035203035400500002c0c8050703229a074864024a04140a0355801440c60b441546040d10781403000300d82c0b440c0280d101c10105080120941185005072030340c40381e4903100750f00000c5a400c200d04690f010b500d46200300e100c0e0003580c400d038a07101003042d03c07000061240011900c5404607410401d218140c04c2d806910f07400022540b06803644c02280484407039000c01d0381c642e80d18100603c01e00c540d1f114125000d14441804a4030788428035402c164815041c05410b0400c40350040318903800c00244c004d80f039600000c1000b00401e580d10545400243d20400000001c210048134080f4081114421940700302c0301c040c00b071032600c10110100f01d1441e4018000300c2c2400b024401c6243c1544400c58224040c00108000d001010540d0041150540c03104490702c1c0d41088200040c0010341f8080240c9801c00e0040388071250000340745c542900e400022502690300082d907540d80c01d0110710002104d4060f0300a8113034011aa444152005007070769000d000306c80c04a004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 228128803 1250 228127553 228127561
    0xd110d0c080405031b0717010e0607021225020405091c030204050901030b060114030108010c1e1d060d0f0c110607050403020603151011010c0c02010c12200307110603040209 76
    0x122840601c40c3c44c0f00b21051381c4440b6207c0c8003088140060301d6240210381e40d1359600c0342070441e0130400280c015490b80000d0003206000c2203401ca841c42035003159148103c17906041748090035040e29070b0401960041042c815450980b07401035a03031918200700c440550078044610410760082c4211015580042c00e00c205680c01c42e15200c904103005402207041001e001004151940d81d4030155000e050410004610643c019100400c03080400a0281100710b006126158440d00155007000c1c20f151642c0d504c00041c1740d1400603d99000b0b2050605000c2e04140d0f042e0030140711a44407201803542500c0e0241c003202c0e01d20785542c1c0c3d02022100d0f5008600c0801c4180094175010024550113001270380301c600660003140105254540760404d0201051281d80c0380c280ca00400e004080d9102501d1602828801e410780000b0014402034901a001140c007044c15441e032803107040644030038208013090300007581944004558179030101405a844490170095a900c525011044a028540040ca50034003511 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 228130053 1250 228128803 228128827
    0xe0901061d0409050f060103061509020c0d0c060b060a02010f0e010903020601090f0f0e0c04060b030601090911090a0605040f06050316030b0307030b090d0801050301060621020d110d0c08040503 85
    0x80e807203820388482c454174500040180d0104a51400b85124100108030380711401c444081003103190304055030b85401440904a000d800044000038005c16141926070741b000e40c01c003200148100703240c850b0869000546641c1c030540540000e24440c1001300c08000c0100010200c500700d83ca000401001600900010404030030a80c1062004a0752144006292800020203c0031100682c0ea50f280c81d40105a200015142a202e83d100610704101c14514529140c40000c010100c280510f0007100c0d03884101d642c40610000c29030344403040280580318015121034028280da04036100350102c9064110f40031510b00c2c4610182c0b4000e91014040309100c6158034419006414680106901440362190000c045a41d10b00c003540108850009000041203ea03001428640140c02c504d0180e810220204071031544181d60801007600120140c080c04003c0c440840a4800c00341c0140443e400c00117070044928104004700401c0c1a0403504002d02100300d542624958421140580307103400c2801030300c41c545 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 228131303 1250 228130053 228130061
    0x8060a0608061302131202010219030807052b02040f09020403080405060c0f0d08090c040e0a03030908190905101d090604020d05090703030f0908070b0901030b030a030e0901061d04 79
    0x50f00701d16001d414100c601240000b60140d0f03a020b003c41e0385040e80c801095507014801c0342e10029814001480c0303044191006004d00c0c202502d008100140001c182d09048002545501d4564008c012440c40c0c8105883d01000f1b5006402880003071f200491001a880019108440407242d011350100c4c106403802c400c03c56190030001c0420214080d0030812103901c001803001407800c0000d52180d22560601462092408003034142c028095440d040c0d00a0990b10b0014950040720340c980f070089000e0b1064a8851100c1c005d1400414a20720054980680f403a04212080280e441c1610018001c0d89030a00c102c03120b6000c0d020703031070001100002501103401c10402c0d5640c892401392015143c24820241c0300d048660072110f41c041600070440074410075500c006c20307032100005c07441d1082d8802c0c28103900365114070084c4501e030300200e00082e8424050b4069044624050380c010150785490900e41000341064404661451003003101100100d905801106804175918150414882440d80d50342404014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 228132553 1250 228131303 228131329
    0x11300604020a08030304260408030c060708090304030506040f021c05061b0301050f0f0316180b04110f0304030201060e090d1211070308100f120302010605060306010c200301060803090108060a060806 87
    0x1680b0800020502440070801001e01070354040003441c9a14dc40c10000b0802c0d240506550042d4104000401c08901d001459540098004c800d004d005000ea04c000b0745003010f1a00c18040030a41600c02c0410300070040340140c410b4600d5290458200005503520407548802d009490748007036105241c0d01c00b410010300320602c842d4064200e86501104200e8004244c0c0207034000d29504000841c41d0140c1d5030710307000e15480c080042e0f4080c05010042600c140d0a40070b03100790001c1c0a0300102c001001d140c03007504480020509111696a03904107050312507102d03205030090034049074030103048807602d05492050546011407015018141100390f601100d14800281c6500c000030203801c00800cad94030144015400801c0700e4401440701d803015260203801c0d130b5102c1e400072348600c8050040000a03600142d5005886501000d941d100d50300ca0300e40e2290100b4607a150316003641c0780c010003045210f0300100070400c01000342c94401c5281d5a035801c0007d00c2400d03014450005940402003079107800c02ca81d250100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 228133803 1250 228132553 228132623
    0x14061515030618090c0a050a0e13050a0c060e0405090a170c010b03030a0c05121606050a09060c03060501090e0c0d020c0a170702091311300604020a08030304 69
    0x10a80070b4090f1849103402602e0f440d240b83c1083c4840c02203440d140c85114010302c807d4030220034983c6004101c0004000050030003c0000014240d20104001805400075803035000c514280d40c907440d00360040101500b61707800b9010314076200c0400d907420340018001d822150320480b107030080600c0d00c40f2552560800710b0441101d6485000d00801543c0610160000d00070030b076145031140f911410312614180d25032800100e020410001c1c81500c3e4204840c0c0500550010408107240d19030621140040034000c0001c0c10032481c00c03410511095064000000b00c89090b600c0c040425151024000d070a102628035030b07450306003001701e2070541039030350090019203a400c0251101c1240c0c0e5200c110f00c140c001e200351200741300009005003c5281840d141078004200e2010250800d007650740380b401c00301c0c003200818403032410b48130303000d4006410308012000c5001c03002c80b0009649044608540d1074000703540880c410f804d448000320b01900c000040d43d03c40ca4007c260100c00314442038454044007001d821080c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 228135053 1250 228133803 228133819
    0x30311090a0902090f030a15060e010806070c02120a0b010504050105040b0f040507090503120406080c04030807031121030a0f090519050313030b090607031e02030a18140615150306 79
    0x5e01960180000c42c602c40c06440c000c1154019031044404491190704113120000c3e40200620480c0c50004505600034400e0a25070920442400001c114400c25090400148141c02440003000400c449840c125807003950705101d5a600c4408210a4449841c4120f0300076026036803600c898905904211303088151401c0c509400c540b1040440c1c00c000380401080e0807003400003401c100e00e607407000440d640700300d9034160036003004e0560b56007058500c01c4103c09020003038a8008420603c2d010b00403480c0882d003441202c0f080c0c01d0541500c000701d410456200740404d142c0110075075002c0290050540c440c0e4014050325225101034459075605005180a03542c80c0f005125102d00001c82c140711501a42c000e50700851145040100d05240841c010140010141014980c10652135104916002c1c504038150158499a1340c1c41100000c0c40200300780d04081c2010000342c0d080c441c0003039045c4441c050203401d94200e90f4802002c89418591070768001e402c2150b9403600800020f0040180d90810b400a001c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 228136303 1250 228135053 228135079
    0x8091002030a0b09011211010c020d0602070c08030301080708010e070b030112060b03011109030c0d0c3c06021002161509050a030905211513060207060207030311090a090209 76
    0x54118409800c0781c03060f45a2810003c0500c840401f51010344442480c0c4010512910f902043c603030340140a00030700051f001714004040056050221000d015020704503a00d0b580c1d40c45c00d9a40d110704500c6a13862951a00c51403a1341d2004c041001e80c00d0700c1c0008003d0b86164038001406c10b2400d10305000303403070703903a6160354141c0155400e00644e01d07120501a059512102d00e101054200458504c032288a0380c1000c0300a4002003101c541d56003210000b2401c6043e02c1c80c0980d0303000c403c01a041901e0581404c2c05142d0001c0342444c00d4510503200c05908540b01000c2c1d40c801d410032481145c080021a60421256000089900c0c1070084d032341401d041c01155594080d95003620b0000d80e104124042000d8000070310060800c030010a800342e0040840035140310300b01002130388802c1f00c45e080c0c4d80c24045040010346160300c202141ca011b2540990210342d11403003420000029000035104a0019040c020700d9003048402906840b8281d000030712044030030349002603550095100182c5140c01c500340d0703000ea03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 228137553 1250 228136303 228136309
    0x90607031b050102040e270604140c060304150b0105160f0305090603100501030e0109110f0a0b0705010e060a020a0203090f0109150201051b0408210d0501230108091002030a0b 77
    0x600010103011401b840da03414034080d140062000a0318900d01c001d031074281034503c01d0340061030300d402039000440a02076124460f5a039040c0802002d00075040b1000000b8041040b080741565080c40d0b05000c07040007403106038001190140b00d00b414014100301016902e0001c640919031034060709119003000c51a1121000c00b0584541080710640040c00c1040700820003560140102c000c4000210000c22400c1c2d202d80d100980d01301151072040c09400e002c1c040c606243c40720b00b4034001504000200a85918007450a0790281411991081031405008041143c03003403a170080e01c02e04001c03500510b04011007041800180700756004028100490313001c000445800440380c0c400d0359803041e03001049514040034200e007000380e030303142c3c19900c440108005c01c800100071940c0d0384a40c5290138480e02c94802d40e244000c55000d2100c02002882c5858000203503e00075841c000300d100208401c0b00010b1a0140c01910300b54000c840f17080c0c4a07049a1440e8041c00c599500070742e88603102000000b401d80131039002c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 228138803 1250 228137553 228137557
    0x5040b030d14121602070509060d0803040c05090f010f0807030c0e07020109061d0c0609090f04080c10051f230303070b010b040317090303121306050408130b090607031b050102 77
    0x82c4c160081c2140d18044240e505200000190405444581060074000d002ca44400550000507003008000720100301000015101c01c4024003000b4409040f500f0700500c0e080c64000203100d42007081c3c8002400082c1a500410901c0440740c110003100810761400003070307008850b00103010300c0441d543c4206100c0000d01511944501c0b0001020710300c03c0c4244114400c0ca03114085000b42c1c03003002d0a201240446e42c85000060b03000c40704200e11080c64607545000e5445004803000c0c40042e004d03200900a0403602603200602c83d414030000d80c1040d80240160310401c0015018600008000f045201580c90545c05038800300e0101608803490700380030b0344030400541c1c420b800554410a0001c2c0402c1031020b0403002c0c81040040328110b51905500d000000d680f485034200729000100322200007200e034508124a2141c503604280140300071f01d800d14050081ea48043d0404c41d00f40030b800008205041d801c0251150715001815841c90100b154030b0540301103034403a58400c0200c041080e440300007842800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 228140053 1250 228138803 228138811
    0x6110d1b050a03050a111218010c0b0c030f06010c0f06110f03010b040e0601090f0e070c15050106020d05070b0c03040501020c0304060c030201140f15030309030706080604050105040b030d1412 84
    0x1035503544442e4544401000d20320420040082544034104010071f20046900b2502c00d4020041304c50801064a001a0b40c60100031030b016000c2c00e80101001010b102c3c200003144105c40628013000584e41d90401901c401c0a251b0018243e0018481c0d15000511709038820400020b20030310b41d80c1041c07404000c1800551007600800a0b111021604001808480302c0e01e41e042202400c1c00c2200c1e82c1084005180501288195112000c484c800b00b02140c0c0205844501c03e80c0100c0d1110000c21589000c80180c1800e20400c0700511901448040c090710a40c182c3e07044580c4890703825041d440310041c8000d190030181c010380d01954208803c40301108200700034002402c3c0ea0300c402e40080c6160078041d08540b100e86200035000c10040400c803214070511002940840f024030316084291039240801d1640c0503044560340c040c8244000440c00d190046001d5120708003c49040c8526a00c42042c4801c1e5aa0070302056059484142c10071020750142d0041411040642511400d109183c41c80d4481540261 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 228141303 1250 228140053 228140057
    0x6061209050c100c051603021807120e0d0f031a06090303190206010807120308010e040303060e09010b0a080c0a031e0c171501051315090204030b1006110d1b050a03 72
    0x4c4990100310742030016000141c1c100c0c40f142003807031850b00031030b03c266198004401c403002c8200c0044c0d00c1e14080c09290400034007180c410011140070003203042d1748105a02c15040491030b100e00c509131140c800d00030080221000095074a48000c09414000d55401042a1980c0b6000510048114032041002c000c00d000c0d0503402081c0b154981101981841c9090300032461161050301c400d40403e03004840f0790f046405c80200c011540d92607090450003007040390000c0c903500c1294818010300c4141500b0450740048101c4807005482d40d100303541951402100403e540265100c0420004126101c1e000040500415100c0f00c032028150740321a0404115040300f1850a56034000301c011000821800030041e0b40d074950440d555042170001910018075030b0070949a40d0320341001b08400d540e403200b41030080900748025920355890b49000800000d04407030014050494140c0010003e104800088044644d41d010f0480d8404000007190300781b00005a141400e008020b2080c0007890410507084800d0083e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 228142553 1250 228141303 228141317
    0x10207090b01171e070c02010e010e0d210306140f2709010f0c0509010e06030903070507090b030f031204020112020c031809182a090405030403031206061209050c10 72
    0x41c507491300c03c0c0c81c0080c00d00d200b004400b00c4410010307604082c00c072010035000d0070044110800c1d00c00040480700d29140041c9a4441b40f1041200a41c020341000f014001984013400100c2e1240800910500503440c004d0340b1102c251550107140c20715400289042d95840810041018140c1c103405060700240d444074200d0395070312106c442000c81481502c084580d24a040c80c50a0000b0000900001108803114459040080810300038031003041103981050740581525140d6580d00307500c01c008c08200e210706000b8007414551107841c84000c01282c010b03102031001c0300724a80304c0c2d80044036900601555400d82d15420400515210001c2014040300d004821107405140b60038414007600c0349015040000813509480c2d001c240c3c440100341c050b002805c490b0060100907100a81c191507100342814140c002c1114002e0005001000c4020b0090340e001c0d440b1204a40041d10880e0708545041c0328820008070510500301c4012007640003081d0507809013080354020031040340021441c0411102c00400314244d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 228143803 1250 228142553 228142591
    0xc0304051903120305090f011404110109061b0c0302060c030a031109010f110307021008011e0f090e07030501050a020903010f050603031b0726060a0506010207090b0117 74
    0x10a86450301854200105407a41c078503900c40d6000c0e000154200c0a154440d0b0008112020030095016070180c84402070180b500c0b0154040e02c072083c20756050301c00174038011030301034554012103200086139050360f500d0464202d51441a902445100f0003210b43c4081950000b016276078103000780c1960040c55002d556241030310a0080e080303800d5105520440502440401c00720780c1c00804000c400c545504200703003030820b007545c8682035205204000754000ca2038400b6403036880d8052402c5050303172055541c003030001300c1110f650490010148120350101084900074441f034402a00401d121000d0b100c1105e200548907a511829941c00b1070b80e404265502086004c0189002d000d0310b40f90306000c082c00c12840c00c00001003901c92160036444c00d90391900d104c4c0580300c8201080140d00070856490b2034001550344940070382c0c03c0c04601c44074071340c4ad104d0b07180403c0c440174407842000e0003180143c00620502d8a00790000c400303401000d0145061060185601402c0448010b0191080186400c4c50780a451 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 228145053 1250 228143803 228143809
    0x1050a0f050a091205070219030b071103070b07140c0d030219080c090f03031606091119180b04360b061903060e0105040201020c01140d0f060302060c030405 69
    0x180041c0b00d29520703414500f45001041d041d03038810f002c0f16024505503a0780d003402d001051554101034041c03e2042c140325400028000c043d2046400b4000320b90318000d816080e0910b407075490161040180c064250800416034180c094100031211401030403940c0d0414900342105810102c0c40c500d40b030f02007500010135080101d200150507059010b241810036450030309002c600018020000f480e401a549007100100a42d0100151410840d1280390302c2d404000358604100a40603a05040f10f0340c406943e815002c130301d03280740c0794014031450405500d003075454121541e0000d001c044600400c540d071100d44500c4c9031158003980c0c41d0b9030301020a0448644030450507162800031040c030354015071080305e00100056009600381c0d0b002101102c000c070301544004480c0507460300382da00051a403481c05406048225041d001144107900136026100d03a0b641100c01906d40d50305500c0e140c200a81308104c001c261032a40d5010306200601381e00c0001d220343d1a54003049443d4015803034912030358000b080401ca245 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 228146303 1250 228145053 228145061
    0xe24010b040b12070302070c03030e0108160807080a1b0c0b0106091a09131e0606052506091a01090501050406030c030b15062221032001050a0f 63
    0x240c0d42000c98603040ca081040611030040302000c01c04422240c000c60003a5210f40c066582c41504042d100075016664a009030100c03020b10041c0c0d020410001c0098590040031020100300850f40d121031050303079503000c000c0f94101c8004003101e1005583e401e50a56408920706030031840c01c586d840d908400011400e041c02c0b00c0f40164040b0003041030b00f88042c0b205002e0311025202d42508200f041c0d4481b400d000003d04068610042145d040b490003036611108440360001c41400d10106504008803030300e4a00482c1d29104034058082006640b883c03203000658165402108680546030006a07007149988144410801c52000c103401c88481c0700500c0042d090344a00c2d401414111010041603142d50360390781a81c603061001030721400b44c060000e1006c1105124400040030000c05a55541c5150720725041030416a140c50100c0794410711000c94001c0c80038809020440303250001ca9903056040c2c0d8102c2c0d04000700084591003e4043c003030481401000d0040030f000e814801404a0401b11140b5010116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 228147553 1250 228146303 228146309
    0x406080106060c06110406140307030f020a0801090b03010e0606130e070b1201080d02060c180a1e0506070c090b12030f12091504030e120f03070201031508030901030c030e2401 77
    0x174100400080140315005409000c4282103588442d480b135480d844240c0040041c80203403c40e0034000240b44038400d500031100c1e0305950850008100001031071062500326200c820700501d00e5403200300800c0d250f141100f444203280540c0200422044085c480c0d590810655900c03c1c0a80d03070011500c44108034545000a02504ac0c110003400100e0309080003c0d034404000d0070315404150f0004800000300144461022038240103408451500e503142e640460740d03060368481d0101c0100304000442d103403515604541c0c03800d4100038408442130801110f40700174588006200d0344031075841c0648005110a0015000680a400490b51109003402c4050441c2100401e02e11481d0011850240440c200c60107540d00590503281004190340104003148400484902c0980c0c50321510841030324024001009064462003a0703401e11002124110584446625000b42c01c05170300240701e0500f0551003540400103a000c07a250100f1400c1010900c4c900b0040c25842511800c40031041000060010038012801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 228148803 1250 228147553 228147581
    0x10e06090403020d0f0e040510030209160210020906120a1b03060302030607030b24040312090614090a03020a0e04170903030403020d020f03060f09100c0f05090406080106060c06 78
    0x30310725041c0d030029101d20040400205201116070381e24100c40c8181440040c9030005001040603050001c6032805890300340c07004031700c28800000010401d0010100c80302400c00d90360000c10701c0150007a03011002c0d4010f031541c190090800e000d1305440c0e500e50f81e001405608821000691028940b200310306914030b640303203007060500b80401000141c40004905a104070246000661712501c000010104114420301107184a00c0881c6074464402c03090040c130071a44102c4a1000e104603040080c0e0f01903410f84900c40104e40c0308e82e135803491008101b00030500500000c0001071225103ea00040c0d0703400c400c0e082402440040310400040000c82442010b080300e03001115810400b000000039628820780c000240541240c0980704215183c021050300c4054008041d01d01a18000700304d000c150400716101d49103882845600540081107100d041400030190f5566101194949005e50380e99204180550700140c0e2040c0008080c0820700c2100003804582d82c5403c1e10f8211400d080080e41d80505010030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 228150053 1250 228148803 228148819
    0xc06060605070b0402060c0a0804080c0112050108250503030a0e01030507030b091911070809011b08040e0c0c0a060e0706170103060b1807020703021f1416020d0803010e06 75
    0x10115000c02d07075141c0d0260381140c48587e900102801503050100042004106031004100070402c51008181229206001c1e80c507880202d01a2401c103040e250284030b5200c1a40000c40d0740d90550001ca500d10000c400040410564190b890003c01d00e1035020001d580c0009694000003002503034140074640d0003180c1072605022801c0c0c907400185004c4400380941364200e0380350f81030140d0740c51150045400d0b1070a0f204110b03243d117841c4c104140c499000501c41c90019010220070b12989035031014a03034401d9000604c560400d8200000180c150002410807083c540052080d9003645d00304000032580c640c400d0301c0c081407800000b102c803490000c050b00003105100304c0c65180940351a0000c0b4260440342c0100020940d0307208000800d80f12004003506120424a0108000f5040c1e00003070b150b0300300c0f4401d8440f0321a44110003040403032141015086400580340340d41d900e8010709000c0c090200d031130b84100c03c800e4154440c4d00090f070040c2c80000464000c0c0b0003000402000e1704602c01030790300500681d00c0301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 228151303 1250 228150053 228150067
    0xa0207030c0507081c1e0f03060905010b09030606030601082a060703030608011109130903090b0c0303010e01050609010507061508030706060f09060506040303140702210607090609050904061b0c06060605 89
    0xd2544100c401c1031b6010003614118a4852522030b4000304000c044a00040000796103400a00300564480070780c0758001c0c498480412000d040c005101d504a03402c1e030016101102c00c6036010812516140e400d0036640c4642003001d64a6604d1200815480d0b203e0b40300002e5803850410118290741102c0c3c5846c00140043c0041c41c0b5130f4654540c800f413802c0e040100023440341e0f10740c50306480c00c010b41c7d044845100004580741c072202d04000020750580340420071208090303a8600c1004150b01c03030640480d00056040c0008070015411b0741105182038540245910701c40c0c0c6851165155802001054510645400b8108090303000c00380d45074040d0443c00d406100c00c07030034800400c0e81c0c2c1c4150f1100400708034185018024003084507099905803076004215030b926450303206c0103a902c0070401c0030718541c0e80560070100700468041e00500c0202d9400d030b103804151614141c10481e4104008000340c0700c25864144e00614801c900b0801041c1308442d0700c81141d124180e082c44e1044074401d030400f00502800b0010a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 228152553 1250 228151303 228151337
    0xc04050114122e02040807060f030b04090309050f030708101a0f0622031506080d09051f03090501090507030c0e011406071b06021f140a0207030c0507081c 68
    0x800000c0703020310402c2c03502c51484043c2c00288500d0f4441000e074000c080e0041a4141d00100042802d04580c1c0c09004140788481084101d4464190040c08540c004c01c0400460030001e4a100340442c0c01130a407803240390340352a010304140907051082500b40d60740c400029401c6041c424001a07450a0f52020700d60703210500441c019205e100300c85507601b8040d008036031011541d04003070000356a000d032107d811021901c100601910180c045c442c014011401d54182c002c1c1700c2d4090b401110300040ca03411401109a0310918003c04001d2440205070b15444081c000c01c000b40107584182e449240180541499402c001c500300c00c0315005030404101000041000b24622040c00c0c03000742c81283c0150380c0e031150b85000741000b9039400300744e0710044100500041040d0042036011302600b044c1c1200d00b104010f000280102d800d5148081130703c04032600840d00c00c1405602806006129090140e542c030041d03180c203843d0003403a070703c41c0d03081d07a2000d03c1e40790b0004808400c8806042007828051209800d510300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 228153803 1250 228152553 228152593
    0x203060705031017060a050405120705100f0911120c0d05030703090e090601060f0516110a08030702130906060503030301170c0406081e030f12010f08060f010e04050c0405011412 78
    0xf07411b2a540c5031030105052240a00500601424000d240c95840b0001c1c5012611000c01c1e1a04802e4145840582c481c240307501c1c091110760640c49224100851a520100030140300403100c0700fa62441108110b80140d1101448200814003c00085446000515000b0030340041c1e900140030805c1300c90b080c0590101d0010301075055071014284104861084002200c0ca40181c2d03201054011500070303d2001d1001c2d130060000c00c0641540c1039404a61074000c1c4541c0c9104a00c4025040100780c25400025200790744035410061280c2e030040b4190b503403600040d1860f0820381101c40b80d41e00d02da45201452404000c0440400e400b41d03070500209150580c400c0c1c0703901d810a0308030100800c0b4840c0702d0841605204580560a030040b10f5900d4510710b2604402200007400f40d024050b11506001c40c44040005680e880b0f180d074440d50061583c2446800c401c40c41024100301e965124180342110039036154092180601805802c05001d050640c0401103a0040700052484039001062074511691480754 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 228155053 1250 228153803 228153811
    0x6040204052509032607060b0f1e0103050f130311010b0301141608130209060409201201051501050c0102120103320309040209010509030708031e0a0801140607020306070503101706 79
    0xc009003234084030020032074071580300e540f055000041d0804400020003020a01c016081c007030f80e08001d507585c1e4011005c0d12010039125800019100c52081d00003070b2082d658000102e10420010034002641d801007401d5601201e14484004050400c01810030341b540140e160a40b514640780026040c414144070003100c0f03440c4040e000391407590028115490301d41000301c0c80c0d544408040f44c240d40c0c14204107000803100441506c10340048440c0c401c91881401000d0060020b4a81c540ea00d4102030019101580800743c0c4000700c7d50203200407008840160511070086006190030001e13001207100f0f000d42d030181201d9841001440c1c0e5049070039540000b01b540c0142c141610016525644000181c40a00585640350390601c103140d80840c0c81d001c0403001d0700d2203242078040016503180001a40389036014440e04c020014014500401c03180d030b0120f4400800840c0900503500d4101c403500407074244403003107540b8800b00380000b0900002c40c55024030140140399120f485031a0b1507070348030140d4903140c1c003030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 228156303 1250 228155053 228155063
    0xf1a040f140607020d0615050d0b061210020c07050103060b0c06010302060a091a0d05310204020d0c081503030406050d051f0e060f1206040204052509032607 69
    0x41c03484809881d81e0040310030943e001859030218900614099024002c00405c1103101c0148103400504d50400760194400c19034841c4c101019035890205004d80f00d480828000b0301442111441c01c00d03503034103200400074441c1d80e401601201e814900054180c1d00198843c4640c1d190802280164a0000c40d44c2c50644ea412250f40340d5940d03902000310307030440b8260004640c02216021010300c001c03030b010003000c2000007107009100c5541c40c2c01d98001200c00c03403000c21400000c0141550002c5112052201c1c0162000b00018104a00100d014045521036000c0d02c1c04101c1200c24004d100b44101454418800100c00451038a810b14500501a0040d1f410080c10203484030b000c500403900c1d81c161030100c008004000c1c08440c6c2e80b582a140611401e0703034494010740c0c5021910b1000c3c02c000c000c064038150f40d000204113688442d42032200a150040582400b80030301400064104001004a01284915076944010505606083d0f080742c00014440c10350ba8101030811000901100070f640c0319603002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 228157553 1250 228156303 228156329
    0xf0715020c010609020421080301060311120f070801050306012d05270a050c0f090d020918060c03100b0c010e01110705010b010c11040b0312040f1a040f 67
    0x41195080603000d424540788142d400c007000422100b045902030000c030b0742044024140c2001c14030384081201800c0402600030101000140b14481c02900f02016540c0c810800c0e03480e12000282d904c1c0788a42c01d50f2403040c114540c20511514a50082145000d03000441c083e0140f549445139202c02d04d9641c8000180182e02d0489200002010400d4040140400f514200c1340c84140c0303618861840c1600251102c4102d0f19010075101200c5115151240c040403005500d0140340c06c100142d9500728620140e03001d80160000e000603190700d05200d004a04004e801c0b104103460400240c248a4000c2c8240c031f01c401e0030301c02c00a101c5440d60071302080380c00c0c00390020381c1c0e40520000103001d070031141406c00c060340c00c0c40452015030b00c00c21700400029005200030452120028011503a106410002400880000184028034942580b2981d0125001006c56017078905034a0b090302c2c26000303075006001c880c15004082048908020a401400031601d10311450306080286039a0199414003440402c000c0d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 228158803 1250 228157553 228157583
    0x1080a090507091a090a0207030806010c111509130509120702270601030c02010c09090203060a050301090f020f03060f0109090c05040e0c0a0503030703050d180b0a090c0b0f07 77
    0x82408058094020240144845064a1410340d00581315822150241441000103060f003007041c403c0e0307108280e043d41d0754480303a01c800f0011070700d18844000a51321000d03070308448080c03661025600140340c0c40c410611604c99144104020500e656215000005070904081000d0030002041c0c4d224904c503041c912645910490000c124807122100e0001000c41e200d0401050610a00886c1c5124041c2640d092014518114040340ae0f07071b080038004004140490002e12510344584c018540c00306000e8001f420203596800044e0079a2180306060303840134003c01540066080410002003200015401402c407820040d0041c2c802c03020510414a02c213942d40d807410200315042c104040207004c000c1c81032101c1940b13120099125220141c0540c440e10f1100c100003454140802a100541d40603160315041c070704601821006044640020803034015140c04507030000b100707602d9560041d0303003174900060113121f14500001c180c0303100e40006001c643c00307000001c2d210405100b00c814290380300e000d490020303030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 228160053 1250 228158803 228158813
    0x30702040906180302070305070f080d030e0c03032113020a03060504051e030307021005070509040209121203090c04180201122705071707060f090306060306050103050f060601080a09 80
    0x42c00d039510041840d10a203c00c05140e4000742c080d094901500c251900780703680d55552420541e00303114481240d000f400c1801036040c0030358040d4050b402c012080c0c940038a01c1c500002c1c1107503c4a18228101012035040d140301944003d000ca60101071230318140644802da80006070824014400200119126000101080414082114111507480e400030514540d10107441c0c0303075002100c1707030001441000c281401d511003034010b8501071350f43e0340c036428a084180b4007840042d5000c0b06055402c4a203400f0701614452040000c2101c1240d002805030310380c20311035241420505e01440349031240381480b802036001800721054018070f035424244100d41708030000d000d1000d41041c0010300240c1d080f1a92001c0f10000c1c118440d100756129a040c0c0d0603040d29954203e48072803080c8820300c100e070300035441401024014651040440128200016241e0b034a43d038a809640307550304100c0350961a803004004110003003201d0380b02150600090000c61a14a0000340515002400f00110075103540124007400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 228161303 1250 228160053 228160061
    0x403021f091d06090f010e01050609010c0b0a0617010902030d0c110d0b1602060c030f09030f0403030504170303060d08030c120a0c11060405030d05220b070801060e03030702040906 79
    0x102d40701d0103601400c14001d20a040c4050b0032907816004485580000d9080c40c40c4801d0641a94100e1040c0d20f12642401d05215941c2c02a41009050150b820200400b05440e81e548900c070b180b9121001c01e9450400e0703c0764000c84103810766030740241e0406840400607500406c0742e50540e0305510b030580340c00a031400c0244400b2a450300d030540010103021044280848010480e1080c1c0703045070342801040c1c00e650101c0e61514100c40308040e054090000c18001c03424668140e8010b0704510032030381001c08070310214020f40c1c8154822800300f03d00007820403010001345885207a500c140380241d0b0031844c00307001147c5c0190004070010310000c000000100b020341d001081ea00c410107510541c5c4028604131072100014161001c032900842c5c03c00726101c81401002504074130607603018002d1810074446000c44000340c00041c00011507440d00302154560110080301c200f030390314007071040b52182c2d0078995000b80864106170848070820900c01003030046905c0c00022102c542e0740c15100002e610f003160420360010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 228162553 1250 228161303 228161309
    0x10e1c02101e050a29010801050f0402070c120b1806070c0501060f03080903070806060d0308040201031407051206040c051813060b0c070501031e0c0e030102031905010503030403021f09 81
    0x10a02e0082070000c010b54070f0740503035175500c20b0007030a00504114000039400c15003243c10490005801d0710052086040501100d452043c02610260070400242d5401020900f281c0140070602c03451a00341040c040d006102c0c541288a050758a0304240308107d89030345400c1c0043c032400900131802d0b0a0000c000c000d40c810801415a01280d1031400e80b24030700b07031005c0c2c6d00480c1c43d20311074441c0c0030000c101c03a640400c00c9802040010003801040016603030940d0344800c02001a41810754460000007032440360070085204500540c0c40640c0c50581d648100c0415101a203078501461500010f001c901360001c040f030311100b00500d242042d0010000c001190103041006111410f820a0400500092110042e0408588030b8058441180d04c440044081325020400f02d141c480900040c10215101130340007600e018120302c3c004002d1035001000c6820780c0d105641c0c400c5801c02c000000d00400c05540302d1030380034003800c5025629040c69034001503d41060030038014002d203c800b40c2407000501a070000401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 228163803 1250 228162553 228162611
    0x1c09150c0b1501090b090d02130f06060c050613020a0902280e18070815130c0e03011409030403080306030a0c06020102030106030b04052710050405010e1c0210 70
    0x3490a9104507100c0e02c0d22444250114110100214000006005954071040085d010b900300a00030f03004c0008001c81841007100496540356013104241032409110003514142e140d000a192a82c9800d078075160b0000e100200d220301140c424030060395110901c404554031041c01588030180100203510701e415407100f52010300c02c809072000600760040140005040200d44814010038100451034001c0750840b0140e00140c05800001c4d91118940399105850301c0c040d10304801c10250b200700301f086400ca060340b80301190744483c07000343c0c03440d00740101d5070b8a801d80100a9210304003480e606580b0700880c04010400680440000c0842c1c4081040100c565008908000026580c140181c000e42c42802401c000a0030880401c1c0181054040d840c001d000c5188000800390813100d0002d000086e00d0220030890040354009503903800a40611401640100c00000c1d0f01458110340d1407800382c5161400d4446a5000e818800345500450420303009012203602244855030442106000b8a00c1c05034161 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 228165053 1250 228163803 228163823
    0xc090807081608150a0c03091a04060501060c0b04080a0e030d031a0f010c0201030b011b0c0503010c030902060d05100302040603080c1204051e0f06070308091c09150c 73
    0x40c0a1100040541c0b440c220280b004440c1900ca00406032212001e283c1c894034035080300081881c04850b680864400c8440e8940055101c0007551007524022001030300d045401da2071001d000911046101d0039004003082e05110405e243c4503904d00c3c01001c130042001e001c1c2c41e800b081602c1410b007c1c0c009000ba00038010144d0b52801000310b40600103040510030025881614681d588045c10200c80f800c81445058441c1001c003c059030045018041004542c0d042101201107401e0038a010211044200e05c030709074142c4480e040c802030600712a514038501d8205410106d5080250b20380c00200c50701501c0320040072600c3d50740c00d0201c400004441e8030080d0014030700300000080c0080c2c0000303014529066020354031000056507102d0341074041e030300540e9884103211080140e11050720290709140f503405030410301941c22600008400c1e0700320034026004612102e0821040d0001440604121000001c200a0448101d60000e10841150280744d980c25014a082e090350307401608800c3d40258003041c410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 228166303 1250 228165053 228165059
    0x10e0c01090612020912030703020c10050409021b01050901290a05091302060f120f0105090c0c0705040c0f0906080408070308130203010606021c090803030a020a09030503030c090a14090a0c090807 86
    0x291f0744d0b480f280e400da006010381065070100b0316061050543c0181d2594440f4141400c000da004001d41c000503280e0309880641a0b903d65800080c01030b40d1140000800010342d500b80304011000c0510460710300031518020001d844480c1d61011003403000d686040d140568680c6d00c2c0c0040045450390090081e40c41074002c581e8a94a00404c8002d03c00e00c0400f4035942059110a001900714550030b010795039010103a20002040c403210310000c1c02c1c0e5004480110b4015598590101e030403114515a020001641c651039003151a4010480ac0c00500813450318540038580750300c1300070842c018000001e00301f11078200130030035020001c2905003100c0c1d001002003040030b984d104040d542d012009a10300052940001c4100f5450140e030500301121091406149907540c0d17074010700025032080c9294428083c506e480032021801c100099071103016110f184550710301262040140c01220303544950100011190400711507281e50b02000d400100c1103901040011091000b61940b43c0c440e000007a161041031000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 228167553 1250 228166303 228166339
    0x6020c12160c0b07030e04150f1707051e0d03090b121605070507090e0a0b070206061306034b0210020d172a0304020102010e0c010906120209 62
    0x385100da8803031a120380b0119920550724005009141c005000301d0250b52001c1c2890a150b08150040301030101d60711007550310382541e03081000c59174009490f000d80c0750f0146050701c5810003226001d0441200c543c0300246e2440d10b5442d03030348040000140100411605801014000d496200140c4200388461340c4030714005200b2103418108840000010304840d07510107429000b813084800d100e4001000d085200c0c108030a060140c4800810701d640c0e8410f80008001041040002c103000b0201507001e024142441000c02c403050b860032002e400c503103140481c100001406a0703c40508d6541c41d01032902030507000c500b807910207500e00c108894002d1301400c202010340491000044c0d40741c4203e9203a40c560781050300407603499442c54150b50115000d0034a0703207544184032003a0f945c4054840002d20242d48442202040f052038801c1035007418030040103001c210368080c020705000380c0d02400140050715144000070302035171480c070483e000c2c0a02500c3d103d0030180be40d0100d888401d00504030103048280c040c44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 228168803 1250 228167553 228167587
    0x2505060a09080d051510030218060f0c01050420060a0f121119120501120f06020f190e01110d0c0212060708040312020408030a03020a0201140403050408010f060b03010306020c12 78
    0x5c86442105c2c42c9080c40c19240c0a0301c261180346110204566626404006000096000c403140701142a07081c4044102d0100900402e8411480782842084d40e070b01030030880c000340c40031081c020711603102801004900c0d030303200000c1200700e45549464032846000182d07540c010620200f20044800001598010000e01c0380808039000c0001c0d56a4020584030f040001d089034800c0c040d0442d903d1484240c2804030310385d002100c0650780a201d00501d000b10446548080381e111150760790442d40c00341c0c620074800da00640b4134400004282400e81c40c102c00c3d40300c00b82d16010a030000c90103000b00b4139000e6080d900c580342080d400350040000c50f441424074000140003040202c1e000c800107556135054844425083c020b071001c07104090011400d044a408080d000781d0000020307002159680c49081e810b040d1103c006600460280c1c03203a60781c5038140300070395080d5107074220250b54031814003034208919803807002101e04682c0c00c000b0050300d4402c088505420300c0700400f2040e01c40140401c3d4140c036481c981071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 228170053 1250 228168803 228168841
    0x804020d050d030e0f0615060f0409020d1407021605120f010501030503040e160801050103110702180105040c030605010e06030711030c07061b02061813020a052505060a09080d05 78
    0xc5038810484205c616554007404c81d035400c508985070006103c2403c008026100e002e0103840703c0c41c141911260354070100d801507091000d000b83c0b42d020754218041207924103500a100c9101824403c45011035160300c5070442c1c824580074140329100c03da030604c81400352031070514400d402070195507901d041955481d0082d0150000d8406a40e003c640c240307003007084240403900349465110103686440300640003442d1004407241c1c101c1041091750010307521241c0c00710031031820b40c0301c62590354100001c2c4401c444142d581c110038185400b0b02405540e0300042e203183d541c41c08460070390b80c985e113284084a030f03240c0c5802c03242e985100109061202c0307500401d008041d5481d0f40c3e5036070001c48403500d0104020030303102006500214100301441a0444c6040320300041e01025007000810b01c02c02410723804a9100c00c0c55000090742c0812500120506060740c50b0019950306500040f20006454041c3c60b58005807505000c2540c468a80041060740810f03030390000040d0004000902d4064500303003607405c14038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 228171303 1250 228170053 228170081
    0x5030c01050c090901060e0a1212020d080c07080c0a0b010f03150507200f030408162903041103070f030501050f0708010b180d060b12031206010804020d050d03 70
    0x60700041d010900c00c401c0d143d4603000240801400e900e0315a00303841e680c2440c90001d0b00003490b081e010409000b4400d4000581e40b003040160014402c05100030b05020116610008200301c00d23061111080380d54040e507000940007000d05680b400781d049500d00e04a104e420040c603d0702610300000e201002d0f070791404116400742101c0e08101d049101100225281100c4900101b868007540000d9219900703110360790201668100c940012a040c80d0394915005070b8040205076024180022121a145001400a01d81c249600d40002980d143e180c0344200161500d03800c01001000140600c2180080d00780840c0c0c0107016562190748640c07842900b0082030005584c0c6600700300100c3c0d49407020b14402489144507689481c0242d0801c00f440710680e1010307142c00c4000c021100000140c2c2d81309031030954882d2241100250100c0d5031020b20500e0401d41c0c0040c610341c3c1040c804441e192064181b007552100091810590b65a29071000900744100b20001500c284120500302403c1501684120343c880e40070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 228172553 1250 228171303 228171311
    0x180813060216090c0516140d050910030c0c0b0712050c0702010f120207051501030303150b0409090c090c0309030e04061212031b0f09060e060711010210020705030c01 73
    0xd03480a0b0b942c1c07021042003403141e100b500b070100010302075540080d44500c07440c5820b615100aa000c1038079220000c4009444008a031074000c5122038040088141c0002c16041c5541001190780020b1075100070f400045041c513846d00c81900c00e25214640c41c0214503405147e10001e8203298900500f139005442c0c0140b41d052801012800c0340001c0e2003501da01c1e59059440748036526101c07404a0302c44c1d00202500003859001d101c12800a0024003030003440700050144c50506601d1424001c00395101001d0310b00c0920380ca08003c1c0a101c01c214202c50944144030000720f69600c461411b94140d0034540d2241c801c1d1440d200c16001c0103503068020b061180e000f941d500c500c14020740100000c64100b40701e0818400322034201100040c01030f4190b250907007000d003000641d480000c00710240c07030101000c141c0000343d1002c240c001c00507023004c0c0c00d002134201490700051000c030f03441c0030034a070b880f0f2a04050008050003d00c5d00c2036a200b0858903031003604000096454001901c0c0043d50f9810210010702c140d420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 228173803 1250 228172553 228172559
    0xb1807080a050706030608060402040e03090d030e210601140310020403030f0806030705031e0304030507030f030f0206060a091d16091404030f08091603030801260d050d180813 77
    0x402c0c006c0d0025603915002400007915240d08000051403120070803090743c0021300030a00d2030ba4a0190b200c0c03c49020b520b81070b40c40b9110004000041210300560a01000440c000843c8a10005038980c1514072518551800f01d0480000074605501c102981d81030f0b9000050101c201907004107603a5048521341c90300d61750b64070344000305034444050b8014660158426820a45401c8150f0381040005041000b500d01e4140c503a11554100354035608107a49510398032070329008041e030082c400340c2500b000703101602d030500349580020740340145882a00c078010b448044804051300715581842600001801f1242100b111140020300840244103080303c051030a1030048000341642e411b28452070707240d61081020b00801806441288016000070130324803400311020084c2d100c03601120f0280d802500c6070a120361521401a200554184a0952050a610505050050004401000000505040d9102c541c00d08000c4014081601075810580c946141d03a420300801d08020900651400071001d41c1c107032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 228175053 1250 228173803 228173807
    0x306060a0b030a090c12121106010608070c0203150f01050f0102060c09090c0f0703030504060c020109050d050a030e0a080702010206010f030314032814010f120b1807080a050706 78
    0x1054410000031150800c0010203250f21903202c250350b50711850200c441e42d512102d0803484408013890440d11420407038840500c82e50041c40b200021400d0300010a00c540c1081d0300240340301c901901e0202030046032100d5108654080c44400e2924120311100c8506241a00b0300001000e003c0c8907490007001e411b60710740055440030401b00c0c41040d450039603a01d820003d01c24003048810003010907803c010180501d02c046006d02004000c064001d030b4001c1002d04060078028112a98a413402c1d05582c03400480c5800100e002c41c7c00c008820540c14626100c120002081e4060142511011707210b0003101c0400c010044036a01518495001380e080350b0003a81c0750b40324075031400135900028000c034240302d29030780030b140c0350000442e4405850103e101d100c00b03031300358004074100c1444000c2c07090076120300c406004410b500440c140148402c0c2c03614140b407840c0c0b04030035400c40a0b607180076181c01c2440380090f4001c03503440c0c85903882a840804850000e5651310003d034036035903500000c56460103280c1001a10394 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 228176303 1250 228175053 228175069
    0x60f010e07050c071202040608060f22050c1e040c0c05070905072c0607080903060c041202040207050f060907140102010c120b01092403061d0f040302070e0c09030606 73
    0x1114078070051040904052202d400c84101704c000f01c0e0300031345807180807800e50001d0110324006c030007007000004142041c0f07250715902c00d0740b030000011510300340c200c26020074070008011410b84001e81d60340c1080c4410442090f00c118841c01415001070400000751841540141c0c00040c040c010010354603401d4582d008203003622411741b003d00018881c0d1800c0841140c0070040e00161a04e03002850030040303d2800480d005412642e001d40b8107000200c0c8100050909222840e44040d100f00030500d000d0030056140c03200388107858040c0c020366000c158001000340420049111030410703c00c54050740b601c5090b0303a554910502a5140c28810051003003d0b6500502400c0c0700340c4a591607a003416589018a40014004150070504005040788002031791107115860300d25060360540c6d8248518250000a001e40d140d640c0944a903400c080000302d464403580390800e8002c03e080c6540005038440d410100d00c0c08141d50040c0b01070171481c03014401c008011f030009003441c44055003a18101d075222000c001c650 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 228177553 1250 228176303 228176317
    0x20705010e0301090f0b0928061407050307031503050a121101140604050406020d1113080703170307021f020918040c030b090a051905061308040302010e040b03060f010e0705 76
    0xd40111351700c0000091505510310341c490011000c4407800c80c10300303d2801021900042540d04042c0b0190380c4000e108080c015101920b09401084c2e159041c0001c0043c00c4d840300500320010903588070041106000300c00307a800c0c01181c00008542004400d4103099003c8403100395481c0104802002c20131150106000e107050a4045445c0d0307000507910041448058000280100c5071580d00704050400c0e0301d680d114108580340241341950700d900d40081c8902c0301e94203541100016510584042000510724480854100310701e080407901c1c5d440c0d07410180c0c030380159203000c505041b00c12110740f141040650701a040b46042141d04804440341d076918061010000e45014060b0240361000388081000c440607186c002c25900d048440c0300800e503d0f07241c28480f42c9009058080d10440100e01407000030000c050300b10000c80c4100684440c5542d601c21103100d20301c4003d0501603030b074560710f14560303484c1d00240289801406440552801e42520940804c09019500a10407100d0204d401c243c4180e007503502c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 228178803 1250 228177553 228177563
    0x509100302010e0a0e070e040e0c0307050d0204141509010603020306030303074a060901020706030b01050403021804030201060614071b05151803160902090d060c020705010e030109 79
    0x100e003150011284100c0302880c00740c002461010010b502d106500b01360784940116034401401002c91420081941c80000904299078416010503c1503940801c02c5000c40740c04440002615034581b003c1806403201c0c506890400300600e082008541c494035507203c0000c0102c800700b44503a25240160f08902050f1825600f581c02400000c10b2107024408207140015103080e82000001100c1141002944858000c660442104c40606c40d40e90542d49403000b44004544c458142900040000d6890703040d88a80e0040548902c420746490340100e0441e0040d40c0c0141030b10308030401441a040784950300352000c50066180c0100007030b4461141880020100300b01000c14584840c40d01c92088400b02000340304400c03580a9070006450750384802241c0b900c4209942d860310341681c030440c0c42900e9140c03601c0c1402500b00d88260300c400d19001c82c2070800d03212107a02c010384800400c0080360039920701c3c8000401d5140740141500040d03800146400890750709989000d49600c0000c00d140c2616600e190041c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 228180053 1250 228178803 228178831
    0x12070b1311031c0201061a090d0312050a0c081302150d061d04020109060906200c030106170c010309050a0201050c0f0105010320011716050708040810060509 69
    0x4105122460914600c50040c1d41d90031100801800081c1801d4144062043d50010329100a0300c0580a00520b00141408032118200032081c101103d4507100790400c0610820806803c4010140a0705011482040240041026152100b1124000c0c6940c1c1c0d500300115910704000380344040e09101340c060542d4040e082c009102c04194003980c1c2500028080d0500c0b548842001c0340311904201051511841c1041001c0141024000548030180c2500b00400300b003080e400034814160080c00345680d644001c1d4213042e40c2128944141d0400c18100070503503140d424844002007000c50084024050340c145000d940c1d01e141c040d401074088a4a40b1001851038100e0040b1402560144000d801002040c6064a04c51401274280c5070031500260000c8405c0080004202c0c80030fa4080c440305401c0000703080803c00103500d001c0e4040a200014641c0c081c61181e15413002d14240b10f1030581d600c050f8040d080588980e103644046845803803407140081038519020b4000303124507010480c640106003c4e503400c0b07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 228181303 1250 228180053 228180061
    0x40603050601111626280b1504060506030c190e1201090302010e0f0a060c0207120c21030516080d0c05091915030c03020f0c010b030c090621070f0e0912070b 69
    0x1803515200a00c406d5815610403491070080350482c08081c6c880c0d2040780c1d0000842c8207074800c000c119503140d040180599010700c100701a0142c00400c50b81d503420000600840c06500050403141681064103403034006000c40954811004150000028503110360020301c0018400880c150350f070301c03c840840e482030307200d01e40300070104542d507008003070002407841a11840368844151aa4006040c0e07021602c2e0340b0a4901004070411007181500194101e000308d507207055098800034124010000240d40422420925100304168041250204c006c560000d01514034040c2003c0d000da0000501c02c2d026110900c183c01c0002821448001030fa0300340c0001c1c044240b9248011070050018800300d006045d800c01c814a02d106003c40940168070034a4008a8550003907014903080860420100b40954a00c41c140701942c0c0e01d01448000e0200c0b000e203043d0b00c207075010040600d030121a502c252548031b0301c040301052080c9600015407060440204031401c54102241c00281845800c07000b920b4048040085 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 228182553 1250 228181303 228181333
    0x30c0810061809020406090608070503010e061c141e1c0f0309020301060b071119060309050c100c030f1404060c1b14040e0102090303040603050601111626 68
    0x401c0e6801c1c1c0c1e03841d42e5100d15840d010f4500490740719801043c04200411700403c51298001c404a502c254a8a01541994035090440c6124600a00014862050300d481050010801c030004421250010001140f00719150040c684920300300300000030100321801058400200082d5441021805e01507680c44009030200449400800042910805446d40001d0f00548c1d400d0240c500901000e100c12980c410081c9481c200a000740349085019a08400d25822400e00f401c82c00c9003120701750705010400f180b9600d812402c1c1001100300690200d00b840d40804215840f17072a100c031103486a12426000c06140b6010380e200c51078004400100202008103000c2c2034400e5200d40c898520030040c00820700c01c4443c0721a072407803c5030001e000380c0c40380c2c4e5940c28852510f40a26940c60030580c0c003c524044c100c0c404a070700d0f407040e80104014580c40f100820f0444c4d11444004031380b01804000e40b1801d54050802c0034200602c6d128907607206540880d0700e40c181680307141035484944031000500d48201d1408007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 228183803 1250 228182553 228182567
    0x604020909070e0c0d0c0e100302030703061706010e0903070503190c02100807090f031106090d050a081c0c1b0c080f06011a0c030703120605060c010b01030c081006 72
    0x80d40807203006024000411058800d196402082d084074050303214000100c19400301ca0a8582603c101702a48031828000d031141d10401c03841458514001d40c0c1c0340c0c0e989000b0381c040c00f450703800002c1d001402600034180030000314400b03068030355105041444c2d807690b003a455540c0c007500c900a01990010418849131a070101480f8210f00c00e01c1c240f6100455a40e0002003d112404011354042a181c1c1304014105071300c440c00c0c030045c16400c2d03a40c180c1123066850b110380144905c2b054500032800002e02815075590f00800804459000b8100c0d24000c03400c1c60085055048084464681050320710450918040c80c040c881801d0380a5690500381ea140702a6046035901f0340310305403410700c02200d001c580c04c5400d1040804888110000706103e5140051103034848111250600d00480c09001e05001e9900100c202e50b180d5030980307030401030004284101300091081d60b019584c0400300150f4507150600641008004a5098804110240321054140c40b09603084510b42503401d219203007809200d0240d55 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 228185053 1250 228183803 228183811
    0x1c0303061502030909060916050c0a0807140606060316050d0b130608070b030c1b030412150506030106030308060105070f0b1f0f06020a0210031e1a0102060906040209 73
    0x1a000c0340055440300401003020a48141c0c400503000001d0164603070500c178903d15007043e03056500703010310300e01700d40040c1d940300c0340c01e002d501040000642540300c2d02d400c024604080703411640c6c03e03564001e2450b1842c0e038451a00c0c2060100d00401c40094850300c0d001d01034031301c80e01e0045aa2030a2146290b001c4035103900c010b80c2110361a03601c0100002e1340d1205242c8841194030010005842e504014207540350030029070241032520000c008120100c81d0340015140701c030768480a42410764044d54030b07160450003103412410031440c0c0c5032007200605c0424020003042140151007004591074440c280f5007614901c0c00003401050f11200811701552150000700a030318040d49082c1118005540c0b59080c505c02a144081d040b0000c0601e40828504241040000d060807441018900e150100181d01c82d02c8081001e44100c0b80300700080c40840c040e410038142d40c892000e0381c43e100400204e03107070000c05903407507106c51900c215600301444d54000500d5a016803480c0e0014501ea50f100c2d0700300071950f00014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 228186303 1250 228185053 228185057
    0x2031903120915110c0d030905070305060906150316060f09090f02070b07180b031801021309060504020a170c1308010c030b01031e05090705031e010b010207051c03 72
    0x3140004034040c40c411008003900c03e0810070103051400c2c1500c0c05072000401d1400e4460010002545020340000d80c556600b4014200411808030604005083c13005660001e401c5020b44810040544000b045841c828981c44030081c041c0311500c0e0516954040d010125459a140c0709401d0024600a1021190301c07803c0389804d440c4217807250002015100c0c6a8000d4101030380100d104010069aa000d550744140680340c00c0403030b000b10501a002c1c103c0e280c842c0352500c1100001048505072405000d0200d42a0b960013955145880c20b0001c5061015218685031980381034408115843c02d402100d83c070048990b5841083c001c0c0b005100c00c07002002c2c0442003201e00030405440c007040300100301801041c0c40000040c40c04410307000030301510840b07000f445c109482e00c4400c8040122800c0c1c0070007452a4940e0014140d5588565946402c401c3c5d000302e54948242101c1c0d07400800d030030140030100c0c0701d110001d0290340340c440010b9030303500c500c1d0158581c00010143c0c4aaa0301614600c1c80103814024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 228187553 1250 228186303 228186317
    0x1519030b04180c050a0e0402220902040c0816030606021506060405280803070b2818020411030603190309091a030d0e0619140c060108070e0402031903 66
    0x380e00c1480b5500c0c1c104a4004101c41c00c01c04c1030340341400f58000140504401d030f40140c0341a5000030b03c0c4614000b0400c071540040854030503210380c035510041c1c1e0242c0c00b5100304405403131810f000e4801441214014400344086444400192107401410101c6042c0e40080c8803102440c101020b00150040150303810160611002840d0f6a5811100000d100b00040d8101e00c0c00784084030160000c0b080c1c0054a4990040045100041043c0c4440313a00004900c0300318004844400403420000b080181703040c9081c01d144084aa00e0f54110755120031034400c6608016007003848020b400e80b800308940d4950701d43c03c20f5090f010025000e00117454014400e14000c0c1c00d450b00c9158603400c81d184031003000b02c0c0b64110800c49249040420018030804014140711a42444000c0060814072071640c1c03d01d0303a60410b00411060754054031074161500038460b180c80d20350003868856555000248500c1c1c84502c19101c0c000f40558a900486001e00d4010700a400070001c42048041002500c0c20200d00f00615 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 228188803 1250 228187553 228187571
    0xf0a2a0216060305010501120c021506040b04150518090a030f020f060112141c11030706020d0f0b01080103080304030309140a031e02070f0e1e040f021519030b04 71
    0x403000e00c01001c2c1000341c40c0096554101000100200f650100c0c4c40b840c6407802c160107900503000078100000c0388054440c00c0d040e0362034901007009030400c20001600a42021802190400c012902c002910416902c02c9041c08110403800311345030003500c5034a165005440b034403022034810100c84c6494a118011030b0101c0b06440105c1e80342c54026403210100901d46641c0c1000c10488840c84e54800003000010f04207100100d8139101c49065030380d00e04051003088550003146000c18029256220340204086448552a0980f5030240c1043c51081f80351502d4090080f14640c0141c040c181a2a008600349003036944540e000d60003011145000c0d03440074601c00b01822501c00400500e108203129a03906000c410114001440c4501d00080180640d0040c8905124900042c0c00307410444105048601c0c56442d1881c250902190102190041040d014208000d21a15461410032140709490f0341201d40b00001e81e1322194020321700856001040750b00e003da0a5840f0303811510407184024000030702114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 228190053 1250 228188803 228188833
    0x4140d0305130e090c040515040b0a090e0c090117031b012a0305070302030c160204090204050f01030b010e0105060a120b060c01091401061d09010b090f0f0a2a02 71
    0x1d4550f2066200d240c256080050400c028004d9100f01807007583c081c04541007411001400c00c8200082d140600e9448044c094150303918003c140c010306842000704610038080160303946840c1420074690080c0c88403400011203205000c030101052425002030b6044c2a111400405c0480b030101e290f10607503491344080c3c6601d50480c0c2800e43c41a00c49141c200e802c801c0c65a01800b5100f008080c1d1041c0740c414800c0044100c40b4204131380f10f01c01c810b0400840002d9a20004008104c3c002d0080c0d0402c4c0f4050411003201e0281821078140c90050b01c83d410660307170741d142400c4122824001d00390080001c2c0f00d00c1240602601c4050701e42156450045640c80b96040403c1040c0c000e480707400003c4c1e46070782e03030b000900c0784100301c02e42403004250003448036030b05150311810003454410815200324140c00010764042420740c0541d1070038000030405a80703810062300281c01200300740d402079130b034032135800101d45640124441c0c030f001c1c070445074804140c90403013400301d0154010014100c801e500800004181c014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 228191303 1250 228190053 228190087
    0x1003120509010f0e1e0301021918172802090903130f0f05010f051207170f06010804080a2d1e020a080306010c06020c0a050d0504140d0305 61
    0x414556500350301d411204000501d408012120381e000d00001c15034001c000d40315500c4083c007510340307484204103001c08580441d0080c0b28903400e01001807e1b40103800c2d44a0383c06060800482082491200c146490700c3e804a00310491000b102035a42c06482c882c01d0900c1c0ea1100440725860729400104000080e40119584c048100e5403101280c00000300d40d000444505801c0c03001e815404407400041d4100300280e4504825401640d040c0100d441240504d94490400c03103c2d940a29200c01c00281040040501b0181c0904140c4400310321090009413603584071140c0900c60345050b5550030150b155a10740c101c1503032208512208010711803ca4415000301c1a07100e9580e488007040d912400c1c001010014036036211a80400185882a5281e140d2240e0005080003c141c0043c500c13a0380c1d445680040c2d55810f01500010401400480e07443d8180350003003a0b440a080c000c005850f1708040008044031188100e020f01200c002c5e20540d1408207082107421202c0c82446400c14520384000c08540311805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 228192553 1250 228191303 228191333
    0x12030c120417030a051b130b0306270609070e1011030910090f060e03060a02090d020a03080d06050a0f1809170d141303030506010909050106090602010b0a08070b031003 74
    0x41615042401010f0480134906542c81b1580900e0600f031090100c21281119034501c45d440300704a0101c0454002e0751410b031210800d95420205203400d0344a0841d00014007022030344240304518002c0010805ca0003088007150b8654024850b078555044d90105581842c11100101d2a41c84144a41505500d40b508104942811900c2c0c502c842e40c5459820344c075400e0320303802c22400c10818806c1011140c40020f0100e801050b051409603c608481d00481c403021604231001c0d512840c0d0031400814000f001c0001c1c4110700340103030184800c42d140ca0030701041c800c032840382e10840c601c411301c208625402c03924507000c400c4150384040344005203600c4041c03240c4a030300710307900003000c1c0069075012a001030b206541144440144035095454440a455400c10007008003505140c2c5460001302c2e10303032003030a40d03902501c0714900401c110350711064000c1c4118000e01034400550f01c1d00c00015500e01e0545104800c40d851a00206030a5050050a010b5908054180801d4002154000c4005900920b40c1554 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 228193803 1250 228192553 228192571
    0x60702010e0f010b090105090a18032006040210030903020c030105010306061706040b0604020f0c0f01060602010b0303120103031b1416050414040209070c0c080109030212030c12041703 81
    0x80c1c0e034120031441c1c02c0841e02c9040d922583c1c94070241c0c00e1161100802d10b81100c1086501c4030079651584107003030140c480c40d00c00070b0340c1145007194482050341140c00460310100c0c00e200020110000102c0c0b41c1d4440c010b8030f010f503000b058159039600302442a0806e03c0000e20920641e042d1600c0e80300403d094403402c2e0412a82c194a80500307020a01c03005d08a100f0502c0600c00810f01030600341c966501035100506854092034002501c88201c9071703004200e030032000034a0200c030f00b0204601d04c2d0034001c00b000d005200043d420003581c0441440d00200384c2d0b100380040c0220303281c2c1da442c40c0d4054640c82d0080030003410100f0001001c80c080b4400c425008040e81ca0140030b050900ca46c098018000b01450b00500e10540c40c0c2100d400c04141c42d13407102a48a50706860039134030f41d140c652041e208a00b00c640020001c1d002100d000c0b4101006401800345103100e5004c03142003071051888a0013078001140e4407606003406111407946200940709084d0014003c0041c042400d003d2050a40aa17100710342040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 228195053 1250 228193803 228193811
    0x15061205132a171c0c030c020d0210090f0503070501120f060806040b094c020403110a060309150908040306050a0212010611031218010501080d1d090f10030506070201 73
    0x1036861028030000c454a40b484c8031900741c131048030a028000d20800e980150400200e54049811510707a20700902000f030300200540c3e443c145248000b0030704c0309140194510080e1252000a00e41070000c2c0c11000e070795058503000300703c0000c0d8825900512149013580100707a100c1e8030000d1440400e100403030146014040c800810b183c03090300319242c05450448410b5120390403401600c0d1b02031803000261007034004046160700440b1804981010044110a01b000f903100060000c01c0116091483c0030b413000c1603911a8250783e445c1025411120031290143c80395403e00121031441c1810b50000e4015403142d040380c3d0a00d5201c1e112642200c00495003080c40a40c0000c0385000051605603103801030182e40307404220340604a1003651a402100301c9819041d1000c0c01003001c24a01161201110192200070401503a55019032580c40c201140c682e80410408014001450402082854031a074003610118030741d26594416000c4000c01080d5403600301300a54080000b540034405a8041c522550000c0307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 228196303 1250 228195053 228195089
    0x30a020712022406060301291620060306100207030609081803120f0a120c0903170301030b06010c02030115030348080d15061205132a 59
    0x40801d180b903d0300345821001c1041004000d5548408580c1907800c0d03218480d640c000402d011a100d603001000e070810380341c070110343c24561001c00701d088004180260014060600341c06a408004c00c410b25400381c00c0b00d01040096020f080600012202840c41e00c111110399550307480350320840700d1901040352032020000d901008140c6003001d500e0000b000300c0c0941116110701c4100c2c0340a114100c040b105511000c168403651a0041c503401303040420380d52080c410380480000080c00304240340021610034019034038042c1d00320482d0f070640e416030b40d00c060040003545071140151134090140c2030807039040d900c807080c04030a10202e0402600075480b0307855000000149449110300c4c4400b98000c03515070003030030b100300c010000c45420500240410740980904100b007820324424500c1400000d05440e820801d50306c2948501440e04811220305a6514002e401481004c1d01a02c10a0b5640c085155030345041d503000c10700364408003800c20742e04100e000162009080ba14214a0280d0041d545181000555 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 228197553 1250 228196303 228196333
    0xa0c02040b03010507021b0f060d0501090606020615090c071b0501120e06040b090a05060c0a090609030201021b040605040c021b09070804031404031713050a05030a08030a02071202 79
    0x356141e10110001e020920b010900259104401240c0c50101c1c076030300782500c0c06a218a95444e1405e80013030074041c0d40d580c0044900010b0a02031080340d01d0240b40903000100386101140160040200060300c02c1c1c200b240138100200040060008072040c2d00811107440014102d500082100f4440340c58181124a030800240c5a8240c1280440351a03060403c03c044c183c02c04959180d1007a480410714205889100368645401c1c6a000c00030b205100b8501132050b00c02c04400a025080c549980e01c2c943c417030719100221003003051840000d000d030f400882d0381440303165845450160b9480161002410380d07a41e078001400e50710300008c03882c00741c0c11400310500114100f10b16400d541d40c0c150b41070350041c281b4040080c40280001d20140400c410300f6244483d96071070300c04841c01107403c44a40003202004000801603940406c6143d20003008417000014641000e207070020490340014050708000e1402c0d1588100e580c401000e444032190300b0460400082ca125080100d4040c0c241d0040200e03900494103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 228198803 1250 228197553 228197561
    0x60a0c0203060a1509020c0c12030408060606070201050a0518040f14010f080a1202010908031501020d020a0305030a020a12180c09090213090318080319080606220b0a0c0204 76
    0xf85000ca03804d0050707a030702140ca030480e4042252490100142c1d034412054001c1e05124000300072660041e00521030b0701455000001400903074000206846603500d80b501004094419404004c3c04220140403c080a81c0502c0180406448600410000043d400002400c40e000c0e227a0340c80c0ca560303407259000c041d0b0318412445030140c1a54a4500c1080c0c3c14991081d907038040100004060f0034444210010162007900410ba44a91181a5030388902b0309a00f540d003618000b81e111780c018414246d040c810f17140b00003080f04036107806032911032440c1c40b4002c800700a07510043c901000e125011b582454a0542442241200c8400d4603299035001024580140c4c01506680310400d03082c10401c0780b80140e61901d9002e0941a0303160781c009801031642c03500b07907550110b440720802c1c9103d51510001e00c008012005000c0d07541c10030321a0b00340740709001c419240840155140741c5c01180074812001112161011940035071218400c406083c1d680b64034245080d404000d4907000130b40e01220441c2142800e0103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 228200053 1250 228198803 228198811
    0xa0b04050709141005060f0d1503290103061505030321060d030207090203040204060803210901021305060a0201020f0f040609060815090408190c0203070806041a070e060a0c020306 79
    0x4400f4203015113180c0910740b060055078890100001e08406400100d0202d07014100522030a000c2c1305441c1c80c0204007110680320a03182002d004004101004441c1c04182c84109000c4100741980d0a503204e4100a00c5258400340f00440314081c04225554108041c0c0401c54000c0c043c0141c00310009510a4204400b401e52030090b150840d4410000340c01160342c0003510646000107807256614000034004e040c19a02c62042804001386082a042e42d03a210903140b00354450142c04141c032201003182c201c2c0705103008103200701110300c403d0080d40740c054010040c00b01d00e480091f0400340040c8500c17445900c110140b03540802c0c00181002090741100c00340c4000c15542c10484001e01e40b102c02d50f01e4245e8551950351084004000250801450209071110a0240c4502e00e0000c0e44902c0d01400200100700c090b0b100384504900000c0071500024180d110300c0c1c1c0800382200e54411282600030118000e0074030030900030002d0a180041d103840d800341003200a070756141066043d40c1d0061504060020b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 228201303 1250 228200053 228200081
    0xc0a0b040305030307050c01060f0303030f0b06030606070204050406020f0c0d0207090908030a09030909020406051809090d12020918180d090501050a0c050613120305061e030a0b04050709 82
    0x48401c01c0400d10201c282c80c2d001400e420003035a20540607025074010502504189a98480c0c00070100c24558960f00c00d14039114884070070486080c1001c01c00055010445c4c000741d10203000c0100ca0f0041c280342c0c00c4190403a21441c1d0141c24108640114041d5030050302200d4003691201d0701302c0000b01c1c0e041000b5001407040140404c10745501c1e484840107403000402c2c44c4000303500d80b005181010301c40c03140a0020509960b00f1074480d43c8821004015900500700c81c080d82c1c412020b41c420307510b0b000001c00c1c015a5102c00500001d08442020b03541500e80d50450391002e503080c081c100c050345400c000c52101c04543c0203400881c2ca003401c90350382500a0764900525981c0309800d1780d500d10740c0100000303060703c1c000d0134003030b2703c0c0c00c1503110440702e0009443c00185a40030708070078440c0200100c2c02c40400e0a01c5174843ca201c40c0300f82c600c01c508440040342c01c0741e840a01c00341c40b694020030004a103401c00c200601507540301e010603128500801e031309a800301c5881d4040c031000c110a015031310415582c04018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 228202553 1250 228201303 228201307
    0xf0a0b07021519030b0105090411040513140402041d0601081c1d0105030903041a09030118030c1509060504231204030228060c11010e0627120c0a0b 65
    0x2d2012020f05442a1189405140c0d661a00e03104a038040d40c1594010f0800500034171860344081e00c44415608240b165900458480b5243d64440c41c55001e40d08190f95010941a116a00ca408010240041140d40215411001031032286013105014203406842d4032002041c2c0010110002016019070701403410800840c00740203a0380c40710240074010000002d02c2c0280c0c0f00c3e103c880255055110319400440d080210001e0343c40301c401c01001070414210110002c02c103000ca104c102c0728101c1c400c3c2d4001000100e504a1600c00180d0102c030b11085a0103164001400440176510740f800c03180107841c15100407801445170100f403125681280103018261001d0041042c0014009850b8005d6000007449481c0c40c02000117404603c2500941d0300b405041316482071a65020040d080304001d103410f0740c10ad4120000c111040d4051203010701c642402600a03441c0c00c100c2044030340140c130404c400f030643c1e084842101e210f030765a000000c0703200c060580180032038180c540108203424020f907001096600301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 228203803 1250 228202553 228202567
    0x10603051014160e0315150a080706080c070b0c07151808161a01060908010c0c032006010b040509010504050601050a0503101d2e050409020f0a0b070215 67
    0x1030490542001c922480d078003a61a004100351020b00006400a070140320f01000781b207050300d138110303e9030040c00d44c5503901e201d81c6031030b030306020485884d0300450000b9070107204100245d900c00c602099205035092155824001c490703403048800c80040d2540004120003050020510000d14891944008100000c000c40d400c040d00101030825211030113400000b010a218001c0002112200246a40081641010401c500d0040c03034079070b828003842c1c000a41c81c041c0854088014070500019807041d884140d1003440c1d45e5811103106005005c2da2034240c080400500c51031104104440c0070b0700d0101885a11542050148070720a4416400541725600308001d100341a60020100e030f070b0b400305a191050303903591014807000302c000f069400814404109494040104044582c8034001d2903075044940d4000c0103030603c9840c1d0300349816040304e000c1c0841c408000501e02640305081041c4040c100da058145020005004060035500403080480001184811031900e0700710301c48240700f034007112810508 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 228205053 1250 228203803 228203831
    0x6060a0e06060a03140106091d0105090c0c1006060e01020c0102030412080304081306020a021309020f0909010e01180203011104140607020a08061003120c050303040602090607050d020106030510 85
    0x4020702070500800c0300055500889109800100d450100308160a0065030344580c010202d101c0c80c440e1201c000814080000b003035988110581c125800107100c11308a8450414440555110b038000d1540351007880f64128481c196801a0001070210752079a188034000c41c0c1c0007a04114842c03c040c0d045420401080c07088440c400294412aa008110703680c40356034614240e142441401c4013498481026040090015400102a04600c2c8203803030254280250200d914107643c841400258002e43d85402046c0505000c0ca80e668401080300010503501001d145a90071203500441440a58121200304020740c223090003040c40700c242800c2d040d45480d140c402d100b07600c2142d807040d00703108500000d840c5003507603a0781c480b44000d402e5650a8500710b0800900451021040f8401155011413066135403080b1409200507502c0303250400050343ca140c0e183c0c1d031000c00035030103222250790003c01070008101281040007407400089054000080d241d0a50524601d40b500b028403c0145509280b00c40801d20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 228206303 1250 228205053 228205079
    0x50d14090f03130e090316060603061112060915040905030c0106150c062d020306030c0906030a082203120201051003030905010813080d0204050a090e0703030f0903051b0306060a 78
    0x41c0071300400c14a54460901560a41c441d4414600d5184980319441d014000954031a40441c0d10502c404c01084901a05229080c086c000c00d01e107c0c03044000000304181407078102c0340d40c0010101c6107100c031040e4003000181164150a0103031039a0313101140700319403c0000d1052070702a0000c0100c2c19841500b4100040164801e07070401004241c0f40c0e0519003a1200440324042070340c541003201031580c1070483e191002900126050352091082c1d42134204541030030364030103006000c0903014001c03100280d00c0e181e07150380c0034403e8000000088040000ca43e001c551545008c0c40c07288049854025603c4802400d4450207484001c00082144080002a40110f01c07242102d03020708044a9641d2a40c0701c00e24001320703180000e400c038640000d02c490404010b900910990700221004240c032a240d5003448110b5541401d182c19a5118842c203001003070040c1c410390304580e01460b01d680c0c1d9584a035a82c504210707210b4259018020720003800b4180b03160a0040c568001c5081d50442000781c0703816007258040b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 228207553 1250 228206303 228206309
    0x2090705070f081209210414031906020a02060106030501181a040c0509010f03060f0311030a0f030305010501090b130b09060f1204020906061c0c050d14090f0313 71
    0xc84400100c100c104031401c82c500507100e4100c00196180c03680003240e0104084200e410224034000c80e030a014002d40c20301680741c0e0002640c101981840d0402c035504641c0b05a904849500d48500e1002040c540800c0365440c419510840001d80ca851300035502a103003100c103802250a060400e0014000c00720a88441001c0d1921158081600940c0408015079048080e41c0190001d0501841e42d20180d0450010502c1200a90710340300d00c240c0c240780813001c442250081c920039042c03910f4200040307901c40c0d07280e00f01c00300010181c1c1d044482980d1000d008414041c41200440d0316400104015030304440320030700410b40721241a250149520340e60b03030360001c02d0154044490f4007060180342a154002030700c000030003011400356a04200d6006c581942c400b101c00300c1c45032980c18005509400d010302543c0403541d025041c80844456074440401070401e201c0020200041888444058413441c0680200302c1c0b02c0c91842c14281c00c010704441e041001013a00090075078130412214000036604544103080b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 228208803 1250 228207553 228207557
    0x9020a051212090f0d1b1d0c090303041518060305060f1201151710090302031c181202010b0105030c2b0e060a1506050901030b0103140c071509020907 66
    0x3075140c0010004036800051010550417605140c0342a08000e4160486032080d401803005a04c07a40c0c2c4c4002c0344119404010700c40070030003078103404181072000d0240a8400caa100505890516840300d40703040d40110380c0d078940000198140040e099400c0030100c41006423805240034002407400c0000300703940285000c0c2c9030780194446039402c6641002075105400860b8100b00c3c154178190b50340c400125002c58000b0102e194010380c0c080c035544403003c1c450b05400b9a403540145040060801d0103456402c1642102131103180c403031080c0e110342d004c14200040301611408407030010864009000f800c4941a01b400380c148141001030040e1600040300352801d032060320000313840c421112030400254040196800c418142003801c0c1500da00383c041060361048042820410082507020520517160030716105050110b80c08201d50b20240d40300b41c00c408400300040c10003082c4090611200c8026880845000b10195004a200700401003400b241c001580c0c2c0090080c40a80e5040d0002900340741c0140034101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 228210053 1250 228208803 228208807
    0x408071e0c08010b151b010609090606150c021005090402030703021803060606090f040905030c010b010206160c030f1809062d062a0501060509130507050f0604030602030a09020a051212 81
    0x2500c0006c881684d0007100ca104001e01141e0303501d20403540a40180c0a003200c00c181044004181101140b2044408041c1c607a00c0814495141e020b0000e6001c103d51440100281001542e140e80c499000035409000705550059a982500a030001c80140e0a41000d121381c1002c0e043c0103e640e1030310300f0f072274040c001151541c0300e41700f0000004008103086000144039001c0130441454040041d800100d040c1000c2c3c0a0342c0c12582c5041c0f907120348003c40156000400c0000c0c1c00d20b03000c0380c429180f02e01c01c1010390038480d80c08115202088043c4100354040036060f51146000d01190418030f01030110002d01100002104001641c0316600c07500b54003030081000802e0701000f441100352140e0108058980c0250100401d0f6414014003804035030280c0360007580d07641c1c0811614071500d601084c60396007200c0a040343d50300b0041040b00d0243e2084c401603102c0400c2c0008400f103201c51000b1400b400301807100040840d4581b05000303201905e40d0040388551903489100c61503c0380454030f903901d600c87c0b62940c1c1e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 228211303 1250 228210053 228210067
    0x141b0a0216090f05090d0804030c020f1305090705040204031e0302072705061206070c050309210106050111190602071a04051b01090605030408071e0c08010b15 70
    0x1d24080030048051510062808009201e02541e400403a100c00c0c030140070710260752082c000b0740d50344040d00880720000d600e0800103008a07106035194003280c0d01c010100310447d00420f0000713521414000301c20000580e41d07400d01803101d40c1081240000c0c60242c50079130601d841d60702e07040c0d00d0004c03500c0d1140e86805148a01c0040500c00c1c4050005066500e444e03501c4203149070305029101d252410406012450000407645034a0b15034810030761510600b005204075541c2210817603070b02c000d144040ba05484280030340009966800d11086103005180b01c410400c0001481940c00c0d0703000356000d0b60502070152035060b013a00000c80d031080c801c4100c05000c1c00300303c1140740200082c418014094926680419859041050b050f0342502a9005004580403840c920020401d42c1c90541059408580c100d031080000714007030000703964042d01a401d0a0b0602c01d032603c2d00120300410300710b1100e02e418409501010031200d010ba12000d020386200030014501050081488400d107003c0c45202a600481c20f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 228212553 1250 228211303 228211307
    0x6050f0f1902031207020c150c0a05030c1b0a0501021e07120827032a0406351002030a090609060209130b06040510020a0f03080703141b0a 61
    0x81d60720780036100700300e0602155544000d460b80c10030324510b04035610a0010500444c400560119005802441c11015200074060404070340d0107240301c440c9a00810340085c000c00c6013800504450303600384015014841d9203a603a11442c1c4003409441d0721680d00c00c0d90a0110740d900044180445410f20705400c4600c1c50b50514500e804074661103480d60084007100300007003050110240298400c901c0c040100049a030003100d0f40038400a030301c203030560310011021105c1c040c0d0a8640c070152100c0c200c200d41110741d650215003034800a030040503550b414000789242019046002840e1141e41600b1203d103002e1442845840c1c5c440200301c0c0400b25000320101c0c0f100c20079580980c01c400d501c401d080080788020701e00900030350004065188118402c01e0700c2c1c0840503075030080c01b190000040a25291034101400c004001420b003c0d107800f18451114040e00081010421020140c081d031034028883c179040c44010305803a0000c3c400700410307015000788030340702d01e0881c80d494010044208030354079641100b5007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 228213803 1250 228212553 228212557
    0x3150f090f062307030c0809031602010509040209040f150602031201060f0e09041104050a02090f0405070516030507110d1e02031612060c020604080d02030406110c061f06050f0f 78
    0x150f0803500c002801880700c2d46405a0103522189060b44900c5c24580e6460703040c0c0c0e142e0103001199901000606400001584214014020010010300c014100700b80400440e00b01d03129518002d00791951110781000c25004030305240020000c5200a524003080c00c0c600c514004018030450f0700784032148121046085c0644480c2d42170801c0608010040d152a08283e85003030204144980240c2c03810001c200c20640c58021204e03544009404013148845200500c4000e1100402e08401c1046c180421501690340e42c0f01e84100c0c0e4020740da1203403a01c040e0b09001807403190020300c0600c503411151148000450311494110710030180c0040c01070f2081e1500119044c119030307641c0c2c03900105014002041b0f100d1200a01d86100380144400c102520780e0b08400d9a85100c2981c01406d044018460400d81400c540c0013158498440c4a010603107581d0b00c6000c184581150419800c65008501000700040400701c0c0d9840486803145a003840c07516016014080b132295203691200e1000016a410002e00c2c9081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 228215053 1250 228213803 228213851
    0x1021c0207050309090c07020108071121040b0408060406050c0313030f1404060c1104090528020904060c030e151816030807050708010b060f0a170103150f090f06 71
    0x545c100f840c2030820a030081c1e01010080b40800c02da500800d00c4144120030b01e000c070080c07500c0241903103c98100864035412614a07549503003c2d04110205164a2080c0078100900c03040c0001c016500f02440e05c1015580010540c1e203022105008102c1c5c9007040413039410071540c045c10702071318a03110900110b40e140c0e04004001050742c400a40081c1c81580310a450000724000c0c1640401a4400700070031007500c3c5151009005640703c8000c0312070700386040201003900003400d609102c140403603a011440e0090304440c181c1c5d056640705241d501c4141c050240a121001d2074020f490aa50013415110b80c42d000501064107801001e0280d03120010b0030440040b901c08606c408400d00c43c0e0f01c0c40d027041150f1003208200c806001d2000b0028420713205000302e105880000341154100503100d038640e5241c1d002801200200543c0d4141000700c003103103040c0300b80614040c02225410700790b10200340303043d0341625001c00300203071420069030003103020341d5010052158003090104510b10221110203544800320 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 228216303 1250 228215053 228215059
    0x309030d020f161410020f1210030c0303020601170c130b1c0804050f0a08071221030501050319020a03021c0b090a020108100e0615160305040f050301021c0207050309 73
    0x21001403001d0440c844c0860300810702211251301c03609050318240e0140701051070f00050288009100105542052580090031019240d201ea50700c0d2200340429405a0003507025810580061001d259149035207610000e00c0070040c10409034000108440e041958440322080b1340c0da51f030402041d90380040741043c8420402d00352041743c0c02410080303095405440f8491044a03501c545640310f00700f0602030b204035200702014201c3d480c6020342203d107680b4000821600030186001840640b40307030b19000156440b1030f41c3c000510390b040074107040c81c0880c40b50480c0c084c1285042c1c40c2006a448054240a807a1f06846081c015180006911101c90340710b54020201c0c4403031410481002d000107040c064442c000d82c0c4c0c0e000036448078011880c1a00440c09084060401c0c40c0020b0400d0521000607908444056100c51a11101032210500d442c54481c040300000c4000504015003083c56040e031000c1c02085008510380f800100d20746100561031a4540702c4c03641c0108406040c0702052094500c400005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 228217553 1250 228216303 228216337
    0x1e0709050123090316090f09080703030903020a1e02120f0309060d02040510020a030305011e0306050717070e090108071514160308250503181c03021c020309030d020f 73
    0x2264201041011707030003405545480c2c0010803001800c18011403001d242c114030310074a050303c0303a20108c0151a510300150300754403a03034068500003998854030b07005a10b0441c246404d0030035181304005820441400200043d403181c8440500c80002000f1181c15000031100c481da140764240c5a1400b1340074942c032403030b4070251001040100e190086075007151244640e07010000342e03032128008a004141c242e020301d41c40c24051800e200146950340100c0e040b19950400d07000c81040c06002d203039036003421030300f41c00016240d64900355241081b802540c09800e454000c0c100d01801d103000c0d5001d841c0344090a08c108052103507041030640d05c00084603028040b003040150024010b04014120354000e8440540c0c00c2c0d040c03c80070360351014a40940c1840101c5079a090310b19143d5a2130660041c4040003106118003908501420401d6a4114001c02c01c249840260301e070510010004030b080454a0313580e03e000d00400c1004a44100401100e16011601c000183c9a020a0700300e41d200d40a59412403002d000c030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 228218803 1250 228217553 228217573
    0x904081912050a061701060602030f2101170c061608030612011503030f03020c0c130204050310090c150e010309230f06010504061a090f091e07090501230903 69
    0xd95000304c2d00340c0d0300241401e25003601d1844010300b00e511a2041100503007050043d614007000010080180c114141010031140f01a01c1c1d6820f80d8190030381c404403007812000c84d440c2c0a41c400340f140c241c0c2c0308411240641401003c02503462400d1098100405200b030000005002c0e9483c01c070000c030114880c80081120392801410710005080500095000c2142c0d0140d01451354800d008541d010740441e80549440c0b8100000d011300c0d02804106241c0594003440080707480d880400c001407412a419101240220440c1010111100c1541005021035050030111000a40042d168800c2d07502c28a80016030107035030300700310791560300004c05c001b10300368541154041e02c200010b80000341d2040c4001da55060b640c1e07070100401c6441750b100b407007045080e0007181c160003410140030745050007010300305103940501c00c400200c041008031194100703020028171703080707440500421060b0702900c581815100c0b541840c001900307800c01c1c10009030500110310b43e440d91580196003505d02242000d401c40e80100c1e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 228220053 1250 228218803 228218821
    0x3040203160914060a0605120903160b0105120304120b10030b1e07030605031002130803070b010305100b0d02060904110c010606020f06100e040c0b12090c090408191205 74
    0xc0c0d03030340d00f00d642e0700f07001011903210310341400341e00101d90194031031600d4400c800400c3c1d45039050051035000140014001000f00d55201d0480620407881400076031229030500d010000200d040700341ca004c20303a00a000920002804d91551a03031141c00c409100b030782d40e88a8600142c0501c15410040c00c0b028400c0921101140c041c21044080c141102030802d0750341d490a003101121722600c00d0903415401440014144c50096000b0072102c6c0554181e044041e89988030140b46503c06d030000c0301c00b080200010018010107120102a000c1c100c0360500c0034a1048001400c80c416098000c1d206840000340c07201d02da55560300007024a049240040c0d12468440e000345c1c02050700d803241c100580a4040ca07a6007411020403918420007000900400450415020740e8804c0c0d0010b20807115601000d5022413048003c00191581e0040c01241840c80c1ca000036030a0300b00300c03058060500400d403820601c000540510240e0b910f02040303044250130b8907000c5804031005624004400350091500c8280310b0414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 228221303 1250 228220053 228220061
    0x405150d020d0b0f042007030212160201110c032107061109120106080a03080c040b040b04050406150801030b19180b0105060f070312020705010c0804050606120a0206030402031609 79
    0x3c41e04403071261407a0502d40500080d150400490000ea60359081c4043d02c0090280107040c0042c06841202c0812440385400d100300d91201000e582c440c402031901004540e4020618000e005100002d400380405034070100c0c2e510010910069080201203c1c0d5a648441c910155124580c220a041c41014102d440f0f100702e0350303c06c41105025005070301004006800501822045500700c0004010319401618200d6982c1405080c000c40765000704800a202d2712620058005040d0891410356070303d140000b04400c8518a5100868021000c0580d240c0503800080d40750443c1c2d001510041141d481600c2140c000306440c00c02c0102902c0c3c00002c01100e10815a80c41c0c031644104440c01caa80d89400420210b4042c01510382e0f083c2104001103030029120355807034070b0500e010640250410b0100d6498509540d240303480c110003ea0010b04020074428200305068200d44c040c5e400c5030404480004581d01d8060341807000c0e002d8400003002c2800c54504001203141c444402c51180070807901d5014500c050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 228222553 1250 228221303 228221321
    0xe0411070f030909020c0c091e0411030d110c040c02011808030103021002010209150702030106031707030f081302041104050612010602061e0708090f1f0f0905030405150d020d 77
    0x614403540802ca480031317482100c030541414001091404e851004025100c42c009202c085003000403480c1005828034504824003551145240c0720500c1d450505161414030b10081040412a03c45404a1000c03400700f058080d0300b070706482c0420301c0e080789a01640542031902d0018003400782c80c1c42035001c0c0f1440da405941079a08c00c0710f1240009041c072138100e091740a11a40035a2065841032142e6040c040c840003004c1089c4040c0000c0f420036581d0300e40c0407003041c41110070001901d00243d042d003010f0f8003455842c55404181040d5a05017440301090b00b40c00340600009006070742c1e500004100000c20030030b440007080c005210503a074032811500c2c603200900030300c2144054494800415182d050a40d40e0460400c00d06405c02c440f9036070b40c04101e4000c1c101410917080d0303000341d141d00e8203038078010301401c492103031141940000c00b6802440a404c40e0070443e11007962902e8030841030005480031080724100c8200315803448000701e9a010003807136031142121000020344009054100e0307010540080b03001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 228223803 1250 228222553 228222557
    0x30901020f01051b03090c090f04060b1002030a11070e0103120206011406030f06130c0f0e0d0203060c1e04030b060f0108040510020a140d05101d070e0411070f03 71
    0xe041404100d8500303031801a507040484241850003410384c5041080516400500c103800c480030004407070041602d0001c280d0740340480c2100c0504010600c1054013412a0008058900d641029250800203440e4040c42614104200181d0b0034150310312001c0007100c2c06409180150036103543c4d6890400004075048003240050301400c00000307007000703400c2d200b07415502000e400d85180d030f5500d03020700c0d602c0d640c010403240c4e214403428076560048070580b2402d51000400d450b5400031f509121005454000311000d8688180c0040b80c1a50050302c0114146400400e031070141611580c1d42004000e41a00c04031003500300000c081400002c1c8030010901c90300440d4152005002044545e00450704150112005030141d40034002200200c0a0755008101c0800c0e46d240c40f555943c1d40c58110301903036101e03c60003404181c45d607060000110030418500d0003005e0030052120f4a84640d2002004188000c2640b014000d0307108076820b00d611550092082080c580310700d2640c4003000c0c40c00c40300c00d800500b010f0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 228225053 1250 228223803 228223813
    0x1030608070e040210050c0d09090b10050d05041112070603140403021b0415030609060c050702030706032417010b03030421060b150307020f0304031707051c0203090102 74
    0x250019001c55810199150081071840903583c50b000d00c141086210308280402804104d08101450300b4480d05d40350866036507558250a1401c4c0c0361801307a030601000c3c60310440420710b0641c0d20903085011940411140900440c045d50f40b410302072034640704440d00903044481406068100c1d20003103210001e4551685040044000c1003400e0350000f0402c46004002d41e0006074803001f0b0000000490303e20300001800030030341e400e107040b00318018007081c2d0049a0440d01c4041100400001e40507820000400f46000e070304243c010380001e42d50380005e103d1710090550710808050030b000b0045d4200c000c4000410310603003080d07031840010891300078088981010752174031955861600d008011582110b0042d00091900040c03804041034851400404541c0503503506402076054903a001c000001c6000e00050350b8891500c810064240458501c46400d0380d00100010700029140c4e82101017261107104206488008900d41589803005040895042da00244030740c3c422141e000000304007040c07081c0d003560 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 228226303 1250 228225053 228225059
    0x6080307150e0105010317030a0b120114061023040509181501030312020a020a0512070515090a084005031501151202121005061c0f140c09010306 64
    0xf42210f8084c00f004081a00c0c0d0061146000504000740d134102840180c00150181c00400187c956160007a0040407079444003c45081214040d0310b40394041020f03102502865084403004000b22807400300c003142442a140603031400c1c400242518003900c0d01826200950404084001d0144809000d40780e0a1003252201d0803503451380000709040301d42c140c9070751703101d0720700a85400041c1d0005c2c2c1c90b01045101c0d2a0002e00400c400304403104007600c14000340340d5940d100b400c06901349180084441c40912441c4240f03c14003400003150300034940c120b05003079180d52b403007181141c81c85108241c06c84105100300c2c5511f0305417600419004d0160944050728a8241c1c1c98062540b11040d4a4140303000b01101c00041101c00e80c00d01d42480c0220a0780b800d1107004410071040710482e04444103d0625422107000c11829035503030414540a41011240300d410114544504038004680c0d83c0780c4071090f0b0701c07524003060040032a013018a40d25070101b514441d03440c008200d2070054019040890019080000c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 228227553 1250 228226303 228226331
    0xc05150915030901090807080a18032001091701050609070c0203070326030712060f0503100b060d02040b071e21020337050a050a080a0608030715 64
    0x4030150305010380700800c0a841d203090042550001080302074a5500c44c40c006001600e40001001514402c003401c40d15400c0e0030328010b0802c0e606480081125040640c2840420241c4401e1010314103e0054660381c4100c0d00c004036500c6000d0340c412000920303107044500e10484190400d0340b0911007a00d1010090766445021a50a01ca903e4040d400d0342250f502400410880100c0c210700c80352245c030040458540100c0c203c1c0c281c1c81290450000380442460b100f20361081d01640c4001d0a221307200c141070178100070001c0c2c1c80b82660802d4040103076403a410001241c84410039a900601010400c43d10b40341c0c1c2c2c4054081a0f40701d224121042507003480640c100300042c4142210183d00000c1034010040103800c0d0003807002c40040400f00750300c400d01c070701280600c8104650101c1c242d20f1403644040008508a519a8179902200b50300344001400469010b903400350946160a042c0d140014640e2280007440300141503640159a042c00b000402d1810710900282c2004020707800d034001c1042e06810510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 228228803 1250 228227553 228227557
    0xc030706050702042a050307030b030312151f090f0b0f071412130602101b0c06060308131a03040201020a11180f0a1a0f01050a17040c0515 61
    0x1411001c1441802524090304061781700c540a9540c445000d0071903011011305030f120f080515000c00c0041c3c0b0000030044030991500412002500980c0150700303200d2202401115414010300359a20004601e404050950b036090400d0400c0c41c0c020401c400303140035010000c00103c100e0040035040040d0800015441e1200001c440b9000c12108400c0c4c2001c2456541407148130b802080a607030382c0305400c3c0c2c042d2201513900043c140305002480c40032250340707417200c01307400e0014005105008915290205942001003034031248460303404d01c1c10b21051403240ca040e1005045e41c0e00058151702c00841c1c0321441c88032241010007610170b9202e030b000020900590f80c0740244001c1b90f00a00627040340141100140d0741001286030700c039005080180e0409015038544200340200c0d07490007200d00726400c0c0a40640a8490a806008643c220300721411444010403058000c100c40c0e24100240001c40700c880c0707131040c21040c0711024000740d00318503400d0508080b0800a081c2c003459129200000c3e500f505170900c001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 228230053 1250 228228803 228228809
    0xc0807360519050c03070801090203070f0e01020a060e011a030a03090e15130b040b060711120109080a0509150412020d050c03070305010203040c120209011502010f05180c0307 77
    0x21204400c601424084000351074003500c244412214440310b000344481d03900030340713126030400544181c603894010401801d120040c1e000c0042c8610420a2280159000e12041d2910055003441400c030805a00101d10f07210810078050100d6181012a010902064101303043d1a440c1034a40c004c0303020b002c01050740310a406c46004010030100c0c5030402038000c4004101e42d101d055285080300d41d50100001c100c0c800d4060003050489641c0304040310300c0c0c0c41e1502c034008111209a410a08002040d03030703030507030388010300c100c080c41620700310441f0140e60425004913201a500c2a4102d8031640961009807207030700802a0144600006c800d20703020380c800841601c003202d00e00c0040c031f00002641d40a0045580c8122070950b0a402004c2c546400e42c3c50421a0340011441000010ba90703180c05d0818104546054000d0380c0089480410040036983c1c19034210b05440e04154104d00012903100260f005003006c00c0c1c41b0104504020420403104100b01d60b519551204201340c0e0008a150700405441c1c40140c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 228231303 1250 228230053 228230129
    0x80f0a0c060504080601170109080c0606090c030105130905011b0c0b07170c0304050a06050c0403030e0a060c03050f09040504110102010509011e0b01090e040807050d030b01020d08130c0807 83
    0x40d004001b8602c47d002a000400540400040c0110031038442c58000c2c6d1000c843c0c0410307036000b001030000c5410700800325641311030380070760440c1194144000a001c2e840c10001001c181500c0b0035604080c00000e6200140902150300d450244550740301c030140100304610003e0716010805000901230f107000d075140c81c0c1109036800c082030740c5a5603644d00b5030389500003a1090750036118840c4e00c04002001c600c02c40d801541c0800708140ca8510b18a0020701e6140008416409124560340c2004101d030008425801c81e0341c50b0522a40340e0301d00c0c16075040c0e64000e00f01c0542c0c0c054101003c6c0001e01007004407140190070280d009000c1f507920381e00700d1403c0c0e60f43d4036110900c0c4922a680ca2030480b184c0c0c0c0c4071203040c00c0c05140c5254001d5907500440c00022080c0e406541a200010300442004400c2206031010b15040c01d0910140d805080007075261083c400d480000d0203a81000a803d0900307500701c60109950045604412a841d41c02e0f8551f50655030103461501600c042050300003500802c8681d5010181e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 228232553 1250 228231303 228231313
    0x18090804170309040c020105011502070302060a140712092d170304030b0a061508130602030406020f030f0a0608010e0a02060c150703020903100504030e09040804080f0a0c06050408 79
    0x140241e10540e080d1201180140003e004482080c3d8a5029400000042c0d90010806506001e0320b54641040b00310f460007035511031801000141c03188419107010742d0030f030708200002c050a203a00c02a2440380703030b00050180d1a140c0900c40c40c582c000d00100d09640e0740c14400d00c030000400040c6902402c0b0200e850846408a480030840070f200c114061001003141d8003501d0401c0e550b07949181c090f00c0140c13040101c0c00e44403241889280802002c2410607103080c9080707070785400c04140050f4005400d0001a003641d80000000e000d21440b501103a505144101290b5032301d1901440f40300a881051b100700e00c00c0d5080c8400003600345414013030054244440805400085101e03802c00a042e07101c01412101401040c1000300240c0c4210100c620071006501c015942c0c02c0040304041c1054412003040e8007143c601408d01c000f05c0e90264a043c604038040d16950a0794540e8144800c8500965000d078032640700d2012540f0810f4000304092506900c910303c0149800d44038401a01c3c0c0b4000c0f03004080c855401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 228233803 1250 228232553 228232559
    0x160e090c0a0b0d0509160608011503090803070c0c030803090309180606040608060d0b04080304060507020303100504020717040b0405040608060f06060d061505030403170405100207030203090a030b0118090804 91
    0x513405540c010819a0450701c50300745000d080e90b200e41c841e5100c01f011900b0140100144078280e0b08049600740149000c1020400396038035103202d07000180420701001410b000c4c1c0020840c03c0803c031b0020b15000001c0303603128908411001e0342c0780e1010307000d24024814030705041440680f55180317902842d80140a0360501e818040125075103034000b0040d6030300c2007600e6084030105010464080c016402428096901d1a02e0304000090f03032401f40440c821580300300700b00306000e2040441002550b5040300c01698a40e60350500c91641014090190780b22040001d000a00012080c01030007203510590b003d00590b81c1d107503800d40d1180e600b1103140c0f60100d800e8000401d240392180007072a0044101c0c5d80020407544510040100940131600e00000c0b540010600091580040254144000c050060b541c2480d05955040c0c907040711100d07100b00550085243c1c0304242c000c0c01031300d41e800c3d00a0440c06880750b1b0381c2840076081400b8415030000c3c8882da4042c0c1950b1285000301040c494114050925180c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 228235053 1250 228233803 228233827
    0x2010c0210091104091101081602070311060c0607080114031f020705030d09110109150905090711010905010b040c1b080f12090d08061917160e090c0a0b 67
    0x20882d04101c4040151940c000202da0b1a442034a6960b070080b1417110041600c0c070009440e402d00031b004022103490035000c1d1005140d00040307401c02e0306c0d8001541c084003160840400d0142c000e01c80d2164583c0600000c1140c00c03680409800d049410300c8400c03c0458001070280342e1142c2c0724004800743c204007800c0131100b28090341c0081000a00c0740c81180d00c1d0000f1080c0450480700d080c42e04030758404500307026500030343c2d04c824090050300350070f07411440b031402000000e4552112885494000d400c2c10000803010780c0500004010f9004484c000e200b44a51490145e0013031580d003010a11692620300c80060a80c0308140032030320b5940d080c0c4c030f05111b48099100c0e1115600007a0700d4101e502002c002041548810f044000d009005000040445178412200030b8020302009040c0e40c0940c3c22200b040000c1310b0700000800c01c40ba180099001c40450500445090085000805805440c01900005d407020309419840c413408140055030400429401040015031140c4030700b00002702d040c064407580c1d071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 228236303 1250 228235053 228235061
    0x30b100809120f0919031406040303140702030a030c0e040c0810080c030303041707081606060501020f030702040504020f030303070c030306050f060f090a0e1003030207050d2d060603140d02010c0210 87
    0x40380d030400300c850b2035500c0e0b690303014100518031f114102c0d070010420302040540500950408585000c940e40080c506440c00a69900452440d401050b803900030303c442d42401121030aa032501c01400c103200c0c881c200701e0050907505007030b82c24031024507180400080740707500410b0281c035250004024604c1d50b141c0c1d44404104d10130294400d600c8440401880d00040c1c407a0008080c11020241036107005082400c24070100d0301158449410341d044a80c4030044464080116101e040d41104c1c0044c0c01d4880d400402d903900088455140c151000100380000a03803c00010f141280c07003030350140100c54a400901007135001014001c0c0d00501c0c1844800041051034001d400d01000280540c2102669030181c42c240c62001e03a2910218000e0807824020b1680c107110200182406440000101d0420b40d554010b061a0002c10030b0504808043d42040f05190182c0c0d034031050f0070840030320409459003003500d0f0f003003158500440f09200b48031980717400a006010306007200da03041d000b0b072682503090340e5401c0140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 228237410 1107 228236303 228236329
    0x91a01020a11040906090206070809101e0c060e06010b04051005040e040816060e2a01080a0203070507021e040b0108010b0406050a030b100809120f09 66
    0x82000c1409080c2e0398032040d940001c0000c01801c01030300810303152200039405140050b5420a002c4000080c02040c0780480b103040d1894880081550081e07100c042ea940d1401c1400e0103401c0142c01142e50341c0b4030303500820000c50008405480c2ca420040260803809208801140920040c28240820f690b4082541403203071800c2c0c2002c6c4060021000140020214000029200001401c0850001460354005401c0c44090510f03e55030391a00c10024407483c885e5920100c241090780390102d0340d20b00b0039060b124400c1c40d07258807150300080e5000505050a104040120400503205d5030340d0100031007800030302d068006405600b0031080d6646011401d0402a07210014465008034070700300d40483d092818290f5498814040680140800b540080d602c00480d0110081242d0040345d428428940c020030303200c45141e0400c9000700303806025051003612070140030304400ca0030118800212 = true := by decide +kernel

theorem cover : BRFrame.Cov 228057553 228237410 := by
  have h0 := BRFrame.cov_init 228057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 228057553 ≤ n) (h2 : n < 228237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
