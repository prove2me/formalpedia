-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1202
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:44:33.443374+00:00
-- url     : https://prove2.me/submissions/930628f3-05da-4d66-8fab-7183e66e9740

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 216007194 ≤ n < 216187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 216008444 1250 216007194 216007217
    0xb07030c14060c09130c0f14040e070c12021b0906010314070306140409050309090c041e0302040506010c050a03031a041103070e2b030c0602070303060801051303 71
    0x108115441032280101001000030360a50202070500b4000d6500c1004071000045000903400c00030402524180440b100304220580403101608510000720f911041001c114814030000d00550141c80103400c0c4510080c94074a0072440290044103812015620b00707480c42c80c40c4d40c049100140c19040907108022000b0350040100030700007260405084541850b0b1242c41e541030b5100d8900101d40318104541d03000c91182d10b0a2170340d02d020111203207024011030901c034819000c2500003088a90364141520300406a54403000303035048500580d00f1020f804000c0311244001141d41c00c240d04140d90084604010a4a4600054542c0607040c03034002c0c04c40c0c0010381e01d1300c0402d009611075482e003404810304501805400c00000c0840713501070400240c280000c018414055400502c810a01d01c2c296882c03002d4900410407201180659406402418881140d0b81304040c8945c88102c0070a078000e402799126601460050b019001500988481c0d45c680350001c2c0050321014030101917640c258a89000041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 216009694 1250 216008444 216008447
    0x70911091c11090a060504020d090308060a03051504031b050706090f060816030209060f12070f020303040b0601050405060403120f32090303040807140604030c060e0a150507060b0a0b0703 82
    0x90002c010403107131592280001007903101d078001403821407412580000d907652503203805000d60802810343d5004800307098040c0f0002350700042c0801d0813000c0007103410701d0350381e50700c0c1c11246490141f400112103003049809808020740011401d0689910b40c41d01483d0544412045942c01590710400c00000e40745c0c000309100b5150410b10407014030703c2d45009442c00001c80301113840c0e80d210704015003180c140000c2c8450200b01210010750020080c3c5005181064a90070095590002400240401d00c081011400c0c51780504103c4006000162600f512640d407030601552002d80c01d500034001c11241c2484102e240c1c800c81c0030840c400540001150080c40c46a44000d030450002d50034403071540d04001401c8581d1701000540001d022100c000e241c43e50902a0401c04420b4120145001d944148810300004940301528400c1e11411f00d041e256072459100003c44281659001c10740a90142d505802810782c400014001540264800d0100403080000e00c8529070b658412a06d400e5028440742d00002d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 216010944 1250 216009694 216009709
    0xb15010f031a04061202091305061f0f06050705010506030a0804060c0203030403020d05010209130b1f0c140322030206070201030504080409021201091b081602070911091c11 76
    0x1c82d00d090007485032031801e40400c04540c0190400c1d240b50396466840011460f005920300e600c9288410030101080da55500c0d03c5d03a481d4040c1000c8881030f00d101564800d040d42c800144020040000a0060340350b0351800542544d0007840140c1c1c0700c1d42800e0003d611424002a0600400d5000200d070745450315101040714000d0200904aa041c001040000096a52400e03501c0c070540c0203c0c0016a45ca024100b00708450310380c4031b610008141828540011070340d40d40381c024102c21301d8480c1c2ca4070008207410102e03940e000e4100000c21b10007602000b04e18501001024085402107005d80449664100c0c0815066091710300c8000c7d070000e01002180c0c01540309810003900240b14260044c2043c9d16a48420700b80d03001203c039200c5c0a04581c0c0100460b414502581901c00070701880400d09650f401130042c1000340040048024448502c1409600303403080054100400421104014511262240c010f603548000c1c261846a800c000c400101c4900b240000104a03503c2200c1041e4409080140080d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 216012194 1250 216010944 216010961
    0x60108090c0d08040501030e390402190807020c1f030207050f0a030938090a060e240d05040303060909030503100806090a021c0515040b15010f03 64
    0xd0003a1072041038103407241c0703003400c014620400318240c03034500b071400042c200c4481040a44a40c0d00101c0c41c2040c60780764650980d80f08070703845c2c0d003c2c42d8952450f001e85041d400102c2826003191001a9818103101744100e20300c50001a81d54509080e162590102e948040d450300b010790004ea2801800e00c01c85c59040704820078041410094100307506615441e041c05107905580070a50864980301c0101a40305c0100006040b440880000f500d08260280f200ca000c0c0008a030003100c0144001207119004006a45d200384006141580841e12100c0060a8400ba4202d8034040e0300e501e95201d540a01c10200f24038000500f0001c182480305411442015000c0644261305060b520300d00411136824600031031500d90b000342c0b515aa2424103603607003540e04056038042942034000c042441086440400c80413070250301207911001d510411440203586400c006c400900d6486070042c00304405001c41c895922450180c50720007150380d42d0035040401c465002010500043c5087c0c9034100c154001c1c1e001000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 216013444 1250 216012194 216012211
    0x1507020a03020a0b1b030a0c0f020a0b1b0c0603040206071e020a0603050603100e0303070c0c091401060f0e030607050307170109020310050303040b0702040207140d0c0c0914060108 79
    0x2030440ea6500807a00d4100305400800d55080b0000c0d01000b0010400c2c0345031040c414003c029441c0c5000d84d4801001c01c0c0d5201c5005101d826200d103244155541d07528044094800d003001c1039034030540c62400800004440c154003080d0301800500090f986869400d592143d50084c0010740f03045000c0cbe03501000a40c202d1180340f084070000c1d01c0301c4096150706440c0c602521a5172400180d5007848010145000454101020518103200c10b040c500007012003520742018542c107058515140502d41040c021100da0045600e042c170f001100b4500c01d0501101604032451034031f4091642180100480b1a94407011900703405900150105210130720410003564000c602c0e1501c10729403d8440c0c0d1244910368203074051401242c0201c24040f403c0ca01030341440042030304400851134986080917404180c010101302a100d140c0c041050401d000401454012060041d000d54141061640c1c002c1c010b44103c410603642c110008101003900000740c82030f4920300452441096196a8038001103400d4417000f8090303007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 216014694 1250 216013444 216013459
    0x12120a020c0a0f031706090601090e0601020316080306150408060c0306012601030b0604061805130b0403020304030b010909030c02121903020616020d080c090402120c071709150702 79
    0x100300f100701c03d110428804d64a24461074032041004540130000760040744500b85040505c0141d81e0404114000c84414005d180c01940c0c40d000140d05500502180314184242c04030500100000c0c000214403488048800b20384500c0005038034101801a409040c14990080c004104080100406585d029005142c40b003240003621b4040c85c040c011507148002c903181070b80b0042c0200650590b41e20f0748254140c6d41045014608801b01c41d0703420403a041c0041050343c80011a4990580000c40400740340c01207101d2030982010300c0c0003903403640316110980f54078030708000110b0b000c81c103802180c5030301e90107644518514070307039808010780d00d000a242c0840c03074401c241c50500820030703a140044046020350003a114a16000c1031280d00361360400213100854128082180b40c80750410386070380d009584d039001941c948116a0100e80203220740c442418560945404100c9002545801015214400c890002c040045445815444d01544403c954007000340c0c00e20100301a03041d0064076000b07000a0644 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 216015944 1250 216014694 216014713
    0x10b0d0312110d1b0f050703030e070302030d09080105060102031201260d02150f0f040305070606031505010617040309062703060203061f02120a02010b040e0f12120a020c 75
    0xb01c1c820703804500401012034440c8801203640c1301c5000070719000f12181c10008021803040000904500c079014000b414140c0d1042201c1c0da180081080c2c1002d56405021070311034881000001d0242980c41c499142698208800a1129403001c42903a85203503601206618607424001c9000c460301522191021220071401c1c5012801003c00400c190074400c0c1c1c001d40107007204041c2500d20b4110003002580c03c080902c084c80103d140380000d6036840350700751410f00d032201c0180c03a040c405011070354005840514002d480306803c01c807941c040c5040700d042d51a001c50702d0703401986140510740704881c054049020444100400c0703001d2119800e59402031424a003402841c8840b2422102080d003007601c0b1a035000c07040081500700526412040600c46c407191004141101000b9951400079000011661002ca80105854001d400012415800030401e1250100b01c40341d0964400f05050ba400480c418050000da0307034240001141d03044000e4040c214000e5079100c261034043d500c125411040c612500507103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 216017194 1250 216015944 216015971
    0xa0509030d050301090b0603060612041514060109081b01110109060f0b0418080904020f040302041b18181a0604030c030c170604030c1b08010617010b0d0312 69
    0x1048140000d0b8031456101d50405c0c0701c88040b0794106003218000e6104100780803503944d0302c50581c0c4d030b6600c0f0181d084005c2e903500e2819118807402103048800b0b03282010b444e985010100aa2548070741000c1c0e80320340c4903039541d0040313550354144040380342c4090a1001c80310300c0c2d9501c101c0400d00001c40400010031200459500d20b0f0032103820043c0401c88554414034103019140030301900d40302045400c0f02c0d0300c440c0031b6515280614841d4210b00c6204a500043c2c000358501d00d1400d40d0002c5030024010028698807600c0c0803130900004582100181110310403a8502006403a200151500d10b484000e4004030700c0b041c03000610f540304952a051070481c5030301c80c00356a00001400035500c0380c1540d1444d186145044000060301e900300b84c0b8681da02c01c11001c1141400100160f0003074051401000201460505004000e00942e40d052820200c01d004103100005400c0700046a01b289588030310320040c100ca9900305e406c0109542d52003a21030b0020300209100d00800b604140001d0400590184030010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 216018444 1250 216017194 216017203
    0x10c02102a03030b03070609080607050a0e0904030c0510050112020609060c1c030e030a080f13170c0c040c080f04060b040501030f0311070f17030f0d1409070e0103080a050903 77
    0x1040b0000790b02c52415402e1410144120401005113041c483c0450b82026401034407060014132a40422902082d18142603110301060100d018010308400c505080c503080081032960076032015946485682030790294a0f10743c0c860b550480d0403032032965070741c0e81060b8200f05090344001c0d49998008030030b024030480c0e200305101790b452480480101c01c00600c007000001c0e040d590030700412541600140701410381a6006859146c0c00000104004265960b9591030f0301d0f50707045000060302600080e4043c051084c04c440090070004810002c50f4a00700b540c40070001955101ca00400028031f601e00895154440c1c038036900d8000f80309400c04620320b00c048020030112a001d83c01a10210344000c0e0400c01e141c0c01c0b0f26560b0700c0e618a040902803041c184140307020151900d00c1601c10380b220b5907042c510448014416510389100e0414591b1f40c030340c240b50142c0e000d4501c2c3d50301100c0c0010f029010441700e9100180c10421200d0401d410280d582c6140c95001031604028030f16401c4c480c0411441401e0f960511 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 216019694 1250 216018444 216018527
    0x30904020a0302120f040c080109050d0f2102030a0b030109020d0308060604090e030316050c0a080a020c0603010314070f081b1c03030507200705040f02040e0109050a0b010c0210 78
    0x5c810348a0b07840c2908000038019026071026485915048030040030800115414030805c030f0605003141910402501182c54949001c0b42610304200200310f905000c00381c1d0000c5002d80d404120500c04010040f040500300c0e00b4164000f9805062821501e00090041d0050381c0c1c41800100400d060039030328601d080940e18001c1c50240340b50000420440c00401c0e0b9001c002110700c55240150400c5144412940e079003040c00c001510002001c81c402040d9071080000554418010f4221034032940d480c640100d0507080c00048c0010b50150030f03408a401c000d05440c020031501303000028410fa00c00003a1050100c1082c07080280c2140a05c0c1d40c42c24090041035203070401c03610070381d80000ea900e032141006004001a03009005c0307940a804043d44d00d51000100c41060340c8040b200020000040340301c41c40244110b034003c0c8402070301c243c000504a0340e2079100901c601e14480e02803001c4094000116981e5400e074400942c008051803c41c00c2940c032402041c282484120580610000d0100c2002c1c0740748440c4c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 216020944 1250 216019694 216019711
    0x6040c0318050a201c140f030301032a090504110904031808010c0e06030a1b0f090b03060a0902032a0a03140601051b030d0603030c0209100305030904020a030212 71
    0x110300d00e90402040b28450b8040608540d5a408420054030014804000c4d500303c45468960034031800c0103110746800102e030f14606d01011658001c010a164907100c0d002480250f4080d000700c0d03000809400d07040768110b00c444100010040103824800e00c5c1d002460081d1040d6408102d4640040080e01c07040805030096000c1d490b65a01401c50024050481145401801569042c4040c075050641c000301c89201e40c01007214141d0703d0341d40351450000100300d49401a500303440b0700c040480006400c201c16a6801c0c419550300c00c615600c921040039948000d85883e608200b148400304030850160f1701440d000003006e6000d4030400b010041408281c0d1002207010100800001c01124098052250105000000412140d00d00c1c020002174030302c1c001c81031000411840c030509c50070b132721a081c03048a03800c854140d401c1003055117074140100040403141c4224020001c00e40854600044800c40e41c041f00e501c0383c01145080280c17420300002c0d40000324481d06050b028051080c0d24151282080e214200d030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 216022194 1250 216020944 216020953
    0x30703020d05150112020c010f11070b10080c04020c0102091e0a0f0e04030c050a0f06061802031306020a05070b01030602090301050f071d0a0b0d06060906030c0806040c031805 77
    0x200280c0221940508483d2540401c031000412990304001c1060700300c02c41400040e200d003441d420075405804510044100c4503e0308420358200c100c120701400a0368056980c04003d6901c01c91600303101903890061071602d0780150396020f840d19042d0010241d2510f0040098203100d085d2002c1401004451206515211110444c42c00c5040202d030241c010140d11840c03a610614101000200c210060400fa0030822858424424043c3c00c104c2070403031039030150b44007429403050708020004100500421044c07000420301254100100c2c0252401551f90461405480c1e4003651000c0095021806450501c2010300a00005c101d0400640e4001c6006500150703840000104140c02c403140240850301c82400881840002c0e0341c070034031051880f81d285040c0802c8610326400a1085600b036403202c410386100041413001780b841c80d0080c10031210140c58240c600c0b62035280c00d03800da44461820341d000410b070100040c036a00d4250840c0c081c0d02210308001609002410104025020f40c2c802903865902 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 216023444 1250 216022194 216022207
    0xf0402010e0102150408030a09150c121b0c17040b222607030206030412023d0609020408030a02150f0a0b01020c06030709080709050c0a050a020703060203070302 71
    0x80007000100120424405854a880c0102001d00030620240020b044004007000003001008140c6c40290603642090290020b68000d028640c05018420050000106506c4089070315030080e024407016036608104400d82105514412204d09030780c0c6809480082c0b01e17031001c80c0c410340940000e001400362041401da968101e03614124042c0041c4840c2d01b80300035084030800101c1c1041c4401030881412803d40341e10310340b441295078036206032904060360040c400402d10042141c00070b80003100c0e201136000c0c1ea04e00441c10703041079500261101403146550840c20f00715000c9148242a102c10080c41400107406030b00c520003401282c210f500102116400052101100c2e6010400c0c1500a6000041400c0c036281007134109038151300140c1081482ca4546030301d41c3e40303603000b4000f411004038041c0c0013070b0712840c1a260040c01620244202260390045c4440850801144d026003440f400d01c2c1420b0501d0030030903c83c116030643c0001001c0c82180500100030001413294002103000c2e4080e079030050380f20708 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 216024694 1250 216023444 216023447
    0x215040305010e1c110f01110c0606010c02060d020a02160f03051603020f010509031f020d11030c030f040f06050108030a030608030a0804120e300313150c0b0f040201 73
    0x110075403011841da51150101e11004040340c8070b5201c0b2100c0624007001c241c494440e00324074040c03809041203025400e00e20742c030b003000300c8c504007402c850303c0701804031103980c0c49400040d1040b60034050060741120040004000d0002c0340c0d0000c040c0303e561481111005255400c2440304200746420481c0c0c0700038603101c10020700504110805030025400c4e00c00b01060310350b41c00154032441003111941803040c04038001c01e807940c00703200103030700c0d9141d0030880340c0f0000387c11076228000d60141c070100104614050781c1c8889000c1400c240d07171041000e010000c1c41d41d151841e20f08643c0500a104036400c2002003245000901c441c01614000c001400007183c440f0f00c14480035003590400d400800035540207110000107580c0c4026290340003500047d00320350400e0a0b141c00c40300341e003045580c140c020280180e0100b101d1803541c0c0300114590080340e40c002861192500640f24890501d405000510841090002c0136050308818161007890034031304011042c9a6405000920854050511f80000e800304000e55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 216025944 1250 216024694 216024701
    0xf0b0403080612030702090a0b03010f0b0103050108070303140309031c060806010509040b0417091513050904331b02071e140a0906030b041703010f050d050a021504030501 75
    0x814121031503a100c80010400315585e010340c0e20080d124000c40c00c041011030b941d40c2d00100083e44090000e000394580c43d0b0740080940032000000e4002860b1200006200b0350200d10302007641c0d81981d03015041d006060134403200e40c102500340700c16800704000c581040d4030042800400100841c2000c1101c40c903040100d4140401640b0250040801070100400611501031559100d0f07408040544a04002414034000e07002d40300e4142d800a0f020125010700c19244800380c80c20301c6540c003160a0190300c0340d00b40700c080b05c42550700a1415559404821403500311229501c6d244000c40090144801141400f20070b440c070f000429040052200d100c100766035410721094020748045102001c02c0c141c91460045000080c2c0724019009100102c1300c621070340e450200300006e124440781070045079213038180b42c5480c20082d241202d14411a6070003660020086017540c0c1240e10b44605c0c1900c40e4584418806511400c14003101c07030b8081c2034007060050b503136840410591036111484d10380320307411490402e085 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 216027194 1250 216025944 216025951
    0x3040b01080d03020a050a0f0306030804290a020a0305030702010f1b1d061806120703051008070303020703060b0112050f01090e030412020d02011403090c0112020a081b070f0b040308 80
    0x4044c0104402d1010940100888514000e40d00d4100000b03d80755100714001c0c111a0001003122400090004602c2e1075407008a8215440105032503403036090180c03041c0d6904c920b542c6440541c10414410001c207002c0c0014651000e024000800c4a1100503c080c00300d942d81c101020a4109a0000c0050030354011980b1841e400e0a84902c40700704808400a81c9a0092164070b00c98020030f5043d800e1a610381c0000d0798100030900000c084942040d090140150500700c0316001c40c20381010001500c80c40000e41d0b641200c3c1c01d5000b41400c0780c110780321071025000800b0024103110380c00a184540100303601c82e50b48203050b106203440040d41400c5c0303690300391a4400b01d1240b040c4c0c000e01c4144201c9005034045100303194111011881c8080d41d02c010782e142905d4840007950301c180842040170780180031031400c080110990fa0114515600f06004c0f08a018444d00d81d400902d00e140001e291102505024144600a00032036082441a1792440c8080081d064100d6400552009100c2096040643c00e0380 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 216028444 1250 216027194 216027197
    0xe2b08070c1a060604030215030403020610060921050f0a0203070f0b16170a02071a07030e091f0305011d07031a04020103150e04050607090825050603040b01080d 71
    0x14103001038590342d035502c2c00b46201d03111510440c0080f40043e03490000b16401140e0140c943c21883d040303130744251303055002210250054041c0200196840208200020030f440140d182e85440606000c90559105080e55a90100c982485642400f03d1010403600e0401100d01006115180c240c1c414141050616845080d0310400d02c5424007410001d00141c0e9051600310140585010950030702e80404041e10a003480e08450004119214540c0400c50000b42c0e180800500f14910301031072003202e240f0400802800051401d00a603a60b403501c042d000e030b04580d44c06a055038008142c031403222034100942c011140f580d9100c0000e00c0f21852428401103568810018005862850f01c50207520300d4000071141ca03e40000000a0031a17010f9800700082e035000081003103a090f200d44e2000301d080344c1590180e41c0c501c164000150440d104000450980d407210f8041d04284c90400d00c1400405601c0b540030050796100003021a55803a5000690701c103502695503612154075041c089400c3c40782e03400c1c4810 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 216029694 1250 216028444 216028457
    0x1021e0d1101021903020c0a0b130b011d0106030c092706050f030d050d0204120602030708090c01022e020a020d0912030e0d05010b120d030608070f090e2b0807 70
    0x8043c0800c0d9000040418018140580d8810b0040609810f08c0c128081c0104407440e060240310081e00586102c2d2811846110340940c1e0382d8840780c007441c0400c6100408200705404800510146200e6000900108a9403d04001d240d40b0303982420b0315412001c0d01000848510b400e200007020460007010000d000980d078a8840700525000320740c403940011418014442c0006201c0070102540d030495004145212008900c4c00c010f01e4400041e60040d10036500189204000c03600300d4201150700c80905c58160014a4145102c1d00e914081e03601c840d00200c0c802507e603c0221017030000340000c002400907503028240c211426036010b8000b44076034018888038244c4500000000340c00040301e4a026104032010580130040b8600940034056800c5030941000707054281c2e48078808005204602640582c0f8180810740e07c07480701c95a81c05191040998454031103008015100c030907403100398542c250300103945001d41e401d03042c10988030740600006110030440c541c0c04081540080b40c40d1b0403500034035090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 216030944 1250 216029694 216029707
    0x20f220c0908070306020f1c050402151305120a0501090506100605180607020d060f0f0e030c100209030a0203150108070603050f0402040b1f08040605060312030f0601021e0d110102 79
    0x2c0380c0da1250740c04010b112690020303041c42c410074020162200342400c0f000b8000d4022048040f40058041507400328000c004103100c05490807105030a540c02c850030b504913040e010b441c0c50100660000c80300001c02843c0104040c84011507000c1c05280001c2d40210001c11507828080c40d01e42100700705603c44c4c03003041810300c84034400bc03880310a1035822040441d4110741309c41c1c0500000d042c00051305802131441e07141c81003100c08080355400024900400a004024902365000840d4403813150100b111400d812100c4900c0d40c1c07450301c1c2e01410402c1d0010f1304854806020b50b0100e0710700302d918040c40e06004150ba0041050150400050740549100d10301803005040c005002441c004001e04020320450300c50703644994980740e039881c26a01c0e502e0184000000c4100c404068203a1005540544a007403d05000840300d09000800ca0b8582d0b0b021030045180d540ca007010744031101e40103000c0e5811401007030041e000c0c800c02d40019800310a00940507100e00040c01c48090503062044c40462003036401442603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 216032194 1250 216030944 216030959
    0x105310e0f070804050c040e0c0f0114040e1b0c03040e0a090c060f0201141017070807050114040503060c090f01080603030d09060605090108010c0906090e010b07020f220c09 76
    0x41c241c001a09040c072440c10785581ca84542002a400d20345608035140840b00151180700151040030000e00380c0744d410903415075200449140200d0007401980c5a8100801c01400c4c9084d900a80d00c94106400c0c00b070340c5000c0d85031400305980f291310702d00a035520104090180e0389071810dc4940054001500300b1010740b8036a141904030b444c501c42d40701405200e8035080e40e024003e401004c1c200041c0e1030300004074641100c04506003130740790003007966110010000c0c103454800040d41009949902c4c0040c9922031420004403441889a102c0800840c03003480002015281040078900030031f085101152140f20b0341050150034441000d0380ca0401c803082060050380c1d00c01004440c01c0d40d00120000c50305600c6403c004026229591010f81c00c1800712000284120042d441001c215100ba659a030003250f41c0d4600715146105401441c400c94090760041000100386401041c2051019114803600103020000407445811001e0f041901110111050030341d15080c441c3c9100a4440d0605582c8641403484 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 216033444 1250 216032194 216032221
    0x506010b03041505150306100609050303120a11040b04030c030204050903070c05041a03060f010e0708101202040b03031b01060f06120203091c020123060607020904020105310e 77
    0x4601d803036640d9040414409144541004062a80a001c1f40c0b12421700c0da00d81c03900500706100d40c800003290712a01207020b00d40801165506c10610741c401d011900c51b031000380010308072288020b116010421001921100c40ea020b040154024080034442c0c0786140180010349100922040e070700e801c20010304000606103411602500c1068900181101d1059030104c007048811035029070510805007002071040852400d00d050fa03200c0380300c9010720f484009064548a106454034800da07000c401080c4a2885619814112140001d0006c81c101c082400400e0656201208081c48041c04514030500f0316024011b10000b0f107551410303000e181e803420100800c08660072008030611500000440c03107442e010040c1294000b940142030342400d000c420064000e10035040160801200400704041e4aa0405170903442020042c25542ca080010342c00c101c944240140301720b0510000b031201c9074042c0000302c4035032220391255228164030b071035050b400b1441c103000da40503100d219041d074100a1103800d2810f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 216034694 1250 216033444 216033473
    0x3060602060708041104020403050a050d0c0308011a0403060606200f031209101409071508160908030310090b030109020d020d112d0109051e03010605040908070506010b0304 76
    0x9001c580f16101c0c2c0c81c100c04891401d441c102d6100340041000303c144074001c101400c0d1030384680129501500031480540b0054492440900415401c0004200c59048045080c2044840c9402945415200d81e207060413210550480710009011820f0903400c8088240c8070020b100b5208004c2c0389040d1506044c50303407031003031101c040012560b03903020501ea46401c101040072507180e00ca0a21084642c1e1445010000084400d1002d6200d000780000c1c01c10904e1542c0701d0f4138400399071117442c80c6d07a0300d200010403c0c48181001e401c10404044c002849841400a940202000020100101d1824140e4800d80e260124a1446a4900014140169074984001c410154140c460950885980c20900b00812a0f800000d4000c522510740b000e0030004400d4000b1058601c001007104c0040e140d00455107000b09000f03080d00980082503a5494000d8401c00c01c003000c90080003c660345444101090a45002e650110350f81c035404074503401041414090140074008103c01c96042d440c16880b00384403020900d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 216035944 1250 216034694 216034697
    0xc031412090112090f050102070312020a090308030403020a0c241403060d21080a060602011b05250609120816050306150c060105030c100207170f060f0105030607030606020607 77
    0x80c00c24a45680c03864200d00000d9030802400c5c0b00c130040900306070b4083d5010013000c9000404001680000c48128425212192607682d150610541035a540400c0c1c0d5101910540540c46007000f5100007464410b07821000d00030800c0103081d0150294014203084076840380784004c2c05010350310b9001c18200ca00c1035030707440072040341e64444a1055080c0f0f84034940107080080c40b5041c0806080940300d0300402018015896000300300700c01039540c1c00481c22180609003407080038109802e184565846003018041d0466a28407440da01c6490040e2004460200f070302c0cc42d8480c2e2100002414441c10136242c80e070f80902c5050000a03458426080d07124510407128241c14003101001003003181d255030ba0076800d003000e80c159007a81c98072031201a5580743d100344100c0e0720a210701c000601c0b40d414051402c1448801c036800038004c070f0b418000c1030040c03603ca00900c000d15116a01c8014000d03102001454000d980a0012400039410501454140140140007005050404030204100c80e40001c40303c0d44150349 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 216037194 1250 216035944 216035957
    0x9030516030f120512070305060a06030b10031d010c03090c0e01050105041503270c0602030a0527042405010e011403103b06031221040c0314120901 65
    0xf070b403209403500c0c02004c3c0e801c0c1c08250030104000d20f45406601241c0588002c5a240322200d5486008406407914805503680080c0481444541203010ba0001c00789104071084a000140d007201e041c500f12036600020702d0001e40ca807280d56050202103500c640141c03401102601c055070500c2d00182140c4120702c070b203007601e001d142d10941070f0700d100f03070b00400b01c0041d80000c0161004615000d0402524203440640e0300e01d089a00000b1020300000c1101c010b0840750300c6060410030b400c11803581314940c14a07c00c580c040381030903d5606581e54460f007500740c0350700301c080b407031840040710107030494915904914140040403501000c241c0e007120001c3d2200403000403443e525036074040c00345503800d81a03014180f0341d90405045050000c0200a40b2050032014a8440e8400880041a180090103036100358264000490000400b0b551000410035151440c081d10101c4291521300c0015020440d425919854150410710070004604840080020450001c08002c540500509124403480f000c00d07052100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 216038444 1250 216037194 216037223
    0x607050a020a02030615181015020a0501051e0c0403020105090405270f2e0c020a14030406110c0f1e030313050103200706090f1209030516030f 63
    0x20802240b11103542c06019910f250070445500e00302c08668416079071141100b030010180c1d403506414a1485a441c0c002e488007454640b801940c8070040161054007103015040901c000708800340200d0340200050300c0c2002034822540b003408641c0350040c1c03940d60607030300410040015030b90202c19100c04e0042190002407940b55030880700d2049030580894841d2220712103001c1b210860108100704080341c8807054036801d6140000405482200d0b40342a00c50101030b0400c19110f00c00343e4800c414a400500441c4c0c08100280c5900c0c1e1144070188100c001d40d48001001c1c81100e90100d071480340c95115000402c4401c2c903c0000400340450901d42500690781070202613031502a4050100e2a41d4000d0b0949984030a00101034400641d9802070713a0219082800e038030441012540e50305200c1946070652824200c41d0303510300002c0d01c02c82c00300380d0342441d040d4181004100110702d20b10340d101440d21407490080c030b14a44203003004035002a03c40d40c400c11800c100081036000d03243c06025684681440307843e07013 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 216039694 1250 216038444 216038447
    0xf0806041a030f0d080108070e01090203040c0506040801090317070c0f050c040903080417070506071209080a05031506090a060e06070602131409040c150c0203060a090b0112050607050a 81
    0x304034080a942c1031041c40100c90001d180429108120003050303440b400c131070b0789030a4640d54481c69403003604544415540104060305069000e1a041445036407503816507076032180028242e070401d03084141c4695461101d20304040d04000e4100c440c1074000000b24203841c0900b0043c00000003010003420780c0e801500d011081180c144094083c120000300104404010350278014480c0e90111003c54842408030700030510255184295444c055000000b00f54540d40c0c20002c85811420303003a1a2002621070f5500c000144600020749003110050b41c1d030300d0f100c1c81c0416220840200c038098490044404102d1090b1540b910010303030b001d43d41e542c2000081c9030300c104007060140c814001c014080b28404100c003408240107114000466009005000c41c040d0010200301451500355001409007110360b90801002d22081112480c0ea28a0b0800f55071b0b03402c59801003400c00104440c800380d540d998101c01000c000746c801e01c442c0034000500380796507100c01075511141e075840301800358000d00002051105a07203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 216040944 1250 216039694 216039731
    0x601050a0e0f031905061e0412091a03090c0a05100302160609051c0305100e061f08060a06030b030c0904020604030f060b150307020c0906010201021e040f060f080604 73
    0x591020781203609201c988a8001445030380741404031290f0142101087c410980c4d040003070002e141c1c4840162450b1107690382d0202d24003a04034010b040c840c80c0600000e05280200b00d201c4000c4003503800965a00d0050442d41c2803940c0c100d9005e01c5401091700901c801d440e0042d04000303450a908005980d940310500d000e2034040f00c0b03c0b004200d90705207d08001000701c0400d8031006001040c034013004124000c00c00760280d65040302c070b415122120b000100b000f560321012107504140090102e191310f820b500a03c007240ca900b4500a00032803c10300510910f0f0034485000c000815103480c00700449500c1500003604d56200706070192040b64580007140966035020200c034011030348500814541505c80c0750000140440250075031103060800480c1c811141150200d0740703c0d00981c0c0c050441801003c04200b005030000d07200904542d800c3c058041d15564000074414080460542c00e0384407480c1c0302c4c0600e84081240c1201d030800c0b20000805201507005005a5003282d0101e602040c1d1030302659440110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 216042194 1250 216040944 216040969
    0x18010e06042904051507090b0306040504140105040506090d0c0309031407080a060c020705040b09040f24060317040e0a091704030b0703110301080d0c0203010f060b040e0f0601050a0e 80
    0x251082c601030104010000a41200c0c00c1003959000e011039503565800d86100010b4800d10369105c50070000200c0390314003039020702c1d1300500c41d5000401d007290b00e02c610303400c4402c101e42c01c03180c9601000a11030043e0080003107450b98846c0c1d04e04038401c100280d40040120020340b00c01040102a0450900c6d6560305000301c0c4041c08482d021201c0d040a01c0c1400c60241c1803407200c60303000d40644103000c119400c203400348030305a11016084040c541c60b40d90300d121800307845a005035545601002c100c00b5082e0382c03800300401c3c2c0e024603101095171810350500e00e140001c055040100c001040004008031254603130032642c0202c2c00300000945045904102c00da19004201c0c515a2550003d0080700300304110109074041d162541e010441008129019032041c802809101e0f4103501282c80648868492442c42002c03034070107000481c03101c074048803010a8825542181c25960303400b0805000034100c010000b40e1008055807032110b0390821000182151051a00308001c010313101d00d41c07554645aa100400a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 216043444 1250 216042194 216042263
    0x190b0a0503060f04030f0206070c0b04020409081809012c190606200d021002090109050301091101120b0f0108062202040f0501170a02031806040b18010e0604 69
    0x2840c0340101124840803811113040300401c54601c6500c040d20300c0059002c1c895543c80c0c0302c4596118440d2103441c440c1d00018012039102d0380354241c084c0014403090203000c001c508030b072510100c031190764204040c1c010160030048404032281c00031101c1c5202440c403140c402c4080f0302d405a040e2995240141c000c507054041c00c40c2d071400e02c500010307030307581c002c260781d0000101e007040c81e036601d03040c1004644072461481c80341c0050388401d02c919001412076001b0000d00300d0504007000c3e11030795200840d0075540e8508068550701d8a6900b0a01a943c010340748541c2040002010400e041040001482ca200d5480c9454100112180000c03155141c0f01c43c80d1408504d070384680c8a020441c1035880020358041e0150045c00302c10300d02d000586502030341c5a5000150a0100040c0702e03034811113200c0081d0030082c0b07008400703101003a10014105050150500aa0003582e0414080c588015030b15000e20491940008a0f0725200404200c8200458041e40150b4000842800d104100c00000711224410080e0740e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 216044694 1250 216043444 216043453
    0xa08010212010608010803070c060f03020912010c0f210923010c0207080102070c09110403080304030906090e060108040b09010b2e021f0e0127020f0405190b0a0503 72
    0x75894a00a90024101c503043e6440421607a00e61800c9504c0c3d00902d240200b100411070414400300f406022034061800c2c1607d401400d10b070f4801c002994824045031824110395444a1b4444459808551114911343c9820403200c0c03100950b802c9259120503c00d80161599502c030444200041c01c000114141c050091100e0125100003207940201450505540548954070340040d43c0c030341c18025111416084404120003d01d490a600042c0210300c2c0180401c100400021000a0f20134011703500440c02079071141061414003c000d0555102900001c41050000303007005900e0381d001c0c1c0303a242e216030310103803045950700c44001290142a12103030090b84500510442c1000c0c01008004c010060490060340185001102042ea11500d910b003100d070205481e41d128040400705500302d000200b59644c00000c166003c01070360f0309845c0604940102d000300c61843c02055191401100c0060042107400300f01c64109206502003000c48511700f0302c80c132a02c42c029010150f07078400c81b010050a0140544 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 216045944 1250 216044694 216044707
    0x1605071e0f112412060d08040f0e011e03020609041b05090114040302090705030711120c1c080a15050303030a0e0d020a0b01050d1b06020f071d150a080102 68
    0x52a00910710800c0e500404200d50081c20790140149000c2e4010f600899003032a250740c45080d40c443c00d90051081e508a400d0780c1a0f00c1c00120440d004000070040421610760803410301d509d1040140c0e0680c02232941e52007050384c200e04040030141c004101c03581110060383c2c6041c05004100580700c00c840d41d8090031000e4040d40d4046401000800f00b84000b41d0312445d076070b00c500304140000d0289000180d00704940c500006d0102e0b00402c000c641000c3c1e5402c083d00c105086081c0a8034240786d900709003524204c00710724284035260410034918094940c501c0c2400010380408e006080c030000800180c1c00a03151000e0300243c110496828000d81005402d80741d5a240c144402d0015260650b020350180c4154200705540c6480032840c0c01c07801d540b083d00c031202039203444200701041c2e0800e1000e41e940351141e04618031048040b00c01c240100803a4000e4500401014507007801c00b034560380700c18140e84200c00200e2001c40104121617011a014000c4020a026840031540c00b071680d80180a4030340c40000d61 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 216047194 1250 216045944 216045953
    0x30603190602190302190c02031c0c021c03170a020c030309060103030e0d030c0201080a02090d1208100b07020618090a0506040b0406080a03110c0d06060306051605071e0f 75
    0x2c2c0b46260020703c1c040c000c184602c504804a11030580714010800d0164410300b512880b4088800700c041c0010200d460b902018840f0500d2204100c9580021a001d940d038101141805003c241829000f12007840810000380c030b002d0a900c140c5100210311208280006851409907810303103005008050442e41c580ca0301c16603040e0780c0c982c20702064011031044604284140f408608054125074940e0b5000a4592a5801919440d10141034081c40d140c00b4051000192120004801c0c400d0103002c440d409100900d001901342030700541a02e0000071204010700c400c0003164100d51a01c1d9041c1c46130341d83c51034040c2c040303210142d03000c082690003103000042c041000c8071904494010031003120200302c0171207480200422254180314610140c1c0120703007174001103070080582c1c5c1c030a48a082c0c16213102090f17140000e541d40b040008120b60056842800b401405161310030705910403420b8a40c0c200c0d0aa0140c03001c1c00074003030040b008041801507410070b1707481d807180f03405c0461442d80b244032001c51038400d00c0c8c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 216048444 1250 216047194 216047197
    0xd0507080d110f12070807020d06020304060c1d030c150d0606050a022503020d02180703150e15060a0203040803030703090209060102120d0b030109020319140a080f030603190602 78
    0x10180b0342482203034a11070b210400070410030206010035900e01d01d011401d075516042a00301042c01c0c0d80c00701d01c0c07170810008910315000851186104100025804108400142201c0401464041c1e18100854001c101e0344001a04080c269001c84d41510b50391107da004581030711848039020002c07410101c00086540d000b0001e0301c83c11a040d025600030113041d0705804103e4030800d1200d211078240c214100090f046c004c1d08420528009004403000d0354100301060901c0e48155084c01c0002c0c2e40340280300d986951a04100c01030301d00c4210f00c0000d410b0481851240d8112070300c140d4440d00c000200880030138000c10444001303015090560342c5134541540c02a004001036201680174cc030032107000514070b61000c108000040c409803000b40c1480c3c04c2076800d0006080310603c1d1905533595082e46000341e07030204800346120600114110419100d4074107403120001c6451081c10b00c0c0d00c440600c600041c0454151030380d0414100780252a03542d17540000b490105a01c15503950398000ca0180c5080c44040d80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 216049694 1250 216048444 216048467
    0x801050307090207030e090c0c0601062001110a050f0403060c020303010f2103030e19080415050f030f0601031119111207020402070c0f0b07150e0c0d0507080d 70
    0xd060320455951452010160b103d1280014002404402e414620b46441203905410140c50015541000c540601251401d40280c0003403010604032411070b0032048080c000100000d46000003031000d031806248088a40c02500074800c280300c3d01180201c1041800341c151402560001401d102100401001070345980c030130300410f400c59840c4480462400d07090050b0b1103d03070709000c0900b10041700c151400c074020010102444101c0c0030764920824202491041c41400c9402100c1d41d5658902e001035810a180c10780c125001031003414811842d80d4801103095a40c402001200b1340229901c80e40100d0090011080322040403034080348074190001c4042c2412034206880d207440c454400f5180c821541c1d101c4821080d05840b00405ca6100142440d40240000c584034101440300075449407107908000c00190000c0c12030a03130104000091000c00e1911901341100ac100030400e001d18008100c0d02c3c1e4010741d40c240d001e0002c05540108205080006600070090701040c0d901c800a071101c01060601e422 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 216050944 1250 216049694 216049699
    0xc0f081005041a0606040f180c0212070b0c090d1a150a03020d140607020d02010f0c05030402090414010218150a02071e091a01080a06030804090b0619080105 69
    0x14031034840000480e1141c41d0045411011400310341143c0c1e0480380010b0b00c01460315400020038000024035004041c205405082da2022414050002c100200100d549018400d411903004645c801392000c2d142046070596a00440108a071b03503560750111030184100b699140c0c01c00030f03030303000082400301409180d9105604031541c00416101d0f110700d05a41c01d03509003081c7e4000c480020801c01494141902c3c20381521078501c2e0034a0300914120f01742041422500100580c014450006c003080e42031103102d41c080c00c1030008101d100d401d1540100b0340d00000300700a0299444402040c1408118a5444403d4407140025580e4500c0030003110519292980da8a00840048203410004024082901e080d00320315401450964a000040d8800713801c01007403021607a0115034003103501125802071003c80b01c66107010f040240320f400700060030040001c01d50840c4a24241041c800a9164000c4404485030b034240406c050050a00050f4184141c0d00d00e100c480c1d0b04603041c102075982008515048035001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 216052194 1250 216050944 216050953
    0x120203010b120408070804091d1c110a020a0303020307051507081302010c0204110d06080318041508030408010501060806030a02030a0201080601200105040b090a11010305100302060a0e030d02070f0e0703090c0f08 93
    0x1980c882c40c0e5840c4100d000314410b2640d02c001008031440bd805c0c50383d00c90341200464805003465000304484000b2038006600603040028848280502080012462046240640d0991500d03100041040802508140c103085090040606581c132840900102c0c0781c001380100405880031003150305990092500c00f06060800c80b0014141102000b070702c05240324280c00e00075443c43d48003040300820400c5000049400e0f000c4001c6501542003020b440034041030400001d16504149014040b050014200740c407980c00002c200c8010b840101d03241d10710950a00f003403609074590b000161211035500824001c1c800540c4403140c03560005400c11405170780112061202034582007070441d1143c040c40009456200d4a2040d111554460381c0026441224184800045512640015103070b6214000b05000201c0054404146140900680307082242c540010001a483d000b25902c4034401845110f03d03190340c180018210714069003000c05100d40c410100e0038525181d0700c14180c1c0c000540100140c9106 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 216053444 1250 216052194 216052241
    0x50c0103090302101808030103080d1d0d0f02010f09062307090e04081b160b03090d05090604030c030b010e0a0b0a050609130608010c120203010b12040807080409 71
    0xc1d118000906806030301410114500e240c9070405040e8031608400c1c0409400900000b14007000040c6020f5446031032a1a41c4880e2031511105680321403c07001c006402108240d0342060f0006500e0842040ca4108185d12665012082e801444d80f080d00e0b107186070610300c1d1501000007035440880c02c00c488008414503001c60440907400d41004a89010214041c0032007484005605000d055100b84034480c81c0c0d150468440a05010700101da4020485a102a00c49540003050b005104041c0901c248000c0c214940302a216940d05d442c540c1490500000140608080c1c0720030301282c02440e0001c008544d22070350f92804020a9002740b11b5203468441c00c0300481d200f98164001c0704843c0c0750080c2944103030360821040001d254002c8003115400700e04105d0601c107240441c011980200180e800000d0651000e142c0640a00c03522030180b181d0a204000500c0309112010540c0d81040102c0030b41d40d00303030341c0714030f094900c500c5900300280444c80d01107800290000390f50071400c0a852a000640312018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 216054694 1250 216053444 216053447
    0x405070e040e01050105030a2003070609031a0405121b0303100812040501050f09030c04050c030105011407210c05031c06050f1e041d030301090b120a03080414010c0c050c01 76
    0x1070007030180c40d501d6001351400b0404100005a01e279580808404244504044171001a151401503404000030aa11050400034400400340b052203880382030480c1c4c0c2c3d03249071640d222a12401070101ea240322150100754410602012203500400e80c0032401101e58909108007042004845803189480c0d5104000700c00c40006050002d48003240c00c1a15880c2c1402c1c140500165070380c10000189406105d16030041c4500d903140d02481c0d00403004000701e1503580d41402e000401c20401c001004009803c20005c55000035550382480700ca01500d11100303c1d680395488811129070440e0640900140f1000c00d4528120341061260038052000000801c8060b503904140701c0c010808074965540000c541e10300c92142070130741ca5150481d0100800014136580780e205c052104504000318036540350b2011006112004452281c0390600e40308840b586038000f6402a21030343c80303449410040400c100a0081010800a45030350300300001034400034030010031201d070000c05030140d11600b6a56031044036a624080d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 216055944 1250 216054694 216054701
    0xa05030703110d03030b04051003060b0301020901080c03040f0203060f0105030d2c0402130b180a03050d03021606020c0607020705100e091008010221010b0405130b010e0405070e040e01 81
    0x126408010b1010a1100358104680c8200001d0140e01749521228035441d117507258030540784a605400611a031039402c50a200f000c0324039002015000340c0c410844a5203680c1c00c4042c80b6400f0034106101507903030380c80f840d02e541d0354002004021b405105040921842c00c1600c814141640e0040d130417a01c201e09541000c41c0c98841924074140c0d4074240034089501581201d510940301117000e00f016141c130814003d01e08170242d003039001d54400031010030352825881080c40711050b07100c0b045406040360307030554030784680381c131107000c5004241640068058819086d075000380c103020360847c104545802c0d1003e0b465807104403c0750000010700170307408007040c03a107403101c80280030000907911019159512000c0c0101a4030140c001070201c842c3c46400510540b0900040c00328659080484140542141d003240b810340060f00082d500b000b06003c01d00440e1600c00d00b1030706130380440501061080c10340c2c0040c1d0f0b081d4040da40483d0082c0c10003003004148d80c1c1020a0b944500710541c0d08100013410005074500301d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 216057194 1250 216055944 216055949
    0xd180c063207060207020a0e0a02120606070c0506031504140106030507020d020c15120a0b011b02030d050703030207120534110604080d230712051602040203040503090a050307 77
    0x64842801a1008143c25601a16545d031024011541c01d940740c1c00d408140c10700481d99030880c55000694200a1320003070011139041034051b903506080a10550303882094240c0b0f0300405000c2c010200c009194240444880c0c800c4010190081140003071404480c40381030000d0140c100840d00340008220b41e148002625031850641d940030b000c506030034404205011907081d009108803a814030150f000340341c1201c070880c0550f1100e000000c08824540c0007601441161a50f018860310000120025031400305556203401103d00d481c41d903640041ca4280c00038002d461003d41101c880a40440034250080000d041440040c4660700319951030100361100154a14801d9140f441c4c1c0c99525000251156520300c0b1800d030083c0801d060984a8030b040b0302d015841c910010005160381c140003100000e0014014050702c5c60480c5078a0551a9103d2008100c14081c0e8a03041020008008420040c2c42c00540c0d001d940c001d1003996242050f003055941c0c1e070089000d0303038440e00700c1d014001900d10b4000b4030b1104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 216058444 1250 216057194 216057287
    0x40911031b0c01020c030c030d0c050a02030403030318140703030207230f03010e03070f150c1b030306050a060806120703020310050402031c11010e010c050d180c06 72
    0x44060401d041d61a41000201190030344d02441060b540b00320a00280200343ca05800a6440b41c4411001000b51445d80481b032044c0714080110034413455021040314166034040c01c010540d10010340c528191700110040c060000c4c81d070003888401024000c91f0080031203009501700c9010300c0e1540314405419941824100d40c03001091540009d509043c500301500e418000d0001918000300915581503921003041140d04045028a000400c0896402c6407420302070075504101c4c44181e40d10181c088540d00c6001c10802440e0361a0340d04241c0300382c01c64009448082d001e001055a90340c4050705400c03040e11098400c0e940c8100c03420001000123081e40449400600401c459602000142c000300300152040e60140201c0c0c800005110007058100c0c2d0b2800e03699035100c0303120518204142164044003206003d64180016245090b512409440e1000d020b098002292400841e500c81028076801000704259440880003c0040e00244030440c42c40111415501254030340819000d240f920b13102502 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 216059694 1250 216058444 216058471
    0x30a031a0109050904111507061404480503010615020d12020f0412050f0604110f01050c0106140a090902130e1e0f010c140901181203020304091103 65
    0x121500e45888501e03040360194220205104203107010860700c1f117440343c0c62080034400140c0750741044020311a00b043c0f000d210244240c3c41c00e103071751811680c1c0c00801e1844a01083d007045115070790100c1070409410b20b0107003490042443c07500420982ca8040d4441c03a8030a500e80100000d18190501c0305804041d9140d01828448200c0c003020b541c000c0040310f9140126a080c02040c007010480300040001c0c010504911410303900a20300b007407a10800006e410740c00e4000703c5c244000200040090761018000719144400d0700f00300f4004842300d0041c0100001d2542c04c01c1e0b400030b00103070005e0340c40c08202415500e044580342ca0358180717030036924003110094010f451003880355000309503a8031290709001c0b20000c0c0c0305002502c0d103440d0400c0b54a180300700055040030074203c220351070074403c81d0300f082058141501d402c1402d03500d0303400714092480e5060501c4820021446191600212140074000305003030360b2404034103410000d41d6600300b0300845030010710740614001d1100d01d1900762403140e82c6400580 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 216060944 1250 216059694 216059699
    0xb0102012706050c071b180212010b0306011106042105040807090504060204150215011508010308091206090601150905032d12090913080304061814030a031a0109 71
    0x1030b002800028440c0c0c1c141d150900100e000a13465107507802d04031044281840205007003114885001030b414944811b028810041c40c060442441c000301d0444000220700c42d200e45e10312006a508140b4a8440036942c0100c1040008005035410007500110b0240140b4400b002ca00c00e0549861140e40541c00f420790240904011700c6845402c440c0e4400c0c801c43e00981050b50b01e2402070440020f0401ca82d0145e004140c0c403807c240009070502740104101d40c0c001086944680001d49000418000584030482c0010000e40702d4503021a03034041c50400304101e461610304040200d440e003100b801044000d1202d8808400881d204140c001c2c283c41009018010140c1c1d43e5014030314591116240e40d0012202c1513048501050500c9006003c0c1d0070502c0702c5a42e07070355000400c03003035460090208181e000ca45149a02003140c80d400d07aa0b00030343c0b085000648075814658804034aa50480081c03200da80100d49060800020016101c50840b644091001c41100c5010220030340242c1c0c21030340002ca210004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 216062194 1250 216060944 216060953
    0x90c080c0936030d1505132304080a020f0c223305030a0c0506130b030103031d09041509080405061303140d0905040e0c04050a0b01020127 61
    0x11a035001000c007080644000d0290150340e50102901d5000c69801c0840e003504040c0140c0158030304001c8102004d145a070800002501d481400390b200c0c04090f85c3c900141e240c023044081680c0051900b00b9101c04a450289060040b40e800050707080018000c00c0c103490000007001445c0314018900801a2107480c16054010f00c0c10307450000d4001c8560349510040c3c0401506049607001414001c41c41c2080f142020081566102e40d5404075029500c01070b00c0a01042e0365920b040f041d60012588180e1318016100768000b540d01c6500a120080c000000000070190400750200440403401005440703032003d04c081009402044a01500442d102e040c4d9014003901c2da4004903809103d80129070900c1c0d00c2d00041661600f182020442c404100d800034014000c500700c4000391103244600603c1485401d02e0000c1c070b420507a00c104c60280d503c0d110304804240040c800c0020740c00c0042d00030455171400e100c0ca4030107001c84280b824099481c0103409020082a00c03030344606e500d02081400012009a0346 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 216063444 1250 216062194 216062221
    0x40f0f080706081014130c020c18010e070f0909020d020d290f0d05010629130b0d0905010203040f110607030e0609032404030305010e0613150f09090c080c09 69
    0x1c560f0301c945c421020f010621b000d0300c20703100d04480a81c0103100e1600b0324018005000e400c4145c0100ca40e050500400c50442808081c0d40e20540d64605016031061002c02034a07440d0098000c10809030010500b0841e280c07040d0b01030082c44001000074040c0c1020466000d8481c00000b050691030145040d0320080303070a0549609a01c80f40240800003e901d03070b92186421034145400a98517401c44000e080f003e406807880005810308201302e9079103008a00285110030cd191445070860000c40440c0302c040e03101c45540412117490300880250366a242903e0a80c500d20703188002220400303100d4842440c03e04040b02a524059819100c46030107155010400c000340d0041c403e0303681d15100321112003547e40c1c050094030307840d244030b00c2e408690340c246480c02400341e0300160460a143c003030040401845d95100040340e500c001d2540d00000701100140003850754480607030000b4004403079002002548100952284007231a014860280c5410f0712016034540306c1c042d54002a501c005100c01040c090341101d030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 216064694 1250 216063444 216063479
    0x5070e030604030f0e0604120204050c040e1807031203020703030c020d090608060303040807030f0b0703090804030f0c0e090a031e08011a0c0a0b01030b2a0c0102040f0f0807060810 79
    0x18801d002ca4001c030700051b015401504400100005141040f0450400f8010160089401076000d1704180c1054aa00c0b2201c20044c54595049121200000320050500503400615000480c1100007035060030098003035032007030108030002450401c40c90030031840860140882111076503001d40b007034503040048600b20340151080d9410f01041100140401c0100105401940b08001c005c20003107880c10a29941c0e6401030902080c10700303000049001422510459007541d038803c00d1440c07080800d04150b800844a9001044034942560902207465000980074043d175100e60740f940ba13000c41032a000c513011040101e011300400c14081c018030896840303500ca002c802c0c200f40141c40c20580c45000742c1e4548103d104055610348101e82c010310034020201c01c255881910340c0c01d411490b40151042e075000762914202e0a602107004100355a2600003901290000c041c142081128580c881c46107101c60491032050fa6003600c6900c4000aa45016070109442800b403c080c010009140402c544443c80941 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 216065944 1250 216064694 216064697
    0x120b0303071101080f070906030905012703140406170a020c0a150f15150512041a0108060732030a06090b10020c061c02190f0318060c05090a090c0305070e030604030f 73
    0x84040c00119000713240c2c07106a8100237006c03c1030360261424041c101da400175209148151007000203001032a041106510340b0f1040134040d407180c0c9c1d21452b012000703001c2d9044081850040d1070580040c0407141c0c210042c0c0c007041e10030400c0709101040f0310f00d08448040340100c810041d400b904100c4a2500440f201a034125400d04500e06a4801805202240700325000c0b00c4c074084480c01c111000d220841ca96026004010080c80c20b4180110094403115031403041c81d0b01182141c849180d00c20180154140c1c001c01d2035402c5807681030858502001c0e01440c003c2960b070919001c4070ba800b525000c600803110810b65005003204030b071884240415036000801c000584e02e01c41c8031030302180840b48018401c0c5406250005102800e90100401021b018032085c000c041c1880d044010f0311801080050129602200001c0d09420181c0705680d2401050700c42070b03100c42622400101d54001b50000490341c510766a0801c401e0f920f10505444040405070a540c042e031026002500090007111f601107858001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 216067194 1250 216065944 216065951
    0xf05240f090a09121d150714010b03032107031803180b0d140721020304170304030507052b08070909020c0706032a120b0303071101080f07090603090501 67
    0x4645491030004e100f102d00c2c10001d003a141e0285100c4a4401a05401250031600444280011080c0203464000c1c00c3d800303011980c6c20104c10b0340d904000d52220500301806004c0c2c98a4404601d03c280d81c076140314001607081c2504800140343e080c400c4c45030303e10b01460300c04000004011514129070001c42034041d05221504150302242c1c00c40024040d2009030291400403a42c080c940312040c0711402e018100f103051007000800e000c0000301d400030b04081c0d07080076000141c80b56034038202220300e21060480a45000e1001041c0824194000002c080c103a00802c21101c2e449402d0744103140f8406442c6180c3c06291003a005541500e205040e21070700006280340800c1c001d41c65007000012a402000080e0043d84041d05c1044043e8041c0500c00d04448186000044a034094000101c0000303050420b1040000c0d0a070040c03401c0100c0c0d800310300c4200010302120746889007440e00e10000c0e4200c6240501161404001624010202a989100705d4590350349280544c034000c419070180c9003150040302c2c155203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 216068444 1250 216067194 216067211
    0x309080d1e030b211b090c0c1006090510080304060c03111c020706021002030108030a0e030307060504060902040b0402090f012f030429030f18010f05240f090a 70
    0x5840700040c1e00c0c00800f5644000040d4621005172400101d0140c80e80c46091601042480ba034a10802540c010707440030101c1d90311100c4d02c113a0350610010410780101c0c3c0d8900040030034071410a90085108401d480240b003503103503c980c3c0c403075543c2c0100d201d00030000b05500c11000c00a445400405010b0301c04400f01d601441100c80d816070201202e82581c001648100c40401c031140e8104028201d40c01001d804511f1741d4181403c003a00c903c11a1900c02c00c1c00340009400c0c540317413000c204071400c15800401c2080141440d03e00740010740600c58041c0e104038284403440001d403511b8800c135007a6000007003500109510040c019251044400e40c41405002120803000c200160b800e040e010107400c1e80c0195986508244111103203081e594901c10418512103002c40f018032306a0126a00102035610341681983e52036104590000680f00012141d420b002c40905c00303c00c5500402e020708201501080c40500340e4054140101d00070f951194400100324020b0500c2c1003031140c0c243c00200d101c402058002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 216069694 1250 216068444 216068449
    0x108030d020f090d060b0a061106010b0a0908070b0a02060f0f0406051018050105030f120d0e0c10020c0102060601030b0607031202070813080d020a0b0601110f07120309080d1e030b 79
    0xc00000050303550a4403044040507c3c90f0465500d4042c0c903060900807010140f8019150781c500050140e0050090000f4021130134038010100400203080c06821184031303a81303030f40c1d411a0f650046034511001d4814000415031580024000b44d00c610481070800c0d86a035034a03102c1601402014000b95207101d403102010480018a01c00101060f12040012416514003010705d4500340301d1194a003030f213030860700400a4884002080b102e04055407080131a40010345a1000d050107882c15203150300a004416604400e0f80101d25415883e030f098094070070f6070743c0398401503094500082481d035005800b0440000007a01032090101007188600006050140c5030b81c40b0320f416801102e84000c26200c00c503003040460000c01c0207414000c658405030810310b19a5484047c4103102604c910306100001011144c1c0d88000c03c8240e0340355105804480300300d0741d40c0c100e8000c0740310303521000d8001881e000f0010456010001d0480700c814081d42d40c080722505082c0c201e6503c0a003070b02c0003808254440e2002c1c046507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 216070944 1250 216069694 216069709
    0x22120c080406031a0321030a0605060a11010b0103060602120c0c0a0305070e0705281809020a02070618030b04030c0f060f1805070b0a02010e0613060e060108030d020f09 74
    0x82c00c0c103440005204680210844c105610010340724865030088181c40b0519103490220b1103490414940c45031a912485410005490181c110b5a00b03c1008207402000361340c0485800b0204588030002c002c2045400011810740f901d5001d031002680c0444407950b446801c4600800b14440b0701d00c04e48075082c109800040f00f41149500c142c8042d131111205022405188014540015190502c10700e40708288444ca81d0700c140b4042424420000c540c5012001802150180c1c010100c2d2000303210819140d40c1410003c0d0000b14108006110748040441d0582c09245850781404200040184403440c40da10321280300d40003003044082090403125680014621708021506510402010070414154881002200c81ca1a61500540d03800762140010800102e80300f000d0b00d83c10702e445940d503000a2001e0b4090301c481900c540b0244565020014032000040845240520038841071203000d81110340e4070755500c1e007030240d41941e40080143c1d61202051394000c007824201c50010504000303000000030482c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 216072194 1250 216070944 216070949
    0x8060103060b01110d090b0904022b0b03070806150f1206010315050415050a110c0f06090102070b1302180109050633030c070204060b07060522120c0804 67
    0x30315480b00074042c03007036800c4504400c102d0f003104000e10080840a6000b0b00c1007003144500b441035000001c02446641756601160b00b40c030310315071003124823072000060042081c5500c10903104180c94910001c44a250101c2d42c1001c42d800c0707900500540e01c800c8044101d44c0c902003800c0b83c1c0035546404008582d1145482d42829130360312805000c0542c514104220328480b8600e401914034070703200030070002400380003001c8414021301a00141c036607518529840145144c040c0c1c29000390000c5904800444002400350b102c066140a0300e00701c0d181c0d801080e003030b4094810000c07d010903580c00502c02216030110810120300042903018885103261800d99a042c084e00941c1140d902d6034100201070609240c10003810300001d440810b8808500080300040c1c01e4018038805000300000440d480000000a940084e50001c10401000b42d0710700d60110554400e20084079aa400c081c001120161300d09100400601580d2080c540744890307945502c24954500c620b00705214000c070300a0013240901001d00003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 216073444 1250 216072194 216072203
    0x3020a030f03080a020304120507030c200a09021201031205040e01091d0a03020303070f230304051203090c0d0609051c090f05060f091c0501290d020603070908060103 73
    0x1e1401d0340d00340100301c01e20040080e912640104180070001d0310180d47c622000070f0502d445078941d040c81c54212040710340060040d02419031203241c0750030301072030407415250510112803404415030344d24044016030040b030780238211800080d40100085254550180701824140c03900e64074050300c80c1801c01104000380c00880480e0356600a20171079240444e01007004102e00c10042003071804a545c0256688402000b044c2003184e954812740b031007401281550b07144500c10030b860210103040403070181d8940045605645610443c042130b42c00100002c1103e000300850400341c10441d0510041c0000d601c0041d2085030300550340c12000002c21024042d05140c2500f40e200702c900c0c42801e00b0005c3c01c00903140c01802459002000411140d544e02084601c1e890701001101d454415440000c2d40c008101c8480008000010003ca41080700c107503c10010100c0c10300c41c1c11089a40318040c010040c80949a440d00441008001005880c1c1040a10b07030044891615050880e26802030b03074145802a4400c54 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 216074694 1250 216073444 216073463
    0x307030605090c011d090a0b21031312081813020c1b0103020c0304120302150a1e060320040f0c0c02090109020c192609100819020c0703020a03 63
    0x12985c0c040503401c0c903a49104e04d140188107003940080e4240c200504040c0340310756a00c0c2c640d646500c4007945040b841b5600ba549141300420044070580300e601801d01180d026245160115400500410020501e078109500508050107556441181c2c111066101d03481403240c0002d009420180c00104951400d84010302000c04440522403584580444023078107150043c0681d030701034040003040d242203818440700c52051034042d0400f0b9080c82140032410014411070401c02403201c0b01900035080700d0200b15001444860241c1c90b610480314280002052031400030710324085e40b052610162803043c40100005409480140f801c000c0780c04c0846048040340702c02259505600d004020140142510482946403000c06280701d900d803039102100d100c1c411810310941042c030000640000d9902000158410340c4080105d0190b0b140d004200e015100d01550703550414850700c1100d410740551040c00400715440d600c00c00c0c0c039020750030054500510b40701c2e0b1000000540c0d214480900118060076071035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 216075944 1250 216074694 216074713
    0x605120a0302060603010e0d030b0f0d03090e090106030206070803040c05030d020a020405061806060a0507051209190605090607050a06020d0e06010602010501060503010510050c0f01270804090506030703060509 92
    0xc0d0038007000401325403103a40742c4540183c510b40b0110740703006000c640380f078009071403601840012030661110741d00c281c0200152000710b04040d00040b51900b520401c0105410981d40c500000303098a0107030000940141041c01104009100000a0340d0414803400e490700d40b0a44440c01b007480c00c00c0ca841320311700607031140c1080025810b007485074542101c41500c006540940c0218011481200648402e004810005040d140c0f84e10500640e50f07440d501c0b2081d500050151007803010503401c60480c6910400d0000e414000c85d84c0e8460310141212500e49910f0300b0304805c0000c2040c40d400052042d43d0b0f42c00f8250340c08001460313503c01000214904000050b5100031620528644401608000d0031f40e07242000501c909500b040c16681110f104854102c14040011400c4555000744c4181d00d191f481420143c030715241044d00111030b8040080001c0f240c094072030300c200301410b4070003d01501c2d0500400061180c070900c0d4010360741c0070710f02400700c600955495a86400b221404c42d403c09850b007086084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 216077194 1250 216075944 216075947
    0x1602031203010612020405032d011b08010902030702060a0c090e010e1008120306060a121503030201051b04050d020604150e0f04090b06040905010b1c050d0f170603010605120a03 78
    0x418000b10307021312045080c2400c0402003503403a0140c0b82c1003e5240c5180300810111040b0714074404455801350020300990340d902c0228444490748564000100f0100700022800d15070780d00c240e030f2080001da0f004140e1038840c222010300034401031282404010304088041007080000386814000c1000d000f42c0305e014a8640c1082d14155459085541290070a11000350469003d90969400c800e08440c802d59a0200d400240d031a03604110074007090350b01f840144202c800c0414104030849029400070710850b61040383d814003406074490300c201c10820900042c0b0142c180710418144007480130701618a02626008058003059156541d0800259a00344001060a240201c09014107058a041c00180610380c0d92002c0c89100034017060045584802e414140a025000551511001f030004040201d151212902045082d03500390303441c0c400c9036550303002240318881140584100303035222a8040b1294911410902002d000140e056403542c0000c9503545d01c404041c05100c400310300a2174900b5251a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 216078444 1250 216077194 216077207
    0x405090316031e0f0f030f06120f030e100c0320151f03020d060209150a170f010303080f0403050d0f0b01030e0a0209060f010314040f0b0f040f060216020312030106 72
    0x30443c040158022440070a20b402248104107079290b401c010454400d0003a1007002032000e9840007404070004001c200500c000c482d0030743c91050080e5110303240c00c030b6038009104514050190702400102c450220030f0201e07104030b500405c4107880480f2040408842100940342501000d00300200c5890f05061050710092800145240350302040301001c101d1075034001851600400202901150300092240e00c030ba0f0b81c0f80300d400810041d00ca103035900d4040001c4000e000c100c000340303110395955070040402e0140c0783c1c200019048036030558078502035a07101c0004000c2c0070300141049003400000d114100d6550f00c140504c085da00040900007801c40c0104000400b9100c42040a08454000090210158407107403012584040240c490400d21000200100c1c02070030280720080d104501c2c2c2c0140003c00019040308000e440c01184a106241c444002030640c4900907a401000b100410040d0350000303180344c0240a402140428052000c14140c020906101d03100d440340f02000800001031204030b42002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 216079694 1250 216078444 216078497
    0x11060c160e09030d050c1201091e110403060b010c0c0608060405240f150d050105040501170a0b070e0904060504051b0609090a09080c010c020d030c080402040509031603 74
    0x2000d240c0745082c0704031001d45030702c16032400c400358903140c00c0040c12110b14802141c0e261a5002c5400c001581e44040781ca008000940c680d541143c4024130340060f9804500802071000ca0555400703180628540d2003000030140e840940d41408040c284400c08641c186444800401030303510740781000d140101c100012150000c000d440d0154120400c181142144600f14280c0d810507944a005445440001100040d107411640e401000010701c620030b0b05101d4209a0403a070302514144a940d880390107071200c1880380441580d06030300540000020031402d942c0150054058104213210f0609440452111b00040328195009600d40f024042042030400000c0030002c20924a64030110281000914600c83c200c81c032071040005801140881c011a403251904943c030150b4039644070783c054035030390107425aa0b6191b1f0160180d81030803a080c0e80039028903007609075550355600c181d580340e60030040102000b400b84407491105021740d403000050008403030a40740c00398075602035114010324181c00d9506100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 216080944 1250 216079694 216079709
    0x70210080405190201051e0903070801020415080406140103050c0120030d1d010e0d0906030c0c080a021005091605120607120b10030c23031311060c16 66
    0x18041101103000802c3d5150321041058205a44028500040b2171038014070090141c1107030000a075000070320311003005040d00078003501600c00315a50340b1764031800c0b030250b44525001821003040e03104c00d09210b80074542d40140701c2c00e00010507100d010200b0303011007401d800483d00c903400041003410940c3c01c88070340815245051410f81c0502180c040d400d40f2805591240494262101118051030310090305072030541c3c00030030013000104510341549a0350320740c03540c010010443e440400702d4240d100b070040c050340c0755241d01e440740d808005599200c070f039a00440940d821409a02424070940c9018010391340036450000080420086040c140e0452095a030b0005200e840901348080d08010040381031940304c01e05060500100c07600b03200603809844003059241d80191000042c0d0a182d8060307000854200155481076603414810444076900a205c40c6904000030044c00000d4030400c0c40c090740c200300c3d4456140c0100402100c1c0c0410519001000e0070b24040d001180c5075a0982142d02940e801003191 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 216082194 1250 216080944 216080957
    0x30f0c0e0d051504030c0308150105040b0c190305030105040b0102010603051203070c050d0305010f0e0601020c31020c0c0916030504080702060a1701080109110f010e09090102070210 80
    0x100400340140503114109401007180840007010300c1000d00c200380d50101052442002d610701454000c2041151a0301200810b104001141010b1086440d5207140708060310359904d018140006050a5000030b481c0c03085034401e840d8400008414883c100300f400340320303459039904d950400d020401552072007142c0740c1c11607140102c2007011401c0025218400741864543c03550f240c9030540c04680e00c1341d2040d4050300341d100e192001403605500d03600460403120b001845440d041d8071180d44000c004410b89107075006034030101c85543c0c20314214034490101c44d442804000b4485414403449190b120180100707071019408240b0440688091040c0300b0a000c0440307044180b850003c80c140070b07425001283c3d00415585200040800c00d01900719071800e50000c20044c2c580000b010000c103030034091141340200b10359030360001a100d1014050303406940e6000c0f80c0044100255000c0c441c100d0503a80d0134a04001401d118042c05449a90301c407030140782d10310005a0784a5050050009040c1403080c587e042084c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 216083444 1250 216082194 216082211
    0x305070e010e03250302060a0233071206051c0501110a090b0307120504060209030708030a050708132c100e040209090a0501050901090308060d0b0115140415030f 71
    0x2c0c00324128442c004ea03455005100300c9030403c0360b950a00030b80c00003508588009a0b54050540014140c082e6580395000c02c148251400158074a0300900d00302407800003280700c04113402034021001010385074040d40002465981c1c580004440f040c42c001d9003080b00800c069105c050050a0107920b0141040e00e600614205480400410501c04c512981c90b50200c04004980d01138429030140007241080202446141070a0030039100950040c2c0c0001d21a11811800040d8600c0c007005a444007171081e100d040c2001402d4603032004035440003c80350700344a5040c50200d4a40e0700100040d4000000b14180310440703404c1e10714550541c00c0540f4060b0326000200080200c0030001e90000e41c003950542c2c5912260b204c02907643c1c60308540407401070a0794204001c01041400c15400194420b00958440c410303034560000b4884103045e15900034216180040060002d4180500c10110660607440c0000d449403400c2210000d80e041904a440c801850308030001e04a5810f0181180303642041b8400c005490707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 216084694 1250 216083444 216083449
    0x1106100e01170601060f0c020d1406060111030f0d18030f020d090311062d13120b04020405090703050601080c040c1701093c0c020d0c020d0609050d0305070e010e 71
    0x3c051141c80c1c2005104442c0034007461007481503844050b07010705406800c02d4240f5003100d000044c403031490454461400010040c4d0701c6604030210781940c180c061072904082d104402816031001c20715510300e0380c0b071708403500f0018000c1c00300d04000e501a80c0c0c0e10f440700c10111802170030b01c903003020b03013600f0410701890500c04900d510341c2000c034054046031500c1d52070300003e1004075402040c4d54a10fa40031441051090391000340c8004203030788503d00310b07942c56154507440000b000d09078168016220a280318002401420f0542c002600b0520388411a03171784a0f6641e550314644a0240c0003c07245030050200031040c2e040c64018840d20f03601e10b060a410b81a052005043c00c500144505907040380c40b400341c00d004060308002e001039000e8004800e4448903041c140031030403074910580031407414900407856080c2c0348003080d08040810150f940d0010f801051b0200000c0d110407400130703180541c0d110140000901c0400c01400c40d12182c0d00c000c9010700d8142c801506036841901821305001d58142c6045055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 216085944 1250 216084694 216084703
    0x1211120906101a0d1b09080f12030a0507020c130b04050c04050d150b100c05060a02040503060c1e0408060f10140d0512070c09050c0a080c0a1106100e0117 68
    0x160302c10b003240c035240b0407100503001c5c0c100d00990744500c90342081c00402d2180d00000f528180c80c1c800d41140e1555141300e07410755845944404510760841c09101081c0031000b91380016400c01e80030301c1210080900140020364821039609444002c2c1d954001e242400d044c207015440d88002d200b1000303070910745000003040140b000d00d030340109980354402100ca05110168084e2071001c030007424a0b500500e140b0030207044a100c901c0107440c54400c21000400c0540540210380c191000075000d00926110b4225020403608407540320044402c00c2c4c41c001805007540b101074001048400000c0001e0b0400203031000d600c0b4005000c2200049440c0428410440b240b210038800c1380381138409003181c42c15400d000d400c10310a54020020890009001c2c01400a8444d4807400e035000c80c5001c105c2c44c1c5584202e0042480790080c1000414540d0001a5800c2041c1300684010426410190211003950001508004080f5a07220300c00c20400c20500c21014005440c5025185460000410701c1e5040328070746d0748 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 216087194 1250 216085944 216085979
    0xa0803040b07031410080f0a05121305041107111005190908030d0b15070302071206020c0703210219080f0d110702040b060a090303121112090610 64
    0x44500300e00106003490720030741c030140150740d404c0040b4030f06041601035800c3c00c040a05c00c08003d0300c90781045106141d408100c216800d40e010004110402e683d68012005800203d0b15114201002400060031b450310f00601d1040d942817841c5640d915805c3c98090104903106440c94064170500c881c0c5100d19030040100d508030120b1003c1d0b00c01c0b0720007991044458901070b030001d54160002141c00a0ba00807560400a68590101c1d81d130b00c3c26944080150056000322807010b80182d0240c0d000b0070050920105000c0501e0013584c015240072a05082d0074949600c9900448402d40051810900f0281b02c10820702e1b20103880c40030700400300e00681d01c020303104d207044070292001200190042d180c070182012144807060000007031194405050303640750300d60401d00702070b0701460401a0b900c1d00c520f0803500f141d00410701501c80f0306103d41162002c46180303a124400301d010f5a502c811061300003114101508000f4070308031400d080c520b04998443d00302034001d0844160755075440c90030f12407289200e040c00003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 216088444 1250 216087194 216087203
    0x7120c2301080a050a090512280c03120b03010e0a03020c040605030604020f120a0606050f06070503030a1a0a0b0310050906010203030a02030907030c14040c050414040207080405060a120b030a080304 87
    0x22139031038841044004101085c0d004106120b5441c44503d0100c40034007509203460f4400c100c00000544d4051825100c0f028003001c03001810071074584002038001c0301800d011760810302002035184a0074002c0307400c550707082044e00c6440e84046585403c059040200c0114403000741c60a10040d4540004243d6584000c0e00091003800942c0441c2d05940f981c20b280c0003034101c60021204c008401c1c0c01c020300141528015030f4003c2c48210542c65a9081c028102c4511983c0440110b2842c2d66a000807c02404820100c805000264120030226a00d00075428068010b200035543d40c0d040c0303000c3d50310810340e081d48507601450341c3d0b02c00c20200381c3c0c000c02506d60003100f00b440940e40b07580d40242c80e800e2401541004180020b4000f01240c0900c070078080c1250b600080e80e04208521040c50142c400303015911414010f0405903205022600b1715402a00809102d5451681007540740d80004200360002c05030580007401d4440f14070000d4141d030050f40c1d1b4052043e000b42c203031781c0055100d07024240300c0108042c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 216089694 1250 216088444 216088451
    0xf120606180d060b04021b0601150807110c03071503050105040c020304060c11040606080a0e070305060106050903010f02040806040203120702010f08180106060e120c0904030f0207120c2301080a 85
    0x80c4a0184c1010940f1200240704550342d050105503003600e1a04205401000e11483c400401c140c080da0360f010b00000c2d81e5480303c0d0051342d180b40044541d07a100490166160240d003c18859603102080100040d141c041d5070106403500240c002004c8901c1640b100d8440c90401030031118040c0c010084400303860107450b181001c00ca403801c021422604000107590040d24142d400240b0582c000c8242d07000d258021414040d08240c000c0061303072074606005c05412600710354010080140640010403120b90060004111852051400e0b402ca0b04582e1040400e030700104204021031030140440700c2d0f0a02080f09039410141190002080342c0e00918500007070100e1a0041445000040f041e001c9104a080c003c0c44076503281d1100418104801c2d8405008800007513190b40f10b00404110130100c0040540f402403d5916a10100c40501c055580407041d40100e180225075010050f040c0c0410034007038180300c141c02d171516030801003440c01c0b403070b0340d11140300b050202d80001c0e03074030051894010503050400f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 216090944 1250 216089694 216089719
    0xd060b102d0203070812100603020310090507111005061002120d02070f0213060e100e0c0a03020c0601080a0213020c03070f05070503010f0902040b0f06160302120f12060618 76
    0x142d00c1d601c1000070240c05c003c2c0c0071903600300580728600b80130300c2514220007a00c10183e40307040076026400103584c0c0c400c0302c8148980c00d02141c8544e42c041580100030340740442e1072403518041c20b82002606414014501c0d1510701308019410b00718800e5401420b584020169103036021906d802c18002c0c1201c224829800148030700901099005c1c0c00b80c010f1b0020700100814212001a4000b008240324500b40b66a0001c0052100403120351b60104031000c1d4409000140e4030b024160803154840f144040902d5070030320126541e9182003091a01800c20303031004201a4010340104a010800c121600300e8490041000b440911004070a40c0d88007a40032841c500900c00624001c1c1c140f003200d07003280c1c1c2c04d5860020284484036180c0c100c850f40c24001c0c1ca0800c403d42c42602801803021118807501c2e00100204a44541d258081c2c0b07056078264002d2054903522040d280340401c5507444412800d00c9000302054020100c8498001690007070b2040310072030b2400c41c2100c0e0340440d009040c50000c0c418040348080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 216092194 1250 216090944 216090947
    0x20102070f090e0d090501020a030806060706060303090911091f02150c09040e06010515030c040b030f0402040c09050a0501050705030405040203131401050f240d060b102d 75
    0x280a890040c80785220140c942c0c1e400c1e0010000d003a054000c1c2d2241903420120140582d116030103030303681a80a80006012a14181c402d841d0103050150040c0c403c0000340081640c80c03013600301840c8240e41d2481c0052810070f80b034050315022106031b11030040803c18000349903140b01041400d040040c00340340d40b0700400d1105030b04144400500d00c0d0004807100c10070540c2d4240368010200301e40100d4080000101c07405102c4c2d610502402030f550404c00d6418041c000302003500c0034503030254210403074620701501d40c564101190000d9416142c00b41d00242404110303e040c0c0100c100c40f80d000d1416084140c075040002e00c0040a61103007038140900007c80d00c003886024801c54010b040d014006541d6400e2a04440d10640058441a55038a510622020300460103006c1e590148500801c50711064039020001c14815440c5c03500305034052800303108100d403a01c034107084034030503030107041c00240c10240b1505100402c82c900950008024405601c0c508015446607811022500d00d000c001114008040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 216093444 1250 216092194 216092203
    0x1b0c02041509051b0705060121080f070b0108030a080610050c0703110306010e0907091d0a0b0f0a090b0a02160b01030506010801060b090102030a080a0204091107120e1309020102 78
    0x791031645050108002c2032002c502c0c0c00c8240110351450f60510081d10142c124a035602840350000c1c8aa0005ca00401050320710440300b9041855254881804010a5036038108a900100c0c1e1035404602c046081c105224a408441d80100000405540f802010708d00041016000400161103114010b280c80040351182007541d81100ca000c04540c07207661a1b043c80e50b40425203061452107031013410008611445516030a60142c101c41e4020302c10b171420082c24801810540c02c40c00076002d405246603203c19020003c017401035000d900b0700b030315a00b1700d4840038101002c0240303125086420901000c00240320312010542c4405202c500680300c035130440d101039010030b201801030b20403403052002000f8420049901070407180d01344001c00a15640b6100b15101e0300422151901503001400034440319800f0304441036000c24164401841c00340c560f0b5810b003c5526010511490342c101094880400c0300e8548844c00028641c2440001001d1000000704256910402c4203503041d26030b0003100031a4001c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 216094694 1250 216093444 216093461
    0x50d110f0423010f1e12050a0203040303112b061a0a090504150306020c070b0a020106030201020c0a0b25050a140c0d0b010b18030a03030605030706031b0c0204 70
    0x1116541c1d0750380d03108031082c900b01c400c0340000e9200c00e450b08414558000c84250380035140c181c442d400c842c6081100000c00004000700c0005104103241b4400000e40140308403403240300501001a181e04080c04c0c010708407a81a4031302140190104285207940d07144041c0c042c0d600c54032281c003a07400c400400303607a0040d004030b510078080e50300c01900c0300381311145607130140072203881c41ea541e010303c41c0d91501040182d40d41d0050408150714844c40510104415400420038a2812022107060550b96400f03021154011115400144d55980060045607410b0000d10140340301102c00c55030250800400314000c4c4a000714501c45594280e00d43c000d803200e4010380c0401160044244c9000c0103d80c101120390080d000e10f2603a49006003941030030646004a003503030005410040f003800036804e00628617802e45c030940701d865040380e80428101c401d507020800c111000744255000301c1c56500c2d0400f40341c68010190040414035040c681200c003907101e5030b40c248050354042d1604401103003039400418000e08210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 216095944 1250 216094694 216094717
    0x306060803070b0f0f070e030102070212160e15042a4a03010908040b070302010608060103080706110f0304050601030309080a080313050f07030c0801060603020703050d11 75
    0x214002100e04000c8003509540d4061695101140d40341036030a40d6008040300d20f02c07125643d80300805c0041c1c0c0f090b1900388030303100c006d40014030344969900003e440366000030a5a0240c0d008410305954040c0d800042c00080800c1c000b003801c1410705681d000135104064185da80242e641c2d0848013040c00e4907500807030120400c0d4500e10000d8040c035900800c015a201503280c2e0380c1c49010a018844010010003204d201d8011410b0360f80300301700c4180d100c803040041011562640d00c480c03040012410740c100402c001e001b42c41c003540e0b40725010b29019094800380d42c800001504a6001000800d04581c11952076540c41400083c5003080c505110416000700e40c058642510302008201c100031000400c1410303640607448010380307a50b0340d00e442542c940b501a402006c0920030310202d62200701008894040e18800c10a64074038440d1042c429281900950064410013807820003009140402e20604025002c580790a510300892620064840c0c490036007541e541680d01c0a481403084185025641c00344410b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 216097194 1250 216095944 216095951
    0x5150109050604060e0105011d0301020c120c01050601170a09080d02040b0706050a060b0403020d020d06110318070f1509150c1b0e04080c030f030109050f0717010b0d060306 76
    0x4400400380145022244507003d01d18000380441e46203101d811881c100c41c4140d4641d200b0040341c1c40c07200703000040c81040a4040d9000e00100841c0c40c0e041c0003c5c40c940c0d440800041d00c580d84d0100d160309480c800382c4118140000d05000e8180d010569080a600441c410030110b80d41c007061030018054070035003130741d2014244085030206414854500030242140124002e0185480710300070041215240d00c82d40003138490401c000c0005040c41241603200130300040141e08601c5090b01d0f400d0a07545113111001030001300104200c40c1c040f04401c1c1c005120403510007015501c1c101014802c5090240c0aa851500e00d8038525410880c03082301a400500300364211810f001d1300810020309908210310048071168420b1102d080211104280c90045451103440072015403034a81702c09015a0008101400a00003044280d88001c000001035008101c07146000032180342a4900d61103845000c1c0c0308100300191880340602c8884002903041c152226195100d5448412100840062030a6030004141904 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 216098444 1250 216097194 216097199
    0xc020306040b04120806030c01030b0f0d06091a0f0c0903011d0136060c0504030f050703030306050409020a03060e0c03010905030a020d1e0f030905060f16030207020a0e04051501 78
    0x3a80441801948100c0710322070000404c490981d000042120b000e505580244501e101e84c0d80320b50004a25200064100307004103c450000ca0101c200b6018192107c1c0d40701c0d4880800c204041d14800f0000c00840d02080c10f03030504444a1164000140c06c030b00245070089070301041c5913400c1d408400c0300402d00c4640b1800304002d803960b40c00380200c400014403c940c0940e1f50340d2816110901424455010030804030b83c40d24a0381d51000a00001e00c044040250622000c00050300000481310442c1c00341d401098010700e1450000e0a613181e13504114003440c104035103400140c590202840c203403603201c507020030313611101c0003420f20745000610159810341c2008000024003101000601100d011642629400c805019058600d036034068440100c1c104100c2d07101b0001882a1764404d0090703031610303021812407055158181303880d1044e45c0c07d1909134140310178000074480880c140c050b0303100710b03003425410007550b030300000c504a4641c4504040c0011010000d401c220084c0184002ca0250740140e880a58 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 216099694 1250 216098444 216098453
    0x402060f0c0c1309050a06020307031d03090906010e0d060b03010e031c0b100804030e0102010f141905150d110d0308460f1b14030106020316030c02030604 68
    0x80b00b11070403e0084140301c2810503040c405025000c60300f5040b4000f80900c80450703495800951008010b141010342e120004010b070444603584054218401004680303c1002d481004102030000d024a03041c05041000c02c0641d131912144409480d811040004003401601c001c04c0c00340c5041c0060b90070034080000c01d028015103059640003070075514041004200c05aa080c040121107148110b400703d8009400200028482d0a4115a030b03201807002180c3d94100ca11a88141c0d50b04481c403603440e50b4404104403814280507044040402030701c1090110342440b461214442024069040c000e140340d1301c7e041e040c4040709060701510b903406013000f02c245055040050850809440e0355a02c80d02c041c0d080c8084078038a100512440000298502c1c007414100c19500520844403800c6c4c010700e442e1324114000b40f004d4400d0001c4810454240c41800321b100c8c40081801160740c07042801c1c1e0700144014050954000295141c19120180d2000d0307806181c1029a4000300d03405000b5032502c1000100300811 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 216100944 1250 216099694 216099703
    0x10e160305070806060607120905060d06030312050105100f031503080712110601050d020120061009020708070f0c0801020406090612020a2a1502042105030901080402060f0c 76
    0x224001c80c252401d0740d8503400d0309a151841a41d0065100da01480280c002c1940784d40c21150f50819070402d40a01c035070340c1010490716005403800700e08190b0741d03100c200107060304030405209055070000d0401640d81080d00150030a600d0030b1000c01007082c1c00d403414034098084c0d4403e103050482c1c03c04c05140d1641e6484c281c07140d5400f07403e0032940c0c020b0740941c42c12100e001d00724110321445110042d2000d80e082400380101c14840b008241d04000c1440b048250a41128181d0303584c440c043c2c2c0292182e4074203681500c40904075544195282c6104005a00100304079001762100c0607070040d808042c40015050000c840302061f044800c0c154400103000500c642c100120000300ca00548440084914000304072040340280d50455020811003080d4070190105101d0b00120108004d0b201107040240351240c031040020842c994250a034002414010104c0010141c80320000c0c0e800ca0f500d443d81d1960b541a00c1c3d0180c6c402e59414807a420780820704550b41e0000350b0b1000d003072401000361118444402140c0c0c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 216102194 1250 216100944 216100949
    0x10b030a0f090623010e06060304060603120207030303050105060702010507080903070f1d0601091410050c070806221e0203030f0d090c0e010803120c04080604030c0501051005100c0302010e16 84
    0x40c031801d8619400c4c0d0001029048a1489880b2000c683d0b482082c010b40d580300070300c02c03540d0654078800440051480568910350600369401407403071608528010b002c0f900c3c103030400d6120307110501c45240142ea1003411030740c00c0f0764007030312031615281004042480c003406a000308509480541c8003080062100d000c0b111b28001d0070704205055120300c0019214078800380107006d848001c441c1d4a142504080300503a03440e1540785000c8d40340001c0101424200121030300030810a402079803d101c44c8456002502a10341c0302e03e0030701681440240c1e1043c20107860500400d090241c0e00041300c003503580030f100343c0e117185502c40a4a5034441a000501008040410003100c0701d02c0720321401300f4401421540241030303901c0c0303500444ca0520b0902e0307940d122100040600c559601c04100100d52408103110b040d0041d4869198a00c0c1414036141c11400d40308010512110922800380411460f900c4000c88544981e0074242400c01c0046414103d02418001001c0b1002340301c2e0310007201c13100c21101c460104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 216103444 1250 216102194 216102221
    0x80c07031403031b03060f0d110a09020a1e020a02100903060510150306081b040f06061707030207050c010f11060106080601030c140307081305060906070e01080f010b030a0f0906 78
    0x10003038000084c111150005417042034000d02e454204041509203503402640740c0303009051420000b40210f00003021000e540c0c0042a20700e030040344180c0c403950014030220b48424420301106c888074801030020740c2c2c1d000c85403010b44581992158030013414001c070b641c0d0300a1500a941800303640351056206061034040c0c400d400394400c003c030302c0d441130503c80e11404050706ca8480282500090110103070170008420000c00d540a540c4e454090000d62652107003100804850707c99a064840483c0c0c0344420300740041c004020301d4010410300001803004200b12014034001d003424090f020520030100c80400e1000780030301042c450b4800200c2d605800c108002e120740001da0301407002c0015004110750092402d44a1980200c090022404450081007225408040600f150100068907150180740203410355135440250040c505114100d41d1104012020b09400c0c00c1c00070841c01c14420b10304032000c0501c00c034103500340f010001c100c2008141e0460000c0e0700c680321092003c25441c0c1001002070114285502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 216104694 1250 216103444 216103471
    0xa2f060d1e02131a2b0209120601050420040504051905070806030c060a0e12120a05030114091e09031e0c100b060a03090609020a140a05060f07080c0703140303 70
    0x1d00e41c0404000300e4040c0c0c007549040540d08030b40a0200c8000c0141c1700840c001c0c0030340a01100000d600d03201e910b03c0d45044800001c01d001d52400c024001212210304c924084150030146c0da1000d800d001c1c08540883d402650001410b950704040d01c11114114614070780510b0402c0c0511104551200d1558003800045050350742c0710b2407120801c103440c0f00d8004400080750a181c1009554a0607000140f0f02c564000150b6074241c0750b804401d41c0541c040e110407400704101100501030b42641b0709805034081c400b52107030300445c00c0094180e10742407000032000c0c680d005043d001401d14601031050390070700700079400105003420442c1a007104981284d009641c1038401c0068541d4030500c039026603407405001508552038050306082c12800b034445000c00340c070000d81314001000140c076152081700040c00a01903040c0d81040d40403c1255182151780300714410340d0300380400c00000f00c552003280c00f00d9a00c251401ea0783c244414842d410103c066001401080c070b65290030b0016034000c4021481003030100e0800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 216105944 1250 216104694 216104729
    0x709020f0702041d2d01020a0503180706080c031f06022109090c030703140c070201030c090302031015080d170108010c0207091a030a2f060d1e0213 65
    0x200d80d00148132030028a95000c1c510103481e003001200c40e4141520f4014403e20151040c1e1109426a44112170791000240000100420207078260030700000c900a85000d0081240f4204005280d6000905018002d07200040461074040080b0440c1c01101e06142050386001c0d602c50300651100111051860800c00340409003910a080da8200c90350038a0007000315a881d00c49042d001c4054100030301c000f050603614030340512034510720030125200e68002c0c20b82c81d5851485200040070b450411004100740103d80005100594021603251100e04e566200000c400d00840880121000705510109641c061400d00841c1d1980c803410f1021150b03c0e04a074a81580d0b0783c3c204007401c0f242d0034450140160880ca40c2442580d083e6080204120b018007000317500c4501080c006420b14090900071500300010905d240744100d440e41802085825500a101424191030045039040c400c11150120b100e50750428210719259880507a02d01800c01102107444100f02c0d411848007450602400c0e0324580170300c205 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 216107194 1250 216105944 216105971
    0x1e030105180c0331060603030e030105070e2b0c03020f030d0f03020318011505010f02010c020a15020c031308010b09010506070b07020c030a0501050a0606050c070b0703020709020f070204 82
    0x4180034558002c510351465899880d900c602950440c1c801406800340302440c00d02a041200310141e41d401002c0014032649903190181002e00618450741c000c1c0d041074108034205411000c010f20704401035038820b0002d00e8420076580e41c480c0000740800800c580c5c00c5603a007030100c9043c6400030f4a20903a100b19002d1883c1c4105569902c814145100043d600d18170400e1480c404d0b00a19080b41c042802a0040b900340000c1c1403c0d10441d2410741c28840b100c01c0200001d41e0b10080c01c88100400d40020020f110402ca0700a4490f070043d0405882c41c0f80da494180b6011016904440c003080c0035209603500c81083c01240012508544034840142d0308220904070316180200070a8101c4000816180c60061207a8502901d0000108400103501071110031200a860511803002d40070310071000041c040c6845113460003115071030703003240007007200c00d101c1316070b400000003405400d4440c20440c00b0384800b841d00e412494040780b6000318032214000b042e48203001c88407501410203c0c0c8225018000d10701c86110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 216108444 1250 216107194 216107239
    0x109020405062203020d150c0f1b1a01080d02071e03020d110901121a090d110c06070c152a05030712020609070e061e01051e030105 58
    0x1010781c4400100303d03900540d0444110721482d0701c2080c01c40f0f80c0c00c43c0d403900003984c04031918800f6505448298800d0000c0030552040c91008803103803d120802c0f58011070300a04c030015003100c00310810b00428a66040c00541c01250002c0511410b111010303685031030441762280c420704011401b620403228040b4022003903001455208001030307500c0204a1458003000b00106140b1000d5842051007040d415068a5406400e4013034000b5090b02800c619403860840c200c122060340c0a00603810400074850813248c0480c0101e00480e02d482c1081288280c440701505100012103c00c1e0710550000300d180c1000303442c4803030f481110300903200301210314a00c0c4d4003943c3c40e0400c0c1e560300048c0c800050300a00c00381413440b440d010383c9000300116401e040300b941d5038092050340e6091480140c1c0c85070041001c4100108108405010342c0c01c01c445031414140c2c08624500612001000c5c1c0e43c0c900c80f462000b41e4890819280301c0e0903001701e09010040d40000022080e84203014907400b5070030842048000002164 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 216109694 1250 216108444 216108449
    0x60c070b060904060b0a080105060112090b060609120601271416020304080109080d0e0d0203072d0c180c020309310c02060a18020103110915040e01090204 68
    0xc00445a5451804100da00c400041080314400c2da19083d000307480d10740d80080d501409000303000198909012001424410058184051560804002c2000100b42800b6030342c005200b42c5505858070130761400100301c260440d1900316588645c0300009184507100d001410100780d180484058200f04104410944010749980034244810328080f0b540308100c200865191407051042d07070309040e141e95403a801e544c108402135405034030200c4d178402020858881c1000300201c00d0024404500e241074080c4d00ca018105c0e0180c008540741c001c58000340c164000e43c0491a81d40c0c0b1041c07210090070320300040030401c103000b04070716241e20902070740c49070140e8850305a900d502a0000c5051200010030410720040780d016006404c0102c030804241c1042400d02c0450b0074621b4440403e040d040e200c0020701c0d05038002e120781042d508254803a500c4425050030b1710700b250340a10b00480c043c0031022041c1e003544200e0300f05540201614906070176040030030000c1c0040c0d4186001c5c1c18082e036618504e0001ba40202d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 216110944 1250 216109694 216109703
    0x50720010e040207120c141b03010c0503010305070b0903031b06041208090309060c0c100f0e01050406050f030901111305010914060a1101060305030a050304110a03050c010e01110717060c07 83
    0x1c45151518034060b096204505107d4000003c40d1490303185000e00f0a00c3d5503194140100c5c0f84c140d01d800364a802c3c0030313000d605e451342d2900d141158510385a140e5115510f1244803035840c000141a9801c0d2400d004071404c00420741c500c0c920845401400c0781d644c01d012182aa102c4130038003005401c05210b80310743d0b401225910019400d20b50640100060703036201103004183c500c00e9141511050b1150541021030036400d8455240704107079004040c1003024070078100c90410500b08000c0c0300441d004002d65051100d2239008545a07603a4040e2680100703141100c11000c480049610342007007203200362081c00c4c3c13403007a85e030b048180b9030b540740200304a000c44041c140d0000d0b091040c071443d98451104143c0d82d259080002c68078503520388070b490859000c09641400120000208400d01c20282d024060401f010f43c1c020700080c0c07070740c2c844c903844642403d039583c10898a0014040c243e0310420000c441c02c82d0800a442c20283e60751500b44148c01c0004122802c0d008180014803940c2015090760b02940e0031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 216112194 1250 216110944 216110963
    0x31d060307030f0608010e1c021603031209061104080d05041508060315070926070e0a090b010f03030e030319180801050f060913021e01050720010e040207 68
    0xc2400541c050403501900740541613584000145890742401440c40c2c800d00f80c00944601c0c0c815aa03215840c420141c0894155440b1140d40201c400c00201d03000304607038040c0ba01d1441441d4148104010b4480980c010304018108080b600c0c44550900c0104100c400f01001c80b00e4644120400b0340b00c1c1c1c001d61103004003144810b0700001d0301c280170b0080c89500c21070060a031030f030403284d000000c140c1c00070a0380c10000203045260305000340e0080500024600a840a1001c0700e002d030058090b541c3c0d20700b8010b0040c0401040089108401c0603041003a4140d030210100c042903840f00c1c081d101881350f61100398001109940304040c00d0802104540b41c19003958101caa0b42450640240c90036103000380352109a42c0c0003100010421005e201d45402440140001151400c207002001340441c0d000d041e4040d0304451490100050395906480c000701c1c04e4041c0031303400740004a40103980d20300950b0800781016080440c40d00514502020515410343e007600c034511805a80d105000c04c03030080e000020490540d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 216113444 1250 216112194 216112201
    0xf010c060e0c0904060212011d070c03140703110c0924060d0507030516050f0406080a060503011803090b09090f06040b030f010c09170d0c0602190507031d0603 70
    0x2041c0e044441c90072000070440da8082ca403107010400000c2d0895050303e030940d010414888464200e40458010800710b5421110400c92002150b00b10202a00072000d0208107900c0b082010b01652100f0f41c80710070361007070b50349a08090070081d081e40340072143c0c0c3e445405481a1510507103002416180a43c2c604100e24007000031020340401c0c0e00134008111940000c051103200607105540c02914030401c15a60b020800d030400d921340311130365940701c280f44041c481d05000341e20a03079200000342d030211517803890403a40640314201c110000b4040c5810154155003045481407182d01203942c200038091017a0f0366050310566031581100c1d103010350603800780d0000404005c0384e45041e50f003070940c3c1c006600800010750808500006440c141c0d01c100302005a9442c5c1403001d41c602d41100f10500203000146041000441d80c0350403d44401c80c0c26031820500c1603240241c000d100c5280d060321354020456940a42c228103408011344550040d440441c001807110043d0301601054482d480c40c000c402400003030441d107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 216114694 1250 216113444 216113453
    0x15070e060a050f0301060903140d1b11100305010f06020f0c011116230118030f0f060c03150b07030f0302030703022502091e0103080904060305010f06140f010c 70
    0x38071106011041003401e01030322107284010f0000b54001c10700740d112201000d02c0c40c43e05514000628541030030941101548000d0700350000b03003006244020355844841c1c259145810340c074948101c40a00d40100b600c0b103021071080c0d050f500c103e045e558510104110035030783c0c0e00104c3e5103200c2004000015000408400c009500a4080c180d09561060603583c080d940c01c511021500d580758840b00001c0e480000c0d6400d02c070410500710741c00c801c01307203807401d00305098203821400741a0b984402011198500181001c1c0300b590303c450303520a5404981402800b00889009002d045030780b40701c01c0350410f5031800080c0a0030520450342c5090f8162150074071180115025002500010300c0c501c141074080080120042c0d00e00765480c1c005a180b0810000c801c094018070040c0034006002c01a498141c40c2201c0b940000d4011542c11682c0c01003000ea07940310044042006403050354001042513080041040140f10150000410356007065002d10072010b2880030420040503508606010a100841460204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 216115944 1250 216114694 216114697
    0xc09091b011206090507120506031506100c1a0f130b0f07020325051501050a14010201021902011e11091201111201090b040501030804061d03071715070e06 68
    0x15685420700140d070f156910010b0003501c1048a610000030103514080480042522030b50740c00800c282d000707000d0351030910301c280c20102c4060140c2c1e200382003d0030041402031244401c0030076698448098260700511030108055481c050303689800740655900007894854140c081c0d101c00d030f6080312245510707071251050110000000f410060840c0010025070050350b21000c2d42d0800054070308a550400511820f02c0c5081c0603140010341100740300c00004101c907a035184049000e03554000780c0750f6483c5402c4030050f80244207040c0b00d1500d0019201e0302c403404680651201031250400d100c1060f44601444c0c1000849030403051401081d0000e001c0d140c8070b0304010314030a9038040d4403c00041c00d203c3d1014500c02503081054080040103001005000c00011402642210321f01601d05001030350440e83c4046507802140106410000302d448036000022202c1141d940404000c0d05036030b2401e0703d815a00d140801c000b0000003041c480e2034841ca411844041c542344c072030090381e95444000e441140411020f03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 216117194 1250 216115944 216115967
    0x606090c0307030c0c05070b0d05150d080c210a02010f2a0905090406021c06030b01090b0d0b040b0a0b030a0203070510170c070c140906010503130c03050c09091b01 72
    0x400008020450001d1b01c1000724102030900141860323140d1500090a809030b4900a000342c070780d101c1d4640742541d907895040c80342240721f42c07061100383c031030b00d56140c50342c6002124201403148030220a0030003411081d010091440b20a10b80c0240034810303201400d101560110100d920385001c11041d5640750300e000e0102805c060700d031032522245240c1e035080080ca0401043e43c0541c2c800e90300180b00b03118604804030803001440c510740c0038003030755207142c071a00c002c03482c1442185101600c0f041210075a540b00507401c168a030b403020b14403203241010b0a2542c00c00004039901c14043d40740c0342c3c120000e840e0000b01600312580c001c00401d001c41c10101402280c501c1010307140f0a0000a01c0800702c00d214146406104000302000c00c1e4440d409814003403000745040d401190400e0760158041c5043d00e4640409501100a003070540d0f5a44640c6180d031007115040c82d01078201402954080100b00d00850458003182c81203850000580b01d1f17411550300d0310300e5806940709042c082503c001d8294012907844c0d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 216118444 1250 216117194 216117197
    0x307021f09170607080f0f01030b180d08060103110405130f180605040b07140a080601090906121506060c0b0a0902040603030e04050108030405031209040e01090c03050606090c0307030c 81
    0x114540d24600c01c4020a24900e0810342d5421034402c100100b40d0140a40740c0c4003c40e0006c8200c03608200c418020500d20600014052840c00390019110340c84800084a00039101421903c078844c4d85078000f4a00c1c041500c079103000034100440040e201070024192400e91754000c109280d110030f181c0d0410001c0000e0001d00060070b442d0b00b004400c40c500c5401208290380580c2d4003040c18541450000f003141e60082000c003e1000142c0000070001d168400c1e682c0030307003480c10000074a0b100c0b100180c421240310351114200d1420117201055080b00714100f1004d203031290b0000b40451801d9007400701603a142d801000c2c0055051400c040c0800d03460078042d50425000080080c1c0d445290300410103503146e03600b007a80407a40600c01207a883c20188a490b0050017008003841c2000d040c400000d4541040700102004040003003843c1c02641e5581c0e003c1c020440201c4000c001d4900146002014409071b03100c161102c1c01017400190560402103004c500c941500503c1619660b100380b4290000c01000c00c8140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 216119694 1250 216118444 216118457
    0x60906140f03100e1b010c0308062e09060311070203060f041110030218040b03061504060e070c05150714070807051e21040501110f01020304030c02040e0307021f 71
    0x40d001c030030384031355000e0036589005840800702d9044000c03c0d0b41d21740814541004849111840883d902c01000c0340c01032421144101d64a100000c030700807980007814a40850010030a0003240c86810089000c110b9040f900c060045680b0f4240c8003e09008081003e90107402c800c2c001486030b484000750541c8244a14035012441c00b0110106030500391101144010a60024150300c0014485d079407c218204121028440e448185000c01c0d00e455020701001a0048800049092303965235030050f5000d060012104c100c1d070301e400341000704184031208060b01d42e40140f244500d10481142c10440c8074401c2602d42c02a1046070850140c01759102400c242c490100a005500014105009440345440d006801ca5580d80900704100c0c01d00d42a290525018080c0020b0410002408420f0310100c80090038585031f02480756a4103400c00108200000455100104200c20150071180310500c407030007628100416044c40070001da40388a4504041e50082031a00f01d917030412850503503804510040e107402d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 216120944 1250 216119694 216119713
    0xe0d21020f0102040b0307121b1d03060f01030210050f0a1206030f1104060803091e0109050a15090b0f030412120207140c0102030702090a020d060312020f01060906140f03 75
    0x9401ca8100d6004828440340000a0200e000d90000c0723058072101d2011010040c2e000c6000300100012180c081503410302044165140c42490916590307660704ca80a000e40300f4924060704040b080c1c08003404100d00c100010400f4050103403168065421500c0c40b0146c05141900b01344c410788a030a4480f402621164a8100100000301d1490741d4242042c800c1f2507520724402268108000d680031030700000030640c41840160401c5d41c51240c0307040354081406000a03070004550040380c801d0915080180c05c88081d01c0c000501ca41260700c04011414295204060140c4507201e85025105441542800100c20b00104001c103c6010700d6502040f220b00f0480c0f0034551844c10322050f604030385410303640d035144038081c0c485000c4180303d200c01208092010b145030412660024100d48005000c403070750b882d40420028000005e50b84214055504102d090b10742c1645000000d42e95010000c0581c200d500f07050300000c0707603080b0740640d606440d092031001c4051241c1c442808040e207100e2403004d03898403521506 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 216122194 1250 216120944 216120973
    0x20a09090807020d03080a0e0d050906071a160315030c030b0916080c040609050106090b03100f09050603010f05010e0c0f040f03030905030f070b07140c12030a0e0d2102 74
    0x2644900f601c81e486405817464040300040c01c480746003c52223000e40180148020403035000b401c8800c2c0c1e00b07080b229681c890309a410310310f0700000c040010348602c424000a0001350a44020100e01004040e9070603c81ca41e004003480d0000c0110388402131444020160a000203160146043e030311900f4007045411100100b00310000390350f040c0d4032032146508800740d00b103880d003040d005210160039506400c0c400ba5143c0100103044444512949180c49000302c08118005960351200300101045c9203034445540d1140d165000415050b60729903c20b606e000107181030b000e81409598105c2d07880c082862120b82d642868004254042403004861400c00c01010a840b00d54410501c003950107507864010903424030f42030520304607101e44500642e521a01d010441d080e49102200d220650201c040003808464490182ca08050904100d6104082c100c1d060401007000000d0b1903145c0c1d460780c445021140040c1485210080104058807040c400c102000024410060722803070700c4d01c5881141e01c41549040c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 216123444 1250 216122194 216122209
    0x1a0a050c0a0c0503121206010c080706020d05010509060301050f04030e030705190806010b131511010c081006030b030c0603070207050307061205060a1d09010b06160506070507020a0909080702 84
    0x4202c6507022031180c2480039090801c098544804013405551070100c2c0c8020040444c90014031440c100b01d210f030341c5601005100d906580c1c5030382c1d00c11410340d114407200c0d02c107101400e000d000d0755001b8030f103140c0001d000340b6050140074010701c01c56480424548036034a084403040b0007520902e0305440359060015403503d07081c41d004031180490000080481c1002a00b80c18010f043c1c0c00126a210b0511401043d4045858114103c0e03c9007801c4d0a0300c2e0b001d41806440860140703942c00341744d51030542100401c0307404c4100c6511585413010414a2203868403000e40440340103113200740c0c055200400c159000d0410b40001c540058881c0101c5407096510300c00a4508860382d00210005490140907140402d421f00500303402050480345030022600b480e0a001c808011280000056810040800c0003150298020300244c000a0020380d83d40c1040701b0f00000403220040308179070740e1094400249505216030280d0f800e80354014041c00405142045900182c03120800689609000b04040c0c0016a139040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 216124694 1250 216123444 216123463
    0x2060415030b04051617060d0c09021801021b01050c0a0b0c070b1b0d020a090513060518010b0f0706060e0a0f0b010806220e0a05010b191a0a050c 64
    0x55010500c0d0a20509003c10758402400c1c54170307002c02401c42d600325079404c211144690716928808940981e580b40026600e0204007102030130008020402060303450943e00241241000c0d01c0704103d403502100c004a035100048a607004003030219941c4058558400d4004124116117001141c000e44243c0d00c40a15100d0305407680c2c0801c030030005080c01085906004258001c04800c15504170040400d00c01e030b600d108000070500016030000b001d480c018002d444082c00f5050240c05029002804245200100f4031800761a100342d01d0711400c181d03240703042c03a00b0078141c1d4500507880d030070040c18019552294100c4801180d41d251201f82c045455600c040c4014454072040e0400f089071310504400d00121140164840e042202c0032041103aa51180042d0301641c80c2881d2000b001a21252160f000030b203500c94151045000f10b031503c0003804015046414002002c0310000c00e0f2250464104186507144d200c3c801501903075840d84807490f15403c002d0400e10416042813860002190040c1d4100803081c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 216125944 1250 216124694 216124697
    0x32910030f0f0c020c09070206182a1c050d321b0708071a0c0d03150e0f04021c0c090f243507030c05060a05030a0b012c0103051e040f02060415 63
    0x2f100c14040c2c61600e806100d2078011aa807410030383d00029110f0584500d07400400c0c034240009168441e00b200880e21281003d0f500c00c0049103600c07884410f007500198860425811058000c0d0f40d00c1c4000c050200c1c403081141c529400800c0e01510740902054815218040c92560a42c01d00003482c03481000c4c031080745080e015a03030015100d4401c0101095060964104132000f94028040080449a0a000303c1d00b282d0101c030704445400b12081c80101c00d0080c240000d008500da40d80c00950300d0002d4100e925582041c2c0c60a01032045411140c10025030100619411045016000c010301c500400b407100b1f1b000001c0c900004203a100707841c1c2d401e000d0894008120298407002c010402d1003004a10034002d460102c4070360b460308900040081c40e90101500c0030104a83d100c0301c0e800c5682c02a270601c4201c2d112070004000c01d001881081c44070345100482c0c203003ca400e100003d0700040038503020300b040c4080100858030715100c41e126010105113250017260040c40c10040800d5014603412069041c4409 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 216127194 1250 216125944 216126013
    0xf0a0b0a030b10030b010e0103051f030b060307090504050a0314090a031b0807050a140406081905150403050d0e0106030204021306032910030f0f0c020c0907020618 72
    0x451051108980e101402d103c20075103001010f009581e4000185d003070001c0246400f0403c0c1c2c0710031106d00c90f01503112450300721881149200004000c1200c1800c3d01c00d900031419038500c4e95403a0750050a0302e0045900414a030003a051620000303018141021302c0c1d0820b69010f60500c0c0c01c030303c04198440c1c413a4001303131003401401c1000d0410b80c002c60f41580190101c00f001d0958280b901300400e003801e51070b004045c0f5110488540a005440b07070340c4076500801c0c5540464022504184c100e040c011035040d019a118015000ca0181c104c15102841d802542d050b61031925010f00d01ca42400200090350b03601c0800d548901c000009070343da43c00a000c207c09070300100600c0c1498440e000c0c00b02c410301000310007a80100b850b15400d4050059040c50701c2031041c3d070500c038004031f6010220014562911160103691812075942144569907001c0345813a810f03602140d50345500a820485d0084040710004010b038801400590f940301210145c2c6501c40000c2c0c21502808400080d030404400540302600310802d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 216128444 1250 216127194 216127211
    0x3080304060e0c0a12060207060504080304020310020a0509010e221a0f0d0b041b0807090b010509130b1302030c0901081605090d0309030807060506040c0e0f0f0a0b0a03 74
    0x749209110040c040308009008082000c00030800595140c400d141c0705a007480e1a040900c46150101c4504940c8800200150320b05032400c6485500141c2c3c05900034814581803c1c403400d050b10880312070a245488240c14110b1103001104c4040000b108a504844070685a84001021000005070503103000000324140c0c107002520010040c040c0003a52103803001d0324185000342c488051381003609401071645a007aa40d6400c2135018040c00440440e84100e05800006103241c1c0801e41c3d2059400444080c0004104003004440c0d6001d51940c0b130398000024180b09102c0007265008440480020b01045804ca40c03000424040740c1088800d000b10010002d84000c0560344a59001d5108410a5001c0f95601ea81100141180213207120359000307120041840041c03602035418240116884080707203075940c0d214540003001d0802611000e001d607080028240f8858040c0609170761640b0050000b203a0794001004000c228007041401941000103240c0c003140180c0c441004080e1981c90b0f071030100350b048 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 216129694 1250 216128444 216128453
    0xf030b04171b1f060b0409020f04121103070909031d01030b0315150312040b031009020d1401050901080c010c0816050a141b040506010e03100606080f090d05210103080304 75
    0x401050401c0103d00d0044107002c5c401810060703a00781c92905000680750304000142d01e00610031038212101410f02000510100400d0880e4075084910076010b840c45290388040310000d4030641c2000a0100da0b2500f003455021020f04050f8032031000500d4042105c00d044c00c0400d0a2120b007481030801d42c0d004a0070400c09440c0c0e604604070030001034004201a00d01e001c240925809107010304940d00310000082582c140b141c001c641c010b4184070700110342d100d404d0660700d002802d00c443d01c6501800c00c400002214075110440604840d03804014200d01d030440c80044812040080e41125044414081c002511608450301028148501c1c01448110300340d06100e00d07c1340c00b070004444540d015401e00c00891900ba004d5522000041d90302180c981c851600603141104802d0140d074051040031078606034200c0c2600450200e40384c2d03854600568956010210b15002d0031181c0300002d0b0b12604024552510403002410204040488107480e082801c1940c0c14188080e4029509910044240402d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 216130944 1250 216129694 216129733
    0x110102122a0f03030f070e100527010509130603080c0d080f06030c04090f061401140f06030619031b03060b010f0206070e0a18150f030b04171b 63
    0xc01c410010960781d0780014089580e40300041a10380780e08090400714084602816441080b80402810a200c40001240c000c0050700820782220342e90a8030010703900310003164036010000d0203040e51040d10f8200c1c0c0c0c00c1400b4011000f655000141a507465001000c16114005440322420580203803c52200d1040018116000580b0101911a01509010040d500040c103603c10030b0003a9801300303a000d041d05040760319000040000d844e160034900184c0911010f000d41905850090020940c2c0340c00007400d007c844070303109186540022042001c10130a1800800702010504015003180000740c82e9643d41074000c0c203031200c00c440b4001d10701040c0204034042c010b000c4582c400703182a0b2000309480c20000e5865002620b40700c217026000384c62000544032440d40c40301909104107615004c4000c0c07280da1008105125501303211070200500403030541d0040304480112078100c21240010380711905c030004440e000402d45d220130802001401c00d00d03408810409840000752024100c078180c44002d075941e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 216132194 1250 216130944 216131017
    0x140c071a0a1106100e0c19020c1e0102031c09080706090c0603020711090702030d09110a05030106030302030a030c180b031905060310091a09030a0f020d050711010212 73
    0x31074010100300b00804413040c48000842d250a8000c03102c1c1d0319404c1142440e81f08442000304034000d040341c0d9400b803640001c0c11451a1310181c0d41000e00c080d80030051070300580390940060040c0c204101e40c400304420020300c001580c00790840020100c07029501d8035a29401200101d81d59605d070300914090100c0c24040308000e0280d803c0662034480300ba66041c100e1484081e070f4500c541d000c80003040c0f03120700c2003041d10551000707500c0810140d00c180c180107071059541420b0900c07640f403010012070182810700801045036412380003981011003019041d8050414140b62a08102114018a40500f415500d00c00141881e086030350f580ccc03d00070010700141000c0c80342170070001d00303110900144e030302d0010f0b61414440c01c0910009440c0702611300440b1b28807407041109100351070f07c001e1020008000c4012714900300c00c1d072154904000800b00690312022911410400310394140098404114115142030700a8014416200b50b010b04061400c19030f005038401c40c24a8200d0080c0428007003480e040c41c1207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 216133444 1250 216132194 216132227
    0x19090906050a030b0a060902030c09090a150e040f02090103060507030506030c0906040f020909100501080702060403140d0f050708071803050607051b0601030b0609060f01140c071a0a 80
    0x98103010100782c0a00c2c0a20009050059400c006107040340590702401c06002940000d41d03030380c104501c07001c03415007012044901c146a4280401c05002c1c441c40340392100c020000c9109035803840c1030034820550350000c20594214114042c0300f80143d0712401c00a018510840000909003801240101200d5005000300d019600000106103541d07210f500c4107038400011500480d0741414408240083e019440300d890b0058451014400b904071106c221400b61750007a41d80440719594030604a075154030030b43c2c014001c20b0b0185a08211003641000a20201d071880b50007207411210b03903018504031075003150039034001805e240a000056034000e008030703200c0780305241d00044c45045880c0c1c5920f030500070301f0103818484000f640c10340d03030845403022003903200c042020b8078503075030303413030820003103180d4112203091060022800280c454940704d40c030300c120fa05040c0d5910001840c030200c0d9412503440004003890030300c91218002070502c2410100d85891008154298580c80c05030b901500c00c2d90f880c2c1d041c60 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 216134694 1250 216133444 216133451
    0x14010b0313110411180f0108010e01150e0d030906020c15040b0304050a080a02030703030b0a0b070609021311070c060906020a0f0c0b040e090c010302090330190909 72
    0x1042168041d40c14102500040c00316002c03984400014020020300d000c15a078807a0210f4000441d0481e60803503404404240c60108043d81d40400446030003200340141151260076000601110503080d480d80302c403031240e050140070044c20800240c1144501e80c01180015030420050204075418004010f101d0030560300c0203080d45650190020750300a40c0214072000f0390100001e020f2140810500000035000320150b56078211b80c2a000b03440e079015000035030100b81016080401410242d08800032038440801403800d080299a552000c1d10070400c050b41d10402000b840d00c03030050244240202c00c50f03c100301079580d800d240b61007034042400e42d100c074090000101d0304008aa401007180101503500031054410404d007482c00340c08000e00c90b000311109490208001c2800b00c0c0002215003d65040c0c0f041b543d40400c2e903401102070388207031002070380c1641001005030001030303180040380001c49440500e41940c0a8103000c00c419604001e80300100c1c2d007003050300ca400d500d8001450602030312220741e090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 216135944 1250 216134694 216134701
    0x90b220902150a090302040902031e070602060c0703050412021807050706140403170a0204030b0a0f0f09020a1802040902030a0b3a0602161407050402042301020712030314010b03 78
    0x44c005289901c0042e0156444e4004a8110356040c4043d4800d42c1071660f0b07425043c0180c80107580d4540f030380d0040b2005446824041003170300243d40700b6500e02070f40c9650341610f880d003002032600400c0c1c3d04002c100d8204100c400c91403d0350b40c18881c442c0c854883c0e1b50b02c25840340311605180c002e6400300c40c0604c021a41901c140b00119a001401070100c000d502040b10301030701d1b1055000000d21440c0e20203411810188103001d041003c9d500303da0600000f00c90144040000350610320100c41400e0700095003e0b450040c2003195080a11030040040541c01005061540c0c0f28034a6040c0c1e40122003074480c540c0e8441910855150901d0308825181e03101c4000010040034412804d1000000d0b0540110b50300e0040715041000125012100e503e40d090207000c520b01903d182c0082c1444070b41100c00a2400f5200c80495641030904c01da400b11f0310031040f608041c1c54001070b40980688103100c1c4a0450280340c401003101000182c2489819220784d0700060300c01941e80c43c249080c0c80603049400e4035902001070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 216137194 1250 216135944 216135947
    0xb040f020a02160e040f03050c03031e0108060f01140310050915090607020a0303050c0c0f07032009010b0a020a0f1401110a02100e160306090b0106020d09090b220902150a 75
    0x6035940507900c4412406c1103400707402c0070b4829002da6040704071076110000422102074800d041e4140082c040c0c0d500d0103034036604e07402000c0d250113007100c0d40e105004002c00100a02a0303601c0c0402d0910601409448a4000700c5081070706035a4110b8081038268420081d98280003000c0c030159511101481c081d05c12800c00000003904da022011000e010191540041444001d401c07003140e0000c0c2141007101c0e4041c00d83d803502c9032180c10f1488240c1d0140c00e501c1550840340c0c1c4548404249940007032108541e07a00705607680b54a41c00614a2030114401c08181400040c98521822215806000100f625000c0c04c80c945094a80700c0c5040e41c9034000910840e0345680c2c0006502c01c0e044899070010a02c40c000300f40031031408101d24051201505c200c40c001042c4040350703019a0044e07004031001c524aa0b00e400c2d060307035221fa4032100000010b0010400700301d074040b07a600640c030f0550b0040c0491009113030041080c0c640025008101c8807107580f00d507503070110b1600c000000855403112110b00d0504c440c5040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 216138444 1250 216137194 216137219
    0x5030c04020f0307030b15120f150a0608040c0b1210060e06030a0513211205010302030d080c0d060b0a1106061c03020f01090501020406090e0108060a0e010b040f020a0216 75
    0x901c005046d02c62030905050340d00c0050044500e05008078450710707203424000c0000440400c1d03801c1542c0184240c08182c6c036100310f42c401d01002034064006402c6520b458000c0b103581c1c10040c0296940f5100e49000318401c1080303002400301d9513650000000900382038000307204900d01c943c0044280000c0c1070608240d81c0b1000c0a4a0340021300e49800101703a50b80710703140c19544000070303401080c43d0700b1010300320324038407c5000c00c10f0204003d588003140100c0c41300300c50301114000c0c003000e503141d80402e009200340751060480e80d070305c00ca88000300f83c10002810940416100d441d040500a004040750030148990304c440002c14480123007008040798240400420700c42d205c6056203400003200c901a69003071600821004908184290007001224030b0360800c103000350428003c2400003030050a0010340d840405480c035050ba02c43c040034019603280c03282000e00030100a405038a003552a01300c130580c55a6035102c0d02c45902d030410000b60f942c82c000c18009060039030b408054595821042c0007840345904806 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 216139694 1250 216138444 216138451
    0x42406020d020618010e010501030615090b090a151205060105090f10092f0409180302030901030b0a0b030405010515060708091302040308031003050606040b060a0f0e0a0f05030c04020f03 82
    0x72404a03138000000da510302404400300200925030030308000000b04030942c1c2c01102ca0b5400d00751503044440d112110002580c00305915194040c20020101d4441079a9600841020390200410ba200c4d6030340780d0512041107180c40d01501c07660021401001607041c61800194021014501981035241c94044003d01c1d080c64014811030941d140e80302007404822507074075000c01444000c803508590307001442c0040d990060003011145d90406114205a4041c0303400ca446159061b00a035003024242401100104141c6842a921500c1d0b4080040d600c4c14280040d17008500500002c2b502e450810b00c130a624400302681240544010807910340440c9200059070302280d422920000000384014242002e40115000900340d13060000910511810708803d460449204000380c0e016640c90904000032500300010300e5401c00701c100003240c070b01e500c101c041c44010000b40c101a811880688041011040150042c4070076404101c5c080c000c5240801c000e000380d0308220380a500c1c102840c43c1c1103c070f900014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 216140944 1250 216139694 216139711
    0x31e04050319051002040e180c0a140f04020d050405060f0c0f03042a0f05040204051e03010621030905100c12020102070f03080103020f19061409042406020d0206 71
    0x3030414000300282400086400c00b00c01d48155180e80c1c980c44984094042510303601c40231107840c5080d010100380413684d940a142c00820b4003201d80c1c9011026901d50015001c140d41c803060758844240c00e961144040d00703c248088400140c83d19141c81c0192410001401c034818600f080c0c420000303602050303001c4916900390214030a4a80d02c503490319002040c4802c0410b003d0003c80f4800705011181480443d04039200c020090b4862a580c01c24401240300d18001c1c070703400002c0b5852010698007100c80008000001030f00009509a03035903541440055400c0c0d00c403010820500c000e6040c15408217460014100071101c9804003c1c0301200604110079440000b0203c000c5114420f01550007035058900e42601f00c092068004024500101f03000002d001c101d203d01d011780c1c007034070041c03c00ca21030445a1441c4c81203225801d00701282074402d02484440300f801c007942046130361184d4642d801818201451082d0707405a081441d5101c114110451f001174003154060654a046203600095441d003061a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 216142194 1250 216140944 216140983
    0xf090c090503060112200a090b030a02040504081306050f03270706050d0c0806010903020402031f0902040504061205071e090207120807030606080f07110f031e040503 73
    0x1486425034900616038011a071502615000050015000800c00001c0788036820340541e03c0301e004a0041860640008540c00500d403400501c060603261b4452010f50000a080320518603d42d4001002d442d0200c50441d0040740c0441c007040c24080300003a41016141c04c3c1003c5081200e104415441030000522442c5c0110000740080d243c07520340343c0054105110354046e0389481d6110b9101074416880030040d0408030f8a03083c070050a0034807400b00c1c113003e000141e40390482d141c69902008044d40001d001050740790100c602501050582214410040502c0e500150f02d881c9042c04100c03c44042d6442400e800403a880d401000a0010030000140c1c0c2c070011552038604e10b54003404c00701c3e420369000000d9251001640c8424040100c5880c1d2aaa01c190b5843c00d00d60f1314a182181511454421031010612150229a1040311944241d911240303502e08000100300464020789000c592503903820b0982c000207a005507031002c0c40c1e03103041c4501185501c00e15041c5000302103540c3d003030a034030290451502c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 216143444 1250 216142194 216142211
    0x1404050105090904061416090e01050f0405041506080f10051b0304030504260105070212120c1e04030510051021020a080d0806120619060905101e0f09 66
    0x3c95070210b114810340d81900400791030511849101f0b201105d1400000c10004030b40020411801200941a5100a807062800c60310380e905000141401074012600a04040d0706450f00c8145441200000c00c04c140c01406500c40300e02e0010b0400000d0310603030750900e06180400200d1120401c440e8030716440c0d0700d40d06540341d682e41803c45140c0201e07045030450b9011012065540e4400440c0300c1030380511540200610340715414160790b101010329540c10314040601503000389624070600301c0c1e030020034220a149070400c64800708004030360351601c01290550220701070050010030010403686060201d003c01140c203001c40708841000a80c86040300d4507402540088008400203840c88105901a01c0aa5001d81b10400140c44101c100d1014000505880c0000c1716440c110045000c14201c10380130b8807007501c0c1d0140418401c419000e18107000e47d201d400001e1603204910a091040200c560170409060034040c2440c040c550407441030390b100b032011500380071200b001c2c190201100d2042600044e00314 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 216144694 1250 216143444 216143453
    0xf01050a050f040b09040f090b0601030207020d0516171b09070318050d1d0607141e01020a0f020319031d0304080a020102060708040f1e0b1005011404050105090904 72
    0x114491203400103002c0454001541c0300480003801c83d4001c00c0310203204a107445541c520031184034080281102d140c1d038020a00f2540668003c00000d40003503d0900b00b400c56132500e91034060246080402409083c50401c034400307026505084940c51000034200303000d83d80c102c0c40700e41c0600500103407051004002241c00d03940607174010391a60f09041c4111a180c41e4908280b80c541075801c2c0d025012034403400d80da000001006045000c2840010700c480d00345145034480d00d03085030258038903203014814504600300350150100110112501d050016070380e155100c80003803542c44030440d2113081d548140310340c46801d42c000c0c042c01c1c0f0b1086c00d8a00080e90761440340f5440320071101140300d00300390300000030041100d41000c904001ca940c005e0b001c480d000d0702ca0040480c2c20702c5040f2400380c01105035800a000050702c50301c1d03100303203078010150180c03d07030f042e5480742e959084083d52a80500031661008000d07658001c8948140b10b4010360311142040e240c8000a05188034840c2040e1148441900003800c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 216145944 1250 216144694 216144697
    0x603020d080304052104152d0f18030602030408040b0304050a0210090b030f0c160b011508090d050307030b040203070c030f0f091406070f03021609051909061b020a06050906060f01050a05 82
    0x4040c50000000388c03040005840030b19800503003100c00144400907640c1039180101c0d004c403202d1052030034082070149980c85000003904094802c0352500803c00c80001c040a100010b580110b001d1800703407580402e24410058a450400e04807000e000140408010040b07481096a0744010344803614512a5039070706090b001407182038116400500106011810b000304068212306860031000303146050361617810103640b102c5081312111082d5000713004c0005058424005141c004409045c0419001ca54078000341c1aa00116003a0000411680d44001415031110795450241c2c10b80c10181e103400507a80c001070591589010b00e0100c19102d2001c10120744503c2c0031201c030329420a022070600c5140340b070001c1d01d492000d00c03c451207030701110012803c00c185104890250310146044c000040c1d11148480241440040030b07a01c0d07130345d0fa4403010091040f20100000300d00042d8081e042c241c80c10b2030000c0880b000641103603460750001080000703d45540d9400760002c102400e140b522490680000c8840e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 216147194 1250 216145944 216145967
    0x90105031b16060608010603050307021e0607060b100807020d210e0f16180f02090d030819050f0106080c0409110304110616020909010603020d08030405210415 70
    0x108000003040060380b01020352000c81c1078400c503014030240f17a07101c01c0c46003078034814007014050b5003080100c0c40c01407070040000c0c91192192a001d04691031613400190898111200941d13250fa01c409880003140741044030000c42054a090190090610b04c1c0c1c0250f948640705503281c140011096540e40600300e004c039603440c16003203120a21965880919140c0c54603e04400d841c114800c900d00250940d91240611054070460190740041c20307080f48030f00029288000320207800300c0d420001101c0a840d81c1d22001090f5000b92542c080da0b0410341c3c40c01d20009480d0001030000307864007082c40000d90390300e009141110058900003451f074450000740c03400c031301c500e9000c921003e251540c500c040341c2c1560059882180144101500c1c1c3d01c0190500c2400c0c403500c008030300309042d03a00e240c00051420605003034000d0010300000a03001e44a5020441d100c031040819925003102008100810204000d48056076a512010000e219500001c0c44050f010724000d886120050260546055110f04096a03a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 216148444 1250 216147194 216147241
    0x390b0309030714160b0403050d0e010e03011416050403020f060705010e06070207060206010609031133090405091c0e01050706050c0904060b040602030a120905060f100603050c09010503 81
    0x1c004031000c2d03803540d03404450344e5a81e8080caa01d01300185942070340c0103440c1203070341007009070448008e1349200301d03002ca601c076041a040c400c081017440034545091041c1c039080075640700c0c501d03000d04003e210b078204528007400c1c00e400c2010401c0184016207441400c1b084c645026150030341c541c502d40c64041d02614480301c1d138207a140705410421852039070006801d411500da68090f212281d803500030031a21a251400060203203c60302e41c0c0100d8a082003c1242421032520480d00702d00b0042180451601c5240141014142d0002c00d00d800213141600c90aa042403130500100082c1110041c0c5884600744910041c00388400364078104801d90003a404c07901c403141e1000d8100300f0787c85c00c004814659081008614091440c1060200f4030558040440c3c0584006400640c20410100c500320340c051384803924940c0940d207550039403000880812229029220103010004640303046404130001c0344466214204150401040c03080c0e004005088a80c0e1000070f2030002c1e9a5900d81a0741c02401c9030280d0b9110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 216149694 1250 216148444 216148463
    0xc0c0f0c0b0c10050606090a0e07021c020318040c09050907030b15030a0f0605150906130e01060212040302010c0807021906030f2d021b0a390b03090307 67
    0x85032240410f40320141100004108080e840300014096140280440030b42c0040220006110000001049075846601441145c5e250b0404400d11454281580303d96401743c8e0010403403600c80f600c1c1c04ca0004501405a40030007941642140c002d18200b55807040307074050b0384510080b40744c580c0300f60044144001d024161480804a0803210a8583d02c11078000300350b2031508403c20030340002401120111507005101503014030072000400341300d07404400415031100d0b0402c454038803000340c6242d003001407142c41041100d0b90315002010b41030427041c003000312a42a0030407042c00141e03088000502e54070b4000c25100d8480f00c0500c0840d07e0001039901c034600c2402d5080340000e50542c55013100b00b0710303621650240031084000b460354074203034089050342d20f521080a60b0010b110f41c456000d00f0121032815403042c92003c45001701381c00c0c00b07209001a10030010079004940c50f0655640b02c4105941d40780c3c1903c16044c00c100ea00000c1c0c0c191750169007000c0d00700001049901d0000c20a40f40d00c25084507484 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 216150944 1250 216149694 216149707
    0x512121e070b1012051b010c0519021005031b0f0c060412031508070506030a021201030510060b04050d06200d020301140306010e070e010c0b070c03120c0c0f0c0b 71
    0x10030910300445008140600483c0c0126143c0f0110b4941e08240b54400001c010304420741c04400780003c00400e907a8100b0004425110100d842005282d91400706440c0c00e00355907440d4014005100b2070948182c06010081041c072200c00c2c0300300701c110610360007100200d4803002d4007a0308050a129107203040e250307886004207100603c404400368030000c2159403001c0182d01c0e0030007500a00d02d151441501101e40203420200604c2c00d0040055a00c4241c501005150940310801d2041041e000c1e0000c3d01d10703611004070305940400500c80c000150099981d49401c06107048005000844501c100422407a00d4441000e600004584200502001c07003040381e0b206c4c0c032042d0506000390024030400c48400d244942201c0c05040100c0c001d410b807001001c0c4103100f6030301c09034291100c1070403000040c104214940c0040205941c0c0b040c0c03e01800556131803407e450300d5810000c110b1104032a401c8032843c0b0b0305804000540d0031607001d580a650004140c194000319081403c88203801d41e00c408081d107400603c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 216152194 1250 216150944 216150953
    0x4030504090e0f070501031e020304080705010203071706041a060c16090218100207030f1406010b180405150d030201061a04061205040f0809061905130512121e07 71
    0x1c1c5108000f10070101e451040c3d4072401102aa410090700c40c151410301c40300804403441c560001c0d41c0c45400780c49068030341445075880608a0788120b94510000b2442038181074075100d480795280d04590110b50520280b41000c03400c102042d06a0503581c4a040002050020b511092040344180e12005800d000d00f83c0e690801c000c080e5012101e040c0c101503e51a210300300b13180035540104502d45e990700030b01c400c608503540c98251042100301a50410741140e00003948140400909011709589183d40c0e45a14440c03c0343e0000d00525440113102d81c0c20310b810042d400390054420301100380d042b02c8462000c4000d080590040159810840501c0e091029100700c002440005100321901030740d90b4100c10000200d0307682150002c1d40c1c0202910101075031100441c0c000000b500209000801c504c3c90100c40f142d01c1680c03c0d01c6c082d066004610089030711218600c883c40040024203050381e21608600e240510a81c503040d2629078040c03856030128200134007034005600c2d200c0070f4509921855840495007003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 216153444 1250 216152194 216152203
    0x12090c060e090925180207020103060b09030d080606040906030b1f0e04020f06040e0708090613050303040204090c030f0302160f0b093109050c0d05060f04030504090e 73
    0x1a980403400c4803007000c0350782c200b148010b0300ca0800d00000e0208104c03503402010301003034909100644202c00040201d88590f858102ca00000b48074100140e54804500c0094103483c125400f19140d00b205100c007150380d0302c000c26070f1100380540f450070241c0d56a510b4002030b0280910b8000380c3d902ca107810008810008034801c118000d1200c21703054000180c0e022003a140104541c01420004083c580c08100107040c01c62107403108101c010402810940c6a02c03203484260001c44004000841e17202c10700050030414050540c0200d902c08406585e01440c0e2031780c035500d20003c0c10080c02142d0b6560028180300c100819540550313840700d42c6003001c00030790400960f5400c0b10b41ca001400c00010400146c0f2503800b071101c00c02c641100131058106900b103800c001e409525004e91042c40442c80c484100c4044803601c0c111501c15803940001003100c2c0d0b80c18140c0c40c0074049584a8018100c05c401e00001c5800007908580c0045031a282c010b16035130390b1500b1a400c2c0200c0c1e0000c003509043c0b04181b100c5050105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 216154694 1250 216153444 216153449
    0x70c0309090f021e03240301090b07021e030a0504050d0f02150a0f0c0c05012304120314160f050c180a051608072f060405210d0c12090c 60
    0x1191080e240c80301307050310501d41c401510911440302102403a6001d80440d00511191040c0c01030000a00d82100c1e200c000904508580420041c0c000d0445580c0c00c800040703041a50302c5012004500348081c200c0c010300310340705034003440d440b50010541050811000c00c1100034169400b40403015812152010840c003030300b00a46c1400030825144588031200e01c6011040080c071740008101580300c1c9481c2c0190b0741ca039009403540405200043c58035265039003070401000280b5100c0c421401400c0241002810f00024a846403040316081200560a10380c0d0024a80c100e50072030040c048514062914918010725401c401e03411035102c81440d0b03165035115051603c1050454814041b50f0786250310003c81454111a2002040610b03010507842c621901200310b40401c41191110884080d0a041c55507031255042c00d1181e901c24020081041001d110500490b0841120340c046001d106e82c0001e102d01440000300038455131400713201d079440d10442c803482555803040340c100440119800c0c00e50305c103200c50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 216155944 1250 216154694 216154717
    0x10f0218011202030601120504060e010510050102010e1c0f02160b04030b13031707030605030f0105010f0b130303030c0509041401080c030d020c0d030903021f0e0402070506070c0309090f02 83
    0x91001c040040054000c80c2d104485c140c1d41e0340e0914014503510002402d018000740c40ca5607039802c1072400c1050901c2840d00507035096508000792072a01c00028251100c0d54001400c64014058410802d06104050cc040c00c4050602000200c0076400482c581206406100f0074030700241c5000071004611001070059070b01500c5040020780d01d800c14243c201701003200040000b0405400d02000d00900203080c1d411854034034000c0f450036079a800003468039854050140043c0d5413180101b00300359013200300318010306a6203101742c24072000381002c1046550380d110290515403106024a0000c1c45402200e002840c001c0003081240100da02c544111a000d016042c80c03403103000804000391900250710402c482c0998002d05403407064000340075054001c80313401c0b01442003620300031005a684220381c0c1c0d0b280b86440030191f910030808100500400c0e100242601503481000090040b8801141c05a449030003820b02030a1714403d0326080741c80341615407040a41174904038032107946010540080410803082c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 216157194 1250 216155944 216155957
    0x13b100501060906210504140d020c030f010606091716060c0b01060203090f0625080a170402010801030803070c0206130302090109060b03070c060b040906140a0504030e060903010f021801 82
    0x1c6880a640e4104401544092176404000c0f2680c640c500d6000154010f206450b0080d03000e070220a811b00e0701c0400416400560002000030085080c100071500e0081d103900300078000140380c003001503d8080203000e8074028102c94650000d031540308000025808010307810360050103986060040240000f018111411049000002010341c03000098482103070300100a1314610207100300304016a071120120880840c0c0c0c01e40c00c0b41881640c00d00060b20356014407003d5070394054201004110100d00402c20466103030707010a000140c0d9100581c0380c19280e020700707000d41d252115401900c1e45c600b29940258403000010301a100881c5070880d910487e44255120395407039032980ca9079000d8910034000c500c0300400900c00907295074440c000c043d03113040c0140d1780020a66558404101561910b8900780c6007151684803000142c1440e13420958006801c2008100c82e080581d0b00605a0030240c24082c03180902048c07101c0c450750300f94031000e075010074044110354640c2d03412002c0303105407000c5082c00d010418 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 216158444 1250 216157194 216157199
    0x40b09210615041a0901061b0c0f0f24050702031603060617010203060607080304020a03080706092003150c0c060411030c01050a0c020603040809030d09090b03013b1005010609 77
    0x4404024602d502e008103400320036824004c04030340101c080b08c024280c1c4c5200e6007040303011580e91421103021b00848090030840c41d0500c036031002c410300e16074084503d512041050798182d11800304c000c0c510144900d0495910005400000e01e40300045d006000f445403555800010000241e10510440b10210540c40c2c907400c642e03242608030700084500f035030450410006680054942c0004561140c03000317011a24040d2661500030040e00400380480784281d4441c401c1040c4010701d00c10710030344e0b140550b00c100c9615031070010070b13107a0028a14081004040102148907490301d1000cbd1a1050792140458196151504100300c1c2c2010101045010340503445244809500c954200d40401c002c64403254000038096090107070300e6000601c203482c004802d000001e480d540500180341804019640c0c851182d0402800400b10b0b01101e00b40c0d4031036072400c0a0f060150000040a030301c0034111240b080c1c203807020781e10151840b44c5610500d03550317070041580b40034040b00107502c82416508543d440c80300b80ca8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 216159694 1250 216158444 216158471
    0x150c030e0106060c141204060f080a0606051e1b0304050a0e010509071821030201050f090a020f0402161209050102070308041e08061905060402040b0921061504 70
    0x14194052600020400d182280114100099140b205c640c0c0004959407400602c003291015045600300b6000140c4403401c5401207a40818083c0e0004a00c40040003003900c0e0a40191407031040300c15040d140004c1098001d1010b80034000d07215900944002c1c06034405c2d4120006e5201d034400c0c02041c0c071484030b602020400d00c01020859050791809031005d44503132200f039402d031501102c0c0075000010302058030000c202001ca080404980d03012011260b01415810718029095600042c0341c4c14006030200100320320701c0c3c0009142c004403901a03a203800c45810070f0010502078807621110901c905111180c41c001c0000703106100741010641d6480080c090749a5004a849083c00e100160100f0003d200910110708100c1e9503407042d548010904030500d58801542e42481000c480d412500c5212051021030000580641035000901301e404500d094180591a030050140c4e806140c003c04030011100345a0702c0a500040410b0300c4202250f65626003038868a4100d01245121800707a03080854092070107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 216160944 1250 216159694 216159701
    0x60e060601121a040f1d12090d0c0f15030e060709090923070810020c06010e06130515040b0307050a06050306061e1c090c0e060a09060e0114100509040b0d150c030e01 73
    0xe1196007003091600080d101088002500325006079070141c0ae42d00000b42440306c80e40803000400540382c0c1c5051444807410094100c4007154619071741c40e01301c44108610258402d182c142a90040304000948016905014003110b06d0090707950905c6442695510f291080080c040c03084500e00401c86032905d2002c0955000e03401240c4428185070701c00700050148030159120254041c501a206001c02e000c002c4482c03040c0c2c0c10682e13002c0159280f109203c0f035207060034011003240810507070040c00110729010114078504440d02c190010010b0201c0410a50340d2800c007241c0c480301c480300361211404034001c4a03041d1548403800404500d451a10104090100c5004401d0314542007202211302d5458000808004100100b410f64440c3c1d40420104a2541301d100e16000b0780010000281507604142c11034051896841103070340700c0c3d11004615003003641d0010490320081019180032a010540d880030076840102d103030006018114174180c0000c07502d01644040300220462b41c00707022100d002d1291b90300302e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 216162194 1250 216160944 216160963
    0x8030f1305150301030213230105040b06041802030714070501060e06042c0115060c0512130b0c010b0607060f110309102a0507060e060601121a040f1d 66
    0x4102c0c18001000985010014581183d00900c00071664984c0502d40804c03203910340d24640c043c155910014007a9043c2403180c3c000040b0123503000c0b8506420581d1410744410b800e0035160300b0580000010390b1003842880841c41b50000c00000c0c5441d102c0314035100b4040d01640c0101c845802039400000e115140c40c3c09121717000030140a1380300c007009500c2c0140d00094100c440100d500d6488200a56807190a210b403080206003a5807890344201862030901d0a194038401c401006050920141d1000360f80d10041a0485002328121586d805101c00000d02505c018440701d940418080740602c10710441d50800300c0544d000500802c0284818624440103000a6940d00c203158825030107200324805a034042c0402c82d41580b1a561800324090041a01c0050000000005038012841c1410003405000304034551140401410741d51405100080580040c0300032182c40e29110540074096414a048440925202401c02d104000b0244004805001107100c3c03d6a03245501c000440f0018002c680310f0b01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 216163444 1250 216162194 216162229
    0x406150b0a08070201060509270a1a090a02090c1902010c020c060a12020712020f061501120e01060b090f0102031c051902071110030504050a031808030f1305 69
    0x28600800380840d0707a9031000302900c013959a035101c0410541c0d030329a1060310510343e075241100c40e840d6a2400b41d407481c002d691110302d5644805085400260101c051145040480c070062550f80d8600b01c140385810900071000c6d42003001d810600c41a0401180201a80c1008115039009214400000c078200d540649060005030400c4010007100d18002c00203040c00c484600d404440480c00800890882e40019403c8481c5034003107640818042c0c043c419001030801c0f03070015000360b00e0003040d4000040142900030341006411340d80003804546581c415050b840121008110303154071340510019961110740203501c00c1081c6444460b26600c000300312030000e2400038801245001e01040e01000d000c000d03100c140030511840d1031102043c00c5101406115024203080d0003211201024040c000100b192505c0c101070170b110070480410000151000010343c14904554a111000c100c4802d50000d0b42006c84140400244541c2001c143d0b80903008080c0300c1c1a50103800355035030081003054602540c1e09030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 216164694 1250 216163444 216163447
    0x3060b010203210601030e030d0c02061b040b0901050d02070b04020307050a0810052a030f0a020702060319060f1d0a0213170a0602041d090106080a020d060b060309060406150b 77
    0x4a8a6009030f520340e040041810003003001c040c04158641990031004012400130b03070b1481481c0c24180d040240d69044451803210164043c4ca401c200c3c980c0b40300c0ca029021440100041c0301c1c1c8142d1090302194121005c0c0d031030464542010f480d12031480501560264424460180045011310702800c1d08822600d420009000701c0b0010103019000d8040201250002404c0c001d842c420069414041e03a24485c40451460380d91174010b00d420441031010b410002094814044000161a046c0469806c4003d110300304407103c01045040c8050501d0303800900c3c0d4405924000200d100c0006140240701c160760b20701c200d09540d0910404101d000c1c0c481c0c07440c8819039130901005500c0140000042c01210b850a407407039522562a84c100f607a03c55031000c0c400c2e03082c0408a11a411076107a229401a49090080c802d41d450445c100f542d48100781c800ae40b2486860402d2001c020490f84200400f210113000d1765241d1a20310101901d480c030032601511054181100c68541058030020790302940d801d500400d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 216165944 1250 216164694 216164737
    0x80304020f090705160f0611030702160608040b060a0b0f0c1207020f0d0507090c121b12020904020903060115080702120f1c090602180f0a120302031c0603060b010203 73
    0x7a4017030112080644840034000119070200340c441c01010462004003080316609c2c10300100081c981007054a581800c0744202c802405060343c0140095002900494651000c2d110540001e00c01e8020341e01c1110700342000225520030548050240840c0c4c040c14064030301c0c01100b0f1100e08800d20030791100039070050a000003003100b803916107442c8800c280640e084030402a140c44001c81128008038003403000c100c1044ca02c00c901c01031809000c1b0304042951010150010200c406080c0710000400e02101c1a00420380310110741340ca84c10b84400d803d005003202e01d2560369084484070781c0d0310115004001890180002c41d00c0340001065018440c140600900d415961400404190849603c41c44400007007094012800d000e0301802107401e0240500680d11a07413070001c0c0c0c0c030303400040075070350701803503e109030761131641d60345600781c411581e0522104242080e40e140c1242507210b2103542052010051400107a2910385602440030390b44503a40400c500428107005aa4900420044805140e0152201c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 216167194 1250 216165944 216165967
    0x910030303021b0d0201091118190b090a060924030f29091c0509040f0e0706120c05030423120c0a0b0105090903070b0919080304020f090705 62
    0x3c14001c40501c4218a111012580081c1400090301c00100140e4440203020306101e0011402654844201c41c5000c410061120308081c14800500c3c001941e01079201648454400d0340040e000844010b1403102c0350715007400164000c2c420390040c0005586003101d0b09a503c0344082011640b81c19004811000c1451661445010041e15200311165101e580d00302d920a8401c1d00808450441c88071104114945425040c1c17030320b0484100c0515144030001075145d040d8022048451416080ea004a4142050083c540140801c1103201826200d8240c1c0012180e5000380c5140e0201d08000301840f020700f40840c01c540340d000c2620080e08032000c0009104600c2f403c40f0b541005844541c0540d1001c4925000804c001d030440000e4031921303001803101c0310820038010102400b42c002140c00394007509014443c00d0b40ca011b4070307600400901100c1c000c228041001c100311b200b2100018914190016140391545003500140d408074013a00d80c0040480041c9001141180310f612640c0d1100d0810154968 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 216168444 1250 216167194 216167197
    0x102100f0204090f0f0c0e010905060c1c0c0311120912070f120c0801091e08040f060302040312020604110f0621010312020a0201050d05072006070e091003030302 71
    0x10a419016401c0000081c800f01e0760207000c9400e40300d441e00050303141c0f0801400c01a14140a82e44040213003d54044541e070783c020350410142e910a130f80d525110403512502600d0207a140182c400c490a0400c103082100b0307441814500c05912075698002240b0740b100309555188034545c0203000c0b0038820300403500306007000143e181d8203003100380c100d400280d65902094803846503500002c511913040d403081403d0108801464008100c100000c01003207202e03441d000c0c0601d014510007c5003d1800044805104030202038034041c01c01201d05280e4140e0f0b80c04054000e602c18482284c401c000405081c0d140c500124800d0f10894001040c0304085041d1010401c00e43e444505555000005002c000d100085603210040c024000400040681d41141002400101c81526000440d44000603060050340d000041c0c440e801c1b14a9004101c6844500c400e5441d038400100c102d491b8401075020007040140010700b170b4040c41c001d44942c0c0e04103004070240040c02008442c1c0c403c080d40e2400c01000007034480da0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 216169694 1250 216168444 216168461
    0x2131a0a0518210c040b0307120f020109030c0608010609080102120103060e010e16031103030325090509040309090605061e0a05090a03060903080114011b080c030a0816030605010210 80
    0x2000c6800f2003a40c40c4035044041c0a454680c80258001c0450703d205040510410089101c110000d0aa251416407103011040c0306450041c9003d0180c1008801c6900640304200a5075200c8056113505484000007000d120092044400040000f000007640740d0043c422603440d104100400c1200380e0841d100c0001800d400d08604200d0345d82c0e84035501c000f00081c465403001c810f0130324240308500d04d1400c042c8840b01178201031512a030802c0041c0001180003030040004040405903912860303005042c15509602650b10154100796810200003c040e80400700d401910f40d8100c040003101c0d26041800a94000d089404c400e0075054009500f09900c40c9001d810180c038a45031030351503e0f443c000421000d003100d134030450b0907030748401c1342a0070990080801400340454484000142080360f0000301250a40d0130782442c40e4446014440510840c1c0c0b0495000c41d100c1001c40c1ea4810311104014210340d4125a800f2040000350520011240b00740901c40403120140c2c0141401d64503100301a006000d900c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 216170944 1250 216169694 216169699
    0xe0d080702031e04031202010c0206040312090b0406020702040609150506030c0d0606090806090a02060301050d02151b0708030c150c0c191a01081c021002131a0a0518 73
    0x83c03040c141502503919070f03d00d00b07102080c01d003030312185180b41ca00800e07084800d10b00190390400c0c80c81d1035001e0b03002581c0c0b030b40580c040c98603d04d0603165103100c0d00149030186018100c80e15000800003442540c0d001007031528400d45081200c15920150041100c10510307007a10340c8054440d0402c01803900e4809140c00007c4403501618000841c01c40b5800c031001da52042c004900104e008108501007449050341c48088138010b0900694958009000c07803005000f8240300d00c03610708000055441e0f907442051028580b01035566551a40c10380175502d050340c1c240c0c0c00f50328819030b2008546407002106581d01404c9120013001008036198640101c40340007044040c25040038071110004900400c43d5024000351482140110f010303904201050816050008550b104010010003441c1e00000301d03130041c5402011804114018400c08a08007401040703104c51450011809a074031003440c3c03a0711012102100030824905507000322040646c020021a00d010460910100381907580b800d01d50010103c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 216172194 1250 216170944 216170947
    0x80a0b09010501120e0105010608190209100507110d0305030603160503060c2d0d0e03130302040b030a0f0501060f060804050c010c1103060f0a0c0203070b130c05060d090b06040e0d08070203 83
    0xc017880142140e40c02d9000c81c0002d9844030031301001c02c01c0c1203840440201d0640301549000350750b02c003180802442d510100308000c800a1a04c0910400000400c04e40c10010000301e040285800c0082c0707075800030b50b4400d200c3c0c011410710710861020042000c044402c003070081c2176581d030f0356001100a40c02c10100525131202c80424540401291045c0c890510100300c1041c1d2a2070a07050420129147c002e2105955801040b040c81c0c01c130080c55492003101c1d070403a800300701000c500010900300f002034140140281007261040040000641100e42503e0a0782842d40d40340741d55140460b02d2000548000d440c58004951104455205002c01c1082d54002c03c07100c40b601d10030002092404008030f070b88010742101c0c4014000e001c5454050282c01c00c0c1c09200540c14600304d030300c540d10184400303495061080060810768013042101701c11400108001445641c0b586450692000644282c09044030701c00c0c5404000b6000d0b1a05100c0c1c0210260160001d10400e1a26003040c0e484010103000700055100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 216173444 1250 216172194 216172211
    0x14070c0f0e09010612020d020405090c030703060f050703090b010b090102210d0608064b01150512040f020d0503030907030302070e07170705090603011401080a0b0901050112 76
    0x8821900801026a0021001945003403400e19003184c4241c0c0198450002c1c1c02c0807400036940e1070340500800c1e1340460b0001880c1c0c032804540785c80c1403a10f010141c0c040c0a505e20000500401d40c3c012000494101010f1103682c4e40d1150440c00c550207403000909640c0318800501c0308040440180c800460107004942119291000c101e04a16175050b203200101d0001400d1600001140512401400303a4401400282003a0300c0150200c1c4400801490720b10b00c040c03000c02121800e00410405059600c2c49042c22005001d103814600350900030740c0c03162201594200d490354412002c40b4050760300d0750390400d09603c2d6941c84000003009000180c0e40403200c901c0c4d400220300203000450003124140000d041080c07541c5070203410300e40d646e4001039451002c10700304615290071030303840320250801c2c421074a025a680d034820388050142c464461f4001340c022001140a0024001030800c01100b62100da4055171603507100c000350346440545a801c409848010416540503180c41c038036640405101046404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 216174694 1250 216173444 216173459
    0x609010e1e0705180a0b01030902030c040b0102120703021513080f0a05070b010e0a06050d02030303060f010c06050106120e010c0c120c0609060b0f010801030c0e0403030204031416060c0314070c 85
    0x4c03940d2009010a15018081c403801740411700c145a61882c0c21309052280002c503400181d200c0724000480c0e40a40d46854200000c6c1e0f02c2840030300c0c00e1100900c25142c0b5900c040c20000c1d543d44038907010000041c5044007162116004001100c030380d917840207851386418504044080603411400c00d40003404028410f02c0001410590400d019110601c1c5440c068907080e07142c00c0955003d0390110780100810100719000da140801200d42c0700c0d1081d680314040025820048450910405010f0045441c020000ca929075204001c0c0841c441a80c005200004000515500b01e482ca6640340005c07a0a080094000508554414504d16a50b00b40300603000450b8442009985030758204407441399885101c1086071415040c9103460380c0c801c0c030f0101c0d078542c103594178840403615501a00c0103412040c00000e0826101c0e80450f0059680b04142c41c000c001044040e176986c05500c01a0761704607587d844e002c0b580e68441c0002e00c0805800d951454265503008103e10120f5100207005d8480d408000800328006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 216175944 1250 216174694 216174709
    0x60e060403020c13090312050c07051b1801051806030c0303040303030f0c050405100507060b181b0f04170703050304060504060e10080403050c07150f020609010e1e0705 74
    0x300d0003900a0303c8000d22850410160241c880b840c012407503c1d0146420100e644184030700c0301500c3d480c2002407280c8446030440c03000e0052000007805840746400302a6240f081110f0b5001d016000c0d0b44640041541c034422118042090242a410400c0c104590b0303818002c00754038503000034028041d94a0400790402203801c41d403080d0410340120345c0f10703224a4041401072184800c2c0c1551440d085017000c2c1003000007040d071040c800c2c0c0325041000c04035042c400d1003400d50000d044040c0c000c00060080d8201d0403074400c103980c111071000780d0098a0350207c1d15200300d03c0846100c01c102c100700914082c10f2a00264154041c4030705034400f841000b40202c00907004200030000341941c2e46030f454581d8a4414002c204060403031125006240c041100e00400e60041d54064005e68542080c1d0780743c01c0100e15071403911480c1e0b0300c9142009040011000f01680094882c02c0ea07202c0340c0d080da46660340703128109082e540c0c0104074200a5018804004034107509030306a180c401c4126065035a09650b903400920700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 216177194 1250 216175944 216175951
    0x20117071e2109051510050d0f020405310302030c070e0f0703020c0304090207060b040f0221090d1803061401050a090e070e060a08060c0a030c1b030309060e06 70
    0x802d0041c40c03206045001e034020703040c00403403428003800b11080c0d80d034a06490701c5202140800c0f00c0800000b29154000c0d4517421400340c04050b108030302c02c031180d0400380755641c0005401d034080c40c50b14011a000042c01e4400e0030b004441c1458004110122041040042902c02c5081e001c501041c0300c1c0034a020307018020000102500c00e1500e460307081c20108100c6001c0040d180d242030510401c54610310440100a640480b908450016210381d15414144003a00b4041c00c002c0d4030030710b0215000000342256000e814120362040c00e00241e58101840001c6100042c2c1d80c0303245a41c13000010700c0340c1070301c10a00d0414031100e00d114007034021780c3d960b00c030011380c0c010a06c420340c02c0203c9001070082d402e0083c201001403501d52400d12201c105820180c2c1c880c0164020a900c001560001a10390b480344440c24000340340c04030480348185850004040903811000c103420019040c0012250090b01c10038404034814903400e0050341d00d0300190b5050b40205800e2204681458480b0441d515441c0c080c0a203e12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 216178444 1250 216177194 216177197
    0x30e1e090a09020f060a08040314160f0519350c0706181d09011d0102090a0e0714071a040302030c1203070c0219050a17060c030103020117071e 63
    0xd010b0350034070402c050004141e8a590103940d0034801c4100c000e522201480c0c00503098142000c0d246000341c2024218030480540e20350010700704085c1d508010021682d508000d00403c00e40340700f07040300012968900c030b10f12009408095000f002403100724030701c5150000517900000700024a040303030113404000d4201c0402c030011074000c40003c110103074000c82c2251030014076015262200e4201040c110b03000c01708440070400c1103032050000f15080004d51056400c0040141001500c5117400c460f28045e40c00480621f01510390703140c00080191a40da0f5090103502e041d01c484400310303029201045a6000050207440300c2c1101c0c2495000c000751390000b180503078000d034059550703012900e0071940307405d0b2172800c1c0d55002002002040130203944900c0c0c3c03000c480e40c1111922400000d443c8001c03d11461500400d511619401c0002403480003031b2124020419a034094844135a5611240750b0103000910003e40402c0b100030105140341600003041e030780301950b4101010800c0700d9003040030400320314007600030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 216179694 1250 216178444 216178451
    0x20f04030209181c050a0e2107061211030c2b0507080907080d110106170105010807080604050d030b22050907091b0c03021c02100e010504030e1e090a 66
    0x200009060222084e81c0380d524031400030900c01e541c00140544901c0210004004000203e0302c200d13030b220610580882c40840141c24002489503519171240c04500c1800c0110b0034144912205520074069103220800c2100294215039540b0b00c907540c0e680c40610441c99a400701e940030b041d2080003480c1c81c030402c103190600080c14540208003a10b4640c0c081c107506d48075402080b00704010b810005504186001620304003800804128110340034103980c2d00040141041c151010344003210552055040710380007000c41d062640c1d100e91b810385a82c0b0035640980190829540700d41118083e822640381c4603000352894002482c60300540d0b054104080c04c0311042a240c000344041c80100b041414040c01b0082c908005010859201c100aa1020035601090111440e115020301d40240302010003c1c0041c0c294070440d00003500c00035100e80300004001811860103071034100c040d805200f460321495158603903259941c4800e08002c0307400c07509062101b92008602d00c2000d07a4585042150040c80d1454011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 216180944 1250 216179694 216179731
    0x30c0f020a050714031606120605091504020a120920220c0c0b0f010314010209010503040204050705090306090c100509030303070c0501150902030a0e030703050a230a05070308070302040b0d020f04030209 89
    0x10582700741e170348442e1043d4026400d2111103024600344252419088400690f41e0421120641c3d2207000b40c40500b4441c1e103001301d61010300500300c03094041c42d2a81c01b0024603a00f006400c00007022180c6040c41288101ca007001741d2071060b55070008062100d94101407000d804507a0392219240001c4030403180032a55100100b00f0004620025010030013540000c0d03040c4004600002d01c00c2c04000c0c0041e10950700d650109039100d00030012182d079820090180c40c404c3c40c0030b800482d9103440c0d075014240258202802d44403a40d10074416642041c000401640c5140c07580507040f280fa50044074103583d903550300c044403d1070f64080d0300d0520040c031404ca40961a440e000350400200c502e210f00084050f0020012080002d034010100ca0f102d500c181001d003038108110041984488107540104000d800001c0c1404071203030850b0180c8034283c4280c0d00e0f4442039403085002c034103030b014070301c02e2a5004005000540311644150042c01c032040105c1011401c0070f1ba260001044242c059070320800c01441e51540c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 216182194 1250 216180944 216180977
    0x917030c0105100605070605060a0314030c0c03010203060109030209090124080c0a050a03030503090f030412110d03140c010f0f0e060c071a0c0c0d030c0f020a050714031606 76
    0x595902021488080da0349900c0d00c4d0300a00544640c4100030101590342d00010b003580d45450350384015542042d203200170340c0308441003903940c0d0788204080d0216100344130802c0603505e014002c03244659010395500340c9191855003401903002026014580d00c0d500c0c1d990042a600d52280d00e0b001e129000e000051001d4075244007141002600344246004040c095018041500c400302c1003001c480d410700e041e590341e40d107683c0d40e981030041014650300036000000f000070302d441041400c40f0b65035004095191a80c0700c0c0504000e41d11100100c0180403c58000201030210b1120000d8441c200f044400032402c40071800c3e444003104d500700c052445055540e001c082d06900c04000c0141c1c0300700c01000711460070b00c03151241e2002c6004130360141c00d001490030000d42620f9446054408084802003240e101ca101c00030050085c0010018000003c1c041403104040381e84009598591940c0000183c0a094107100e0500b410072604005560103102d00d101c0c0c0c4101e002043e003400000d162a0b510385001d492403042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 216183444 1250 216182194 216182201
    0x11401150207030c052e05090411090a0603021803060108060a050106020d02100b060d0c0e0907050f121005060c01020720010e040b01022d010e030f030f070917030c01 73
    0x100c0030442d44040710520006010302d4800082d1581100d20565080d0600031503841d0390079034030203c26880c0303609034003140d4250040c000c1c0ca502101110280207036051443c00c500180102811281c3c00000c1300340030419030340240d00800c1540300d144c0d010180340300c441010074030305007080e480425a507028004000480c0541d01c5042d000d0f04403840580f2303c18a0402000355110107d6003502950b1b5039400c484082a541c0d04102c424402200500b80701c000a651005802c01d400d00b46103038000e568120014074401d100b01d0071203102c0300001c0c0f405d80c206160b40401a101c030a00a00c0c01101007110b41c00400e865983c00003074540001c01e20009a91012189840303d008030103003601d00d090440803200d154860f80c01c008135003110304041d200090b810a4210041b880d244070802603415003402200e5400d0403100ea05190303400e00500400a01001c175466205943ea403240d40515214018148082200f580340e040c203440d002000c82c80c00c2002c0644600e00c15444150302101440300c2d9100003601c0800820030300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 216184694 1250 216183444 216183479
    0x190503030a0905091602060403050d0f05130210053a0509062a0313150c0f020705030a02011710030203060a060e0f01050102060a0209041b03060f091518020c011401 72
    0x1003c451788005180003a64585014100a0500101251030540d08c0f01650112050000031201440503003005009600903403038191042c0d02480e540184440590701400c122800b404c1d081c010b1144484810071815041c840c40c021031142c0b40981400150344141c0c9004079802445164094040c500b81145a4034081400540304540c1d0340e0a10340200d401c00062007a00ea2003050440000015109441d20071502c51020f140c0c0e852007803501c0c0c0d104000b59440002240c0d510b85c90340807200001d44600400d6520512550020300003000c00c96010300501d0050b02d0540c01001e219005010b0755226070029060410495840c445260380780700400a00000c0005d1507044861603620021650500c80002d48404004085001c007940000780348041c1e48450303020002c0844a04c105004030480100020007800142c07107503403015505080d02098418940c45a003078001418203601408900c0d10031038086840070460000c09181d8248a00302c00d041d002c0c004c055580d42c0c2c001980c02150b040042855403940d404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 216185944 1250 216184694 216184711
    0x1009082107180501080f0406090f0525080d2d23070302060609090a08070803090d090f051c0602160221060a0e070803070602120115050702190503030a090509 69
    0xb41c200304102c0e60000784081c1c000841503160001c0c3d036101e0800f0710142803400c20060000b1601c8038008107028010441c0c1703845452114100c1902c3c007041034800c030511610b004141294201008555500d4041d4100f08044011407550001c41001410300b5658154000c800901240e940c40d106a1050120000c140c884015152190304100440c1c500030340c1c450000700030a010350241f20100f61704032400c120110209a1001500f0f9440f4451701c1c5c5404c198005a032052180e1045100f81e4103620f002d04a281d040d2900005070180b070030301e0501004100000c0c258009491689840171402144080c0024885e40d00701000603a07025090340b06200702c0b81a03966040402d881c000f104a0342c0414081115500620400030218240000d14047c030b0070020b29901c03071149403100040c4641000203a03000342078407401170201240503a0307aa4641d8550350a4000040c1b001074001c10600c0d006290000d022000d00782e5525010304495103031804a859984802074001c041810340c5810400c628241d032855a001050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 216187050 1106 216185944 216185987
    0xc0303150f100c020901060804240b0603010803070218070c0b09011b0810060509060d020c010b060a09182018030a06050103030807080103051009082107 67
    0x2100721701812007080001051400b803890f051240b5000b5880d94a00014550424030450400804500980d51865008001d40303800015601820105004580c0c1ea00719004001204010844e061a400904410440c4640c0c2c8502c0e036040b01a0b01944014079901c542440314050041041152500408410840c169550100754a03000700311607000080029211202144c4a1151440350b540040b0100151030040d01c0030340c0201160000030000080132404803000071519070103e01e500d0009083c0d404140280e140d22498440d689600c40010480794003154401780e040040c4204403aa40324022412144814103042d1841440310010b003600c1c0112000d1819100601c802c0c00240c00140043d0b0010f01164018900541644d4000000744803035070500d100318000d040448011511120f09010880803000395041c0001c5000402c03450420900d07243c800203210010f00228001c48020 = true := by decide +kernel

theorem cover : BRFrame.Cov 216007194 216187050 := by
  have h0 := BRFrame.cov_init 216007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 216007194 ≤ n) (h2 : n < 216187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
