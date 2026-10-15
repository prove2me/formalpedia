-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4293
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:08:57.049735+00:00
-- url     : https://prove2.me/submissions/dcaaf025-98e4-4214-9783-f03afaa6fc7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 771942446 ≤ n < 772122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 771943696 1250 771942446 771942463
    0x12031e0a0912120912050619022109010b0a21060b0d0605070f080c190e060a170907050307063b010311190309050c190f0501030504030e060c 62
    0x1003840c0c002e491801d04001d280690301c9a2000001501100042007400c08201d10810150307209000700911360b280010030003020b40041c00303401a5038080002b6125a054440d05207090350720905104c0c0181055800d0790700712600303a40c00034041c101d000c604101b000004190909000c6068008200a06141c5840300090030030b520707410340c0000402c3d00481449030903030115110341c0098540c100700400b07910342a00d00d18800c40b605512480b08020a400b06403091082550304c00090030324880d20322640000546a03001007001c0800290f0310081106103044440d8019000500c06001d40320441c02c19022030340320000c80c052a0b0512850b52465520b40c10081e11080740c0341c1c01c80c0c0300d104180400b5141c0e000c44d90303081206d4500190408034013080d1007010b03208481c09007240d0f512403506445004010381c00742509c4402a01c00380102c21142281d030300d90110000341420b80341a00700740a41003460010f60030a807030700914109442d260800000030b0308408a40200201222850b807604110302c20035141c007041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 771944946 1250 771943696 771943709
    0x41e03061407022406011b052a060a17101d01050909010b0901050111100c0323010b0d020304020f100503091902090606130b04030f0212031e0a09 64
    0x521900d000c0e60420701e0400c0c0c1c01284264203482c82d8210408910000d66030203010248001d0340400802c04a600850b03004d6040060b40c0341011041d116526124201084081e44c2e8042c81182440c039100c1940d1305124900c0c100c0c048402c5400e003148034400900e8103c50300303401016020110041070b1580d500311140802018041d5940200e84c3e10340010840c00142032080d9030007400014045001424180140445000d0217020420203030302c0d1200440e20040c00110595150180c100b054030704504a014241d420b008503200421140740800041c280c102030612039004020581c4014440c0c07407400d504585e0030901000b000743c5c03291541d000042040f00c204840513800b00750078080d400b4258210f00614030413884a8192000703101401e04441c4032110151001350300540520020301c1c1441c040020b044005010000400015111148000c0f1a40250416203814108644040851070203000c1d80b62042c3c0c44901860500b10411480c90300d03801c001d60090010040450810f54031889105200002d0a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 771946196 1250 771944946 771944951
    0x60605070c0e07090305070b19030516050d020f130509060118050108041e1a0a0209010c020603070219050c09100b07060c0e10030f110708030406020c0109020907030c1d06041e0306 79
    0x603900c0d40e034082e40c1e010500c81049e252034228000d000c54003900c1007500c145420701b9542000d0050350b104032000c1e48a110b10044441d820f110b000645034600b40980403060000525500031400d040401c4081d0600802c02070400002070840c1404000c0300d104041295000c2c20210f6907900c50745045a03c1e07005031140402c00c140010310600a1148a4650030301056400e026006580c4030116a03809900c6080004d5011488002c0c1c40401401d082c0c0003158804c1c075070b2040c0c8140c000101340c07030440006e4407102540c080e4803005c07109034540350450041c0e400c048002c0b0740c021681c0c5070804258490041250103040c1c1d641e145542c000c81401404840b4401c14014608900c0441c108400f0300140b0140300100a000e141c503e0312003018401070212082260401801c03070940e5116a500400703580440300f028425520340720140c2c0180c42d85840b860050407140c03400306000001080007800d0301c5c80c04e8a04106d40c00401004102c0d5102c030340864040d40c514100080c5070b40c003210baa611504d5804d600c003c00151 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 771947446 1250 771946196 771946199
    0xa0305071b111302090303250203010501150e0901050d140a05070b0a110a080301180e2a0109030b13050319090312020c0109170a0b040b0109060605070c0e0709030507 73
    0x42c8080050000a01115180800001e0400140c00c90044c401c1d2550558420807000c521346401da4030121501d01b61000103a480c100701d501003401c3d00d030281d001106074100582d01e0031312940c0014500c001b000060342c18800702d40c075207000030b0403201401e90040c0010081421803110010300f480b0b5080c50704e030030008964415907034440650055006900b100000351381c109540c080144080b03407107101650003404250a507401d06d14840c00041005404220036070b035450a0b528405001d000010f031004032105030f544080c40c2c2c506d440b61503001d403056040c10407420400900000d502c50010907000a041104601d03290b205e860a9450352050810300460003040303144030a0419440302211007540d104400485010100300400e9a840448000c1e17240440c03100f54080c0614821440c10100d1031400358200c6103250b059440d926185801a80c0554800020303c00500c4030201038000c1000030308941c607085213821072580f40d020b0701d40e03c64045c25074210b4410700422034240c45840756501035070f0408252032465 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 771948696 1250 771947446 771947453
    0x402040f0608060601020f1b040e1c08071209050d030b030a020901030c0503070e10091806021308070f0b070f05010e19030f03110717040b0714070902030402060a0305071b 75
    0xf48070440742240184245000000d000b42c02141152010303901138504403103600681c007008007516540c46d0360b0075284614180c000d000204201800d40101c4203840714203140c1040305c0300078441502100d40c0c020003820308001c0c00025a0000708140700a4541ca0009060340c6c070400000e041c000d100d04042e620450410000c0240f1a11002d0001183c1d01103044400d0a03545544032506500b044030900d00c4507200d02002c0000c142d440d0001507050b41c0000340c142c007001c11aa205000ca800c0419541c0b40d1200c4500d0600402c481001410080c4c20700c1d20507100464900040b10741148281da20090036000409044001c0040c00d400c4001420a000141c602101c0390300041d0b4400c007080001038001810821010b00043d0083c8143d14104080300c2c1c0ea246086020303140d00d14078581000c00705100100803c4006800c075520000380506500c1002c5c0d07003000ba6190041149085a55000961f81c41d01c1003090200503034849044401d0711a481c10045180d44c4e40d001e00351111036000101102101851503c0c6040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 771949946 1250 771948696 771948703
    0x40303092f030f0f070b210f06040b0411090f040617060915011212140a0c060b03032506020405040c2d0212311d060303030f0402040f0608 61
    0x100034041d0116107400910042c41d1350307500d8a0400c0f415103504481e0062104c860f1b02d2001b001c91050340a8114400341040b4006690014200c459000003645c48013800710601e8039000b004c01501c412102400482540011240c1034450a070845101c0e420296601c541511280c0001c0700400c610b00c460b040d404003011080c4d0b155071044590351018014821000b241c00d50788440d641c1070320078041d81e50043e08080d94400d403152900084420502a01c40076001c8170b2580580102901c0e5490ba4500031003141d58580030042c0c035000c007011442500203000206004440d02d240d41d807000321000009042c2d103502c4c00d142e4003c0c4940e401a5801a06245541941d02e422059490901e61000b8180040641400303075608110002c075203c0e0700607008040300c80150002d000c098502e040000480c1182f00ba041c240542c500b400d1800c03c0d03150082500f00070840d00c03200103101e0034a661200503080c203529041d00001d4603484014a40c16001d16480086410354860b0f40c81241620101c00c01003120340c0d12010702503070303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 771951196 1250 771949946 771950033
    0x18070e1206011a0706090501051f060201020301080a03030908070b010f0e0a09020d02012f151008030901030906090b090c09060f030715140f09100e0904030309 70
    0x101811144011262400140c0c01c1c122185000d0f89041903100c40c20020b0107610400742600c0e020386826039800820028819980a500320701c1c2010300c0e0b61028841c0e20f02004299204a056901c10300c010460480040b50f40c00c01d0039490320303002030f00802c00e20b0000058040d41401810b140100b50010504440000c46941626400000090184e40d0b1480500a85628850094205444600709401035015020b07019107014840741e18804501801c80c84002d8484840f605181d580c409103040280c00d00700c81c1001d0300003650104a0340203601f440c815030b0b500d2050810a504040e9100c10000500c035441d448003004950003410221a401c103088590307070712a811040d4510038081c0c407003c6035484c58502000190260003070040c051071407401c17a401158203039146044052084144442000910490050003045044814562103903400000e1007448070420710300340107000c0602210402a0f41b10310310258000e40c513280208442d0154070740080391800c000e29500b000b103904110384101400304d0003840ba = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 771952446 1250 771951196 771951199
    0x306121506040b060301060e0d0204020405040c0512060a0e0c0f121602070503010515220c020a0c050f090c0a031506050c120909070f171e0a092018070e 67
    0x7043c1c4945008102d4180700a21400300031410b00e01140c0954204070a10b8028a40014401800c140e520b10100e01a80d10030098400002c80000d00030307440005100000340c10200030740b9200070040c100307103600f52100c0b00600441c0401c0e07000700c0d0f00d0840424480844442e81c503942c0e007a126508251050140040b801c0b240c0c03030f0140c05101804a2903082c14801d4a01c1480181c0c1408000b02c0214240580d69a4625030030000080c0c190900383d2000f0980204031101c012517008083d044a0390038644200c60464000760300c10055140701d10031541d034101c1503a0b000441642d44580d03840204400f074005150220101c4081e84038030a000030943d800402800511500e0400d0790807500c0700c80e070034030f42500c05c413006a0792000000c0003041e4124403d2050003001d21550503c01c159040698252030b128400f11000c03845100045190001000090182038200c500103c3c18031040c880b682d600c1e9440d0740c0c03001c50317004113403684a050710003540c13640100282c0f800300d038007d00d816051850001303159034444107055 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 771953696 1250 771952446 771952451
    0xa080c09300607051b0703080417062202090702010b090106110c190b0702011205090a140f07061d060d0c14071203200a0c050105130f08030612150604 66
    0x4003518002240692051001c0d6072000e180c1407842615410040d0017180701c1036103204030600880003600020090026185540074010528402da41d0f4600d040c6e0f0003490305446048582050b900c90040941100142e6411101e00380c180d80da803c822401020301811040d40140c00ca000002d100390400c01a0001c900030005130b0ba40d0820031400c0c00108101040c2c1d00700350b109061800c200c000e9012000d03080d41c074814940440b420a0040d07541d000d8500641e001c110941100b4035140400010743c03540301101d807645010785044056101ca9036140c080a2040300c0500c6020350300020840310340200e1700b80c0120700400b11515403400310406c800500031a1001c41c0480c0a00707800540510000042d541701c0d41d48a0752125274100001c0084001c0d001080c3d4050020640d0981d020f2400f4542c07015001403061a510684020040d041250950340c000e441c0003072480d109203132003003c01c0e07c0a44000c15241c1081d0800d0707503a1100d1001c00e405500300103d039241070055030842d0b80a003290b40034007030140400b16030a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 771954946 1250 771953696 771953779
    0xf050d030504021c0f02090a0e060c090a0603060e161103160b070509030a141e0a110a081b030322030309060f050307030509071a0d200a080c09 63
    0x481080c14194000792415403102040c40c01450003050b070a0f03000b2448d520104240d243d084410703150200c2038890961200d00843d40c103400d41080005940206a1407505110301803501c001e40c2441f0700003070301e842c1200c1c20141d0f29410182c006c059002c5044c0c0315108895550074400b800d1250200b2202007110305140a20200d10ba4034860816120b1ba2003008019191000140d607a00c50301c4c10040288034032034000c0400340400f07a03007021001942400721038040c4c00031f0340c883c1c42c028468415418003e4880d140b158000e01488400290103800e26144100a205030808100028a58020000107031502c0040d218a168404005c541a00482e4480e4444120858441109480000c03500c6502c000284003400001c0c3c01c1480381d0091034008052005882c101911b841d00805000d83c2c048821036070310700009200310102201d01c90280b01c4210340083c40399007000740900346010300c03e901d0a00200074182020400400644003116800400209003901d00500f00760003440c54075181c0020503d9a512021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 771956196 1250 771954946 771954979
    0x1103032101170d110f0a0606090509010c0509060c0304050904060b0102071208030a050601050d06090e0d1812022716051e0a090305250f0608060d0f050d03050402 71
    0x1580c1e03450009403800790103400d1885000711028490320040b419184205840b0301c00d030003806d03c40c5a04c55402a440411312034188074406047d1000070b49442d9030f903032400868640c0a80d010313060320b0711107508498041d600c00d0071a4616246015a80095078003211034428001001116409946003034002c0c0c080d00c001030756070076104500c040c04800c06020001c0420018000000310f612090340080141816800e290880e12071030102e800340d402c1003000310717510002d06042d018100072090501190b4941a4800088406038072840c2c00313240705101c840e00d000071452046540d45106164090941013400000f00f6a0000881c60f0610a0380c0140340311040000c443c010714460360403201000319006038250f283c0b07a050801400c581c0301c0d0343c0c2030f401c020380418044009001840b800c10341c5110140150461105039010661110321944928000e00c0104000c01009070803a210560000d400c8613200d040b030280381001074a801518030010403034090240101d014980580c0308501450080e42d409900103880c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 771957446 1250 771956196 771956219
    0x120f02090402030901060626010905040c2402061f090c030209190f0911070b0402040e0102070f1a071e0909090f030e0603010f0b22030804060201050a0501061b1103032101 75
    0x10347d1107402342688006100e003035165040742d5003188c0b055801100160ba501c4c603420340c0040614030580103010740f840094005904020380c68010b080281429100705460060442d50b0b003983c80b80c503003215186c410509600c0c0c001c0d030603205200400351043c894502406a16805618240108884508441400700c1c400c0d401e482501403c20b030703410721245800f403541c40341e540031030303000f0030890303010303807110400c0303511305d40030300142c20000d20a0019640d514036524055954004002c0496a103c5d44030040081840d84524113115050302812040074807103500398215040702540e040642d01c0d600b829100c0d420088076090700403405000e41e803082c0c4907944100400c0000e110a1041c1d1584658040301806880002c070b004250704001700716142101e4680c2d803020010404c40d9030091309d0501002c1000c1007410f4080c05a141d00081c40c1c101040320390b06083c0b010b00a440c5c0300c16540d14001c000f9400a0402c1010000f1000352007006049a45401da8603003012900203180e11100b200b0529000005030090040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 771958696 1250 771957446 771957497
    0x1212030501080604080a110a020a080109110303070c03230607110c1203030106050d09060608060105101b030806010c0b1005012a30081e07120f020904020309010606 72
    0x1541a034901b42c070910040b80e2164000141d090300b80510b03010000140d5070340c100e200c0109031800000c511500142401000e0591824000d400b0f40c1007088418001a842928032007070f29881314008011200c084e110071000707801c41142d40d2452060074203004406d81c101d2002e4401c0c010307000c200d030342c1c0d0901d490a101101b6004005424141d02c1800140703c918061005444041c002c103000184c40181c0307071107500c1a641182e2003906a50040390040c401800c0980d0580551119414548010021050343e503852041c052006410482118082541d9a2244080794100c2d9005100da0045060260009000030514402c0ea800b182d9002c0c20303240035580385440c081d003245903030440322041c0c0c103140c60307a10103140781c150104c9400c0d8a10880e5407038a024410300c0d801660703455070703540c40a1070034241c0c4200c4001c82051118903c41d0302000c21000f1540003810103c1e0354408034002c0750036510f1b004007101034020f81006640c0140088104401e0000c15440002150705d55660405c140b1001d1003030b005c0d42c00c4034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 771959946 1250 771958696 771958703
    0x2007030f03020d0b061801030c1d041d0f0f0f0f070513150e01030c0b07020609040b0a170f1005010b0313080409050a021216120906061212030501080604 67
    0x8040c141003089009070702074006800f1400d030204c2c50883d5400061469803040007903000c0c1720b2142c40c80c4501075905121700b12150b0b8060a000c80240c8181103c60408011580003620a0f42c590a500442c0081441d4900c2c5c07880041d000c4841405201500c10340380c40f00244101507610032401158401640042e505170300408120107043c0482c2803c003840b03035004001104103500b540340ca1034940300d501220a200300400c42d112101005504510b00201c40e16144c0e4014141004103024400c05a62007070700301c07044e80c2011540001c040c00210086070a01d28503030711040c06c1c4912400103030700c0c024020443c9440c854508080d030320811204a8544100c0344280968202d10700d082c07001a503001c0900d120003000034010b25032142055510300030388098440031030300703a0445070300854641a00c0c40041501c641081c00c2c0801e003200c0031260600288910440c101d6541c0b050780740c50301c48040c012280c0c4050042c0200b10303425080080c540c00d01d80780c482c1d214003108000a1811000080b0407401180782c0c0c0c0520391 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 771961196 1250 771959946 771959957
    0x212060916030b03030405060a050a09060203090a050603100810061a19050c03040b03100503010c030e28020406090b01020d080105030a020909010e0d0906020c0a03230a0510200703 79
    0x28001c0441c018996002120f03014402040080b40e203a80341806002d2410855035960390b2481010b00080200300c1c81c0d80038406540c410320501170203a4400e40720740c003556820750b6141c1d00ca0f0354812221621240952006250303002d4000c4010032680305801c01e1090340c45059500c0d04400c00072018454a01c6607041009860140d1701c01251451720030f100611117840c2e69001c803828203445803003010071988203680f040e030441d1b51030b04104100c0c00c0c01c3c01450850308083c1000c20090021400580e254048040d88280f08403001190000380300440480908046d00504200456911183d55030000c01c07075890304034007600c00c0c1c0350070300a100e01c85c0b0045c5050703c0003d00540007005450703080c0483e50402921200ea15502c036040c50a2400302040030048021f41c0d0340d20200174501e0644080c1c02d241e0100e501a010b09180c031780130b102140b0000300800c000f0007030b480a8441c0c40303001559941481c0080a0050443c05010084415030320142c0090a0a108144000ba90300c240488828400e1280c3e5500078086038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 771962446 1250 771961196 771961231
    0xa0501090b04050114070804080d1412061002010e15180d0e09040f0614161409060d02071a16030c020a02010e0f03030c060a11030601020a1202011e02120609 69
    0x144100d1021114a6404940d01d00f1700c44647e0360ba80c4281c0168000340030721b510a80100c40404e6002584a0441d512409024503042c154074102c0c0c50070800034107060182400b44020b40b4018400d5005080c01952001038411b4411250340082203204290b41c101c20340c0c0c1c01c0500d030303003501200890010701c401c00d02e0b04c69458408121062020010000303000340c4024480c01c0545010941900500445811052121900f46000503c100c201f440061740c160800c440d4075103003031207256020101d400d9001c0480b003ca4032440d801103034a01a00c80d40c203004020b0460040942250075104800602480d00d8281c00182d042490008404988003140e01c24010790051140b6005940200d000f07800020010700309440d204658808a071a5034821070040149034841030800541c0b205030720603c40005010721015107141400c0700000d6450b0700401018091041d60020503039454003d501c00801e100716059140b1044200710314150003904a90542c4440c2010070000508910303240138400d119402d481e02140504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 771963696 1250 771962446 771962449
    0x506100903030305071803080c1c0917010e0313080c0d0804060309050703170702040f140103080c0114100503060603070e1807031e020a0609050307061b120e0a0501090b0405 76
    0x600005e4199814030809103d059215408070300c60300d010354011103145544004071002c07645031808458040300a1044801c0342a03031294410160401c58068040c000c0010388800c1000780109445000c00c0d29a01c000240752040b6001040707a58201e50042c030590340c3c8041e180050009942c2c1a8800802302c481c1000140549400307580a542d00760f004000301d420312a12036503494072040c4401c00000f080040461004214030303050140544040401c40103200e00300042101c3c0e20503d006003c0141580c1c1c0200706151140000d42c0320740091015448111202d007000c24803100742c2c0e0301c039006242c000c1c0a10800103503a802c0019400c0100e400403070042265035620303880754440e1540f4804e80f5085d800381a0b0f000000c14030154101107049a020b51001140042c0e10401c4060141d5600031010711005410801c05650042802002c440260030700c248030a981100c0401114401c00c0010072200d800b03801513031581d90000c2c2100154070251488090301d03444bd00195a0884a0310852a20010400c400c0c040c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 771964946 1250 771963696 771963701
    0x901030c030f0c0203030109061205030304121218030807020303250903200a05120619060510030507140c1902010e1e0405010e07050a200f0303060405061009030303 72
    0x48110a240004030008000403039400d0316003c03e81c400059001200501071800300744107200040c1000c44244030b101840d640c5880d280c0c0002880900b1844040d22000ea445015280c00c0341c03198410f580402c607203400d2602e80d02c5810580e000603400546600c0008440e50300010480b401512260507400f00b0140c04424007210015004c2040704104218200000242880281c0b0060042c0c105c1e0024481104009105410941d640424070601508103151743c41b00c004035201b504980d58011240031b110704000044041c2c07206511454100213000480543d1980c10780c0414050803140c5d0301c1e01140300c0c601080c89020300400c0c03140c8019030456030047d0b65a040707407000d200305c0034810f040403c0b100c1040d100140802d50304810400002091000100c4145454801c0c5405080500d4060440b030401060081c69401450200c406101540001c00c0c56103e103220301d002d01020080885082803020200d1a80340d40040e6001400b80341410040b500030b10340182c0e0101404003d83d103c181c11031546e10201d02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 771966196 1250 771964946 771964961
    0xc030b0601090e180106150503011e1802030603070b0c010510080105070e01110c100c11040603111e210c15030f0a0603170a1b0506130201020f0601030609021201020f090103 76
    0x50a6580d0440010b8801d51701001c484051f10a48401e9240d41c50300380030b01920040030381e90700c040c100c01250600c1704494070303040f2003000e100e03851006031280d40d0749012a1405506801204600b00c0110303100c4100c0b101500800e01c07179010071010f076029681c1c031000542a81c4081d40c024000c29040000e54000754450800110041c284004035810b400c80c000100345c4481c0751003c07050001d081c4040520a00142410349480104240d80420400d445c41e101d06030144001c0c107855109540c007200c4409141da80b10407544a85c80f000385101d40000030580c4403400140c01007042c25107802181e071109202c0c41c0100c07409000480c1c41c0c035a5480c60f9140e18207180006002013094a1141d41c843c404400302c1d0b09a903582c0a82c1d1400c41d0030954803110120050492401500d103041d0402d46100c2e104001400410601e030006032000003401e044442d480181c1c01e201e440b001d03000d0741c0d1040c41700002c184605078001d902c500c1d00940707400050303900c111046402d030f100e5000320010400f01000f058185510a500908 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 771967446 1250 771966196 771966241
    0x11805070e060a2a0c0611060106050703021c08060f0301061503051f0e0403080622020309030403020405090c10020f0a0f081b07150908060a050c070b040c030b0601090e 74
    0x6250f25008107421000c0c60440c1c04103001c114540380d40c2003001740108802010304080c0c00c2a0344a000101155540c504050060a003040000b0594108150007002032850b01d02013800900040e0840c1e0700e001300403510445d02c0c3c038400e1411144001450406128410503261000301c81408408201c0d8250003610000d8007140d0140300d02c0009600c4403440517101001761510840420480c2002e0600601081015000e217100d49861212000d000842165100701c0300c2c0d5082001da26540c03444451030079402550b2010b5002424036003045441c04020807081c41c04541110040102070000f84200d07643e4608461003901c940c05050240082101d00d0815207001d4440c0144900e0040d46014006620b034003a4590803d03a40f002c0c10034005050808200e46000d0705a01e00500c07414904503450380c0e40c0c1c001501204025940f0fa001ca40c0340c1606034111201107410014200503070a06240034100c1811030310054445044900100e0555885007440d00116845002c840c880f5885858461b00303d06441d80c442c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 771968696 1250 771967446 771967457
    0x2060f0c0f070b0a0e0f03030d0c031d01020c0607090f0e0a11120906060102030f04030b060d02150d050604050c0f090316060e030c060a0503191e0203011805070e060a 73
    0x55407411030410959000c1c04100020a4403000b0822020b0016040b50042910400b9185402c0e8120b40340002510b11061741c50030f020801c0e4060b000c041c0d0050103c0b801548030908100303045d2980701340540087c83c0891032001160b4507542e03814021151400d1030b0003203114810403840e0404c06007850468040e000030360480001044609050494115403105009942c035111000030400007007824812140d0041c000c0c000346140c0f620301a0155050310442c080140760402070404038125496a4140400d941c0c3d02070810034840c0ca5242014001e50000e10030340a030142801c4c0028400c0c202402101c0c007440780594514104500418110b007290040600150180b04031074004146c0c0005041030401000640c485812011081c014117050142c5a100c840c00352000704100300840e5403100031640e01c081242d120000300140301c4002c9010701040d4046502000d41088a02608a003542c021812140c60403d031106160781241c00405607001160040041401400000c40504000c00208044407551a10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 771969946 1250 771968696 771968713
    0x6020d08011d161707080916141c050d0c0c090b0114030a0f1406040c03050408031305070306091220061b0c0304031101020c01231c0507020c011b02060f0c 68
    0x1034840d0440704842c03240004007404c2c1031261f0288144000e0800100c40c1c3e05090903107040080030281a5410400e0703030f0040c4440040d078401103a0f0040c0c0d42410780d62002c00d683e481c0d10a8840104070400c038000c140d0300c1080480380000c00390401d220306582c1d090181c45422214107214198040c03038000400700e0308100e450713848800d8001d103684988010192045c95410b0b00c1e040c40401c2c80101e074440c50212040c58640f405000c0031031141c4c1e090307a5122121840881c0ca025103894150f040c07800e69070000301311608020990b8200715510414480c4045a5035411602c00c1c0f04200c10842c040c0780007000c14250304500d000c5240c101c04c1e1401c4031121100e070f0700210b140c800b07441c61151544c0e006a0054440e242c5c100a90f203220b40c1d06008091041c442440d00078200c0f04080111030144111041d096680400042c860303002014620558a00102d071800410a529207442c020303444100740c822450008815448144085240c40c3c0d8003040d440c0c02030a85030601e88003043d40122603010801c0402d051060800c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 771971196 1250 771969946 771969977
    0xa0302090d062703120902060405180402030d0807080411030c030d0c0204061a0307030b010311040e06210c0402031005090921040e0a021c0606020d08011d16 69
    0x41d40e2000600c5000d0001c1c40d400802c82183c4a08040c030324807189003102e4107810340800e5110b01c003240002c680000020340750415100055491090754440c980003d28402425201410a04954402c600a40982e00680100703e02161000c1c0221500f00102c0c07481320105010909400954a141001400325000c5081c044002440c1604202c031100014500041140031400e1034010300005050314401d040d0754051400c9041080d000040c1100105556003c2070901c0360705c203402c0781c2d41c1800803500c11a52140c44041030000c05030122246802041050040b80100300c1e00c0000b020141c075020044c3c0700c400060740030407010b136002420f0f040f40c107041c1d498081401c2c0d4555194600a007000341c01401ca000702d104124103852090300b11044200400d010070001c000310f110409501050316a4010799a0501d0f1b40b0203201103035101002c030001860102c0c0883c03070b2500002c480180c04050f480300f81e800d03030340c5200340006207412604018180003030318082910b01c4520108803651030300c5800d00000070082c120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 771972446 1250 771971196 771971209
    0x120203040612020c010b2d0a03030f050c0c0a0906061d131e0f05010e01080d2316030206061305060d1e0605092119080c09060c06040c24050a030209 65
    0x50b001000800081002a0136507c034841014004054510f2940c039895510050506116840030340248000001d14004071403041c0000180c058004282d10001512202c0354070040220340220004034228802074001c2d0410f002c480503c0c00401440708990400046405c000307000076003000400381480b03400d808000080c502a15010759030302d0b00001020340c540b0080d04122030040e8452074654100b8a0a841c1c85684429000445600d600b0030b600050f10b80344e1200b07010700c03640f04c04803080103070780f0112000c2540c04260280200c0e0300300d40090840301c0c5198454110f07001a2001540008006800c10001b40040203140c41860496641d07d8415201d44600065035400c071050341c401c1e0801960780e0b50740c0f00d24100102059070311940003800d100d0a8250542980c4038000600c06011012000482e032588010454076500e5025146a4981c40c00c507521595030b10003524111440e0030840c802007660491103c880c1040021244074008000350711600f911240c2c0080d0b0944201078003000050a55100c94 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 771973696 1250 771972446 771972469
    0x27010f090b06032506030b010504090c081504060803180409020d30080f150301060801150e0903180f180403020601060806011d0a080604030507120203040612020c010b 73
    0x1021400c0c02482c0c00c104140c10161440010410030f009951028080c00b0001442d006481140c28006024030307820300140c0349030246500007407035142450742d503180c200c5e84181000c3c014161740c101d040c07840a1217420001035a205000b800c0582d8410f1020320032049000181100ca040d028000240d800200d4010038500e60f59034500b070b1080e128012417003020b52255a0b8a00c80d15040450040c4003081c40301004094400207411018200a0344010074118140c2c0c2a03a07807810070005008205082e42c03448018060464610302c10b201a003213260002d0005d801f0b0000f1441190400051840c0c9400c41c0000c20130314641e0b503202d582041d24207a4200c19501c68038030002c000c428a024403a10f518040c45e00915007a4140c1100080151003c28010166004525244c044407a90303401e00440d50428003141001c0170306c1d44407010903c140c0d400d2106160300203004008440c0900c054401403050300c03500380d949200364440e0600042c01c40001c1040c040c415030180020004100c00403c110f0003000010345100100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 771974946 1250 771973696 771973703
    0x210c12010e090c0303070f06091703100801060902090a0320040c0e0f0f0a1203050c1015080105040b01030308150315070201060602150c03040c090c09051827010f09 72
    0x400e402e02500040400c401089500100e00442c80e0044903910304907810014400284519250080b45040202d141034031280640480c45403522490b200384601d1042c4203900c101d0b84507500e450000b048005443c000c80f140c24801400c0c107500c0519540e00c0071140e03411030240412080e03150070314409941d80c500076440030354450740d41d0080c014802c80810204440403c0c8071032160003200034003d0039459510540e0704551040c012000c004640b070030160381c1446201c54091140c02046545c0080c80045e51081d03046101244001c02115103a400704c60803135409807005402d61202000410000344a070400700e40c044d0881491040e0070712004003080c40c1a07120400100310107401c000300f03c4072960900c11500200180e200800180005040c00c8000c0c96000d0a4403640d08800800103060000740003d8000516038202d00300103400350104010320031803407405264824158048074049082c0d603104110702642c625114030800303010401541c0169854030700007240c65500d921103000c00710a10710a1141d080d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 771976196 1250 771974946 771974969
    0x160512070218060a06050a171003051204060e0607022b02010e0d02090c090609121006060e03030a0315090f0905010b0619030b0d0b090f0111210c1201 66
    0x18034410004003500320b61510740b1070000001000f4003669400e80d88030844d41c082c10103d170f540880b003800715001e03130341640c1c000c290b40312080034013001c0e0035051202800c89000c0c8055454084020078990828441da103e4840040e0051580081ea40f0304140102451072000784021010f00d010f004002c0f00107484444030711072030040580c3c1820740d600708850010302c0000b1600500c1c0320016500040f404000901021601300e4042504201a15010101e501c9030800070064501039014503c0c0d560342c1d52601c4076405900f41003150004415010307407100c0030040e0004000d507003003800044088005048040040c0d06070344251400264441242c07207a03100a03d043c01011850003194185542559083c0c4449801075404004584c02c03d0762400440c460218149004120550300c130002641f0050000e0001d4400718500d024010784801c00079404101c03041d07560091001c0c160780d120500e142d000e40100803440324000b5002e412115601e4903015030003440c106a007814900400380707112106c8800d8004040880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 771977446 1250 771976196 771976207
    0x2010504031d1c051e01110706020306190b190203071218031502090307051e011101060503030a0302030a1404330501031410090c03020f011e030218060405090c160512 73
    0xc2101c0390202205004170300a2004480541d00401035102e07102026010585c08800716030300b82d0304c008800b0100d42040203041c004030344803802d81020b64082001c85803c2e881909140e9036017070000c02078807152a008858103000c0c01c11204c054a040c01c0880c3c4426208910640100c00241d80f403044003104d00762005e0050702c59007424149407900e01039810007031084603000c0c40440c4c0c0045007010000c48803001c2c40c144c40307401a40712281c0c2c050100c5810031075050001055480c20b082c1d01d41d0142d0f10804000c0b40c103101994683c40700c160003100aa034050305a802d40020500480001100c044280300f80c202400b0320601010310f1402200c000381c2049440da0001d00490500000400078840401210941000075254607a106411000135110090280c4102c80103030744540c0c080d540e004160011061614292500c4000050080d446192130301e0801101020301c62007801c1041c152001e442001d803007407106031a40c010f0b403403054010141c0c00741030301c0f6850044400184144004032001014007206d0380c0b1130 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 771978696 1250 771977446 771977473
    0x507060207050901180903021501030f030e12060a11041a12090f0d0e060f0307081008071a07060912080405010f02030c0a1d0411040e0702010504031d1c05 68
    0x31166001d284a4001c3c1401441642081d030f442c000015030076000050000044c2c6030603401c0c0304019452144450810000205220740100300c08e41062003a5118000402400c1c100f0034400c1000d06030f401da5900c003900060380c05045512441204160300c19441c20b140c4d03a5a1045101e45141c0d615803203045010925840b01c0300003805954200c9c001e00058103582c0d004443d80f03507480094035000c0040040050010b0169101c1c10704462080461143c2c10f96a49001d50000d40107003000e441803e05161100c00003c0c030035601103400c8090b02c4543c00c400002c400e044900c1412a04a002c0696546556070071550000d206129444414101d07903c0d41e500c0c520b041d08009003100d0241943d6085180100100143e002d00c100c101e40030101c1d282413429548010410b040000740500704030075000b40c540310f0344d004048440d41c06841155420010b02d0302e039030740d056022401d0f61416103000780894003607004141c480003035042c9240c2d60080a08051751035400804130707d480e07140905059580c1d030031000c5001c070740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 771979946 1250 771978696 771978703
    0x3010e011a0f070f020120011e0606300509010b121c0507140601240212030f0a0b12010218061206270703050403020d0f082a0c010501060906110309010e0303070209010305070602 78
    0x271480c0d05004000c80f91030300101a0004c3c25143c0300a054013264010369980c1504c2d112041d4180c80c0e141004c0005142224544d402000c00f034503000e02c200000c5152140c01140094000f64980103c000403587c41440c00060729981c2210000b250b040100c0704951511400400005009001d41d407100b0306014030000b034034040341000740c512500315040340141c10401040c440c2100c1c0c000d106200c1a840540c2c0300155080149000100643d2028814950f402815015001b42201940007808100c0300b01d00c50040004ca0b100f690b03600900300080c1c0c0700207801403600412070902d1060708807501d441d082c01c0d12800d031210f40080700c0020109a41d0401d01081c075034100a800c1d14101182881c00038039484500c05000c0380c0005100000180e84005904408985600240e80301d1444801490300c900e41d90b51510b000e844240103103c0000e06248000640e14461102501003400207000f80d480c040e4180c004540754029040b041da018031080100d400140c44111400740290b01880c0035040c0c490405400a04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 771981196 1250 771979946 771979991
    0x904020c2803091a09120304050301111c02161a0a18050c0f210d08071812020604120c050906060a020705120a0803010e011a0f070f02012001 62
    0xd41012001c0700c0800690070090700b0341a07544503035241c0340e181c1d000103402c1024400e10030500d80004201d00107244906001000d042515000c900900001d1144807056180f802080b5960180910b8015440c00a900c0e9134014800f6128482d14544014802e4943c0c2c86105075500c45030309000302c0d00d000c2006920961162001d92400048a0381c0e101d06a9154265141100e241e0b8622841513282059210703603a030240f88005640d2034550b2140c802c05910142c0d01d1b00758044190020806840004140522070480401140203c8100c40d900905000030159004480d1400b00c0e00860100808180b020322040360100c0c0c54891000b21756450f0a06003031010050000e002280203200c20320052410341c0e0082440e2043d41d2040c0c9940c01c0525104004a1902c18040780250840c0e20000012848180010b0b10b1416100e0040010300c000d42c0c1c13828004103a20071604900134090081c4242d10000702003c406500d43e80c0140351151400e421210700821222450110dc02140e640e071102c0302200700d020300d5110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 771982446 1250 771981196 771981253
    0x103090b0f180d020102070210090b0703050d021201091a090613051005040c050a020c0904030c03080709271503051e01090503070c080c0409030f030b060904020c 71
    0xa810265891011a04014041021101540000a416002c822189001030081c8000c5450321010110040d00035030100e04203074090845400c01840c044d005460325400c03100100811403608610b51002c50701c5800c038113084002c45800300103003142140990401400390548000010707001d82d0f049504204075030780300c44603401981c541d800c000559450209070a10040c1540021840b542c5d002908160301d40140c100d43d07032107480c0c59400504aa800000f0f4000c084d081e4084410315416002001079a00d401c6500400040502000000107481441d400703030440c0150401000003910ba1079140300c40140e081e886483c000c00041200341d1500c05004070303e000c800030b5040c0ca401301d0442e21100d4a4981c2c01007040e444030829a0048804d0b20300354012524107800809803a1141d4980c500485c0d2901c2c00e2141038603910400180d501280b40622441c0101a4191600021001c00342c0c0c094001e05081c3c510198058070a100d100380c42d868a000800d542c0c859030018205c0c1565181c051080244a8403400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 771983696 1250 771982446 771982451
    0x120c0405100815010507030c0602040b3006060a170109020c1911010305090a29010b1c0c09050a0803090114070c180b030f01090b1f0e0402030f0303090c0109050103 72
    0x200143d10400d100c0e804500a103001aa03c03e16401d0503510b2000c2408010405840000c1c00610b08108501402e000780410450145020a00c1c00000c3c0d0f078903c140001413a8614140403a000349802c800605e13002c0b4031414102d8006000e00c1100b150740109074401c680a03034000510541041d014001e489081011561b0b000050f586501c0b503010325011640654185551038021070740000e0100b1180e007090354018402656002030803d408040304005c000c80546030548400400d500c106481900e10000302d87c0003200c0c8a501d40c0d42c5080c050702820355035400b8071490b48004182c5813600c0c2100d5001c0e1185000a40c2d0320380050000405c0091001090703100c07030400340203403c005437510403604222514402c09030190b03003072003070070b0b10060401850055151044002c0500081d0043d00202056030198130b0108141d50f41c800b00303a40038948011107069210a544080c07101c9041810540d030007600190484841614100c500342c5190f01c242c03080007051340020500391070b56a2040100000d80820302e0309 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 771984946 1250 771983696 771983701
    0x60f0d062a080406020c07080a060209010201050105010503071b0201120c0804050606010c03020318060f0a030c03050c0c121e0301060c0b2a0c0a020402130509011502190602120c04051008 82
    0x10034680b0081e200500032900002c1e400007110080100c8006400010151080140da40c6420070082d481806890302550170a0000034a540c0180103803132040801c1d0300c40481030b0a00c407001c020060f94685040381032020304203010482c0403c0e0322601c050154140c40d44000c0d03081a04041b407500c04010312150402008803083c00002c1c2c1e010042c1e5050340c80120b00c41c0c4a0310007000018030740b4040c0800500c682200810b00c007d0851740740c2c0101000030302030307101085541c40f03144010603a84680300180c22545d024a01618405183c2d90040218508880c441e6032030440641c000c00302944280d001000145040b40243c0a12144015480d040303000c0f240480034403c0c003100c058180d0703400e81c8448134050302c01040c201c01c1000184182c440d401e0340284115914101d582201e0103400b003d025450042e1a810001324a0f00760302e140c03181d0340305000e400030251042582c040f20b10164111318202d070455020f003c5403899069503943d0b02c0c0180245c24100c0e13229801d010a0005041c0391841110810140c00d05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 771986196 1250 771984946 771985031
    0x3040f080c120312070212270f06160203010b060408150903032a07050609100c210507090803042c100b0c0102120108030d0e07031a060f0d06 62
    0x1101c00c403800e035500e4540700d0340d502001a42005600f998202e204180058610323122021a2a011079108400d901f68024034000c2c2d040c0820800c6100030b040d0001d40820000240f0154207511100f0244003c001081c0200c80d5000310b2095000781e88001c281f588030000407400700c1606090260b103c0c1c86c0400440c00c2d0b2800c119580041d00c2514112072600444044a801d4007190030111100160001c00f20780060410010082d038070080940110012071030980700c14040f5108169100001001c0700d141d1492802c108040e81c0180400b0b0305a2050151b0007000080d40d29043c800707040200a1070302980d240c1d07014004141650322a0311180d516010000c010000c0c3c01240c000c1d02001c0e00c4802131150b0f181c00e5400c47c01170091041000498807011000000500c8140000003842c0c0051000420320001070486103081c3d48040500008059003031903402c9112400e42e40300941c1c1d2043c001441d1881070401100403070900000310700c0546120303841d200d40e0402c0405130400303210442070130401246a180340f02c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 771987446 1250 771986196 771986203
    0xa0e100308091c050f1c1e0e0a1701180803040605071809053411120406020a020405010803090105090d05160b070312110412031103040f080c12 63
    0x4000c10203080403a502d556511064010704640303484204925040045041096849660150743c031010303c13419040303d61021243c0754501081609850b07030800504025499888040812640400c01c107086818100d141ea400703000000a1112401083c50038403541d502e0760135100c0408455000000c14002c05000542e800c0c212640560001c0001845c8d85500030f0485200039100b54040d046000795101040c921825031107240190303c80c414901c00400301150b000c6c00071100c2480c8039400c041400140c86c60314016102211080c2d240360581e80120703a84480701c1c3d4190040d41100300160f0040942000f10704262045174050480c050082d804c00441c180020454401c2e408564000c0c0b282000c21000c02004102103180010503144591516072980400440c581080005800084030724240d03161201c1e0503c51600740400c0b404c4440d10302400c1150761544100340d101d08a041040e20141c4c851500e005001400c06403090004030700c4024508206280f520348940c0c00c0c46d10400d00c24112041c07525001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 771988696 1250 771987446 771987449
    0xb0d2a0f0308090d140c01020106080a0308010e0403051917091501050622060309050d05030601020613021f02030301090608031207140c03040e250c02041d010207050307020a0e10 78
    0x100b0701c15501e0149a0120b240e0440781c0d03100606000020807040401c080106581d020036100b23a00800025a0310864103030741d591241e4003e00030038185401481105000c031b480c3c0303522030f01070309000749050787c101c1d54200d00e10410b8005000240170b0040d1280040b8502c20025000700b898070081c054082111204818501c06104241c4501000075110301d4001d12140b50005101c4003084a090300c2d079441c180600500741d500000c42d8035000b184e140400f07c0d0700920030b80e400790307070b042e40107114594a040100c0c011400500302641c1c4a42c000039031020003015041420000800c96004d1030316545010300080a54090b900051641e030000e000a80c456610007404039409901460035034030b10380002c1c0024001e4456042c00e29410302002038086500303001c0c03015660242c40398040c80e4103214900300300603003000b00410514000900410b024005803509822a850001c40d45080008101205c03078030f00d003241d11110044600360070100707c09066180c0480c44400401800341c40c0407240c50250600360703580046 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 771989946 1250 771988696 771988703
    0x70807020d0e012003040e06090c0403030f140c0703050f0106080c0f010905030d261909141905120c0d11100603061b1b030806040b0d2a0f03 62
    0x3407010307015030320071110b0f007013648003000c400003848101850850b01c80c1e2060080341c020030b9202c0b0200e02c01c0d04082c05402e206040c0c0795515424203055a038120b410800305003070301d4108003607404101d000e080d8800040a61040d15401005a81d24601c4c0850520450114400442e4500b074010800d011002c1000c40d0443c03821548048807501c4c03c00141c41008050f0443e0747c043c443da0f01451219074214008544004035003450401444000ca403242042a045907091025609141d9000c0442840c0d009500480d1280300043e000910310b08070203103404250106000000240000c070030074000b05000c0403103002d066140061600114200c01c0c0d0f603444a000f9984108203802101e452940400d0200107616100070400307000040d03481c244040030300b801e021150035035910105814280c50217007100503441d20301c01090070b0550030640c030305a61000340101901e070400d8852140d803130140d480e00400044603205001c041c083e85c465400954203c0400d03454800c145255410900a031110038508500300c1c4e61 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 771991196 1250 771989946 771989957
    0x140108012f1b0f013602011d0a05100207180c080106081003060c050c0c0f01121d06071e020106060905060a20030915090f09040f200405070807020d 65
    0x101d80e44503141003920344844030f20394030740f80100f00d14103000c40612000c5905096489540035440840b00400d10703030b5000003804103020205e20304401c0030216540c00f040c20000d002011207a9501c020a04465800242000503004654280f10a115400c40d50011000e03a403001c110381d15210002810041d418010750084c072142c00c0024043da1f20380365882d0040c580c0f00005225001b141040034040b50020107030307107000380100c2901002c41d0804440b5408011016900d501822103c009040000d103201e0030050720740c1900003d0070341307458020020180100d580703990305481642c400440017106600e102c0d85e0703421641881410800c1551110028054500464490340c0d141c490000c00e40f000003408141c41c1c409800d81c0c030b00011858000c8080c0000700802c0e10f00d1242d1401000d0a402240700d140c0e0080d80c0801d00191500c11800e041c01a95807003885003400103005c224070b0310394070030802c0c0501c1d03040040a144411003186051900555070000c0d6582490f44403802d0200d8041e40b03c11100c2d002104211 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 771992446 1250 771991196 771991237
    0x905150a1113091d0706030b09090303101511070312080603070b070b131a01060206090d09090c0e0a0f080c01030504050309010e0418030503041b0303020a1401140108012f 75
    0x4201c03d0301a040321050b0000c880172550340c0c00d00500680b10100380140311b6810003000520392840403040782d100300381407409425214100101c990b040e0728000c009004002c0140c200b650740d15070400c0340c2c0010798000c0318058098048004000c02c150310041c20785010f500201010009080384c00251114141d1004865055036152a01850084c00c1e41c040070b0402c100d02c08020000210b04224175040e602c0d140c2c00e0700c0180d5568002d01c2e64900c9901078901c0094010903080100d404142d2002c0c15149491074441d10f25600500000c140301ca16400c00002090000c40c10000da0f5801c0000903c80102030805000b213240c20342b41d19031203025031414641400200d40320f06040e036a555014100c05038075610030140341802814001c00f0b03500100c030704a40c80c400440349180c2c0703000b03220015022680e255004201194541c0c0d9021b2090a901210200541d00c810454503490791211815018120715000011000b00d120b6401e00b1107000b19060103080034010400d4003503030398a481143c00c4c3c00b000100400711017 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 771993696 1250 771992446 771992471
    0x3010207170f0906070f1518080913020c0d0e0405010e150f100c05190206072a0303050a02011b080a0c020a0b072f071502010905150a111309 62
    0x9108420079142c0c13005002445100300300c0503000c84001c0c07601600c0c02040600c10940c0005c21500f007030440c40d1a4600249040001401c0c0038020300b182003001e0007901040e688a00401c0c16600041140e000c0341d0000402d200400b9400b091001284030121003d000f40e52410701c4040d103c24001d0a501014110007462034119103403080c4207000d109010308600801100e01000810700c003401401184c0038080c82980d0540300e410340c041c241c0d50580080c0f0881c81c116881c1e66191800c0300c1070100071b00c9038240c0c5600320021802c4100200045001e0f03206c90b95140e000f03034402401c4030300300000140346130005480100590b500034131040d40002c040300d000400461000069140c072801c4031004200d0920780081066242e4401c40345401d51990310032080612080c81d108005680881d02e103100281e0001404005a0700130214880c7c00e41803600002039041c2c000c3d10f0766418106446094000e91100000b8807170010100d101e409142c07a040203009040c2201078611840d160840e204e9a00c50304d1f21585005140f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 771994946 1250 771993696 771993727
    0x30711030c070303090f05041103011e0906060c1716141203010b040905011a09060a030603020d0506070e03010b0a0306150e0f0a0605040504052e0204080f010501050301020717 77
    0x20100c00300840d8003043e901d140c024416040d03030050ba000f0400394800010381d405c060144d140e0f80c424040c055402c5070b00b05018070740c1d10719a00b1121070038400c5107000001c9040045c0320340c401405c010341e14030102c40d0b41d600702840f210310404800030544e0020441d11383c5411206952aa0990340101280c1c07404800b94042c5190000d044460050001c00000000750071034010000d1080324140728080c45030340c0c0c2e0b8403040c040c40504031824030511030040000f003080b403030030b4030041c42240380505001900781e440e900410304031109000b003110f2580c041e905106a5503002211820080401c030000e2110724420004681240100c0c03100808558460310b01c1c04c07250b00c0d4001080040e06d888031a8a5485c981000d1042d0602800c0c1c6807080c0c03c525140020034582000d0080a1003141c025004021001d0b0080c0c03a008100710203184500e07003200a4945401488450000303100800689005001c13038030800a009084171010303031185210347e10400181c03001819000480d910301080d940e50544450000146000c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 771996196 1250 771994946 771994957
    0xa0804020f0a150804110f03030406030b032d15070e041109090412140a0e100905150d1103040f3801081603051e0a0f0f0203061b03071103 61
    0x45040703003c8000b1080354001441e52140340503140781c0d4851944401402040000c100b02160160004c110500a00c0d00a4200510030040a001c546191032a1400ca00b1070003441c203080048048101c03c1c00f000032a0400c03101c4071800d4081c00400c050b06140382c003d0002c8410b110030340e00954448001c0c2032001c0c00d035401e07202c02d00e10150a1014920741841c04c104501800350040001c00ea1906090301860304510a5035514401a129102c06c2410042040040707201d100c03104041004840000c074054075002c100c50220502d04c013200e80c4464101e1400800c1ea05c02514400a010045c001c100108104c00c08032884580c12200d0b880d084150034807914000440300000505d861000c41c05841c902d0044001c40d8121885401641c0403025500c103040510340c118070018015038802c88042d9002040d00d5240701100250b102103034091601c03941d605500f40b0f500881074640031180300e06038056040030b008556002e81000440e038644042d102c0740d40c6044c00041c200c1c50800c44514154a801b44e010011160b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 771997446 1250 771996196 771996209
    0x5040e0f0607170c03060603071b0c0b041502030304080a0302070507080609030403030908010b01090e090c040513030e060f1206060c0f0d02070b09010816031b0305010602060c0a0804020f0a 83
    0x803494a00542d010301040000d041d140118103a036800682400103c20689008081c000c1c0390924540f00d4400840384100841e134018a480c0036001c404000a11003d020802080411202a2140d2030180c205100020140050342076400400811000a00000480c0c03021846400c0050311200682091490016140c01004d214880c450910110b5100040904112442641c4085126071038017425400d882c40c01e035074280440c0b0050001e000c940844040c080e400f002e001c00700e4441e404410005000e542c015201300b000300000001c00030a042d40001200440d400540d104c43c1360280c105e10340c03040707480b0b1405c4c520580072500300455501e81e01d040445003140c07650b0701105d13490030740e80f48155140e4241d020b8190161042c50790010350110010306403a10600140c50391600b030ba40700350100d0b010640210a450416617108600280c0710744000007400a4034981e0380016241d030524402a00d04900070700345041401060001000c10755001c50b11ba03601c21380c143e5142800090780d00c089002c4448640244 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 771998696 1250 771997446 771997453
    0x21204021207050d050102190c030806040e10020f120906010f09020f041a0d06061b0803090102090a0e0a0c0e0d08090f1f02161415070804090f0e060c0405040e0f 71
    0x1c4c04c0c0481500900303043c220700c8903224a00ca959140940c2c0c0354480034070040215401e1070003c0d041e45456404a02e82000f01000d4034070151041c00c4040c05c99000c140780d658001404103410010b402d401e604242d001030004014a595414074005070203021032485865006500000e041134072000381c200340c40c014141c050400b1004038030310b08800c1003034004080c4d081c4450b20340f40c40000c40d070744280301003402d03548840c840921441d110f45404a890b44001d04042440d034081008030f046880302da07003850080050b040392000e1410405400810760b000381d4211000c0156141c494203603962081c081c3c02120b540724205075541c100002c04200d41002d0504070980c001c848080a10100d04804403c44007241305074262031601d003c043d802e002c035000501034031405000c0703500c82c6091410110081c55510a4600b441400c1240340d60b209581a40070b13802080a007505d8a010300c3d41c0d80c250740921031141040d0701c05045507203002c0810740d2690280c0d104d25482039444601d406400841800b0306034010600c0420f9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 771999946 1250 771998696 771998719
    0x31707020a230f060910020712030f0f0203091c03121506031d0c091b030a02090103180215030a020706110a02160e010e070921020f0402120402120705 66
    0x180502021082035040d49482031030b40c402d0262a0a03903141061000092015081c0140320f4140f0000c1074001040b5030551103120004658401003d011010051190340c030300d54440c9440400502c510301c10a2040107540c018400c81c201a5a100d1054014150a00200703d0003501e0741412110510f10030711461069252110745844c4124601130308081c3d420070f490621618800e00000100c038210f80500394540c0d041021900404d00c1c0c141c0780740380c03c6112526400c80030110003003510566841a03c0107100d00d68000307100512540c06000301c0c84c04d420340c10322003050500710340c0208030b00808012001010210010010b00c88544690542e800345401a50400184030f4400034241e0ba41c3c041c6075440094030860344100405000c0da00d0407020b4070200d456035840d69103400180c418801001d44010240510300303001142c4503104010000b8040a8102d4103508205540180400802c11204480c003da0040ac5404507601401794400e4116a041e580e5000002100c0390b42c0d0b04008150300b0050f0300c14a403009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 772001196 1250 771999946 771999959
    0x70306050913050c010203090a090504050a050f030d060e01080a12030e03210604021603030e100c0f0f09060e0d02120109030206010e0c030114130b030d050703030e010510031707020a 80
    0x70403401d9128004560000c0213070740042e03a81e802002c0e8410b510014030380c028042c00506070003c94109100d20101d1700703503003082e6a03610701300651030f08405825400412103a03e042d540e0300684c0010306200da241c3ea05075041c64042c41e12400c00a502a088a4401046d10040c622940c024400b100d00c840640340c60394165a00c540b0f0764a9640e900551129039000031a055207424130884900c0240e020850840b200c0701c0c0ea043d0003034044100c2e816040e01415414241c440c055000b1401200103da84050140b8800040940f54400c012599010086110000d100040e040300d001c0906038000c0300c0e0790f01c102d0040d10000e80d6003203444038503811950030242113200b0141c00084e1039043e80c0650300449544e03038030204440702c10300007403160218038a007207400400300341008408240a094106408982420301c03002084c5080c502c1c400140018a002607220300381540362054110301e80c0d4910081c001400d2010309003c902c11340f40006000580c1600909058a440008452000307a000d080703948070070350702c80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 772002446 1250 772001196 772001221
    0x20a090903030506030705100c0501110310260717030d0f0e061e0a050a020706060f05190e0105010806011205010801060f060e0d080315040216030f0f02060408030703060509 76
    0x85044002c00d00708404034803540350204100307095070750203801280d001584031703411070302d50007002019201c80d5a11210010403150700f900452160260b001d40240c0c1c0ea03c0c01500145842008080c0c02008038036001c182c840d0140800c056084502104514808030104800d583c00c6100302825540d2907840d1a901000d07072800e58010841210b007101c140c9407260784000304010759528034840840203540302000a101c0c4589079220b950000f40c4e403080141458016650602110542e81001c040341250761000c01281c40c0c04510b0070100c0f11070050400072036241c03880751001c0c02c8043c000c1c281448070060004810b070f4802d20316000c800020b44030a01140d40d44040e01c0740208428010540c4800308031101183c810301600a550041c440a00034061501d41034494000d603800203040ca000744075220644c08140d03683c034006031880d107001c0303010908085040c0c81d019142e11000310300c440611842c0c4021022a45d000f048165002d600120402d07900d5503401c40407402004160045076105050000340280c0d860340c0d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 772003696 1250 772002446 772002461
    0x70b03090a0c0e1608100b0a03090b011202150a030b210c0402180d0204150308120108060115030c031b0e01080f062209060204061d0d031706010c020a09 67
    0x4002d0607075440d0f100c07044803061030001c0358803040c1c1d01103003491031900b80e00c2002c4036548181076414100f01291203414003140d90b400b20407514000381e00e0301c40d00c1c424420b8030349841d030051800b04908001040702ea800f14841c170420222401c40c081c00455600c040c00d029400001c0da0000051401e03841410441c0102095038182c40d00400601c00c03004136050b1070a0520032645c6505040b034240c0f044084090811200541d1007078200c0e0495140c0051111a1780c01c803052001541c440c245c0f003070f200d44004e00c102ca039111050f88140c4080d03202e05c00401001110a14110801d1080e1401085a083d90702e01500075106043e100d03c011059101000c40c91980b08100d1040c169003643c5050207a200c5c030b0201c0d81e800304241c07051a80710456184148035008a114484a140060f1901045040391a260380040340c010341e22400115189007600361544140110003c2d452a017203c101d240300b161600c000b8034100c4980d90400b5080d421b4070101e03c040c0e025441c8020f600342c1c010f10400140b5200e0b40101d000d090070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 772004946 1250 772003696 772003703
    0x905030c12010b1819020918100e07020120180603040305040e010e040615060e13061d060a0b18151207050a1b02100309170a03061701140c090102070b03090a 69
    0x43c03400301d1741d0541da42c022030396030980040c0303201018484c425140c00c0c4440c0240c00400804a054800603503003240c8001684188500c0d00001400b40c43e803142d07107912114445175000c3d2503001304040e812507541c001055003035000075510a516603480789000e6030f2500c0f5a411802a01c1e02d1072000040324a001c200e011320844c4101400c0c40341e041e0191680d4441d11032402404085031405400301c5150510a40080e0000301d00080800c5450b070b43cde91010844918039100c2c54209408000b00403080c100401d480b4000e0120f40240c903d840c24212180050441c1e801510b403140c002000240460740b421016214030000005210301c05082c403c20144c05544040f12443c00b007058564100324511641c1c096441080e006020b039a1895a41c2c0804c40041c44420310842d90000ca1038803103e082e600307002c081d1000030869180041c0090074900da4050201c41900c085030306038180082000c001c00480a0303141c20100c01d40e8002c0d1590031000042c1d080c0706082d0000400c0c484040104540c4a90010b4244403980c003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 772006196 1250 772004946 772004971
    0x3180f0c090f090b07031e0e07061b11010c0819080709091503230a050703021305060105091002010b0d0c0e070503130f030e0a080f0d0905030c12010b18 67
    0x105101c0700b000740d910900d4060708641c503010000b1005800f9401c4082912030902c4c0c8044100b1b583c9500808543c01e07208503819a0340a50b005004194001d504804c0383c10b1078802443c0c208500d640c600040014420ba100d04000c0080d03030100c02c100c3d00740c4c29609640e081e0703202c1c0b0b8410104008018410942222090005544801300292400192103080241440c460740b84044c50704533261030001704080382011542802040300c010300520144080840e06215101422010703245004020410032000b4602640501e40428003210b683c00c0401c0310a81242510450840101480264010302042800d1a00144450b04800401284510410680704c2d020120140e903190300345d04441a003c1211003901e501400f50350b03900400c110000100c11584070f40f8102a41c400003001203240d900d120b40c45814641e2000030003d807001010b0103030a03c402004d1070200b40a926000000383c4e284c10a251060282000500644890030290401c8100340c00c0030308103803040d035890790000080490850301c2c10389054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 772007446 1250 772006196 772006211
    0x10f0606030b03030a0507020f0405010b04060e01020309011707110d02100f1a0d11030709090209070f020c060d02090301111b0a030c02122e060b04031203180f0c09 72
    0x70301030711a0051a640240c01141080710200c025103030307175004e08026a0301010076034800d0702d940d072036010f12070203800c18181d0380d900e032451700b140500802d00850104e41075410074440c440c0d003643c1c480303041040d0383c048440126440d1903410095950f40441c046030409030141c3c8000d05142a00000c00300f400800c1071000300000d0064030103100c1202c0c20302e20402021801008001032071300c1c00c03030620325010b402810600c141d40340440000e850650340f944000740080e01c0c1d640e010f06520340044d95540c4401541410041d898082c440251105901050350b44030354004213071140989483d03070581d0302d4007034060000c000d0843e24070070070f52054200c50110300714401c070391503d420f80740c0c1e0200300e20350250b616490f400041d03021a800c010302c42d0300c00c690140d0a03214003d80405266500e0003030b15500112100035024940c00404484280c4889030000741c0e22800c00c000c20000a542c101040200700d50500d400903100e400102040c4e0040d0b510000a0208580c2074401824005086020300450760551000c00140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 772008696 1250 772007446 772007459
    0xe070b030f0105060a0909021603090504091a0a0209030f03032e210503071a01050a0501050313140a080d050f06010c140c120102071a090303071b060e010f06 69
    0x244021101191444000e8004000500f0b140d40601481752050619110711030700c075084842260051342200350b494610340035190a241d00704203460058034068405004803030f055159080b44814910440700c407803e1190006003094520b070b0613101c102c01d00401762203c0d0040d0103442d590720780050f20518150780505002001c6c0903920244908015550403a000d03030240f900640c002061030b51260079003017410420f4a00300082080c00203202c1c0902c5144403200d0b1585001c50003045040503001107020780e400100c1440340d6a040703815250300c0600d142c02003125400d28501071000c42000d403076103d07040c418410341c0300400425201800c0c030000014000c01c845c0d940c0b0072103540740100588100e4042100001c1e20b0f000b00741c100e00d890f83c0491000084868049002e0f000c150034075030b0082c01000c2658045600c2c0d00b00020301d640b4000401d480100170b01142040101c1e40d44a200241c050400d100440b61505400344810f50010a81038000004200750585444124081e00444481c01741c211f18000c00401c00703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 772009946 1250 772008696 772008719
    0x60302121302101206030c08030d0c110a08070804080f0a06051f0509091e010e011b08160c0803131209180f09020a270b060a030c1709010e07 62
    0x1650000c21031081103d11540548200014110b00c80308140c5540000c40030a00c40c0c154407000b40001002150384035941c03000201114000c10300d0707000308541d078078191030a64000074020940710b4004020907030319042440d000003d0b00ca540e00443c80c1e80915102c1c0c04c0c0844001c0390091209004090a000599842201c44401510745c84030108007a920101880b0728100b0100d11544202c0000441d40e442d2090300d1030522190143c0c02c54065691140540340e00d5103028096000c03075091034154184901c5500001800c072000052540594040f1301e16030701b0410348035502c6041895008200642d80307041441c00f140480010310020394022402107810074800e8410303030740441200c040c0c1400884050800075141c01820b0f90b06c0707400400e07a440720b004070090b07075895100c10010400080320342d14034a0860086502d8882040302082440e2034203400396180d449880840e41c035204685400292500604015103481c207001845070b4840ca01c150420a00410540c030002c011020384085442055860042011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 772011196 1250 772009946 772009981
    0x5010b040e0a020c1e01020903010908030901111303060e150709050a0e060d03051e1603030513051b060d02031e0108190605270106140109121205090a06030212 70
    0x4860780405c0f590300c2c40c211510346071031109100c40000341c50030311610300081c00d443c4180c4040e540707050000140a8401c209118904540c10103a0049082100b4180c03001400401c1d0301c0060f11840e15468442205607082c4007910346034508141c12002d604103508000d00c00e00490040364040c4681c2ca00220b900030210714014440c001c0244104003000f0680c0d0120303041e40044400e2022110f1170800341c0d0340c080603a005007420310210b106826086c0c00300c1c1070050076a10094036501c881d584070224003000c03403c0420381361440091a03220740007035021203020907010f00c150001106800d20100c10300c17001e120611701c58540c514201c80501034690f04c40d04016100d00e80c1c401c0030400e005c070801c0d10300001040341d000543c0c03010001c0005020441c58220000c02d05113020340301d100c2c1d81d5440d5010700a00c000d804098071158028038002c11030720b00f410f0084103335a591220240500000841170301849101e8021189032240191158030200d6442c18060080d4121100b40500c005100d4001a400c0c609582b0411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 772012446 1250 772011196 772011217
    0x5130203090606191502060a1a100503070216090e0111310509070507060e071520010e0c0915090609040f0b040b04030f03090503030118090605010b040e0a02 69
    0x2c1034480504000c00810407001030041c000c400e640000d80c031a08201d01d04904161038004c0c1c102440e050003a001203c103480c01ea4141d001081030b030107106480d40518060822500c1c00d02643e251a800d6060f8600600c02e04003842d4014800800724034a092a00601250340900e0001c0c443e003005012040050300078142d00c00310b10328481c08924803d090b030515000620400500784211141c681d400f060803240102c8103d80407400c0055160304101c81c51040420009044014140d00b5041c9034411919480c680b41a8040002c40c0a0513072410311000c005088031800340c3c0c020040110700300c400c6034480c2d12185035148980700c2c610000780d2407498419444a800001005c0c182107542e004100400e501340030304103503561441d0008002c002030f858144c2d81e0040340142c00d8801e091400340f900401d4140785903002c03020941004680000510000700f546e054580000c2020740488448601d00b000308900c0b0005041c040c1008000101c01c10319034000c00c20340d104014102c015640c0d03e40d071141684038423412031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 772013696 1250 772012446 772012453
    0xe190602010c0f1b0303181407080304030201140a030b030d091d0108120a0203040e0405060a050c0a020601030618060609020910050a050304020108220302011e0e1f1b08010513020309 80
    0xba00d40b60000e8046071107036209086c0020900c1031101c1c0c1128030005518119101740d501d0b840300142c074604000810060107100021846c20307085900007010409240110300201402040c00102c590081c1c0050050540140445440c0100020b0080440c0c4241c4a0484c80c14022070301d80d080719040c10152070590340410700504840020003040c8145600040b9250114081408041030698203044402c0c0624000c900601c031604110040070200c8401516030103c0c14400c110100105801044060460b83c005a0019502c00e800480800842c641c085c0205990310380354003c1498801540540120074003518507140752114201d050300c0718803482c008038000c10303410300000700190301c1030358216406030721701c055140d604000002490103200301d8241180941d446082c5000414418805000c403102105400d10100800d50040340e2a070340307001c5c034654842401004a10010b0030a400c141c0440c0c4000c1c050144c080d41201004041e281d0a00950f40f259000c8010f011b000710707043c000d990158100c0b0f4040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 772014946 1250 772013696 772013717
    0x51804020406051504181104150f1715030705030f030c0712050a110103020712210b0604030b0406090203061008070603020712030207050a080409020d0f06061e0e190602010c0f 77
    0xd1803141c08006d0541300c02a298007413030400c40c8552000d4401040c0420303000c0c61100e15004054040c4500c2c0c85814204a132a0440f00030907184130020780d40040341001aa00c3c13001c400b40200741442e0b01504403e40500c20b02c1411842020000010080d0305200815181000d40303400c2800c0007903105101c041c1140d40a070072003801045000544403015101418014608036544c0c0e0f42d0912000d0000d41d140114800c4054423030207030340c40e5a400000c540034040c10440800c95a0004446008902010345940d4070b050002d420400f084d03004800c9180c0007021200e503072030304500c800140c503118060466180280440092098068020703101b001703a201c0a00100c114903804210700030b4012880903aa80d00c50346810802003400c200003000a85541240582d0301d0000c03010030401d0b543c0d00381403512014608602000341c0780c4d000508904011800d40000c81560416400f100c0ba14005151558000b800b110350300d09402d41c00c1280000c03510b19400034494080703001002c0d182c003c00c1b82528008540540c58 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 772016196 1250 772014946 772014959
    0xf032d10090f120207050d140607140a0315170601050a0e040209062b0b060f1203190c05060a02250203061f09020c03030103050705030a050c010503060a051804020406051504 76
    0x22a43c00e01c0c1d152040720280740d07640e0002070031394a500900f610f00e07108580001d0800c0c8003d02c4101c2c0d00c611a03007000c2c00e6803500705404841d141320b0702074580c0c209a81c80c00394040c14801041e001c0004d00891060200701c5125020701d54403030720280705080c4030b46034004c0e0000e0440d1590070058410f80e0010090b03005555030500b40308000e0100d00d2040c1c0b00d460f0074a0030807080500404034640e900e000354011965860b09a003402941310062243e80c0c41420165074141c03d440c400021079494001000780444941e1542c001034400700d071100402449401000104140344a403580030302040020172802c0d60800103070403224100c41013100001394041e0844800205021055003008169a40c240790ac00e4046503101c6a01040381c00c600d4030403c1076040040100b0030b004080140202070081200941071203505592020760303070702c03080440d28140030011000415a41d10111550000e140207804450116403440040d00b4203038048604920480c9803402c00b06450a080b50803d4900c907421400d245080c0c02d126 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 772017446 1250 772016196 772016213
    0x1b1403120103061a03070b0403170d050403020601091a030601090b04420b071412130807050a1508060a0905040b1911070b06061b061617060f032d10090f 67
    0x55800c2441c0008002e03074981d5058bc0d21505100724040e50103420103505121010301912340c0e5030680d103000c002d940c04c040c00d10b40d00030400078115880d802d0002124002040458090000401a0703803104055005914040401000c2e00d255809454400b804240b04007160b101e946005001c2c5840d0f10f4000d014034000201600c001c40b00c603c0381d0030126600c0c0030382a0b80700d040a600091480d840000d4600080190100c104011005464120b41140855040c030b0040b05032116040440d0080100e407201280700d94580841000203842d142e94140814686800d120301c17641c0003920003007400c40036510301a01d1518a44214400b800c15030b21590b14003110ba841c2d240e0200340142200d64001800c1003d41c00c8a000c41d4261010130b4060070103407140d0b181a1240300050a409540e15050001382c4251380c182028402b0500d910080443d44c1c28280b02c2480c01003450007045008200341c050196220404202c0c0b00c000b12511111400125010502418900410340740fa5100045c00c407014000c40d40c000a0028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 772018696 1250 772017446 772017473
    0x1e0b030c091c020415051c020105070f030c02031203011e06120c030209090403020601051009031a07120c110106381306030c0f1b1403120103061a03070b0403 69
    0x202e803100c601c0909500000d04070346201c108004441c0304014200b029040186207140290a00109a079841c00c4640000e406481003450060811244010501c1054000c9c20b105840a4024044580101c00180560134584c400c4c001e103000c405401c0c010409007044104940269002c50b0f54840c0043d41c0e81d01050701410a0000710800d168003400702c45178540390501001d10407402603005184c294500702c05e210070740d04138412000c2000404481030002ca007510b05404207034110040708020a170348814044808a814000340c5084500380580307000001d0307011103458002d242c4c3c4002048003a42c0c1d020003201c1a001c803503605a889480c01c0521003002c0c500400552204500070b5110301d031410003000c1a17803030707083c0e40c00c1040402d0303480181e0a140765100798618030000d204d00345481000401c17081d150402400100003464801031280e48407034140e092040c0c0b8400e0040b02da8000071561203242c502d0140c16048940003e0005041c880e4485140000d5198122440700c4440b514042c2192609104481031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 772019946 1250 772018696 772018729
    0xf0f090f070603020a26070e0d12140c2e020a090504050714030109051017060f040201090f030b18150c130f062c1c1b1e0b030c09 57
    0x20014031b421000d103003003442088810042ea0a043e83c034002c00042c00740d5001c4c00899000741d0b501010a800030390451900b0088030303100c0c1860b0f0040d003074041141d2094460190494102e0055005010b005c207001641c5902150328022103148014503000d00e40b0407801307410100d00010340c80640402ca54100f0b84d01c9150040014907007621001b0306003103240c9084c4d0082e03000403d00740c3d4603c01c10000b00380c6206088080c10a001c00c00001080c0781885a69131403001c1c213100c40c681c519802242c2168001d8402034024550350b81800000c1340d60341800000901c4c1110f00c0c0399106046a903c0c1c200745030100300c01000052243c0e010b1500d48903192015410b401c031110034103c0d410003400200750181280c039070000500c02540c2d00c8842165a42c20b40490180d258100300b09500c0d05141c04100369281413903d41c0342c030240c41d02151150000d06100929203400616444100c1e032041c804107001d01004001e00c9000404140b003113103960740d64843d01c031030703c8110382d0096108000d100f042030501e0008001c2959482 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 772021196 1250 772019946 772019957
    0x8150f09100b030c1206100e1009050405131719050d140c030402010e0405070f05160f050c03240a050411041104050f0604030209040204230f0f090f070603020a 70
    0x2c070748001d05916031007900c00000d55031010881a061180c00c0a0341540000c00343d41f01100b56242140142500c15140c051074400c80078104040c844034400e0750301d90002e0030000c20902050030905442214001c0f020404d07281210342d40c69032960103141c1000c072006076000900c0b140359403009407400c44a94101001d4400340d01c1d12400526422008860858020031401031000d50702c1c1024400907096040714000c0c5401142440200701d259038110143c2400c500d018241290b40f41c0310210584a08540340b50000e00a80060003a2004c1c00000030302510102e5054040342e43d55100845c086081011000760001030b0310440001440307615042d0402c5421500c43c080c00f01c40c9031701d4003000400740d80800070702d070780359001c00b003001c012038a0660300246410a0075183c01d03103440d06680101d00e00c0c40f4010000b0b401982c4510034041c0084907110416200106212080c11500b01003410840c2180144c40481c032101810010808400c00400c44203042c03c80354000700131841c68030505501941008180b40b05101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 772022446 1250 772021196 772021199
    0x509010e01171b07080c07330f0309020a03060204140d0b220210020a0c06030612110a151d0103020c061503010b0d060e0105010b13061803020604090b0108150f0910 72
    0x404400242141903111406840e500c0d092244a00615803184424880d104222440b4071580340407071034030050035159142003100c4c49a04400ad074064440020000d421405061000050100581c003401c1662414030b8050f00300e2080b102000030030b250f84e20020340701400407400b003584440d100d9040e80c4801c41d002c00c404192034a580020384401d04800501c00541c10001001c07080150000d4000050b01640c00c0400c045810500b9210305172544d00710003030a505000d03482007429a100c000d40c1c2c0c0106000004d100345400c1b40140200f400700105014440345071171448004043d8028000d491280c1d4180c0014441070359a159460001d07a4000320450b01556070741c1d80c0b202c1c0d5442c1d140502d800740f40a50004110603030144401421500305a02c0000454418429043c2d82d2030f0201072081280c4451070600181d10745801003086803100c1c1e51001f035000c20700007030004103000d15401c0443c4080003603c9a41c665075900401000b1090300d0004c080d8000e0200c00003250a150900e0380c141c010448095025105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 772023696 1250 772022446 772022453
    0x90c061d060f0309010b01051801140f0a09030510050f130606030203100e0c04060311061b07090c110606010806061308010c0507120507020112110d06060509010e01171b07 75
    0x10381c0911002c010655002040091421090040300d002d0082860034514140441540c00d14000380d11429604000c550007829840c04000001e5990106810030b4aa03aa074412243c003500716189032108403524015a1100c148010042c40760350f03c42c80f076184441840e80e454a00014000300c0300b070b10442e00329523030303039004809030f281000744d0151071050304d400080103848810218500010103820600c41c60504500b4800110f00a100011010f03050f2034441d1a03042022140400e0020115106080c1c422810300180010a035002842c0d1074105032189000c00405084054480703d045550741d0204034100082942130503c14001c5c030421012a9515000d0317501c902400f402c0d0751144c04000300090010908005211210303c2a104408032810190325044081c2e001800b28424204402e820301d03a10703010707000b03030501c0f0404603405d43c0305081041000540ba81c030090031a030028440f060014500c2282c00c2e0055000c0c1000303001000351046801030b81e5544e2140c22105103015082c51a0400c014403404000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 772024946 1250 772023696 772023709
    0x507020f06070905010e1c03051c0504030e090703020c12090a120f02040509060415020d0912080910060f1203050f0f0315101205040227090c04090c061d 67
    0xb0301d41c40e90714840868500400102040d6000040c0b504c030701031424020305281d0a4052203100a0740c1820a1503c6482d4001c0701411200e0041d4100002030905007040b0805600c500801e004510464070300400f926003100c120224051901405031071382c0141484c840540a140c0a001c110310b008105155668580641100302054402c007101c05400c10300041e411440c05000345a401040c00c0c1c010182894030342c641c40441e2443d03030480c007a40c55001552102c40713451074000300c1196411941c3e10401c02c0d1400c0b0028060402250100b90354000d003145100c201000f805440101c1707003284800c0905500b40300d4041801990000c085080c00300030411b104085039290301420608078480000d0703840746001404403c684190916182c86403c1c03a901d4032246541050390302e22801060100040d684c3d81c8c5101041c58004a0a007021841208140b2400c0804100b59901c2c0314010b108142c0c4d2403603444070184000d6807103541008103501e044c60814011584102c034040c8418240409034504e4680b040d020032032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 772026196 1250 772024946 772024951
    0x215040e2a0426060f0a05091e03090111070501050f03100504060f0f0b031312020109080f1b030406270b0a08011d09030f0f0f030112121707030507020f06 68
    0x950801003002c007401000c43c82036241e00d1450360b01030310103441d0000907042c0141e03008161101055880b000705500341d00401c038013000030310444e011a040800350b80320650b9a8201350031850001e000d034041024070210110780744003154010384804c1d041072203c1c5121149600000c007006070800401d1400280d9075101d0140500401190400580281c103044440c02543d003260040a003e12040050101d08076801c0c640c180f020750060840031261030490310880c054040d08a02909509000c5000b42c000d001c840e00030501e60720000d43c9450a00303070542c8100e40300c0c011881041c01245500085a600c03040480041c0c56a0302d000480342d03452a01c551103103d15401040d2240c002501c1e1000601c2040c031104030864840d445103121401501c0c03c060103a541c1d11603140c0d441402c00380440d9404006120005656900740ea200c0110340720340e10b03500c0644070600013000c00c0d034600c0043e1307240f90318650041e81414200240d90710342d956196241c1400350040d10026020707808501c01c050441582d4501803140c20b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 772027446 1250 772026196 772026209
    0x5010908070209090105070c080705010209090f0a0f0b0306060f0a17030319090c03030e06040b0403080918040302030d09170c07080706030614091506030106020303040215040e2a04 79
    0x80d01c8481c140140140c0e82c000074940502689084144001c80c2c4c1c00501d0b044041d54440f00c940c2d44c4810304c0c9030807801ba0241c0340556401440c0c940034024550345110070a849142c6480c6c0401210102d00d1001058800040d1181d0b00361300700401088440c04d201111b500c1b840001340a0204050382c0d6460b00c45001c0c0001043d1000e5000441444045120011850100781903050140041040707501d4800584007181300083c14800501c0d000c0c00340e6211031051324010030b00b5614540d2104c0c1e0764101a05e507640004103c501c141440c0342c040d040942481038040c01690194029800c00c4a070116440041c0084541503401080101c01204100380d0307140203010320b03814800a050040d15003c12240f9002158002c3ca003450309000c4140411402e2410400d4000c400f21000c52a903122208800202040500c1e0907030040000400401c0340d503000002140036910079541040f2400c502030ba82449402180156460f1541d440b020480d403003010400b0b0b18102a100c1d20000c580d18911010140c294015803081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 772028696 1250 772027446 772027463
    0x3080d020c0601090509031b1c1d0603190209030c28051c03050f360d0b0c1c0608010603050c040c050901050a0207080109080706050a1e090807050109 66
    0x7803032038801400258010100c06609000905081002070703182e009400c13180c0450360034118001049142080b11000040984a43c500808081a401403150041e05000f44402044280c400114141507044074400c14204001410781100c98880c44003941c13116060682c503215030802c0441d940e480715003100c401000321404904050070604040001e10060707108911030403c804500c00c816144c060000790250381450510303904e0215200503c5c041c06041002643d0701111812014a40c00c0d40e240c0142c43c1c0c540132902896412407108000e8491140703903000703256013051404601c43e403404d0006032a1101e03001204c0c01090800300040070032200c1c03940c04032500703030f449040400c248070051103c0300d23011001750343c00c0c4004070007802d01800034071807a05024104400080d103054154403e10410000c3e1103010000d0110360490f06007451150855070064031152700e00301c0407440c002d5552040c480c0c402070203448100c85040319010b400080038a080141c0c0c54100c00c02159002540a209d601d1401344112001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 772029946 1250 772028696 772028707
    0x190305010f09110301090b2208070c030c09060b091e040e03271008090708011406120307021f090503030301080706020f1504021c0506070c030323011202030703080d02 73
    0x1c003d2500c0c081c4524000d074941501e000104200d60040c0d507014814044552101080282d000b03810000c903540900070300300c0802e065041000380d61000f41100c0c0945400715407103842d25094022144e091060182304001041046d10384e040000030211201c201d602c0303400b1646008d42c081819904900c074600c03085d40000504009410651031003c440d87c406041e03590b00d20300c1e40700100c0c407402030b40c0c0c8621302409800c1001442c4040200320940140c60010000c1c020f5001c0304280d0200854242c6d000c5111303c003402c22034001c4460000944501075001884c0d4594042c20036070100e0300c005800504401c00c1041c11000c030b19074404100440c000c00b05e0f00d00401004d403500000a0900002c544100c48039000072101a010b440260704983d00190115001d442500c070b01039817442d401c00030f62002010b41c015170702000356043e08a41211840d0f400303900c00f4000c84540c40c040d0004c030071408142082d10445200140090520022813540652018040710101c03610303a1540482a0428041d45232081c1d00042c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 772031196 1250 772029946 772029953
    0x9060f021306030c0c0b13140f150c031614090a060c0b1e0a0b040216031d030601080d1110060f0906050f0a0312021c05090a0b0c0309190305010f09 65
    0x3e10b18007070203a8034220f04840b05c10b40c3d0701180c0d41e0b005041614000d07280c1402105001c050a404803405104a04071010f091107003a1154071810a1590b01c0340700c50844000a440070b96040460388a00e01950f14000258a00d1303006503020559085c2601050340180450900c0b40c80754075120340908203548070b1340d00b06c1040c0e19092400d03070030040c08404601c0340d0030898005100516079454004543d00000301e613801061300031900900840d041600032803008031180c0107060300075031440c0c0c4452074800000ba000c071003001415a200001c2c400c02981f680240080c20803103220b03506400b580c107102c205a5006902000b140400da40850b0050208482d03000010400c101c028811a030060009507007580c090301d003100c0081d07450603480c440034040e00980d800c1c1044a41c0300f80001c001c180b5060000007810303901c1031002002d940149038485e0181a1a0703402040c1900b51000f6907861003680c81c011860714004505111201c1c0e074241c04003400d811184800300006500307000d64104904030550000300c0007a10708 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 772032446 1250 772031196 772031201
    0x11031e04030207212d240204090b0102011409061305120a17070f02070b091903060b0f040e0712051509030d060b030603100b12031c0510150309060f02130603 69
    0x5da19049074540e10009070480da80300303040d500b801a00401e0106800e5020390002d800d4004110742207959a100140200c4c854100d0341c0b280b02d01d4003003a4020018189164140400d00ba015110401703d540200300080080258503855503601e8425015074000b00c103508000c00351904000c0107007010840304001d20003d024801d404c16400446403402d2440d403190198041d407500c40c0c2d4007071210326040c0051100f2664646008003041c9603d82080c51005554a040420083c0b0f8a0340d0507070f1280f00220b82e424140e141c140a0b40c1881400c1801414113146030041c017404156140000f00c80c02d000d8207824108d00001c038050544501d045034083c540d50908035001004645040e04081d81000d4140144001500c0001d44290504942c04000480040b88170000d005003030b4581350361859203c002020007011884420f481c1010b2220f080901080e140c21110015400042c020580c6400001001030f20103031007500807400141c0a6040010741050240c000800c3c5c0c2d1084800d02c00500180c401003254540c5072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 772033696 1250 772032446 772032473
    0x3050c0304034404110607170d0b06070f11040507020d030c02030906070807060b0d12031e0923010501081b15160611031e0403020721 59
    0x810251862030305030780c0980030401c08101d081c2c00e621100c242c141500d100001180d00400518a030890000b04084044030081044400303d17440d10640c50700c4074071801d01c00c3c00c0d11780041d8000700300c11410303802040c8811650041402d103120301e40c03651040070441d180c1100500c60a4052101c03000407064908182c004800410010b9000707500d400204660103034080340600d40007015240100344480c0100d412451809141c18880d0310900006261f4100000380300180555403244606020039181d1000708090f044440502070000d6114400d490040c5200303610006d944e0185800354100c55804030b03850780c1202c92905081701c420741d0720a40101050b108020713007110000c412000b030081c0d40c102a100c40c1c403031090b00604019400300b0800b005555503111011413407410708031810b50300e400c03074800d0203002402e420380d05a0b015407600125070301009290b02241c0c03140842c1c1a40d124108106d42032100301da40002d00079401c5000d107503004138006004006903590001c0341c0c6603a520501840c10f0100040545 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 772034946 1250 772033696 772033711
    0x105090c0f0f012a14070b0f030105040b12160e090f03030726040305090f09090c151c05010501180501090506160c060f0909140a02030c04080708031201092f0f190305 73
    0x48c00300b04003000040d41220f043d40c100b903c0c0800c502c2d039028082208080300d1075101c0b60a026560650302c04400c02e000354000c41e1075030050305195840320f0700402d44039034030b10100b013600d6001003000518841c011405001702c40c00c0c0b10300b0704401245000d0130b18041c0106450440c0003550024a0b55101e1805200c0703140350388011078500039981800c5c41450782c1c03820341e0900c15008407001f2140d221000040c005907442e40544654540954100714130b000000e200074081c0b1404074040c00c0b00080d0590039203104009075401038541c2c00d011070402c010001d160300001e802011060a00015000040b40c030752001005000301d80320a6880165011302030121840c1d9005214071a05d84450004081d240c001e00c01d400058a41c4010b1707803601c071f00b42203242d40d1041c0e8000c202d0b144039000300081c0c900b800000070480c4003001d503411142d0340d80340ea15074000d03500000160109448044a015424a0010b600302490714211b45807516090300b000c4100c529400c5003402c414240b4824404100c1e1b113806018042d8421301c0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 772036196 1250 772034946 772034969
    0x11d0d12110111040f0501031e05090a0203030304140d11120f04031e02130209060d02071e0c081b01021b04021303080c01061502120c1501080105090c0f0f012a1407 72
    0x440d03c5115801910303272002c00ca0034644030808160b5141c020320040404603005400d4965034a0302c0e0510405c102d031036007100c0c1c45c3d5114800d0348081d09481420300101074070105002d440324046c0d8401802d441d41100c221004c090348108800000120910704200e250042c40d0315a20010130300d40104040200c5289401024a004000000c0b865481008481d02c084111000685a03641030030a400c02a680702d4003001003a00550904050045d605481412914004212804600842c000c1c00100d520454510b0160b0702156861411990a054401d10000301501c01418410344184085522507198000c3e03036901400901c461840c5c1c02030080034045c060581000c0c4c180c4488140096550580b071701082d02c13400e0301027100f605411051001420b00c6101e4401111256101d8074440d00a003002d0f140025184105462080a8200000c41404c00540100304441e1042e40c0001511280d581c1040b0f600740164000d141c0c01c1482171031009035401c5015138101c0700040b01c0b40d48042c0c5814156003110203d2030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 772037446 1250 772036196 772036211
    0x150507050406020705150f030708090607032d0e10150806070c1e05070e181605101e0203070b011202090a020702030327011d0d12110111040f050103 65
    0x2900012a9005c0f1001902e0165001c00c500e540c11a90740034002c89441050b41c000306000070994041c0b00c8034040c048800030760f01c5030f84032040140c0c2280d103c2044103244403980d000c1c04c41007641041c04541090214000803440c086189002030a04500c0107508100c2956040b00981c000c030307000300d40805000c000b4003c101e1400d00c00000f800003002c5420007010840d20281e43c2d12465030180412120991000448001c551500324245004100315041d4110b510065500046504c000400035500c14082c051844194103050030310082421205021081c002d500100060280c12400300ea020700c8070310750185444142610344040c2d02c200680c4030a03d15120508003d0140c3d5403036044070341000000c24010b84c0c0344601d02c003080c00c5d40640b00013407a034101c642c900640c004111450702c0e211041c00342c0c4c0d1118144c0250700b5901d010940601c0841d00007921181400002e00441003229109009041401038081c2c5200440e0940701d0a000d0310030982d101042c00c02100c00c00d414400043c18013400c0900c80310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 772038696 1250 772037446 772037459
    0x10e07170c09010e06040e03190c170304121d120705010f02030a0e0105070c080a0c0510050c0604020906030a0c0b0409051537030b0105120a031b08040509041505070504 74
    0x1c0c4c10140c0600d00c202c1d551095450700390010021603080b01c8508410905240d00030001400c08076001d5800d688041c2c0c07201001c0c07589040c040803030f40720729484580d8180c40784d0100001c803406507504000d060360b81d80446100c019661620382a8040344641070050541c0380c100000100005820301c0e2840941d1f1040c04a440d056402000483d60201c081c80c1c190348604e640e0038445058015030340700304524040c00d40071000344500399030741000362030080d07903159002c0940e80011202d070301c140348485000385c110102040040c42c0c030b002c1ca141c0103040107080700c080b400c003500d8503604605244d00491a426000030b040140c0160f601401d58403101c0401c0ca81c07005201800400c13041105c070903150301c1840c6002010040405c420b804580c088600c403402d111440d0712882e0182001d4801e005142c85134400c01c0c4820000003001881071030569040d915070b0340c150208000c0c0458200e041004850f03180341400040703440e84510398924490ba00a42d140300b022011200700c401101c03005499002080300402c070034841e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 772039946 1250 772038696 772038719
    0x140304050a141f120e16031104020c0f0307060c182c0106090519051f14120f160203030114030c0310140a051314010e07170c0901 57
    0x48410160203420030501c0c00c0c0000340e41803e5104030302c2001a0f1800c40e02e50b4607074001c001c01000c82801d0001c00c003215a43c3c0340e495892050000e4041c0c080b99204050000032403065200c1c60001e00a0809420002001c980c40c2c2040032100fa00705542d800460854144120350007521500328260620382c504108020307400c0002489401070481c04000c00320540190901c41c0300311010002001c0110045585862004162100d0b600c42c641c031a56804c001b4054644000c00740900b11000100303440e03401009280c4026250030390150000900c00303105101c0480d18a040c004218aa140c03108001c19403070b01d9803842c402e803500640f0b80407200300c10100310b6103032603000821030381034a11104061b01640843c1d4000785c039004c4140501601401101da1601c3c52040c1600a11640404500e042031150350711140d410490b80300b02c0c2c9900300e142d5200e48542c081903c410220341210900e4002087c01c10500700c95610b4156568400594807059103074088040740244407407a40d80d8030850b8401e030385502d0700301551703a07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 772041196 1250 772039946 772039949
    0x1140a0510030609080c12191b110a0905040305041d06010f08181002030702060c070c030b04020d080c0c030c030c0a17161508070c0201080403120608010f0207140304050a 75
    0x1100d42d00c501900078080b176a1700b990010080c1a08030b030b00c64496030f00105000d030804210f682c00071030380380842d1800c03074010070f01100382c07010f28007107804168000d88407900303500441c3c8161034101ca4220400305096010b4000e06200300e000c0d407078035956180b809040d844030b050074000070070040e2040c10500c05960b910249014408505141041c866100e4050801585114142d030241900c103518000d000303190301d0380141d03214201c0743e001e41d2400c0c4e403081126501c5102c1c1690080106074045420b00004066034003503a0014000ba007e05100e0714036a80d8008c180e8081410005280d0103040352502038178007000f416541c04002d9026004698450000c164291854002d4060b01c0001c1c0c043c1c0c51800c50108a00844031595290402b405540c0d07003041c030b40301c2c030200c3d0120000a9a500019034494090300810044a90680d0349808aa0755510201d960700011a0841c0d18191140b00014000000740211140701010f468016610401c0f843c240807801160340b251b1074a608140002c00c1140c0e903500c280070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 772042446 1250 772041196 772041203
    0x1090810051801020a02251d0403030b09180c0301060f0509090309060a09030302010e150703051302042904050c0f1c2a090b04051c1401140a051003 65
    0x5aa42c0740e0b041c0c081d5200070049812041584042646400720b980061041c801d407000d074141c0088080175072002c0e00c0201150041c2c440d0308031013121045400d00000c0f0700d181d006000e07280018001c24400006001541c1c1500c07445200d4440c09a1103000c10401c1c000445044002c4008100b0315203450880d40c80040e07548a00c61192900a00280841109008840005200030142e070750f9031440e65006000200c07503010980040d1b20700345a070701410b0340004084420f100c1d4446282c045171746800e01100681001801c81504440840d00280181c82c2c50203503900c6c604418100e05450170490400d000310351546028188a2420321040c86070002c841021210440001c001850b0346803048003051440c0c200440e6004102460320300340f84a42c0f0410f14031000306200241c41d890b244400322a0468151406000d5400310800c1003101700114540a00a8441c0712105600720318100016112030794000c46841900000d6511a41d01c0c00748141c1005c0aa98806c6810500304458200001c0388003228001d800002d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 772043696 1250 772042446 772042451
    0xa030807201b0117010e31020d0303090c1719110108060616050a020109051824040e1b062701090b1602010822110a1a0c0c01090810 58
    0x50364584d2144a0b41c001d180f46a403003000b06540c0da0084030059000448618400940704400b0f84a5074501c0e84042c5120902c92200300c0071280f0603002c106000244074400c40c00d00d87d640d8007400c0020154402c0900600001007402e85000701040c4260a041a44c0000d800f126402c00d01400021b850440b804612071007842d10144907038803032000c9003507449600040c0c6030402001c207040e402c01c4400503d03240750f14401c1e600e241d038a075030b11003d200b400950046c06801c0c40d45020001842c0308299240b100c503402401c045903600340501e601140440e4402504500c2507004640a022190b40d40080c0844006080d9030341d1b13117410142110b0100800c07244855408606203807104040e1680314080c5800680010480a9554011801d0108406e900d00000b00d002c40d00110000d555403440541615201d07402003003c070008401603450a4100c1d50301e5011030342c441252940807400d95004074102080c00b03550a0919940d0703400710a2107140202c00a04c40d0704211001c0418031010101240ca00031611300041f02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 772044946 1250 772043696 772043743
    0x3120307170408090109150e0904230102091801120b0601021e061609081b04181a010b04210c030503131703030708070507050a050a03080720 62
    0x115640c100e4010100d108508100502c001d000141000300640f0000741c0740d448400d50350b40648011144000c00d12030220300303c444000038504220740341e00d5000303114001031141c039031040080600714040c0018008560703501003400d101c2403c0041a01048046098040015614144609076150304411000b418072000303c0104107507034020480070000103124800600315071040100342c3c1e82c0f03503011120529040c0e03010311041902800b0300d0510040e201d40c040500104ca00181120074501800c0002d5074101d6030f98207030703c0440901100206d03800380c0700740320344100c090006061001610060300030304c000440410003000000389024140031202a0700e001c64200312030a00f48500602c06546c07015000b800000f450362050710740781c000c400c251402699508207460b01040c107640d0b00d02003200e0540208007050046440a4015006011359034480c000b01d4030b5030607261751021300300ba6640000701c02040900042c031001c1d5402242684290542c1c41029201c1c010744056142d403114101d0007800782d8840401c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 772046196 1250 772044946 772044961
    0xb010918150b0907050a0e0a030203030a03200f0702031513021203091002010b0a09090f0206091c05100f0219080c12090615030601060e040b042307030c0e031203 71
    0x6002e11800285110760900d031440d000380c45984100081d000007000200c0d0500b01d450401000415030345c000e4001c50070310f18521001c4d4002c288003050f801007800000509592040d100d0020030110451640f070584a41041c810b042c44c6c40000d2001c086550708078070800100b0503207000a59803c5804032160185000c1c1116254294440d41440a4001503220b0402e100e0a4054224800320002070316162202c541c6c407034016044507a92180100f1548804100d00090b24220300505507124009121a0540c004100c26110004441c1d0048400d5003043c00840c111217924400c007400d07446100c03001d501e0510045a10507920b4194510402804a154003107483c41c0d100009803520341041e103000c0c055034241003611598848040f5403062031140300c1004051182401304809048650390340300c20618101c03010401c405041203034402d54100b0f5503050305008220000c0e200b070745d015240d00c03000426414031200c02000e075481810448180044005000090349001544c02d824000c03102c2540c0d1240c0b1140e8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 772047446 1250 772046196 772046201
    0x1512040f0b100602060c090117150a15080c0c0c0d060f06290f030711010b090703020703080a05060d020402030a0e01060303051201320127030b01091815 67
    0x140050810705148082021080c040c41d00c03075041e60015005c82c0c1941e6500034210301d40348201603580e400200440c800e10540140e1507116500300c03071000b0641c0c407001caa80001c501c016070240c0c80000c400d04070200c440c20b041d070061010340d004030040c1e00d180d141c11b400f10007070340d40e86407800d94450044074403501010505c0601d0f401880c0c3e000c1c802100f40b080a1380c0f041403464010f0038000980c11140b00315078403d028002842200c40303074040342b03041500f1566000011b0f02c4009100f410030340d0035520340b21034181c03503a60559414460201901e0050300c540860900070401500240008982851b0009000c065078079202040300c81541101d000d0380d240c0d80c190416000d009488105c00c2d10350b080080c08403c0503044006012000d080c0000c0c1c0a243c1c0e41c618585080004008012640c04d030041c01c1d18580080304c12400d0394240041c10224440e1400170900303c019886a000920300d03080350f000a00401c6107001c03c290041c65a50810301c00d442d00e03480c002c812a03541410041c1031599220071800c2604894 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 772048696 1250 772047446 772047473
    0x603070b0a0c26041707061b020a0e091b04021603140705030703050a021905030301050d0c030204020c071a0a0e0d032d020d171f0806040305090109090504050703060222080307060b151204 82
    0x12a192941024031403070356505622050080c00400310200070f00541031034030903240c0c60300b00000c1507041c40102c0d4701c0680e00c1458030303000080d9810b0200451030100300304000601d40701d44a030b80c840e1340c3d80c1030b018030003400c05150b0044880340d40090580032000c61400400c0e681565012943c84044600da0b1600380e032700442030ba00003504240049000101d81c48041180d50444100c4100780c030030419060302c0b4400340d11030180501c002c83c5c0400b541c00c440e03061250301c507641d10307100c1c3c200290130450002d51920b82c005c50524400414081c1100c049050758144007000c45a582800e04d1410681d1403d0b11113030202d0001c006104085c408524200c03600c0602c840a0018003107001039980505150070001d205500c1148d441c0e0209001c4000000c414820f4800e903481160800041d10505007142d80d00000b17036001811802007403191807521002c10307610251520041101400031590b50303203070389850340c1603035100342c0083e11030080310001c89007020040040700c54880880c01d0051040d503ca1421022641c0d98 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 772049946 1250 772048696 772048709
    0x60a05100f08010903020d0c15050411180414030a05090d03090e01080303060f220f020904180203010f0b01120902130c03020705060603070b0a0c26041707061b020a 72
    0x740c5600090b0004194004079805000750b0030750303511980c00002a900c0300c3c9aa580180301d0010303800b4000d2001441d0384030b150132500c07440951140b81c00b02d000145d03040c0506018081c1c10356200041c442001040c0090701c0b014804c00d0040e42c14440c0e0240c001d041805103048040c05001904500b07001c040c458840240904148120700006584500440c0d6582c0c20465419000d0010604503407403610380f4006050356040c3c10003982000f02c04610b45540501440e044d101942502409131408594540c0613490f07910b61000400c411030f0100e4010142942d10007052596440d00d40000308174240d92003a8102030507400403801240100e60b5101160456410400a5800c203150200c03010746c15078943c009200c0d40f4020001c031140e0f511400e0030583c5985d400d104010050781d04206042515000d50f141c040024001e403428082c400242074600ea92106c8000d1841841100040a016000c0a1001c42080c01c850100804003103040000280c10112081182ca0031617682584410842d0b880c0d980e0400600708 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 772051196 1250 772049946 772049969
    0x1082415090c190207030b070c03110f0c03010b090708041202070806010e06011d01270e0a1b02010e1504053408010b0906210a0305070201090b0c060a0510 68
    0x2000c030755451183e00440141880541c0380c250b0b01c50b455100203945420380c6d40144180203d0b4440d008152400a4400822002d00c031000103051096041400300e4541c0d00c0302c0d640074103840840d41082508507100b00c0155480340001c101800152644000d1041d030240e4440c540103420001f0078000d0b40b404071181d00c903600d40d21408001046407030f445803d0718090942a203648125040d01007400341310f0380e4165025030005203003032400b005102000381000051814841d110440701e80310342d44030503032480031648154841e880c0c40712000d889100c200c200300e4068140c0f008000042c40300002e243c40d2050b40c0000d40f803c070300d024045014072805006c00d203801c01c031031000546002d00340401c188a801900340c1040180a82c0d660025181406000b01c2d2844107000385182c0141d92142c0c1044400d49035584014103091001c9140d211015081100411a902a4440c1ca454010900c0014904890754200011a0109221144d403140340000c0058001503040b402145542e0307085403004456005a0040c042c200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 772052446 1250 772051196 772051201
    0x50307171207031806021b040203090c060315040905010c081003110f012c010807030c050f070309080703030c0c1410030c1b151b2c060c010507080108241509 69
    0x540000c0c0540c0c07004456054403000c0941f80c82000100d0000305d40004007078202d0f2145600d54603044d0001c50b406a5034030510719000c00c8080115081b00c1c0c9842080300e20fa99a00842045076130004001940712100400c83c0403120b00310b5035100c01c180b08207a40769000d5001d03102144081ea006d468400070200810450621160340013262040c035891a00d501c13030200e00b0200101d01428801c0c050081c84200588801d0b00c3d203580401210002e9001d80025405c10541210104010000b441401e00444c001d03a501c0c07812100a0030101814605544822528440700d0314034503240e1120b85003442c04400e05d090000d2051202801680c50325000101306e0950b008210411041001c00e4294007401d00c000302d0200044409840300b0910f5200c660802000f00c1c1d004040f5161600d903900c2d070761026050401090340e4800002000c9a1a03800040103010756946440410000e190700001d075038014040040104983d0441070a0781b51640ca00c0c1129100070b1210100144803001c2002115140d0a0058448102da1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 772053696 1250 772052446 772052459
    0x30e46080f0712020d02070303080c071e110d0309030204020c0a0204020a030f0506040b0a050904061e06030605090d0806060a03090b040b01081203010f06030506040e0a0b010503071712070318 84
    0x140d0102d03800f1070300100307408183c0c1c1940c0d20009100001050a030002e10600781145c4056900c010018900a02c0000401107000060759808400801ea41c0d00d50042807440303200e10300703402800c4148102c68000c681c039080c00c0010aa02c10441c108480e01610016590712844403443e081c4080320a000e50410300001ea400e1549603da1720012403a01000c200704003544800742004152010f020f01594460107206081c0018504001060b40191184000186d25188040b90070307100340d2074004803040d9a80d5807204005002c4103008256202c204a005024491080714018100210181000d4082c22001c10a444014048d43c004040340750403826103e0321b45890701d001800348000f401048554050368021a510859001c1a40d068420040c11245260300b000b404078020a03000348442d078060384540000b0a007101c103104c040d141a0180003240d400d036040c4004e061074241150700040080c61101c00d640900ca03000304004042d40c003000355555840e85281012030f9072084041804101d007000007000100c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 772054946 1250 772053696 772053727
    0x1418010e120c130203010308040b090a0e09061806060306010902160503030c0903070512030d0b01141c0c0507050a120201020f161106030405030d09050715030e4608 72
    0x40b500708883c500005041c010344603050380802c4c4001480042c0c00d100606c101c0d265880a0580200064140100740b5503610448220b10400d44094010b50450300502c61400c0440300f001342c00e03494480080c0a80c1c1031a03000711703590b6881442102e800c0755012070345007041e840340002040419004812662241840c2402d0b550680c88004083e04c80d10a07031400041504140d01e102490003031360005141448500520f00380607010302d0078964100320000b40104007144603c80903000b03001074008030846e030f54102e08805c411540311100341c400348030080c0040d2000810000b41c0504c40e9910580e503980c0850021826406030041e580d412080260106110094240c1c00c0501042e05024000d1039607a0b22034203081c00100d11041d074000c2c020350010440541d8040c565004240c11612440c1125602e45c0d550a010280b0103848002d100080c1d1100a07030013001808220310f41c502012000511103100d4014070340c491118084200c00c1942c0d41c0d0300640c541c41030182100d4031450b40c003c15a1640d441d03003072001124 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 772056196 1250 772054946 772054963
    0x61f120c050c010f050103050706030504020f04050c070209060a150c1106070f06060b1e1309020a0201020c061f03120e060f040302031009080306060705160915061418010e12 76
    0x1256191045880a1300018040d00b4102e90f0000042d01c00942040e40481c050f00c0001c0040ea00030400202452440c2c0382c512800b8400d001554155403110310318410414508800782a03144900741c10041801030620441d500403003c000ca0400b103000d22030601d0207489918001c04a254400c101203800030601032044030482c0a83e100c0da500b000103d44988802e8402e00030b140042e101c24400141100f400090301005141104110f220460701d0fa90b42c0700c000040c0d910000803040142d4001ca9200140c80c0100040b6030002c070b4401c014079050402c1c0e0740620003089a4400540007404900300544664003030f002e25490420003030324443d5a0100503170103c0e0a54003a1000701d004c0c0c8191010380c19450440d1140c0340d0240d51009126180d03031260740170428203802c00d03841520240603c0310170003d680003180c1a0340003003032403030000304d41208441280c0308441041c3d8014410700040e050800580310041045500c1a14008000545110240c004844144c100300889030002101141d41401c43c1740041d0714207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 772057446 1250 772056196 772056217
    0x908060405030c0d08090c12101a0f03011b0305130506040f03080708092e062c3319080715120207031e05090301050a0203061f120c05 59
    0x4242880d490f60891790840d00311560811600480400001860100b20741541d0404400c200c82e81d440d40000e2480440310342c640b01c03220003900c801d0a01c10310300308890b1000002030110003c112844041000503001940c42d41c41c081056950700004000c0522540f40d000400d800100704d4541d840d1601c0c06001290710f800050300407410782400540d00030310030301030203205002c42005000e401e491100116a43c00403108044801030b040317140c808010013a032152100070480340c8603200300450420380f03c0c8160b41440680902d035554503c01c2004440d020342d500d844407843c400d1840d000038804044040586034600d0311591004800e0344044044070011f11a0050b42c14a000f0786c2c40e42c5a84045180d81e42410070380500103d004800c4810a50380c55a000d421624024205080c6544010580d101d076402c043e14500003003800410b003401d40c0d0400344074950b40190031071001c51440c1045000550b281510f030300344840e906002184445035a110f628201511030340e1501c140194a240e442c0035003140c0000c559030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 772058696 1250 772057446 772057453
    0x15140427080a0816021f18030c0b1302180a020f03090a0201030605030c22060b07030807030b01032702040e01061412011b1103040e0f01060e040c0207150908060405030c 74
    0x1c1c908052881d180c03821300c40e594008040c080b4400040509000380e40740b03400c11881d45e034100400100680c03420b02018074825600c0e024401964074015000c40d00281044000d14510b0742c81c00e0058482100400c00c4175803401ca40c2a2030382c0d808110001034414042c081c0c01174003000c42440000d2200180e000c01c6240301b600c003405041d40f03941c181560b6585080945505c1074045d48000c112002104200304000d42d0800d0200d00307039823200448002d075484000101c0000e10502c040144c440e82c10300c07801e00004000d29061008030841d2400c201d08d61101b481e403406800b1000300c0c3c9000c56503654822035507400c03890001e00500e40d6911400c18803130100304071a400745a032682003041141062050b00260140c01d100f28241100f084403c0768611601611500284000c120202d4981c08041c141c9201d81d1b809040221a0342c1000030083c44c0c0d804405000d4010b6082020201d150b503004180c5405540020a001e420105424400c4036210076651100c0c3e481e000d8941440140031020004003000c0700c00c8001c6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 772059946 1250 772058696 772058701
    0x6010c080d0207082106010f05070c08070b070c0803040612022508030a0b060906030f130c0f050a09020705071e0b07060902030609070f060806010c06050a05040615140427080a08 78
    0x40801c03176201140c84c240090403c2010f0781c0d40705d000718060702d10b040c0190107014410342c4401d0a0791500e0020b030040381c4410b801003801c000b0840c406030b01a001e0403d5201550905d854020003400c490f2110348142d18054005c500c007402d0608400d0700591002c61003502c1c0c549201107082c103180a034001c0d5014400369042001201c0c1c03508081c0103d45841001030081483d541d10103810041072800684030a48107800d41407500040341c11641680b01904880580c3d0442d42e00e003004101500c0c000c0d61001102a005100c1100866808901c0e20f00b01e8180d0b03000420300810f01c00210100605582000d074a409002c01c8180910005a000084107807081d400c6465903100c00d486d040d43d03030300244582c14502f9038402c1d00b40803180c418107006804c503030306041444e03500c0039955650007901c00480301d41c0821030340d6108210621406004141202c406145d4001d03643d401c0070041400000c8a0058900a80d11410034401e103111988610000703422880d0303800b1090040385054078156110a0403c0001901d1401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 772061196 1250 772059946 772059997
    0x2c0a060e1e0f150d060e07050d020d060b040b100e0f04021903020a021507020604020f010f0906200118150203060f09040201030b192c06010c080d020708 67
    0x801a110020a00401a15516401080855103000303110801800d0700100583c0c0c0c544811070006034061080c00c020840c2680568144d07d8100554002c41c031441c1d001c2840c0340940c407021051005150403100105500d12041c01180241140303010b90350b008000d0400d03803102c0d5a400340003425000e000700c1d00240e035404480d041000340d000794156128605002e03140001c100740243e0051601e94040d0050f1610141107e400040d83c1744201d84c2400980c02100c1040118903100306031038136030102400d00c8504030303541c0c5c64020b04c030340984c7c043c240074401f651021548041c54061074440c18070000c0c0003880710124003080e42c00550700e92801155500d203036a40c0d61800b02d00500a592107004043c1002c403901d407508040018024000c0c000b0382c141555282c0000d060703150440040007400744031490780c01962800c40c5494544407584040740d00207501c0030030381207d80d035100070321504001c091805110b0281941080d05861049111760f014681c40001d14504100c84d40c0c3c090176524120015441500d0031481 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 772062446 1250 772061196 772061221
    0x7083009010504060c1509120f020d0813050c030a140d11060604020702040e011d0c0a030b0601080405030d05090a11030f060c0c0109060612110d03092c0a060e 70
    0x14400780032440a200601c0210300c100746482d000c5002e2a05a85241841c400c008101c5410b1102a105d41c06440040283e041e048964403620040510040c007044c0d040c100014040000235244800c698941150041444020010322048401c020300b070721029080c2c2c0c03a188491100c1c0340c640150034020140c0200c80c0c18061000000c94824080241c81207170350701e0080000a40c00701c1d10132070b032050b030f603100148009000f4425100c41481c84540d105000c00403c00b81490704402180d0340d403261003525030034000141d05002c019000842030810300d103da291464054110f0040031040c04080b45800c0c1000f0234480e000a11171400c602409004101c10034403010f2648410705400035803016408000450042101d0400918940603600300000302c00c07000d680c80500750340440d481030254514841600c024444a075101074414041151702c0301d0b6800c41c940c2c000d0b004480074800c41c0c240e00b102c1410710090548282c501c401c0061a801070080360b20304020107500914440c010036143c04001400204800304c0365 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 772063696 1250 772062446 772062457
    0xa091205120906192102091e040209030312041b14150c152508010611010204030b040302060708010801060506040302041806090812100501050a0809070830 68
    0x2001510080c1c90034040c1d50141c0d40306900b4103401040801c4076821241140c8400200780140380e5501c910b00803490380e08010a0b2a20550200d6240304100c4000182c0d01c2c0070030a09040d5410300784403080030802000900034020710700c1c1c0d6a018040040d0007076142c0c2d09192007510991083e80002d4400707403a01003103900381900340a6400840c1540703101903142c5c6040c4100c860b0120403050454545040d040c0c826003003005408140341d90030f00c1d8005200e41c9100c0400500814011656801004140a580241080010700c6a0000d0055585441c0103114080d0108c4010b940c120300c00003803e0030300707290003940c0d03400c202c4519001071100000440d9401c81800b400c030417190300030f0040d03007014156000c010040810b0300c90a0a049490b54440d0001a003d000d180030b84c0f8060002141c84902514509a40c03090003040c540f0070380c1ca00501032215030f07007140130f81390241481e0ac1d2003102c03959400c0800b45005a20780202d01d86215102800001c404820040d0204205020807400560003003a030514250040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 772064946 1250 772063696 772063703
    0xe010b041514180f19180b010e0d0f1a0106030c03090210051b0d0e12070518041b0905180a0b042a03060603020901080c130b1302030c0a0912 62
    0x3080720000820399040c0c1003540d80c90080c504080c50f80d840c13001500842d00794044100c224045482003103501c400d03c0010104281c16103003448100b0340e1400003809229507030840ca01c11a44d500f501010701010310315900f00540c0c098400887c24007042c00c4201910004d2141c10700081c10900ca00700341521174000d480d030440c2d000c2c1008401070400c80003694680c0150b64401042c00300e090706804402401c012104003003019480741c0d00c4080300c036018800401d0751a0000005903110304420401501c44000800702d07420f00602c0d181864981d4988031040c0c3e10b00c220385ca0100d0314800d43c0410794560590103940a148101e0821103010035180049446243c1c5000180440e01480c0005000c10f030011403c2100c40421400c940b01e55107001201c0421880c990029110349550344030610840c284042028003500030600100b01c1c7d11384401c00103840c5800c01c1d40c07021b103103500e071034100e10580c9072604205184121040c00b0364507480d00414002e0150030a00820001540304a0000380071170a503a110380c1c03025007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 772066196 1250 772064946 772064987
    0x130f2d050a060f111308060c031501051e030708061309030c120c0f030c12141603050c0102040608090c04050603030f0307020a0b180d08090a1403040e010b0415 70
    0x52601e62400404a01c00c0043d81c1c0e5454034580d20b46410020001e00c5551400603011213064140451240b0f040340c020000a0040010405c4c42060304006400d540100310902e00580c0c2c42c420910407054041074825011502c10000c418006540c0e000f20b8417038480c0360291500c503014142203250505980340c039100913010030824198840070072a55104000040003c0c18503075501d02c610f9440d810074180d101c4007900003800041aa1040116100d400c411000701440c0084040c080d0095a000d14401c00c0c1c803400c8402d2110300758100f01030241c0d040e14909490b44d8001c54540303a8401c0050700e901011181d0011034061000c0c44600c1d0310b07081c8500790007898094010f6040006400d51144194000b078912400e502c64200600001105807900314400ca0480032154945540a041c8529103010201d0a109000040f4104182c0110010710300100c80c1d00040a890700103107854000d402e6106a0b080a0182403c00001003a0100440000c0c42154090011150f0481d98048100d8017451a001c2c1c8a2120340e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 772067446 1250 772066196 772066213
    0x1050906040b0f04050909070602060903030f010b030402040e0105010b0a030f110406050304080913140a2a09150509030d0507030503010504020c0c1905041808030f130f2d05 76
    0x40d420b4000c1d1189141c88500d5070319054464001a030031090840d020070b01da5000c02c0c020700c00c86a051080d1038011455000131421b40c145000700c054813441c14091900460404000102036585a400030700084d8581c100801c15943c592184c8580c6074402e111102c08607003401190b00440e8404c0c483c4109526a0b2032015007050704218048803642d03c094019562817209110740a40d0707580e03005c01d8a401801080001881c171300d4001c0310313031501c080013040810205d1030f02c1c9c1d080e104140a0b404003050886480101858100041000d5503440001d4009040c00042d41d14050061a0040010908848107c045079001c1d0345105084606125030000200098000c4c07004014034200754000d05280801102601c684040010101c1c515600c07040d10490043c2d01c0420810003800c191240f1146040340c2c28040200d000741d900d1740031a5200250900700030b002c0800010303030000ea140500b4000c20f94071160f40400d4840c5410011a565006136091003482c984425118681c1400080c0340c080c0b83e4810040c00103079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 772068696 1250 772067446 772067459
    0x10060906141602150c0106050f040e06070e0604031a0a060f120f0201110d030506210604020f01090f0b12010b0a0c060b3705060903101e110909060105090604 69
    0x80b88050300882c0c012603100c51045020240502400300c00d40d08000000e5070390710341810071407000284d20800d40601c0ca403035000d0301403c0b008105298401d0090604403a441e41180100e04140b1442d80060b0400b590201c203204607a043d617410031b01502c0c102c03030b0900c41140c07030741094000c0141c1031240b0301f0781ca1b55800400300090181c0b000d501425005040003061407a00d901c289041103d0100316000090350381040010310b180c400c0045100c549009084054501c0d8100b034076554140140c0003034854242c1e000c0c440e42680c415181c0c103014042d00405c000040d5640c913001284d0340c000d9941404480c00c103600214a419569099811000035031f5201c1000d2040d94441400800010031400e810a40d9801e03050315101803624864012109140c4a20031544d4520440c080d03604190802e520903031080080010682c2c001a8050a1391000c90000690501400d18024140440c8160f412258203060101302c071540310f000500540c01c0107030750b0509107135508401142c0b00c3c4603000c01c0c0c6920840a10060190 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 772069946 1250 772068696 772068727
    0x4030b060612180a08190914130f02130e040b250503150411040905010b0327010605030607080601030b010903032309030304090207050706080606040b1c051006090614 73
    0x252034014080e1144c203400760301e41040590201d045c0005040d1004640241305a00c0b40101008110b111068100c20b1085800141004d00c43d10682800544594000601800325412075001500040004220310ba482084490706407044505584070b00031840028078410b10000007003404c480c151641829186041000c0d220307900082d003582440350f40e1340400f050300c0c1c413035114a40071000c0e1812013030b0b1201d24200c015000c3c1d44050f00140c030159024020300002810341b9580012108602c0814209142009812801130005a1000758580b00c1c400c1444501030704a40000e008000030398003400b200400341b0064038100d030b45100c000c00040090001040009101e168a560a4005003d06241c00c4c2e5100000b03165070825080101c80741c0d80021002d0400c032081100300f000f00f049081c03203602da1030704000044041c00395200720300c0440800a81c428940841c000c03414008000c414040001e410a803403034510a0000c5e000300004140350101c00b04030b071030180d100d41c0048001c15212a1a2070712900400c40e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 772071196 1250 772069946 772069981
    0x3080a0203060901090c12110c0f030405060a051c05010902090f100c08030a090807060c0e1c030503370606051c0b060702150324010e0d0816030504030b060612 70
    0x1c1007000e07c1c0c4c0441340d00d4240075a032500d8240e07214a0352100ea15440e4141003c602d171170341e00d03507503401000104055200d0074180c800340461810410384400c540c4107400345943c16200c3c4581c8541c82d1000205510300e0301e901a00f0844000e540c2090620020424001c2d00d0111b0544000400c11884420001070b1600c030040d9484480054041038100ea160b40e00030903500b008030121180e6859025030381e030f000da01c04c60018807190100e4500030610100d0308200030744e59174940302070200803000001407187c0203030b40560030340c81c20180d0a44000b00382d20344c0064014045280080103540c01c2001c001902440344007035566520311405075800409074099002c004240302c5180d150000400e000400c003503510545412115403070303241000c3e601d140034504a000c12500301d41100040800305121600c42e43c0c403020b01380380c2c640700340c800c1792960005092509050040315034201c50b0462000e540010964880003a2040301c0c8621100d00640c2c640344c040003ca4000c2c0391400e42c421115400040f0454418888400d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 772072446 1250 772071196 772071221
    0x90603020609091b18090604063206040b1201050102060601120e0a05060c0d0e030412140a02030d02010c081012331a0114180a080d08010303080a020306090109 70
    0x340000103240080910360001754071080354104156108450b4145071010740d41c8180c0841d010040d039420f25451440001130200d204403c01000020b0400100c0709a42100c05000020015501c4030b5450603151900e600600d44504184101c500004443d40006101405000161901c11400000091840050020240c56000e03441403002c4c032400718506011080c0101040041d41c0d56846400b50104141c8011072420b1240758020401081001e00803030800e94107544c00480700744042c20003d0781c01e00d08400804069814040c424211603001d405601c102808006510383c24000d41e50844c05142a0f0603501c102d80020201202401c0040e251100f01da001780c03507816040b6004200800040000c240c1e60060b103e1480d0340b0b4aa12221465160424040940034031b4204171a00b942200c400e6140550403100007400e184030400d40c440e598801444000e4030624046031001c8080b140e008105400c00c0c80b05401054022012840b03044a60080360b1052201034204e03980b5928140d883c07401012030b200d011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 772073696 1250 772072446 772072471
    0x1140d05011103010308131203020c0609030a12020303190608030702061e040f05040b0603040f0611040b0705011506020a050d0804060b090f06100f0806060a11160f09060302060909 79
    0x51242010b040c003540c061805070a95945030240a10410094441e80c0c00c9004002d1203803840c080001c1d4009001d00603400305455490f1101f0441020074540a00c6503001070010030107581d040440c82c0e00001442c403880851407a841455050307a0440121240e0740600155030b04108001d2000d407c00e0401002d180500c14090001d045007501402e500b0781040d00041001c050b0003c040001b4640f0780900004200119122440d41c101503841c2d20644034200002001c140e1200040c0400c1c0c512401640d00a1069170f400b00c1d80e5070940e10b00300c3e00030f058081c03551940c0f1480e5880450a944005460b201995010000313021031136110343d054401c0c8000810441c0c08039114003010300c0ba92a5200c2c0030340102e030003005950503814400200038120b200d044285080100a000b0030b00c40340d0384100c40c95045003003918500d0b500c0c058000304a0b1290340420f00050944107800000c0d000c403594400c0381c8203c0c1c62880d4850f0320162206001c0064503118071001e07500079003e00c1641101d181940c2c10700d402c020814840b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 772074946 1250 772073696 772073711
    0xf030b060d020304053d050c16020a150504030203160f0603050a06090608010207020102060c1305040f0b0d0308040b0906010608060907030e07121103030301120807082703010e0601140d0501 83
    0x10410040c41c0306c1c0709448030030984120480c02c0150116000103001c036048040c002803911000da290300740a00307001c0714402061103080c44195100d01200e075000d4003252100312032348001030030060002d50061004a00a02c01c912030001d0b0066000d201310150b4064002c04240e580c0fa01c074080700604400742203464030344c1e9200400141503a05120b03201c001c040f002d00140c1c6a401030b00019041c840010000e003a80b003410850b4a100085642c400700980e00d0440300095540c2c000900d4400904605d082c45420404102c5903900b03143d0420304441c0b00320b208000c00c503a15515036416035101c06083c402e060101d980d0001003240ca1900c4103040741d0201c0f031481c000035003108200b180c5203010340d181e000c40c070543c1c4594040424421665000241c030803054008514651404000c4000b80040000150070f65101154550411203104100d5000884105503100300344668010390f64198007a82c152403013507290120b040c00001010558a0480b80c1c12240c0b44400c54a410030300c20030480f106400c880d59542c8255 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 772076196 1250 772074946 772074973
    0x2041d0f0c09061b101b0e01024209060c160308041406040b22050604300f030509010b011e20060601030e0601031104090c030206190f030b060d02030405 67
    0x80d28a1090a1140200301c5980a41508406020441c406010088801f00c1115540d030005040d12144491410030700e0180092040e407280105842000003001c0c5180191030315111799001d0341390050080c201600d0040e01d41c7d0003146c030b207841280885002003c401c0d0300e80005c80d001305c40c40e903445405160301e031940d690641031590030034004580c100c0f42d190450301402242c8511803246403044442c40d030300f0425085940c4502d135680c1d0009000515840c100c01d005610360b0b4560130f2027119801d04004100c0d69105048000c0e000c4081750481100003482d0000096901d4014043c800410f04180c4840c103c004000c544171a0940281c078034071040c8071074450700c00031000c0c000c4100708100c9224409000c0320b040060004040c0c03042e1140e0000c45503c404014004180d4900429115020883c1d001031480490b15007221019440e510180d844040490096107112564490011185042d03554114141031104103408844403c81503a400c1701c07083c4050031082089070700070340d0031502450895042c0c022910 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 772077446 1250 772076196 772076203
    0x5090403090909052b02150919060501180912030509240907050102241b0301090f06050625020d1b0e0123130e0102041d0f0c09061b 58
    0x4034104e031030358401076401038050f8400d80d0f968030242c1341000140d048400300c00000c0d071b102d2143c6101d0031841d0b00900071402000c410040100c10007984082c10488020701d04241004000c244110a050307488541c0103c0c50358510311521004035070003a110004485604021001414001c0c6000b1540c0300d080d048000030040c0e544030000303010181040150a00d01607a545052a480b548070038155408032009d4089400084503d1140c01903120a2440594801e080811413007604049219074000000000c65411700b42d0300a40d243c170340d142000b4003000c0d61b40d20034459207115022840b00c0391208918401060041e0308202e03100b1900040c503180013110701d41c44e0401c6101d10000e0703030100c075113800004105d64858102d02c43d0040650341c1c0148100b4946400103c5100300c4191120b2052148440b1076104940e990b02c200030b0780d42214003c40d1641d458901100d00301100417120020130710280006940e040c5440da080b441040613032030680c106144034050007043c0d081140d840e50b4012806200d0508c081e401c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 772078696 1250 772077446 772077461
    0x3030309052505030f0f070608130f060c20060604110c01060608070809070f031220012403120804050a061404290601050a050f16110d0b01050904030909 67
    0x30300040640f6050400d40741a0003500a1503851304042d070144440b20022034507504456850a00c942d0b2541e5080d004040004006001010620507215081c14800d49034040c00080d00c0301e403500f0103a0030034001c0900010101d00b080492690041c00040d00905080d0464070300c0d42e4080e41c4440c00d051440303034420b095400d2a004040014011410030401a90000940d41c02c8903200002d00200c50801e030814800c5001d0b4013019000b298503400030b100281c400c0e11240c0da2a241c001e9109105801400200e001e0000f640d210074030094400220131384c20700c409100b441200d0307012030213100c0460742180c16a03480308014010b40d400d0188010f17a1021802900910469030000c07a5419030034500383c07500e10981c014641080900285025403d0001054520020340180302400e005031503810388034041b2054071507051748040d00b94010640f100e2807401741c056401d020380300d80c00c400107403903a80d02480303c003c43d1a20041c00c0c01c002c10740100a10708016140c3c941080c028503080410717a844039841c50a55030324 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 772079946 1250 772078696 772078753
    0x905190203151e070c06090c080709140115050c0d020a170705060601030f020c011404150b010906031806021c0b0f010f18080d020a0501060f0f0303030905 68
    0x501100046280c1401004030b01c84101c01510b00508080080c4280f50342c64090f4000c600c036140002c03d20450280d5100005154003540900440d0b0603860711a4001d5090b1103a010a4418003002080169290140108804e0420130800481e80380003000c0030625480045541444401c02500000349000e103e8044000c03516001441100074a240c540c180c0c19180500303c8004405000e0800041d2009c01e8164100000340303030101c0c8095254803104003d100307124950206600e0301d44560800030005903481e01c44c0d409aa003003948030039120312080540f00d010720001d00085d0030810030b010303640c02076101c3ca05945141198928550f0b40341e403414100d074000c3c0102c0c005442611000c002c80759080c000d81703641c400d0a81d982c8003a1400791001034103000381e400e0564280210003000c406442c40c2012104010200002100c1031501e2022029440d40d90500c01521344c0d50901f0b202040340d44501d22b50f64112100454001e00711480c68404500424400e0300842d400d005411800d02c3d4861010b04144403000d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 772081196 1250 772079946 772079983
    0x20312031303210c0215060619030914011d0111030106140c10050109020c210406030f0f090609020a0608040201050703051b0109111801050901030803090709113c09040905 75
    0x246001018131120040145129480810500b805180d2083c4c0f03484050019003002f00d54107150b032a011500c2c6082d1050068590320700304c0b40f1103084444041c500000600e007002080b606000306400c0a80d803100340504404a0116883c40c9901e502d00001042c1694a14054a07405c10422a000056440a138408440d42c0d401081c404610b00e014811210070105e4040d08800d0001c103540341180500462140c5814075a44400112202c061600140020001c03400c0412803000c0342d1070440001d1880442c181d0007640001c0e8081003040c0200429401160161509414055180d070112125031083c00040020305080c42a02c0824009000c2c0c14141d506c911400348902051390240307ca02800c02150341050155400100510744800c000c0c1d0b81529000341d000340d030740d0380ca0341e10390380c40d00c140d41c2c1c024803016242840076042c50b8a01030240c01c500002c0001c00c516080c02e00c2c0d20440d03a5540103801210541c4040d4050542c44051000f000100070161000c2031000c042d894a50806482168401400c3c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 772082446 1250 772081196 772081213
    0x120403090303110312011503020706050a02221805070915080a111204080702060418020409050601030b01051803071701150f060c030e0103090609050109020312031303210c02 76
    0x140c000c600c112407290f030f0300c000718245484908401044501845542e8112208000c040d10051082d0106d07031500d0b40082007400103041c51044c8c40c0082d440000d5003460603400c03400c4110000e01c0e0310020003c561a55180403405265003841500420002e00f180d030501001c18000114242c0e145640210400c0701d4842d2005460700101f81c2c0c0c140c0f400301d14490000c443c108041d00c9544c0d10541400c0c0c0198000c000319484144c54408586140700e1a005a080003000262020037807032190001c1044d610551002e00c659214807005609940c10b00341074602054040c0400030404215400c0c44441c024001c0c211008290380d0f0400c0b08a900c601a84480303a42d44900c25160a040f02090000040160040355071080c0d20b030100083c140c81e2026001020420401070b0601503038426040280c05039000328081000c03160314603200d4020400444101d01a0040c449480c000721000c81c25a88201103400b03204201c1d800036039007107540d043ca501c40c0780180c0004814034601c041c958400c10b40d0042e11034009103040c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 772083696 1250 772082446 772082453
    0x92d0c02060a05010f034e020c011d0f0907052502010f0c03020304080102040b0a08060409020906060a030204031e1407051e12010f1b050405100e03031204030903 71
    0x20800800542c2d5141c2004010420984241e5020301183e400600205010040110b9164810030f00b28100102c80c10101c14405a14081020104440341a030883d444ea1016803809a80742c095400c04113006c510090002128a0341211001c8203422006004160741541030001500d815400d4078001c2c00a1400b2400e01c1c0c854010a010f0f03190b8044102040582d0195680020110348030300610070101302500c044402014020400c1d68050b14401c8001e544407074580a0303110040d08100c040b039000552080c08030b00281000c1c41101b0340260041e10f03c4181c1e98070102402210340c070a01c0c1c98010113501700000130203d0b41c80318841c0403078000008040b2418000d42004400b8444164034602d1a80001d0030801c070a0307072080c0c4649010540c0b42c0c00341a04080c110001030069030b489081141c0395080418006000003680e00404603400c1c403c1c9007904205480c1011601400303903000da90b030800301fa5a2500c0c0c255004040b8800d2040c0001e0880e45400720000007a0300e03510050383c086010960802003407040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 772084946 1250 772083696 772083703
    0x20d1506180308041710090f02150a27050d0c140a0e0f0a1b1106100b1b07030f050309031c080406051f030804090b010315092d0c02 58
    0x50007000e407810340d4624196240c000f40c42c031480c4a44944041d0b086019540401c0a04c040004090604000c1241c04114103000c20602d4000c50128820000c0d5000c002030b070b0203020265001072220759103034a44101050a486880c0094180c0b017592003010800001340c170b59900c00300e441c40d28402d84004145914101d0180181020540307903074401c100c881c205002508411103455841042072200764542d031140a405002403121940d6110150780807001503048980080e6a101200364500c1140c881da620031450552512080c01501e90100c410002e256941c1503680c0d60800c1214000c0a40700700507a03a50b81c81841420388142100d06800c003203150740e464501409260000580150010344500181e50000c0201c24004c00040c00640d0324ae000c00ca40075905400c1c0d0a1500d0b0100700c000403140c0b01c4c101382c1c4294009105000c001ca003400d803400c8055119028400d404051f0042c1c0c440d229081c4003111014107105403000e05014144a406424103c559000301d40200320002e0010f011802604c0007400e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 772086196 1250 772084946 772084967
    0x1a18190f020d39120b1c0201020f1603240203090703051507080c2b0b030601051906080c0c1b0f04050603031b010209131410030c05060c01020d1506 65
    0x90f208008884240d10403001649a1501035600d00300c00c000103003d4508009260f20500d4a03082400d96268902442201c04100d48240c000d80032a0200d060b445540d5030b075685642030f013200071800700504000051181182401c1c9a4242c0206c80500ca11110560120303013044500c01200d0340000301c200b00b801001d001110005001c600030102c6441c082d680a04100005400f0484000c07001441400f016402e4403800c2008a1141c0410711415149240720003901000c0403041c803c2c0503403800043c0d1031504117901d8000c08070010004100740d241000c01e851282c8000c12841d5414801c1001c0075001009001c80301d11701d80c0032101b0132001c0c8020310611691401014400b1b00451910041c042d0595000040d41c04d01e0f500c9041120342106c00e040c0d09406401403028054000032a1300809109840d540c00050603801801c012000e45d03981d901c404030f01c045980c4809401c01e000741d4000c0c0054145030b0020680c10b50070500251910184074020b504440c0c044015201c0c036034207801c042c0281e0347d0128807a103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 772087446 1250 772086196 772086251
    0x110418020f0a0c0615030303050117010b1e0a0305060a050a0e03070c09020a09051f140a0503011208091e010e03070602100203150604091a18190f020d 66
    0x10304180c9101c9514207a441064650024000002083c00070001c280d0007a960807040c80d020107061503600d1074060042c201c207001e024400a8580e8000380340340c2c014401c011504100409150340038018802001c2d00300a590030040d0400080b440210116804000c0540101d041840015091900c01030403070480d01e0412078014950400c00660000c207249940715410b6403000440160b5030b6601d401c0c1a15040300540c1301c2a0040c0c103540860045440c402c05400c0c0782c0c04070b5129840038100d11240412107202d01c40c2c101010980c140018428819941c002c62070084c411949140f03824429000500c42c0d80d043c050300781060854882e04411540c1c071035000308031500258000c003a4141000000394881d5040391104202e1680480003d190450295107548005005444c9640da1600c0d283c9a00c041c2001031402428004038110001700740c00e11041070014007145820100c2251501c1c44441070002c0710042c2504a642c03240c140c0c4104640d544000c194986c0a4880000c0d0102040c12010140c81a8640c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 772088696 1250 772087446 772087451
    0x6040b0a05093607030e010f0207021302130306090201020a06090f0516060c080309031902100b1c020409021503070f0905030a080f0309100f020a1806020d0e1201110418 74
    0xa0000b41e41449020360481c6205288129070361316454201d00810003440004000d41c200f180101c004c01e8185d0003015181c0c0252158501184413007052401c0e403003020a8691042c01c180410004902150b010042540c4148141d0759106055116038040d103044c0b200580c0d03490600c11070b840070000200540051035820811200f4003524082004d03100c6d561300d02c4060034529000001034100e180600480382d0010b03450301030342003d41003020700a5680c1c0c6030804001003d40340040050003850f041c00304201c491100c03a200760305400c159003440080c0802c188100d800817039540c841d0b184c20764503070042c40c070404003a5600d004a100140c0f0007002c9565aa011500a41004680c440402d040c07030112607009864000f0307a581c030784941070303500c0c40c0c240c100e503c1e61110382c41c0c07240704920306050342c0060800c1c60040e51580d10750315501900907105941c502c150005a84840c04610340c0c240542c40040100c035004100c03a4010300f004030800d09482107401c200015020008061001c100c03034000391400d0042d03001c0c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 772089946 1250 772088696 772088749
    0x4091d06060f040903020c0616030206091f2c010509120c07060c0203030d42030b0606040302060d06051008150910211e0f02090606040b0a0509 63
    0x89442502c07a1000540142c1d01c40c052034082c94000c1203c554001406485943c1e6006010303412040c284034408118010301900000c0380c0304080001d4114902c03180c841c224a40501600d0080c4002c18112550840d442c00404410b1406408a2541c200c07061440c40040391350b140581806080c1412000c060141c072105100400c1c6050b80080d4000c15100107042c0038503017600740d00020b4614042e80740646a211f040c038800c04c0d41d42c11028100b0540001010f1551408400514083d0b11039000c4041c2c0d4000810005c010000b049404081603006000a4040d03031906880c2d4010607403d5120011040125403a0001040a4144101c07034191907d11807030a01e20700d00b01040c18001d03039801083d4241c03141480e10301007048030451611746030040c6400d00040c0c448e06007805401003400f643c0201076851990401d1071036001c004080d01c1030600c07544041c40482000c0320340d00300064082d0142031076400000c18032010658040030340092940c07020342c0d01d56540f164214010019600d040d240c440c407405000068 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 772091196 1250 772089946 772089949
    0xd030f0e10060f1e0e0406060305030d0204051c150b1c05150112020916020c1201091203022b0e06071206051807080405010906051e01090615050a03060b04091d0606 72
    0x480d2800d031540013035106215202ca047c0342c3e010f0b02d615040980303540400580000b000c1280d80c01003048840c2503402814001290071000f035004107003080500541c804003060680228680e111000110000f071100a0085100e0070000c00d106010b10215a07544c41020790a103000300d00300707085005000b00407094403840b001d60b000c5112054090729402006001f1130348511041d0003032100c04001c2101509407072403000200740d40f50203410402001d0702c11750981c1ca44007419030300c03038000c80e0703001c4440314141240d24449103103d2401c42510019102216a1142c481803154030610026000c0c582aa4032021100c8240100d802180c50710740c82107100d90300d03240c8828000c49103151525884400fa00300200e856070345080050240c05600782c0245614500000c209010f494441d120203a09116140c44102c0c1e80ca660004048070254000d1201b00b110200700180d01c81e110364018541200c03140307404078105550360404c0c8010740098000d10302c91625200d41140554040c00301c0b149062222004020f170307080a60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 772092446 1250 772091196 772091249
    0x120321181e01020f120f060d0c050f0d05030a0908070801150306050604090203070303090618230d0506090109200a0317120a02030702010b030a050d030f0e10060f 71
    0x1424809506114003400c0078a0a41c140d40c0c200d43d014040c83d90700d0304c440003da0171010302200c2030301d6445540e10200d591400c2c801110300c540c23540495840000360800040101442e080f5004607800000f08070203000250007440035220843d215190010481e040c85c4159040500c5900107038441ea00d080091000c110303441442400b10780d002500001c1e2501c5040c0031402038a0b4064000c2d4051080c1e00300002050792040071340048814556448490125950f80c0d18090307010b40c42001c000003102902c0000d40c03007502800d0760401600400902c0342c0030107641c0303003418040c0440390300b10b060f50344058610034040001d5031440307004001031481500000350400114015943c0c000a80b220600c69840c1148488620482c0d1441d15504046010342c03900d980c900000c0c3d4030845508005500f4103c5003a91411700044e26a4205d5002014141c2c21203a96000c0b4010000c00c4110100ca5485225100465005112403880c000f820f41f408203816041c55942003400075031794484020161998402d003007691024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 772093696 1250 772092446 772092463
    0x6020d0809030315010306031e03080612033709031104050c0a08180f07030615082a0409050d0201050115050417160e0a06050103050c030f040212032118 67
    0x100c0420349980301300780120010103840d000241820520440281b00361409801000803610076a6944107c0d5a070b40305110700d0a0182c5040029079206100c0300050100d040e0280c04109028440e60a02c1c2c0150300c50020072020080a500100b2030b1103400380306000d07404501048143d002d483c180441c0c102103003016142d1040300e84507000c002443c0b0110392020441100000c9a8082000311081c400c9589074003a00c44815110403241d051519400340c28006190910f402120340c400d004d4072044408000e01010310841c41100500b403c1103000c41c1d03205640b030b0b1080307034072840c003500061902711002c0c40040e0840c1e9060700305440d4880031003100e5190b1580300c81240c040d01c0894910115805a43c03140a10f001d900000450309080300e07034404507001c0012004a8440c8400071024006180d807040194121101a00c000d5000c45007000060200c004031050749422520241c140c400c01c6609000c41400d6401c107118100340010455464114000f004103619000ba000c2c4030041000c540400b03445956400c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 772094946 1250 772093696 772093711
    0x106080a15061107080105010602160f140607030905090f010e070c0c1a0d06092306030d0806180c03190506030a0f0c0f091d1506091005041506020d08090303 69
    0x30700307088090900003400481d0090071700200900195031100006921020301e54852030360b03103840340b00000e98590502c82503001c0741c01c0e88403024a00701281d018040c2c0d0383d0140d441982805010900010300762102503682c1e10414074131004180c01d504242030f18005d008007402c07a1040154180a40d00800e14144a42003218004480b0202044141c024100c85d406400895101e5610746840055403c40a41000c01c1001c03c40240014040041070b07100d580400c1501d115030035501003003109020a0140300f20720b412500092035814500c025080920548000711205015088d0100c02e0154069040b40c519045015040c018030251a051340425034500484c88041c1405280c25540710900180c0c00d01100078201c20440c180205440726a0302000d030180a58101956010050210807144042044899a068280714114030b4840700100402020f010341201010f102c09100040e05550f00d01c500c280880301c040c211429a864240d01905142e138030515141400b032480c0420251103c01f0048940c0f2414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 772096196 1250 772094946 772094957
    0x20060a06141e01020a1a16090305070e060f0d06090b060307030506040809061207080103200105070201030905031603030501050306090d02100c0905120604121103070303110708040e0106080a1506 85
    0x8180b80102d1420040d0007000c2c12081249143c550305050455000d403003aa14120711903206049460201d44510451102910940260101740008151064100c4d00b0000c0140441545152000040c590321000c600840301d0343d0341c41048104200d449891036520020440141c002d992031600c1d0b09481c1c100003400241040800280d000d610760722102503503290150008550f0492a12010240c100c10007800300b500c1503e00703c2c0030880400404408041c2c1100c040e91000d05080f0941e0044d00a041e01c41000c03035850005100115801192012500c1618001c1c1d5002c24554580401c4c54107250002d04583c000e41c00c5031804a1f20b09400054a905a515400c8000380c80d040c0c20364121881001500141d83c042c100361801001d00000181c0580030764003a40c00e9540020158409960480d0f95101b031900903082406034101003030082c1c0c0548109020040d045113044070710741e1404880e038803071780101440003086401805004d501030040d91384092907420403c40d082c800d04c04c8c00d440f4443d0b8400e1404110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 772097446 1250 772096196 772096249
    0x503011116060e06090f0c0a050d0b180102270402090303030c0c0307020604061e0810061412131205090d150905060403030e0d180e0720060a0614 64
    0x6540d43c4a0b00b040e048400940d0014104105070544440040002018a224245000c4a14545803a07003004840004203c804003964942e10308102500062013010162000c14016062140a000904d20100045c940b00e00441403d44100118443d0202c0c46001d140b06000d00c502580f030000841e40c1000c1761304009a100c5241000c0b10349540b041e40ca0023500700b500400c001412a400012151060342c8141d240340f2403c60409046070950030407038185400c139850070380401205015101c06582c014505003074034034210032208144640c02d000d48201c01600c400c072800d81d007401560a90840e0015051500501d0540d0110000d892206d04400c09400c0b0034075807040b400c1c1c01c41198083c038216503108007500c0d070b40d24081c10054024002301629202500400c89806010380c8120300d0894034200e241c0100c007951381441030b840c100c640c00030440b01c2403110038000601c0c1c02c0164518a008404041d0040c422440c281030072006132412540300501103001001442d205540d28144c60b100e44285130f4600d2900c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 772098696 1250 772097446 772097453
    0xa1203021606020705060f150a050112090c0b130f0e0403031805010f0b0a1202010219050c060712090e06061804150b030a051506030a05100315150503011116 69
    0x164981070008044a01c00603104082010206945204a8500780320346501e980d0030702c0d6201e013202d52000e010362003800340c0401e01056003e01812031460040400020300b40f502680c0f101d803c1ca01d6500528000c08011a042d032006128409201c044c1070451054003207245001d10240c1a0000900700805050719035480ca14002540500e00201682010092004d00c2021840d02e00402c4200781d0107004403108900400d0000c85101e03162050f80e410790041600004502508290007601c1900b03c3e060b00450903014150766807400a0301344640a1501c0000c28a61200003400076011640525202803241c400c00142c1c3d9982800d072001c1120607140650503d170504001001040703210440d600155110001207034034040360010b184200c901c80c00c20031041d100d095180d6400010f68409540c0108200009141d4050303e0304103a4000311907109140b0f001e0780f2a40e038041803900400188010903511256102c80e5000c04041400030700f4150020000c05a410038402003d119041e41c0300c2c0b5050012010f034041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 772099946 1250 772098696 772098727
    0x7090806041101031b0f030b030c0105071b080d080907150905040e1c05120c03040c23041e050f01180b03071701060f24081314010e0d020a120302 64
    0x10b01105c80340402c0c00d41c81a01c0044c140c40040c200440c00240380943d114154103000609282201c4140c40e1142043c0c420b907030724440072180c00384015140080c00d10000f16a0b8007007117500c0a0f800706840d00b504078903000345028075240031a845200322112030900c0039009900609180107035482980e01007a954409851245014461001d5444a0000051852080f40e20034090700407514454038040c1c0300d44480e42c08502c0307400280d034090035480d260001040004220b03844d844120140340c850b46403a0b5520b100003421540c03c03002407110240410403a905100d407034440c19070b00240b000c8800740c00d9414990500380350091201e00200d0566645503207071180e81d0400030840207043c039130410f1280348042c5e8080d501074845482f4251a9a461282c00700303e941815400c21190810712070803a42d001d900074070031682100017811103140c2d080300d510940c01040900c003d00031100304160021030b48103208600a850b100c2882e00540442d00482e01200002d440b4070601250b8000380d28015031a810400c11215a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 772101196 1250 772099946 772099961
    0x12070b071806090501030c14040603090f060606050d060b21090f07080d0905030f19061d0105040c0b210c04120b1f03210905030d03140709080604110103 67
    0xd8030300c03940304009600b9074008030f03503400c2d24003c0c3d805011158680300182d425034010070b60500e040f0300501080c8200c0c1d21070362160300000d004000106541c90310303031202003c8404030b4102e0700c001800068640c0504603039005440080950f9510649440888034019001260452210740e51132400300114401503c1040018105c052440517516026074071800a9030325a80c0c85101404030364110340000740b0b454042012842552200043d01000000e44240b08400d4020103089402d01c0daa01920050400003045c1451034503217036800000c0d2818a410000c10403221a445103a1183c8c0410640b000123186011403040e01030402442000c6807240744079000c1301c1c006c5070030014070310525002d01e034280010a002035000700b50703542a01500e18a109003c800e1140540009085200700420381d554903860764105aa070307000c6d680303030003003100d038035440040d05045102c03454000007074564194a07420802d904506030403408600b450030310315141280d41a00e401009201a040b400007010021a990180d048040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 772102446 1250 772101196 772101227
    0x60f05090408272106131a0c0d09030509010306050307050d0803181501030c080601030b0103110112060b0c0106091407140909160f03050c16020103060302040e0a1412070b07 76
    0x1098216030030a13401500d03500100c88104c1d44150720108540c2d040c00c0303940710400341e0002c0020000d0038201c06100001c40c005011586040c00030171486001800c203128415420380b080c3d840ca90b4800121000405480c026000b01c0c0c4643c100d01400c00c8140d0391a003444110a6024604540320742d82d84c511000010f50300030040f04140125020354103403601701140103060343c0c400c04601d001e0390348070818103a84500c24000100000c0f02c1c400184081816681500a112070502d003040c40c860101c00e01c1c0098800f2584503080f1804040b8540050050a000e0000513051001d420456803c64200f031000e040e5001d1716040601140030100a885020070040394003292010345a441242022024a000d01c540180081c1c0021116202102c203184a402850301528480c07080501303150800c1c400d489071000c0900200d0506641f18000401a11680902c04182c1d00d2440070380260180d81c00d0215064480d4030b00300e00203420501d06c0d064107a2a00080d5400180c0084080d80b07155290002a03c40e01200d0701e88a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 772103696 1250 772102446 772102459
    0x20601080d0e0d060213080f010203070203030411220c0215100e130b0f1603050702072607080c0906010c1205090f090415182d080d060f0509040827 65
    0x102940380c6c1c08001038007241c000c0d40803036014503442c0000d2400c034001a1a80001031b041000070801003102601c1c040000d86005103120504046552004200034100c2c100d22190b0707889070140341d111a01032007480c070740b410b000b0000705051401c215002b081c000d09028400d102c1d5151008204010001c1045001069200a10001c0c909241200b80000320b800c50300c51041c0581103550000240c480c0c0075440c0145160b800a290741e5013842000300c03540d8009107210a100a20294100c1070103000c001d1070300180460030181c515040101c0a1200d005001041d4505100c0c218190f48000768504440003510242c2e032401d192154019000103002034401c40070903900108800030b2209020080004000e244e800350010486c0918141c42002102032403000604513684450740c1e01c2a2101110f901e900d078000d500c5048240ca40d141d900c040441c0c210703564404e40156104000d000308802041102e000e41012501220203242555814180b4852405103040d040780b403046105800801050620038500000e140c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 772104946 1250 772103696 772103707
    0xc130e030403050a1101090b0d050a0b130207110a06090e070c080c1b1e0402160501020c0601061b0b0604020c010e0106090c08010b090a060c210f0f020601080d0e0d0602 74
    0xfa6548088000c0150307120380028944100540c020441c504c102d13684144440d080c584601802030081c5030052849a4035601d4010141c1c1d156a0508503146035a8006801038032450982070207580b0498071443d00e0300511140900b44031144d04481d07280203d40c190903d19401d541c4103c0220b4603d050890002c2a01c0c4010070549601c0300081610102140e000060a10781202c00f01044400010824104504912644a8007480c10f080d0002d2414009901110801c10358640c0c50b0b5013241d000310081328268020100501000c0c0e40200c0c1c50310190040d00c281085820141c460f4500003001410052146500050b00c0c20151800c0d04680c4d51000001c008105040c2d1f150044ea0240030f00f060035800040d0003030700120318002100f00b80c48002c0b0300600307540041c500b40300d42601c1c0003082c2c5209982071501600e030010171202081000ca1040801d90780c18000c60410f01014150500300c0b0619001c0d074010720300503c200d02c00064040020380040c5820000b0034403440c0492240310314000040c5c100c0c2d000094 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 772106196 1250 772104946 772104953
    0x18030706060905090105040309090e0717060f0c090328060609020c0705030f06040b0c1b03120a0524010302130801091b06051e0c01090b0906100302030c130e030403 72
    0xc1d802c68201c1e003418029640c42901444c00c131402101e00501095029009001224541d030000400410b81011a0542074a8004000c0c2d400aa440c031501654007502c00c0000d13060325205115040001c03a460a420300100d0350000740c451003111035000c500c2c00c10844c40c410512180d0100446950010010444c0640364059000a94090401d460162003040d60003c2c16090004049108004000c00b40c6003e0712580d03140c00a20780003800300d101e000f00900900c0790001c0c1c000346041c64034034048020f5669103022418054203550080110f541c842c540b9080001c8200c1541024181c1543c601d010032410181c540168028050010391220f0a01d55283c042801841540319050301400346644200d458048a070448081c2c1c418003411001401c10710464800d510781641c030b201c030019050290b07070030f001070b540c6080d00310345491809440305000042403110080d4103006183e00a0011200300009605540102ea910f50390821414022445800305000e404856400118817400f010280c0c0d80d203654a08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 772107446 1250 772106196 772106201
    0xd0804030f110d0f060b010c05101d0d020c040c17040312110c15010b1903020a02030910030203040c0b09010e010c05070504090c1a0301060807031806180c05040204030f0b18030706 79
    0xa0100c0701780345094460861036004241180b8816848001410103250320351141000e058090842c000610450303120380c2000c6030600400c050040701c0e40c010b000d0500140c0821041d41c4c2d112580c4401e01c9180c554240100c40700745085580540c05080c96403555000282c54001800303021240c0c40820408503103008041d03008200402070040d8698403010a0743c035003002280c03a1103000900e00880414502e6000b01c18080e801a00c2690b007540144e0b8202000c28022503034440041d046200004e41c0081000100014644c031107018003040301d1041c0c00d100c900d2001814000040003000d042c0b0940c400d0760820018104802c4019200282050200c05002d180c400b8099405000354001007500c402d03c039040041c82400d490490b071141e9608251a21000426030040482e80c0c218004810000218800324100b030240c151000c0c1603004540003851941005030f40d01c800c1c1e420052085004110400104204800c1e442071940c1050041c070300d80e15002c21845006044405e0740392140008940c510030b1001c0799 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 772108696 1250 772107446 772107473
    0x15031302061902011a06090904030e090c0c01051f090b1201060303020307150203040507150c0c061e0507050a110303040909150609150b0c0c03030d0603030e0d0804030f110d 76
    0x3e800030702c01d0070701c82008034450b546480c1032543c20100c10302c103154082c41c00c10708450f0001d01a0400660481d101c0011581903502101c0c61407084500040020168000744102d582c424a01030030b040c280c0318a50600102c2900c10b10400001c0d80d222400c50303615a803860021012290044002c1103100d949190181d2640c001d0340c01a100c800070000b004844400781d0007120b20a607440030203481d80c0c504125421120039107400c071140c20841500d528800150f0341c04d001c000500400c0d100c02d0301c00702c68a2086012454403d2072201005802e000e02400904000348000c52240d00c044034103030613691180485e2440c0600e600c11611030703040c111071805221844c1c07503840c00d02034869424080d06841c3d0607130341c05981d929003084000064502c004c20040a80e41c010b00f891042c1203090314140711000740000d00d5a0058400b00a0140d0703100401c004041d007210b80400e2041060b12654401c620036202c410840c016448082c00d408d45451401d4100040d800d80000d50200007042c3d07401503d85400e0620300c02215 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 772109946 1250 772108696 772108747
    0x170c1b0906060f03270f061005030d1209021f0f03050609041212181110030c020d0336020316140d05120a080a0b0105091503130206 58
    0xc80104070745003005411140200d010041413072864076181c40030000c0c200b507280c0140b00041c4405880480c20400c0c07291220781c10160009003202c0c180104400743c1d031401944054820740c00000c1008206400401c658038038498410000350704001400410b20350010401c80c62104c102c0030030811450b54000d6412400c45019903801c0000e9540e281c1030140441c0c0a55025020507604008904c40c5485881c440d064408501c0303000c80e01d011289105400394003103180441d22186006565000b6080000c002590148580f805200300684070b54043c1d11408242c42e041c08040d100c0c0d01c04c860044c4940076403c404200018072062004007460082e00b0006600c404912030f01510270240000a80f50040e0400d848445090600030095101000384510012904403018020760030400540d01c002d070094152004c807511504402d24000904070215403c02c1949418480d051100051039190880d2150792104242c40c2c5075074079251460320401d00f0420200c000c0d8050400544500020050301351400b41011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 772111196 1250 772109946 772109959
    0x203030a06060507030c060f090501150504051518071701090902010f08010f09020903070f0e18061003150b1e0a0501030207110f132a08040b04170c1b 66
    0x40710002203c0a21424001800050101829a000c5410f40d44545c2c0c0110200300000b40a54447d9285801d49208850301c0c00c144c80130401c1000981024000e20b6402007500101c1e1000c8440700380062030702d10f41d0003510106a0f01020004031814082c41c00d000c40002001042841076039a180080040c0c40c001400700d0000d143c200e01e6604081c01040340c1c50503208150b41014803a800d205900c0c001350054640d055140c8203000c400950640e45200c2ca40150003203407055241d0b40f80405406a2006008007444000e6001208102410704980094020789501c01c03900440b00b4454032550014110007001c01d5485180c41c15460590301c00380f032881c4800c10041d18000f840c160ba550054040b405440c40c007409807030000d0700708006403400d03240c01d41c5807842c010503103158107200340500c60440d038840c0102c090103035a41031180c100002e14164100707900824580a01c071407800d41d0398002d00d0f44c0040c1000b042004c850020200c041c19180590b0107140c011070440d00300c80c3d0110007041c1c20210040c0080d00904 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 772112446 1250 772111196 772111199
    0x602070f201f0206070e010302042c090d020a02090a0f0e0c03121e07020402040810091703010546030b01090513030f12091a0c0903101509020a0203030a06 68
    0xe0310061201002c0c0e425030003904032076a4410060f0341022201c80d00c941015402c000103da8860041c04e448204500140407503580c1031041e800540550006d440c100d1960300004040003d20b40c00540c0603c01c60b0705907405400f0f42c5481c1c0288001d0510412111384890400802c0140d00c00001409c5010304000c80484240501e02c20f00c61181d442003800901c00c120004001480348010030b0014045284090001450300b9900c04d115030412150415103041c064840980320213001c060780c180035507807882500e200c2c619450304001580410703002d8101e4881075100003442d000d1211018008121449060120b525001000c078145064001d0740012102c001003c00085080c40d8507208070762040c40c4200d4a000004580d44080e0380f41c1010b10441c40c20401c007a600d00509045038081c0d20822803043c804295040b190301c01d1020151002408840742401c207112800e129036000416210b0f00216140024402078170900800065070590040e0010711300000c1e890580540c0040110302c64120b0440412086 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 772113696 1250 772112446 772112479
    0x702010b120a020628080403020f0106060914030705060a02010209130606050f032e080f010c05090f0f1203030103050706050903030403060f020c0f0106150315030602070f20 76
    0x15104040c41c41c29610092202c0b0041c140341005080c40c1c01940c180c120905080c4504100701284801d01000280b40310045c0002c2540402c0742c00a000f000d82c00034002d803403c3c4000100300d8203407445400108030304002104000e403401e0003864003a040180025a0b554500b0001a0107503106603090f074000d10700c941c50040044200e2203440180d40f100c0d034440d4900342c1c10080d00031081d0800340114200d2204035a82d41740280c1c0703400501c2103d5910894010580d880e1222031402e0551031008005184d0400c02e1060840e0b134480c0403203004580c2101c81480002c000c1020542c040d00174000030740c01c401c0d180350209010100001079412688a041100c1040f0389584088585005c3d90340c4903901688140024000251950001d90203a455040014101101401b080b0b01d001d00c0419584400c1e5510541030280100c9100c5c092000441424103001750600308140e00b44401003403002800d080d80c0420f00108204011009000d942d8200c940e071411012900306800c2c00700101d440e183e108580c400d10340d500c032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 772114946 1250 772113696 772113709
    0x5010b010e03030c060c0a120516081f03120203071a0f13050d0339020f011503140c090a060504050109050903091023030610050c03071203060510080702010b 69
    0x4d6803940c040c0c0031645540000395910f40000044405100c01842c44071441000f52080f1442103812041d00310010304000b00c080d10129001d02540b0b40c1ea600c2160b071402c49460b00543c4170440b030380700b08580c0c04140e552400300d0450281715002406003200003000147c50300c1d04120540501074004c2540306940b2900082d10614600e00002402604400384543d1140d000398000c08509840b118040011442e018048111840c40d80001c00b0313401800800d0420658100484881d00c1d81070304c000c0003041c0b90400181501046844003e208400c03840710f181d524001400080c0700303101c0c00303820300442c1e0804240305800341080b802024000d40c41c210001501801d41d00942c1e0156203550051490680c04000380031044144900b842d081c86804400742caa0500c0028040e1207002502e444503440381012000c200b00c40c3c0b01010345d4410010140a1012944000f10880d0a030030b60082443c0c00d0102190001e6001d08030fa64440359110070001d012601d02034200c3e81c1c05101d280203078001c005004000040220 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 772116196 1250 772114946 772114957
    0xc0a0c17120c1c031b03060f090f020c01060f06020f07060503040807321501050a23030109030801210804180f06120201020d0801080c0d060b0d05010b010e0303 70
    0x8107030721001140000c0d40c889001041484200e8054820340215090f0060b201c1072400046800690b50351400c0c9100361491074606640c401c079180c02d00000b841d040d48104403044500501640d00c4e50340440e0107281e280b9604907900c0055400c000c0c42041d40c0c91541800141d614842c3d50098000c0040d00f41c0c0c41b003800700d42581502c00a0701c0d040e05644454035904072903001182c3c110b504218000340c11130210401005140e0311540a165581440c0c03402060505017900001414081401400180710a035a2103000805450046002110810209885954004820b000f00d42c26503c0c210501e410300d5400b000040c141c6072000304016503103141c82c5000010306a4068054110038040c001401342d844c410001340110303a140c00c408216808411a8541218403951000f0301d404940112002156018000c180614200f41054000c545c5042c100c1380d00c41e2620800b062050004500720000c001207a404040c0d1004003030a10b68201565160183c002d080006842d80410700e000080074082c03400008485 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 772117446 1250 772116196 772116239
    0xf09010e1e03061f03110102010212010b0d1512111c030c110613050603060a03020402210903030c0301091d0d210216110f13020418020403050d11030c01020c0a0c 71
    0x8550f070340342d6103607412411b14041003141103540820144407035103c07507101d4038040c050099060780d48442c50f049240417605481d103080e000e6034002c0c42c200049001e5008804403250484c444c11201c1c51a01c0000700e03600c8543e8080c91614030f40502c00810305620000380d0340305a1150400302002c60300e200411005025840c52030614240542c410700131410560040d580210001d0400b68180d61a50b001a080c3d070018054104c0070b086041700d029110a01d24021f640106000d00510f10f0f6040600640880380710500a003d101ca0312100d48049400c1c52050b01490041000c0503940d402270581e8000301044000c0812000710b48844011807036581032031003114070386480b004132200d050b0034540d190b205170390117044a1030340801c4500da407a059440340c1c9482c44a10001c660016030b61400c1828031103141c12902030641185106100c1800026400148030300e0102d101d041204a00903018441c0c0e03d18440d00a84039800d500110302c5000003200011010781181c4151b403241034960700d5070041d80d003840781c00b000e05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 772118696 1250 772117446 772117501
    0x90f0411100315031110030c090308070f0b160e06031017120f030109050f06060306041a19030b01080303090304150c0816020916050f09010e1e0306 65
    0x10303030624081003180d01c1c0c19514100031a1441c0c100100540d00394590703000f0764822010070021005841c0010044a41d4010b0341410003d600303503000c00500311282400010460080066800d0034410f003840104003d0313a0006041410f4904032010741d40300300c040e80b81d07840130603a507000741d031060300c0c203170091300d02c108010507000c0d411925042d104c80b41912010880703030740c80c05000c0721401c0c000500c100404600e0280c0d0f9000b0b56a5140030949130494000600c0509034100201c2030064542c1e850f4100c130f820400444001c00d2040301c1d004110700100101900c558444041c04001681c0301010211004072401200e008110741c3c5d80e03460198880c401203480e40c94603002004180060380924090140c0300d1000d103440407100d4100e80ea071400c0d41d4000b82c030940400b09059a080110700d80441c11a5010f110884910001c0600d03030805841400f5030103600f0805031011450320f55991042e60451341217540100030022100311141c8003c1055000c9440c2c42c0207000d20f500040340b060100c05410000a1841382d00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 772119946 1250 772118696 772118723
    0x10b031b0109030c03240501051305150909010501090609050c04090e070e04050705041b090e0613110a08090a0b0c0f04260106060311031306020c0d02060402090f04 72
    0x25005034000c1a02081c188444800048041364141510502551041040c2110101d808240210303100c0d40521030550103080c60018020707900c0d103245417040101180c07004551515418503c01903a80c29203e9075801582c40e10070001e00715015003005048a1049104000c407a4591845070180d0300c0454400f85801010402045605142c2c3d1204805061507403c0d41c8100b51958010813050380305407000d0300e03079a00600c0140041d18061140b0007e09400d0001d22074441d032600c2002e081040c6038414841721308912400a03820391a0701c005c0b019030307040098040040300925100c2845540013021a4000140c8400001d110030000144130901c0c1e6030007105080d0255912906900942d000e03140650100006000c0000c801c6000210260701da1094045200d9080e04480c1c51421100d140c0c3c00082014107000140900d128440202e0340c04c184c14122070500b5052a0907c1e4000c2d00c50114440c4182c4602070240c0c00117a404503c2c28041da01c2280c1440c0c1079200c052044003a2070059501a08103540c1048 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 772121196 1250 772119946 772119973
    0x70809030102070b07030903020c060301030f03030c020c0a09050103060b0a260c0604081b04061404020d0b061c1103010e0612070317070308090312040813180b040509010b03 76
    0x602214900100054903040f101e03035801c0b003076000c10b90769207010980301e6110b44d00305038060204105544041d2032090441d85141c13541e206600c16440e000d0181644d904504216a100b4004105842d101820b00c03000304e0383e1a070103403000700300074403040d502e82c1d18102088a0700d280420301c140490740403d803102245184510990300300c120310139a40b4281d00c50070300004900e860300c4001c0e00042c04c120001d402500c11002513110641985a10a841540342170001d0101141310030300540541c1080c1ca0060700c1c1c0c041000510001c290002d50180d0101e00415045041d0403990310343c840700b0200603014009089007144440860000f030046904c110144400200e03681083c1858040c8804482c080b1802523940e03495481000242000c855a801000a20300040c9030300008810b81014035800154074110012001202c1c4650181006003503490000c0e1800300c0c0e0042c512424060b04070528a010301e02c0c0c44807030610003065420200c60190b8200000100300100621410320440d4014000d040303035004045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 772122302 1106 772121196 772121213
    0x10305070c03021b0117090c1c0c06120207021801080c0a030b070c080d0f1a1e09100e09010c17090a03050307030b09150a06020c0607 59
    0xca010340002d0b0f0000c0c54020039001c1c15103883d1114400401241c0b40c070100741300e1381061144042030109146003c280d03040002c804986481505400d61083c40340c3d1400705002030300712030788010100505402103425084000d00440c006141c840a036001030600343c145030340c40040001e030b9001808900c40030000b021a000e82142c003c00600c0c0b440e0303900b181540d4028440010403c42c404410200300000007079525650039850103003e440040c1b481400241580b68584880110401010044d424a00e9a6525103100701302c41d002c10b48804030501410340d1010300040d541c0b65000318009400c144c202102405424901c001048121103400020034005881000c407101ca50341d0f006004c1c8640d40000d00725022541800c10039180d0340c0e5a00e090300100031020750f9a8101c03c04808200503290941c004100b01d2200b00e031040c80641c0c131a00700301d940d00c1c03007030b2101500800d040021102107491007 = true := by decide +kernel

theorem cover : BRFrame.Cov 771942446 772122302 := by
  have h0 := BRFrame.cov_init 771942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 771942446 ≤ n) (h2 : n < 772122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
