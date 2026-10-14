-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:57.29067+00:00
-- url     : https://prove2.me/submissions/e6256187-3775-4e67-b157-74813e8167e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 360791366 ≤ n < 360971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 360792616 1250 360791366 360791377
    0xa0e0414070f17070e220804270c0804020d0606051c0203060f07140f0910020a05060f07080a18020a08031812030d0b1804110111060702060c0a021e03 66
    0xf94000c0440026502401da640d4525210320b07001c0440660110f41d000c0c5820060005081030001c0c440300e030146039140c1241c0c41d8890f6100c0b84901549000d500307881c110416034004416923100303081040703650b260030281200fa4010402840f42c4030701e0304100c0402103c0d40c000c1010f407201400d8142001d40c90300c40e112034048101c4080e072091003002c00044114441d24096441040103958200d9142c2d80d820365900f643e00400201d080000d014400000c240c1c54043c3c4e140180f1665a00900c20ba154509080e410100040c0c446282e04c0005001c00c0300068004040540100d80c9003c0000c0f490700030103107041d580381c40400007507015400101c009003040c00000a04210b40b803c480500d61401f07200d0402060007958404001c50703400034014041000810790181074850700c09804600e11001d040d00025085c10300b00c0d0115554034000d031204146580c80b2100c1922600c4078002001942000c00010f991100002c050800d5490002800d00d2641d00c00d02550001000807184000300d01541c0041c15203a8118 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 360793866 1250 360792616 360792629
    0x20a0f0c051513061b020301230105010203120402131b0f02161202040b0f0a090606020616080a050601020c0d05060105100201150303030510030807141501050a0e0414070f 75
    0x11914504441e103809030443c1c030914060003030004950326115090710411068180043c0030105840ca020151300c1c2806000005082d5444240d00b9001860203041c4896040e080f90741154824041c4400800c074000c0f0039504950101c40c880c0b580440f54000c4c1025050242c0324240c5911388207030000d0000c3d0030120403880306800d5003d59800962003207010314400440c0c4164050000000603070405801c059000072040c00c00030300119210800000460325101841d80042c915a1780e90780d00300300d250307030603c01d503038102200100c109422019407000401051000d070001c050b0980c1c6002140e2940c2c000c202d4100c101e64094904d0074203003c80d04106844003800d10450f4001d0340c0500d00050140c0c818030945036078801cac020300d100403d41561011401041c0080007031300411f4501c0e60100110302100d02900d0114403c56040d01c14080c0c04a00c0d6060651510403417202c56070240c01444071b0b80d5a0203004d0103460010100d54015036076070502089090315081944198001c0c84000b141c01c00b41501c2280941c0d03078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 360795116 1250 360793866 360793879
    0x604090606020303070e220905070b070503040806060406061205090715032003070215130503041403160302152206020609070b0c0607030f20030a06090b0d080a020a0f0c05 75
    0x25071105002d0382c00c0001041190f2080750001d0f041f00c05c1840d030b01c04110039024004a552180d101c2c07903003000c20750100f881030319158404541000001010072110b544a0410754061084a1500c00c0141103210302e0310301c6c1c210040e2114001013200b00e0800000004101440c03502c10301c5084004060300603d41180d81c8061501558018440c10500f40120f9001c0e2115900400b03040d0740c0d9002e0112a410090007160b2100b081d8180f20780422802c05c090b001400740c1c02d5140c4081c2860b5400c00d45003a600d40b64814600c3c07100481000540c0d5081001c2c0b0341700c2036224095a8540c0b805280d121080c2d2000083c02c0f2542e05507001141c06640001c510303205460800448400e00e86801d15140140541c40209c2030551141c0300240e08a48030b904a20301d1180070240100c2c1214524100045088407819035221600002c0204040310740b61b4041e240003800c01c1801041814524404a0084806083d0180c4800c0300041d5012015108101d07081220750001083d04100d842c07482c101c40c144041e0f1041c20321605 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 360796366 1250 360795116 360795137
    0x60201181103010906060924120201200d030f0c0f12020a02012703081f0302041805010207061505060406090b0304020d02090406051608010608280c2d1d060409060602030307 76
    0x41c0300540340400d48050032750383c49512025134011100001c1080070f000440c84400c3c218401c40000f0460403c64110545010801058000e1040107d80070701d0f611004100103201c5050600341c03c81000300c52520b141e600540c1d00c83e60344e007041e4050050246440c5188891158640d1781040c500c04010175244250f444568545808217054030120550100003000c1c0c00b410710400040c0303000d600c09580b09455882c0d0340c2c4001d040f42c4695003203801c5004c05407000358a558070b81c4142c41070b4104c400080e1004980290410b41021030042000980e4010201050800400706095503100003400c240245d0080809500c1e14080c5415005800191206240c502d070b91100800702c2401a001d650581d240d6a849221070b659000c43c03095030100301610349665840c1c807212020103400307030f000d840281d1440346c907650441e80400a004009104900102c1f184004e610303568214590b000540c244d240d07102402404003100d200d1700188091080360b1107610040e1034100001412500480550310481c0c031a2904c6805a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 360797616 1250 360796366 360796421
    0x1115120106030902150705010b091f0b03010b040b091f12140402060706050402011709071d150603040804080a030c140c060a03020a0e090702070305070602011811030109060609 77
    0x80b03d03030700300007540300c0e6584103120401d8100001400e1441c2c022000420031000c01d03004030310001c00549000c5400001c031b00c409491a405c50700b2080003000658000c1e8950340c0b400762214214080c03400340301c171900000161481160b941c1e214030040c0180744000c031040c444602c280542050b0508031040344c0c01c0d080003d082404950288002e11998001d00300616206050395207900034400240124180b0540f941d503488215203000003544524408401001c4a07400c0c0300d04e003c581400d00700e03000342040103142040246422003a5501d0302901c1640d080d512900c891925004a004035000b44500d8464000104141a88903107050001030042c4c13850308040d0400c03a265602c50020701130454225504203c0029802c0c440d41c010840d0929900e0f0140c040f5400400150015105403207070401684003030b4003441408428041140181041d0008018030f040d47d142c488440341d401d00016200b098906e80880040e1000e421035290307074ae4000703000c2050603203501c1c8040c010309014542c5c10b034010f510596800c28 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 360798866 1250 360797616 360797621
    0x70501062606071b03030b19090203102408070504152a020a03030f03140a0624020a0305070204090b190608030a0203180402120a0b040f14070c111512010603 69
    0x8590b0010741e004c01d8a4040d2815006000403115654104070392031641d19141c0f0410950801405a420f0007590b01c0c1003c1c89031551980f00764210038008201c1c1c1061030302c02c0812420700070102c2814109941c0591b60040191107900a5601100140301d00b01104d080196102c4206171707040c00040500e0203000c5602c0b5a00303840502098000390484503038002170010074000c1d03842c04945269468081900300305904d003203451072815500e054196441d00c005004100314141d410a414019051402c0c1c540c0480000a40d0f5130b51b00f030000b40030b11070000b618000b952629048200403641050702e80001d424814540b000301554a80d600340000d1a21502140510340403084451b0440550300650806411000300407500f600a00d0f43d95205600f001840784215a407481140f06410340d20000850b140e488091209850001b80000485481c00b940104d0429141c1e4a4076041805894403d00104091504a030b40080e040f04450340031008140355905040c0000080c00c0c0c6000403031162985c0d9a0f960300503001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 360800116 1250 360798866 360798887
    0x1406070f0c06050c0f1b10180b0606091206040b0903040602070b09030c0306070807090801060608040605040c091806061a22030605131406041707050106260607 70
    0x64440e0200700d01180d45600510f410800300703080c881c80c01404860800b010350002e02d032100388078010250584403001c14000e00390341c800b482d507082c1722a80100e0440c000d000038900c001803824003035802040c0700f030700c64500f42c0b040144080c00035483c10040c0314483c1e40c0c5507011030b000c0b03d090342110300088072113101105403022244682c006110391414503c041d080d6030400c8120070b4041c4203840e011019940c042194501848907074966010500300304030000c001c4480d582200c840b507814072800b007003003541c042031499101c0d4008500281c1510b0301e2800f5000450b103a4010244035050403100c800281014180d201e2031841000c3c10000c41769a1440210114a80c0b4604041b00c4002d0009031103103200480110103a05810209809254880d039800084403030a6442601c4004030102d48070802c1031501c20120b400170a40024089460b03d1743c1e0744d806c640c1c540302260081040100320321040203025001a809059480085000c8454030708000c45040441c103e40d205521542d0f000c140858083d452020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 360801366 1250 360800116 360800147
    0xf03010c020304170a0c270b01020c04050612100606030e0114040f0c0308030108030a27090f11030c030a050709150c080405060703030b0f15160807050604140607 71
    0x103091621385011101020318102c18403116000325240d981c00100310854800c0901440b500d001888401c06210307045000ca4255072011580c0707001c041900384d170b80005a80001c1d44044070301190b20b41d50903000c00c0380c50b500154800201c0c4031345c000141d461035841d04400c003512040e43d03081250208814040742a9000314400b02100c0ed008800700c0c000c070f4801d04503461118050154030002540e25907030901d13141d000342d0115040d50000700da1401c00690045110340001c6000450703416074813040c0e418202406141c0320704084181c2c2c502036a4000c3d001031700f101079403030300661100d41c40349020200c00d2100e903c2142d458129a150000082c44503004181c1c01090319140d00741441d03400f8212006680c2400c01c404180e403280418400000da6036104401030507154420f036004034680c4568003c0c40241145c400010780710312100030040701f070040c50038183e5806c0d840e211807204c5121b00508001e12984140400a0001d0060008010034004006004203020311044210f94403640c3c1d510342107444585440e0600e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 360802616 1250 360801366 360801373
    0x70504050d301110022a070b040303080609061f0c083705160201030f06030219080d0c02011b020a051003150506090a050d062004050f03010c02 63
    0x4408215400c40b595001500e800064000c580040214030310840b030791000d8000a030504030051030080e0280b0010401d1200454150b0074608445580841414403164081c20008203103000807401504012400091000c00c07021075071540c032424020034106088a880c1d001c0c107048800305003d0306101e09140d50001495560078040c960a10045440b5401c00005aa400100303000244c10340803081c4e40d609403400c094550040e00c005030420003d8a49000f8800b00501c4000e10107200744241d662420751609609203000141a0340c10387d8020007c0074580c0019400990b200d940843d5001c0a03080d81094603555021a010320b45511803c580900848400a00185213030a5019000c292040c07030403007a51000344500c105507154004111030718000092000007070f031145040788800303c00000d080050441981c80c60f291516a001080c040380e21441064014985040e0410030321009a000003c14400100e442c4c2e1014100d00e81d0781d2150b00b081c06000e1040010b48502c80140c50148144041151a500034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 360803866 1250 360802616 360802639
    0x1509060e060a09032003030301170d020f1c020703061503051506030a2904050303060f121c0519050a110d081605040803070501020301060207150210020f07120e030607050405 76
    0x117621822441600c6101d071a040302d841d20f48243d805102840c040d10f2109407448003e441d1004051508040d845200b0940d0028402c00400c0c52020980821040910540801034207188004a2810b072065202074034252030701c41c2e40048070b00e90b0807941c0100c1c3e00400c1143c0e441c003400001c0544009041d51460b030305a10901c901800112100080b10010380310b0121281c0000f01a0408005403808403005c9031690000010007680c0c0c070740f442d1195000d182c140e42028200420301c00b20303540e07051200320f000342d03403507012080d015100d2181c0101e81d9074042c65401902c22403c8544003800ca40c000311152004221000d01408200400013490000f0358403e81d510140b82d100d4001000180808556050800a0802020964640c1003005003103041c030030707000160f0b00d41c9001002424142c4a0b00b1440c0300300709903601c0002841d80017424129204150700c0050b91170b580600381c05c0480c800e00354001c01c01c8600c00303030240c08690400c040d540765000903001c4e87c07055610044126079070310450142561250b4100d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 360805116 1250 360803866 360803873
    0x4122108060d0609020405090a020a0909050303060d11100206010504050117250b280804030c06240e09010605010206010b0406110309090f090706051306181509060e060a0903 76
    0x26081025003d120005102d03a240d0f000319058403c00c0341c202c10554090350000741141480100c4000619507603008105024540d82d4007500c0b4032000e4131180c4140d2841c0200e005000031044410011000141515458110307102c0180d01c03168240b00d00d5202d41e24043c000585001c000c85221107100d00c2201034040342902c80b1310f500c043c9021100c0c84006c21441c1d0700100c0c00c0c10b1400b006180c44481050408114099100002400c0031688200410880110103000010760411154584540e01100c0820810700e01003944240d440200541007030b9040c004070010301048011074481c02060520700901010303440300c0043e82d40700000c0c480c041e2800400c0001304042845014250140c22000065925140c440030008030304d1581a1102529a040c48061042c910b0080000c0001010207040090502e910300c95072242840c5c446c401e00c000d1100c2010088851401d5141e450301500105100e28030301402c0640040a003485130144c100492003440c840c003010f02d4000191000c06905035281040e40f41160b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 360806366 1250 360805116 360805129
    0x9030a0506072a082109030405040e0307020123090604030b060112060b0d0c020f01050c1903110409020904090b0a02031605040302100f090f09230f060918030412210806 74
    0x20110008401d05404c502c0805407175610203000e450048001d689036403e007402c110440381d0300e005010440d07004001240041c0d030000000c98a8015202900340b00795440c02d1445002d00c10b0300e0703446501090001c0e011040240541456009071020782c0e8110001d010416a1422a11140a05a6214414411100c00704140d8200e080c1542551040d580c9101412911601352241030b110241550f0000c6205d54405884500071802d101841c0b805000030030580c034821542c0e00c624082c44a84a4000a1203021601c2e903401002c10240e01a0100e0b406240c4001120700030b4006480101410b0312610101c00c41601c580155415170390002d180351440d00050401703035141d2035485040380620400c030f00300040400300d4074102e400501c800c490203d2003185025542102142d45030392071072107500740010b004220035012200c550001040c0c40300951515100079940c00c2001d642903440043c400010017003240051500c100c01c0701803040310b204c0203610300c0001621800c5d204903140340000e08008000b403641e240c0714 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 360807616 1250 360806366 360806377
    0xa1a1905060c010f050103052b090603020a030b0d0c0311010e06120703141f09050c1206060906070827030a20090c0a0806150f090609030a0506072a08 66
    0x2c00001071244100e941c044251075003684207880f40c0e000300395441900e076040000d0314640314100b011108032600c0d00310f01900d0b112407401060101540801c81c2c09107640203603c94080d100005107900750258051800c9090701020740411a1054441c0d0010042ca5020300c010f0f816002c4020000e5080c442110070a40040c07070000c3c812002c154440300b25111881d100074419000791b6260880c841071150a2110705180407150744498200b030300d000c040000760300b1034206544100b03d04070983c00f855140c8000184c07843c0180450303c0c0d071014000921000b0851000001c0c8030f20041d10480c0038007183e11510042107019802800b54042e04803650340320008196005071181185202c5400122050202c0850300b6401c080f40c652102c1140022000d406940000700c540c0c2c0004212105c2d03202045403980740e00103001e180c0e550003594801043d10f0240c0d9448505540340d10b040601254648060307400c10340d40d03404041d50b9981c003007950444201c1180e144002148201c0c2400020b00c83c0f6400165642c08e01c03503000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 360808866 1250 360807616 360807637
    0x20304080316050a080712090f0e01030206070309090c020a020f090121030c1a0402040b09072c120102130b07020307060f02010f0501092319051305060a1a190506 71
    0x8000d004c000049042010300056800b5810b40803004840203c080c00c0c180c80751700702c0403080c0211001007021049214032941034a90544ea0b1070785542c03007843c0594103008250000c010300c5091041d07511849034002216401c01b4021640c206500b00e040c002e0100c651801c0c090001c4001d0184994010283c5600000c4140c0e1301c240b400c11101206a02d03202d035421a0039410100d120b51030024413003949043e000d84240000d0480d910511820500d6010700040030080c4105120b001e40ea02c4184801c1d042c3c0d4400c0601040070b41100004c09040702070301d00070361100c20301b29001002e81d03401143d4601e42d90140c0b444e1650140c01095110f042c007801756541d108201022046640741da058810000c214007030b050013841c080d80c011070081040c104002c05031001d10b1940010100d01c0c001c121250b5411004212440c2c0c0c0f079000041c83d911014001c0042d85800c0e17002400d14400c0b2014040354800c1c0341c0c010541030031180e508030001061401040122080182901c070b000320900350038080e03854004014808000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 360810116 1250 360808866 360808873
    0x9040621081c020f0904064b0803071403070302070e04062304020102010506030c01051213050303040c0f090605010c170c0111040e06040504033509100c02030408031605 74
    0x14074514807810fa83c8003d108000041d004034650f0f030380b820326008801c00341001020213000c9070505a80c003a82c0c8a10004014180324039132101d20341c41555140391050304414103091020f841c2d03c6a0b0225920381c0022003c841c01d0140c0d8850060341007000c030a8800c415890340c007600a1501d0b02c4503d000002c4040c20603101d20796160304641c0035660a0350300381c5010380c010052117054070b0280006421160020441402500a4518082c10380c1e03001c0c045900e202140512010951034024010040d902ca0a000411502c0004148014407020903550000c0b9182081c45204054441090f8400c6d208580314660104804010590028002042140e1105811586c95040a4103000010309680400524045250000405221100760006444c1e4411425a424030050905a40040c0000c010312034000b412210050b02c0070320a080c182d050b4400c1c2c0018128910742d403e22201f0b15807a0021503114001d00c41c40c0050758541c6c14008002d440880300f0f6080a54108060382100b080e2812031b4400803250fa00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 360811366 1250 360810116 360810157
    0xc0603070c0510090f05060a0626030c0f03040320090a0e010e070f0e0a020c120705010209040c08010501080a0501032f0405070c0c0f080613060b0a03080904062108 72
    0xc01841344400355801a481c0240c0a41c45040003418407001410140b0101d040c2203050001c402d072038900d41c5c81809042d410101c2d5615850143d41180500d5080e8a124011511140c1034090f000000c1d00559002c0c03036100c40051800c0001c0e280c0c441f203400c1b8154011a007040020440d4031240e0096030b0a101480010803010740d100c50440c1401001e030840c40c01716456a405000c1c1d000302e842c41c180d1050084004600d000904a1a542d40b0b208030115400c40350400658802004401e4058420035170f07014105101d1807020340d4018068500c00d004560003e5040c10020f042c0003060300903035040702e400c844100c00c00702c4840b00705074150451b41002c0a280d500c1c00c42c1c410140e1124400c8501c035003000d540d0020512702528248440d0301155000122410301448140103004002c201aa00492002c0c4c00405d000d0151900e80080c0c1404c00540b903101031503680000500c001000101a4880c00301c41c00c1141d0703074544034000120340313440c00c0f014810091103200c440012959001400003504800f001000070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 360812616 1250 360811366 360811393
    0x5060a020d091a1e151215160e01080717071106180d0903080901050d06030b040f0b07051215030a0c090609060b030405030703121104080f0c01020c0603070c05 70
    0x34808010110075140d101c07020401c1140c1034010300c20b13400350f100500c800103042100b0189810341c03030901e10700d12071180d94201d006581801c0201214528085e0f20703050765454054070030498802c10707106e0000400e0074540d940d1800e40c400d05801e486130a4603100c81d441032083e040a00c149550090003001800048410b0781c84810341049090b2049840c0708030755000e00283d040d801e04014080d8044024400b9114040c00001d4480065551041e000c0c0380c265110b81142c459003000c0e20b92a400a03241c6016201032109021000ba00f10266038001c24844081c2e4607204402ca6043c0b08842c05084842c2032a00031601d904980620742103c0b40e802000c5801d0006182c81c0e882560307006501089005a4404c81004030a5a5001b04d100601810022504602e0b040c2c88842d02c0b031142e900e000341000842d150241c0d40c003195030300ca0003250004843e503a803681d80300d1403001d036900d0010041020307130b1140e880404015031002840510070080602810700b191124642a01d041106010481c3d840c0650b40d4004140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 360813866 1250 360812616 360812633
    0x5040212010914010b030a081206060712020604060501290c030c19050f06010b0a0c020a030c0603090c080c0d1203021e1b010b0913081c020309070b030405060a020d09 73
    0xb0030f0146040c0034090201c122020708540400c20858000d0b0064803188001c240031109441c500c903401001d00805a07034050001ea20342c4181c440080c0121000c140b402450b46d800640700e84105e100c0d45003003102c0d0340c9030302d511103080d82621150180107144860b1000000a402d010340510b2218070102c1c0c0c104000ea0910300e04054604080c407688040e021810014800100080415028450040d040a5040800008491042c400381d80305200f0089041d80c01c41d1290030340c03c001907400001140300103460b014024040c20001c14250350f00040300c54045204c84000c208030202c460010044d041040d401c3c2c2e644480c085421041c3c805043c0d090000c03542d0580b0b8001002d108540b100b106039030b03856461010f5101100b0800181e090342e8542880c8400c107860f06c0c107103103401c440464010b6a0700d100e03c0c80d11100c02d21922150841c1808a110079041600d056009180542c44050586d04900c0c2c503110300f40e8180c002150080e10b280d2100c3c01190000c0c009500920803400c4007800440d480040d034a90019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 360815116 1250 360813866 360813881
    0x3050d180b160c1a03060906030f0d030e0d032a1206030c1a03060a3c08071a0306010e04020c0604140c03010b03100c1e03020a1d0d060504021201 64
    0x402e401c40c144010100400004024042c0c44044000d042000c4d00158030442400002e003954041c84090010403201e0354104002c0c0d4140604808984a6038900711004014042d104240003a500c103006007407401c05e002c1d000f000c00900600381c01050082c40c40e002c5404041c112105e05045c80000218156455901e0107110080c0d80160030140080380ba2058a001906e2482d05000e0f0b401d000b0310511920769550400e44d001c69200104200621981c02c5004445518041071040d0704400540c000c01c500c070003200c004e400c503104d51007605c00940d9203040c0c07040c2c42c60204072488002e8070301700000345c0d141d03002c1ca00180317040320007400c01810010907050403483c142e0191415210304114180a2024080402c000c0101020540c0244144401c440100c2da4032201882d8101d8603685a04580c11a1440381001c00301d0040b00349056a051910710070058001c1d405070406a001482c01048103451440c041c0c6200302142000c0c2000756040340320740340c15008010192080b0703403005c804008101180000d00a807007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 360816366 1250 360815116 360815137
    0x703060f03060e0606011d0d064a0304170a12020a0209180a020603041109040308100b0f031609081f0e0d170711030d0204091503050d180b 61
    0x41d0740c0c01907924451a204e070003000d580c100501d070007003600a01942c0c0410242005c040c2c403584491602481c1c01700c0a0701051007a07400c00340411701300c80c0c3c171401715240c043c03a11414106241c0034030041c80044099010241407111142c0d10401003008601038141c00c8881202c00e03101601c14003020f66039040904d01d014124440140d0203916854154a0002180740e040a40c0180c0280c0013a03e1540c0c660310b0f110781c52006485080080001810b01c814051980b4030701400802d103012500e09450060310300b60b0155440d400740720115034003060b1141074030308507500420480701c0c840c19aa0341401c46030307a40c0c0c030084203801005103042001400c3c980400c4140d200010480424450001c0d0340c1c40070003194898400213400343d001c0c0355403500064001c4070b4140050b245001c03c5031281c2e652403096a06954180640019100018503040c440c1203582c003602c161001d42c4000d00800201149001c00864140000350050700004c0d201030b4040d01500d28042008a0103502030400c0c0c0e40c03a096000142c1001080c070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 360817616 1250 360816366 360816371
    0x50f060108090d23090901030302010e06091b060d021b010e0d0903080711210a060e010c0e0105033d23040203060a0b0307020c01020705100c0602030703060f0306 71
    0x89119030300500841d500c0300c50341c0b000745540c200c808401440060400aa150580d120b0395403c5030040142007140e10092019001e9081540d42c0d00d0024000c080ca52201c03080e60089401055000c40d011682c060240e2050840c01031040091040100340e52100341c00c000c04903804c04c0081c6000400886d5010f51054480c000108107541417442404c2a0031190303240c040101e01c40042c0000f88094007a94240e075002007800c102d4882100c086401d0060703005003040140c40a880080703854200180c54008684140000c3c004111f01501c0036003030f60002c0302c216020590042d03030030800d035200754060760340205180907a6a482220340b10585910302440f8400c201e4411000d00030140d43d518807050360091886062011058550035941c040000c07005c0b006c2840f0725000008100c00f90354091260b4051b00fa0210001c5e5641400701d00a0750b201686081c0c64050300038803100080c00c2c0340c41d418400110205444100414840303a0f0340800035807000b010307441450f5a550002c60b4068440e0380200185102d440c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 360818866 1250 360817616 360817621
    0x120a12081e0a020901022506090b07121409190f0e160c06020909011e050609010210020304170304030206040c090c050a030c030b090a0b120307211101050f 68
    0x1050410001d1181c10041c45204060070150228a8090b902501e01480142c64404000040342083d603c91585030880b404011460190000b400250003101d080b80c5540d403400342d60b240d42c12000d01603800003500000070008594003090161300c05481d6050200401c910303003c0c030040000c081d01e1010800d10a9079011a0b030511919a00c21186800303040a10000181e0345000b00304100719103400d0303142d801086000410201002082d4042d00c551190082410b9034030341e150314011145581c1d03006026a601210100041ca9040040840366042d00c181d000d80031100007c01c0d0314010b1740c006482260550708241d00d000101301d81401031802903200b940a0913050402d42800c0c4104682ca1b0000801c25107024510611a908002110480d04a40c200418505002c0d2020740007050403010450b0400d041000304510603000c0c0d072212a150380c040750b45288010600d24015502e01070180000c1c01c1c00e4519980d06180d00e091000e078000d2142d14a00802031011450702c00b420340d082a24500380400d926801e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 360820116 1250 360818866 360818903
    0x30c0d0e0a0308061018120506060a030f03050c03040914090c01080c0d022503020114070905010206060d1110120c0216120c0915090c11060a0e0a1a070e0a14040b120a 73
    0x43c0d4ac4c0001c0d048a0b1300e070749141035449401c1000b02403103005040c0540040c4824031072000b40103a4006020303100c020885800d4142441c180f035442120450078034000e00c41103062039030184009034004c102c0080c0300c5044c680c066030040f000b54014400340d060b042042c60000031183c0b0050094420702d100e6400070940110620100010340c50181100c010300400010901550340d000030802d44c450422501c000d0051803d0520480c0c054201c5407154209130324011180c0c6007a003140051602021134101004014041c03113003241c5032080e000881e41c81040260040000c1e251045000b100c50703024840c0d04140a0340d030b400c42c1c4100c404001501030050700070f2804000402c0548100d40c0401e1590920f03003607503407907460502c1d02d6000c01020440d400343d950500c6920904104018403000e40e001d0008414401146940c09004400302e8040c000544000f2030368100e0705043c1c8104003100c1c210444481c0c640420420840074000700d183c010341000c04611224040481044040c02650150b080e0b000c0c48010203d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 360821366 1250 360820116 360820123
    0x52505070821090a030212070c05030610170d0206061005210a06050a14130605060f040801050703020c0d050703050706050f0411010f270308030c0d0e0a03080610181205 74
    0x1d1142910360451382d0404c01103900480c04000000c030410b11180d54103010b290048000b0340c90380107250903102d0841084543d0075007100940c1601c42801f086d0b2145101c0c982d03819a2228046000c500680208000c40c1c85400c00c10140c1050b114a81032031814042105501130848805112020002e800c8bc4c09001c014000d51041c14090041a03500c00382d107a08202c01d070b0060034000800180590812011402d06032081d9024101911000304078907907558084410f000365802c540940401f5500e89000300710280e01038402c881600340190701030911000d8500e016034841d002031000b5028032504200e64800103002e44035062044140702c036501040d04050a000f8945074030302042c0350500000314003c6040075040030201100000303400921030201d0803482e00e0a0460300561000b04400ca01009011120600d40060980c11701c82800404c00080e030007442c207139150060039018011900d0300c00850014109140030340003103542401e140010313051600c03510402200396400b503211406030071003107410040c061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 360822616 1250 360821366 360821371
    0xd050301090c0c080726040902091305010609051002011416080610051c0b100207080f03030f0a020a0c150605010f0905060307030207030c0506090a0b010504052505070821 75
    0x903e40020100b255907924901c40c812090701811000802e03540802620000d9043e000c1e042445441684450f40e452150f80a500140c99492280b144221500c9102e1581d01c0390701d040340c0c4141e40d19a070702c1d0302c0c210034421580b00101403070003195201c40c0000800003199030710500a0407400480d0031801d0045000800c256000350019100e11903141040d03001030707800000c0d5241119074844004081420701200740080000e200080e4201d098102600341e41c58001c80c42104585040c1c0a40f00c890b40000f030b9090300c1e44000c44d03803228200d002c8004145181d1465010341400842c50070415014800c03038407400c881c0d02c881d45146950544400c0300b44129640012914001030403803d01240b950309141c00a01d69010040441080681c0842c60009162040314443c20182d000019030b00203041086070303d9101c1030825402d5541c188800d00003d19070400d132140303d2044482c03116840d1410400240400703085240c3c004132042110a01c040000305460700c008120301941ea040031007049110244d02003044900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 360823866 1250 360822616 360822641
    0x80105040f020a021209061606091a041a060d02090a051005010e130b18042909060423010606020c0307060f09030b0601140c0c150306030d050304140d05030109 70
    0x5005039695290002044110044001c0800d46c80e0107014020882034014602e401c50141c0625858800f030003ca5449400028080d82100340e000c0d5005185500711003040d60002c107000e20282086100d013200c54101600400010300039200c2c0f0079540c00040004d0015508cd1078000e694100740b214000d0308600610040100707080c404090090400014a42080b24010200b95600e4110540440e81c85404105c1030007148110700f00181030600741540d03c2a18444200000b40515400d0003866142030200b41c49944008002c0450756582d5170740745d40a4140024109035059940c1c144c140d8040c2c00c1c0201d0780607058542c002d1500350400d0003014a404180e40c0502c0a102d42c80c80300350845a4080d410005598020301c00c00d5458692034012200d00c14014110b0130b10040101c2d11000881c2d0100d4941c0018200b121094030256038081107881c188001d40d0f000b50b0641c4604400d0000350301171001340d58400e0007980341350703580c0d8051712107039041414134100707200007500000060244049511514000052 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 360825116 1250 360823866 360823871
    0x1030b0102030a1d151b031e18030f0d030b0904170c0a08040e091b0f011b020a06090513090506010b16020d0b01181506050c07090606080105040f 64
    0x46100040d48038807921980c0c108100c001403500d0080c0000101c0b00021000c007038502c0fa021034a6046002054116041000580d521010516001c11002060360b10f9604440d00760002d44041c0040c01005038800040b003100d00607030303001301056981e052000c401c0c13142740c0038003030032400c26511002000c0750074400c6064410303400c000500020500003264031520001d004111550b4609480d01145400c1000c0300082820b0000500800c0d04001604440d0140001104403040402410241c0c4c0f10a20900c020030307001050030160400e250b11540da0351520180b01b445c0001221641e4000c181203d141350050701c0400e01127901040070f4107203200c014040e2030f00b030030003040110000c0d691243c458206200f4a8032010000c9480000078400100400c0001e40c02055404140d045103841c480030f071400d100d00d0010701f03204201c1d000e521203d030040c403403a03010100c84c0f41c201d5030030000c0c2070740c40b80c001541c80c407181d120700c01010070788030381c1482188050700f100c0d01e03440410340c0f400003004140d80c680c0c0c4003107001cac0e030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 360826366 1250 360825116 360825131
    0xa2403030302030a39021912170601020a240207060209090106020d05041a04091508060106030c0504120303021b0a110f0d0209040318091b02070605040605070203030910031a0103 78
    0x41081c250403005640d441c5407421711796080300049140031b802c6002c090f40820741e811000c00308841f00041482d850910b4a80c9000c11140d040f8420464400b01d61160158002258800000d210650b4108824041862900080c00c403038264000300c0c0c200d00700880b42d0550001d01d1400514180041500404840c80201148072078104014190f0255100ea0340041400112001c084e5207080156000f400e94001304010a407034030740c50720281c400144202c0c80c10f8011100013080243c07180c002c0d000401c00584076949032030329100c01c00b400060080b60590805600780030044c036004509164420800240c1e004112008041c1803116403100100081e622800704101042c6c2541c41d0a201c41641c1c80d0111001c0580e65239909042c0e40c00213020710792201001c01c1c80d202013015185540407240c081803c0382c92181e134408141c02139aa4182500030000422001d01040240300c0c4183c0c000c00005101030b05031382c24150b02c40702142047c0010341004010070b480300402c00c0c41142d25403011103205803d00c0c00f4050359 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 360827616 1250 360826366 360826421
    0x3060103080f03091e010209122a030109170703090608040c050f0409120c0c0f080c060c03040315020406030f0501050a0519050d03050703020f0f060a2403030302030a 73
    0x5204100c001d944251000c00010419130b0f0502c8906124580d0001c2d44440c2803d001c5060300039448100740a200d02a0030b0700001900c0c0001a401c0d04034801840261090700d6413540d40c40c4528040c5811030362541d05d0b8012100004c06038080d45187e100e070605020b480c2ca20740d1500ae04004500c1e0051420864400200300c040742030703100800102e0b40c040c0c40c02c000c149120702c04207015021240b0060024070702c02d44c080c5400c503804032070440f440d40221011484076489144030078041c07800384942500c551000100c4803481c90020010704120340591308881c176190341ca43d6400c000300c03001034010511503404a401c201503a01070040d0300b42c140c019501000f0940c1008000b841c500d40a0217001d01908016099044c01144104000c002c1c0074000c00460003002586001881503104100840041c0106061594030300800a00e644c210201480904219507900602c01e0007001d4140c12160f40a2403920b41c0e21205401d40f03168030195000c0d9a0242c6e49250002c0344100b964000f022108214200741c000708a407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 360828866 1250 360827616 360827633
    0x9030406080406091406060312030c0901080702030408010606090f061b0605071419110f07050907140c01060906050a0b0403231902100f05070b0408041503020c060603060103 76
    0x9440580c00c041c1442e03226810554000c011000d0b009100100c0d500444030a000c000940300d10810048040310045100d60303000c140309003c259107207a070009042c08161825801184140d6100010748101c0b42080d90b601d182c3d034296102e60b07204034007182086a003401904650003104000e04041d0400c00040c90200016090244240f0005450541d07a8800b18a10900c01c2c00c080034209424110f06441e00e25048a18805805c0c5005600100b06d050301c0300f1184038004170303080241701d042c1006082d403280362500344031031110003d06501c100f11441002200c46031300c0c2d0000c0d0100c0d00ca0310b00005500c0c0d0030890744200319542504810301c900e100d120108904003202c8215019a41d1000104000c511060712a4030100d00c1c401300f03c5024003400750590941c42c00b410504007500e0080724440d010003e992030a44058206c48044000940200007001c04a5101c580075a00a481a4141d03485c00340d992013a00702c090401c800400001b0b40000d10800840001c02440c0c0e005103003140a0161540742d035070b42280f03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 360830116 1250 360828866 360828869
    0x3120a1d030312070306050604061101060f0503031207030b0402031807050102030c0d0c080d0623060f070f2307031b121527140c09130f050a03051e03090304 69
    0x3d1416400248001c3c8260494001002d016040744e44a5450702000343c2440087d8014082c598601140001c00040c2141c00e40b04950700075004c0d615002c104640000c030307440d005007900145902c3d4005003055840c0c0d03100440c070035040f01039080c5100020514541c10110303181c0c0310f1411580b090000c09007816002c11054401c4030b0700c0c1407182100718a0301d096079649c01200304a40100d807800b000082c03540740358650040c03c10100101d1103450a45401040000e0182e880710918000040c050a000145004c081c4410790340680d0207210139412110841420000304e1100c180d45401a04003041080900b103188052f01d4031020710a4840b03404d22248104c0c2d207591030b20140295803411484405c1c1421913210104003050316074104108032040c9940d60101401c0c04080ba02404100c14204984d01c0219030365080440092450344c103600c42c2500100c0440c52044280d40d09105900c11342d0014004004c640c044901c20385440340c8901802d0014070099000e5018144090801c00c204402d56001000320340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 360831366 1250 360830116 360830137
    0x4050c090d030c02030a0803011e0e0601030b04021204030f11030c120306010908030406030605100e0904061104181410030302060a110c010903181d0112050c03120a1d0303 75
    0x20078410396080803205401c44080c00ba406005001526042c03140c450000d6041e0380c01c0c1c85030503d519220414108807050f061003034200d554070210214400b581b10340c00004045000800141c201720142d070311511b140c20244c8003203000c02d1150700c001107840d40107910018a100e801000d10304011307813000d116803140700d405c0e145000604000300295241e8040e510708400f500d0000e0440362520f44925000d001007441c0d00406200c2e0a445c140591a140b00f48190510740d600582013040c152203a596040140401000000c807900d404d000c0803e065060549014030303022071590200300c0c040e40b61800e1012620281400f101d8040311642840841d03000900a038000c054500000380d490216130542015003d00286000c05500f0080507130185540000003c824542d0040d25541c081c0d40ca8031070300e04180e03046003882071140d040320040100c1d610030210004494000d40c1594424441c3d50002401d1040c0c6000c00340b09a2400b09040340302c9030b4026404041d416107000c91405800748940026528040d009500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 360832616 1250 360831366 360831379
    0x302030307080f0c03031623390a150c020304030f0c050d03050d050a200906130e0f090c090402090a090212030403030219080703080c0412061a04050c09 67
    0x400003d00c08a044541c2c440c140e8041c0e035182c1c100b0400018141c40340c2e00104000506401200c0c0d020140110b101180d00b00152040c3d150640405280f801b01100754043c03c0007100792104450711001e0403115680124151028002d01c1c2c03031a103005c50054003540c81c950351380c81ca4403002c006c0954000007246c050701d0300811822515410b91400c00520b003404d03045185c10032000e020000030940c001014007100550b50506101c01c0d511200040110f0340d41c0c01c400d10344d4000090042c4102820000280f01440000d04603510f80321410f4081100c004940d80032950303a01401003000641169018104e8001641c0e4010b0700800b81040009004040e01502c0648240c1d20807020400c0c55416a00040046034041c1680703a80c0c1d0b80c202e5a03207440750450300c01a0098003801125001c1e00b4070b600c0070030050680c030a6205040a409031011180000010005104107404101c00f140c400440c02c1e40000b490311811001c06c1c02d140c0c07200701810031000710507918096810042402006c110b0340d01a0b9400d0075040c0d419 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 360833866 1250 360832616 360832627
    0x60406050d0e030d05040605130203061b12010e060307060309030e0405090c12031809090607031e02131409061e0301020708030a0609050f010e1603240302090a06030203030708 77
    0x201d400a040d040114405840300060000d000f2070701d030304024450f50081d00704003c5581d0300192928803040034a8029450b421050001d8640c2284920308417400c10340580300740c10401003800c90015000207070461a12030081d803003041128641001600c01030a59480d0034030011041d50790113030204428628a03482a80c5aa0014495501c00c002c0440c160a0040c0080034074106441840c0d100c0c0c0c090a568450801d03502d4100321541000701005014003000c5005020300d0f0744500d0118006c1000e4041440300e00f10541c0d1450f0403044500103441402214004021a9850321401607480070140f074215004126540c1044000c1c1d42d0180c00c801c060000325152400c84101c800041d00900c5284401414810080107020881495500103010340d8908401008551107034030499820034800d20680280d0045000040c002540c0e8203a0405a00e0150501040c840218540010042a80c03064400c1505000d9002c00075071501c200000e8200104170004c01105003190080707074403441070800c01f60145000103030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 360835116 1250 360833866 360833887
    0x10501030b011103070b0609011505030a020a0207050a03031e09080a17040504021204061d0a0303022b05070215010612021804020c030c0d030b09160908010e03130f0506040605 77
    0x40750302c00c4803c0055035a107070034600c0c00341107a000548082c0e01920300c80001040d0a02a07212006442c981e546030b05007141c4d00e80040401075070100041c4001c502a1a20000301906c410b0a0f8501a5109450300340701240e050f0100000f0841c1d1030f1804040040355441001112000f040c0c1042154110001040c11103007080d8204940c440c50b445a0b420030710002c0d820014084c02864140190701c200001d005010030380a01c0081c0f00000600100c294111904403000603019600600e8100066400d4542e041480109031501d00c0111015000294443c010400c1456060040400e5107030501055810755051010040902d55600c06003c0c1d0243c0c0003458501488029040d2005240010030556850a01c4e1045544070340000c40c0710303d01441888400300c010f5001c2d0259040425000d428040555180c48096000403c050300b0301060081c24440032400d40028080c0c85607100e1030000666482c015007002401a140315031007031603401c0350031030709202990b101d808640c11143c252504980b118110407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 360836366 1250 360835116 360835127
    0x8060111070312020708010b090c04050910080d031a03060c2d030405010b1003050c090d030c051e070806010302060a030b03190507090c0503100303260a05012c010501030b01 76
    0x2000503001c00d4203045000c60f07882c2c1c001140e8003500e003858024080d944400003031114091040e0b0301005040418031040c06141005400158003204100d080708505a4a200c1641401603e0320500000307612480c145d05811907000900b104484181d000b009545000107840c07185000c0e404041c142c140554008c01c22808021a0b40240034403441c0e01c0e2a40c0e820207180c070741c0c004c01e0801d403040d000f04e5486800c80000d44c080c0c41564801c0028105030b6107411340c0f11040182100c006503045080c80500c1e00c042001ca1070810880c030480e00551480d0066284000ca03031440c1c14400e600040e26940420014030040e03c500c000c1d43c11001150502190240c01c640010741403020761004042c001c446d141881c001e01070000341c088121410000c04101074548800d0450381407004544040c44210580c5080001920a5004c511040120b401c107074498424540b00e4211280d00361405400c60f034503400180320b600003c107811204002070103c01d007102d4825044002c0200760520410b410315a82e102c0e403005590058 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 360837616 1250 360836366 360836369
    0xe03040302090903090108011e030f0f0f1a0a0605010c1e02030d09090b010903110108090c06072102060708070320070b0f10050a050f060705030406110c0904030806011107 75
    0x102034158a250070b00f0829075030303007124441900080008000103104000c941c140c2c00c0003031040281c0c06045003503031560010401445803c0340e040790108414808510b00c1c000c81d10f04140b060901000030a44040d1021101310042d0408149501d07015040000da03030400a00c000042e481814141e4000d00c950740c0c8012002c49040107501406080211101035621001d6841915a11601041980c0010004584039440c501004041c0384004800d00040d40c014a40c03036034405002d4040b110f501c901800410251b400c00782048403238a6903845005220700c152a4101205005440113100615003454001c2800c007002c4d0065003070594403010011001c898020121440051002c016928441864454226a0100e440405161440c40483d4024440d400510102ea10042c880b01c41141088204660751201c0285a58001410490741e00040e03414009800101300e6600e520b45090f2410681c1d070300300300080b00060320680d0f200c0704000020360000c0e1203907002102860110422030100e860b45203402c0f800d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 360838866 1250 360837616 360837619
    0xf12050a0501060e0708220308041506060e0301050901020703090e0c0d0507120515150c0c130902151606110c070e01050117010b030105040c0207091125030906030e03040302 76
    0xb008008100c50762135007031160107000030b85d07220001c5617100c00c000031983c00304028003041c100e070341e030280303030100e8495900740d600035000f8010100c1e03002e55803004004480c983d61040001c2183c980d800c01007442c080c416540e10200c00c4009500d0100540d40c0140740340350038000c542401c0500008268070030b130a0401c7d151204011403040141d428140e9001d0241d0340380742074410b500d604140c002504c0c4000754041035041c0720003800c4680d01d5003024603080d51a412031034080d076440c800c60a41034240d98a0602c14520788411030000075401c520b9006110800c40c071007100c10709806040000482103174080884841a50300440c0000b40c0c000c107035640034064440d04010b00c0703561250b120003241c1d28210403e000c1c100c5100340c8514042102041d0151070051003403040c1030585009100420403814039800c1146404054415610180e4442414004a50114141c0b03288280046500d00200844c034000c8a9a002c00c40c02c99404800180e400510141c1c075030051804141d101d115459002c43d040003950060742d0b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 360840116 1250 360838866 360838871
    0x6040215071e14010e0a030e04090516090b0307240c1506080c01110304030b040828021212040f030908010c031a04050412051e0c030a09060503010f12050a0501 70
    0x902c032003049a1040c00320803d98081008034829080590148102c08501e00180c000e4024551142c4040d9146052190300031303007150b2141c2e590400904207004541a054603d002c03801300701d081008140880e480e10390424040d0340114014414075103400584540101d8000403101915075a04c400c0782c4c80f805412005224400200c044c8504d1411074000074240c0b1613450485004034155801140d450702c02821005c640d400402c410f10101c0c1440601560050082d41382e2454054411b00c0304c8800030000704440c910f9140300000c03106860741402407060408481160314205008100f90706412200544000e0980d00d111001c5010103010f050340c1e400904001000704840b01500b030000c0c0c0a0407400d05800000211088204681d01e01031003154002da03080804001c208c020248240c404d03602c10304005401c21200841c41400c4902a40103150f84c900c0302c4044c2d0b4440001c4480035000e50b12540000091040610040c030007150400b80c407408850b11100c40480c0601c4600301f0605005204001074103550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 360841366 1250 360840116 360840143
    0x315040606021b0109060c0f0507030503280c02090f07140a020c01030b0901080703290103030e030d03050411060d1103100302011101061202151209070f0807080604021507 75
    0x182c011501c0d41e064402412580a07960580b0300455440c1c640b4061440868017040400300072601d2544d103070301220f201d1001c907000030b41c5946499165400a0702a61a080c0924143c01c080c0803e54500075203000f1107040803d001100c13030340028180039004050180e130b15249000290840e1240c40080c0580c000001c18a9607400b00c00c00081d250310044ea03d00780881d06240b84081d0909108402d1412502108060101282581d4031980c0440780c00c130001c04203204064284850311030824800340214400d071160030707401401d40d003814100000b1401c0441030502c0c01d0100000b08240c290b41c0d0180c00800c84066540e40b101e10209001000700300341034003082e400803041280c84078451100c002643d000740c0700e00134043d0b080a200c5099841d14014241c0315844114076a0043c204155000f20303500b04143d078203080c441501901c2d1324020781164002ba8552006804020f444480a40240074140e4030028103c07180c01d10115aa0340c50b4040d20090041c0f03043c03000e05a00032040300a0303401c10741c1c5c460400c40b100c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 360842616 1250 360841366 360841379
    0x80f100504020f0a150f0507021003050405102d0207020109030228290c15070c0b040303050115020109050c13090b090307021306180b0301021b010203040b070c1703150406 75
    0x85120381c0e05402041110090640c000d0041f41540c2007070360300030501d000c01d41c03a4007811009418050401c455503c281551761981c80303c0e90040e006034955003011600c0c86091a0000407051a11480c039806442c0704004081c0581d078403007481815203805503401c140c6030b144000c0d0f5684d06510b8022a901510040a002c00d00c1c074140740c044101c50200030900707050031700e0170840c1c411640300d800026500760788030388905004040d074910882d510210781e040064504170315031180d02c6000350072582100000d40da00014000c003084c25103082004c40643c40200441d00d030341e54640b5940c2400003e8203204869091452810701d420750030880c0c0d8541e10044001c41410f00703080030382c3d41b6081110100d2045c40601c3c001c2e54140014800c80c4d003210280202104641c6001c01102d00a098180c2c1094265400b000030500b498102500000c42c0d41c00b0380b0006a80346081d08207005c11030b00140007082080081182107020419040c0071450300d054000020b5940e40340c3c10f8100492480718160240c005003416800140c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 360843866 1250 360842616 360842639
    0x90b0139050105060405071103180a03060e030d0606140706050402031c0f0e03030310060809010f0c1205060604050619020f060403120c14041203020a0611090a080f100504020f0a 78
    0x151070649081c0a10380340c0c1f1b10280e0f00110a0305980d0300ca54401c0c0141420500300502d42042100c0c041c0c001d60b0b6441d103c3d11382d001079840368580d07040c41d58000110403841a049202d100001c0440740780421205014032482000b1340701c0c080d40600003a031510041001d5590600011419507140391144000c0e04070000b0180c0300304040c0c2140408903103191013620290a0107c1124845c054040c442e0400600b402815107550f100980201c141d50769070a404620000140710340e1890301c006890341c49000e006100810180c500007800180240014003040181d81c440005480721041c0c50041e485696000145c1207142182501070216148154003c4c001490380051034100703118290301c4c0503c142c5070000740984a0446c0c0d51b03468074158070100400c0081d02c083c5078842d1640f0b0710900c161034411b54103032103200c15030b00b03100c0c04e100070004d0001e031425151400c401c5c0c030310040c03070414041c0250a944501450316405242c00e42a41c064071240014115a1103a0a1407000f460040c569200c1c1500c2c0c4401828 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 360845116 1250 360843866 360843871
    0x40807030210031e0e030c01090605010f0609050d020103020a14040308190e0d12030e01140901060501170615041809050c0a08071a0f04030f0c090b0139050105 70
    0x3500071200b488682c03910038019130b410311840e0500000c0c107910890303082d80145200c09155400340030510a9a44054080c0102c490715805007801040550400110821840407a4015010311040b8003041145444407001028150b409090050310313503501407801c5d6183d8a1300070131890740d44c03000a0301008001c2c0c060301030081c07040540200340ba1138400a10554070b0800201c84154171500340200400018150316610760030120328503001c600c079103101140c0303820f44400d0413548840c20669401c00000c0c920920800b4010402442c200035000040c0404200035100504a035000b10b50210230071f04030f086102e0445004020302440440b20000064044000744400e5070116068080c0030201100c61400e800001c1c1903031640c00160440a150bc070352540104400782207842d44036014841c950313825041102500c020f500507000d081d150790007450f00c460280125000070a0302842e02e4261144e070303648039200001a080724501c041c0100d81454410407020200c9030194035203480c3c58584420402c0c1900300a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 360846366 1250 360845116 360845119
    0x61507030c0309142d0301060303031b020a120305040305070209010e0717011815170601090c020d080115091a07020f0a0302060703050d0605090f01150f051e0d020408070302 76
    0x485554441d82000303841403020a01d5503000c91a4001c6003d060b9402200c44480201c41708038015001030b000219003591a181d20980100c0d940e9104c82800081c0c451452049007080d101a000840042e51807115a40440030031000b09036032900081e04150007442142d400b1500140b07044c0341c0d5a506c04140c07044d21400c0300c80c000024480000d40d25080c00e0882c4680c140c0b1880346400480540800c5103900400421916000e141091071001681070401c002c034003490300b0b50b01c01a00466044c021010306448054110f8001c550144280540d20b80c1d00007201070540c3e00542440c0f02c422480101164074201c26040000c001401100d0414455030000083c075105200342c400043c0c10310f1040c204000c030030041c0720281d0070500801918002900c120014401c4010002c80028619101c20110702c50540c11148514090140c6005000e81c8840c9000e80f00300982030f1400302c0860403040001419402040d21032484d5000381c031622003540c5000016994001e49004003107450b035559080c5d0725a9601284002e9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 360847616 1250 360846366 360846377
    0x1305160e07020f0c060307050f0f0c0c1f090302010c05011d010c45091e050112050a06150b07050102041505040e0115030e1606091e0905061507030c03 66
    0x10300501080c02c080313000d80240210300b1a5079140c002d490a611482a00200d81010080f0049d80c0c000380001c0d002c1d01702008010b01c5805205400d000c03d120703416900a050350061114000300d15030000380c0005a0380d0a10f004420402c052034490b0140000b103110300303100c1400140820b80c040701544172100e032485a941d403108904180b8100b0b0a00000070b040d2050a60341d111200d042210011410f280c0c00721100680443c040c0c2d101d030448110b0700c2418006174044400421003903250380728001d036400347c4600b80d000c10f01244161743e619030390b00303492400500c555220380c1c510050500f8a1030100040c140ca4219940d6408140f42c03060003580603014031b980c400d0600b00d05030307045403188050310140c2c0c01c070b00607141541c0d081444550001c00b01d020030721708154542400a546903801d1121886201c0222074204400c0d08006014107440400e4000340940c1c60640103468441034090140c104607041454005190307100c1101140380e81035480001c100260000034881c082550012a05018178041d03031791ba = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 360848866 1250 360847616 360847633
    0x1505070315060c031710080304060903020108010905010b0703030504020a1a0c01050f0603030a030f0906020d0b03060a0c0507020f03010e071d010b070f0209131b050f0d0b1305160e0702 81
    0x3a20110300f51200600050324214a0b0444400209000c0342c010003d84034540c02c0d1541c4524144c41d540c880e400c03490005580010810440d43c03c01c0b007650142142010501003503041191a0003207010300d14002c1c080580344c402040554179480101c1e0041c09000080e00a45105034104182c0c81c2c0c001524000300390310b464009040c00d4088080c060180000801440c9007030403510341200a400c2518032007468a607204020070005100344010207203164803240100302240f2410825040101c02001450b4032818901c40f40e01d030303945c01001c4490469044603940d020417940004a401801600d030030700d02034880e54502145c9940ca1600d0302c2c04240001e0848441682c88901c0441c00d40644900106162507007034500e001403801d60030b0b099100e46042440c8100301c0039503c4101c5419060841c0078194400c00405001500f0b0140c000034030b4003401e84070055900403d5070b602c015088014654090241154454020407006110401a003015002080340e2240c8440c0401a0f0643c02c1d2848000742c4101102c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 360850116 1250 360848866 360848879
    0x1203060b0c0a03020f0c090c0307210c02010e06042301060b0f1306110c09070e030d030209010909050402090103080c0f0102070c052107060e0a09060f060314040c030f1505070315 78
    0x18039a60002020b8140150364a5400c60190723503401c041c120f001031200301d0301c0b01202ea21460b16902c103603500154001c034040e1286503010382141e08180c001c64494001c10704200201e00c900d603584400d520030b07805554044c0800d200c038600412103030b001458024000549c0c1404101800040c1c00140422480940420740d155401d507000581c068a0500d183c00c1144006a10314000301480c0d44040c10381000315204020f02c00103400d01c41c40b0560720000c41ea0104524070746513030040b80341020b05a01581080709083c903400148003044148030042a42000151700c120701041030041400c2c001d41c203c025901c0340d5036454a030a5001b090300401d80600000e405044910744442c0a5800031441440507140a90904008849000d1138405468115111b181c0010304a0791600c13409000b070140c002d04541007400d0284c028103940303498420900b081c0c070080038480801c40034600300007142d81c00100c5100d0101c0928010b010304500d1a0704070346440c44c040402850b00d82680102006000e4185510081c6c0c0d02c460 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 360851366 1250 360850116 360850123
    0x905150907020601060503040f0b0702070810021c090602070506040b0412092409081f05151804020f060313020a0608101e08030a120509191203060b0c0a03020f 70
    0x4941074010b80c421801000418091002950040c0c00313410030600e1000c2c10f407510340300c034603023a1480001640660070400c010442802003001c254020401507142c18802c00c40b4020f1801c0031820708045a558565230700403c1000d6045803030741680304086d1407980c0717800d003044445000112010b40c0d0400c441288510501e00c60301703035241502c880e42e01c03800c800c41030b00301a08441c01d0100500c0f42841156900800c0011007040390304205181d04c0410103c5c90309581e250001d07130788050050b40e25046110300411555558103414181003406109490300c640d1a07000040b0382c910b601030981d42040e8000184500c02241c0c80f48130300e4440c0260b41e0103410650303d0808860040307044500001103556035105000e481a00800042c0c4a0458041ca0b2034140c0c40c0c200c814110f901101d20b10b0040741640104a038481e400340101640b18544802610401d80851148030740042c1c9840c00500c042c42400d903050f1240e009501c40d102a10307010b01c0c4e90351100d03007002800359030f02010320003a4090310855080640941001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 360852616 1250 360851366 360851371
    0xb030403110601050604180b130905071208030f07030f060609081603030503010510030603061a2103070b060145080d0c030c06020705010504140a0c1a0c0102030109051509 75
    0x500800c1c82e01d85040351700c503000a44d202402680a07101c40c4158023680e50301401c84003400520000003080ca0032071900d039240c21402e03032160000050540030280864583c0c41030340e620948109220380d1542d20034004900800501c0ea00d601d22510f40040450703045d61140d0038a050760000021514807852092a030107010016110080000da420001880641040e0001038034401da14180030904070b4a81e555407040c0c400e01101446640070100c484030061030480740d0102c0450000b0005134031a142a00e41989a10803801c000d071030f401d0200041003040e40304004003612507200c8204001d078004840c200c10003108080e050701015100f01d01498010121803281c030012100d10324010b0218071038110f001d81d00303118000d405a051280c2c001ca59070200d1800d0008041c0a44a10000102413a141c60300401c128002c0d40380c3d5401d580002e101c0c1c4000b4cc0d036801d503401554026a49828803512030740a040e414030a00240340e880d03500200001070341090a80040d80514404038592114035071080c107001248104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 360853866 1250 360852616 360852619
    0x1505010f1e03150b040e06031e250509180d0905061e04122f09061e0301020403151107031d152b0507090e090f06010b03040311060105 59
    0x58014881c006070003540816060380890b40c050b0949965102e0440311a0429030054802e50a44020828a80307014894815101c02d5005050110700b074680743d05036120120640041d003180c0002600c0c6c5045800552100100002406503801d07103420350b00c0e001c14004070705800c0030710300c42d104c00203006500a01b29401580d00183c07000d402e001420120b00034075514081d10a0b220030040102142d2008000042c00550340035485001c80d03080c0303a41000e8900c0b1807040d0500da400000c81d022010700c3d0355200000e40c04c1141110020444006c0007098981c8640d58044541e0540c8009400010030101c06c0640e44400e43c06c0030b00b0050300c0100403282e821403040349001400581041a03604043e40b8000325050003100c0600715443c480b9140d50540c4081d4003014142d1084103007500a80e64250448074010000d00040400f0701142c10444d201400c46009070192042c504c1c042c400040d1404c1003040310b0707a840c01007042202c801d56501c2c4209040d9501c19201540050f042011002c100100000e0300c6048860 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 360855116 1250 360853866 360853907
    0x1713061d1b0d020d08040b0307020703110904150228020d08010b07031710031502120a0e03031b0c01050115090902030906060112020910180512030306011404091505010f 74
    0x2c156080040c0c0301c0640c10300702c4010350180404030340e50480300051842090300e500282030160460405805202200c2040c62048100341708010014000150701c0403580c284000258031011082c0d1400c021800c80380d100410305050b2010b81c44503a0303000802c4245c1111980b20b80010340d0f200d0318200041c2c45000009000709003804900d403515000c120645500540d8899281c680755143d68034603040354403d400014150381c0104141d01c03052055011150070071800c0790204540d04000c041d454490000900a030300401c03210005100028401c800c454803d42e13454000c101da1341c1c44840c1c0754140e940b68040c4000041411b0340100d2405014400c0742e0041c02030788001c1040341c0d284801107443c00e01014180240030b4003480300c3c090b01d40790400d1014840516844510340044550070300410200b0540c4020b2080b801c5004c0104451008802c40750441c0d030030318000058080503040918244210f42c00400c00724644070424589009d43e207280825035000b40d03240c1444445880e42154441682c90074040c4a12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 360856366 1250 360855116 360855139
    0x11403061302120717030703030c050c0d111005040c150203070807111302190f020a0c031b0b07150b0a080c0d1704080309030706020601061713061d1b 66
    0x103003d01c0d062101040000c00c651505481c1c070610780042d0704070101100c05a1020030303075130f042540500401ca40c00748186011802c004001140366030350500d881030030040c494121891003504006000354103058008540c10312131030800e45006040c0703103014490328903018081c803c01c020052000c011a0001604004c01074240140c640f0742c40e00721100400340030703800420042000807101d81400030300040d8200380103041e0420641040039000141e03800d919011500300703520040002e003095644905582e041400f15284114080c0c01412054080c4c200316084500411070a08010886024203e841079544060040f01802414800c0c0210f4500910f560740c0c02c0ba42948406040c10512400c1060041c1031001b4070050440c2d05000c50381c8a03401420003900005140245400c04010410082ca590702c001c01d82cbe5858128001d2031080c0100d0660034655101713010450038886107083c0c044454010004100540b0803d8041c50607103d008100c0b02140686040c0d0034a801d90000c03140140400900600280e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 360857616 1250 360856366 360856369
    0x30c0f05060f09010207030b07170105030304050d080903071e140415030201110a06050a0605090c0703090512010b03070b09040e0a111005070b0705071b050f2115011403061302 77
    0x9800a9440f181140300307281000000c50120103150307026003203139201c1080c40c060f440e041c0300342e204050300658001e900400041100e5142c4010240c030740c68000d85900d888500c6036000a061142c107a00190700b0030302c0111060100585a281c0c03d04482400c00654800440d91040c08243c45c1c504224400d52191900104090750144910030203400c1c402050b20362280c6aa5155000c850041e205506035035075400051140c0d060181c40650441c1100800ca8107003440c43e6001410400180550b5002c0d55600c00e00da00000303004d40ac0320100f040c3c01016103108940b109541160703074024845c0c00b0710445c00c01c5400c80a058002c65107410703442d040844800140307038920511119041d240c0101c0d0802104014000218883c0c01465001d061559500b5580c3c8860703080c1082181660882c040700900042c6080000f0389d10400800d401c04016076400c01e0103004901c07446003800340000b442030140560118907910341191840302d4140d60400f0081c62072075400c01c00341565036008455001803e401c510150f07015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 360858866 1250 360857616 360857647
    0x110a020d050c15030603010e010207110d03120519060519060516020312040501080f07020604030f030617011d150c07080403020604060809100908160302010204170304030c0f0506 78
    0x1880c06907044842c815069000b0a40618600d03894050550012051040030720f804e00460b90140107900082d410211161220300750180048a000c1c401c5070b42ca000320381050300030042d0003030503100284d040000b07207080c070700b030204044042009503056450030b00c0201745c500d82448180004180f242003002030b1303401c0400a0322180d10001c0d4803028420704000700300050741c080060201070f1248910b49500c49142400160446001411030600860300900300241540c0c00150035134001c1d0945840b4615002400c015401401640c218000440b41444032540701481500040b0b1203521900414080e20012032105882d001c000005c202e24020100208000c02c6540340a0001540141c9246140c55a82e9002501075403059014602141542c1c2c10004070101c18803407404911903149003480081074682c0c5460681c07142208030003d200d200c01000742854403d6040d10003034602110800d25030b00d68014219502e03046031104482410701c115020800c2500740505408807000909064181000c0c90242001d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 360860116 1250 360858866 360858889
    0x130b070906231c0b030f01061508040f0b06010e090112030807020303071706031002070b0123060304150912020f0f0c01020c060a020c10030501030b1b1603020a0f031e110a02 76
    0xa40b91322040366001a0740c00b4408407060128080c0002407540c5032a020f040600b0f903001c407034020300c046d0000700808503101c402a2000c2a0780100081003690710500181c0701d0302a0001e4264005080b90000710b506c031002c61440000c613009450760401591054003c0340d413840225010000104190141420040820b82c0c940c0c1018004054819140c480a0084201c4e00000300650301c58018000400c8a4100c110000032469a1031300d003034140703400743c40104895200142c00180205640b0344100319110b5a9800107400c80da000251191403201148001c0d902c203684e5941d805140a800f00c80f204e0410009080782e814031040c0c002d4003203020007008008081e0400b00b0441d040d4000c0b0500440c43d9903494040341c04009003038600103025411030811014800000b0823014401208407074200b4600403460541d81140b01c07180b0503c0c003080c0c1d145022400c008140000420740c0c6d9072032a408040540105442341e0141c507131a0b03540350008244004590700e054807003a4002035000410880d0150130145005403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 360861366 1250 360860116 360860167
    0x3009050a050a06050f1803030105012a030306061206081e030c0312010f27020309030705060f040302010b1507060507030b1e030f1b09130b07090623 65
    0x31030341400d50700da003030030084000001c41d000c558460400c00d185803c41440768208410f200c11041c209a42090300e65644018019681030084104280103a4000240c000c12030b81100d448031401000540b034054050030103070041d0404201c0c0041840c440040f64404c200454000c03100904c0b001d886402c51401c0800d91140004075800100007044030441d040000784401d200f4900e140704a0361410001b41c1d00b120517904501400510511640c11b13501001c0e900d00d120840c0c108006a480d259226090318610a00400a080340905010080818403100303040344103902a80091005950301000c01c100c20170b440f900703296400350034001c03500810825801164045a24100020701c91101c2c0e00040b00c628a003400c02c00001e8004e1303005001810140000e000840c4204001c012090303420750302700c40402802101071b01540c500c2000409041c3d0f990b005544054002da90b0700400e00340070078001c09081040c040c071000318020003045040401e41100c150146400301500a0030000f4004140041500541602 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 360862616 1250 360861366 360861373
    0x9040b130c0608010501021002030c18030f070b07060f02030f04080d06051e03010f0203061c0c030b0408041706040209040b070c0b09030a180506090d050109060f0903300905 76
    0x1500015001150000580150f444000c425803400e0700082c0303061003644c42100300034014800c0c001e909030908240e800102d0608007800300c0d240c0c06d40100c5d03e481c070b91280ca86081d200d00440050424550070040c84480e00903031041c4501d280c0144280240c0c4400c1c0d51240c00b584842c000200880c6000c0050034040401c8e440c0031a5131039441c4000750300300b07107110403012200e400c4407603590741840e00344140c69003007a68603025403c5141c054005584000c1010440103209240000c0c90200011041c6580196074041e030201c04da42032034201402a80c00500821107020350042c52692820740c0016101e114560091000b2041e0341c03207644c0c0d1016000d001d003c510910010445040c000351028400d548a800481d004540f00c0c19400402420060f81c1448260f090702d100308180115100c030011510b082000381d0b01100c90103240e1070810b0050503115406800d451400c81034042c1c08000307405c14040d950003642d8190030129a00c2a402603c3c0030350031b020f14801000405804042c049801c100d00301030041003a03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 360863866 1250 360862616 360862651
    0x414091e04120e0307151206090609061508010308030420040c120b04110304020105250309050a0902210604020c120306100207030503040e270114070e09040b 69
    0x8600c8400025201200d52901000a04460381c1d840054900380d80c000300c0040240914160601041070511607009041081d5201980c40c00301a60304601e004048400d02000304c0340d034a02d60640180300328003c2c1c9c185142001c171081d5030184520340c4681a070fa00400f03142d00e103440320b5441d0380e40541c00e40043d1109900c0d0240b400820b5603030744a00e07500400c20b9241c0d03020680392100f4007001c80385410105232085160071136003100911000705403a401582801c0c0969a100003c84809044a0030039860f44907219a40c1c9250405602c0a00784044800035500c0d4080f00e034540400f03609901a00d020115002d42e10048445900c0399030f160301d900450b02800051403c102d202c0c04e541400381224110350811400402d000e82c0d4103246002c0c0d0900f044a2024041044c15665015228400c4e40701e0801c40c0311840c40801d00780007804001d2100111403800c000d0a00e004091440d01070990b842a081000001000140302c85001e10102410100c000303105910715030311603440c12030b81e4401501090307080700c16000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 360865116 1250 360863866 360863911
    0x5070c030206030901200f0306100201020712050901200a0f080f0406170a02030118090302070510030c030c080601020a06231008010f020f16030e06030c1806041409 72
    0xf10b0183d00707801c1c000310f40004000c0112031400e07a440e8140440103000c00060810240000590760800c0301103c01d20902c4010290890280c05110406400d03690403a50304680640c00c04000c0c00450400e80f01c45030704a8040400ca40380e00311141140301c017600304070044000105c03030301544034003180701c1c0c112542418021070a00010381c0240c0c22480c081002440020200b05c213004038240e115aa0780780039440d640c10b100f11000468851b54951512949540c60901014020b02c1110090300019154541d00000c030a0020003920310012200b000c6032400e402c4a5a5a100d0287c65100f004182c0090052800682d60340f0300426000405640560b180010000780340341100416000e84069500c41c3c42c00c078100f4240d9400c4452409580000390320411800242e10100c070181c03412a18010031f0343c1d00510b01c500f400d480c42440b900b881c5611a07400403c2103100c1d00c8150161544074800e0841a241c0704642c3c081c010144584d003c0c001a020846502c04540d2030000000750348444070048406200c0503200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 360866366 1250 360865116 360865129
    0x3070e03061b130315091a01050a061103120c030601123e0f0901020d0302091e011704060614030a02090c0c0321060126071b05060a0b0a050102030c0c0105070c0302 72
    0xd640d411003a20707200b1074424800d09000c403106e03c1e00d42c1400b200e81f5500d80350002c0d560b840c00f072183c9014000e8103426a2070503181403066440d68032410a80490a00c2d1200301081c041e4005c440e003c1c085022840382c8484003840b44a0030034051440500901c04035912442c076950a120034000d40c090040d008403540020740e1b0400500302c40e5040c08046604d600c4110006801d080c15036009900301441445810400d030380d00000c0b8907a00c0b80c40041c502c0d104200400494444074110410b1441d0101e090501c0108401380d03001e0000c0315920f464198012400d0000c1607111225010080d5111840300d0100d03003420350240041000200b4502120f144c440d0540f00881d11403d11a010586200a60104005035070003110703000207541e00d030210460105015803480e030b0114006c0c02000400151200b15600e00c1c42e5664403540d42a0460f045510510b04140402c0c060261801e0481c0194200040091554000419034015018210281c800325207540300465007070300100000d039200040c180001002d0384495 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 360867616 1250 360866366 360866393
    0x11101021b0a060e030c0721020301090b04020a050303180f0d02120a050c0a0303020d08060a1a03190b0904171b0d1d01092601060b03070e03061b1303 66
    0x41c0c000d000007040d141401c4084a210301000b0400f6002007207410404030002c10600142c80f9489982c0c04c4007842c0e800c0c181c0c2c0306056440001e4043d03203465044c0d0180b0007203980180c4510b200321030200c4602d4403041030607203c0c020001280c4010541d001d04007081d2404007008080c0c07043c040c0c1400544501c9800092407007000011a1b0341c01d4000c7c880280a0040900001a22000948084242d00d00e1527030000c0d91100b441408104201000012640c00d40d00d00100c9002420603c180c00c100c00440051178105500c1594020542e00c2c20a40b289030850542c001e01082c04001003c99103241d54a4031007101c8840c900360301e0540c800301088440700b50396200d01080c000728401001051b02e03a5101001410031119202c05031248000503040070500e03a44000c1c0c407800d495100c1540d0904410004140860300000c1201071865403c081000ca1032540c0c1c0b90145104042c15500c04548075201d105040d1034485c1620341907040c801181c5000350f01c0030810000c0c2802c0900718020f00003035507a03449901070030244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 360868866 1250 360867616 360867667
    0x50703120906020604030c121106070306090b0904020d1205071208010806100b0d02090607020406060c1203182003101b0224250909050906070e01110102 67
    0xc95902149030341c1c03160648028040790700003444103003040e0328050070110b10110014000880c0350400240c2c18070800c11542c10a80070400c9980d42d0805010240242120b40981103100d803400340107800500c0c0a2801600664026060020b940c166484106a00460510b45c0d003c0c04020440b17400003c49050051800404a03a212030455041403540da003030140181c004901881c1c40039080c0207808403002102ca10003681c070030050380c0e1010070340450042d00803110003a502c24602800021211740141002103036034031596450018400610f429000c036134080710301d00a003078042081240043c150840c020001c8401800c62000d0031415400a494120f04a10420201d515683c10300c0c008a9080c5040707090460300d0010705104140308213900340040c04c1c000a5024511410301141019071030100400c429111072000300114035105501521013151403080072292442c110006e1084000071030705601074402a0380c0d07483d4039240e9000450705041c00a8540003155420009861300b8220032030400941c020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 360870116 1250 360868866 360868883
    0x5040b0d0506101110020d0603050f01051e1005041107080d0b0909030a05090906011701030819140904090c09020a0e0f0402070507120813080a14010e0c010e0607050703 74
    0x200b8005000618241c1401503050010f04c0b546100c02041c08078103500c0407040d0600040e10782502106010181159520240440c0075081081c80c1498041d08524810703030401c41c411072801c0c80300100304401d40e000c45501d105070001c80c0050100e490035030000380c88410b40307554260a1007a540c4034140282d020b0340c0303c040b21640e00c440e405d1090800040740e07548410024041d5080070f08518000e4054442c07408581e100d5000701001409a81c0120b00125074031400c000c506140d5a124507120310720b50300002c101150f106140f0210340d100340c400d481403000640c0c40004c490828503a8030a00c00a41200c003403c440010f031900001c01c181145102a00070b0307078203c0d0f2b203042001000348148044c0401e05071860380210f0040065202140d00040c111080310b610030f094400c03104c12420072007203a000e4800b020403502640003001800300000940c0403415400b4598070001182603000007822560014420311242c0c120031095503045d0b0003000303903010403c0d001d40590310300300003603540600307050454000300c44054 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 360871366 1250 360870116 360870121
    0x20702030d080601050f0c010e010e0708060f070f05090d051605041503080304020607080d0c0e0f040603050c01110307020a0f1a091305130f0b01170c0a140105040b0d05 74
    0x240c1004981909242814507458504000000908501c0f0720b01074580c0442c3c0008181740b440b0f1003540b090000c0c41584008015400d00340800c251031b103005100e02d000510810021800300b14001001900aa0f03030340d15040c1c1c0720306000000f50381360713008001d00781da0144940e11181c021600a0200d504004605456506400d042c8020031044543c15010951084c101007018030010b918081144d80090701103074100e458003460325125003140300b12074440d0607040c1040d100328078494009115100442048504c1c0400c005000b00b03110448007a8070014049a014a150030380550054a070b403a0496001005d60303240482e1500492440045544286810501c6078820040320540046100d41904034104040c60110384000086840e104076803c400500c1e541c2c00072482c070f10805840b10f0365007a13019042c1c4041165070b0a2131008004c092141104861203529090305500e804515203050b02001800030025500b4031421580b6404001e81c10307414071404005c0801d061036144060300b00c001182c10007142c9071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 360872616 1250 360871366 360871369
    0xf1e0513080f0c060309120409090309120506071b020604080303010608061914010314040606080105090307240e0613110616060504050309100305040501050906090604140111030a020702 81
    0x404003503001c404950811080d5a0032150b01084503030000c203045900d542c0703a4803a468800d0500c403150008403c450070004001842d028190061200d01d0300030348030003400380c3d6101c4000c80300d1582148010a039400140001d14122700a5040e41c801c1d074a02c12590400c0407440d4081211540260448143c40e4800310040100e1940041d0040e4001030540c0c1800c020f0aa51500c0540f00307420340030b4408400400c0d402019176910070f502480243c801c000350903030303142491700305107006041c540100511542400002041200300100312100c2035403102c0001010300f0501d495840c800b03e61900c21050030745401b07100108c0001009018083c000080303100a502100307142c401c3c801e8810001c42800b0b0441030103c4905040000304113000c8c0c64000d040419599030b02d181190452189442c4154006501000fa00d0344540c1540f015100d00e210300c0c0204000c0d15507a401c40d5881a08135480d20321a4403140000703000880b1003910141a1071034400100d11040030b0081502142c10881d55181d83c0d81d401b0400c00c065 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 360873866 1250 360872616 360872647
    0x60b060d06030c0b120403080604150909110f030705120307060903350a0207030e040507090e0a05040507120c0302150a17010501050315180103061b05030105100f1e05 73
    0x801800103070600d0507002281780301c00114000c0000d0140104600054203540b100e0300554452070b8900c48840009407607048220040c98003071002d031141d00f40004546010308145054542e40034000780101015890030040001080843c14607101c540014409040000d080d40103d1180310710036199258000b410b50000030baa01100c40000c0ea40118010700c0b0b0a403504600c8196411152512025130303204128101924003844203a5100e400924180800841c0c0341e010450717500b61038081026901c01d0711286214020390f6003d8070081c001c0d03001000b0400c4410b031244e240501a620904401a400c0c0d529000100039040c0000100e0f0711b01d200140c48400c10b9400200c004a92110000d610b01c0d035410040000d05500008150244d0500113685101c2c8a984149494182404500d07414010f50703140d1402001134208050304850486416031001681400761081d281a110b010f091461580354004003110324180114a50007071140380054610a540d6804070f400441240c1c0d01d440e95180e0291342c06142 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 360875116 1250 360873866 360873869
    0x90b04121202091e010c0f031d0301020c0309061309090b150d0b01030212120d02211b0f09030a030e01111f0c051c0c020d2a060b060d06030c 62
    0x24688100302c00c0f0038a5035001090a61006541105a810360304400141c03010100d43d078014051024121a0b003080650006c2d034109480c54443c51031a1500900c000d01d4207074000c1100915444e0024000141c541c1820000b9140c90000300342250100b41d95040d06c1003c84825110a95030b03140704c9020032a0308110625468a2880240d4842c0604500385d210080412410f000c000c0c8200d41c1200a0350b40b9200c10040032000590007007001d130750b9511001e601c6009610030310a40c00c04880c2206041d80111494250911541422500000a55203060000d503d680300d203000f90303e0540c0502c030103402c80c1c0342003201040c40d503ca500e0b0f55400c03600e84400076200401e0094071704426488000c1b200c00f102c0382c21200c0ca001d07100b0110003180c80c0ba1400c400ba2458000c0c040c1a4090180e40c1d00001740f0004035820815980d42550261140d211103d6012540003894283c2d41c030b5010048a00344c115090110140b1616500600c000259043c00744001082c0f90310070380703a141e051600d0700003d0081c8043c400c00c010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 360876366 1250 360875116 360875147
    0x30207050a0302093c010f081c080402010201020d0e03280c0311011407082d01031b05190906080601080a14070503030f0706141b0d090b0412 62
    0x24409495680090b240301300051107402281c40c00d040c00d40384074190009260503003513841c240d02c49500c06080b06010760042441004581002100c0005444030041030b0304403141c5d0300204900410780b002d401510214009030003241159800c101038654a40742e4130038200c810002c80c6c043c507540d0ac41600e40c241d508040c041d41d042003821928005444582112100c001030b503050806c16141051604858010103040e1007600302070002c50104101582d01c5290188600400c040f50b041000c0050344030424502d008008602c152040e03401400803a030441140015041c0d4200480310043d01c444c007140c1d08601f0000e0010300301c80248024030440445004403070142211170001d100329890031001c580d0391a0310000191120308031610342041c0038014058107005e08000384c00c0300c0c0e44281e08401d810440c1e10846068449501e8402804026200d22000c640120a0740f00000f4000e1541d1541c0c142c5a4040d40da00f031442a50340807401e002814080b207040c0b140c0d000d1000d94409030b42a641c0905240d0300180b02e417 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 360877616 1250 360876366 360876379
    0xc0406090e0c010216140a09090302151608010e13050111130e04050303131b0b0d060e06030601050907030209130b0108010e04081204030e1201050402120c090a020904091a0403020705 80
    0x180d1009980021007220a01400303006d040b080d000203d0079484c3c880c0c000288403800d1040503800d2640000f2104038025400e18140010750f1940340800511903009100c0740001c10b460010454a500c00b55120f820900080c0d1a5069554541d1030340c0c2143c40e031544040700090701140e500011003042c0c15a40041030401140c022030b140507031303841d40c50f88402132003441c1400424000c00140007a030140440c02c004c1320b59003512072540340d04d01e01450b908100f258480361414a01d01180528109900ba03010368400fa00030308060b400c00382040703580d10307005140e001015401e00003040603a642c0c0341206424000c0035800150009120001009508160403005042102d042400000b4010000310740401000400c113601030349461400316a031081804070180c0c40440c2e0784c00d16100c080e0650189000318403c88200d09082d4036000d1140e111064645900da01c102001d001907011442c0d07800420340a5002000018002d1003907684d40c04001c51034aa000000041d03908020402d501000400c014100440d000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 360878866 1250 360877616 360877633
    0x607060e0a03091a120f13020d051005010504090203060a0b03010b030114160504080714010905130b031612030c1403040e0a0e010203130305220b0d052508090c0406090e0c0102 77
    0x1d4185c1c000094007211404605800203207900c5003c0380642c0c0710650040c499040107006083c061341d607410901c91030000c140342c0000013840d8a428401c0c0d0f40c460398050054803136903440e0b0542400519000906c90f416540703808414143e0758080c07042081c0341f16041e54078601030401030b003020501400422194140b1078208801e02c00e4203c0042c0301e004450b82c2811684074190369400403074808550b40d0019400070341c521403041c443d8103183c01650980310140d04942c00141b140c01d04405407070107441501c20032002003c81c500170910851105249600030350180904401c07511916246a100b030344002c0c0a0040c020034091301d04218001e080c0e4003090100294158140f44072a80c1c80c11018140003001c0c0700340000c1000101d10b00e1150301c6408180d25880304401a03440450340120384c000307014003101915040024616108216041c0a0842031a180b85440d1031880350039502860040c145045610411060520541d80c5014a03400b074a40034901084020356042018a072014080040e815900861038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 360880116 1250 360878866 360878887
    0x8010f0b09010f0e07111f0c0306060f05130503030325021209060c010e0a0c0f080a11040c02030c03030705041a0a021c0e04020c03090306010501110c0607060e0a03091a 74
    0x30000a43d20a0000e4402580385e03280300f40c0b4070b0b14440c0c04880d558007400f040840300044140007180081d1129406018561003800224111b402c00c5c06282c010907c5026403000b1705201c1d03005080c18000700c0030480d009903202c0c0300080c9960000c49006011010440c0d00740300c0301c1e0304007141d448003070780368002444404038419040b5802c0c0900c0141500601c008038103010080310075000865001030034001d9440008650505820110a07402000c02c0d4000350280003404640001e0a00003d58104500d070140d5403181d41088060144000d1820841c4018002070311f400710188020360141700c094640c03a40c1d4500e00f002d010a510b01000a070100c508090020840c500d40101e00c0d00d0700c550030701c09200b401a811010640d110384603100b101d40c01c6840440d0110311107800100504919804500b1201da40e0f0345d850046443e45501e505154140c1c000c45100001070a0500181c000e461103000d0228807802001a813030300d001070b16442580000d50a200411445000502031954800740c28181480c0540901 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 360881366 1250 360880116 360880139
    0x6110f0307081e040b1b040501050405040b0d0b0a0204030204050a020a020d0f020f0d0c150b0607150212090105040210051809060604030204060602030301060f0903030c03050d06030c08010f0b0901 86
    0x51481c0248070001c4001004030445901d0105a092040580d2116003040c0c10010b2a160341200c0c1c0c4042c0800440740074640301e02840590b012108140e442c1840c0030305080038000034240c0042002c4d04507034015981000102c11a10142c8501c0c0d200c4001a00d643c607500410082c1c3d107028041c880c03224410070580d4810765020400c00160040d904069003a4041c0341812860140c80030040000d0f400381c2406106caa942c8040609080d5000d0442c1e10160300c07640020404480c180d030801079001808000388000117103c240700004403211004014104207283d00d030060301c090101c0d080091039644100300021840c02c81c46400d5800d80030b261541c18138601000c840c00d45580b9152040c4120b07284800a200d5035503000c2150040c2d94054030a10140d562000060750741d41082c05100045984d115250500d0341c400c20b0010304580e01592862007540140d2030556880e0711010a88000580307805020000ca02d14812140c0103103040000004e01130105183c00c0704540075410424840d20900780100010100030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 360882616 1250 360881366 360881371
    0xa0b0105030f13111512010512151f1d0a0b0901050f0a150c030908060907270e070801060b1206100c0f06090311150106200a050a06110f03 61
    0x28002081c080b43c8604180c0003000f900e80d4025032102c0503640c07100b0800801400ba15405a420a45041c5642c8600800901c83d9008070280d4640d4008040d8181d00078040000b0364010700c0c1d1540f9500009070000585804000b5504104d0a41c2107030080490545d14034248242e100d010510304001040b41d10b0000b81d58100107100f19032090300085242086a034074009008010802c60395207881046c0c050102600c0503c0c070340b00a8001c40c20652002a601c0c1000c68003074428004a130151a4450401e01c0c03800114452661001290054116080c1d00303c205100c8c0350030320402d40300248903d42c0b078802c98600390390194110080c903038000e0004400300765080140380e40120084aa03804207881800c1c0441e68080046c0014201c0084402c40005211855100341740d8603004c0d6581c8003000340070b0f0030115a02d0801a003040030900c40c0000400c2840d1080b810101c1041d06043d592055070800005180380103001d0f501031301c1a03009032030184104200c0344500c0c11046001e20142c4e091000c102855140d50100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 360883866 1250 360882616 360882631
    0xe010608130201050a210b030c0105180d03140703030f060f05130c0e15030105040615051b071802120601030c08040305090118120b0606130332060a0b0105030f 70
    0x41160180355001e443c09003c624128800c04031000300342d21403100902000c03440d01c2d00a00030618480000d50bc100200c0303504084883c8601068a0090b040c0800903205100540400009500c401000e440340001085220f019940c007107140503c954101086a14660100c4000c4001203420440b54880c0318009100c0320144500240c880191107090300c049000120711780d4403a40d0f60000041c4c040446e13002c2c5044e1481524104200da440d400f811c0032002c44030003601d0108005103c002400d446086510840c08400c605450811f80d0b14910f1124140070050340046603500400c0b80001030122038025944114240307801d0103040022400034140200291025040040c0041d2191083c4d02400d4401382c0f4044400c0560240c90b9a014205440b680410b8111411803030580800c41a2038180c09032281d0981c52880c11714810300d9603491180380c1c6c0c006400c0c80b0340841c40103640001242e0f0303401380c4600401c4e0302e0043c140d0303442d101c44406d0031600303402d9003241400400e1080c403501c02d03c0d0301d5806911942 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 360885116 1250 360883866 360883877
    0x6050d02060d0e1f0e060114120a0203010c020a03260f0907030c0303030203040204180209160c080a030b12060106140c030702090c130902030408030f060616030503010e010608130201 80
    0xb00d0500b0b680c042c00700031680e2403541c4110120081c1c540039001c80e407010028030748410001e400000e07100e01d80f075550a100c5d1300480030480000034100d1916900138115030600500b10740c0c000d500755012a0940780382c01408405a00841c9003107091642101c2142e010304040740c01c070015080301d00c1c1c69001c001070140c1800007403801c2c4400208894000c0200001864205c0c0070101c1180c0c0c0c0e0718004001c0c0d88101e0f0201d010300d05103403260b42d110001e0080e44030a6503000b090000f440c0d80700324204624145600c01e070002c101100450001007081d00001b0111510207903800704500103000c007800f01e003584040b16545594415401045440ea101c0132850a403210702d0031195032040680515807444c010400f002c0e501c56000c20074009003d100c01d00410014040500302e118080c0c2c0c0340d010f501240001c40700582800410400642001903400d407296100d0801410740d0701b0440e102c000c00c00d62484241040f000b1960001c01880950040703c24140102203c0c0303081182442d010300102d10141c50404001d06026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 360886366 1250 360885116 360885127
    0x315040203010503031b07032f03210c01060509010b0d0b0303030f1f1508010602250b03060a0b0d05090606041a10031e0f060506030105010f05031b0a020a110406050d0206 75
    0x4002e001f84001903400c482802c120788852041400c00c085901e443c0900404802c400000340e040200311522003c5804c031110b2807044901121030810790210403d103440c0c0d566000007240d9503843d00b4600e80070f811000c10498443d0002c91201d4103c0d12000740f9103209600a10401424841c1e201b822a841681c01d05c600544808200034090a5480c84d0802c80145400f14102003c0d03e903c11000ca0407100140c0c01c50b40d048005446410703003004101c40070300c0c20399141d50f010b10603030844100454200b9009011049042da890a10305599049101c40d01c0d007840d168020311000080801c01a030300084d00f16810012450f650042120681c00182800c0c00b450703030000405003d5010b50f02c411035400200300e1122022842010040041040640c84180350b0b1420f000400c0c181001820b84e81030310b10607100c12422800c2880c060b1220b170002403120300300400032050b1212071560340d030103410b103000c1580082c10314047d0303498500013038010f6041240c0154904030301045641c0d90754038420141c54042e03880070703580e2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 360887616 1250 360886366 360886417
    0x21204140c061914030106020d27120302010c1704150e0607030c02121812070305070b0702130c0e04020708040305160f0806060a0302010e040f11031504020301050303 73
    0x34041c40081035005a02041009464480004244856115545030226881c07207800340b28060000703009040059000e10091307807515026604898000340c8844225a00b6002c070303503a864981c03241ea04a0003502c3c0b442a520000c0540901600c0342103400c50502c4290b218102a0035209503200800180201c49c40c1d030b0000a1280c2d0315440b0851046000b401d44003036190030140a8060500041018014070409564001418040050321482d0080304003001c070481c048400c1200380620f010041c500d034001d902000001600810100001f00517404030203886441c140100118800400b405008007403d0441c42c400d101d50010202c0826001102d0040c1c4409281c109651540520b400040c03051041c603a140000d0211040e220040b03d2031143c810000b40d031210340503a00c4500543c2c00741e810038007514080c0700642c0a0024442142030261000480510b000b007400c080d603042c5184400040400014000140845050002088400c0d03c0c03e40c615407514010035030380e100f84900b0040f41c0c0d400c45ea1001c4503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 360888866 1250 360887616 360887623
    0x60c0605041e0501200711010807050c100b01141306050307050d112a0d0804080f120703060b07030801051c08042705070509090a06050402041202030d0302120414 71
    0x86220070800c01c0da07100c0355440c000d4000c2c0045c6040003019060383c040001001d800c1030407610b0f140d41c800f10501d5460312050044d10100d4001d00403000303002050108201c2c40a00700031049102881c000c010407100321590001d0081042070107864003100040280084002c01c015880c4229030003483c1040d5a55200e42c000c0382d0a0180201a25500e810211500103406030306002e04486401c00841c046503006150382210f425622515001107500414940c6190901403070b40c540d4410b00450015180c0841c581e06014035030300004d48a04610403080a00104a07810312801010b0004002c9030f52130300c01c0b0760320054406601407080c180700d402d0400850040310f503400c1074403001c580d0120341c440e11203454445445900f08802c0800e040103080c00d1442e441c5226900560340100d02c0c43e12818682a001d00c10f0003161840104000d455a440d488001803688452006100401101043d04140c1c11b0501c10182050045002d6604140c01032001030114840380041c0c94004c6c0d40800c00c0340f681041c440d2035906 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 360890116 1250 360888866 360888893
    0x10e04150204080f0f240103030804230105042f0904020a0509010b070b060f011205040203070f060e1302030c22091802030606010201091101030f0b090103050703050601060207060c060504 82
    0x10307034041c2440c1100042130000e48100c82018203400c1c2c5600f60390440062020403404009071074000000401040485d002d070583c560028096908007010908500301900b1402c048080c12072240e6690f020041408000e080c01c2c071240070582c102000800148810b810501031000c9154429081c0401183c1150384100d844030040070017514008056a42d54035480858000312803c0e50b03007903000030009603d4544454a80d0000805841e0003034080c003007d003210000c0ca8003c0c0220780620070b054010030000c12480d0240c00500c000c0c2c0d40c804c1c54001510a114910081c803241c88800d60040c4140701240b0540c00c16100890404030010030411035812040c640010654419410a81380012402c060400980841c03c1d460003a0100c440c6602c0d100012401c03160081406010105005407840781c942c800c2d04241068850701c00041020070b410b0000680041007a40100c5042d8801442001000018082c0a0042c42c490010340303d982e15003071000e80851110a0700404155071500042c0030050380541110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 360891366 1250 360890116 360890129
    0xc0f0310050405030306150f0304030c230d0201152301121a040c0e01170a060302041a0102010b0916030903140304110f24030c04030206030a06050414010e04150204 72
    0x100900381401c0c800c2e269070040c3d500340e0042c47c644825000224a4000300c9201042441c50140345030b4403514210307104912284211801e10010000b040001c035541101035032a803c0301c0103081c0710340c00d5180280c2140c13020b80f01d0348185442e514040ac065007050020380803882c0100c048002491030400103e4030f0b40c3c0c50200c04040300303140100b00f005400100c090b031b4140c007038150707401c00c80c2080a40060b03552a580e0440e050003c3d4040e44071b04440d450200d003207a0040e09526010510340e03203a82c0060140d845030b1890804143c40c0101000403580d09014101c100300701511221824100032072a4000c808100d2540f9044c5900c030040a000c05100e0740045000030f00c04040f06499041900d040c0030243c0000c0f04903032040b0100d100201e441d181c0341109500e07003e848441c02d07a2400000600c404a608000e0408940810a1000001503210103008500c103030f548410000b5201d00f04004c0108949040e040c400540706190014018041c03010101034006401160000e00030810030b5906000e442540c1092 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 360892616 1250 360891366 360891371
    0x12030c06040605010303020d11100f020910030b1309030f0804081908060909120711030c03010c120f02030c0d0510150201090b13020d02130f1407020d080403020c0f0310 74
    0xc020b2005a07440345041c2e074802d5007075814040c202c13001102c541c801da040c091556000503a441190f501030b40c0c0450021200c04a01604000081000601c004035201c2c1c1080420349410b03c02590745081c00c42081d0044200b0387c104207003c5940c0f40203003110b007900746003c24011280040350611aa003405c1d254603c010302480d044201000100a10f17900701902d41c1d9000301a0350010030000740c0c01040950410180c050340034103100098070307030141e44110b22110302d415006408000301030f5203003030013000a0b040580d1640410070051445090445d03d411821105052052042c000500000800c5138122602850042440d46810650b80680525036010b403850103914070030740c81400d8042d0400e00307480740207505130b0203917540fa941d07480c0032018400002940b05144000d0000113290400103202003c030006400a03250384800e011108854404c412101170703006400c100400c00c0e81c1005211110842c518181c1c805080c5550041d5441842c840b00310310883c50725000c0c03152038508005013100c061800409 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 360893866 1250 360892616 360892621
    0x31308030a020901080708060906010f0504031401020703110102092d040e0d0906030912030504030203042c0c0918060325030302010b060c03040306050604091b0f060e030c12030c06 79
    0x801c0000d40c00301da2154003007412000000d011702c0c001ca0406220303042c00340c00c0c0720596a0b04401150742a00c072400c66001e01805001c0800442d0010300a0703801c51190600060340c1e8041420081c045484041c402003850f0300400680c00c21703850f0920280402003942800380700068040d4405155841c0b2440c006410500c3c107162407161190000d403070210125103032a858a544d48800c07084040c0d60010310060450b2681c0c40c0b84480030f5120303078480b59106001e881a203007050388540490b03941c09200702c0902c82426100f42c00fa140185c040c103110350010f0890100e0b916013403440010500103038000c58130707200c02c0094500003a1070b9201030003507809543d528042e80740c4810144040540110260000758015860040c0303442c40c501f05102103a041030358050065092600e1640ca110142030f0003802c09411a80718120500012a400c00005003c0c91003282d000c0103e040484065200c4020703801042001943d0400030700c241c50101e0200c0c003511040c1d44503c04110305015240c51882181c036440202e100e44c404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 360895116 1250 360893866 360893881
    0x50904240501080a060b0315011b0f020a06050322060f060b0d0e010203070206161707080a0b040203060d0618080c210307050910021e0d12180803130803 67
    0x40303025038400342c035920b032680c8401d0140301c00c4407001d0240707400c3e070841040030136181a850313852840314110524100d20708a2200a441300c0d60340d100601143e28440c0840041c0031894440840005402a45072035800c516000d000c074200d000300c201c16074900101d00649034040c48001d410811440c4103028080c0100c1c1c0c2d80f014210001ea11218181e0b4001c0c0c50b00d841c141e21400c06008890050005600800345522107040700411055800031410500400303003140301001400440042c41aa60ba4683d103c1c5840c1060543c0305076819810f8941c8114410010401c840e600c14640c0040190071880001d10307120b40324074403c090214550f0107444240c02103034510200c030000813040041c9900761183c4030b0b044a6941074580ca40401d84503035000c01d82c20b0018400a041c91410703241c050040b80b049410070f003604450864444c01031504420541c0102e54a0122223400c48554000f850891500704403803800188030a4a110382918001d010582c0003000c11204034401a001c10903a4101400d16913a04082d007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 360896366 1250 360895116 360895181
    0x3020c010e090c0d0e061513090f0201110c0d0b04020907081b0c10180c0801092d140601061103040305100b0118081507050c060106111005150a05150a050904 69
    0x407a1f0720b1040c05200c036501c01d08011401180c505962040b0003001c856007650054819039002c4058902c04d00c030b4454914001da0ba5400e071820007902500100a6608140c0140040c20782b00600e00010f100c003090a1002811856503403015145160f45803507103030141d01c2c00c41410704180300540c030203040c20003240642e00501c80107502c0b44184a00014840b0681e036040c11400e17280640320280000ca407904020401d11840511032038038580c2c044200c803803200280d8400514480d2004d20110a40c0010018000b1030f82140341d1440d080f403034078003c1d070a062850399090b603520038484040c2c1d5440c2d211b802c140e5059003d41c2405044880250280d207202d40c550b0f0029584100f05081c8511152141010548d480d0140e02110800c607590b601618a6a00780700003603600882a013107203000c0e0b200e42e004000b60180c0c070344a020700541f0751200200c503e10300641000050091600900d219000d07044c001d00e20f03070303460b0b10440311840d08a0a046849160020005000340000e00d040c204440340300001101084011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 360897616 1250 360896366 360896401
    0x3090607051803071805011508160e0315040b01060507150e0a0b0138091e061602180c070605070c020406270e0a0b13021206010303020c010e090c0d0e06 67
    0x2000c00c203523a643d11801696141c042c2161010074071117008220240d01480a000072005141061601c0c498004044cd1030001c810648a10540b4440c0500003040b003640ca000b80180314510b0203605183c0207444034110403111b0001c030140d25035222485c0c07445d01014092a8510b540203203541c030f207943c1e4882c00c072607840348140c07900300070100035031015965840340130019000400400c480324100325008045c003641e0a22210354281c0703c1e60f89400040240e42e64001002d031002001e14010000009205020001191b4200c101a028580c0e04200090710f000c0181e400c2c0039040f400201d11919a8181510000041c01c0041d40282c141040800d0400802d40303a8851404d5040050b00344158400c0170404a801745c3e0b9841d55650020402d0300c01260a140d0400c0c1c0051001481e443c41c0d904950007c0c2400c211250452043c0d0080d0f0010028590103018080350007400703007403c1121288003400a40c1d031441c002d001d0640e840001c0b85901001109070f004080c0300f104101141c40500340050542228540c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 360898866 1250 360897616 360897659
    0x20409080c0312100608040b1902040f050102061012021905030604210c0302100218030a050105100b040e01031515030605061507080415050d0603080a0909020309060705180307 77
    0x8503011401c06130a1209160498146031384110b055110f603134401002c5000a401d501e074040c40714002c820214100d00c0103000408086a981e40f5141c900000a403d055004141c07502d20b406000d070800c854a4050344c880b0740140d0484284085011200817004541d81c0b50f0811601881050200420814400b10404201c0e81c6007112081c2d0649818040320364892198000300181c10100c01406038186c075401030702010b00c0000c041394010781c8500100c3d1034040c0d426810341d1641e44500901c03400884120a41c0e0103080340c0c00183d8901801c0c030307004045004040c4030050880c111034100045004983e8001c655070001240b001c02d410760b885c18040b003e410140c402d40c0c45040a038040e4003500c2000d00031101c42903408503082d0708151901c01449180045410310300140002000110106041403207480c02441c4102c81e0251950701d220402400380078281c015881d05071040062240c00c1e1000a141d950004803840c06583d14001300c140c50124004100070160148076000001c1420300c0b892620b801c1d20484e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 360900116 1250 360898866 360898897
    0x60e2d04031206230909010908070605041b0b0f0d0204210203010b0621090a080c011a1503040f1e0c090b06031003140a0b0c0901020d21020304020409080c03 69
    0x440f50950004182d0344c85040e84006600c10198009051017458140e210251800001301981c0710384907844e4070382c000b00d4103d4100b69114104001c000200384246d048550700c2219081842c28200d11030b26030300c60f48026081c1840e0215500d201c2000d581c0407070b0090030070149200540b45501440b41030407001c03444120312035428030080b0485424064183d501040f0030082c641d21060054424207101107004d002c86d80240502e030040404503008500500103907203a000006101a100300d004040301d1245008544240107440e0b80c41c8001d0004815250060b0f0071042401c28560549403030f6012a45085007a41d205100041550038400c80804800c100e038004d06040c044065000c080080364401154442d8286c0d0500c101030010071549401c00342240e1082c822131700821101c0e10344503c40c0300b044500030a04040094245165603050014400b8840c460508080354225845800c0d40c5115181e8034100b2941c0c00300000c0c05560760340c3c12100e01e1581101d1880d69600501c03500c0d0752070b54404040155001c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 360901366 1250 360900116 360900119
    0x1502010b0a0506091809010e01020304031805010207150509030a050708010609060b09030304031e0204050f0121150903030207020d030503010e090a11010e01050c1204080709060e2d04031206 83
    0x401008403104d0701801080108070200300c045401c02400054100c1503550361f035103134000c210182407004502840c001d40b00c0410b500024a0001c2401c103280c1c00150464004910400c000d65814240349020600c5081c00c035100d03030300d0070040380c6400c1c05042d01070414482c40c0d5002600c40019803200d800ea4540900030300c4500e03140d603280c1600d4801e143d0615050381c800c04c0300308041614803445031f2103a409103042c0210907030f1907000035042e524190f440c10b00c428416001000401407019072507c14181000c0300c600c04500c01d45401b402c10004840c07100c261602c44c8074000030540320307030304444440d176004001e042c0d04016030400420a401c02d000d0000d48505510100e0700400700095805200d41c0c3c807002103600d001079100111092600f00030960b0501c801800101c201c0c94060111400135618054036a44a40c90f1094682c0703402c441d640076407441403802101780a009052242e4076030001d0110000c1e00640c40320b882111080d8040200000040c0b540e13820320080652080c103c4182f5a480e20301445441d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 360902616 1250 360901366 360901369
    0x100e0a0c0e460b1c060b3106140c1b210307081b01020a031e140c0717040602030307020d050307020d1d120606040e010905061f1502010b0a05 62
    0x107214003210009202000e80c04000d80b0440d50000c00c55111202d41e42c4040c100c40034180002c1d907080f40c00900320054003094040704c048071481c1f410322040d012842c400101444600d503c0074004140255401c1014a96600701c203240d5803000c0f40c400b000c01104880a000070301d49140395940322911081c2c030841c1012800420000400a1000845880c40140d8a455860303a100040d590015851011a244039201d030064030070b080c40501002040c035100410075444186181c40c1254440d1380c40000d6078a4140b0784d056040300810301550107a007080100340d80c3d4038035003464404090b0686440426400005000ca0703440da0220207140250415001c4400140c41d080058034607010440c1c0180041c0d0165070100d0001d442804140c114804264000f4001c10094011417070f50820300f4600700080e4000010b216036420603214064100c10b0344c200800445440d030362502c1d1102c034050030240a05070302c186031031040003080034400d0040800c0e8269054030501200080e0103400c2c03060040340318040041d40010b09 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 360903866 1250 360902616 360902719
    0x11210d0e03211902010b06040305010c0f0518040b030a0c0f0602060723090a0f0902040303170105010804080c1504030e13050609130305070c060801030b100e0a0c0e 72
    0x442c5107405081d0800c14001da601d1401180c1c400690304541d00d036444403400c0d4594070018000356006800100b4080c0100401402c040784151044003001410021442c880c040e0032201e90001c0d600320b40101d048400d03003000070714100007032002a1403018907203070003c0c441101c0b02d154000c5074070940907219255240b400a0712900d89600c5440284440d20105610920180f00180003440000f02400b03c1213031107104000850140350840f00700030342d00050a200b450742080704030008030801086440290305000000f0a00d00f0064002480c001d03022407040543c0342d0900580f2607184217002c886805203014180280340000d9142c0c1d041c000c12152201c190ba12280d4000c1034803514014105076103a440c0c01c00301c0721040c8031000c41501007043c04e0040c4000600da040207840141015030301c0d52815415030800036108800a81005031f12443c825080120b0021909601e6100250560000702c50b4109203056608065041c6844da120000d0144074458140c545c40e2440c0790040c0d814081180428240d14240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 360905116 1250 360903866 360903913
    0x2205091908070b0c0c070b0d1d030a08070c0f03020a030f0c050c210709020310080f10020f21040c0504090503090d05070b0304030f0f090311210d0e03 66
    0x1e41d0340801c19030001c24218900d00381c000103480036040c03610540c030400c00e080000c40c0d041401030300030000d61006205000d0107407585101442141c00c1005038604411030340e034440c010482c410301c001d0300002141c460103107a20050710307038009800b22070b1062240b40007034035009039420440100d11326220700d8043c0751240440c03040003503111004180300c980c04820001440031344c070004075078030b18100c500c40c200f10401e001c000d000b48034039040540c903400d00f00103d14108403c3e400a400541c4945000c0d214000001150003111541c8240140d644c201486045070740e20414480b00718040010120714242c450b00c0b26094800c40c02000d0101d40c490302c031803c00040cbc031718803400034009900c10b10103000c091501610700411144a202110b0aa9135a400c0112140d00300315019408a03a42c030030720541d080c2d00020340d005001d0325031800107a07050030f554495054000481002e400340b450b201445400b5000b0b14140010f501542040703455003c090305000700b00c41ca9400c0c02e1806070180e03047c4405003a2200b031007680c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 360906366 1250 360905116 360905123
    0x3080f1909030818120a0302070e0a1b0e041506050a030b030115050103052208040f06080f01030f0302010f0501170c0a080c0910120b0901360222050919 67
    0x510b030401c2100c82e00c14010340c01d402070b0361151024080700e00c0745c2020000e08404501c40c4d00a030102c64940420b90014490003000c590402e030030810202c5c8007070030340c441000c4400b09078140b031480100000d000c500100401c00d020311046510020210300303160010090140c4960b80e540070f0103685450810305080c1c0d0205c06101403505415407050100d0b60003a001203521054403403041d03800103411082c89001c08a07804054902420010301800191325203941400988100d040c0b403061400c2c00904405110414807020303081c4090064801c0406100307400c0030900b07585000c024040d40d6180d80185c1c8200900c2c2c41c6c0720000d84640d0b0501c900c40c0c00d269615204447c1201c02034070210442006101d4003100040885030084645040032500309440c030000e11a0714001c04c51480c0d40d180030441c036800c5843c8502c003c101013411242c2ca2000c0c1c4490480c0c48025031b440c1d150412191b80500c0494007003003043d01018852207d00304070f005605e601c0d5001074440c81400b411540455401134262030361054104014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 360907616 1250 360906366 360906383
    0x30f060a020906190306080f0d0c030c080c06100501090501020114011214010c05091c020a0302101b0f0302190c0312050702041b020601140a090b060403080f190903 72
    0x20040c00c5a41d014105500d0007811407454500d4501d0f203e90780d01070102d113807008241c0e00c0000b400803503001c129403c92034200ca0020564007100d580c01400b00d2039071180c000d041004089442e0100a420010380700e03103005403400c031840380c100301c000a0320b801c00c140a1a8000307848840e0000e4207600c14002c103400d000c41011010b45a90811a0700381c0200f000c20070595094202c540c229440c00001d20842c0180422035840d85e456641400400101e1001d52410f4240c00506046d44005a524402110100c4ea811035143c005621503020664814600c1001d2251040d058980310050210b0075100c007081522030303801d894020300440300340f075200c0060780c40c05081e11000704030900001e41c07506103540c4075800b2800c0803420f0490720750008054075500c21250f0911140b0a09076005c3c0f540400c46036000d0113482d500302403c00f645c032021800800c510304c2840c1d00350b61110002d001584824085801a5030002a070030b9071040d80952071505607021000b517210a44500300040301e11481800000256036002d103a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 360908866 1250 360907616 360907621
    0x20f03040b180103110304060b0915063c0c070e010b0f0d0f020319050610050f1614070f05040606090b0705100203091608030c0322050910050906030f06 67
    0x2c49142d09020003820306150b074414078a014802040090f5100314800c1030041001c3d0018000d0007104803000d00403036281800b80003130207200da03549801e4070b180c5e0b02c8a6240e803202010400703035401d98403115030030075400030310380316072888840c04040007040082440c008885501e5a605001c1900b03190034030030340b541000e0901078664600383c003100074500700384925404140703001601c1554089034401d50b032030700f2001e80100c44450150f8103401000e80c8848225148403608520b0030019003a03200703030400d10300d10301c2000a80544034504401c1e4215000c5e0008400c040240001c103a41d0742e01c0445008015100401890000e028a0940584001c0d1501d60341c0c0e48554520b89004801140c2004100f1100e50055450703060702c040702d43c4041c500c1070000000900704e1052681c41500f580c00303d504004895081040348078641c0f00c0c0001100d0a6501126101a000701c04181082c00d002440d04440d41c020038250900000d5510220100152481182c41c0380190b1120001c240c3e039407060880d000a44d8100100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 360910116 1250 360908866 360908887
    0x1050f01050a02030d0609020a0318030206010b07140a08031801060515030910090503190306050a150c0f0b0f1e0f0703020403020d080c150c03040807020d060912020f03040b 76
    0x10b490307039500701d00484e801c1c074504020303c10030749480d0341001c1d4115502085a1012503450b000c2e07811484c06001070780481d141980c07030003511076505004004650000040e007108003e01702c62402d40c103a1214040e01d441c007803030b071501003d84d0b030041d40c40e4405001403844442204006115010407100001c0456401a414468000e20307500010000f111600402500421100300707400740703c20640c404c1c00510355400350050404140102c40d04104201450076078240b00760b0300d850301202d06844000c000c84403c0c81030382004680c2c0c40c4003801d0052004d041c0c500a081048480b2410f1402880c0c0142001300c982c1e90b4680341e001040a030707002e4148000145011810400c0c100d098684c00410500c1c2c05032600c1c0d103a80101d545030f00201e130100c9900d0300c000396104600c40144500c0f106140059244502070503d403a840600d4000030b800130307000440001c1c0400440d0b4480001e007103141e03030080050041600c6420055444086003d100f401340c02030001e0900009000b00442e0f0035220000e0003542456400e10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 360911366 1250 360910116 360910127
    0x3070c020609030607081f0f050f1c0f11060903150601090f06020604060f02030c0403120c1a0f07031e05090c3003070314070f08031006080f01050f01 66
    0x2005a030001000c0110607040d0b2400c0c0180c51041c3d589464038a490b040111265120b55400034105160300039144017800686076190603c01211801c8921110134450b080000f00840403410304103640b134200200c0c800400804c249204000c030300440340e07240444904000d02c400d03442002022641900070b2500e60000061540c207a0b50000010f14104020503200d91149004034816003001000da1b004030b00b04010003072140901c034083c00f0440003d60031070410318621442c5020724003000300807403158145214840d224080da102c52513084150306100383e281c2c5189110600d000d50742141140200c00010303080ba4043d0144011645481c070441c11040341c16492030004120180c14040036000700d0700609560b503156820a080d03410959110300c44c100c0380907100303a6610710380c05800003507400074401c400110381c0121451012a445020603a0b880b803251800c900d04107028100180f50700740100500c1480e44c2a007c0d08400e0b81c000c1e496001c03443d19042d210125400c2d0901c5800d50000d00d100003440954440c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 360912616 1250 360911366 360911387
    0x10f1a09010f050c0c37210501110406120f11160606090207050102041d09150702010b0a08060610030b0d080901050c1b01081303080a02090f031212010f08030307 71
    0x202c280d44244040f6800915288100ca0307110b0306e1400742e4072004001c07903c40342140c40d1003405015206071311032070142410143c8070f0403003a12540c000c0d5500201c06110080d0002c007040c5c020001010360325511804050442e00a284800a0082c5000c980c00510007c62044a00c070b4540d0000040c02c1611000c241d00a91400001c12070704942c0710b8100040e042085d002a00c1d441c2d01c03800002d43c40341d0402e0b00c2c0c0502410748118442605402206120407802c0c04500103014481000d0458100d0b40d030000e046c3e0241141298080d006040c03003274001361481d0007144660082004a400d622a154000d50440558880510050b80b080881c0c5e400c4000070a610300070440340406041c0a4145030040d0f2019080480316151107402c58413a80100f0165030b41301205a0b40040c5031407546040010548000f0440a801002c50341c50300c1d03000501d028260740740c1f030524840140080c00c541c0220500b040c401d0158008569140750324804100204642981c002e807001a6401e4100450a56580000449124410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 360913866 1250 360912616 360912637
    0x10608070903060b010c050102030f04020405100b09010e0a26010c03020c070905130f060b010206070305160e03030415090f0b1e030a060f06021e0f0d0c0203010e06010f1a09010f05 79
    0x185000320300091f000380040c510900306040090210318040c014001650002000382c031406912140c14019444004203446a000b420319001c80381e6041c00010aa603601307940c01130f8116035682d0b008160326040b40f0a80004600d0080c0080c4a00e54a00c14180c0a9004068890300190015003090061902c079030310440e031000d56103100244101c01c0d919210a0000b00c0c803015218517843c0c41d14103c8950b010011650071000502d402c01440c075042c1000701d004803100d08100704210040c10117518580e000c0066a0107029002007009060b4503114000d0019603051142c600300c0b1240d80d00020360084254203541c01e0404500c2c00101d54020031864116580c001001643c0b4195281c05c04030f20700c1126108036018011580003810000015254465243c5c52004007a030700d60b001c003400c0200c0d000c001c13440384c56260341781c1444102d2800350320009014045000507081c2a103d69800054180c00181030b8400301da00380c02c4c2c02001e002849202524920914080f103002c194445200e078020340c40b400040040102 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 360915116 1250 360913866 360913877
    0x60f051b07170a06112104020411160209060d020d170706090804090f060f060509011e210c091502030d0606050409060b04050d1103210d05010608070903060b01 70
    0x8642401164240c1c040d490120b095020345600030070000c062140e13107480c03205090f000b0300380b171204100e081035119030030000903a8070b2a2002190441d02c4030307045510380c14850b4202e00d48030508210030010b118912041a48200c18001c0403601601700100c1d03400c02107801405660ba488019115010800403185013040c101c501044000c3c081000c51003085840b52255200303541d076a00e007090000540d812084038586003441e084c0108071600e80710402c036048504c14103041d9202c009070001030303481794500501c25903202d208141078100d60382d116844152481502c1d2a21803040c8035103641d4000c0f82c00c0c6480c08008100201000d212402400702e03184a4480700d881200d02c4d040f81c7d1070b200416161940d0240c030200d80040740600c42c40e60380e03000303203c040c00ea50403165090070310f000700044200e20040005000310f1140302856986031814404609004000c0396242c0b203070300045451421651010040c09a16807130200089101c43c8510030180c01064195910601c3c941951030f4135004102140d503c505002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 360916366 1250 360915116 360915119
    0x110c0615100e1302221e05010e010e04050903040f0b09010306080d0206150a0305010207050c03010b0609010905090604060e01080a051506031e1e060405010b010806010f12020d0e0105060a060f051b07 87
    0x40b0400d20100180040b00031680406d5040b0b51559880c40050b08201d044c04100d020f181c03442d99015241001c0c04d5411500412a500c1d2284204d0941c40380d81c002c0e0f083c623070030440081105000e0400400c59840c3c2a07904101042d652020992143c041185450058200702c02255010120034240f40e460304005020080440d602d0781ca0500326030225034200c906400c44036a001c401e2400b07105a044c0074400380c0b0502e00e0002101c0009100170f00b17501a0612400d0340c4004600d2540340c0340c0c403010203040c4109207071a5a584034407d59645010000b4212000c0c81031200c4503c02d00c1950010300c0c06198003400034440b09203040400840c00d0001c0301081c0461090345000c0b841425084004003540c03510402402003424207003003250945002c443d0f00c90502c6145024000f003a41d10803548800301c816458804200c00d000300c0801c000c2d12171214224400d60034213100564940065108078010141103902e040314a0b40d921068800003550b20400e00895000d1010b0850a683c200c1c0380590310680d4010b552106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 360917616 1250 360916366 360916417
    0x50c07141e011b0b07090f05010f03020322260906030a050604090819080a140609040c03020a06030204061b020616020415031b0906050a050103110c0615100e1302 71
    0x40400f100c00e580c000c0c0d0100030b20036443c5d0806104805400c891621070011400c1130000307000c0910003089c4004141e070000002e00e80214000003000c6549250458112519a40c1048014894012603411420008129034210040300303004403055880f0141009003140c1d141c08015006010040c0050740242c0ca46801e5000140e903a0010880c031070000d02e00c41204500700d00020100c100090154040c140317088102c000082d11a074845a03c21030440e50031101e5903e07440e0001025030185d00007034100500c401c01046058054001d4402d0b2000c6685000550405088442030310300c05080107034100d00c0c10485000c0503440302803140a00da00107000450941d603155204014406164801e0b55050100400792a10030690b00122000b40000300050109508110000304004c0a901c101c505242d5038400c2110044503450586444038070417802d03501d03203207003941101c00c050700c41c2c549085c8030300400b54484d030f40e40d07004500c040072001000e040901e00ca00b8810000c80254410024420040b0004960b902103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 360918866 1250 360917616 360917657
    0x41a09030d1b03060501030b0d020d05030d0f06060e10080a0f020c03030f0105030105180d18030b1005030106090e1009051e280503030f15040903050c07141e01 70
    0x505403800010b0848441698010f04580b1180c104504050a01d003452000d596040c80e41d0301801e4045030803824a0005207040c61651151204044056042120319400308940394840d1086071040c1d229840d034010042e00304500d014440104001140d108000700c0c550302c201e5488040503804400c3c0040c90020030b224400d01c0c5401c00c84a442030041a10014411400d00307006564201d04d91000b201c3c40c00500038205601c60780920000010800c10113482c0c0d00302960219000000c2d90040d09042160500e051903500d40240b500500d4001c1d03003041400240103807030384506110390320302d40080c0c18881c0014a495014100c0e40300180c03824891a01c00000c1800d240401d4144083d07688020200d4000705107004180d250a498500200803500d1030010100f040401101c0e4400750111207103d40da6680d420001800d54100d582582007842d0203190001c0540010041150395010340c221211a5500c40240d00d220650703400190b08040045030f00703113940c070640405101400050501c50390740940124030402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 360920116 1250 360918866 360918881
    0x1a0d0c02070f030804031101110d12090c09050615040f0b0c010e03040e0a050f040b0c160b010626010b040b0a0908010504060501170c09060607140d08011a03041a09030d 74
    0x50701310000504000300b0115011564400c1820308004204500c2c1c00f081c29122488400c80c0d00620034810a034898080e140e5014071083e030351060b4000d10032900c07041c0c9040204022101a0300904401652000c3c21310303e4400c0d1000c850000300e0405c4054240625600785810405040c06190749504140040002c14000342010744212240404d19182c01d00352a070603280f002d8945c525103400582488089183e17a00302c0d6510200101c40c455903035042c0080346d07a00e1b03103030584046d11600c0040000b280d683c0e803003a0040120030840d210b840c0c01241d80030725010170f51000e1292260241041204100403100303603000e803c07984114105034000c5a520101203007514002c942c2158403c2c0d0351001404000a525824002d100940005000190031800410701000000d4849840b40a01103040c1c0304020011201440c0600034006840412100f16806800501c1c203000380110200702c04903c0c00304140e92000d03a885150081c401c40c04210f17582451400315600075000c6181400104410000d10107039001d041c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 360921366 1250 360920116 360920123
    0x50916090b1807031e0c0e28081e0601210203030d050112021804111c02040f0f060e10030305030c120709050411070c050f040207021203090108011a0d0c02070f03 71
    0x10017421043c20b0a04580c040d00c240c0351001d00d042c0c48000196449101c1440103201610700b41401c0c44681c01144040303010f8856141c0429003100007003507240e4081448940400303c030f08540f4407800012030881d1284000d008410150b00041824400c1c0c0c0c000c21901403169002905603032600c50035040402c240c40c0d00360412110000a10030f54011428004805018007550800108560a00d40e5800f8000c03010035651a114181c100038a401400c140b5101006295004004010800d002652180600145c2c070455164900c3c0100004d80c100038540340510903503c1803440c0180a0a665003a14140c0000d0000403201c581813195442084124104a004540382d8071040061483e0104100c1921490b03210b0603481c6030103001140004107a407404209485003103442e07106030142e0201150090140c07420180d800000b8441d0849000e0703001c4014100600700380d82d180b000e0713a2170303002c0c0703038144500c1c44901520b00d0810042201601410740c00480341808510517100a1581d4400051180e1625041503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 360922616 1250 360921366 360921371
    0x602090a030308152b080c011a040f09030f050a0e041107050f010b011b060e031605060601020102070b06040903090512100f0501120f0c2601050916090b180703 70
    0x8585038099202c026541100c8148550015500d01780180008031002c10304c19a0f60084441004802c038140c030010602c000082100380e00c1509101e0f4038140c000c814a004a140545941403c0498019644c1040c4c064489054580783c3d49011500f0f07510400d0b514041101d104c080d2903030390fa280c1c060701c03040e0510341e40801d4980b651400d00178140024030b040440c20380e260268008180c0d0b0450f05c5422544034141c0380400c00030b494104400038096112450a550100061a80c1c841d9a1482c00e1030406000d0021270f00390b40e03a070b10010781c200d220b4a10042c0004665100081c42c603d001c0d0400340ca10303440b2f03140c07506090303030754001180758800b02210418040e04001c001748c502c0306262142e010080c1500c401884035514103d5440d80d02e4401b90009000211641d120b4018454210100310043c100c80362100210705004580004a0b0300f820741d03150043d4203040100c0c0c0a104009440c0706500d0040f02586119840c0280c080020400c0301d001641000921003810303c0040d2a90500c1e1240b58581c802 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 360923866 1250 360922616 360922621
    0x1109010b070b09011b2607020105090d0305010513020304020607020a06110114060607060924151415130b07110f09130b0705040b0c0d0914130203040602090a030308 72
    0xa002810b030001d061000583c07401d16040400341d0380c82c824046448940c00e00e0072000186616203c0243c80008800340008104024810000c0e8150f100d98494801041540c00507462a20203c1c190b331000e00c0b4850b813200d240300900b0b0074241031354015074000e88000c0c00b143c6000c800740d010402c002002e912000c007080d8803000b07a1020040078042e0f2030f101c00243c2d40c101460301d409000581c0c1800f61880207012140d03140343c0d1004018905200b180481e0a03513030313101041101319143c017015004134800d000c0b00900300e81340061448104103c100e20100e0083c43c0350040c410103c24080150003a21101d40800303001c1400103105041000107009031406075050000700c4480700c06100c44410382c034803914010300369141044481440f6161030011241e21403011940c1c2d4075400d100b1940d0b030146030001c40018400160a10040000045500b600e6201e85c55191000e1754900f4841404080c0740c24a94001e400c2036200d4001142e140e008560003445001c0060400c0d1b50306001c05d01403600c940049001c201050305 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 360925116 1250 360923866 360923873
    0x190f1e06060e060f16060204051519110c040b030102090411090415050d0b0405120a0c0501060e0606040e0408041d0709081c0c03090e16030b03070806040206071109010b07 75
    0x7019881d018040d81c0280c42d28084e4001d482c02c40c07242041c00000204030148040811a041e01143c00610f0010102c40b080c40000310710000e240e102c4004135108403800c0001f800410701608a0162825a20001d02144513090043c4400743c001344501c0d035495542044440601d54662103401140c01c0c0380c4c01e440340c4501c0014148021542c4094103500c91041701d44d02000103a03510440b442c0445d901038219209074440d89490b500d031220000710080c1502011829840b030950003507203403081c00d006100130701c05155106042c0312240300c207884854010000300800d026450f030a9070000c0d001881415402e2910b41c3d2252071420404404140d0918501c0e07072000d102e00180c0c0036401e80080c02c0070002070094003081c0b044142001650f48880010302000c08484410b15015801203001070503900c50a40c0c0601c2d0800140e07049146403030004003c20f280a8401e000c504000860000f40c4950310000d250326200c0b1340030000c803a0031490080780c03103860400500c0c02c1916010308141c004d00600b04c401d07884500c0ca14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 360926366 1250 360925116 360925127
    0xd0e070b030402030d050c070317071e03141b0604060204050a0603140123041401060f090e1b0c19030e01030b0a170c030105040516050108190f1e0606 66
    0x5210314410314040c01404090398000ca220340014a807800c00c0c1e983c40300911521402e01d0659071014241c0300c1c44801c0080c1103410700e00104600c0b0b21614058510010f541c070b104c81c0c0028006030240010ba1082c011300208001e410081000c0b042040c002c1e10a420300c026032524212040b1802c03511344c1d4000c6420406420f15242e0b0501400d0f01341010311111641e03902c0d144180300148a21072005229902d070369100030b40d1550225a040018000b4031a6034503000000030781d10003e00c2120b00142c0d4055a6002c20f500c00c2e0720344000e070f443c0d607807240f02c8541310b1702206c420145105100c00c00c500010010114440c0f42000300303844282100c1c1c1c040f40400071609001c0c0c403040d0600d64150515040114840b00750303491084810564520620307030a120040d500d1404e28080d0444a2903401d0341c07810040c401402400a884000700c1415040e040005407120011a01100283d80748900d80d035410600c90f80722892a04000107007841c04c04005010054551080f4144117000310700c1050a03915081070107a1603012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 360927616 1250 360926366 360926369
    0x6040f0311030315060d02120711190506040210090806040c030c060e18040510020c010504110103090b0103030309081303080d32060411040b0c1504020a03080912030d0e07 75
    0x304090b50551401d000041c0d04080d54500b5584900310001d091800000c03503906480c40940303c08103401081c5042c0202504080d50703140e03003004500c070714601e02110020341c1108444455100300079000544490b400d0002008402d01a002841407041c00401d280d03004001e602e01c200c0c0503005418080b0b01d11704006c00d96034400d40212041000c01924441c9585800c041c01c00c090350005000419030755a420403d08241c03480034004d0b0070b940001400030070700c801500131500590040451812022035600150700711990352030000c014403800320040020070700036030110840e18010301842c0e00c0e1454814001008603101e8000b12950400492010001207841c851110364140d4030021100b141c805150009440002140100010065000040c500c0e21550802c0c8102c0f0141040c0d00d80b07840d151403007040c06402501c041000c83c490056a12400303140b02000b14003858010344a8a000760568585000c25400020701540148400860314030520041000744051451b203a000204070700c00000081c03c28005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 360928866 1250 360927616 360927647
    0x609061204032d0f260106020a03110c010804020603100803070309140a03051e01061805091b150a030213060906021516110f0f0318121203061206040f03 67
    0x3e100c2244034a42c02204052031480e1905054000403034546100740301140300145401c51040d00340001070f440350000780c03003034140d4481c0c0c503000841d00e954601d4503555500703c1c00d814005000d4030041005824050000d5800c0700600034006000398407806400d1035640301d003d04400082c880d034020001d400780c03000c402c0011041110b11100340d03031542d01c40c40d5540c800050003d0341d41c0850a0380c2c02a000d403d521160090002e100039508030150440032200a15003142c2c03040302d41c000c8000d1358a014054800380311802c58000e0080c1041d114486c0c11845540103d03c4032024591b080060203200c0b503084400c00c005100d1a501c80b0390316404c110000341090142e00f445003030741d4104028400c0c88109071051319811005490f0640f040d251800010703182c000c121003070051502500d00d0712019854084000c100c1d00c6001c58490311024040018043d04075400341c0d484065800101d812030900003000015504408000e00401100d009445c039a420b019043c0e4040740d2082c1104032440400d0381000810440c2d495 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 360930116 1250 360928866 360928937
    0xf06050a020c100b0f12010509010c020d051603050706050f0405280b04030215100509060d02301905010b0f010c0308040203030403060f09050c040218060906120403 72
    0x8440070b20a40d0350306103980c501650303600c1d2504002a0b40b00e100041c0c528003c0280310303c50340d0081d0f00d0007070f0007460103581c982c540754207121007001d025000080f00300b108212562491700e40000c2e80c0d100410394864034012010084c0c20400e2001060383c0340200f0f8059400f14907034600b54281454400c0c0303020100c0015400e803003880e54140349440071030000c03920500c0c2c001180e0310159445107000c904098480900607039034056030062000400a0f4031000081c3c2c2d070140c0305100251540700401c0390000410304002e50101d000c0c046244007540c582032030501910f030680c0b1171072182491808070703003040b0034051304801205604241da4288802405940c05208060b11190901c1c05107a0000702007105006001e41446501c07400700301151001c00840d0f00031500440c08004011540e00e907180913259031103003a00d0511805c051000c06140034822034a81c1d1441c80640304070104803200f80034240c1c00102105078403210601c00f00300e10b0ba2250300c507984102d11956414009a0800e140380329a02101d050f40207200c80b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 360931366 1250 360930116 360930127
    0x702030912010c030c0f0903110a050d03050a180b0304082a010e0c18181513110306090318010905040c08100b09010e060d180c050a09020c0a03051c05040f06050a02 72
    0x16005040d00c4113498009c024808810f2103580451868025540581c1d04210b07151045414107501c50040c0240c00d10f603980e8905400d1a0701d0b9902264100d41c014011710320800c001280005240c2e400600b0b0020310301240008104050124810382161488000e000e079458518145600c1c4081c020502e404500311800c20310002c9400241440d1000104420f020080075014040407060030080c0c87c40c92140301e25a600b20f850b0080100c1720441c1c0f403150407110494501743d900c01e1351501141c502d1140724440021170800350030365a0311003110751250310141402110b42011030740740c0385e90007440418566038850b1401c07410025028003204070140c0c04100c91207001e0024120756070b40107000f0200328908692271901c540301406008018040f5078402c6000c492500318030780410111114003070480e041100e445070050f41c1c4d400a00203a100d260f1150300950092032004001070301410240484814891200b01d020000e4500c40e82280c04c252000d5441c085030b20f00300010401a8050154000c12202095082c070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 360932616 1250 360931366 360931397
    0xa0f030b181603060f0b2b0c08090316030e0a03020a150801080f03090907051c061404060614030a20090a050a060c02090a02090618040b030a08030703050702030912010c030c 76
    0x580381e50107104486940040c081d00002580c2000611758403051584187e1001c0c00c007944402410001880c1e000b2030858800244c1c820008070548201000750012201d521002d82c0d0105c49c02442c21030529070084440401002603141c424045010b40a00c60a450b80d1004062014111720416407040c02994404d0b0417085031020f002c0292002e4ac001502c2556603503c5014056501d80503145012002c2d03a4a101c507a031a21300960020411034101c110315090340c211174404d1006440b00342c059400411003504070382d440f245070303280110b50025407450006480c905030720b098100b140d004c1888042680d400301e010a0140762501c01d01c4014541119401c102500d0400007400f062400d10000c0c1c03149a00c10001202d2140c190100e45503200014285561a01c050800114500c0b04071030481c05149411941040307424000392001001d07422003141803c656070a0001c5015001c02004042103010078031a030070b980d403140802030043c024080004600307400850b9009040303c00001101d802c0002c2c4035411142d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 360933866 1250 360932616 360932639
    0xa03111c05181c0f0605070509030705060d0213032103090b06010f0e1f03050604060e060d03020a0605040b180105010b0a1431080d02030a0f030b18160306 68
    0x1c000c0401400150780b125407000401d84806010705107200310700700a2910400800d1084080141e00c00d1008000c0c50b19201021500c1d40903803111550550302c40b82e020300c030784d142410141c00400b80d04a400b40c0b501c2e52405034040c0d00001035000706d5000000100c2c0c80e080302004910386100805500d1b0420a100d40c036100c104461f680905601d05118a04400c2036a1601c10341480a0800c0f0140401003c2d2800e00120585801c040d00c2c82c100081c030307240215405103018014801103451450301803240d52980710400000c40314800e0210305600c01c942c40080000c14070300400b8461401158000300501d041d070390740c01b1045880403500c5083d0340b400b401442841d0b0300c80f094400c2c1e85101d01d0070b07918051032070707907400110320400c03258680c6079055034040132135152218500d00900c6980c0c050039440b00c2d520740f1ba555481c80d4a26550700907030024090004103520910580c001c00081d07140118120f000000461040b4003c50018000d9415450801ca80c40d46045442c0c2500e405510b41009030520b0000c0a40382c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 360935116 1250 360933866 360933877
    0x10212031509150409030203040609060c05030a0f0c0b13020f12071701020d060b040f120302120d18030f0207290708040f08010608070b180d0804080a03111c05 70
    0xc42d6561401194064035401c2003800c00e140301a0040040540d40d080c040c2d41d94103e4450807000885040c404503480b0300c9142a21003841e405001507041c50700c40e60302a02c0c070409548402d020081c02ca100340000c2041c030904030703024101080c40c2c001071042c41d006101c803d0711451000b6006400401a030030030100300045440c08c4400b03010500103818082100e840c068810f83c0040f0f4000340c1040c1e0081038021500c03000300101c038000c2d5040241913594014082100c42c000d0030181c0542c028180341c00350042c02c48000c002c029410703140064242d01c3e4000038403112590a03020b400240141c4040401640c04000003801740403c04a00140022107001c1c0300f64250040000703200d40800403401c041000910400d0b40c001d07100d607040606a41e91a18125070003000c0a1003030b43e030a4455060001081640303c8100c0d100b00305001070110001d05202c0034040401c48445d01210030401c10040000e1b0b01c00240325003102d45100703540d45442080c2054010740340c400c1801c1e182044900c403110040f60f15802104481 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 360936366 1250 360935116 360935119
    0x80c04110a0309030e1009080f061608060307030606030f020906031614040207050643050c0703061d06060405070203120a140f0702010e1c0e03010b1207050102120315 73
    0xa2600702c140390443d40601c4017694550070114614402c03003403e1300722401e1415203250383c040341c008100c611000c0c1c3e6280300541d6104200e911421a0785a40b80c4a011500ea12030310140407100c880d90f9a507102c600711a0a64001d50f94030768100700c40343c00c500d400001c49400c400118003c2c00da840c0c5114580c0440001c0d44a40084000740110182c0240c445d9010b44030182e8210701510041e18003000d05114030f40c010040c8041400390300c400010b09802d0790300c80c4800711100149044400c50303404415129503009954000c81c03885130480010018405001b000807808250305920501da12009103945460030150003d07110381e05003801c202c0ca0342d0340001901c0503800c201422441075182e03050720304018000001c2244005071701200b0010031288140b64580079040a84c02040f120001403800b0340c5400c2e1a44050700302a540444103515280301d40d46140b50a5070003000010b01d810040f00180d40111017082d00001a04040301c2003109d980c043c04500c0c1103c0c882400207107140b51203035000e141e1002c0c0c610448d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 360937616 1250 360936366 360936371
    0xd03090b060d03180801050105030610061713051f0e0a020607170f040603022a0c060d0f240608190c03141306150503031b01091209080c04110a03 64
    0x744281440f0760186041100c0304c4003800358031034555881601a10003405a9400f9209003000f040082103154880012100d1595882e6698035a402400e10a0b10300601100342074070b5140d040e40045002802881d8040340d22451049015003c07a0015080d41c0103518451025040007071440d026807120b0f402c07105041e44c001c842c400b15201c00c5d10807036520f000d2190b0702c030900c000114000c01c800380c2540c02082015203440e80ea40e0081014501d01c401d00307092034220022504400c840030000d041c400c0c0904101109200003141401d00c5401d01000c03900001d2442c00306101c07444094540b040c21762165006028585050410740c0790400410145000b00d65090140ca03507600d1720000030301d02c241d00403084146101c091074000d08000100c640c20941159007903030030600c2c2c15076000444506040e20401c4440c042c2c095818804040000808282000390345034a81d500c401181e00041c028484800e00842191900c900c2d071030510302a00d160101301010300d40101e181500c40d140f032108110030b85900c4015480d01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 360938866 1250 360937616 360937639
    0x1c0f09032c090c0f16030306050405190f0b030f030910170106110a0609150b03071a25080304110307030c03110118260c180411030a140d03090b06 64
    0x12019140314540d00110480c0d0f000c42c0c0d1402c00c811841c11203445d58013950302401070b10340301e80411040300c50035210b16203144d42141401204210603041084540c0f081440010b0000001001c00c1c205603030300f03013600d030701d50400a540311f0149000002c01c003840384075141c4500ca00c0c0303100c005902e8848060144106101d083c081c40000018104604001315500000a000b03100c95803502a5882c542d00002c000700b5820003031400c0560030005400340403603812120380302d80007403500100001d503400450802034950041c10842a26003807204189c0fa180c0c4078901856a07441c16080c03042241d0046408240f10790004642040401d581052030002d403a0400b115008448003040180d4406c490704180d140c100072004000513480d40361101800001d10503580b110710702c01442c000a80c580190f600c001d9444584900100c01c175410003100329921a20649080540d5444440001d2402e02440f204541803110b248422005813414081d41c0b864401d581018459085c090f500c00900900003000300e0301510358600e8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 360940116 1250 360938866 360938881
    0x1031514150f041205152a09040c020a0b01080f0705012007080106090f02030c16022707110a02100807020c060f030403140315061c0f09032c09 63
    0x1164005030b030341052299200e665140380001c000c0001010f6401c2d002c1c65600007003440b4244075803031140b4038010103140c0080d03802112002d03c10941204201d0200d041c0404103c940b0b85110f9081c00303294580007001c26030001d00e0302c95090321058010000c680c103c02c0750012020400034440e400c1e41c00909199900362401c0040085040e9100c1000c4458440ca280c009018803042d403280080d6440f00400340724003071046154205074071040d5411408907208020403405802e10362036086006200400ca480001c00c4403c00c501d400d05650410448884594184924240c01803c261254031801000c0e0903e0a01ca80001d040c00c00403078421424031001c1000100424807d0080c400b1084004010380d88944144110345220f8004035030032404501000c00e20440b25031902c0680c0d10a040440070001416804030a01c03030305800650742d20b0300400808020300c170204038030300602c6482e03524800000740000b0320307080040450348900086108682410b0407501c0d01c0b81c06000d015003501701610011240d4a5451 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 360941366 1250 360940116 360940159
    0x706050702010c0218091c091514030703050603060106032d110c01140a02030903250b01080a0c09050c09012d09170c0d061d070b070201031514 63
    0x200d0007540324005000c1c00005d141180394060090361110100d4003003a440340c080b180c20b908450380c5100410b50303646040100d151600301650b24100b640ca0f180c00400c12600c81090507400076541003000c2030301d4504208480c1010001e040c01002d01d4a002e01030310b07107407008103a000410407000708600449003400d194000c1170380c0c010b807000d86000d440c4580c5c1c41d0700c0c0f0315001d4001c0c4a84901c907113021810070b02088003007204d40280e0740036109850240d85403400880c81b0009240420208240705000c0010080208040d903403958000c10f0000c003e0728200841d403514162120302500000000b0340b91000b48414100107034141d03041310301b0a00301100032090b004440d940c0c1414800500d403d0341d0442c040071194541c00100d100c110355000000360703003024505489a8840220300c10a03038008552a5040c001309038a40c02841c940c0c0c82950b0203001c040300a83c071140c1002c00f160050496480c00048903c11542d1600c5400b048801d100340d040c10721410503288841805103507072050b00c1503088818040c4905480c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 360942616 1250 360941366 360941387
    0xa09062a1817210c0712020306010b03040515070504080c0d0b0a020f0412030201020903070b0406120b061b0106060e04020915071a10171b04020a0201180501090c080d02070605070201 80
    0x40c803c6500762203405180d00c0180d0b0040404407443d000d1100c000420015400100b4445039000b00546040c5e800e005d440c2c142500b0080040e280d80c8600014006003007101d880c41c0e40070380403070b030303205551503080003d41d503e070450a100f8940103c40100c00c00000c42d510380c2031941c019880510141e5641064203a800150080b40c0061403948403800b440010107405500800300b14006a0039500c0481d551200c0c60101d02903882404081000d40038a40040e84040e4002c985031500244010705200200d4507038045408201e00d010103680d95018140300c1d40f90070a01210180d2022038055280801c0b20011500c074552500300704a08a001140e20420440014010a413020030120001e47c1c6140ca04105900c1c05101e04c148250501c404131008901440400d8070410000b1b40351001043e0600b2300d0a01001b0340c03000c3c0016085541c1d0362a800108905d03800781c6441d4500810000c582c600282c01c118501030701c1c1d030380300b1a031a030b202c80e803100c03072003600495650100c45580c2040358682d8014001610401c034034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 360943866 1250 360942616 360942643
    0xa08040b07141209040b010915030e0c030f0304050d02011b080706051e071d06041701060801061508042907021209180a09062a1817 58
    0x41804248620050040d00c801e50041000440c00410740400d69250341d51500703030581110080103009502d0a0035000035900381d00614015860326030301c01d01d40540e000030007841d800084d107400540d810160200010f48000c403088006e041c802e0b81c200312441c0c0d00e1046210f40c0c3d000350003100080007907a01440d031040706c1504100114085289601d0225503030303400040b0440d44e0b40c1c68031012070070304118486a04d40703410040c605901c4030340343d544c0d041e582c01148444c10706200c0c0c4000149100340d251000a400142a644000031640300582e40b0a829509581c0010a0603071400104101d40f0b40000d500402010190030910380c151558100180160918854500a40d01c0005054070320249101c602d80315071003503802d0b070388950310f56289517060340300d104502c40d8043c0700c000d02002981c0c980c2070601d81020080b000080c2d1200c03982da6400542c2c000c1440c042c11940c2000c07011050142c0c000c5004900e031410303d03013181080c0c580121080302a0b8940940b004d44080091280543c400800003010307010314 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 360945116 1250 360943866 360943883
    0x31c1404090e0703120801050906042d020c060c0c06041403070206040b122505160c0e0619030c1412010e1e01061404051e07021e030c120c0a 62
    0x1a00c20b0010360702d0401e884122004403002c0681c182551295000c5416904010038500d91900c8500410000e013100d00ca00f00c04240d10280c98101031440c5070b8107009004030060b03001d602d0365080b0b4010340c14070704018080c204d40b1900300201240c800c0b003c0342d110b501507844041d0003520030701c41e08054514040c11400a40102c000034011542c3d0040c500900f500c024491400441075441d400052140c010100728201c041c00707002012031855002d24003604c04120f0090080c04071070710f640c0b10100c40d620030741d00c511005250035050000d01d041c48182400d0880c890b007c07140c1e401d455544c2d0720001d03440034440d9895040102180e03000b10740d5041c519401002403000240304040810101c0c64071000d00d00116081c032001011403440c050418000c0700203c4d509030ba020212401701000b40300103130800800814510035204840f00100d0200c2c13014038042e50b00360340146801704914424a02c080784200c400c1815a00500142d400f8860010b14207180b00080780040d0745170115156035902d841d040d03560003024405e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 360946366 1250 360945116 360945131
    0x60907051b0a0b1501030e0a060507020309060f07030206010509040f02040b01111c030605040b0109031209080304090509150f1611010e03030a110c0709180606150806031c140409 78
    0x640440f042d0240b800d40410340c0c4107444d180c0042d012900300c090613031036680080d036030310012405603448558807501030300599143c1389400001407030320b42c400248000c0750003010610009041d8104012409410190f4012110341000c0c2c61320604c240d0f40200091003562164048603c90340700d41c10b905041e0521404407490035120200e60405e5010f122030341400280b03000b0b800591071805004100302d4102c180c54000c2d9181c01d584980750910b0301840304c02c040c402c1801d80003a00010803c000c00040480303041c0002c05043c0b4120702e1b403c012508c031440740010441418040141015555641c014503420b00f07469422802c200190384040502c60291003551030101000741c0c0100120080d4811002c40304200324810440380e112500780580c52040c1800c1e404000c080c4000241a840a02190070941d4040d09181c0b00385e44587c15641c1c541c0010b00922804d42000c021a90010328207600560202d014000c04181c0c181c3c0d02110410b41041e80c8100030842c1100c49003800020222000f6107414901440301a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 360947616 1250 360946366 360946373
    0x201020f0c0d0809070b070b09010204120b01094d030106030603031211220e100518060603060402070606090e0706080c0a4e14060907051b0a 62
    0x4102400b07680e40803d001100182d0349580c04514101614107065606060585c262100703017581100400d4618159420030000c00c0034040000104038141c402c20b0080d4140d8105170520741511003080032806c4031001c10040c007000f00f5441810f4150115014050817810500944503248640d05420000888500000116003e64160895800d0364047e4403015207281202c0c42d02000c13110481c4d0f202c884810140842e000490700c0d00c0c4240c0c42a003448052044154840f81c0d400e4045d0026030b0b080008002e0000b080015080213440e00b5015410108001d529141c1a80490114840204140d02c942d0703000555030100200341d4080f4020b0030b07110100300100b2049444c0a65910250700504000c51090130015600004010807607214058503070b40c4006910403280c070640220042c2c9140b4404140c5019050382c05001c40e6064118800e105044440c0044900045002c499070705180c1d817030422580042280540b03030704e8405600030300036140255490880d0308050103940606402c01103070703000314210350090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 360948866 1250 360947616 360947623
    0xd0f050a0c09050609310510060e01030b0a0b030705040b04030804030512070f08030601091503050712090215030406060b04030308090114041e0c08161e03020604090c0201020f0c 78
    0x4503401c42d110401080d486004006940c01909202035018080c100c80050032000d01c010044484039120280140134401004c817001e8580403141400019507901c4100308003a403120100352681001c0c2810030086000b0b1000c25030781503482c0124202c41c0070010208950601c46c0e0200c500900024400039210798491610010590041c40243e0b40d5200705100c0070955004841100c014540c40220740c14009245d0350380d00d0350303504014440e905100c02c40380f0019410301d810a00301d820031442c2d50001118540400c000e00f80f0000d501c0403c0304d42d850040028016152440d882c601c200c0d294880c40d49984d107900d802d201a02c07158005003907000c00450000300b0540c00c802140e01a00c20000240841540b41c0030103043c100c01201d000c0c000c0410480300b500b03030f00e045c0c1c42200300300c40c000e150210b40c0a40746d0340300c02c0c44c1114038864140b01c0062164200403000d1000043c00d00e104140c0700103144249150001140750090780a5400350954417000145881d000358100c1d00500c0d081640317181c640111a910648 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 360950116 1250 360948866 360948881
    0x40b04180b060f1606020d0603060b01090b13060c021903030203031e040312020a0c02091306060b0a2304080a081c051b07051e0607021e03070204020d0f050a 69
    0x180941818030910091602c802034801500700c3e60f904905000241d40c1030046a21150015912607600f0000000303111003601901c00514015000814818034880c0010720450407580141c5200701c080c40300e820544100c00c061001c40c1c840f441d20f4841d005035400001c2e508284a07c1d0303414401e905400c004105900400070358490070b603010003c403504100085d84000100101c0740100040d20300c12034440c0c407210650140101c512285401e0700c40700c00c140e0100d169a00251a402e2040044240c2d2000b0002036014010141100c02030703d41c03d00c1407100001d459015806680010300c0382804000f880c400b045000ea03002010548222559085c150603d80ca89034003101c9655200e034002014100001d555004075405502d20000721203001b210403900403441e4002900868243c007440d46100410f2400c00c0b480c074440401c805c05031245080c41080030b46000351250311101443d4000f6041261031401009503900310341c041d070b400359641c22070660400060525081c24202c42c2e1411051100e07200f0654417000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 360951366 1250 360950116 360950159
    0x30106030c110a0c050904030c0203120309010c051908040201170c03071b03020601060516080408030a0f020d020a021306050607030e0102070f0e0c070305040312030905072711040b04 80
    0x40401559103030740c0c0c3c2c41d0703509520050000700c51000708200c40d04120900030340c030601914040782c0349043d560000b810b000315000314840c00040482401400c481c203104420960030b03242001c070325260350212142640b90007021303000280102040010156400344958600100081d42026071515089000046640007030700e0303034000110070a05001c54001c1100c20085400d80540003400944e103072900484041d80102c050951550000c0e41d90740004806101030300c0646038035000395484140b030003030003082c1500360304403c400c650010088070701c02600410b0074818260190340300001880c81800d58405050644e015641143c000030341c80d001c0c164041b50142d039540c800d80c00d4801043e5110307120b00da01542c6000780c0320441c0ac04404111031480031001044428131034240305040070755035103400c00c645c0700341900f00000ca51200c110f1010444248204c01c09007084022004507904001209130400c0e50202c0c0810640f9914803980001c84004800d80d0300034100911880e603143e0710340403160b10742c0c0309011120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 360952616 1250 360951366 360951377
    0x51503060421080c09150f070507090f021c0213170303060907030c0e04090c030b0f1b040b0a2d03060e0108030403030e0105030a0b060706230c030105040b15030106030c 74
    0x21aa80e6210710001c0d402941c954488a060411032420070820740c00c03190f141c0e86d4080003004000c0111010718068480c05002e04050321400d13103000c03480402e8444c03039050114010303c1040000301c10303440103159840c1161024801a103134808d5101240700c0b010150010103005100100d500090400000118482d0f881624a1b81e40c0d40ca0b46081503003590443c8809101044140b11001c5203400c0c44d80c00301d001c607402002c000e440180c3e2503c80d5241c8e48015180e00c101440c840041014001e0007848407044008840702c882d00e000c0c0b07042001003160103804020010003400c45e4000c0113201420444170106141e1b0788001d004071200c600301a00501c020f1103810010300d0301100000b030b1180080191400c8030f0b01501ea9010038111400111140d44c0010071082845545a5100c1402d40302d045c050318001784500000078156800c0f5a400f52818200c09151401d9042201008041904c0206503411a0780030341d00412945400c1c00001c0750024803181080040002000002c6d8450303254000011204050311070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 360953866 1250 360952616 360952673
    0x2a0c090c08060a120204020f03010602061b030c070f0212060a0c1d060406050a02030c0d170619050f03010e0f0105010302090903030408030f2e090501270515030604 72
    0x7a500141e04661180d8000c3c02c60304100410b4000103208004544018001454481c15613611401a04280c1120700141c0c85801005101d841255500b10039a10800b11181586002a18103a47e8821400c0085c411890a8042d00840d101d0030b101c40c2c0034908900c10b880c080e10f40132902c5001003030560503400009107407060460050340b0140d1004150300c40500500c0c40c00381000350a46c1e8a0348054501803c40c0310400c844001c2714424031040311480b1444d030f5410350066030420b42503900350026240b64425044030580392440c2c4d48004a401c00c6a10545510601074955400680140f050403100c0e0950300401a42920354241035011906803442281e01d00160b4803440c0209170ba0b4002100c00030840d4004001041206000c4c2e1019036204080d500504448419403021951940340102c1003049040403035000d00c01c5071064040c04d03014000714913500c2140a908803580e0002d040f080751031060165540c000c5510100201084280e254002e0f003254403030700700361400310b94007902d41180910000380c0440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 360955116 1250 360953866 360953891
    0x5010515040e0a11010c021206040318061b060f020a0905030d050702060d0216080408030d05070203090307170109021c0309091107110a080f0c0405130f032a0c09 71
    0x4010700040690010f112582c0f440d5500c58003034100110b19410b002c2c001200b0700040c0d561891001c0c1408d000b00c0503092500702440c0140170511840c0f8505010001490103000307032948440c148002240d02415020003020b81e003080401009001c1c081e50480780006101e20318203401164500c2100c0080c0d0845480c030442d4030b0111100d00031040005d40c858400c00c00102e40307100b143c002e05030407074407114035200355002030340c0343c1e59a80e02030b51081105030008030704625203125501c10a9840715090002c0c500e040321000000c0e888030018095604e6a505410150510707603000d42c4003002050307018020130300fa0503038410441d25087e901c0d5070407000248091800b049800a50061380084245411541e0030800c00d941c0b043c104503042080690410150800000c818a040059442e2000c02002070464414680180000d659008243c1184492820003c000140e1101450044145c05151035200918600c0714442c410812240d100da000340e0302d2155a0602c404c040b182d00071600360000400c22100c0208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 360956366 1250 360955116 360955121
    0x5030c030f0705010522090b0f0f06030a0f0b100c021009120b060d17042d090c050403051501050f0d0210031d060f1b030f190b0402070501051504 64
    0x81c41c25429002400100403550041c405072420ba40481c1c0400c54541806240980758280c51b0302c5500710701d4888009100c1420f0044c041141c9503015030785c83c00c0c1c0725130b15000310300c01e880050104802250781d11203122940b030196000e29100500100554800c01881c08014403030308507518181e101311502d060b1840c036103000701c810000b2100d0482066003803c5841c0c80c2c00780028801801d868111103170008150001c1c2e83c00204a01c8849090707051511541018050080704444c1208030030030702c07005204036070491200501c040469100180c0411a800c24482c00c607200c0c01076a00007000b9104441140d0702080c04942150f040e501c0584502c25802c0d1404100311a14020b04006500200107010480343d1a109402ca07540103420480a0544001b100d10743c580f0f804411100392113071215005c01e1100d1541000b62443d142904d0309900c1c5e086040c0032641c0140001c01408108042130002e41651281c10700760060030f1000c4000784111348445d42c9091040c081c01c001c46030141582114040c8501916251 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 360957616 1250 360956366 360956383
    0xc01090b0711061302012a060905070b0405090a02030402010903020901030f06180f030f030209190806010501080907090905100207060c02010c050c10050a0905121b03070b0f0709081605030c03 84
    0xc00e280c104d80ca5503400540e030069040035410b008035003016115580c0d610f006510030405200e9600000c5103041c5041136401e0140a03040501404c0701040b08000c240d40300724601c0e0700a0b581840040e640d840358401654001c2c4940c0c0001d400451701d800000510200789060901540200030522030038550340c810305032040d01070303e00400b82c100001a10b4080ba22074280d44545650604005245c91041000074052094803200180307400d19038403061090040a01803a8010402801c103440141042e000d01510b44e00140204007581c0d0b41c46482506200c0e040041c4032550500060440d510741c02030502070091710b03011080c5d1000d90b00304881e600400d4031605c21102d481307441c0c0002c0d04800005401240103040041c0116400c991581c0d900404a40c0c280f10551240c0c81c05004c4030341c7d41c00c4100b403110050215004125854005010324070220703a0848415a0100c07080104072010399440b6030039180d01d815500f2100e90342c4201102e0650351078281e0041e83c203549080b002c561106012200301903441c03110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 360958866 1250 360957616 360957631
    0x1c030f050f28051f080d05090d0c0909120e0306100618030206040e01080d03200c030d060807181b18080f1f09120f050c01090b071106 59
    0x500149074042221981001c100000c1000560784050140042c00e0b201e0a5828851400c0c107101001340703291114600d0760040c029080030b0110a003441c00084d10b140140c0740f0316802a00000000c000b0011514500005030503071110811441c9241d060098000082e12020804569441d6490b040c0380340001e4101d20890381190700300c4849051440844d180b00c05000b078071413001c82c400004401651400c01400c00303480103290203049580f400c0d086514141c10442d40809061a090520301524210421007819071400099180c2d50300c0e1501c0041c0c07462099102c1c0595561612a0100368010003059082c1184c00712201031440d44100e0144500325129031150140b010309050009815034015500d900300e018030b41d41c42612103903841c0c0c0e4242c20440042465001600840107228640c00c48202203d8001400c01c030802c02115165110400004025901700600411405008951348510300310b928a054800091061550340d01d06118081c405542c680040b40200c440321240c0800011510721031040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 360960116 1250 360958866 360958891
    0xb060409020906061e0d02070c061103040311010c0605041a1501050d0e0a080c010e19030e01270e180f0d0e012313090b100503090c031c030f05 63
    0x110801004a5580310340441c1c07003000120304411659081080c007909403803846c40700150b03a41c151454050720005240d0000320074846110312101a048000041d5020740e584249a00310002541c001610300c1205014020308041c00c0604000801130480d00c0c140c01413504800c9812592601d0048010305001c0c40d44080c00141c00748050502034031542c10852941d00000240c5aa4244c15102e80016512000741c003280d582d11120785140440003000f103400341c0f5090b128044000802c90790010040c80a54030780c1030421160f49042940200d241400e282450900340002c2e81082d628002060304501c102c508400d14008114a41510f110100c2c00e0740702c2150103006810800d102c04001d40d80700c0b81c2401c1c070700c1c100b00d00c00b583c071001004103040c20741c3e04a80610040340c40382a00103912680045130b03004124814108042d101305500c400700507000c0c7d540a42060780d280d41d150b0352540e20306042d40f6613555040c45040d00003d01120002011900301480d039605010300c00003907549a0035508207071501c9200ea40d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 360961366 1250 360960116 360960121
    0x90a02121005220906090b070914101809020d0b0a09060b070f0614071106130b06040903030e0102030c0406080903040b0a140c0706180f12020d05120d05040b0604090209 74
    0xc083c0c0f01d2105251075800014515510740f140401c41d1a00c00084580380480750900c01c2c1d043c1c00102c104d004118418029060424001c08070f218440414004814080f000c40b44890b241c01e00c00b0a10060020104115110019000308101412a4a9255004046248021841120a0044d101656418900245800c0d100d6483c80e10411202c0002c1c3d48850391001166a001054110749000d1441c1c1c1d99000310401646100360f0410201801003800344048021240004101c10b58480e0720038170484002620050506003607025002c2107522200d1544004100300c5e441642038040c1060703e00d1507135883c040707954042003940d580c400c5004e1a500d0120a000d5060b030b00c1e00c18504d401d4801e613081003460805003030740290352a05415401c0800415030b104c854201d080e000700c042400500708040c00c008541d14251080c20109064030019008480340c0e9900010b000f010026508480c441442d02c5a0701c1610742c8102c40140000d030340494003215010701083e1035107010b0044064094009080c082c194 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 360962616 1250 360961366 360961399
    0x60b0717030603100e030d0c020d090311010903051f050106020a0f0803130501020a0905120c150a050c07080a0203010f0506010503070e0f060c03070218010608160e090a02121005 78
    0x2504014900e40d4548200c113280f0089805500070715020602c3c060046807640e95540301c41041d1140c000316041150b004c03103034000750b031580305484c401181d4202810f007401c00d03440360040f205450310741c01c003402c940720740090b118000e0300721a41303030200c07000b44041007041740d07240e0400b2038850805800140000c04110b04c030a0200305464000d44d0055110f2075a0060365501d5690306017a40c00c241c500f8004299148410042820310501d450000e55000340901121351943d4009903840c1d0070506a022521404505100d03582d024004503410814000100c84640756160f1100c1d43c1c608512804070b029500701041488141e1040c010f05006910507118141544c0d40e0307110442e18a8540c01d4002d6000402880400756915404018104180c114020319a140c0391401400f0381c02140248255480c0341d1080104a80c0d40c0c0244059002101d04c0c1c0c8a04d032350207048400b1110200381d0f0a13081d9210b90502c05025500f0b8440d40240400c010644c888241c0c0c6c0c1da040e626041004403031107400d400241d1042c0f0311049 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 360963866 1250 360962616 360962663
    0x9090c0a0c121b2006090a090e01090516031104051005100215011503110c0705010c0c0f060c0302010c1d1903061d0601090603080f070204090f0503030a060b07 70
    0x803410758503120410f601e0140b101c1c004440304070000e0b00c0000044440f95510b24448074100c19002c802d41e1541d00d403103c2d940105183c02418410000b060343d40340c0d409105400e003074002d100c2490f0010100c032500d1281030880c01343d5000601c011100f4071107100303400b181030a05006841c4500740c4c40303590b06600351904050148442c400c0c84018210302440e2007a00126905c96007240c068000b00c40c036514190020a0064111418031381900f20f401c0c6e0900000902450001c0c130402507032000c0c079000c5a4501c4619141c0d50445181e0050f9544001549000c00d40f660711107003503004d65001e13500a015191b0030100a0312103240d0400c100c00403840300440908242000c054442090340400810b02d806566500c4600031a401255492244140c0464004904200300a00340c05040e00c46801c1020b0b510b190340300c0c0310b40d10410f0317415807007414003081080a55596078000ba401ca40c01282141a012062030719a889620032544400650700d03010020a41203906015902043c0c0c0c80f0f04104800c10001c071902d0348 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 360965116 1250 360963866 360963893
    0x40e0a0b0a08010531120306170a0203030a030b060403061a090708040f1103120d020711060a02150c040503030c060a0c030b03070308070507050303040902040608010501030902060d0c050f0a0509090c0a0c 89
    0xd60300c01d8200c01d0b8000070304c40d2441160002180d0f4000416609140380952190107421020a20f94040300e40c2e2b101582c1d001c4102c81c03c01d004c500f000036079640e04501044903802a913002a060519012030310000240444001c10b49541c2110313900e0305991100c02c1a12007040a480141c1910b01c034502000004036800d00420032000c00408480b0308801044040303143d035001c0040301d6001c54000c0303020001c000b91105a070110b44421508541000c075070540095031a2654081500c540840c0000318590496010480d805420060300307a83e03071840d24840d19076807232009584101d20180b401a192050318802c4c41103108400004000d0305040345140c40d0f00c8881c0c0c0151000352018021074100043c25502000180004c00001e14007603207441c5000c0b8090000c000583c0041d044c1400e0217007040051359100220361410380380441c0066400c4110714100e643d030107201420240840002110100c054000020300a4540c04035038440380d690301e08007540c0c1d06000c0c3c03442c2c0d5000326808064480004200030709151 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 360966366 1250 360965116 360965191
    0x30c020118031d0d0b0c09011e03141005010212090a0806090d090603020a0504090f0603020306013305120406180804060305090f0d0f05040e0a0b0a080105 68
    0xa8506450041c8070829400340004401259040180c0203144184410740200700c8800ca03641c075400c01c801d44401c11540d41c0140190450480003c03621583d03806400030040d44202000c0f02c24014401a001030028101c01044095244002c40040d00c1d0061511035001a140b040e4041e00d000e80e80380311515466085034000581c024580003005c103082c4820010301d0b12414104000f4850020042c1c000b0b04100c0854000e0303020140100040881203030003100301d07802c443d49030b08000346555036000c001000709100e0300000c2d4103009941c0001010090031000d80f01c030b6984603041e0070000004054051003103810700c1414011400034080301c880300b00301c6070381c0d664418020100410850300d02c44d1554100300314403004882680f008901400340c5985841000e51207101d900081041ca900d1f050380a039a112604d043d8410024403540340c0504030300c0b94040c0d800070920040300000509082d4980c3e40a04440681c0c039010700c00c040f1001139410414001d450080c0d85902440c0820000b0082803681c12402c1c80140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 360967616 1250 360966366 360966371
    0x6061409130516080c0310050609010203120f0a06080303060d03080c0f0706051015020601051e120705031501030804030f080f160b090f10050a15090c02101b030c0201 73
    0x9440028581c054140f0a5040c006a85074108410f140905242000341003020241d4084c810080354030300d0285e403101a04d000300e5603a9220402c2c03900403441c521441041c42c904c1a031410501000e104c5203c8a01d010341140c61042c850240c541c902c0300d959010817240158821205c09284002c6401664510b4100203003032042841d00c001c40300c254843c3d41c0700540440e900c60b138941c1005181e645500b0390b04003402212250303120003603c0500003551004103000d510b1003800c21700300421442500c0c1d80041080e1b000682000308107070043c1c07141030310340e8031034440c1c1800781c06035100109070000061102030580b540b201283c1d050500b503450f01c002d2403411940c2211546020407001520359001c401a00b0032205000c1141420a110b1819100c00100070300b9042d41981b03d8100d51200324004210041c6540000c900013406943c1c0b00c582c0d8025108020f070400c0d11003a11500412004001e801c0b98000c40402d0b000c446c40b5010380004c940440c2d15080f143c2d0a0710826080d0f951102d8407a410481d6802c0961001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 360968866 1250 360967616 360967639
    0x4090b0f1b0f0405091501050703032a0918180f060920031006080d0503150901080307030e0109150c03022a09010504050702030405090415061d0a06061409 68
    0x401c0d80e903034442c0300d60085002000c24101303e540b41003400340f50701c6910744102c04072015002001030320901505400a00745602d03003000201d0303c4111703e0820580140f0400f010b0107030002c007101411075440e901900610000503150011000704501078607091544099460202002644070107a0221809200f101c04940b00d040f4040858200500c510340b00c20031b43e402c1d800c1c04a902c0c08262038a80b40840c180950b03428030380c0c02c1140c0d100c0454034074460740302c50a02c990b0300c0d5911200c480c600500c40e008668400e84090010429000001c05445414400d45880b64400b003042e00542d0f404105210303070f2404024002031801c1840c03080700d8259803e4806d00482e80c1c80c010701e581c2c811914040b04c1100c5001e10030b9160340c00a900d41424194010481603400300098106150020b44a00c15401402d008407140404a02000b24444e4041d81005074a401001110b44849901c01780050703511444d203182d110758003c00d4001d08035100d8070048521603141c00826600302d050303048407501b0484807290f00880b603440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 360970116 1250 360968866 360968911
    0xe0f031c090e070305090f060103020303030c0702120d08270a0201030c1b030f02071221120504050a03141216030f090f0507060507080f071119030b0604090b0f 70
    0x1902e5002e00e04030b031008292481c194400c00c0c0703400310740060761039950300040c01040562030101c2129041085442d605903500d40e04c0c000309154107800a0801e00314070601710007014156000e400a4040d00700b84544220310b901d61a1443c052082280c030743c1e44243c00c0804071000560090348045011801414660040c031280c0f8000c0302c9100503d0740680101e9040c40d9a460503a03410b100d1140a08400324102003010410341324a42201c00c1c48400d03c01d1a540080c19490490140c1503205042a80b0700040c0710b14601450b102d510303142d00c10401c502041c18004800381006800303058800d0207404200c50782140c1d80c0d00411a1008045542d18418183e1341c900c21900030741c15028841115000b0700700c0038518206483d0543c030b0641160f0240382001020301c81c04000802400c01c4400b40b00c2c60000c603a4070307030384c0c0c600f05000b94114051880d81e001008241e135003440c0c0c0c2e40710a000104d03030091082e603811b5694542032009640d88141d000b0404403032200003401c0c1503c14040c5507080354040705100c20b001800303034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 360971223 1107 360970116 360970139
    0x308042d060b0a0b07080405150c0613030318060515040b13090303110c0607030608030a0e0d050703120503010e0a020a0806010c06090b160e0f031c09 66
    0x541e201e0b00765660380100b5010304450044a1365608492500885640c0588103260044201c1003620f900c03c040300c010b03101c2e1118014090729140da90007540c0341521502207800c5043c183d0743d5840e0496035400310740d002042c61150000003254180b03040c0c0000800c022600684c45030742840b903811010740320407111444100714034070040741882803482d00341c0c0a040c60115000c4c442c02c01142440c00a200010300e06c0c0a11f004ad24100070260322408401d80301d106810698001c0b506002c1c11000701c2c20140102040140150300780d480041c3c0307039607490700c2481e100070314900000c60200050020341707084200103400801c0880e04501d0800e48940107800c8031002042d4906000285003402d045c000150482078220350f0100703003040186840300c100250307902c001c42c810001841c40c104003485824170320040b600510004008040840002c0e10039800302d00f075031340808100803840c80c002503142c1955 = true := by decide +kernel

theorem cover : BRFrame.Cov 360791366 360971223 := by
  have h0 := BRFrame.cov_init 360791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 360791366 ≤ n) (h2 : n < 360971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
