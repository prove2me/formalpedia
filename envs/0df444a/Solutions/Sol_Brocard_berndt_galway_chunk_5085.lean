-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:41:32.174364+00:00
-- url     : https://prove2.me/submissions/8935e928-768e-4008-a9b0-698b3313259a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 914388489 ≤ n < 914568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 914389739 1250 914388489 914388491
    0x306051f090509060f100b18030f120702130914070e09031c02160210030501081002030903030411011806030b2e0c050c04020d09030806100c020f0f030a0305031e0106140c011b09090b04 81
    0x22f0045c041300f0b4000b51143e540d01035503d45681c00d501c4d61a940100140b280082507010840030100640c180045e40030280d44c03803020107403819207461414560300c0c0901c0c4444071500410281032800c4840d550003624103400e070500340d40007a4a1a41c0004c5041640040404c0002d0317031500104244242000340c00b41604a90404502e1400c0118205880e4403005002401c00b42003684400c1159200b0442503002981190a440e1095190301004004c5c11301c00b10317614450002503210101b4411a000300848141c005140c000007400303001030542e44181c50401c02d41d4035004a40100070f0545a80c0010a00e1032210800001c0c07005c001d107030140c080ea1020305614003566030800e48001c4640c20841e110705864044078520781c46142c420008102d0081c00202d1034040c020240360304105038105010b140201301c0386240001c00200030419070080c0c5400d108880c001a0780c0c20354804807068400050110310f805000101702e009004e000321400e80007108004d0006901c3c4101004144198400d20303000c2d100c1120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 914390989 1250 914389739 914389753
    0x20405060702010507020f090a0e0c030102090109050d0804081501051f020303070302070c0b1602011101020703302a020c09010603150306051f090509060f100b18030f 73
    0x804151240035480c4000d040c800000307048002e569a08009021583d4014110040c6140a210580c0940521440d08405120701d013180001860180283c600d40340040c0d4400c00c0540c40e00e01000f0311005030041c02e0320100c400704408a445041070185e0407040001c0b81542045500d0041486481c4150814080c00994114510f14070140d01100b00c030703000161450003589683c02030038034024112030f980c0914104507002803d5407180d5030040c81c5003003241c001d0302c441142c040c18103c11800d1f4071500200900103420f40c0015074045000440d0102a54401001c03c0c0003001c0f00418041190a9070498890700003980f0741c49025404140c40b40313490f1a039035102904003e455400450051141805600c0034561030310141c00310030800284900c0115081442801035040440c590512000041c0d10030b03809641e6010086000c0b901e6002c0c8500400802c1e0003010140c2d140104400045405003880840341056500041c161072510060500d0030107445000800c084500101889c19070074a04251281c5c01142e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 914392239 1250 914390989 914390999
    0x50f0d020a14030f01061404080a051015150302071e060e0c0604030b0f1b310e0a0b0109150203041502070509070c02040209040507180b04080330011503050a0204 71
    0x2a105d045800604005005c038040f500d07164800d004503041804548a80b040c03401c280680028200241c454107001045a1030480110000c050194010307080d454407400c810b40707040381c23187e40103181b13140c000d160039150b84440c2416141e2983c90244260345141d19002501400d90082c00401405041215003c1c40e01c0e29603503403840d01240080a020000c505840010380400340c1005540300c851400c075a0b03590700d201610f030041c004501c01c00c8440c03840d840c3c181c43c000f50a015480c148151554022096035940e10111981c1c0545425103072a41044110350300000d01100085e400440011590061520365041c035000303c0c03100c1d1010395050b085510a4504010319264130380301ca07401c54942d10f4030041000c1d086c00030401900c01d03000110b400c54501010882c61036801000000d8440f10a5020610b083d6103a40d01c0318103008a000d80480c1d504100700e403214040d001010010900401083e000340c000300c070140c110601000f41e003c1c0c0d29260103868120301c2954540301c2c840e4040282d91045042c24204 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 914393489 1250 914392239 914392261
    0x4110d0c0201020c1e0703021503100b250c0905010f050103231801060b0d0e010b1207141302163005030903090415090b0906090a0903050f0d020a1403 66
    0x5c2c0c400c1c10f0564465600e104070742c005200c01000745401505078183c030300f40500d01e51455481151216008520030030301090b400361810854400069030805103107000c031040da0103000300800392400c03100300202c52000a40d243c00c03030184030300030f03d0010001100e080ca440000b50550380b0001510004520090080406414071500141c0240b80560154804044001c44600500164000406080c0003050900c50190660407100f49011044020300000c3c4084060080c600120b4500d441641c000c0c00302401031b0b0301c03002e8240c40b1151009000c0c0c140c1a00a00d000803c0380d10450000c2070541c1d468001d10305024007026024240400c010f09d0000e50f45039004d9041d800300503000301d2400c1042c0040400c000c0c600810654002e040010030401281041fa510759120b24494400c01d00307400e00700184107031507207002d071401481761201500380341da01c6c1d80e080808002440701100483c2407203010b010040d40e00e10303031502408503095a0940140d0b581080480500442d40b0482d02c150309807801c208201d0501f440c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 914394739 1250 914393489 914393503
    0xe040507090c1202031518090c13230601030e1f05040f061d07150509190305070b07020a05120c040504021507080706050709030503041a0904110d0c0201020c 69
    0x74a8000120599511011210440c086200f400c45500200602003404440e9608049151040320f403c100060040ca0450ba5120304a0b1180c00300c0c1c100c1412200d41c2d00701b0781890075003a5000c11000500030300408100d610340310302065400403055044100013540d60944110035a40c1c80d82030041c03002007040786407031074203020450b4116801030703c0303801060030440c1110300c420380360f60302c00014040d4103d902d030f4117440c01d030034496040f910784152140021050261181d02102e075400d55201490f000312001481106040ca000b5807860104803c000404514180141c00107424106001c507942c00c0e0a00401a1480c0145c09c5648208150012000031807000074118030b11b401c0540d4085225521400082c07101c103005402502000f400003100c0c420032030444001c01465105d003c08000755200c0f04c8003296000c0c40350000401c0703540f0400050010f0704035840c180c030125903802d140920345000c20300400d055a5070601c0102070f0b03400104000302e83c0c090a0054001d07803d018402141420303502e4100e9aa1111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 914395989 1250 914394739 914394749
    0xa03030207020409082b0b0a1413022a0105150d11030f0d02010e071401120b0a030305070b0912220305010c08010608011401080c09031006031b0e040507 67
    0x1500103011402c640351900300c1c0c0c1c81c894010606540700c01d402c43c40882000205501c4605c1700f12881e1980300d04103280c0c8501c1c80e062202170103082c945401d2640e19024000b140c6081544415000302c07800d00d20601d030000302000402015101c241072103a86807a012030003070000007201d0764102010400c5c5000311030303031081c40c00908035142070902030141080440303800e00c04241a0540500301d00c0b400000000141a2580d2000d0782c02040305640b03040103103455400900540702d030860103100446846d80314008022a580e20050002070140002c00083e84a407001d42c011408614080341c00801d1006900e10b0692100704440a410400380280c41010380c0c3c03152085182d82c0b8188190f02d1078446c3e02820b0b01d0fa01459100c0f008000103480c1700f501801c004003d01c01d220001d03880200200b031074010903a09400381d10040e116080c85440d035005140040d00001e80c00b94252048100b500c0d0006120b000d414000d42c018500e19414001c445802c01c400c4031160045580b041d0000280300c0020400035800b01103031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 914397239 1250 914395989 914395991
    0x19030b0d0609020909071503020a23031e090303151f0207090c05030f0601050c07050d0f050d0207081b010e09040309060e040903120e151f0608150d031e03020409110c0a0303 76
    0x7003c0b4003d032284420382252004140c0115007612f580c012141c0110f006440f80084008e91046100c10900928001c58110b0116001403000ca04108000c4030024607031540240454100700d900100005640c0c5401101c40041c1d00900040101100901c1a000800c019107030881c5035151244010104a0000d80110304000001410074110f0405009403805030030000c004550350751681c20b2080c0180500141030324640108500107108600000701203048a01e4a0054081c1414010740c141c0745802c00101d942c1888201603404502e581c0303012106205034465101e0b000100d04003d001441e0b0211140f5145c02289003900820100750401030703244843c0400300c00414031101d00c0000c6414006c03c240c02903000c0c1510740c184441481c44141805a0350069005c186000383d46290403601e600040e60500c0c20001c4169a10855040c1144c422907124040d04140e0031440c01041150785c0320140c04a85000641d0205003884512200c0c0181c04091705481c1c0f502c6c2c1050b00448020751a0104040010149 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 914398489 1250 914397239 914397247
    0x18100e072d2f0d0f08071103070f05010e010f050601052217030c060a0b0a21120302040303020f0604030906082d0601030b090c19030b0d060902090907150302 69
    0x4510400c0550030702c052045514507050003070040c030107054921040200d00b501554401c4840340d441803110314114081c81da101c0e091619000c0050701e11f4501c0d040b14002078001000f40b140861591100034035458418400098030740c9502c04446d0844241550300d15900f4105400d00401d681d02005407000d19244403450400981900d850420507072165122408046510304107041c2240c0110181a18848500941d00703140c1d540ca040100701c0740e0f1202c0450748a041c10340140940442645004021100c040c48c9103071030121502c94181c4088209884000280c000800340105981840148107800d0190020300c91410b03da0303009010054140181000c0080c40c00001c1d1170201e8111508401c814540440100c0005c0c01c542542000c0c01190440c0c0482d04010140e400c906145040601c100b801c08991410b04800c0e0340c2249041e00d0740c002c7c0350304150316000044200e590f12102081464810000007500200da0f105001c00240010903001040d00018403c00c520031403c5e400002c00b054610b00140d403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 914399739 1250 914398489 914398577
    0x90e01020c0a050705120d080114040b130501050316030f080307020a0c0f06080c0a0903110105040e0f0702120c060a1512050c01030e0a02010509060918100e07 70
    0x9000700300280700d10b031007615501c0081c0f020202c0d8250550304141c5401c541203880040c180c1e0b07030786209403110000849007001081a89180c12030f0300a4a500100042266a10b001c00103078081e0075105c215000550350001007119240801203401e41d0110000100b010514540f82c1d42034503010700101810b840d500100040317030b0314070900c940344800ea4002c2491022a0303c50749080b00e06080d42c05202c0128201070003103a0307424215400c0c1c07240301100ba5076042c1220704590b00d100304584030f1005581480030520010800e0101d00d0802c910510201500d000507290500c4002d20b02542c039001e04010240801040081c0e11000c00c036103612160b00b040c0072504844441c0e503258500d140c0c0c3d02c00308149610400500030800f01061754440c0d00b03000d81c1c041c40116a070201403030301c50b0502000203010034420007281c0020f0a0480c0900b003031401c018803029100c0841d502c8035a10090499507070100d905181c1c418400d1503c130800039a00305004d45000c1201008544604111000042440d102050160407182c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 914400989 1250 914399739 914399741
    0xd020d020a0e040f030f030e06040f1b0b070c0f0506040e070509090f040b060604050604090b030307080c0f070f05060406030f090c080c0109150206061c05010c05031f03050304090e01 80
    0x1c020a69a240d019861a1a00f08008200c4500204170b0005801c00d071302000343c030310030700908600b10041e0f8003901c400c0c0c8403a51081c0201c00008421107020145454482c001d440d011150707801000070111965803000185060703196011290441384040401c080140015210b901c1030383c1c150f4014002802403a207500c102500e4900800d07029680c8250010300300203a90b01203405241c050340c442c0d10300e0400e42d03c1d8141001882d003e24010260004424801040b284031680c0040307036464000f0f000daa10f880200d4603903000681c00000c201d032480d4440c030070a1000c41802c10120700148030382691401244c2c182400100c50b1700c614071600c03003019214a040c10424400c0e9002c0e01c00c0d40c1d403103101c1c040d8066644c2030f002d8403501c0001b0a81c2c04100d106c1000201c03130140400b4030f00c4140440e40901039a079149000c00402d4814910100f51a0300044411400540700f40308d0041d1000306519203523100c0c500b000b0960806598003200554050b41e0303330002c00000340c0010550701990002034000c500c250102030054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 914402239 1250 914400989 914401009
    0x5041a162d2615130c0807050d0b0d0f05190809060c16090b1809060424020c011e020c0606060f16081e131206020408012a0c020d020d02 60
    0x100040c510001480203100241144084100041d680918151380700c490440440341c5144103070000c00e904034001003889108800424800c1c02220000800c142d548000ca0007600307a0040444011100120359070030300100704507124035801c030740b0700808030040d103607071020594080c804242c0e01032400440d015943c24801c1c403981da0003c210801c9422800c5d590141000502480c0340d013a4024811440d404007507401c81d10125120305e850900405080e103445d5103022064000701c0a040d44400301401620360ba10141c0020405412004000300310110302c10040d0072000c0300d9010190200384100f015085005c4041081503000c1011900503031107040400d0412030620903d944244088101c034074840c2000702e0a00582601c0c0c0311100c0da6030101495845a0049104008003603070141107002042007600326003440b00c803801c1d06c03a40e001340c280f680c4c80400074250785480290941100c0000c01c000c1207802000e4022150320304602d00100301e4103d9401290a0080d401c2c8080d004220220310503065440f070074070013 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 914403489 1250 914402239 914402297
    0x1d06060f100c120504120318082a06120a020306040b0f011706060910020a0510050121021f020d0f030c05040e0c040f12031205010e010905041a162d 65
    0x50000e1500070720b0020b02c4000c440760411200302d41d48e10007042c5810300180301d1403100500002c1e03243d2150521410610280f28040499110000b0040c1400c1c2c00303160807206e03014080303c04001da240d04041003004103841e04030540700d0107000481480c46850b81d00680b020f420841032a50031041e52940c4002c02d080f88500c942c2c294120481c1d03419008140d40c005400451203000380107681440350310824400a5800030321900e1900184104a4a4010b011010350007802d440203010701f29800043c0d0a24000034000c07041d0784050707001681805416038220203010340d01000307490104416001458054175030f00503402158051041c5000041803403e0201c1142d0140c40204a0fa200103a5141e1912204080c07481044000628102016811510350b000d05c0c0c0c16160002840e40e585d81c03d005500e0000e207030040064403402e44400705c1116070842e00e030b1118020040ca2900031020000b40300040c112280c00c0301d0a02002c040f1000f600c551980f0011465190034030fa1620f01f8403080c0340340040040d0003085002c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 914404739 1250 914403489 914403509
    0x21801050c0a0c060207030b18031e07020901030b07120b100c03020307080d02040f0f120201210e033411210102070309060e0d06050a1d06060f100c120504 68
    0x70103d0103940001b6502c0440f4411010100107030707035007215550032085c400c100800030703801406940b4aa03c10500b0324504400c04501d0903083c8001500042e1442030283e1081e64000c000d0424405810b5002e8070416a00580c40300a211014098003c9820714062403080c1d010404070808400405100703200322642507800520440c1c80d070440d4001d44c002503105105400100141100c0005c1070901c4010b034004403891118444d1100d51160010b442001840c0c9601d1641e454080f03098120180074401c150058031031100440c0c80704c562280c6880e02d074410301ca07018400b10001900407a801c2000450303c004681c8182c40864414009002ca6120240046c074222500c1c0d80d01002d400640c0b05501901c2018040e036510207425603202d2098681c400c082007926000302c015026800858459042923805c041100c074001a6007003850318642100c022944512019000101840180d1515036401c220321001200c00755403400c1e4500018148060f90840103003101d0f010551a0405802142a10000e102c0c0d44c1c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 914405989 1250 914404739 914404763
    0x7170a061d09060612030a051608070c2c160e030706031a0105040315050702160f090f06050a21140d031415060d0b0a060809010e01021801050c0a 64
    0x10240078031541118082054030864002401da4908602070401c06032031400030b50b18100001c1c01c2180c0940c000f207004070074561140050800905540003d007802405080b903608441e040150344003a0219402d1001ca4269036011400c1d00f01b0031000c1516007180100c4584205150500c03415620b20b81800c100990500900b01c001460507055005508414076040704085880d01c080019070b00d0f030150b404080d000c1e2000d400d09581203003481c2d019075049406c0e401180c00340c0d40b12008008040d00281c02840d00c926446a00b0800392030b4074010b480300b2115010050203000c3c2401e0110344d01100c184205c0c0c050040d14103040400b60901000345140d260068690b80c04858011b50301d582e10a440721100e40040c0c82c04000082c0c01c01c003e1242800b0380c2070f0000007601201072808104040d0441c0304442a00790707603a120041507581c0d40000100528050f11904e000d8a0050300e402d00f1140241d0030a0390342e03401084209460103910088040341417090810315280c1041c0d2403020710300031091800801556402c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 914407239 1250 914405989 914406029
    0x80f070b070606030f15050108010504031205040f08190206010906062f060f070806030f070b07021908071e03020d03030e010902041a1c08030105270c07060e0607170a06 74
    0x4000e4400641c1c2d6100241f141d40d0780c0d950200d080301c0c0c1c12240038002401185043c1901c0419801c040d03002402030010703401e0000541c94080c0d0b603a0000050010307a606081d580e283c0d09405104050051105030b004003d160b02d015005130045480180c82e20540c1100c1a101c80c18181a100e2045420806c13422034245141103812074200c414103881103004502060700084062400099844a20350044040e2110519092550b40150000d001c226808400c8441f030141c05024600c6590040031210020b182a520302513500b082d00324200f8407041d0200d0001020300c052b8840c07240e03d0154030b90500d8000394840c01015000d0042c103003403100950060800d4258402c80d900e178510300201450807a03192901c0b4012203d00060500c41c80402451208180010081031501800c2a0300c011070740700700101182c5244031481c0c65a002281e9030500404085a5142403008920030b0102d110041001007815003020480900340c0c80035001c000c0082ca0304400041c1c08400c0c25003040340100320804688170b004c0020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 914408489 1250 914407239 914407253
    0xb0a08011b1205040210050a0531150e0d0f02030a060501061202040608060f01030b09070804030f142d07080d0b04110304080307030605060c011401080f070b070606030f 74
    0x10282034400602d40e06200b0019040d2446401d00483d80101a1202c01d55403050a40d01900b00443c03500510500307002142206680c6590061000d58041d20b80c4849031103200361409041294200140d246051961b08007030913008001c8111040085450b001021039a03e014451103109400094140c0200c014107400c00c55503030402410381c0d205480e9542c0908021642c1c034224001c40c4146030000720079001080d51030410a0800144800600d000b1070121080e8000c1405850203564000c00280c1c98410041450340c0601c3c0e400c0120f00310b161080b000c0000e242507442c039000c1c105007070041400c51410b10513400c01807a14062001c180f01c040c1034590a0394105100035812040409280718180440003805281510030890000070340901d142c00c58a07981c0b210901c0c1c0e0402003002d8141035440c140400e0b10b40c0c40e80003511540301c1d0071002081c05010f1000078504450113a210500d15403100e004034084201c0800c001007940c0300501c036070362201458203040e0042c0100c1d500190861000740c06400500503e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 914409739 1250 914408489 914408531
    0x3050309030613080a180320100e06041427041b060804080c0f06010f03051014010b0331020f0a050603160207050d0305090102060f10050d030e130f0605030f100b0a0801 74
    0x40350328032182c0304420070038ac594003105d4100e15800401084240113200340020b0324801e0310000780482e41d40d0104050125030700c1c84140020072040f08118200020060030702284c100c0718010041d4014003500e050000b506c540d10141000f018004007149001064004114104170440014115042942e50302c800940f17018542c0000e07170700c5010380b01c003c0007500300e2406560903010f135200000c40240c0ca440304c08401a0005403c1c0c00300703000d0202e8100590031b01180c03030648400c5007481c500306900a80c8100300c0c0415080b40000c0c01160800340400c45075441c8010307a0b520201611805040f10380381130040b0b080401c2a0032103030340015220000c00601d40e02901400b69041d080c1c00300d94060310349940c1d000d15044200e0b048500c04000c001b09010078103003410b002124034403074280024898584400a8000512a098a030303035030b82d582480340000704050003110000c02040c1c020740b29202c1080c03911615031112006c00e802c0f29403210019001500e0380c0e808030700240045002004007a24404080c060380c42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 914410989 1250 914409739 914409803
    0x912010c1112030c0a0e01140a0e010e030d0f0e0103060905040b010518011a07060b0301050a2a020606041d0607050a090b04051311040b0403050309030613080a1803 72
    0x1c100c1982c524640d00c60400c490080e090402e4050400210384011101d013103070700f4901e071704000050000c2c0703c1401e00706001c1c04001d20070742c81e0310309804c0f0307030000050901d810030030018403a90100706200d0a40340c0080164000c5c082034030b8604854001c45006034068040d50b4002496070f4544410041400054034201d4141c0d0800c807181c080d100030208200c1c200c410203004403100a00f01d00014151000c1181c01486400d00c031b024007095000a05001900b120403c5616403010394641c0d6072449064510700441c000718150100700400c4282604000750344400c0182228090f90341c641c441c1290b00c0c5441c04c1c4107a028031800c1254081d1410901c0140b140d00704401d00000300d850008049a80c090201c10340c2c0c10b80d50081c011903000d03900b45040002034403400c00c60031581441008040707078450f03a00c001000a940034038020b50b650400d070010306180902c010010f02c200c52080c0e0307641001511540c01c5034480d10640ca001c07441c1183c41821158440041d6100a003484801d04103e4044002c600c03007184504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 914412239 1250 914410989 914410993
    0x70210110a08030f090604051b130509030d14010602100203091905300316091703090a080102130b0a0201020d020a1706010c0308180c040f020c10060e010b0912010c11 73
    0x14851740c141a6450005450091143c1c000100c0d605a0105410440038400b80c000c0000d03007051f004080000c210b8006960414007a000040e086140000300e01410100071104402c3c4401d80d803500342c0081d00e45a1741c0d00002e4034244c000020403400202008180c6003401810b494151040607440d01a50307900341c000e00c81d004032000e2052450318005060700c8503c05181c40080c01d03c0c40d40c40c1c21212000215800420091000140300425103418007255540381ea1030382801981d0b030f00525020008031008580c85182240e004002800d510482d44001d20121201d082c11142c48001381481680a03002d00c440c00003075030348089220100b580d48110064084910140c1007415911079800440342a11340040160220350303144013103030301860300c1c109003032034404c0d20410340b041001c4600004042d0741c1005850804640c01041c11000401c0078481884503d007280010803c862400200e40025a01440b83c5583ca042c042013400031501c5000400ca24403072000300800082c0c40c0702c2c002601c1800c400310004814 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 914413489 1250 914412239 914412241
    0x15030a091b2603070c06030507230306031b0609010507170d02270d0b090109080403080406110f0a02060708040b130e06040207050312150909010507180b070210110a08030f 75
    0x2402001c000c484c082608110344a00050420340d00f41c0c0a403a000d40010204245030700704a9025440755618800d03c141d21116940e0790520804151405184c2c1d411801310104070308035501070313549000844480d032000382003050f11048103003440c4900300a500030424800100242490b6034503000e60080c0b204104150706440324000101440094004500c0744507009480c0a0400006c20042640075030701500580012505058907510200d40d9005540229020382c0e01140c00d00001f40c200004048010340e5400034030500c0c6a0030384c9295101108980a8020880060b40340e041c448004100ca01820708080300540d81c03401c581d141d1416454600c01c0d150031742c042d1004100d003494180201c0c0d0b90250480029400d02c8900e000390184034401605101425156080d100d1103a100c16448600c82d503448400010f09103407000025100050b00042840d151405040602c088003040080c1c031411a0160751103030030309988600a65106922032500d14461007900411010405410011841100d0350a100009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 914414739 1250 914413489 914413559
    0x7020f01180b070309080c010c0519030e03041517090a0212010b0f04050c091c03020708160b0a210204030533221a0615030a091b 57
    0x141000c501d8000c1154500c0b0002c500d00c1d0388207404c114206400307005640c1c03400104891180c01c44111728140b0011440100d8080380c07024a001d0011980c150300e0805000046880383e4142d00c910880c02010f2242c0003100e000b841d450320640405504002181003518035082030320f1103640d901d201ca5012482040503210300035030380106014003d59140054017040c0e007200c0c45400c21010301001058685404400c0c4111213490395051040300c0108450265050300c2455402c0c0203007800c10513000f510030f6921070040c21200c1000b03084440203c0b61040b40300754841360419400c4036402618a0840054030907018100a594956801882100e10030000c48240b080983c3d81a0043c040303458014000c104030800448110310311070340255002e411020101e002180110100c0b2031381e440050700781c1d500c04c103040c1c0703140080b18200281600000110b64201c8000d041e140c4501151000401c010f08840c1c071401828104401100405102d4035000c02c01298240c8500f07211021280d2800c10040c414141050010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 914415989 1250 914414739 914414771
    0x2070c171b0108061011030304060b10050a080c07021906020f0c03011a15042c01050405091c1715041d1015090507080103031e08060d0201110607020f01 67
    0x801c25810707100c62400e581e40d4420030002c1c980269901c4144480800700c07250651061004500ca41c0c0704200c001080420740041c400c042554108580030300004005024040b500301d448654440c0f0550b4400e40d9074200e500c08540082800d01609124480c41c0101041d07480c0c0104030795803002585411034110340c03120810107099a03c041007400354001c035040381100b5802e20b40d00d402c84007040c116000d817610b40d58610140301400e103100d00d069402d441c20550194240d1101c002801007008480501107800c06649035034561416681d00f0708040600e5045082c002c0c060fa000219030b030744c0c2c280407503842d2804145007100010700d460024491450540202100201c090b90f45c00c2020780d4034010100705c40f0713449201006100c800e0024940d5699044001003440369070068500c500702c296900c286030f52651801414184202c40d0740f40d120401d07004004855544407228580c003400c229800d00c2e4140301400103070340c03c1d080c141d113080c41800342c0e0040268a60700002c03140c1d007081800380200045540340464003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 914417239 1250 914415989 914416033
    0x80411180f07030219020109030206010e04150506210c030d02030c0a11030a08040602010b030601212604030f1401150902090a08010606030f2901110102070c17 70
    0x405422644045504003078589151a404061401c0040c5000310801540009809071911540146c0d141d804803010141e0500003e40141450420150720f414103650781c3d5000036034841150b090f0340d03072000001e89071382e9200100200000c5520415510b4a071031140a522a0011000c540c000d2251140c405a200c0c40001110102c4241001070100030225036502e0304c01d0f52520a001d5030601c9241303410004a2000c0b8018001482c0c0f41e0000261560440185818004142d001195012014074039562244103204102109540400c868913241d007030806100524507031505403131005802181c00300410407504811a00f0900481089000804180c00076007681c20010404d0490340d00c0600400c20203080e40c000c0c0c0790310341000b0a403040c403d489900c62403c59413141c0c00440040d0f140c4145120810107807050f1a15a00761091500800c051601140c0c00e2040d00b110035410014210250052060294180c1e04144d41c840500c5e05250380c1c404140c100700d0144101c00100c2d004520800d0348041c0421040d0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 914418489 1250 914417239 914417269
    0x1206120f141f06090b0a05280e0412111606111e0601060e030a02060a2a08120703053705011203031107050a20030d080411 54
    0x12060080369482881001e0034010803621845003841e045007010118003501044400000002006440c0001d240c2c142c862200c005401903601d4541031015456202c03000640004030b0203d01491848080401c00c00381c225449001c65299540a05c000c004445041ea07182d18040d0381c0d046098203001c00003546075030038040660344103c405401080840d0044060786064094841543c1d80f1201003451102452561511050740e600408014000560080600380506109038001c1c48040240d0340407820902c15401540240512000402c0f661140922181880300304c1003204c0380c1010032031803c05d00c1130b0008514048403d0030705000030f1f80c1600c00c0c41824440c0c1e078001e41140d151107210200403842e2821900c1c8084000781c000d5010503040140c02400d0003020a48803a9081c1042030900804030f03103450300c410392420002c100ca0008150006804031a289d08480329071404003c3d460420a841e0301140459058011b86403a08821600b0140c0184581d003e2200e28001700304c02c4041203803c2e605c9101d0303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 914419739 1250 914418489 914418503
    0x10020f280e090a0207061d071703180a0503070e100914160516110f091902030c0403060911010305060303030603121b01060b07060c08070914040b0a06120612 69
    0x589000c0340b80c64800d05800c000e0980f00103152142907101c1a060f00c2440211350b01c0700360800c0002c81182010000d0000030b244d48581d05401000003241d40d500c0384122107100310b280d41200c803010301c41d80e1458400d40040c8401811600501c3c0d80c0c815101d2000011100108403007449200042e07910340c03d0050110b011650105895690348450146800e27801450f80e88003044014400014118240304002c100e081c00756200769605120f05003000001e030384c0100041c2c0644480303014000c649004807541a482c086a000250322542d801a00103201c0c0295030028080030300b00852482804244000e005a0800a903024465503841c0b10503d03680f44025515180c03d80c3c008000070a0600c04003001c1d20040c0ca6080d504210300d240e1500040c213513141ba03044044040e00024284003000910300c1040041d01160801c3c082626040390003a0101c14180701d03802d451000301d403800312603940301da00500c44414001d210b005030f29110200100000300300d40180300f24500d09940420035a003101d01d030220300c50b80641 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 914420989 1250 914419739 914419757
    0x309020414160f0903210309080f0408061b0301060c05120706020c0613050d1d090f01051804020108010308031f08060a0b0a050a1a04030605090a0c140d060e10020f28 73
    0x601001b624240c40c169410540d80c3c1a940f0300145a217002003c0b25603540c40355940b154105441d050400300c0c080d001c40500260140c0300c0050283d42801d883c1110303440e00303101d011074445081142c10000c00510101010b50002100001c01c88503074003800103500c654040700c0003959121401700010014580c081c10b0360b407040d19400440381c840c80185d07050150541d914002c89110a000c2050b010b1b0075103410101c00c0c88000140818105812208507032038031500084158141500060b100007010700024202c000000b002820321121600103417400d42c00d40d412407550907681e02c40d05450b40e005642141c1c5050511a1107050f0346480700114040e182c0040044001900d0605c0c01e80c039905250884c0d62031600d09000000c0071031a04d210301c1d44100340140c040c1a9181c0c0500d0860400d0714507070081201504480821f011700d41362803a0160905900400000740d05500b9242103103004034501c811280c0342e000249410341320342a04054961074404031a0460b00c1008120326090420b40f40e0203010004500704 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 914422239 1250 914420989 914421023
    0x402030316050706030c230a02010204032127090b0411070309031e08040b07020a0503060901021218030304060c020102091207091119050d110403060b09070203030c0a0309020414160f0903 82
    0x740142304101140c0001460103a0300e94800182500e10705040461408603090180c405800c41d01290305440110300134070144620a44030000c540c1c0d14007074004116a5441c4411258595502030404000d20f240e000361070701a0351078010101e24050104845489241c070810704018021100306a00c213902402c80c3e0708090070089070800c16040048145d031b121014146c0000c1d242c800303000c1240100c10040000d0781d41c000d4942c0080301c00c2c00180800400945e07640c0014500c0f040402580d812139070048011901510b04c82040703000e801503140c0750340d20100c6040c046102800000754001107444541e0180121100c100d02001c0a000e0155a0140c1010301407108040a110300001d00800d26169070010f00d20082d41003060958020786c20031240140d540b01e004c000b41c6066203a0580c0011148011480d5107002d00d400b150070f000e05490002070644844a400440d5141c1c1c01054100311881c11001280c50080702042c50114140c2c2c10401040c0794180f0300140038802c4002c18280c0ba04080e05880801c0c1103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 914423489 1250 914422239 914422307
    0x114040905060d060c08160509010905240307090e0a05130b13061406120a080d090c0509070513080d1407030e0306100617040f06050402030316050706030c 68
    0x100340e42d030b1000032003140c540042c00c103108010000189540c1c03001b0601d000c401c5240101e40c2c1000342c5091050a1080c0101c036a1312036108826a9020790340214420300950221100451100301c2e001203440101c200041107902103041e008a400900c01c50b11103488502d54074089503001d940c1540400032440250010a10030400d55070001d18140c5c0e0020350320842e890f40e01c110b41080417018594050a41401100c1ca00741e02030500074240280581243c0c64107580b003000714801c8108411040307840c0c0d0b10590034041900c0015000304000b90031001a4582080014103d81c010802584280507401c008101c004000840c044034a000d03440c1d0f002e00f05518944542070790441c8900b1802c10500749110306c1d50782c80c1842094020702026915076420f909000e0040d045403030601070346080e6110b400400000c02e142c1c1190f12882d90708020005283d803203030b0010034118401d401c0c140c0950986140303503204210f00041c1303d1048a07015034080180e10044141200c612044849519402d8120000e004204c0c0c61 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 914424739 1250 914423489 914423491
    0x3060102030c16050a17100e0a0503121815070305220c17030c19020a0302031905010b31181a0106110d03050712050c180114040905 58
    0x1050045070b08100c03000c44154a00714824008494814038210100314030304040c1c3c1000050008500000030003040072240303d64601819001810803521041e0500000e4018440c04000c0d41d004001c0c1c030745d1038455a250a0109205580741265005800d180311000c0101280f2009003d1071444c0c05c403c00e8446002c00c5001c1c01c406031415087ca0601081d4003004103880007001c0841384074030300c001032052410400f030f004111199260301c00c64104004000d2151008111030451034000e80b219070f034418060010411400301c940009401d44211000d10701c0d0741104981b0303996503c2c0708500a2180400e5441030000140d00c020346503840e40d080040d1000c003400742215201340d0148901c80041d040302c50b428120074550031781909555080010201c0351041d060070350520301401042c1000c91140e042e170f114031642c81d000d0303940c0c1108065940002c01c844900c03a00507070018180d00501440b4a060001a248143d44000e003e00d031480700390850002d455004030443e003e08081c4411143c00c042c07030b145043e000740c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 914425989 1250 914424739 914424751
    0xf030a0204210b0702190f0c0806091b0301092013021c05060307030209010605030c0405062b1514040e0d020f0d1e4a01050f0403030503 60
    0x6000d000210b07020911000740030b41d110107248225201c0160b8181441d880703101810724401c64201ca800c044021501000e15004035070f00c040c56030750145940c10440b00841c003640091805011341010301c4031402000615800289000d40c1304907008020b40700700740c00c0b07c0500b0f00062003000200c3c00000244080b03211f02603070440c007500c920300ad8140204000b00b21390003450300d002605e0360f8000d0f00140c0e2003103102c2d4a80c4941c09030014100340d421030f00004c2391420140324072410464004001450503031010309a80080001401c01760f2110762100b100300251404031583c9002a8451991568088890007900f400000c0200410421340c100303031103400c10a41c1201d00c540c0058403982506100ca0080101c50000f04055018100700c2c0340d100100b42c01c0c24080000001000040410428070001c10b0480329039032401800c1210102d10b041c40f10010510b0704001c421191605801c0701d14900c0d1019140d207242050313403010700302d0440418005540c0c60094150080840d18144410b00c00240a80015500304d0f07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 914427239 1250 914425989 914425991
    0x2a06020c04020913050a1e0908192c04050f0f16050408071403071a0f070c03020303030414010c0c080405091e04050705030d030b0303160813030b0f010b0f0f030a 71
    0x21001d01302d0006550040d210084120341d45d00d02c801404400b21802116040c10050510006903103407200310a0b030056000f0007002e0700c3e1a01c5a4140c0e6401403130b41010400c5460140401d08400c216003030740c02c0c40e0424426006e141840001a40c04610840542c41075484901c0c10442c2d80300c076100d421080108601c01018000c040101241d030318020002c00d401403e944060000a001d584240f508000142d40f00741d02822081c640b0f6282e1052940031746441e4100611030a89501c030506003000710350096480a50180000024030060190f901d400c0c2160383c01c0d000081c01017030030580080f40c02601d80c05000c0e000b0002400184243d140820b60345402241503c4025010820650000311060b0f040e10110f6013a80304000410107800c0a00c0040342400c02402d04001c0a403a402c080b0307440c0e200d0355540c410044074014690081055081c1561910546500e040300b8154803450035028007042035030540302d244010000018440886001c40d44004180701c4086c0c01c086120b4421119900003401c0d04500d6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 914428489 1250 914427239 914427259
    0x160806151305030f030c030a030209030c04020403080318070609090911030d021e030a05030c0307020f0f010b0312070302030406051303050d09091401050f22092a06020c040209 77
    0x81440396000d8461a6038034000042424545820946000c88040100315107820520906c00b41c1c43c008016209210840d0a000d0b07900e055020019040070421070308151700900c045004020b121085010350311030105c2d04140340a003156140e4155072008980b1403040014040c00c401e110150580c6c101019045c425151100740c020a5000a41020101020b03000140d03c9540740e6042c0d1300010b4a4002c44034010006545003d181c1d000040041c803005102184070307140080820a407520800004403082152010303118179802803d00180030348190281d082c070074455103021410000c0146d088036080769044d00103502e818038202065450f5046180300414201c4410b0000010031310602c000403401400d540c50405490502c146031040718100541d049424031600010310058a62171040c40854074100e4640707400f006510b88906140701001e90515506003440e00c1d01042110020380f00042d50035581e607454082c088884810990b00741c0b4803404005034429580c0c0c201c3c0d8202680144101d1802404500d04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 914429739 1250 914428489 914428519
    0x20705010605030d020a03080705030708150d050109080301090609060e0a1508070801150e0423120d02040918152a0e030c01020102161704120f0515160806 68
    0x400b030384c0c6801e140c0560000c9000c41c04150703101c0c04440d4414020b050280c110f013000300b40108940c0d401010902c01c4061296028843e0b41e07101490410158454001d0002e503000345010140c5070420f22981d0021800c0c003201050340100c81c086c440568203550344208030b41e80d0354414140503100414181d100d4003015100031511500c203102e0200034100c0880042903002c0c44852040b2135034910b6200d4440b01c1c064105020000d200714030844c488640d41c2d6900c030700045103010030504012045054401e0b950000034038001c4030f0055001340c01141c80d9110304100744603041070b105101407101c100041c040680e000c4c0c0d80380d22410b540d1020444e0702c1c1016580c01180d940451271382203450003100800208a082d4601f030040d1408000c2440030081c28402076040c42c45081c04889640704241c4000d0403c4965210748804150741c9003510000cbc60752162103540702c030040c2031440c2c000200388000d8441c0c0c05003000110340310b150300401a000e02810030600b9030700b2150440032211900058074032640229401c00000d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 914430989 1250 914429739 914429743
    0x919030609210203071202030d09050a0209070315090f060b12040611190e0f031203070906090e0f1f08150123210601030807021815010302070501060503 67
    0x40910311a4400007041d00c0d40e82800d0328060b901d050041d10300b2404a60b004200799020060b14240c55200074003081e4442c0e00d02e8141e00310302840404914951801034102e0900c040024040c840074000d6488501c16142e99804605075103c001150405a4040004114142ca9540181c104105140f0005005038580445a4003030b4003070040e440102c04410f09010030b0266903c1011550300c0340034009850720072030340d0401c074105001d4140802481446009a11291502d040c65580d84c0e000805548400302070000c060040c0d0400d441000c00645004408030703442d4003e1600d0015034071129088452075542429150164000406810001e0100d25010700c4074410224890050510f0002400c40741000c00503125040308143c1c41b0741d5030343c06060300d4810054000c0351411240c80060341c0114003600030312140781c08503009041481c803e1051400020502070704802a0141d039100b1100c02e9000070f08070185d10399144058582101d1003044d001500ca156009900918071144280c1c00442c0321561500024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 914432239 1250 914430989 914431039
    0x5040b030a0f0b1f0507061e09030f14091e040e010209040b010521042118050303180405130203030d140603160e180d120c0906021209 59
    0x1c120385840303518a144281e00d034020f200ba401801d0303e640c8a41c008000328a16408140040101400000100d030810302c501a0007034007948504100307040c0d01c0a0000c40400050061030700070380c001740d010390030605842c0c0700c1c0c00d6126034030038004212800c014001080000e00f0394164004018102d200c4c9014000d1303100d5028281c19a10325200040c0c4810382031042c042541d10341c00031a0b040103400c02441036240d0200c2c03400c1420070300075000c40400b41d44510b080c0740320042d00103ea111329041292200b02c0158400b500081d21040307844680940c0f5a2181419601e0040341c483c100c1c0c402a2070070b503101c0e42c00c1561003181d000d40c81100e4007498400399008a41154000c03900b03000c4d0107403207400c0513980c000600741207504408150000c01c0000c0304250f880d9404082c038062441760f0441d0340c2c08030b03001c1d1891803c1c040f81d4020610135501103402121000e0410a21031050700030090400480380c4005000b5662002110a543c0240130b00195400440f1325507889410f840341e00c0503040d000390120100102c080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 914433489 1250 914432239 914432251
    0x2101215030303230c0309070e090a050705060708180a1a030a051b0a0e030c0604080f0c1221120903030a0605060403080a0e1807090603050c0a0207030f0305040b03 72
    0x4000100e0071401d000301644c450964911a44181801c0c4024684840c51960342c03003010700c2600d54403034440d152000e0074205503902c5001103003200b200f44078006c28046006003c0f140710f40125582150389800744840c500820b00d016080c51400c2c000c0158540030f410310702820b075600414680b00300d920303042c1d1007107410340380b108044000c8004003c0180b4080c1034401e81c0e03002581d8620940400c41c116044985c1481101000c0c07041040c0c6402c58070090710100100071103900c005242e82d880d80d494510702030340d400d82c40e103044146108400a040060074403a25512450070780c98090801100312100580a00c51030301d01c071243c07440d810010036442460140b21715000301580307000f555890070002d404d141a6200e582100e481110100401c10000341001d00300c98407800d0300d0400701d4402500301c001680000130340000700003105950080046440d8480300080c203640781a28100001d4440c91520000e0b03001d11406200541c0c007000c3c042c4041500809500e01462003898018034041d264400380034aa0016989 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 914434739 1250 914433489 914433521
    0x20c09090114130804050112020d050c030406051501080a0e1014010f24030b041506020c03190c060507050a050111042402060f0a0f0501080a020f091003021012 70
    0x14601c12002c22000035420040596808650781050b498014551045200f400d0500c181882a680e1060803501614603c0c01021800c00191506254584036944102d07000c42da810301c0c100001b42c06000502c551294918103a44070306a5a0383c0795401d2009000e00301500802e44a00d10424001c4007560090600f030500c1c1412031707081c0d5458004183da801c0718030740000041d1503010004000a81101034400390940d594a40400c0d102c0c026008600281003c5454003250442100c01007512a000560550105415821216403800041803d01d070060742d800b0042c42d041501e9410003010b8402d002801c00039004006a945800d0b0690302c1d5800c480507401e052003400c402140402c81e49422a5540304039502c00a076200d60300110f034400a407280c00c010309484014401002185070403501e903118080c1e074092250b01b0413255840c1e5441c2c0303607036170311b0644101d21804032105c8000c1d541c1000302d041c50003420300c1074541440714110303030811039007411040300c4500b000801081403148640702e0048800107611445 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 914435989 1250 914434739 914434751
    0x318170d0905010207061a030d0c0308060d1e02033a020f030403031e030204080c0909010f0e062403060408090607020a151805060403061107020a0e0f01120f0f03020c090901 76
    0x16038034030070700e81c00c801c004d120380c000300c00800710700e60080440030001e8bc0c140b9000da50381d50b5043c001800c00c55100d0002d0510710b4111840d890321101d991294400d00e00840403916000e07500b140400c11030260030001c0004101040d160410f0241108451400d41040c0c010348014203044101b0924582103588264000340490074100401c0c1c240110350700c100501c40c503065241034245109141d0340c035002240580540110300c00208c603400c1c00e500010900500c40d1702440403034150703d4102d03030301c01065450302d10341c1c2d0314406211049030400c90100780c04c80300640640000e946d580c440342c0103900304907d50303604000e04116640040c0d947c48121030180440d1010f002d0000007580c030040c0507003040d020038903411a00702810b01c1560f941d4000e607002c80ea440b0320f01186000c04c0074849103050044ca94021340200603444040f42640120707403281c1c4140c0c61500c24142980e61605030620507110b004001d0b01c1d001d240c1c412070003c24039120b6a0910300d4000e004480030f6070381000100310600c40440e4800c245942d40c1d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 914437239 1250 914435989 914436011
    0x613031403070c05030312010e130516170a050c010f030906020342060708041a03160513210b07030e0d0c1104090302120c030403030318170d090501020706 68
    0x9520009800c0a50003541841c0d403004491805a0040c089c07a00d0108448000650b1956011607e1452940c000140c0c1c1d0842c0000012400d45407280c015a200a0144044414000000500c07140e2003500b00d401840c0e00301c0200c0043d1404070845440b042095118103c880110b407141c00210b00900c000812900d01816400e40c1008207841400b0602070040b01190312202c020342c16002110040c021a8078581c2c4030440d14094031180f042d0341c0074010810104a200c265100c14a014501c1558901c40b03403e000c2c2c038008402c40780c0c1e00ca8a1240d843da10300060007400307007145603e11064415142800121804d596071181c258203001200c4840009444101d496500ca80c01c1c025030307485400d00e04102d803800700280d80c0d88492250340080c0034062039507102904240351080007000181701c1c084104030755440042c1c030b019840fa4420700055001c0ba050180c00c100752044003042510f0160003c100c05922028000003070070b958030a03038001c40040d0b02c0b0013000021400070301c020503040b0b104a0001030340034100303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 914438489 1250 914437239 914437253
    0xb220312050a0207050c010e0d2f2202070804180506130c080f0a141f060e01021b03030f18130606020a030c051c0f110f0c061303140307 60
    0x4008107900d0f030050161900040c2d000600340c1001e43c0900341a0744c8612603030081190250505e0303000d00f10328640554040007845203041d0744d00c1c041c1d407030200d061a03918a00501a41080b030320f01d5024070396a440340600600ea040d034081c2030038a106011140c88c02d952003a4a405440025022402055490080c8441403070900e6400321a07210700c000034440c85403a200701600c2d01800401d815411820480080c100300502e500c4030f490599910314040f51420f00000f181c00d447c139400705084550003403240c04511107004440d00948140160b00070300410301c40c1140c20b180c40c991800340a80612042c403030150076210340c40103800c040100c103004210300e004038003c025111040e803e0301d81522340b800d101449041d83c0451003014480c1c150400c4141c1e0442c80c5002441e0002c0c040140c0c2005600c1880b00a0722540614040045a0280d44507401740f29905e640c1a180c0948522000b070315444a042e00c016802d14002a010204909410096560b03480c0c03a00d01d080080713140e201c0c0c4a9040003541c881000b4803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 914439739 1250 914438489 914438491
    0x203070b030c0315010e0a12060f060b180108060913140d0f03060b03040302070e0c09030303070c110405101e0b07081e070c031103010209030a060b0f060906070b22031205 75
    0x10921b410304240054038081005400301e0b028400ea01004040d4803428000d494011800c9050410740402a20359200800d48a0360442040345644500f200d041c0c0700558411141e00303004c0c4038001c1120300d041e1a880d03c00702c5000d46152046034400c946100384000d00c4801d2002e100d2407030b07030307511a110b0700c24043c1401400c5401b02e81003455521001d10510022940c00124603080d241c2a0800d181961220000d0781d00034020016842d51510000040104003503102c0300364940c092003503c06941030b195802c204000d0b07400441e03100c0346e03461000c0340c03c01c84c1c418014600242000c1079200d9038100c64940400c20107581c014901926140700c006007a03805060354000060380303d0006061541001a1981c07101c464001502c00540700d06e0080750003021907a0294121410002d00901b00e0340505070368584840038104445089116580700f800e841c0c014202407013282c1d000c0800628451801070103642d4840c0b0401c021f04849080680c44801c0030340f0403181140c080d40d443c029100c041000110300c1d00e00c801da481c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 914440989 1250 914439739 914439781
    0x18010501022b0e13061404060909030c020906060408060405030405210d35040203060a020a0203091c02090a200a020c0f010e0406170c1008130203070b030c03 69
    0x4072002c020316407207103002e150444041240c80c000c1000c0603a28001034a12154201c4071108501c0c2c10800141419210310305840b148090b64140540c81d5107801081c00c843d50100080c1c003007054120f06100620f0084640360f84003a0040000d801c10351550719081c03803c00c01712004c94445c0d100140030700c81031401a030300c1a6442c064561814100100030f10307007510350301014100d4081c0079091050f545001c040c480d4255100c0500140b03403001c003002041d400340344e07441036800342d0203402007401182d1211121b008440d44162a5001140f90600c0c0c1d07030500840c0c80c008040410700420219001c001a515919a1400344894002c046501c804107021610f0608010601a074010b400700000050389070049802c41c8a444112000c502c0e00c0e02180050b40ca0240c102c0019034094604030020801c07003c140112030220040d9012601c010b0344250a00c201204203c803040c02090105000600960391900c5600c0d52510140a48a12070303038810280441c4c1d001a1a4440c1e03541001c4104804002c034801c2012040e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 914442239 1250 914440989 914441023
    0x3050312090a0c0b0901092102010306060207120308090f010606050307020606040516030e101d010605040606051213172107050a030e0106050a06020102041503110a120b1801050102 79
    0x70300c643e0b48640d40d8004510860505480200d8082c20302d80c014010080202900c690545811650442c1a80703030000004003203003c689481300204d0034520003c0c42c0310a41c2c2c900da91000d070207420703078030300f44e40012004121103150300c43c800524901c01e40c20302500005100743e88916440341040400a0b081400042c1201c0c080c91801040010750b05a100d6561250030160070001060340c05500310701d04126180c0008004107080c0215216490030100b42400c80c0c980c000000c00665489604010945265108500015805014220308940071802564116103003c81401002c9072580d42c1c501d0460803069a03101c141b04c0410102083c0d4000010348580a103454011051480d20aa02510900400fa00d842c00c040d039803551402d4500c025030050300505001000e51118035685c0d01c0090203503005000e0115090301d62000903006034000d001d1803c945450401441c00c1070f07100c000031101090700096140c40702e906c43d4003061260b202d0b1120380c0308580000300481d04540c10400068500358084060354620 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 914443489 1250 914442239 914442253
    0x2310315050903070f05030c0111040f080c09010b130e04030c21020a120207051804050717070b0a031e0605040501080a03091a04050303030c0408161d0c0d060305031209 74
    0x2c06800300445000985c09400e03004540301c04d0500c03c1c59400f901c241d0001c1e56185c190030b500f0140300c040c003900454031081401d105458a410760b041d00c0740402c000050300321846a0041c80222000070182281d002044103100c0c20755515500040008003d880503000704015030314101c00d00c00f440e0001815045040c50406180d20203d00003595405203040181c01c0c0c0014100324940f05109008460080500a20f44502200d40e16000d1000081c2624215403e11506000050740e1400c01e200d6000d0b001d0080181410500d0080300d54150b6009441c4202019954075078980040703112460703200065406040092528148000e0004607901070304180a1a07000d54481d0001903842500402541c05540c00c450089000c0000d030300301c5010329004507506000120030402c004001101a004650446007203840c1d89101d0355080841e0b520314084c2d000c0c40d00508044a08911200d070300d0640003640a0000da16000d45c5c01040310803621342d60001ca505030030000312002e104a44005950300a03807240090155 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 914444739 1250 914443489 914443501
    0xf030309241118090405010b030a050f1504020102030f0d1103090d0807050405130f180b041a010513020c100c020a0507140f10030b03030706091b06050d0231031505 72
    0x101143d145244501c01210000303040103001c0d001070201450190880b2080344580c40c1c01d40c7c840c002c0d0040315003940b0030a41e00f0b552043c0180d5246028a4060b0095454002e64028065013944852510340005441d844560607881d9801c0c000c6203d20600c0000d00510b0022940040100c076014006104000e0144002d001643d00c0c91a0326504400143d0001144050104240c1c042d00c0845881d50f0032070b0344940344c98240510401481c0c030680c425410b40c01800b60444a12160610a004103a00180c87c004140900c1c5002c2d401081076440d440119410160000f0304041500d401200301801604196040010000300700700c0700029148041c44940501081c00c04500b556800310036692150440400d900056400707503001401140010301a20fa807104141002400f40c80191000c9a041304030b50607182c6e18502180003d400c0c2d401644d1003910b4404a0420403000e034204003091b06c600b40301e40300010f402164040c4060b54009145188540303030b51640c20b002d0640360503950180100c504103030400031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 914445989 1250 914444739 914444767
    0xd0804060e1609090311010204060809060108030403030e0108061210060801062301030b010c0c0b0703080f04110910170c040e0f0601061421011e0509040f0303092411 73
    0x41d11414980003504d2a07550404940c46a0141c00301d0005520001d400b02c0e64a86c4802000e21551031041114a6a6640c1ca03c11340d41744624031014000030303041554800c1640c400c4400e9500610024240048007001040381c60034404a4005001040e176200000c01c0103d0302805000000d00910b42da03124007185103640e41d000321000c144950704060340c441110348140c1c016520b03c00000c0d084421403280070344450840740d0950002e10300f540440c011400244034001005d0fa2a44529885980e02c18035001c0c1c3c1c401d202c151007000d04489800070031070310302003084c02c2d444a08403100350030800145080007805042c00102c41c009101ca4070345070421900414240400603200d4119801450302c0120f20080c0b40000ca62405980070500d0070500d007100e940b5043e003040c419a4181d42c9902c040c007070702d00000c1801e0307102d60b22070380300c1c0710b80154600001902143d02e04d02e10310100e034005e0401107140020759445030380045100c0a502c15a00075148040c2d003541c618410307000340800720030070b551074601e1044001d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 914447239 1250 914445989 914446033
    0x905040e06041511030c070b10061d010909150512030405090714090409061415030a0f020d080a020f0706050715020c010f0204090f2901050315030d0804060e 69
    0x10f8441e50000c040002c04503a41d6006000c41c038284e001c000d86030b00740440c034002a17078002001541e500303801750003081034000310294000c102d47c0c241c1c503244940440d0220101e510390140c039401e410300c191064001020305807806403800e0311100205506145040c881080f440280512110641d68028072050060703880c1c5005690308410a030504803104808070242401e5807040700712207a0024140004d0720200525608540900c3d85440301a005695032045805020b1903000601c0c0e5050303014080180108668144144000d400504006c03180c131305a80300d40d80958014841c3c400140d01915000c82202014000c2c03001810003458064501584ea46494000711040029400303516400138607410009401d50088000d580020001d544681c0c0c1c0380800c90040c10048611400181091410036000403809080e06041c0c000c40c405c1003c03044441c0044036a60401088030a00300c1e0910218071040c3c0e01008020080c0013283c8d90318aa6150a103490400d4401c01144001d05500808a8460003041c10ba031507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 914448489 1250 914447239 914447243
    0xe0c13090c05121510030e010b04110901110313031419020d031b0c08030a0e1804060203040c090906090314070b010510032a020d050304050c150903010f0b010905040e0604 75
    0x100903407a242c203900511902021890350000f1719019442c045609034000c0c4294184110003004100c040e81c0034801900c1c2e0380e81d14003920840030080041290701800219403046980400c8a0a000c498a030200d1400e03550b40003071310013a040e69662070780340c0010401d40485080790716030302032082000da012500c8541701490081c20b012141c0c51110115441404000c0002d81000160640c00d40e1074440d1501d070b5014509000004000511114507424440e80c00c1e0030038a9800540e4400d90361365107400c002904040c004817030010700083d0015a98105000302c0388150b0040d140080d000078507180c042c140c6110303104040f1910009100f004041f920140d0b840e03045902c280c620508000602600300c000341554001c55a0700b082c20f805030041542ca035030070040c612100d502100c218501208050301c8074001114010541d520a800201c214203002410800d4117003080c51050030200303003400190a46100c40384d140d03404c99545914148941e8012038442c001c1502303031001c01040411406041d06c40c2401840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 914449739 1250 914448489 914448517
    0x606100c110609090a060302040501060f0914011407050d03061d070305090f0708071712160503040f120201080f01060f05030907030c060f03050703141504060e0c13090c05 75
    0x409009620b4a004a902c0010000c022084620b054500030009080f5800243d005510744070000c9031190103400c41078064200358960400441c50b01d40c942d01021070b18002c1074100302286000c0880010044050031000d84a40060314100c040004014102c1d0342070341c04008202403d84508040308a08100c064226490749808101669203800031890400d0b50400700c04184100300000890754000f0882000b5075031040710005401c2983d4800c56501c2841401c1513035a414100b00d8a6264075000c0c0300b915041e8071030703c2600e080c95074032020601c40110135446105820b94400d41c60701150381c44003c5540c40b001c2da00c080006175041c2000104080d00e111418402e1120001c081001007104000040045078030800b045403d0340c076054001d080000d81503a110200b41060045110381d8068000e0610440c5106200c00d075507950000b4040c0c0720801c0c2074800350440da40f51004100e8124a8100a22510790200c0256894014940400180c6a1030f031062031554504580c2e00c11340b90b4032008440d074410640c26 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 914450989 1250 914449739 914449763
    0x3010e0702030a12092a05011b120f090e1008010e010c021f09020907020106080d020114060112290a0504230907080d080a0506421602030606100c 64
    0x580021b203031035070514602071350345010001e5085c0040942c9060a4801c20b994501c03d802101080391509c65648100a1200c1c0705c607114408140d220312944055409189410041d496807040446060398080d1f40311030340b00d00c49038000c0c415520240143d0100c1122080200080504500d000791202210b0707001c00c040c40610711412040d80c1e49a0020b03054103800400c01d040506100901074020040342c480e0142a005400680f6100d50042c41104904403041c0500280c90b5a06001110042030310040ca842640c2d645c4641524020b246076002c2e030f086415040b10460300340003000c22601c2021175001078810360070003020244500210002c0455031000700168030440e21450441801c0c1440750f042120980b00b43d141ca03d1000d94454001d9000d2070100204019940f600030901c40071076550b041c0325007031503261740240b20035441c1d81d241d0301041da0130742001034110603c4d050f050841d5442160b101103842010075500e003d501c1d09000441e0031240480303441958011901002d484002c92501c040c02a5441c1e507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 914452239 1250 914450989 914450993
    0x1140c0d0e1302040e1e100b030a021207081b0418050402041e020a14030405030a120e0d08040b0f010e150a182408190609080304030503010e0702030a1209 68
    0x15a5100c0c8454842d00540d04d55441e60b80c62024110102c1c1c81c0c070b205010440e0b0020b4003448000c18980509280240c020900c1e05080c8803801e07d82c0080c0a14089607401c00070070100700004420031740a030f506c6541394107480c100158000e01d492080e48050300ba001080204000d46581400030452450f2103110110781c0784d40300e0000500401ca946400340308103400102c03800e030b6480c5550044c02d8050054a80d09007003420364044080d0390000f00c8004145500420013102d0440c09144080f0b448484030f100450b1214095508909001088d0340200c0403c901d00c081c001003095000190380d000324821440d41c40d540c904240c40c0c0c1c07942d5028002000304e46920000755030a40b260035000b40540f0480c10034050319041c406040000b01003106032441544401d509444030748040c08200da048410200c01004640303000006c8003000002d6440032a4100da41d000318000040400d00914429030003900c40b0b0741c5a6150880340c1c201801c00800c1c050854000b00203091080b9003020f15000030072084d8600040c04400d038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 914453489 1250 914452239 914452249
    0x90402030f06010e0a11070206070201030911030d031d06151203073e060a0e0301021b0a120309050d08191d0c040b0604030605060d0b1501140c0d0e 65
    0x34114a0341c10703029010000c100400500d5103640603a1001e034040203801e0400c2c0c8194014080c45030003e41c8450100100c3c405503100e078100701821341c0500b03461000da071800d40020345000f0a454211010175280c0b6224080d8021407080201754003415005840300f4a09400810301c40000040d41c90301c41d000d0b80882035103ca60030001d460007164460301580782c0301648101e075440c0a04ac030515011210032070407101c28100f00c03001603164000c17000d824a401c3c00e000a0040d6034a400b103030b80d100d4140d0b60900000d10000c0071014001d804070003200203030180c1e460fa41071001100321184403610503d41403165080014100162000f5100ca407841d080446807103800f800c1b0105400b40d00098030705030401401040e00c0d00d03031000348840003031001c2c02c4826403107801c1e042c002a0b8a003401c21941c400c000b800b04201040c82504400d601c200000e0040603620800e94822041803400c1e5407451101007001141c00c40c6503003111119000c8001040d580c0e080000c11204107564484035035502040001c0d00c0b020650075143c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 914454739 1250 914453489 914453503
    0x203010819050313030b0103020909030a120b010c2a150207050d111909050115080a0905010207021507020a050402120403030b0a180e061605120603150103200405060d0209040203 78
    0x71390958244031542d242080b5549040a00040c6d105030b80c0b46001c500c40000010498240070203036191140c420414002010081ca1403022207818802c02d03204101c0010454034105c92014201503800e44011110324a00380903880c9900040000f040d02c0c0c515000180c0c0001e0351008885040f24500148049454039010001b07160f214240c000100800072070644d04105800b406070b40f038865041110341c2c2c3c0c035a02d03171445440c00344064010440b1500415200b10403508456032407409500054039114940e8003007074014400c2850000f40300700104a610451a02c05001001400116010350406104c00c03070000c0854006072004045c03607650001005562904403480f0300401801d45010203100c039103211680648140001044103014010000320062400101e807201e20b9101c4c0e0710541022008481c581002401030041d0f6418460030408419401c1c0d000300c00340c00303144204180f01d00d00300d40b200d603001e071500b00601c0302d4031690421040004030340791210501c4016404079070040c0d07940c503540046424402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 914455989 1250 914454739 914454757
    0x510090603030206090d05090a060503090f1c09051009090207170f09190605040308030405030d02070c050301050a0506011b0215030a0c1b02241303030305070e0402030108190503 78
    0x10800c80d00200b8190081640e5201c0e003640e40c160740350b5400d41001100c0a1003049440c540c40171185100f48556441607020b10f07440081e443c1219072011000c0e0310185892800b003d41941400c40491090a42d548a810100180b8059031002e40d816428140500401d5090046100c1d40c1e90100307001c403c0c002859901002151416400e66680c004074641d10004e0340460442d60280345002070301c80541080c46c4119080f242d9580d600d90400c1c0c2503541d0f1ba542c690010b001501d40c4d100c00e04c041010307034145100422099214100c030440061511040c0750a480000b00140100c13403a01c8104451642c04c5001c40703515041c0d4444014a136042c5100180f0458005e5000c0400c03a40e021081210a101640c482400b1625603280e90140c2c41181f114501c00c054030150094209800e0141001e403541d01c1e083d50400c03604003109460402040c0680c0c403002403150391065001940303074010b0169541c2c12003000780da1000191003c1d451907042451150b5220014150030f051502c1410303045003400014015661505 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 914457239 1250 914455989 914455991
    0x1b030c0b0906060a080619050402010909050705030a0f0e0a060c120501090e010b0a03050c010806041d1f0207020f090a110d050906181c05040503010c0201050a05090a0203060a051009 80
    0x2080c0042402e40d40c84045039220301820b00e03000042098030000680c140700344004140c008052446a20701409480007a1089040c011103c2010070549400d0140070300c6868140c0e62141c07a4600f0713150309400c3d10408802c186c1c90b5854401c540ca902140400e0b00602184c1154020412100c40b0342c0c220740c00c40f029528030100e10301d80400494640b5807034010f08054541c900013801002001001c000721403100344030051280c3d10000068029500034109182e002d04000c2000030101c48a610b480ea0810041c0305500703040d0801e48950800b1050310b60b02c1c1d0700c0007850b880c0442c1003418030b41c0440d08003103105084500c00d1031843c0025820104981040310403a03a4544080e4442d0100148100504800c0d10780b42c86500507480020503043e400e08803a845c3c00306020080205d842001c9401030691258903503c030401604200c04a0103480c24012102140800e80c00003401d80b628504402c12554050000c1c06150008214a40943d90000300350b0b410840c0d802d40080d19031145203680408480c0e5a000d1030901d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 914458489 1250 914457239 914457241
    0xc0f150408010509160f0e090703020a14090a11090111011d101a010509040c02011b0c1109090a0b10051e040f06050919021b0705130203071b030c0b 65
    0x4003106400c044d000c0c500d500201e41c404002c4412204c0c50203228003402054a0707501804200c404040e260721f82d0421003100682d001c1a4403034010a80c03100304c0341c21420107070050014184050a090400991199240c001042a440c240c21011780394403441d480c50b410481162001060902c0a612251a0384110051040d5410b40c040515807514203c0b81038801052602074020101c06406420107402c1005039a80d5180034850800c2000400701c45020f4001c540da1502c49100d02040789a01803001111034480910b05801440c1c10260a641e10031103500402100051000d41d07200040d6040a01d607001040c0c490300d03540c1c1c101481d410140c0e6403049a00090910700110a0402c2c413007070800b00740081d40d092000d2098001402c1c2611024031446802c001203400090300002c07108149251000d82c04009490060704101000e0750a44ca0a0210013641025104000925022a01c03c803c1040c4200a40c10751070b000e8405065155103211941c250741403103544000b00741c07151210f42c43c566440300da441c80b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 914459739 1250 914458489 914458499
    0x316140102151509070e01021f0213270905031b120d1e05040c05040b0f190503061807030b04030e130f050a11191404150807030903020c0f1504 63
    0x10f03180030140854020700400b804503040d05c0c17203552141c42d01041a0010541e180c0000241c0c242e0721035400c403480015500740300342400003002c124024018000b40d424a802c000032a403890002c40b100b0041032403610711b004003250000d5404815142c1081d088001030380480101200c0c0750420b00c1240d061440d0705d100050040c04000298490141045403020005115200200320340403070720f080e0f4020f4000da00481c0704014505d041d41000056a501078200c0710424602004528400901f2805102821a4080510250904010040d071002c01d41501e8803500c802c5074074603a15841c0c00c1c0001703000e00200d14001010305005201c8000303401c0014001901140c4c11006c1103006000c00f240038182c1d14180008648100800e00441c00401200c075001850912100204124894920740900c00d00144e00e9040705000c0003140070304010480030300030044030200090b0040481c1d01c01480401490b241c1000c0001081c4c3c0003584007020319080c0c03648100390340c8050004650406410550b42030020020b00401c3c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 914460989 1250 914459739 914459761
    0xe0606130803120721090c150903020907020307081602061c051b0310290705070e060603010e060f0d0c08070f0b032e150f0e031614010215 61
    0x4040c046502060300140c40751013040b80d2502100820a249101c1035140101e50301c00340d480508840c0c8282c034901c2c6440e550f4606642c40d2802c5139404408600764840401c158100886659440b88451000d10b00d4039003035540c1e03425a8010020f040c1e071f400009201074411901e5403421030300103840d0000fa1070f40c10303400d105405014103004c03541d0b540e122001c010b004400346014000c0d240140800c801c41100681805c60500341c0e0380101191a8a01e455001165080c5549074024048540254041c3c598140ac10341030301484070340a02034034003c4108000400445081800f001d802500440d4142424080e0b40c000410082c01400050407034034540d0341c001210400090450211041814822111560b6689010190004070340000c00826891080c449155078500f00705500c15000c07502402c0191074400c41115940c20171404400b090511445940746904511003480b0503400310010700c404c1205504200c804000c034445c3c402c2260a550241d04568024030021800712018000160340303180480c1020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 914462239 1250 914460989 914460997
    0x503030a050603010e0a0b160e0a063c05030903070605010b03011503090b2d01032301020c0c0f01030908030f34180e07030906060504150e0606130803 66
    0xf80b00750301e003000445140c0f001040c0341d4201900400da02090703564203250003540d012032103421010002ca0b03000001060b40c0e001c135040054102659440708250344100054442140b11281c060703a2007a440911607010489908005040ca0520380b0513140d031a8810b00e1fa16500680c0d80007800d1604241c0080341c44d9540c20040c604030340080110081002071440e0a804071008240040e0003130001400061400006150080c41041d001c407070100f180802409007000c01c20207810071105604c00e04a0700e1b0703410340300302c0c0050b40e01c1516500851822469000d0503607124000b460450041c544080c00314070503030203603000300710058004426680d6443c14604400c404501203510aa1215031007405101041c8081c18241245580c0602c408003504891400d84280207490422480b01030318060106085042019441c0203034030310b8030040360300c402034905201550030641102d40111700c1d00103074800800401584000b240c0e0440041c0d0307110b84680b004984544900d096102007a50900000114108000010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 914463489 1250 914462239 914462251
    0x20412150b0a0605030109020a0903051506041b0f0e13021605010c052703030706180203060f2202040b090705070b0a0b0607021905041a010908010b0a210503030a05 72
    0xc006240301e110400c01d458041c1c1c01948001501840148050b02403940240406100e508140005680d02d5030340902c1d011000c60801c11500480c2c080c045507040c58000c45103c00c0c900900102048480c1360010440c603030340c01900d81040f00e9041070107020740700c2e440c1d0400e4000307903c1400d541c0c1f00045080d04042c3c2c01c45240848196280614030300745d8522403c00e40e001c902042221368030285c408503009074541701d1020616818001045070400140c030a01c00c410582c1c00c40c11019040c1c5441d40105810040001d2508a03103841c200b0400c81007001ea10854001c40d280800025144005400400d0040c07180094a580001c0460207002c4056001000b0b040d10520408001e409540d81c001404140c690044c8184d410810610030300006281020702c2c0e40d07c8818800310000081e41d0303100001c0548422102560984100c8140d03640740d56488240700000c1d28504d00280010900003002c2440c89049200c0c80301c000d07403170300d0404a00d46001003130306a2a87d000310459449040150702c000082c0340a40c0c13a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 914464739 1250 914463489 914463491
    0xb040603151a0303160210030b041a0f010f02070623040305070e09120403030c030c170307030b090405070b0f1b01291509041e0212010f18020a0302041215 68
    0x4607500b41c0c0b07000400c44007614100341919240c0e546039824040f680843e0441402896220301030b03000c0c0390700d43c1e2203900502111840741034007150b0018140428001d00003005070405c1240021400482e40008121080f50841d1610b0707019141602c010003c009800c50b030001002c46d0000d000010b2260000e800e800f650344124080d01c003601e0b008051a66140200940c2004100500c02000882e00a80d003620385280241045d02c5048441c0e80c402041543d055100c0d20500780200031b011146625100701d41c045501a00d81030140c0c14180c035410768502042c03080c0c03107118100081000d161480c0d102912441c41c8002010148511000c072024042d03c00382c00c11086d03448903180c0c80003041140010196030a1406841b1100346d0f40a03c2080b0748550254060540080e2501045440d480d0071000000c20084d04410040c0c4401c5802c82c440b031b50400c1a07005520a446028090100704083c00c000e400b08404c0d00001641d455419505901170301595214960001200004005011420640840359400218 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 914465989 1250 914464739 914464781
    0x1d1912051608070f031104090618050d090305060402150c07030c1505190305041106120103020f0402090112020d0b18060411040f090b040b03030f04080607020601180b04060315 77
    0xa400e030790780581c4c0c42440210600d104080010408506185180e81000350001c10700c1c01240d241d0704155841480c242e8421110034500905014040c4404500510b003864419240c84c0f85440d1150b03503000240002c0c0c0310b0903107424082c2c0341100d2081290100324241e42650000b6070760b81008080040d0030310a4a01540404e8030301c4080b40d100d6400c0b1040c00a40c001100c64100fa0848100e004010050040396181e00e0a106205603546400281c203014008200c405110741c11441444070842100411314041c0d80180040d090980c1c201c03800c04502100080f005032610bc828203c00c001c1c5c11184500c0c2e80040410000ea0311003191240310034400e0000f60b60901c043d8030305c032449070741074412071042018070325880d40144409601e6400c03012940c04014004110300e202d400002c2e0443d440301c0b0498104100000702000400401d101c0d040d40b00c0790300e00190550350300d01813103090b111002c2c40780f20041959503050140c2d5540c03035520a801441d009402c00e2000609a210741009107a69040d800c64103248003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 914467239 1250 914465989 914465999
    0xd140705030d0804060b030705130f061208030714090a060306030b0f0108060105062101092702010804030e12070305011d06010302030a260313020a05011d19120516 72
    0xa07152004040b0340d42c035001da079513681c1c580c0390091101c00d440075454051010002000e64903400403803500c0b405640c0024a80c1e080b45c681804840c2036600c001040030a0101ea40c0104080c081980d50141d03860501054101703039141d50790924407a02d842d9a5002d80750190200d0b001e58140c0c408016a440307100720340125101d80301d00050b64242407040749442e031710480042c8414240b4801500c0e60114021071280303905100040d0722040e580c01d80002800d0369848001e81070b0400e0150b1040003148900c0303484042135280d03800003801e15400900c050284032005901200645a03642054007004181043d5800c8544a183c5240a01141c0243d0701c860140107111100281c800710b0018100c9900500621699200da5103c42547e00c0000c101e1818145d0080710a0708080c40700011446480a0855988054241c0c41000915a07003030f00660304000710101600350011050318400000700c002c5030703669440d07004c02980e10f202052a810492070b0514020f2450b0170040002034070720248d040040500300c10b545403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 914468489 1250 914467239 914467243
    0x1207060f091101030c05071a0609130b010509130503130326030f041b14150c0a060e0f01090b092b0f03060b0c06040311060601140c0c0d14070503 64
    0x110700103001d9150300010100d081d0300a5101e508444010f0900d541480030325210302002d0441034100c0482e04c0d0004e4100581d5243c003d10040d40042c050b003e05c2d183c103009480300080e0080500541c0d0069440802190121002c038205001a40d031050450741e50b447c040d620359000c18100c0c0b1045503499030b68035045040140321205140301e980d0074400c03a030440c3e0312282101c003c14405442500c6003801c013041c0d41091880b03074007040c02a00590404c0e4821168150034001d00d00d03074014201c084002c041c00240c001e4075020407030304490381e00994045101c559005030701c1d05141584140c0d2610350b18210800e0100310074000c03441e02c644414400e607201801080d15100403800c40b80b05841400c506402101f00f980d000f2030901070500c50510340050025284d49103001c103a1310495503c13000c0d0b4807010402041651024903a40c81c8203005021f00301c2402c000b00064014410b10094084500e030100704109c070008100110801920010720002119410342803d40c0f4451805048150314021140003168900700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 914469739 1250 914468489 914468501
    0x10e0d031e03021905070609020306010f1a09181b0a2a080301120807050d0305060f03070311060d0b090112050d03091e0503090909010209010e010903050a14030c1207060f 75
    0x13803107000303030b665000400031038140e4040f44049800c181d1724940340e80562000c0100f00c1c0a014400d2296032540d00f4041d003c68490303e6103400240c08202048110001d80361176219004081500000752803548030032181c1c4905000060180c20300c03d10108070017400d9980000540c1d00f00001c00c201c0300901e503841c0c0c488a82c1e208401d501400440302040100100740e00c11840b1910a8000c031141800c00c2440d40e210790804915031950030001c4e4403035062082615103d5102c10034414110014001b0303503d580d07514007002110761502d0f44604408030f0007420925150b084110483c0f0f0040100f0a40e40c2c6825091070206072100c800e50b058419080c183e110070b0b01070f00c1039419140d040352903030700b0000c1800303a4082402c0d500802194680410722545080342c80c1d8101c040d005280900003d83c507003184c0c074001003040c0d1032001036604120348002d080020a0003c038480c08901e1f04401a10102c503000d480c4240786100785802c8150a103d2380e03902c441408920b0020705103181c0301d00c9080c00448840d10401c0e0035100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 914470989 1250 914469739 914469757
    0xa0b0a0506130e040201021207030801180b010f03020a090909080d050906090a02040207030918060e070215181e030c16050f010827012f1206010e0d031e0302 69
    0x420005100e43d10041e403031564010b01c1441150242c0e040700103000440d80125808030003182003803005015140741864405c60a0400340e8081219000410000702603042e07035150007040c19030001d402c100300c0c0e00c250aa500501301d40002444081e0240c0b8060780790368065450280b000c0d10300030114001c054042159402103101c1d00c018040c201c802e8003080000c0d4005178040301440b80300f01c030004010444c8580601c003996103143c00a4000d241c1480d2550a05c4000c002004540191400511380c1c80d90241c0d0705d0300546014044000801c00301070720340ca44994a0f02d0012840383e5030b03006c08800400080208a5131500310141e803c12100400b01505851250280700c0d80070000041e10810395102d078002e15031041c0c0c0e8010f094203045e40310001031080c030146003440d68641d440c0c00b82c0c1005841e100e0000c02c032000740529094202c0e0f04006c50020030340984400801c50041160204815a00c9080008800b034001002c0c03001c141e100b490050010340852038090710a142000346c60700107a01034804d8403141c1e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 914472239 1250 914470989 914471017
    0x4110c211303120302070b0106020a0309080303070207030b0a0905011d070504050c0a0c061407110c0f010503013c051002060c03010b09010c05011406150702130e0c04050a0b0a0506 79
    0x2d045559840e003400000b40041e003015424011100882d08401c1460300030941c0f038025001c0380140d4240184035080e82d13044902e03a03920030424004555030020740320f4100d9400600441e03a5840751001e500c050100343e080540150300f440e00303000c150b04030b882031100f4050005e03045a0003260f4550500050b21401c0b510b0703070743e415018040f00c203010340184000c0310294030a07003000881030130301c503000b00102005540746000107118030b54000c0c0300d0004101500920000301c0701d840d08024030500081640c441402000359815a41c3c046081109400e1015544442c10042881c20102c02820840c0341e020f0511406103d4280b44280384174040c00810302d640100682056586540c1c2002c801c030b1400e034032508205040000129114011032030070310410f10400c01764042024181020030405c0315a036100c42c001204240300f00030031001030780e070021908944001514041101880c900703110b414182c0c118003843e0442e09000c108007020a19900840840c1d41c01c84200a01d50f0303c500900a43e40038190b1038039546 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 914473489 1250 914472239 914472277
    0xb0604231c02031c0201020c01141009060b1e0c030406030209100309121b05070803030f010602060c16060225020111030a020303130c0302030d08010e010909110f04110c21 75
    0xc8040f20344404101644d600016207001201150f0344d08490645044201c65400c103c14400e11440341250a4010704900c2c00c02d02c11a410015620458442c424071007010035020034018a203914441d06850b00041808140c03900c443d6108005000b0354400c3ca41503101c0c003415240700e402c0364081d12a86281a800200718040902039030820344141c5000104000c20586443c00000010001c2000c2000340030170b04081c54881c20702410089280d13006070011405d64010308200841072801c0c030300744c030a0809006d64a1804520606003200284100740c544e04d090503600040c11002c140080003959a54801e985200780780c002d001d24662280140506440180c0041000c542c0719031800f0141038003039014031002c5034090354960010745851492042c00c00480c8000004015001100203885d00401d0480b5040c003142240d551200341030010480c85912a441c00201481191030300d9204040f07880015241f00e0351003000c05012562400010010009403150440c50603002c28030713034169031007189000b4058802e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 914474739 1250 914473489 914473513
    0x3021005162304060201290d0f1505010b0705060907050a03060b0a1e06080606071203150f060c1509020a030f150212040b070306060e01030b0604231c0203 68
    0x412040401100c0d4411404a4200301e8102d203500400041585400004010744958070404e9000c0c0e1013203252206425086504803a0b482c1c100c80296019481104520038039850303d04040c458040001824116240c00c0000c00d0700800700300140302440c0120b04a480d20399030440d250340d0f120b800780510340c1c02a07240d950800c00101c0d80e800800300220700030512041151185040d54000c800003103100500729041d181081216001540c00343c11140550f49507280500301e03160110441d610700749083c20959185610781c00c0070031000a027400382004183e50490103a5910b002842c5030041d403401e0355000b94940c10680034000c1032245000300c0354050185001c1c10701d107450301c20400514001c140d400141401c0e454251031071900c000c009649103c4111149810075042c03a114404000740f048040c9450314030203100c4640c004007010300c072440074a000318082d0340c0d4902191087c0115801240608116840000e0410410407035184080c8140e51529040ea000001c0103264000b0000194058200c440c205203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 914475989 1250 914474739 914474747
    0x1518020705030d0f1d03030105060f090f1807121b0e01140c1e06040b0412051b07090c090e04031202070f060902010806270702070b030703090302100516 67
    0x3600c54090320940741000c2c0e580c1d065009480d5a2a000c0303010701c5c1e0302c00c2401ea00000003d11102d20300010801142158105000f1503c903101c0e84800c51031856010454050a9581a80d60800640c000e0100c000c0d18941d20810380049800303580d5040405c5032081d0078001c6054a2140e0010b0940140c1080d03404045401700740d40d80007030010502d042020441000c3c600180c908006d0040c200640c0040500b903007c0c1a0001e0501c14800c00d10029802c20018000460401c640d000d81080c0c0164981d00201d500502c15a0399116524014040b0203c1e840352990201c40400c001089411440c01801104900b280480d0804514020607042c2e02e420303c049404248644441fa210340e803005401850148692110700c00440401d2007100c1c0c85485610380400c41d40d108400d02d0700402c003a103180f60a110440366065869004415800c244600d040001d04154400c022150041c030807011825500d0500c04c800070003a01a9510035000b40c1728141266002d05568400c0500c2558400c511401c60610944116 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 914477239 1250 914475989 914475997
    0x602091e100c0b060918031b0d08040819020f0f16060c02010f180b19020721020f043305060f0d050a09060203160e0904032a05071701151802 62
    0x14030b000b01c4046d00a600400c20002400d081c3d11540900030305403414800d20f0324000030403440764204980d220500000680b14029200680340c4031500401c400e00c152001c07440c1c02d08400f00c0400714482e6528050f1051030204030355403181c05524000096544414007a100d29200303810003030001d038a526000025034032401c07144078481038030414661aa5a00d052007141034002d5107805014407400718184461039010840700004240900b02c0c5003054400c41d10942001d421000d0180c060003280c140c07210585e4450b813000c484100a90100343d2540103080d0340301c0c3c1d00210b5165803d07009500c4040401e00340303400c8040d0303020300d40c01e510628038000c801074444020b40405000765110a407a12011000202c407400034500c54120080d00c0200411f00b800010b05040c04844240c4c01551034100b84408039521680d6000c41c6c1c40c1e06400140505511150748011140800c0085c0c0705000b0500045400340000715010711140e420702c02480441c52085e40d4011015151269040c6002c0e00160f0109404807500a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 914478489 1250 914477239 914477251
    0x30206070f170106090602011406030309060a17090a05071d0a0c110d030b0a0f0302090c0a0c050709050708160f140c0601090c181508040602091e100c0b0609 69
    0x155424100368007002c0c500200ba0482004240c001c6018081a80e0910990040103aa4074545246051480100e0b03202d100d800c2540e4042e1000140d4110002e02545030441c41700c0414503007141e98984043c0490300e907000344100f00d03130501075a0b900040c512010144403158680129a6202e251142d002140003000302e60900018400c000e001040d07101003c4c4011000100e0540b404224880000104100c204050b00a020b09c00750700c41d428809a21060742482d03104000b080130b65580e6006901c10f642c0070a039074100511620a28402051760111038020502507071541c8c9a13047e02e83c448a0304001c190414030303000b800090003c003520240c140710b810110b69103c1030001c80c84ca84070075000101e050079400d810030012140c0720826446815400f50b1405a01c45002070703840041ca007009802040451490110020400100041418881d041d03044402032035000b0a6095021b8180708628545030003c0e64151061301103181039081c490280072141c660f1940543e025015985071010040c000c0000743c03030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 914479739 1250 914478489 914478497
    0x180106141305031f0c0c03140a05041e0312030504020d02150c160e010b13060c080d0c08060909072d0f061101200f0703111605040f09030206070f 64
    0x10002c0d054500344110075004407459070740c900650f1111550020b5920b242c1c110000c01120783c102c040400d500103004a00b10315035540d0703913030b540000100c100c8050140740c2001d952209818509141d41845110180441e4030505041240c40042101941181e10448019400400054042005151030f50300890344e10700312a00700d410600f104040c18070300441050244e49070414044203001003004059650f0040130111000c43c0b5008103c1c08600c050740c00d6103d201d0521003008031580c200429001a201d404401c44c504200d424481940200b00322019620b80780241c4080780882c2180c0c00c081070768010b581030150403440c2030791700d9060900d10000400f0b1000c88906095008510b100300e0114000c0244500d40c1c61000c9081600100c1d42194410b9401d4200201d2212a540b140c129801c103030b03031400b031003696615202d18003810107440c1410840e903d2040f40c000c42c1c00000484100314040c009549040d68100000c001403000039040700d0700070030041c0159000b2030001c1c04c042e00c20f00d9400ea0000b031902d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 914480989 1250 914479739 914479777
    0x306160809120f040e01080c061207050706020304030914030a0819030204030f050c091005031b040f0c0906020f0c060922050a09030e01021906051b040b040518010614 73
    0x301030980c0b40c10030f54619030380020008081141560602c64503000d4601d200103411a03c12810000e5010311901402c802c43c8401000020000e5028109452040d50800002e55403131070913160052902c985c42c040c966208102450190480c1000030344c1c0b02025a010283c1c0346051000000002c080e80054142401c0580801c40840040d041103040c207401c41c450802482070000e0311081201e00c4200400c0c2041e540c01100e801c00290b50b00080840d1030900e940d8031980034544000126001e01154800244810309108a91400d44d52028000c0110303041c65003035404c484690342505e620346820190466010340c0510800015103400004443c1301444102500d0000010264000603540126041c413000c55849261006254000c800074207501802d1000e000003a00c00803004000f025400c8014145660f1a400070f241c294448000f10038600c50100f0300d5441c0c56643c0d10030001640140500ca028205800c400f001c04142c0c00b409606031401c0343c540b00109026403c084125030002c400304409c0c04c282c80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 914482239 1250 914480989 914481013
    0x70c2a090506030a02120715170a0902040b03060f1803040b09040f0b120610050a0509150f03010e1609140a0e030d090305070c2301030e0c0916030b0306160809 70
    0x180400b01032954100c091f05134149441c1500150420306002c010030f002c0d03100556011001040c0c0c4040d40802c903d1400981140303130f400814000c00c8002c03102500b5129000600014400c80e00d0b00c0c2d07210310034040a00c407030074151041e400d44034001c0d031284070441d52007440001841d20f031035000051405c04c5107000103200455040007c01600c0c3c01c4c0f489103070942022080c8441840c4d05100d050283c0400d58500d1141442d207000302e105028001e007088040c1c410411514919a6031052000e08000001c000780070344a4401101602c443c800039400486000b00840095656464051040c0d442c08410941c6283c1c0c0d6075002308000b03013402c880d500943d400200102d5403440c0d5076104d0006814040d541e0f86032520281d25004603188955000441041071403040c103c030550582410030400d03002880c0200300705030880000b91500d000c030f11006910003458010030825144080c1341c0c0160701d03020750f070a0041d002c18000b07142d2100c00c1518840ca241000342c40e1000014000c07178200750081d0000c8211628982d0700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 914483489 1250 914482239 914482249
    0x90a0302211c030f020f0409050a110c030406080610020a1401090c09020a0e0102010b06030c090a05040c050c240a0e0f0109060e0127020f01090905070c2a090506030a02 74
    0x82d080300901800301c1c0c0d01600710761511400194402407081145464000c0c91038070030714080c6128000711141c940700054ad440080380c111170020941201c2968869010864140c0c81c0d421901543c400a500701d1300140040c40c141c065080c43d40103039009018071071902c0d154510103142200d650f140315903c0315101000501001041d400501c0c040e0030042c0c8654402c0341c028144508125010b045a0610b504c009840d0341b6001104c0c0c000d078032241c80b01d507034600d0000800c03040f4070107030302c450b910502d010b460405840d008001800d10080103016201c141e80030340d118029001d003501808124200e2500041d1000d0700d990700110300d200d02081203548885400304402c1c20341d038541d58212102a2181c801e0b02c00c1074001d01807018400724400b44110941d0503401c00c42802c039a84c04002c0c2c41600c01d11160302103230b4098403291000d490400421700032854a803038050000300700e140c01212403010800c40c08162111490b10400700d42c46a0a02c841100d190001340d1003c1c1ca030250140c0e03454040c5025000041c1c0d59 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 914484739 1250 914483489 914483503
    0x609230c34061b020303070e010e0310020f030a2007110d05160312090812090a03120801030c0e07050d0f060503100e010f1112040c050402031515090a030221 69
    0x31600c800705035241d0f02c80c1c03c034a4980b501c0b5084010f5510a00600c00c0081c0c015443c45008902881c05a205210503030009103041030640e84c9200c01c0e880002c480c201e04140200840c0b0440c8890024070986007403d41426007050f807d0b008649009090248400203040205124580e08000307102d0f503070349041915103900308131f040311314117188a501007010000c00241e9500701b0014040d03810700e00d0001e803420480580b1640080e112030b074444000640b455142c1d4824030148051500150000d0450b841c149000e0048802070005540783c2100c9100002d01e40c01d2a1401449001e5541c1c555040c245c15110321009401c041842c00b4040e03848400c041620346007000412450340c925080070842c0c00884043c103084410048260b101241058100704000715004100d50030a407401c0b200c0261a900c1e820302c40144500354008a500500010500c243d10f0802c418680b8960310031203000c0d01c00b070403010200d4a24441c26049940111129600308054580310004140c650700d04012203145045401c0914100f0724 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 914485989 1250 914484739 914484743
    0x2406150302120a05010f06051b0d110f060402011b061b0f03140402030a0b0405010e070b040e0f040b01050d0821010e0114180603030d0609230c34 64
    0x140c0490480d4510b055408482d800c0716605008201da94100b4406512011880c01820180140010015440b03000000d00710110500042038403981045494000d0268034031900100c0207120340302c000200f10f200404c2250203182c0c16101c240504004c50351206982d10001426281207984d28a080000621400c0c4d03000b0703080040c2c1e5982c220003226032015040ba4100d8100b00c42840c8c20004220040e1400550200d0b4690455040012075a0301d18269024003801f002c40782d403034000c820000a10605c10307000340050303c00c00c00e46c001c4160b80c1e5200c05000761404940242088601c5801040b0324180614040c0e081405411058500710740800d4503a9000e4000c0006580c10240b0001005030b91003011456014242c03e015030600c8024100000e40c6c5801060421002d004081001c20070595040040300e880407010401404865501c01c4000e000700100d0031007030120303e40c5d141e42c4141d1040c507003401885110304820050030900745d000e480c0701c030520307420080880c038204410302170815181d10300100c000c3c0c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 914487239 1250 914485989 914485991
    0x1228050c1623161d13150612020109080105060907031508121b07060203030705131805070806060715020d11030c070309060c11040b0a0504021c0c050724061503 70
    0x1400060038001c500b9160742c081c12101604584c2c0320407118400b20000d0304081c0c5942c02980481683c01c10282c0c1e000d03038203564000140b07400c10001c1c6645c0403542241e0014001d81398200182d6544451740d007622002c275a0b080d8048102000142d505003e68401c05070411803260208506440b104068509000403620b18a00304000c9540442840c5c8a8424096495550301812643e0301c0c20802035900d004c060500418400e006c91203000505402d03041e00b00404030f11501d0721000d041d01030004001e04082d203a4400103415100051440d0038060700300d40810754003007030b10103203009000b50640003504070340018004207840341c0905803010001d42c0518011a603a508903a541e10080c98043c08100c660340c00b0505010311841d400000c50004a4110718000e02a5400f048640314400012900c203184e40005620901c013042c0111081d40c410b41c6100ca400c0380045c100085103030310005a80d1401034a00041588100c0078000301c2030380c016032041e01850750010001c50b2543d101c40c00c0580044041740076400207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 914488489 1250 914487239 914487253
    0xf04140301061205070306180618030e01020106080703080d02040e07050408060105150d1509020316020c030c09070f02010b0d080d1a031c051228050c1623 68
    0x285420b1207070308000c12a007000c1c2c412244a0b40e880c50303183d060320300c0050115a92859200079004640c10390309070071a0700000c200040701480c0c04400260328000d0f03090300043c1d103194030008194014841c0c441600c4115009080007031031a034940c1c038070b584901072000301c80381c0a00c000030794200c162894030b025490703c2c0c8941e0388640c1400e000b80d00c4c2010513071120f40b040518013459404100c0b4078040f00c0130500910300100341000310307951000d044d20360b5030300c0421014070010800610034003625820b58001515429a0014050101019554240f9010650788170504070040740243e800382840c4240e140c4280004100c6421000c0002c6515401c107206540d0604e0014100b800e140480c03184d140312081d0450304d4184419140086680e42800080e030b40b02d04420304000940080c010400d40304004120380c854030280c9030003074000c0c4c500c84009482c40100c0700b202c6400303071a166940c05076900c07a1700b44803501e1342081081154186403030340c0620103440c0c00d1244500351012140d0009002102e9201000404c20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 914489739 1250 914488489 914488529
    0x1020c1603020112140403030e010e060411040e0102040b121b072d1115160804080613050a02221a0109060c03080a050c2b150e130302030f04 62
    0x8680001312071000740c6182c448104002d040300f804080e0025010310700060f08200003040c40d40100003500070301740c0d1480b480c0100410030200d44000d880c3e925055600b4884520030f49506401d034010b41c0204440804240402d000c0e85444c1c994241c1d004800b10246c8801f41002c480c1d01407a0340c8029016541040301150652000c603462409500c854018084c44582e00307003584800416900f03c030303d01c86c403440a51130440c030400f6070102541d040ca048140d03207501100342444c00a0255000c1c0c415511903000300c07800034142c803440115800b5529001702c058005c814007a82000058071b0003c45c4a101e8211100180c1c4e000741e124402d0022840b02000141415100407001410940c100c0e4041030400540e9461a00026400342403150004000700c00811035840c2d00c01c41c0d91150041149131504482d5800d8682031106c02c101100c80c3c0310b40f21003810000281c001031880d004800d10b004841240c200d8001040c560346140b441041000d0184c41620b0404400780d02c1446581d105900c0500800a01d001d1240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 914490989 1250 914489739 914489747
    0x303050601020735100c0203070b0c03040213020a030216050609071403070b18100206011505040302060a0f1808010c080c1206010f0c0507270b060313030201020c16030201 75
    0x30107003890794210381201130200c001215610f841e0508a40101d1281045035181000304030982c0e0744c010820040c803500c11043c600950b00d8210072815a03207010840045140c8109000460f402250003411520805001d1145d5602940c82a40c11904140d0708026205c4511410304d60000760718410005070140381400c4c00318030700d000615001180c13b15150090303003800d683d00240d500100c601240340d05440740d81b0b0300200d1400d22921030f803250300140c0e40124028084d41c08241c40e07041e00c84000e24800300ba04030038011280e60007140402504000c0400c2401d200c1d600405101c12060901d2078042e10341c0000021a9003a801a0b40c800c1146a4482410b10522a00040044d0f40104255041402e01940001014240c2009826641400000068801c02ca07100c6e40c01c0b03500e0b085d000400c0324406036031020380010343c1c201601e00920401c154003907214503001a000301100d40030010111400c60300c1c0c0029400d22101111802c0703055641c00c0011030018007051007a8580b412400c001155102d1031800094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 914492239 1250 914490989 914491003
    0x16080c0325060f0b06031515220605030903161514010503011a131e0e0601060306060318061d0f030304110a030f1509050f0609010b0406180b0d0c03030305060102 71
    0xc2031905018a000940e100c0206891f80407040342040c0101124000129000d1020101000070124002803852248070303001c5101004051347c00018241c043d03840004503494042510300242d213410402110a0340b80c480d403001c2a441d4000c50030410303201410043e80d01200d65102d480d030a03200c1c00100410043c0b50a1013110b001400039020f801218505400240e8407440030030001c0a4940e544102c589000b88030364000b0202c81258204010945501003034659401d0248102000079082c0440071400300c0c0720340242d045001c200e0907403400e14142a070f1100060100c408010410b924001d1000001100400c0a42d10095000c00559501d00740340c20920b08a5161300100f50040b11101d000f0000502c0c1e01e449401041c2d0007400c40342840b041e8203038510260141180140c514401d620060044500100780f5502070350048008010910301c400500c001d450062042003403003280510f894a0b07041458100f4040081d0007008080080344039510403100189a030000d4001076560000c01c121544c040243c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 914493489 1250 914492239 914492261
    0x9040f0c0912020612040501090b040317070e10112e0c0e090c030a1b0f020705120c061806040617101505090a050a0b07061116080c032506 61
    0x9858403183e4000c51200d00ca01070142044c80000c900003401e015085d4800c488299000c052610b403824103007402084411803051403014034200e02c1c0411000c602401210107500703806000c064130340c24040000d039140503140035100703894003800e801c0034600d1070f21003482c03040000598000d400d4031a9880008003280e540c04028001d104418210b04810794a000c000c6e0340c0180956102503232a590721080c6409092506074001c540344a141d008410f280c1c105600070341280240e4201e60700e2941d200208036040e00700b901307002c0381c0d504810628212400c05800604121b02c042400454000c40c2d0000300d02907034007e504c1240080c100c00b4495444400140e00b00ba00041174107800202142032502d142c001c0201101e6104c188000014003915075181c0f5818a0000c26005000001c01030f62058051410b91000104a03035040c5010304030410420900141c41c034031004200c905030f10b0b59040e0b40d10f0700198130004491580c0d10040c8401d0072056841c0040059440190a03664688150340c80d04000b43c900c11010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 914494739 1250 914493489 914493509
    0x30307021f0504170f13090606080708040309061d12030a110706090b0304030e030a0c180e06160903051b010908011e0f091415060a030305031b09040f0c09 68
    0x42c00045062130794464012802d55001607596280483c030085944900c0880c81c1c00003040c2d040006481c6c0e05036002804542854480ba11296501502250112011280180440e04812051106620916514810840c0c103820340500c9000030300041d024400c0b07080003072020350001400e00b0b6025400009a840000210010003010307007030446c050304019081c0210741c00f500707002c030004040c144290b5144150b0b0b03002a05032581c0d41d12034106403181d454680070300018184407c956030050703229031081502e4000414090843c3d600c840015644005e8405c0c038003800c00c0401d88005c40401e4081c880e8003000149441198001c01c0104009403000500703900071744060b41351a55001000c0e4110804258145c064140002c5102d1845960001003000280103000040c1a194028030b28100003003028285d06090440031003a62200e04008003900c0502000300000c00c1440850400114948120500c10742d9100e10b908203400400420200c0303c1c140703492791041e52640b0040d00c900e9000801c0c60050440c03481 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 914495989 1250 914494739 914494741
    0x1204230706081612020d061e0b0409200d0c0207060908030d090c0909080301170d020a111c081c06080d11151314070518040311030307021f05 62
    0x8006010030000404501c3e04011003640241501d200d03080401012110700d0086451b0003006682d034001749424054209103450b18500c810310320000c1c081c807904841e002035005103010b0400005001509010030140c4191280c84000d66042c070261014005c01150704000055881c2540c6d0300920b4000c0ca03030300030400c1c001303502010720445d4808412500f03a211a81400704200e9072610b4005c0c1001199403045004501e0908190200040721008504030f58108000d9085820440c2c4d206454031801c000c2000980d100304889800030f0149103000d4040100100503c00a00005030b03617268100d08100202e07501403001851000c218003c0c1c800000f00e5614a034208040313414010341e1079030ba030bc03800304110a000c007080c2d00c1c690040c07003000240c1001256190420503405e180090b24544c8680c14401c0310007860580340d00c0040140016441c0032114000c15044590041c14203080e070043c8092b205404100e010203203040c055100b08003c42c006c0d00340d0f0f80102082e502845405e0b0101c459000301b1302c01d03241420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 914497239 1250 914495989 914495999
    0xa0209030c0f2b0c231c02060309010f0e15061908030a0306080609012c0102040323070e0702030a08130212060a0b09040c0302041d0703030f0e030105040f1712042307 73
    0x5c0a448035a406441c014a0f402c000d0f030601580601526000354800000010001040010f41040f00901c003210402e201981080c05a1034035207400d011030018618481c80002c03607503e09150301000d50010841004400740d22052a0741c2907501001c031460109854040c10011040c0410a49502101c07410080103d93301049428007100c080050464801c9143c407120450150300394115402103a100c15480601a090540c0d41140500080c0c140d050f80200d101c00030320125003070621482604294044d5151100d408416118a01c0c00303401100b0f1810140c4948005845107500e0018600c540c0c80148160302c1c000030007000359031400498034000e00c1003105200014100c2509403007643d60480b0080380c174403450191810880000c218031051445800c0e4000b00b49074200c42040b03051003036a9505041090080e050609a88040c0c8009200e80c0810701c103880403443e0a0b990484c020ac003111207a02e405040c00b00c820042c501640c5c15940140e1403144140c000040b0521000b903000800068070383d9524103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 914498489 1250 914497239 914497289
    0x6020703020108060f0a0515430b0109050705040801020c0601050405090102041409060d0209010608060411180d11060d051e0c0307050c1204030f0b0a0209030c0f2b0c 73
    0x507100d11230081c442c082c0342d1041124604141c880802c000100c2c450440ba10145450711203240600740700100e0007000002803694121038840ca2400e4010390f0041540c0d00e8922020024034005140301e081080501001c2400d030802e0009200e45c0d4400801401103505040c100400c4441c06860001a688100410080c2404000e4546079a00e01201c18208940d1294007265080513030860085d03010143c0400802d000340c0201c1000d00410040d1410030204103401d41101d1a803186040311225905e0390301400716185801e200034000380c0d01c218514810300b8094000309805410000c07050030f6454640041080f403090500c035840340d030907142c25490000e0401806c021107922002e00018104600010390313100b01001017050802400c1010300407a9901c0d82ca04009070030081850048940052100104070003003003e0007654543c460040141603d04102d0301084014140c100000b40c0140f080096002c11009030059414446003800c1245e0035860340707140c440700c90711081d00080b81c030100040c2c04075090450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 914499739 1250 914498489 914498509
    0x6090303032a110c091b070203010f02030907090f06030b0c0f0415030509010f0e0d110c13060503160608040f0f1403091507051213090606020703020108060f 69
    0x141c100020408440001c65141004a400400c0010021203460003150f60280d414440c0d039481e0000c0e2002d991002c2c0403c4410f0310155220002041519560007800385c1e00700042118500c02400020f90030f07020301e20f030400e0b41c0080382c170710300c2c142c000c100c0030000e441d02c034000c030000c51040400410003642595108100342ca00a440e80c0602c0d400132548450302c443c10000c40c0d01500c2242e80000440340380f10401000751a0403038899080d54249480d038810321005001e50804402410003505017490202403c0328940404480f2014030300c46c20200c05c0c0191220b0310118000d52103a44082651404d0034185460b0002d0b50407a00007000e08683c042001a901250b40c98203e40d105940100401103070511221807804d0600241c082c2120350314455840030700100410140e0000d0720b41c52840002203e480000303008586024001da040002c084040f200c4500080203401440b9a034030306103588680f40d0f030046400315001f850160380221001d2081d0b68101d00c4c001d41c002c00440d240d2440000d8807012130b05660f4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 914500989 1250 914499739 914499743
    0xb0a050a0c06021602131a1509120a2105070f08120a0b030d0504120204020d18060c032d11091215010b09030303010e07021507030b0118060903 63
    0x40125811554500c1010340220068104105548584240400703103d55840c1c01d5040f44102106c0a000344662081e01801c0309214690080d81041c10f803800c1480314001910f842d05006e50380402c0050416580c0f9010300b10707802050f0004269852851800104080c074841541c1105518410041d810319030010888452030f0344000411441c44113480c0c800880d0143e07204104a012590b020801d401e00b20394020200258201c0403241889100001a0f6661042c1c0c002c503044011400c1c042405405c168000f044095081e54001440b516001142009410325460440d65142c0b26485001d0b07080d410301649141016400c03c40c40c41c070070311041003131405072050000300e8003a40307030116a840c880030401a03c4903500040e14808148042c0300403d0f4840c0040700c040c40c1d41e1020303500082041141c1130305031800d0700d20140c000d601c0c50b42801403100c900400100034400f1440760300040900301c4207503c20035014034080d40b00814500030960014150881010491420400100b010013490741d2100c1540100d13030b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 914502239 1250 914500989 914500997
    0xa0221061512071b15020a0207051203160203070e01170c010e31150612060f0308070c0909030512070e030622120206040c09021908091501030b100605040b0a 69
    0x508460201d4258425295016210b05d00c02d141c0c656841960750010600440d044e42030300e80c3c45898000b003060000c80510000320301c0e8400d000300000e03041e82c019440d02c900d00003001c41d607019175203982c902c00d41c20007604807040c90942403025000a041c10044000300d803000b4200400f00f06e5220010074801514001c4491010644c01424956a0135042440c4d104c828244014444100022619417030100c0e6880384800290000105205a402e2845040103032504040395103040c901e1621692002c1c0c011031800d8411041c204c0c1e0010388544588503c40803a482a155691110020f010100e4080720051010003071219103046040617507000320f0000d40c0802811644820b880c21115452108400900000c1106509d1511000c486400051451150b4811080c20391000d8692101f035041e0b008516221080311100480e00086138052034202d640160100111044180280c1036441c0c402000e030300940340b994502c0c1c00d001c21071800b00301d101c0241181c1d007000c51600d40f410304000c00911175403940c0e04c200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 914503489 1250 914502239 914502257
    0x50405060720070b030115090b0906091201060f0e01050f2d1309140304061416080714010612050a060e031605030d0b12030901080a022106151207 64
    0x888507a54508020740a034112000213407120046845030b4420b0042c0c1d144001c842a441501501c104020002e41e56608115414800d0301c2c01401010b070010900182d002c0b80c69412403201d0402481803500070010420080c400916000490140c410181c010600910640c074a11050340c55a000f541e20203c050000c400d5400141103689040d40c4070300c1781c4503500645400101510b11103c1e00458200381c05024102114082c951400c0c2d5070f80300701e00c203c4004c9001c100030132250a00502c058900880702240c0038260355016560305209a00c072800880d1062640e0141c00500c400901c1031b280078002c109451000e0110a031515075403100d142900504003911520520347d000d81c24070568a461906000950007081d0a02d8050b450b90012820004454548098044207117045c850001840300074038080d601c0c2012140044036491001800c0c1c2d401e190f000c000880001c0c0095940d1032001d0400011120300e13003040820080b82e04c0003400380e00e280400c2441000c1d88a0212200075800c51010b0412030b0b41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 914504739 1250 914503489 914503517
    0x105160e012c121e0106030317090c0a1e050102030a0903060b120114010314191e08190201050c0702030c0d060b03010510031406090706031a09280504050607 69
    0x40100b4101c48680c00c2025018805903103000021810031499103c20301110480c00c8a004600302c0315144405000291740e8a0410f84030075035038050b541c1104100341541e01340c1c110080072481c009800c1c0c1c45600401d00f14480d0041d410581d0342c101000e4002417025528241c1d04481c000d110652034003001e4502d950b81c5480d0f6030030f5542c81c041c031038074010654000e21002071403080804040400344401d540d030750201d400ba0018060041540c04c074400484c00c000f030340b4800d981c0310180a05003010404001c1d81480210501041880019003a49c01d984000045540040e400080c290790b005001002501801e20016006903004515080d2040c0195070702d80c81c007101814400050108050141c0d05946018103010b0084074400036030082d203000740114981c44203400c40c1c5c42e40c0c0b40e1040f15800c106030400e000c00d211080c840d400000760700d000d110b00710700e80c46140e43c009001d04500361180c01504401a4012121645e2145201006890170304100460301d02511010313140e000c010105010008800c041c155 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 914505989 1250 914504739 914504807
    0x7050d0b040f0e120703350a0c23070308091f0f060b07050601031410020f040504060815040210140304050109020102011a03070510090806090105160e01 67
    0xc8040052051002c5008040c04600400070310580d58418060301c0920040a001501150b04071940350b56524480c81d1610401445030011018009120102428944950a42d14042c601400d14540700203400c03012a00d0161400e82003900545410701c415180079840315112080e903550a0701820b022405646460411b4109401d881070002840d01c01409064480ca055202c60801d1a0b600d0041150700d80b2102000700c40d00501c03a00030481c0d80300c0382c01480000e080500007410f03044000102d6091080d44880c003426038002d000050810800801d0401c410b20b0700703004150051940001800f9240c0c0c8544074419503120080c0064040d50540301e50007101841107480e00e01d900380c8a460aa121708140c54031502901c103228040c0d0041d800c0a400900040078800c5914040000900a00c2c5040c5400c0900c1a841c13258588582484814080011101010b10590b4410f050030000001c40e0b01d0005008460004458104002c2103801d801800490760021040e203011540141c60b12204000e10040c49 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 914507239 1250 914505989 914506001
    0x306010b0a0201060f140114031302150405150c210a0e0109050a06030e0105060901121115070311060901020f030112060b1203040303110d0c03050715090c0512070e07050d 75
    0x1445d0042d00e81e000124042d81c40c044543c802c5099a0305806003912038441885400295003506c1041d050300350010052405e80710b0311100c007010000c4c0e107040c80c3d40d07400054803407000744090041501c4001003803103090f00c0910040031020891000386000300307641c0034851800d000b4280c000080c0700106003d06070a030f0140308070800400004151210072038031041c00801829116207208001c0d800c000200312541340481201e4181d43c0c101d240c111000c1000c1c0c4070040d5060241c21141d40204c85040740886004c02c02d401850200e00903103c0e61140c00211900c1c0d443e00780c0c0103101c0c0e6000d0748140001c0424980b0042201c0c1100c1c1d0940d0041c8841803682403100040ec04502c4c090780c401d080d0140d0441c00500400030700126400394aa15a140b0030301e100841c3c941000c0c40d070702400200b4041b0842e00090148001c2d14000d8000d100462254058008070f404584d004401a29000c507003410400c420728000104d01d040d086018050076580d1702e032094101503101d001d0081070500101251018049c03103035511407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 914508489 1250 914507239 914507249
    0x4021206130b0a12060c09081f092001170708070305070e03060405010515180103080a2a122606220906060b070c030305090a0312021c09050306010b0a020106 69
    0x20865081d51140d021030b41501501e4115000e904186c00b9402140c0540e00ca402100c0540024008400c95400081d034049400d007075540c461382c0e0341c0300e030500441c1c0e400500c02060002c4c0041001e905c1100340024020520b0452603038500c981c1d00301080840c90b4080e09030303900090b03070703060201d00c1c3e480d107400070345015090094180c1c2507c900d50812040c44015086036004070070b418401040c107131103802400552140c50306490303210212040104000380358035005021125581c0740440d900c1451500070301464184400750400000768032442020f00a00350300c0c0c00103105e602d0a000c082c00828022400c420815010b0300403c40c081c4c07000040c20740d04c42c0c00640310080ca03c10b000030a005a0701c65030600409c40c406040d104d807440c1c40008514030030361104807221540c00002c5009202e24540e400c40d803552002d4442da4204d03030f600740004000707140308110700c0f404041900507003188514202c00c0d06144148050000400064140c10043d40e00c4c0805c0c0141034a000c608c0b525502e0100410aa005d002ca6603c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 914509739 1250 914508489 914508499
    0x114100e040804150e010e030d090e1f0305010207020f061c0b0102030f210105032b0201021204030c021e0a0e09030c060c0c0616140901021c0302070c0504021206130b 73
    0x304002407030340705c0c41264911030246ca0351030b40300480c502855503c07030f8000003010201d6045941404945608841a170740004442c14081361807030941d508018480741a03004584e96074003c0703040d808510b449a01301078086415500e0a050103184500c0c0d02d403400c5005076403407209a6070203144499034400d20486034500c1c1308039031055407200141c164002c0c00300d1821804805101d814004207080c900801c40d0340200315038518000300450141d1689900c400c03d07202ca0b0b81999400c2008100c1001301206e214031441c0a40c41d0360503081d45600600c075407540301070703c800c1c1c1041d040d803006540307a0740d072004020903038540c4101d80c10b05613111805540383d440f070540142860310802c42040542c0404a000b0007480c50583c00b503800a45030880046a03203190b40100794040f030741c11485541008150700c040c09030280c0c144100e482c801801c9060720740204030f41840c81d00094000680c1018444030343c400c1e10040009880031490469450040619040c01411480c401c0c0381820040750500301c0742d00000800741d00140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 914510989 1250 914509739 914509769
    0x118030605101a0c0f0c0a15110a03030c03050a0c14130f0311031509120307031b18080303010806060603130606090504021e0a0e0702190f050114100e040804 69
    0x340103c0940c10218090042d8414185011010100454502c1350800d02a2042000d1070a0a44e04d0802e58201080801040340c01c0300100006801045001da0160094900250b040368a01c0000c099507001800b03c4800350914016682183e0b025052440700e040f1015183c2e01c0d844101050b0304118050790280031641d9010398044140881d462840381c032641e0440480c3d074111600d000024240d11304991015280d0854500855401072803401168441602d207030000703252500c40c190411117408104110001841c1c0b00900520700417840e0b4220141c0000d03c001d40c103542c1f4200c1d6080d600c01000701030b98080c2102001040f84802c010b10400071740c030f51056041c4102c64607100403000811044405070322030740c0540000d094405155a80105902014040034038507404c1c861038050405024107448214800e8910416180382041c42640e0b919101d040700745282046802d05500351340110800b03005050b4500c0501c142202100341c00c5040300c0071004540031035a40d90810700124021548081009000c010f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 914512239 1250 914510989 914511029
    0x50a0b0a1203210e0f010f0b12120a110a050120040b030612190f02011d18071101180c060e0102030301060c03020a0b0705031e2e0b0a050a0e011803060510 68
    0x90441c00c94000c007e001006814061410042280c040005900b8150840140002594040801403100d80788600744044038590800506252181c50790040d80c0c9650f441049001e03c2c4c041994031071401104000c03c50904d070071b00240c08424480a0030717192054811002d1503400480c2400759824040b81c0a0255290b842e0b02c0c02c003841a4003c0d010104e0000d10300c40444200312a008554180f1104044c00350040184007416030347c801200a032154061004101072621000d0090059403490504002180404420b9207462510030b074030b80e00701405102524080354001d0b40d00105590440d00c00e8074200070500e2150030140d0401c050307028040c0c8001541d004200c2202e4201c0020360040ca44070501c0700a500118140031009441a07a62000d0f10304203200702200e0794900c0004007800754060b804490220368130540b03589958000904103000c584007081d803500907600520f81d4082d100080c00d1210900d80f003180c071030202d45410b02000b0600343e07540c0080f41000801c00b07030711070160540c088921505c06c3d240e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 914513489 1250 914512239 914512241
    0x50708070303110f0d2c040c030902040e06130f060204030c06090302131e0b040f0515120606090a022a010b040c0c0c1710050a0b0a1203210e0f01 64
    0x42c5a00942d2013403100c00030a44900140100c11083d140da00d20301810b042c4002c0410b0049098003e0031000303a9602c03214100d5489204200c200189518009000340c0c041c414041951170304c010001c2250010400c01034200d074481c0102d007129512140510300c1c4101440d0001c003e00035030300040e1030b00c42c10880c0452007541100480059a00031240e08110481240c9002c040e03400304a039510b160440f1145800301d0903d280c00c05114600010804103d0320448910202220001c82d035000710b0f860048007908440c00c1901100c030740f10503184042c0c0303014038104010800c10b0314080c1c40003407220b80c0009e1a01c41d043d032140c0c03a0100f140d486410300e85000d40304142d080c0a800b5046401f4800c500d405110520311f4003c00c1c0c9031501030390121590350401d00d40010b080f00d075400c103c0540d105001c0c402c502c002d40320746441903911a01d44120005600c89005083c0810a07446400c03444200c8401030349140800d4001d40380d58070507903181002c0f1000b1602e07000c03d1006017080c500c01c1d2200d880786410100c500241 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 914514739 1250 914513489 914513507
    0x150507061407080c1903020a090e0406020904061703030f0601052809080102090915220921270f030812090a020a0902030606090a080604030e0306070e0d050708070303 73
    0xc41d94600e44513440d41a20043c2c00e1003101c0c1010480b0405a52104589000307401403c0156080e080c500d0036165510016544844122003c03680c02e940003031441054903103807080001914003144403002000f90782c0f2036a9a28800a8a8500740060200c002911680b1030780483e0b000320718a8010301c0e454005110307080c61004105051902003110540c010400000c14803c0da0400310b0300911241241d03c3d18014120004e0341c24414a4010b43c04580c140d4403105800041c13445074000c07800005180501e03040c41c504205124030f0400c1c0e00b2420141c0c84413050f90000d07117a450301d07591211144a40b5a11030454080308081d40c072000074200691000000d010140020b050482d0070708207200f040e81e40d4091040d86601c45030b0300096211200505c1403180c862941d024513802480a410a803a24540354001a000300055110701d00b41c1d0b102c04100010503511440180800c0320542c018811420540d0000e050a41e160742154024003006584005010040000354000c001d860282c9484940b01e050003441805 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 914515989 1250 914514739 914514751
    0x80406021605060a1b09062d0c110105030601120203060a090c032f040e1b181e0f10140705010203012c01031236060503010305071505070614 62
    0x1107843c1c0542e0840d03904c5c4481e820050b12a9650600e16420882d040c3c0301d40c0054042d0301c441e40b14a400100c1c48200e10460044c080000e40c42d51a40d200851401981416090004504004083c424010301d641c103e210b4207051481e019002d80c5950396140403030200d801c0f50f400b6007080d50030541001790064065000840390891040040200112680c403840c0080c03041414218001d0200002c2010012a94400d90400040b0302c00504000e039144ca05041904075550b52410094000ba4504084c0f4210690f02c2e80c181550010200342d801031000a004006401e50840c05110324084494070944500b0044103d4900505201d03150017450619034002d401c24040c40c0f56000c0311000074100f0741640e854044003011170402c0030074542e080d65201c1d0700040310300c05140b0a00098020000d03820b504203006404000f9616115890030302000e08500001038a42c0c0b0000520100308018008900c000c1000000e075038054409030451007010000311880e00c41c43c603000d803c89181c1108544402503000c14035008130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 914517239 1250 914515989 914515991
    0x20c0d0c090e0a0c1a04030c081c110a080a0c0b0a02070204050601020601083d140109090f020f0607140114071422080114240d03080406021605060a 65
    0x400b055416600c41c2c46220103405950f180400704441107040200043d4010407034032a07410a5071b00e03500c0003115452600a103896070000c41c004e5030301e00301d83e0342e010990294602d490305044503254a4030391644480400580070700c200081d07050149004408050003c1c2d0700140c007003031a180024010b0025000184101d01c80d83c00e040c0800c010b588002210f07410303100f01401401c10702c905401031918000b2a900000400c00d1100e1307030440b40010341c2c44c1c88805814205030200d041c4149a8032400294016003211040c5454508030201140011403080d44085d816901448450102030010311300c1d0140c00001002e0088400c10421a842c064102c080b01034120103c0c1101902c1c3c1e40c00c00e031789019000c042600e0002050004070409140b204001161407010000c0030170007500c3c0d0b5416800e40e40445000080c02080e1030611034129241220814050f1581c0c0c400075200d10700400054045070b00082c003600b0000c030303d400328050000550490315060000b000842070300f105450030607220301040710800300035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 914518489 1250 914517239 914517251
    0xc08151803070b0106030b0d1502070c081903080c040b0403140c01090b0d0c0309140c032803052503090e10140d05030f030403090302030f0313060f020c0d0c09 70
    0x845000010b580c122503101000809681c00c00c00e0440050103007111040d03000c4060340101e00464100c00c600d03514017592900140c3d032400c003401c03c0020944150b000b40001e03442010591440400c1040c1202983da0528005e1510303103071008003036200d0056412415449070001070000c10400014890790700703100301c20296007004500000554281c002845040203050f410000b624401d0a164440c42d0100b60307074180041d80c4102c548590000b507001d03c40f1400154010440701d10325203005c02030301200e1520b001d182002c0040380300c0481036801000350000c0a100d408035000d284e4004803101ea004101205003606d90f00d21050900a01d080001d10626103503d208a010442e90340d0035000e00f00550b08440c605680c07021101e000d01241e010040019100e60209104429100700311800440c010380c000d13610349074500c0c154010942800381c00c114080785a40100282c5003100480300020f821101142800c00c86800541c5041e400d09084017162503100c44460380715000c10680d0354281007038642d108410000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 914519739 1250 914518489 914518531
    0x304050a090203010b04060e130c030618060308090906030a1703040606050f010c1104060b0705010218180109091712090705040216170705030c0a15020a1b0c0815 71
    0x100e1201303000341103032154100014407d07203008407110880000064401496032441c1c0c0078200445a000d401e10700000d880c0e440c2041290000c4000c41071400003000c04100c02882c61fa24046284102500d09000c0c419080000380b0a54050080341030290f0440e5400c44003410310845c42c0000d920484044803004e01d08403001c503042c100120460129103041e1101c4803005000d80f582203126038440c2c00c0c00d0348191a8a408140b81c1801c00c00b900c0c0b017900c604005610b548440300c40c1c00069039642216806110402c80144041090801050448245440005546031035041c0b0a401c242d4600c104184154001062840c00c1000031269100703030406000e50b004541c5500812003680318680100b0a420081501e1802048041100e80301c40200180124507100d140c0da070303150031904018584030094008003c0d0001344003c3e00c404407180200ea2703004500d8040e070180d01800d81c1c1c0300c031325036604c190740c1c08041082001100b416a1000d407501800304d07020b016802150080700340007241c0458408940320302c0300c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 914520989 1250 914519739 914519741
    0x1808030f0f0906043314060d020d12030209060f130b0301121103100c110d03060f061b0605011205191a070c0f080403031707020c1215090304050a09 65
    0xc040d4907150040c00e62501c4d02c1d2a42d41d81210440203610340448140003007501c0010042c0380e03000c8150000d40200740000140e0b91180d10100040c2402d00030310120100c1001680c40c000a11041a4042a00e04410103003020440007801440c90068214100180e540d82003071101001d0620029140440310080741c07074034903804250000b0310600360100c600b54a607030005503105c0c0e01d500c0400e401030100c41401d5558130401066030b00c0c0c040341c080424120311551442c90740510449001c00810300b07003031100c185417004403c01c000325441101d0070044140410803a4016900e1031091258010800740702d1943c442000701d08105c0041c00c11143c62040030b1440207442c280020b40881036400010a0b5018142d89040840c0c181009001c102002258072402000620210710300d00d29a003d85101501e0703d0035441c010b440500689082d417840c0c81038000b008141030f8000b9031f94103080001e48a03465180f010700181880d1181035a01100020380c0c14080100703000000015100b00e41c011540b11050540e1400040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 914522239 1250 914520989 914520991
    0x50609180c0607030c02031504050708010608070e07050909040b16020114010603240801140a0b090c0d110415030c0807080411060c1605010e010f0c0f061808030f0f 72
    0x80c16030010300d540405854000c000d030065600a0038410798000c05a40000c2c00c146940480007000043e08007440144941000883c02030101c4400030031200e424240016540c0d0100d00c0340a1031603028400082c6101e100e0416502900380c040e2004900742000d2411076000302c07007203a9010030b002c66080d000d152140705000c0e118151100319405400f603400d145d012800f07001d4141514501c081c522001c425910704002d0000300901d02d940001940900c20500c0c000c0c0b000c400f5040030709440c01c0090700c603c10360724210010740124502c000c2560b43e9200d401024040c0041d43c504201c100c40210300001d49140c0c1c90782c0481e2600c2039a0302004034091812050342c05150554009002480440028000403a03034140c0e4951100020119070901c0c11810030540742002101042d41c664000590410183d40c014021210703d25003401d0800011000c084003c105802241c0058028002e0b644042c06000503070b804501d0200c400d60f4890b0345440344e4240010541c0c030540c3d00c481e0340745201000460365240d4540031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 914523489 1250 914522239 914522281
    0x1060612090c030602030403020f03030c180d03050d150513050a23010b0a020c04020a0c0201021c02032b110406140f030109020c0f06011202090109020c0a02010c0c03020603010306050609 82
    0xc500302c6803c0d81c960000070340004000700c5c00d500c562001c07440e0f1911b0810241d4842e4181aa00690b61038a1a402540070400103402601441a02100702c2c0000d070060300365000e84601180009822544200501080f42d90341d00c42c07038020035016400010a41140c011038402c1d0103001c82070000b41c070000090355201034802040104000e507140140716520505c001040036078000e2048443c00040b20700014102d0703014003284000703e80c40706032180441d6014003d01c0c400e4070000241d4088607819800194070f0748500503806000c01518050100001d181b001c1078924051500010400d1211050614840ea07210740541703070100318602c50403206002d00408541000a0000703149086034648080035001e0b4001e901c0c40d05940c019055255200001001b07410300034402848030224401c014014030020980603000040414010000404141000110a014194286003003090f0034041e082c0704030310f40d4141d000294083c40002c0008144109034000314058001221214a6512104240545c0c200c081c000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 914524739 1250 914523489 914523503
    0x80c120c06030a020913050f061e0f12030a180f030c0b030c0d29010c050a0318080105090105180f0a02060913061e05030f060c031e090106061209 64
    0xc465820704078091a0450020030f00981800302070710008000d08031714101201743c01d41c0c480401c401c100c04c4d103059680203c800d0f900480c4800a0055440298503220500360060b050703181503e00a86441c010040300c40c3d10782051301c2e11042d0594004000210118003d1174400c1103160102e1112050000e0a04507540503511444881c039002034005c660300000c00668600405100f26529015980548003a10071231910914a40143d0300940002d90b082200c0c5604000300d040d90400081c100050301080c0070b415041140750303100194040f1070011640d4205007119405c2405015100c18150015800303514030803080c5548001503100c1c580d07951508071070441c1d1030b4060007044001d81050002020140b1000d050b41e0b6a03115151003032030580b816940450014131000c00822030075004040c0310005001d044014050046042c101c0350742d91400980034410b04a000400304551018068040254000100725000c29180946005000706194407900c030106110144901e4070702d0140c030440060781c0c0d1140e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 914525989 1250 914524739 914524753
    0x409080c0f0d084303050a0b0913052b12020c1005100504020a0e0909060103050a030e03010207120c060518030703050d060e01121a04020f0103050402010e06030709080c12 75
    0x200700c8035081c01d2001941312802001d0b0b84603960780b0501585802c40c4501a9144000383c0c1c2c0018014101c0b64014082040f02d45042c0b11580c890361002d0285812003001305101d428109a410100d081000c0d904800c200c032802d41c41c0d841414503911308403c032038032450b0b202c4025929019503618183c0c0300ea5003469001d5000f0b042c110900300042d500954128503201f0a00c0300954070380010070201d0340200d802001045030781e60346000030f140112595901c8402200545095407640d66516510b070240039008003484500481c0380e07041e407001d506445107141c10140800044084200281284900c600152541418000080d0503070403241d001c0381c00e8000f90300c000d41c03401c4103a48084401d0b800040300d4141e41e07600c0c0c0c3d00001d840301d08440700c02d01030f1102d1154420380c3d4180d8940051417201c0c0b4041120f07140c8480c400c20000d41e4a80b0841c0140700310030f00f07000c41d4983d03035480103c400c0712501210702c0d4818030205c248950142c2c040e680f24281ca00e01411144000d86000030030205405880c0d03c2d8003075600c08a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 914527239 1250 914525989 914526001
    0x80d09030b09120a17150a0b1605010908120f0624070503040e0720031c0b1807090828080f0304030201021e0702011403070c020409080c0f0d08 63
    0x1050381e0204400c1c0548000b07600d440d018045550110f1128400101d0000045c04a410f20241940c1c104035094521804180280d0100c3c0f002010340c460580083e6021810781111100e041045140b181e1003c002c001a010300e10b4415829041400391320b440740d44c80e4000403401c41120003210300032180101099509554940c15151a4601000e003060001d030034414500060b00400c00b0348094050014204020314050320f004207240d01d0145c08006429188200040d0081c0100807201444031070b40440821585c000d0b1800007504141c0f14090b0000c0c1802085c41149003401015405242543d513900794140e500e40e4281c0d91450400c2030007110081c0c4d141142004042460a40412481052584d0810b843c10702c0c0200c65400031901071340582d4001854078000300782c10028440c001241400181400d06607000203042c1214001c0c04200c084000020901441c040c1341e0401c1c0b20f9900420a1198080c41c1c90f002000d40c00691040c60b644c49500c60071480090040b0b18544190030720b83d94070403996130741 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 914528489 1250 914527239 914527253
    0x180f0507181a10020102070203011a120303070909051e0403080121020a050603040524010e1b032403011d010c02070602190f0f05150a020a0e061c140907080d0903 71
    0x3e40900015907508200780c100684080c01500b420300c90b03840da0100c207000c40c807042c0f010603d440e065003005500100108423620384c0146d4440169603d489000039165103d9400c540c1c54401ea58201700b04403108000c010415a01103201416a40180504401c4104c00403103032002014240b00250310034044070302409281040405076511900500c00c440c80e68035034a0b40c3c40345000b910f8000341d040140d0200180200d404400d2800d070410782c40c03040703200d409100400002e078030301014000c44e1034a1501001d1420200103041140f0307012000030000c001c0c2442c2c100000204120340710343d0403499401c00701c5101c4c4a078004103c0e001200c5403600a00003060207018520480094002c0840380044034183c0c10020841c22048444100d101e50010700c54060103641003000364030001c088840f03c500401c146c4041c41e070300181c540784465080c0d416584a030030800c0240d207039183c001c41a00b0362524003020b1050303504411928a0095000c401a03409081c0c494005644071030250716840c000c15814030007000020303c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 914529739 1250 914528489 914528509
    0x901090b07060b06071235041b08031e030903070213020c06010b0d050604060302011209063b210315150a030b180406180f0507181a 58
    0x100307002c0081c40e00c042c4000542e65030032418082d16244194002c0340d07001c0340c200c8041900c0030140011030125444118491075600d907241c03c5510880a09408a0704200120103542400700b14220f0700c100540d11001490341da90000c90f5003210390040d15424041c0c9010380700803a4000d1103603602035403410200e50248440b0030110034070004040d50070010071320050410b0100358082c089051401c0c1ea109402c800120944034050041d40c4240c0c076160b030170001070784c0020340303144001d50005001c161900b00707050110040c1182d41040400c108013000301407403040b0403100d000d07031007070404600d120f10720345100e4090781c490344892250240c001071207200407103840c40000355500c54840002c4450702154080415000d0305905000d406424001c46c29100d0315405005500403178009844888101f0004604c6501d060000391018001d10f6440e000c0128803070340198003408954200028110007100d500c0d00300d5a0b034100b882140f0f030010301010302c15190314082c002e514009607041d1201b01c503841c2440403c110109 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 914530989 1250 914529739 914529743
    0x203030f0d020403140f1513050a0c06090e01080304030215090612060a090c1403040311030403140607050304050d1d0409050309040c020a020102071e0320150901090b07 74
    0x48144629803001000400074041014580d00160f10750f0b241d07103840100001105240050342e000400c010318000e000007505184040b150781c0018260720b0398900440002c02c00310000d1b02d035002d1300f84c8800074050303481566000c40302c840e56100840d550b030b552403000f006020b01410110781c0081200b000946000c0d0140800c07002005416460418a100000d000340d107c81107007a6212280800c0045529015541c6030091900c1002804800414007000f01481079000103000700c2080400454107041c0306044490709408007204680da176585a0804ca460072a00340c41420310b91240340001003002c1e21030b02c1076a00407540900206034400390a281a608000e040c510740d64070004040e03446c041580d880c02400001030181c3c018690328a501000e0000341c0d5132800c4c10030103550000b023800c40140d80c001020003c81d2842200c1041c61400c103800031070100016440a88070000f10304011303485000443c0800710008088626011307003403006110a03001e0040d060218049101c03410300700000350b500402000118 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 914532239 1250 914530989 914530993
    0x2190509033a030506010e01180e041505130c0603020c120f090f060909060d06200309011b1d0402040312180611070312120c08060f040608190203 64
    0x1207504204980e10158180c001811040180300950148030700b2203941c0c0242000f4a0140010314203140003030003104994500904002d83c80b902c070a864107100c41050302800b109003680100f030805081440719210601c24081886181401150f9101d1203d402c001070303554000d13104100185015410b400075000300c03c62400501814181241d48c4244a0042c00390401a82c0e140352160002c0c001d00c4900751181d00f14a000d46000c01444045d40d4492560300c0c1c1c4228210342c00001c0c41c1c1e061030031134094150301001e03000030401640b0000e441d40125020318852030f851402004100350f521800000304002030804000b1403d010503052040c0c5410001c102002000342c005403425541c0e0383c07020705605100f080200010f8400c1c0842d07006c0d103410368100000b4641450a0103080300c1c0454400c0d207995070b91100604500000c0e0024021500482c0000090000c2c040700300b01c407144041c0042d0882100700e9010344200600c000ca02103a04e018420f0105581d49000108001d2a4400d02e500d0024181107080e0784c94 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 914533489 1250 914532239 914532253
    0xa030206161b061106101203020f0d080618070c06050a11030408070605060306090304090c21090606080a0f140312090726030a0c03090803040303030603150219050903 73
    0x100359040c41d02500d0b1004045415481c0b440d10b0340080450700150000e0b00c1a40001e0103014141011012400954100f070b14030b504030561915081c1d02d061282c012803013441c001c000030000c000b60080130046c490b420540764419091500012810404011580807022526883c51000801c0c4558051680308002440001e00c80070b03045040d40740f94000b290105d13805100000c1c004100041d0740640c3d500a04260011700c0c1c0c5041c0200d8040d140d00507401380e003a13184c0d03584041710f101500c070310b00d009000c80350382c502c04020317031071a030384c810041d046004090702c559051030400100c2c124001040c83c1a140c01080e40900744405655503220501250401c840c144420710072514103c0b801030410340141e40a00003071582900d00f0800a01c0035011600552402c03580c403082c0b20320400084100d45c0b844c003180c50203002036155407a0a4800c0c002540044555210200d008800c0540503407000f800d607805600c000c00302e480e803036103200141d100d150395000d403481d1340400660120b401036000d040c0c40040101500d440b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 914534739 1250 914533489 914533493
    0x2120a090507170615030609030703030e100516020d0e01050d0b040204081c090e060a060e010c14030d110c0c0108130515250818010e070b0901090b090a03020616 71
    0x40b644a9010b80030030b540141060041408806005143c0c5c0e10741900540400e1131306800c0251a0f0280e514050141074442c03250480440b0140005440719020b0304e010080303802c0491108004628054182e8094440c00c407110441038041d18404200c1d0780140e440a00e0324102c0310b02000585645000c05811079003e00c004a00fa000a105c03082c1603209128000001c501d900d40700038004071050f442148030940001c10b104403a190303074860900352505800d0124820204800480360b0308040c28028007400c2c103030103110b8030f004d401000926001419031030038400b50200c031a42c43d00602c11342c20420301592001000079030650081c117829522950f03101c580c84604003580c941ea030500020118030790b001c007502003c2080c2084800005140032695880200c0794115040004d0070030040a0111031030000046010721010409400564045607280140c3c0c0383c0c1e594072034001c03c83ea00140d0010340410546034000c5100042e00e4195024540010004c0d4003103031568080c0300b52607001c6900303e031101c1007994074100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 914535989 1250 914534739 914534759
    0x7060c03091a0106080705160210030c020708010e07050405101a07021323100803040e06040b01050a09030204110912101113031b031203051902120a090507 68
    0x1001040d00c0200307881c1c805103030002050001e80d164240c000c2c4440010303c000c40e484441c0300c1e8001254144030baa2200d04190080f03903003250100c001d46c4024980d1041d00c1080d031582001d001501d02d902198201c1d03403129243e07802e0703424003c1a099681e0100e0b00800003454150000b0740c100600503131080b6080e88a180f00301c204e00d035a4203584c09103080012200110708080c036904039000c1003a00b0070002c036650404200380e40700f070b58156400d101d400030380801c004400c0400107600030050701c41106c1c1d40d03075070700d002c01882c0280480b00700380301d01e01d403207034081d0907501a0b021100c201003d99181034415056500300001851f083c80002c015500611445143d500c1d11200c094a035000d0200500c0c012a10050a0341503800d030608000307001605005502c20411a171985400356580200682c170140c00c2003124507540c50059001500488105d10304200c4181c1581c0200d0140c212441191840c01d14400c16405900c01e004a1f868020200c100080d19440c0d02da000b0214148640c0c01d0300d14150b41d9904680e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 914537239 1250 914535989 914536001
    0xc0d1103071d0c04051c060b0627061903110702100c020a05040e0a0b1905011d01090203040b1602010902040c03061806030201170903040503010c080604140606090609060706 76
    0x40310b0751119401003208026203400365001c0c82d16241c641c903250628000c15480015007401d400c3e40900e60300030404001050300005043c11000e80346580300c245a49410ac0d00e030480c403039540400c1d00d42e0078861510b814044100d408041418501d01000b2008000403130003007401031400c07040d1000c24003a501c0141c1d21074441403441e43c0142e403808080880c50040188044495208911581c07610340300c94440303800420706c11049030b04403180100c1540c2c0e00403058490003029030081c032458a40360001c036007030711582c42c1002d444d00142d400e00800d07070302c81a04408a2109450103000c9a11480016180c0720603007038410050320f220302c000304807050b140d0b0118064400c8455194046a00c600702401812242d5220440b42c052000040c0070341440d58002902c8100082d01c0740343c2c29403601c0c00080e1504001c0048500820000c0e0007000980300031040200600816106076200307a042045180c0514070b816802809524000c00c0d152402c029002000016801945d413103400c1101031010501180c20351081e5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 914538489 1250 914537239 914537249
    0x70b0f0304030e0108100b090d17030108060c0c03030f1e010f082103010b09210312070804020f011817010603050c0a0b0301030213090b0a1e0e0c0d110307 68
    0x2240c0380c1c1020320b40a04102d0307000d1101410485580c04001070f18000c1c0da00307041142c01d1900240da5038940d24011586440b03060201a084000d420400404424410020341c12202503000362405521001000e202610614041075826030090000c07501e8000300c01c10650f040000c00410000042c814142900c1400d8240d00001c01307103000441c02c001c0d144003031181c00890f4004844210100d0804180c25110380018003407609041c00100e214640c0c1e4440078200704001d203546844100804600c150190359622110030721402c4a5850041086180691101402260300804400e035641e104001150069400020303c1c3d50303110f0603e4000b03161621400120b80c0300e03c100340080f6095041d41480b6107810080503815000d4001d0f001c080195100741010340e030540780d0413965071303448900084800001d886146400343c001d0b60024284099280654000c03a040440e0140c0381406a8901520340110780d121019021142c00034000250280b814000300748210788140c1184013100000804680350100d15041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 914539739 1250 914538489 914538517
    0x70e030f0601050a060e030303160e0d120207060504050310090503191106011508241f1103030601210e07031208150112020912030f07020f061911070b 66
    0x60009040c00180400901003d04008035021b1701c00002c20f6480c48010070410300c5c021036940c5001241d1140c0e45802d07007450010400701c00c2101c41c4c00c2c4a1b032903694903a01d00015106501000400340d00500a60b070803260024040e000000240c0669000743c9079244040f40c45010410240f403507074410749604419081c640d50303442015004420183e00d07184060b0480001c5540d00c00701d0000c007a9106a64036407000c0500d02e94007841810714030340702c10030032104030b01548150300142c0c0e05042c0c0550300643c2c1c0180c140c2c2d030310781c950b880000da009034480c03206503111030015940211681c07403600d84030381d14500b60f04803500000790000c001e0040b50500f40c41b5001112402c860b01c05443c40c40764442c60264018240c5540100c01403952000600b4050a409141c503003541c02007a840c0165650801580740f150f05003080e80c3e95442e80c0307c6202d10726880340700f0884c0b1444403409000000e080c000e044d20016a4a94103400e140c48600074152003244881d4080c3d035481c82601004203050648802528251004200c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 914540989 1250 914539739 914539741
    0x15050603161403040b040f0302071a03060f010314060f010516080a0f11070501122013060305010302100e061b0606040b01020c150c070801060f0602060601090e010e070e030f06 77
    0x80090059030401e8090921110500a00c00483c45201151b0f400c59442080304d810440d4914040c0e0620f540c9500501c8075180382010f03000300f144094029807083c202180d0400800c9180c0c40150102c0d001d8031502c4c1c1c01071844500041950806840200d106281414120300706407030444007040d807441c001c0044441542c04201e000446801107000b4803146528204400d0492a441c051592058544282c0c0c0c1000b843c0150440b0f461401c0d440002c001214442c1441ca810000110050580c0265850800c5084104d00050010310034031a00341a0f990003429100255010314044034407150795215503a0000c41004015081624110701d110b100c04984040c002d41e24082040104541c03888004034150342002d4290440e56641e55456000b0540303590b0300d13035110760a0f8140540360600c01e4201440340e600e015000b040c032040700380201040304c82c26400c80c1d4050395494011100c00002d0710800782d080d00d80c00c00521201a08250440c0e10121a1030100d55455010b8006854481c54425400443e04104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 914542239 1250 914540989 914541031
    0x309073c0504060b030411041a060c0d1103121b1603170c071a09030904140f091204030303020c030706050c070507050f01050d05040f05070315060f03020f010315050603 74
    0x406141c0043c160090b10905624060720740a1001a032000420f22440d5180c00c0c9c0c03420900320b40340c001e4091070040c200988400c81d040d0550340d86c27103121011001040c52011500d144200000444000103048650f01209c0c1d110101e5060031180408503044d5941c03000c1c080349402060303580e410304045000380d50300d903041c48035541c400e840414060f02107a0120020400e2002261030b080550181c800d0f2810012001d580d803e10041c1140250700314140d11038205501000c1d07240454441c42d0084159910000b1181c40359101170b80c3d651881d075400c0b092040140320802c0881e001e940905a43d2300e0716000e0304d16248603969458116070044401c0c140e18080461648280007081000d20050803090f5458043d102d0542d001810034096501c40c0c0f070300c8640300d8000500308200024200d0a4a510400310741031281c0304e1801c415044480d18146024a00d0f10f01c0c001a0b5031a03030505202100c0d00502040007001c1c240004401411480e138807014420602480081d21b611610019071141800700c01c81d5880ea2204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 914543489 1250 914542239 914542241
    0xa05010e06190603031d01030e01020309070914040f1202030712050a0f0e13091118041e0f0f03050c0601150207050609150702120d0503010611030309073c0504 70
    0x1034520b00c01200c0c41e03c20203000083e00a100700d50a00e040302c2c640f8a02042040040300645203071805004030b1b50011013886118000051800c0548844000c14820344001091076004402c048401400702d100c0232469802040c4a84e00c00300138007020384140c920f4608146c40e01000c1d80d642011910006d000020380804140d8802001d000c0c1c0400c91801c1060303d0040800202580d1540221099076580c0b04001010421101c23001310f592003001c3c08088080801c80c00054550745c1c211400ea86501000b4403120b152140c2c2d000104c4000c1d400940c51a04e00d060707840c1c2100d0b03041c02070421000c3c07040410228442510030082070740200400311000d12012001c0c00000d0903c542c66000c0e9000c0c130014004030743d20341c0e210300102440da10000411a1600c04a00020b100d40e8181d1000d001c082c000d00c4030312003c465001000314180c50454680071207010511095035038070f12084841c003c0f1900007410602421900c05008010804890310389050400b5845c0340595505d040d024286c5c907401390890070070040c10a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 914544739 1250 914543489 914543521
    0xc07030b01050108090c09060d0b0103060b090c0a0906050304060603050a151a130b040204050904111c02091303090b0a020703050f0d170604091e0c0e09030405010e030a05010e06 78
    0xf8078004004d801d11041c41d82e6200c06500c142841812104001606600c90b104010011600301030b181060b5652410414010440840071354040d491400c0001d04404081084908014a82d07484090032882c20303e00700c03500e8101900840f92a5290100003000c01c0c0100300388076955000302d607680c3c03100c4c40c4030b0245421200c0103031040741c100103060f4042c12a945e0b06102c2d001c127181c02047c003003400e11400001400901c5203402003030f032004681040c0300c1403040b490701d100c2d12190180c91492035086003000c6811950744103038000f0b40c01034540700040c1d00203000103000c000c094801d0508014454550700a02d90742c1c0c10003001c200059101c04d4082050100400922845030a09800b8190580130030400810f0040f40e00781c4c401101c100f4002043c01521a03501520325031b500081c0d40301040400c07082086040c1c00c131030425901e4601615020400d0208000c1c3d681c010310420340198940b925080041d10000c0b13020781c6465050043c6072500002c42c100b07014180c0e10700110b0000e0f08851a00c08001c1c222400703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 914545989 1250 914544739 914544749
    0x20f07060f080901020d1404060b030102070b01050103091506140a1d0c03090c0a060c0b10060518150c0d11030703080f0916030b070219051216080c07030b01 69
    0x21000004200c16504411501004055403030a00d5031542d49100c1c4030702910842c844506002d14040310b1000c009460407155000b00d11039001400300d9068102058280e0141500250260f4010320040010398040e03813000580320301c2000c03121160b598012180048403020390007461101c03c525025101c516203503801d08041c201e400c6c07500100d4081c5241d000206400241b00f80c1040900102081ea08002084980345140300281501d80013521803500515814500c40115110740840380032948401c5400c0d1f40c4815268641c2c2e03100d003003c00c803c00340c20b003c10444034181c0c1c00c9050790100c08050400e500081505503549001071007440424440203001c40300c280b000001c590400c0c8808000070360301c00c220b83c0d04400e03101c11038000c1340c071030440c06c5c0e04144054000c2c0c10900081500001000802c1e041e06119100c590281c650000c03881100410300c90802c100140710b07400410305401c00110070400b8100d0800b030401101d00001403a500e1040e0380d0322010140f00294051402002004103500c040d0780900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 914547239 1250 914545989 914545993
    0x60902040f120f170d0501150e040c051c0501030c0501110a080318030a021e0c011209170d0501080d0c02030c0904140a0605190b030a061a130b01020f 66
    0x10314101520504460034080c100820380c0b401d001034180504040d44030940c0e50000d10401d604a00c842d40c0144c280e121401c450b5440c0d00f4035000140031441400500440142c684803401c51141d140e00f008010842c00c0c800009101c400c2c400c40c2050b0010f03448006040d11044800155941541010141c01026500040c10401480e0b503940d030121001ca2010666036000c5111501c82d107500304454100e584d20a05403885200210740d540c1c4040d40090042300200400da20101d9100941109a884142c15107045010580c0300c9409004a40c0d90703408084890f01a2410072002400c624a20b699540f28203640010107031550018000c0c04401d20004e030044a940c1820003607400707280d0100e500d0b8103054902c0c074424568080050107010101e18001000007912080d5a00c0400b1450490010082a248440b5941066500342c0300301803544644d880449004006007041a030603a0f5044c0601081c100800880010042440064547c003406862490f0241400f00d80006c11900091911603010900c006913 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 914548489 1250 914547239 914547247
    0x510110102040f09050133050c01060302060d0209040b24180901030c17210711091609050603040b160c08040e071701050604120311190302120408030307051b1f060902 73
    0x10a848001c039440c0401f841c1411611550a20030749401054190710207900603100081e001c00040d8168000c010880045400f040000092000e2255580e4580d240c01e2242100a407401307508201c00f0080c2c0302d0500030310040340f0f1804030b0a0202c0d0b4084400c0c1c3c011036244045120900c00e004542c09200181c001d468000c1a100003805540ba00c0303440724031042d0b04a0000000ca003414040e5000803401500387c0900307580707082c2c103000e0148202c004805034854001240d0010100b907030b180c181c040301e0046800154051058840410303503c14030180150502c140140d00610100050307085d130141c0000c2c45c022030100707c40d02d0031400c00b0342407501c2400141c4113400c9000041c880e541d5a101510280e840100a80c3c1140f02d091800340c960040e031103c240c8040c0b180e81c3d481ca075040c0c0812911503031680702c0d6095030144840e100710f0843c1805140500384079a04140002280c0c83d10501c043c20a00c801c481c404001444520416410400100021800b6400340b40c0c22423140304950003a100245001d040071854 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 914549739 1250 914548489 914548559
    0x207080d091404020c070b0306030f0303010e0f1f06031e2d3b0a050604021c0f060501060e030309030c150906030c030f100510110102040f090501 64
    0x10020450080c1c2c28960515200d00c911500c40b54180c0d0243c0c07071484102c0d071665445035030404068004403800e0307100b0300c5400c000f440806808815030b070407660300000c4004251200d840f449030100b4000c01c00c400754009400d00240903001a601c1000400241c0c40004800c0c00068601500c0f042440d10001c10908202c070315683c1921329403400c402c0c482000c9045801f40d4415480d03002420744132503039400c00c0c1c035090300e0141c00c50150703280c09043d00602c40700c0c03402440b00c547c21a61108490034018140d40c00441c00540542000040701c2d802c150444842c200f07450440d550b4458408200394103903042a943c50050000f260040d840e9411a54100d006600308a030010000341e8460101d042180a000105084454126500305480100400400c559128541008020341ca03420442c0c0c03600f207940d5850f01046218181000d240d081d60310107080041c0d1030703070380340c0c010750361260f414050340100e40d0300b00320008000c02040110b8001d03011004001c607065160040b840c2150901c20b1b901480300c0485014090 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 914550989 1250 914549739 914549747
    0x110307060e100c1b0f0e0a05101a251106031612021b0a120305130326070c031701080d0c030504180603060f0b0120010b04110a0207080d 60
    0x2286052615160342424228a040e01c41c13100c103280c504000340510b0700b000c1201000c241c03900c019030340d007480300103403541e21441d80d4403e49600382d07040321030102e40007020300038400c0c00e142e4420b0110100c8070080c5031442600c0c01d800440c042014044003507100502e65030810416442c408800b0030102e5640b811418a4140b28203012038108020003446000761040d0035109080d0190341c002c1700301380d5620305601086c24041d51140b503000011952040d402e018180d10328041d2003000d004950f00c03040103130f03805802e56081d10075100c00c0c86e12032383c80781d00c61030340306580c0f8201300245125420310303a00c0402401c190f14000e01b041c00308403540c544286481e0018400e0407800100003204041c01e18101d6814a16030074240c4092046800c10010080518814944404550422030440c0d00c1035208200c0f0b0401113590404503100e04001c24002502380b007542800b40e1080c2c4a009030400084000100703103000f01d000038200d9554a00c10f640c00c0802145402c94150140a44401055003002514800b01110b900034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 914552239 1250 914550989 914551009
    0x28090614031c03020d110a020a03020f01060f090c0c06050a0218060c0615120a0501021c140c1803060f0603061f0b0d0f02121009060e0f150d110307060e 67
    0x2820580e002c901110000b05c250007241c1c42c800c007441d01554401120000035100c1c1803040043d0051700c20403440c1c0c03124000c1480741da02121501200c09075410708200c500d00141c10403048480400c0001e02c2c25a0100d183c5201e940c1c000d40388108016940c2c01d0600540620030001c8008510415050081d10500301010400310b41c800c200e00ca581c2e0000ea03081c80094001c0501007080c90700c9205080d201810000158001e02d0f503040110711107115030501c0942c05013a00c0c41e202d800b541a400380808104d0168600e00980b00c0c4910280b000e040c0010351001080c54004200d078540301005100041c04201d0505108940d00045041c0c44030b0110100c6403281c0010016a00c12200b40c0c03c400035000d49400c44070f42c8001c500c90032461095542d1400062860b00501043e2500c41e40340e8002c1c440010700103414820402203c840c2e004e400036640c3d502006481003900101142208100ca244103411951041c80318501e5520645901c0c03555680f40d41854909040c5170030143c10b00000462185895445040d20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 914553489 1250 914552239 914552293
    0xc060e06040b0304020420090a050a03030c03030b030c04110304350a0c0f0308040b2d060a03080a02060a0e06011206050709150e012a022809061403 65
    0x49980ea261440800d009202c1c0d0403691005003d00383c141c800c090302c2c400c010608d5800884d04201810345910801c10301c03d20a110060106000310b07c8100003c0c002c1d00445034a140080c280c0d5100c80045010400b9501c0c000b1805040c00400000c100402c003020301c106519020b114030f04543c4070030000003206818100110240e04010101e04d6000240c81501d00c1d50030140c2c403441000e1900341516000d00342c840309440460381e548a1400184c48415103183c2c48180c0400703e203199960307411454804068030000342c04950440025840400425080d4005210a075540e500500043c034011141302c00301c501c3c142400150390080001004181500440c0d18002a0440070001c1c058440d880c3c00d80b9a00120340c03041185d03a11801143d1829500681c0e68084290286c030391a030303d04428904003160b4100c00400061502001204401604050240100800404120400c00c00c2583e0240408180c1e40d449070030303410b44980092006101014074070882041c290000c0040d82c4510f40d204008004102c20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 914554739 1250 914553489 914553509
    0x706060b030405070b030910110d0b040c0f18081b0a15080a0b0d0b09061609031208132f030c0a05012601090e010c02060f07031d0d020a0c060e0604 65
    0x3047c008602031111140c10030420008101321100003c244049402c150040c0c40a10710340203606a040c00d1600603603400d00100c1e55818a00250890250b81c04584060700d4541d0303001d11400411600c00400c01d441095050342d508030800e0081404101500c146904501858511000c0c041c6031603421002e00380e008041072001103140c50b80795001c15070214548201404004202050003810040415100d000d400e515204a43d0003000581c15504680e84c0e1100900903030f101d041a041ca40e129084c90354016131038900781e008501c070a0701c03810301090aa44990400c02c401c0c50041d02452038180b1103603807110b020b5010307100b40d00300c0c2c40c001445c1d03461501c6042e040c402044004010f0032654a00070002101c08810f002165031540d150200808180481c04150740c0b92190709844280001880380c0703d0081090f00200940d00e102003240544908581d044000d101141d60441d240c10501a01d502845e956006000070139581c140f214861803c0c1d03100c401482a41103109181c0d4417040300315004e40f03401e450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 914555989 1250 914554739 914554741
    0x305060a0218060a0807090512070504020309160e0105030c090f0703091104020d05042a03030507032c19080316110a1d062b0204060305120706060b030405070b03 71
    0x40340e41c1001c1202c402c0c0960120000602404554103c1c403801e01956a9a40380200380381c50700c050020044441e80c0503034281e070003040c040180e80f40c15001154000d44100a175181c1d289255421103540741c0c550080e41d00003c80000601c401e06042109620040d002c1380d500c0c10301d007824040c000d0010b070054044010551035580c0c103818040030190505500c1d0b4003401c21507442c0d20b01d4092200504050b00c080b00c1c65030003103040c00003d000d0303124084140b17600000710b82d076843d265640c1511598880c0c2406c50511000c5070007481004035100e508005900000003015025042c0d070204801c1d4100c01d44941d5400400c07032030500c86d03900c0010035900726007241e10b0914202d21007814034110303001c0050f02c0c007507002092044c04601200181c030504850550b0300407805690325044100074040d2600c60600a410812026001700c00e525203610445407030018100044c41e076103e490701420011034075108208568002140410000b940c41200300615070840c007541076007029920f40d03880c2c07162481240d09110b4040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 914557239 1250 914555989 914556007
    0x90c0112051302100216170c0603071b0803041401060807060e040e07080a0201021c080403080408090a0e060a1217030403120204090b150711090702070801090501061505040305060a02 80
    0x5488070b0000d07a00101503c21980790600025070310850032075600103103056044002004410b0f462901c1d01e41181d034000d810903c040310203108682d00010114001c0114000b94440381c001c6c86500088810300031240b5540e207161074105404401c224081c5040507a2401004002010010845400340d41c02c81c6006492403001c180041e000e03009000900740c0740d0142d188002040b41000a6426500380300380c080e44d200c80b0140100c10000910f101048000c108070400040001c0d03c642d52859000b841410468280f43c00700f008604082210f800100122000d401440128034207641403038001c4c900c2c840c80078600700181e500c4061400d08811410501580440401d08240c0a070070f64110102d0b801108645403950389510501400e0705102030360144405e52056908840684121002c02e6040320002e0704007080b200c00d105014500401d110114024050040348000d401e010359411517001d5030002c11a00d05140b011002010b8243d200c3c0c0502104201c01c20000c0c5d404101d080e03108010100050304c503900300c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 914558489 1250 914557239 914557261
    0x602031e0f161403011401090605030903090d0c090507080406050c07080d0e0c0d0804090507030c1b051c081005010c121112030f0702060f06060d0b06090d1208090c011205 75
    0x80c3c412031904481c04000411421040034036030307200c01801da9800d0a119900d1105903450310080c0c40d01420358104200340e0301d40707040000360b00301340d240b00b0541540380030365400e01c0004491007034a60800117800c01c020b0101340035140c01241d80002d8800085403130a030781c1e0313940c1c0c141c184140c1400b045403580b00c002d030502407402403003c204002000f40150044503110300c0e1400440e800b6024502100c6c0c075000204416a100340725905103504c0300c0d121000e681000c11005144581c100d0800c580c3c0c0d100d8101300b0b4110240c8560842080d0101c0d07140d4803001e00344143c0c038020103d1290841030411822841400c081060b441c00c1e0070a0071032074108102907002d500392030b0b8181030040801c81d024101c00418070803242030b030420b5a4417601d010341c241e5034540c4510105d100c00410694010798400b209000e940c0003091140d000c1c4420140003001145840710080224890503078884064858240c0405c91074801c64000514031b900c080c6d414003804480d49400d0011702034506412860002c140d0300c0d4001144003d030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 914559739 1250 914558489 914558507
    0xb01050408070905040c15020a1704140607020d0602130311040b151312030804050d090302032d0a06150e190e0c03010f0c140403020d0b0603070306090602031e0f16 72
    0x1880a0841f1410350a0065582d04807040126149956a02e004880907072000a5400b81c3e00440002014888030300e04122441d0800141603134007032007090081001070794502c003c040c2d0300115101c020100d403450030300c1e448592201c2c01e03d60203107042111004142d9605a40226002c40e40e011032038403420030100c03000000039503410090144144e95501c80505030031010707061090b0311480840b182c0013441c0000321403601c3c180c030000350194096560014107850700c480d20180b46010b10310506a049002080a26191340050291583ca50b00c020b400d800e007041c21aa01c01800300b001c135201c41e600b45041e40102483e0a400701032051562446401d42106043c4607041c0f1400e002802480000d244030180e1005043c03c03006540807464a0341e00e8002034400030152000c80b07800824075100d13407016849482086200415040d85070080310004070000349503101e44903100380035100044c1c0724609a200d9400c074000c4108000c91b0072810f0420003211081452100380d00080d40c140d20004501000710036070f41c001d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 914560989 1250 914559739 914559749
    0x150c060a11160c0513020c1005060303090a0e180609100b01050f0d1a0a0815040201090807030b01030b010f03050d0f0323090606090c0706110708040602100b01050408070905040c 78
    0x218802540b0500400780400030a40700101d80356800707080d0406075942284141e1000c0b46030703a00000700780352017a5190f40c481c0740c3c000c8018085e2850088504001898218541c101c0c0042c104034001b40304802001c41810b4450084200043c07145080c2000034640c0c0781013684401c100c1948584881003541d01c2074081d15000e0205004180e1105000d5081c180035140c070358980003280300c14034428801482c0003c594021600e159018101d9414800300304000880010010780c1885288140001c10b40000c0120340c0085010b41d02540e499410751030800740f9084180d0000c20f58409029080c0042400070401ca00301000604141000404005081c0e000d401c110240301d098500c0e100080c43c0440e1541c0803644100080c0d000c3c0c800c5640c0700e10410061500c259640c90b0004c10030b021440005d601c59002c4442c88807a5641a0704043c02c964603c016136000781c00103001a00002030b104030591990050b2065003409007403481c20181440c41084d503502092203200c0e40380703850b000801d0030f01042e5008440584 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 914562239 1250 914560989 914561017
    0x140f0a05040218340f051c02071e0b16090501050307051c0507020c130203010e06060f0903062e0302060307051b1006080d030618050405011b030b150c060a11 69
    0x40c1d6109510b84c02480c89a1001000c10001c0d5250000f407072040d01103460780340240703035400d40925100c16131100941100c94125000c0444d00c019100c0f41ea281944108028401c00d1809141c1c984800b18003600313107000b500501801a285070600c0113a8010041e680c1c00451486e095884982c99100989030544081400b08414900001d02075030590103e0320b035012078030640b02949504142c2d40c20800f01d1000b48990032403502003401083c501c2c503041c40208072103032901040f107042c6080302d80040d040100a6880000f42640c0c050841454011884108403404501c90b164510525640109000d8440200300c41d003040340000701000c001c50701c0307000c001100c00800110340303805a0545020004103d2030044000d10b10a5004003011544680240b10580d048143d40504040010715088007600020304215040d54030780c5400405211080803090354100140e0700800d08a0b0f6107010b00c814054015032544520700c003002240e00070302d800980c2603001080c003d00000c0c0c40c000304410028a003e8410386405507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 914563489 1250 914562239 914562301
    0x10090c05030a2f0c123f0c090f040903020a021306031505010603110703093c060809010c08180a020901030b010e0a0207050a06090213140f0a05040218 66
    0x100500c0c05405a072008000312141007031141210701d030a0080341e00281010140560000da41818046c03828100088000c9110f10006500711180c90000700f1100410f40c007501190460041c60a14000b40c40c11900391410040700f2000d4400940360b000051000c2e00881030f0245e40083c58009a028200840d00400204000021902c1c66409000284103100009042508002e5062038050440701c01c40d91507120b10b00044d01d4200c031101d50a80c0f11b011800d10140b007103003075212801d0000f43c100b280d1420786001502541486409090440003500200d40c50789003c0710300040c82d40102c0179035045a442c0110f08680024482140e103030540c82c1d80c00a4104200c1d10000040160a110f000c2c182c40b0000f001030300c1c1d50b8504c00038a00301c1c060300c540507100da4080c4003200040b40c0d8070303071000d100c460016140b0642080006141c030142c404d00d0740113500c2c05d0b41540800141030514103105400c003111101c144054107298000030b10800124030400081200800070901064110200da8006254402e05d9610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 914564739 1250 914563489 914563571
    0xb01110d300509010c020f0303070c262d040e09011d0f07240e0111011506022127030d110d081014060c030309030310090c05030a 57
    0x2514058503201060340c20300040b0310a443c00070891003c0300250000444c15995030a8ac1280d200422203001d4032217150b4558003020b40c50044c040045a003450401a943d500d18010380081e811180e1001e03251644040c24070000200c0d0700c2400c45003103078500001c159a64469200c1c2c0d900400030300d0641d2483d09004003e0a0b141c103000318515180420440a98a80f16503688000c082c1819003406031502e4110f1460350180305001e9003001d80e04001c18909202000d800c05002030031900319180d40b0710034604460080043c150b041088940005081301040100d0541c0c88402c10036000700660861441e814402825802c0a1481002d6007544010100c0e01c10038007800003e04540b203408a0f0410500031241f064515a00651040e80112a0070035510241e0b4908043e06d49041e400e003091075031014007046003048006082020b1030042d91410061030743d070b0420103d21070710500c0640c025a1403504058520343d50a400c035064035801075002d24081080f8400740310b44509844003882d0420502a083d07007aa20b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 914565989 1250 914564739 914564741
    0x703021f0b131b050c0a020907020105090c0307120209040f0c0e150324100e0c04060305011a161a1312090806130609140f010b01110d30 60
    0x103110800395032000710000060b0042003aa0b6128001c0d403032000320162600080d91044005192880c4500f05032101c041b000c0c0d00060316030350169060340050303459000f40901003009000120f040783e0104e00401843d41350070300c41d05013000c0c420000b920400c1035200050600222205500c0c419510000d050318013500d03080b01ea081d04030107445680301240008040c9940e4240018158003180412807848261640c01c49641d00d6401d0040c40303060305155425000800740680c2010b103014271503200e0740f40d440c0c0d41031280040403500d05a00202c00d080d60a00580c0707480786a00202c0d1043c1c4004941020301816505103110403000815940e1000400e6408000e544e0f4800c45000d501d140c4100440c03e2103184005049404101a005040c041d070048404100c40d040c6010b503d0380b0141c881c100c08942c61000d0380701c08e20b100f010b0128041c01900003d0180b0700c1007000f881417001c0c840e02400c1c50b614204003299441c0e502d49030080d1100c00e0110340c1c05440742400310465412490040010f0f18110440036001e058 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 914567239 1250 914565989 914566001
    0x6040e0118050d0e0d080306090a020d020a11060c131406040f03060b04051f0e090a0605041b08030406091707080d02070611010b060703050d09021905091b040b0703021f 74
    0x220008981e07103404400b920b04170042c0340d01c03e600190920305584a42041040e0a00003a050b00d000380d90801034412000118005007000e01c40c03a881c0c0500f030a8403081e5084c2840c40051001807200c204002c40c0c1d1006404c0c2c0d034400103841400c0e0110006031002000f0900c00c3c4500d402101c41000e01400010812646070450b252958064406020648509480f040400c020040503414003910300001c4c051982c04035849940001c40c0302c101e4648101944484040711410b5800382e840d946d40da0b000741d040d0f030000501c100041c03180b00e000b275107803d160070720041403040140074113034800103804800c0d100714808200443c00b8081010945a04104c9403102035598141440307400042101019500c01080741807141415104014048a15100d00d90781d045845500140c0c405400a03a00c0500c07070050b80b605d0809083c2c403458400441031103800e02d000c018804500511181c413140c601c141c000700d00442d400c203440880710341e42c0182e6142c030340d589070581c100102d905c20f120401c03000d03610710010807003290091 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 914568345 1106 914567239 914567263
    0x1b030203090402070503040e180c01211a01021e0303010b0901090305030c1e0d090509100801020d1d0f030901080a1404030c0308060a030b06040e011805 67
    0x40c03c0340c01c002d01c255100d91000c1000e01c516005102c00d20f41055421448100c80c1d0f006e610520f035209a82c030343c118108100143c1c030b090f61901c074801c051100811420103200211703583c3d200e2800b99510380389450041c0b103038403e022440380f112000c034440c0600c14005185076070f0a20320822041e600141d002410004a003500102084013480a49180381d1844060b1151201e8032081c0c0d2114401c6084154092b00700c051000c4c10ac60304004035008807581520050426961040f0700c0c94016400c3d840603405500000b0343d165113208551184204051400301d088480c0759a5400658940c45010f4000c1c59900400031424158000e80305142d000c0380a20340030070391a01d1032250408005094800300c010480114200b41007541000025601410075511104524a1038440c2c40c1d040c18040c180f00d00842d92900030b088000c42c290802c1081030640f49100354052420316180741d48041180007 = true := by decide +kernel

theorem cover : BRFrame.Cov 914388489 914568345 := by
  have h0 := BRFrame.cov_init 914388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 914388489 ≤ n) (h2 : n < 914568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
