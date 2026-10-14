-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3379
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:29:44.285637+00:00
-- url     : https://prove2.me/submissions/aa2f8100-7ac1-44a0-ba2e-3781a0b7fac9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 607553956 ≤ n < 607733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 607555206 1250 607553956 607553977
    0xc0902090a060215010905091f1b0e0306042a1503110408071401030e0607020607090b040303140717030103080c2107031d0604060e030d081b0304050c1203 68
    0x1d041c5555903a04a850740000c222900c0040943c0c4010803c255850708901c1c0c01950080c16202490740a100e4404002c50341e4240001d1981c07258040f80300a150f61b0f14003000c50566007052840d44411400194584100070002444074804080308141c1480c10610003c0303900d012035100044540301c84450541460349410f07040041c1c148020703501d12044200070781d41203550400080500d03e050010b00e104480720202031504165031041d04072030841c4204034550040c1243d0f00a0805801d055000422107001074106100b01d0404000420009500099034185050091b034110345410040c6001c05413810141c0712a07210340da0200000c414032107030000401103107081408030b544a64206005004a801644146003020800d01c04403020034042d800c0b80100e4009460706151000c41400000d0180c0c10640212001400c803070500c8c212410100103a00c80c5d80b085092942886c600b000030610070043d9134881560910000c00132608004d4104004d284290004229490440c0d00302c941d40d42c4c0360000407604 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 607556456 1250 607555206 607555219
    0x11040b130603060305100b180f0402010f08070225080a0b15100c08210115080a0209030706210c03020c010515090a0e070506160b0903040803091c0c090209 68
    0x1101c901030322610301200c1c0c1c000050320300701032030010400c028441c101c0040c0c0c01040030145581c200496070740440c8110070302d185030b4529007440d000040c00e0b80f01c1a400001030110070401e0001e21500040c030710010401c1c2030a51b040e030440640341d12941e0328007640803408034482c00024104000300c280317181d44516070442c069803111482500b00b1550640156031000840e82e001d80e58001b00d02e054009000c2590700d070b08201c030201084031005131006c009a001035005d0740e840c110a0f231411b902c10303d40d58000d8480c06040d0f00305000c8200298a4030000c0c484d000501c02d103841c202020350081c024808074954014000c1258034845c02004d0041d510281c00480554600400209500341420207154003001c0a851815960340d055071107001071441c1d00522290348031311400014180c0c0c0c0c41c0d00500701205503001c91a08846940340000d848a8050822035003904180030034014100004143d0f85414002c03142c0907101560a2041c0380b0206110300040e01c90f40c60407801060030041c5800074003856000b9541c0d0f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 607557706 1250 607556456 607556459
    0x30606080f07060504060e1206042402070218040f060203070306030c080a0c030809181815010e040803040c23030d0507030c060b03072d060f02060f0a11040b13 70
    0x415494610b6070080c54003080c0d050105200b414131a6080310021007001c0c2c9402d12404181408500e020003c03582142d48031a045407070b101c400b00490302c60000c030944140650030441c0c690f0001c0c180b0b4214a10030a50a07802c040004c00f03010122078951810750308a0343c1150303a07003058100200504101d00060b50008031860780003401083c0007601c0c55105030040104c03001c0034159907490340554040c000540e4001800101c241c0350480300c00f2598040c403a011807189072800c0c2c9491080c10984005030001d410110b0200400c100340b18440da00303610640c480c07000e951300da80310703e010300c903912150700320086404404d5603080040708001c03441da41000081301120000207001e4070403101403154440060028820380e6000000420541140c204941c0040c20341d8001500c500d00f0195090010326440015403560002d5075a01180307100000c06040c0c9454480903540c00010060740c2d0303c00140c1801c2142c00c5200008450740b40e0756014504002d00d181020b81c3c3c86640b000c1041850300404c0e0441c44801c0c429a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 607558956 1250 607557706 607557733
    0x4091a041e1a0a02090303370503040f0206070c060c020406080d050912120f07110105040321090e0702030a09080a02010c030f17010306060905060405251803060608 72
    0x1074080045500c02c402020380968075038a481030b031001800d0103805a4007400041e0350740d40c05101415605c0319441c2c07040444c01d10740850418200c9000d880314541034030200300001c03286e0300800f01c0b039000d50449220401e250403407011544920030380700054401810030001003400303988028040c0d4a240210703020301c40350752643e010036200c1c17840680d10004075104102403401818902c490310501030000041e10010102e444c0031804950014030440080d00000580b6804c01c40810000202c0200a00e044ca0905003103a4035010881e4480070300c0f008410001c030190f49503a10a08100340905601c150740542401d00440c003030740e00c0d040030310000d020916001000c2801180010740c507001a030140e540030558501924281d5524401100c0d038000c208076110715070513071114200d080d4000d503c506000505070385007582074021504040e10040c40340b8100b00c2840240c611484116058400e80d14801b10101400708083d01c410a54030792654115070345c250000284140f9922890440e04e50130142c0f45810320208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 607560206 1250 607558956 607559003
    0x50a1a0102190201120e030a021b010813060e0f0f19020a06140c01090f06060801021602121009061407050a120f0209131a0a2304091a04 60
    0x200240181e0100d440282940100d00342070001c50b0060400c0c0b0099132100640ba801e441038002c00780d00a81c000294221b101d40d041000112149540921001da0346043c400280781c5440580560aa42d82c11461041480300076030050009440c03a8040341c10005959100b96154142041d0034520340c040c04852400c50203200407110750240d4002c203a601c50b1418280d0030707604840064419002d081d001c0c068000541c000f44900c80b80313103005100030841d1031034519106003030b107070b81d80c100200a9006125440b4182d00c902e542c007036902da0445400703803040711400e9418580030703d6006c40781200b400c0c0b040003010311565500008025003030450004490781e82c204280c41c0b07407045041610001c1c1da620022030115860750300c041003002e0b50f0303100545004880b000098482c40420320008039141e6035181900600001d80707500c0f50b828410356503028007038a41104600040c00d028029a6a81c4100c25254001d0b82c40398451016a03511180981803424850f8030300050080c1100c044032409003485854003640c0218 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 607561456 1250 607560206 607560251
    0xc030a1d06090a09020c0106051206090d050f0d110c10060311010e061b150705030906060f0a140307030f0804140f0616050f1002120a0b030703020105030c040b030406050a 75
    0x280c0120302444c54509054025071080300307210015580d503000401c1c0c2d0390f500300b00604240e0030703400102054109022141e0130541000d0020050200810089001c1d507850b80a94040d01c042050000c3c07011606821030005201d0034240b907205004501c0d0060101c41141c3c0820700352400365400828202d6884010368500030070005540e0300c41c0c000e0154199804901c1040403401a0394810743e88240d0340c4d85071361071010b0016980398007c60004810481c440900700a410b61160007101d40f16180a664000704100000e54000c6401110080a6003c2c49840070025030001310340c046c10720321003200745040c88500358006005401d08824681950003461030600c044891162004080901c1c180450401040b901d00400007101c0a000702c24648070380030f50520010006e800d0400e405a9078108505440c0d03645803000b08078180847c40d0110340811a10000780c0c08068903030a0030f01c2c59980e11685038401c1310f8051a0301c1103038081400820001000003d0f0421070181c012138a092142e5807040380d20081048a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 607562706 1250 607561456 607561459
    0xe07020a061508072c04030806091302060313140601060c02010909060e15030a050d020708070e1303050f07170a033801030f05090a1a01030c0b09060c030a1d0609 71
    0xb124140304035090629000411081c5d04a00a14484009820490204c0840e4141e022984400810500e418001011540501c02c154902d0701d004607640003c125010203071803002c0d003083c400150300802030060f95003100e90780f000045032102d40e9166401048442c8181080340002c4150000007243d060034011001038859003a495000c0f030360b40c10307031420700d100c03000a0640c0e06200d401e601c08045103046c481d46c0d01311003855018242960a01a55501c1c2c102c42c0ea00000c1049605820030428207140090011001e0745850100d5030f8a040b00301610050054010242034103036200148440469010010045030070b082d10301b840001c100c1c880c01100040e01d00c0300b4a16a5100e120b05000d1000700140010301d00030705060000c2d0b010040c3e03045a080380d504440e001030a900c01940c10040c4136003c1045100b00c814058001495070443d0340d4a4800300c07281c82100c0134190049804c2c40d2a6440806460183d120202103945a064036200101a4803142244800441d8600600000f900b07049040300c400590 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 607563956 1250 607562706 607562713
    0x3053003071209080d0f05060405070c051902040b06120403031a0303122809200619122f0f09091b0f03070e040902010e12070e07020a061508 62
    0x720741c010b002030641c03c0360403620b15100304501520b010ba14852840d403111014000501d80c0341036030500044441c0505800300380400c1000d0b802c0002c0380062030001550038624002c3e4018614030102c0d02130403240032055846200071803108035810131a03801601c01d50080c2c4e001c0c01600c445182c2c10110854203d0282d4054104015000c0709102c1d01c2981500b0280c80c05a514803890340040c0c0001c0342c203401e40100000c0d0b44a0b205007080c000a488103078129044406107800c01e50020000910344c0c03082840a2a205c3d00780b80c81e400406018000001540c11003800902c8000c0c980c04000805501500b5002242900b00c0602048965030300f05407540d210104900501d0201c00d0720800c400c42500800d9440900d4500002c0742d003171a29040a04500c1c4810411300c0d40703a003005200581008280603541c0c0c0198034011900c0c02503070780300150301c1109000f80c4e00003240c8984283c1650a00312a90000021000010f09101240d0303800500d00b1102c0740205810002c102e51603207050080c0c1028814000c8aa2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 607565206 1250 607563956 607563977
    0x30a081311101101050a0c090f0e0118091209151125091a100302031e0402030a0c081608011505040e0f010504060506090108061e100305300307 63
    0x8204a00300308640c19403c0440791045500051030940d502110603841142c0c480045016240d00b00c0d0800c1c0141c0440342d13404a10a00f44148401d0183d014492242c8140b402c40c207540000565501420381217421080100302405207101c0a03200206500c1201c0c4c0881244074040c9005100e82c9464111602c0b540160080c02158800840b0001d031944008c1c40b4501000c0000440392564490154803212003888585401a00010001c10f6515107100707105050042042043c5404140100020424954031101b071030349803800800c3c075100b005c0c02c004002c180c00410100e02c2250008203c85000a01948100e4458a45420034241e60514402c42001d0b03640000c00d01151809820a02840d0040b0381156005034052145500303544095500b038404640d100d0511540303040507902e45024028241c0100a039061084110503501e9085c0b501583c9a046807020500314109189501d00a40c1c002c4111200c050000228106042400c07400e89032801d100c07245140c01104440940e03204036041d440e120341c04d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 607566456 1250 607565206 607565209
    0x50402010c03050c010e0304150f02120a140f0c06010e01060311070f0305090901170601060f1d0f03030c0c090f090a03050d2d0b0103060b0f0708040f0602030a081311 73
    0x5030041100e0304c505540b00d1030111441e10041016100a10b21a9084c0f8040030a5030300103030000b54101c0b080d10440d081104803080c500400000c56404040e98a00009403402c0b60001184034024542d550b50400b8000600c01c2c02031000140c518160742540c00c1034103541c0da80700c0d41501200c1151800032107610301402080c1c0071542544e0302c0c210796030081c1091071900784a00001601039009030048684284100000340d04400d080001038050303c07aa0070080280e0311404006040c0c0444486401205888458002c0e00e0b51502c0a682c6200000582280e44841c00c0d14400d030344504003244454014044a4001006000714400d01c034000d1500c5006004043e4607510100e842d42d204161449106031280300d141150000920411800c0801680300351410303000140c6141039409450300300d41014101f03681480b4041c41401150001c4d01c0f00750460b9901c036601d180c08426401507030300800100c00d10f044001003c0e0780101c02400c3c400d035243c0d41c4c2c010342d9846050b5a1222031104c200a8510070320001c0e40c0549 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 607567706 1250 607566456 607566467
    0x2060114150708041a0d0c090609170f01020d0618111b15160e03061b0d060503010507051b030a080c030c07140c0112020909163609050402010c03 64
    0x4140c051501e982c0381c80e8940c3c1e504014414403031a4646292000100111518511b102d10350071f50410b4a00081c4107860010010f042070381c00c2c0141403600300c40c0c00d01c00240f41010484010b007403e18000070f6407036030103d405000041075640300d0070740310080c0c060948262004d14400d04000b00c48101020b402e180c240741000000704500d20014485104110201d91600703490350003644240c0084101848403841200b00403c07002da903400c0207029038030004c140f0016211036002c5141c0b108079616542d40759405651850003801d002d90180f9019441d100611143c150700100034000b5202d541031036985a612a175010b84c1e00d1040243c0000002d03030324404511402440710003150021581501103003414205d468055601440e070444c3c206030760017030704103082035600300d41c0843e07148100d40f00c21402c00700c140000c114440b20042140c1200403082e16800d00c014001c140140c1400e1f685c00c2c0b140311505207543c01c2130b0707003644054043c20301e801d12010000360444140101c0b171040d0f43c103a60700c041d40900f40d0b900b51403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 607568956 1250 607567706 607567717
    0x91518010e01110a03091e061b05070c0e0702030d05091005010812030f1801020a08060102010509070303231306050405031216060522080306040b1c03120f0f0c0206011415 75
    0x4a02d0000e0300407ea0141c4c1129a619005019001c00036000000099100001801c09111018480e007840a9408a04031540c02c0b4100e9002c5054152903030395600c070490440c0300c0d035005404403a28010511201c40c000082c20b48524001d0f1034208040c2c1d03211f001a542d50030101c03c02038407a182c2000000c061824007141d8507000800c440c42c541e07030a40c100441c80c0c00c0e42c0003141c0342d00004a0680030094190707824050306401140c120003614030942162002010f2448641d429180081c8544010701020f40d244106c40507800000c6802e140c50341c07610002800e41d07000784207040c460f00c03801e00b07100704500c804800c40d40442c001c20401c909081c00d5580f401c01801c00102001c1c040781d5250100180411107814903450144600c03080e0b036a034030306041003000711114803800c00d0140702c8440301d020510005071105030f030316909400c0c1400d0390701c0c185000e50090b14400e0106003030f06081040610a810407a040715803024401e4080d1562a0780701d5082050704894906541d5102c40840c580e00781603260380d4002d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 607570206 1250 607568956 607568963
    0xa110402070c12020a0f18020f130608150118050907090801020a0918060311061b071205060a050c0301060c05010b0613150c020d0b091518010e01110a0309 68
    0x5080c0007150701d641481c240503901c58420038180c0841d5100b10b1a100740002c010b881c8600c0524000c50620706811041c507a11211000031030350008001c002c0b4140142500e4990458264652000e42c5510005001c8941513941c40f007048062000e1020560282903240d0703841c1041c03450070441d01c1c988010018070400c054145e50520800743c4000c0b42e014000c5c0003c0151a60716180d0030502850940083c040c035a1000c000b6081d2842d0040900000703030a80f402092401086400c0d40d140c154200301145814012600e803503c80c450058005402800010050f050707a0040003614965901d0f00090800d0790402c544080c0034090030001400014050032940c006203029000028042c811200400c0c0c0c5540010b02d48409520014000c00c10514070b40d100c1d90142c402032424945441003075010a00c0a0451600100309148010001d66000010041d50311440000000c140040c100860b256443e030500030305264080d42410806021a001402850344010090524518103a0403810450040c09042c2c07080307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 607571456 1250 607570206 607570211
    0xf0f0604020f0d0f062c0712020a08010603110f0609090105090915010801021306021c0503130519030219020a092004030302070612090201170406020c12030a05070e030a1104 76
    0x1c1d004613880e6422000340d60721401e0b00280450385024100000035034880c1009601ca26110b80703007081080802c0040459504403a0400d4090b0f0510020300c1b0030b02190008001c40d031804c4000000d00c07000358070080b8000d400b500c2c0304a00c40002028492103201d403800507500705480c54010001400c0240029a022503100281d031000881d101155003003110a030f00c942c001c0e81d00858250703440c10014005200400b180d00080c0030000d800c080c038040000c100c81d080414004017200041c000801018041c08072036102007a40ca51683d41a007001c909201a80141e0043c49107860703038442001c402050041e826001008040c0a0345000c030040040e10031104007441012050603218541440d9201403c00f5621a070060f2061a090850013810500e440c0b000504d414100b010382c1003d80d0f0000714001126500c01000844e42e80c030b80c1040c6002c1d01c035482e0100700c18070445001d00004034061003c0d40c000d2442c1202408952901241140c081710441040c41c1d054021014180000d490001015805035020300701 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 607572706 1250 607571456 607571479
    0xd020325031509051209061b0303070806030304141201021306091d06010c0f020a0807060c0c0b04031101111f020d05240f04020f0d0c020f0f0604020f 66
    0x1265100003190228660040c03420605008000c0c1c009242008050340394800c10240c110390b1642030751810742000068614000051500d41d9454440c02c883c8a5540e0403040103c10140c50340c0660b07254811100d040000705481d0204020f85004800c50382111909400501200b61003001c1000411400d14165210f66080104600b0581d459000310000e0002d911004403407071414019023110648035000009694000b800c000042ea007200003c2c1e01c050300103920001495a900c042074040d42d05030069403851180400008240d9405031850a840c2d214411030f0b40b1007541c0e250510014041d0f1f010040901441707405030b8840d940718910b4098004080b400325885140103901242d4140d4291201e60012500080e9510812259006003a00700e010401503a51041306044880f402480400310385104100d4420000381e2231b503c90701a210402400c280d42c1d41d4811510541070010700e590764244c8007500600b85440c650b8107000c68400007801c4a50003924490340c856003002940b0b48644c0d00d1582c03140840300c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 607573956 1250 607572706 607572733
    0x1060f03092a0e040302070303020d03090b040b07051b0714010509060a030e0a12020604110306060a090c0504080115030b010509220204020f0703020a11030c03074505010617060d0203 80
    0x7103d801a4040e8015265481c11400c1c000d040c41030429400c800d060402c8000c1001422826956034040e0300556411085d80b41c0c0c6004960910505c3c414010004001c82410b84201c000710f2140e0032600300b5103450b007130400d622005403084d0142114044e070288041c03203507800280c0203800100c005224003090383d254002e29034501011021154403100107034441d500700710030041000035800300803000310024141d9242040c00a0081021400341100c0181c8640c00b00901c43d010f2030a440103800450020b00c042c2e51660f545603c503400c14401038030781c11030070000040c15017800001c46006115424031184250840303038000808881e030300c4049030400c0e42000010000010b01e030162258038460742c0501100c0d002c908080340803002c3d041d032991007500204900c60302c81c1c2d00007032881c0455002000d04100845110581e1010060360300c0c0c107884c203480c104142404038070010a60180860506000c1003d0790700c5180440300c0300240b050f800308c1c09818002245081c5021100b40150754401030454140194604 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 607575206 1250 607573956 607573979
    0x405090a0f0501050a110415030b0604210537050c1c060c05090f0405130f0b1e04020a030f17160218060901031205040803040e01060f03092a 62
    0x4282c5450755244244100c802445c050000c620f88043c003064109801e01c40c6030411114064005004c0c145e0740c41c41c9071069212002514010120307400d2808800710f1f090001442954444421240d0b4020032000142d040f0694065081d0901000041c403080454440d00e0740103130801810036100361044002c11069540c407080d865404c180180700380c04405010b45820f0090700c1810f401340f02031003024891008ac580320300420791403294046a011405403205c00100c1002c04440902400c5000c1c1c014008003404104101c1d075000d075000040d06003042030024000380760b103001614001e40c0312504040030804205206058607205028020080301600070140440a80d4881460703042c44460500d480c40641c03400b0600d80c080c28116058440302c0c3e00c1d1020004210401c14040141000900140030442c140f040040c0d40c0034103412801c59035620303101c03407001880d03c109120300070021340004840500c0a100f8001d42d20ba055021030610080e4140240160140c8030305c0c0c0305503401440811001410b480c041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 607576456 1250 607575206 607575233
    0x807140d030b01020f0105090c0d111003154401051518101a1b010f110a090b030c070c09050403080c04120809180f0603101104050405090a 61
    0x1e85000410401e00000a82000d400d0001c03503d069242208002051102103050030701442300b00c030b403221003040724035110300c000c12994040d94001312100c0031114016016445034280012645c2c100d030500b41d40b13507041964810740c0d109816050300c003211000b0b40c03040c148522004060500c00710700e460050452406003161401c8aa5102a203401c0d00c0311b41540c1000304003041c080f0200001080d0070301e00810400c607003c00d070307120f00305807e00100d91440031051100262441c41c42c2450030701c0c068140c0c10290710301030200245100300c2c0038940380e9600c9444c1003c80031104111a907848011829180010f000c10b2500014814115000c0810400c00020f6182035444080c2654510019481c2000c3c100140501c1001384408149001003106202c1c22a10085051820754011091651000403c010071444011314540400100d059810f12911103207100f5498030800c415421200030012861101c010b941d0410203c0440762000c10090085041507045103610040d0303242118019200d980c0ea074403401000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 607577706 1250 607576456 607576483
    0xb0706020910022b1e03091b0810020304030e040911030f0a0606080c0303040b090a03240f051e06030715020d080a1e02070201030e060123030118080714 67
    0x10303412128003034804c6846a01c4040e0b040080e03018512100409404110a000300c02e4140c800719800302070041c070a0b002140c82c641c0c0903050480c2900301c0c0d0803401d5a01004c2c041c03c641805440d061402c03148039882501d210710f070180d4960391031501d1081840003c201c0801d0555044881c0040110340703850800400c0070300c546450003020500c1740350a02100f11001d680001e0301d2608003c455001940c0c00106482c20b49000f120350643d10302d001c500040c0c1c45043c950000b0100303002d00390500350514500081030383e03800e0984020300803805140e200c442191011140300343e07224088042c0c2c0c00c48005028545a103c0d40180c1100c25a50700c2d075240c190808000e400401c01070344041d00c40004160b01c40320f0f40d80c01840844050090410034050300349407c6585120b011542c1e404a07100041d60310a4102008015016013a94400d503103440c00a0b0465042e00c002010400c580d91900200d418144070f00081c204200d80d0018508510b41d44407112940840019650300040c90125011070a080c02201c00103000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 607578956 1250 607577706 607577713
    0xf0706020d02240601120209041812030902010503011502011e02190c051c020322050a0b0304050604021c05010c02070501260c0306030106092f0a05040b070602091002 73
    0x44884000340360040d5034841e0038010983e02e0380c019880c1c50120b40590012000d08040c94580762500c0300c00300900880c0303a80c1e5409410035000100140c10040f0785a800d5000d0589200f4003082007000360251800460000e0028108000402450b08500e900314035401d00c600c00464400159082411700010485400b8281c40c3e000800048000200a00d0709440c4458102400384040c1c64031116280c3d00700010502c078800344444d540305114130038000c0b02c00c0c0455041c014205208906040070300e0001c503004e5035009041a030804a40b1440c03683c140d0388156070100c02001d146d512035090104204100d198641c0001442c144880065030a0080302000b03100380d402006940c0c41c00340010905440741d400d000c601c1e49401c40c60300f0f10000c0d682501da44100002a140d580751165000b20f0300414184c1d0051034031508d014080d5424209052003000701030918102548491000d100c00b4900b4455082c4010205034200020411003902c02c0207860064002e800050824000c58041014648a000c603140143c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 607580206 1250 607578956 607578973
    0x100b0a180311040c020723010c1202060108010f0e030702060706060e0c0901030b2710050409080309070609080d1b0209090d02011a01200a061e2301060503090f070602 73
    0x400d80320342c07000c45110f8170041054629080303038601c10130800f043d483c1d000701284640f01c0d4264011b40200f641c90707074415035000d2080c0707820000a46404003802030300025401e2421002c2000c48034041c1c1c070040300f9800081e5191042c03582c20040b007a07018040c2180c619859460008407001038208080c03141226212030ac0e0b030361086600040445980c0c0c03015512440d1042044440f030b40c1c401c42c0210b80b41204440c54055600c60140100000c001e5920684e0710a00300402d503410003902c0c0000e1401600c0c3e40c230440c0e1045440308026222813010b8085c0b10217a80c0329041d001c070000c1c8200850203c010440f82031022200442c0c01140d005c8400f1501e0000703542c09540640540f66091192034540c8030100c07022180303446003500013480c40d0405100c6291a0126464420707074003000b8000298440e070711540802100c2d0101d03030750f03440c1c020305698040360304c0b45450b608202003005440d0200740d42d0900402c55919a00b41042518280c1010b0007204051280c010028416001004900003404540d002441802c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 607581456 1250 607580206 607580209
    0x3031b1006180b1503010302060711090709060e0306012d150804030e041b0e15120124050a1b051203191a0d0201021c05090a0e100b0a180311 62
    0x5420070941e0f0381c01a291102421443d8100d40240d0f41520745c1183c00d82e68400180c01d04049103844845590350150300035040c0802c1030b410540f100100c816030380302c10104100e010101520390710240301d10340190844c0e0170780c03100009104110b4610510100c1801c02c0c0c15865107150600c1510410066002c5a006802ccc48103064100d00c5004a106044174203101800062000c5104080c501c3c0f50f1505100320030035100b945590b42c0c9400c070249400c40b900140c54810351101c1040003003088c41916548902c50065000074407a611519417003903600d864103490000c0004048840c110480c20b1440c2c0e04c00380154401c009801444407903000302107030601a03140d00300080d1961581e50145041140705242c80304541c0392078811011403441c403200b200c000004806070700050f4244614030416010390020840603080321078000c8040d004911060b82d000072500d440b01a210707101c1c0800d8070102c1c1161000d0004003c541c041400600c6012210320f8461181d400c415440c802e0b400341c541040350001e40b03200c0c241d0740a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 607582706 1250 607581456 607581461
    0xf050a03030618020307231e0403060518030a180506070507050a05060909011e03050f07081903021506031e0a05010f060303050406080907051809010c030b03031b100618 74
    0x843e081c0c1400310b14604140c000030301000e480c04c1d8400008201002c506915035410400d6941251060b000b0104450840d031082036140d100d4002124454a008041102d4000e2010816110010040107601c0d09840003000c1d644000301040b6524401c003144808600754442c10040c080d2a407265005040f01e0b414601000601810741c1c100301c0c0218000d2020884556519090604480e140035811215000c1800359101c0c1c0482d82d007016080d440781c102800705445d07001a0780411580048107840c1c0c02880c0904d01c03000d401004101400592000a45440b01c404031050990400001400c44211501642c100729036403c09240f02c82181c0c0148a1800600200b070043c050307490307502d8004020160031558003900a0050340901001c200c590800101c00a40400c04140500001800ea03a444442c0503da4144d88404699281103942441080800c1c103009000384200001c004000e141480d21903203800903114604401040240b141e5080c65480703040364484c8501a0420040b040c03c2c015011490b82c05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 607583956 1250 607582706 607582739
    0x180609010e0c1b0102090a03120207050405060d111f0f1106090312151905040b0f0a06030903030f0e1c090f03060f0b03100501050312090d020d0f050a030306 69
    0xa484208904200d80b640c804400c41e940c2100550f800030340c07003600241c224024040c103d201a04841d0800c0c010041c071020150345200c5141c20b5003200c04c5e190b280c0c2d080c40140d0b002070754403540010b181500180002da80402c501c00000003c5c10035480016141c1d03484480c40210717038041e0013140d440d10b040c2d120036071301c184414085c00e002d00081c04281404554a6031f00d00c039040c0c206000417002c1c2d0202e103042c2c48051001d0360180d0300400182c5100f050042c8581114980d10503148640d1400001d11800c1c180752203000112000140305a40040c94042c3c2030b40074004c105400c40806982d8011700210488502c504010307041741c00d000345206a06800c1401c1e0a412642030381d01480441401000010940311200e4241c2e0381c000d10104145210100601c050013405101e585c0c98003030302c0c45100b800b19441d8017050482d503044033207503803401440d545091248aa800001c0d0420746086d4814094100314065095480c4545507140080c00c4940340c003400c0c4450441d0131400241c6503a02003141c2c07522043d1164 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 607585206 1250 607583956 607583969
    0x20d090c0603060608091e100203190c110a060203070e2d060c0706051b0105090f100603150b190311090f06131a060a110d090509010e10030218060901 66
    0x440c80d09088020b2552109512100c840200c20091f001d00c0924003400000c1369500501802c0d0b4403810000180504800051998070b480341c40e2842004c0007a2003028020480789014015004004542e01e80c48040d40c8010001404c1c4504a1200f00494444400014403400b00a2540c0c65081402e0004d000340c01c200c030689442520305000c036105002010541d20229015070600755035a0410315402c0307035119815850b0121552800b020800c5184001c200c41c02003a0504081e40d5a4010326800b03901102c485000c0540441c0c3d42c070321070001c0c08180b94800c181400700209098842d0304050350721044418107800440726180015098841c600b054a030f0319800108040c099116072800c24042801801c1001c0a080c1094503105840ca0004002902e0b040c01000038240954400d4914400f41075501c00049008852091140748001288142039040580d107004100320301c140d203401e0340e81c244500d014111620002c101000003005a6540c603c24054800800140b402441d192080000280301648200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 607586456 1250 607585206 607585217
    0x402210a060f05100f0309080706140a0509070504050c07171b010b0f0607020d0b0907050109090c21021c06080606010306260f030301060c151506050706020d090c06030606 75
    0x621850f514440000071113016031800c8121055500f0048010f8501801d014180450000b07442081c0221500120900120000030002c01d450340c82e4050101c6604403081030040c1c00c40c5206001500c0c1603000340d9000080c01d00c1186c18405152148040380e10800c046414200300024480303462510070341030104071581d42000708030303c110080c08900d10701000344105218140000e0040c045594400c450852103402c050f140d681480c0c014140d680e00d40329801040c5c0403909089002076084c5c403c1c040c540d86003e10ba5074901410200c982c180d024207200400e41d200c075a80070310121020203031600c00040641802c03a804500c40d0710b040c0555040c04005080c090400d41004000d1003030269040300a41101e0802c0000000301811540742030030071038004094030301030000200001e03016a11100c0280300c0c9004240c0c15201040c40e80c060300403208002d4007001d01110155080008901070805809500e02418000d882c0a0900180c90100c0d04030840845890000050074002d03150300d031040c3c00143c001400e00303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 607587706 1250 607586456 607586459
    0x50907031b0309120f0302160305091201020c0705010503040302030d0509071403012c010b030601080c040b0d0c06030515030313210c05190e0c0a0314040b150402210a060f 75
    0x8080c13807950310499210a1203082ca04114000b4400e60480d805600c103000550035001207481d00170b10030b90101c05014031403841c6c210310310380c210010700c2100d910094105c02450040c2c500001540c180e08000c00a40540c002403200d54502d8819005151040150a028180035404c0064940384100c0601515001c0c1e8905503500b004140d0038003d000300402003181811141080e071145502600c0c44641c040c2d0940a07000c0001129180000c017403070504c1045070248403210f1910148040c0601d601070151a900c3c035084204111400b80d807100382c101d608030352160301140d440400b0a20315403102d12140c0803440c510341d0070413110300400b100c44044054401d40381842c000c1034507030080c00c403600d006042c800c0ca130b8502010740844500f81140000c1032140801401450700302100031060304414036800200342000070a00448500300c441510980c0d2001080507961540e03424a40084810168103411131303801c0216601106042c24040c03040d0604448281003442d1403a00c50003900d4451340600b100c03082c0e1210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 607588956 1250 607587706 607587713
    0x14071503110a030911100201021e0a0c0b040c0e090303040302010c05040602030403150e25050919020310050a0b04090e060112030804081c020703110a0503031609050907031b0309 78
    0x859030b11201034034021030014224108038000c0c511034100320b513200340801c40b003a42198040d000f41c2070503560f101940031000c101c0c1c107404000744900e110b41d000217050854408000740700e181020b40c0085c0100030201e05180c840d0347e40e20310201c1c140c954503000d5102000308000c140d42401403004201c03ca01c1d046003000e1600001039900e002d03a0100070248045109891f001380703590340c0440025034008084503a404410701c440603c244079800749255510400b040402c1e642171045240c1d005603045040b0400308516400014020741014100349203804822070001003039559103403070901030f20750041010786c1c41e4500140d031800ca0320310303019000307858100c0d00040001c000590807848125030542811603c1d641c0e40e145c1a641c074402c0710500c0650241c13003150400c4811092b8050007815100303445002d40d15180401e0713140d6a9002440080040c0d00070000919001183d0b003ea0300b03140d1035800e1a4680a03215000100006001c075100310001e565035000c65805e0603212501001a140c03404c0820244003ea02e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 607590206 1250 607588956 607588991
    0x90b070c0b16170f0601120b010c061a1807120e0d080405190515151513090906090203060705070b070f0903120233040204051314071503 60
    0x1401900c0d6900203000b00d082181c0141034500002008071648032161902100144030b041040d0351540c0025841039000b003140340984a4452191016159840f1a9109540b001d001d01091881400e0001130008401c0e240d0301c5046121084070881084441d0300e1802000040903200c00e556801007460600106001106000c01c222990041078580211550750b02d080583c40c00c00403000c07101c1c0a400e2409800c042c0540030030f248250381c1000200c9070301c07a1210b03000c0c4a00d0100c2d020a19034000c411514405100107040010904c41a64051080b10b00b581c4049a40441c2c1c15110141c503001d4480e801c490840c80c00740300144e84803146041890800d251601c40074885000100b0441c1488140f8040341101802035136204011603000c081c4126405000c08000d4461050260035081da4011460201020440455818189003519503544169455400b00400340c0000303000206503007480c51140e000705844c01e0380c484102d407000c4010030700c0900d0700c0d04007230300c0229506200c0100b500d0301d0070300d00c05070803c0c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 607591456 1250 607590206 607590211
    0x1120c08010b130314030403122d0e22060b040308180102011b0302210106270b13080606090708040f140303070e0918030412030e0d06090b070c0b 64
    0x22040b580c0700c0c159006500b034070080f00d400181c00e00000110f0825818400401481524400d02e030003000413420040c16150352000304000f070f001d0018200d2410004075a0440c48407002c80c545410b001c00030100b000b09202542c0058824824182071400800c0d118030760080e10300420351401864031342450343d291034000d40141e1041c01c6c0e2507550000342c034016030b20075000303407141c0f040061a1040900100034050002d51186051600d101310006688204160210026040b19410313240d6500801101315122001450010000070044802350301003107065000700070f0061740c0e04000b44020342c903007008029864510000d000600c1400303c90b040000256100c0344130343e00194400400c0c3c02c00304581c5001c090301e0345ca458000900e07100c00300800c2880e07030b440440852804410b90f52400107441e80b000369451200e5a1607100090713407082000304010205038501440b0140245413100107907502c800050407200641c40251211074481c02c4503014045510a6190095804d04000038645540e03a00e140204600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 607592706 1250 607591456 607591469
    0x509060d080c011506050306090f01050303030c0705010612030207051309020a12052406010e0901050d0b0c041701020d0b061206060c0f0102040e01140d200105040305031801120c0801 80
    0x4110141e0320b5000b50400c020464202e04c22280c82034543d04000c229070421582d0354400d482c0040801c0c20941200319140c16204060007462440c0e840c2e01c1d0081c0503622082080300c1566860600180e01648840540c0c0800d2103503014050242c0b5000802c655018260a0002c2c0c00d8540b841d8040140c0e20140004115101440a9440141d42d41060750400c0c0c186c19502c000c0310764564094440e8148a0001e601c00c60098075141808840d0409100a140c002d00a59401910707031240500440d6032802010341c86075460b81510715040c0c88441c5540382c40d848950009641c1c0d0042002840c403886030040da8000e20f002d803080c0c0d007011846a00a0000d07900030b061a8001c184c0011030306580507091041c1d101c00741201009641c2c580e0b4171344514406400922810507907070950000c1e86083c0c42d044403800c44454000c40c010b410920342c140804000b940000034641840010080040003070001d1000c0d043c040625200781040030016070014000c91000c19020001320302d040b00f01103400e40c01080c41f9054030350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 607593956 1250 607592706 607592723
    0x60e040b0402090612011a0705121e0d0609060b180111070906080a02100f080a1116081902072304020706020301080303150f0d0b2a130509060d 63
    0x49400309000f44142285160013040000d648028001d0f4940c1580c100c505480ca05030841280303042950345030294440080c0250043c5060703240100031840900140380c49004000300144a41c5540c05480d40a001840308a03a01c0e40c10401c001c002c02d20070038005044040c0c00c00d02e8030b2440c006d2110000f84141e4100d0500800c016428000d003004c205481c050160a10308020850f210400640d41307a0001008a1059160000c00c42503e031103810300c0290804c4070b445488050705c612480001600c1408581411703048107103c2c18400e0b62024596840007801b94990035507034015210b03881c10300c1e0724074003aa80a5600c41c1c1400c009840904038140d00012018030f101070041c00c4400054041d1141c9000070b05881d00100000c900090080000d50040c040d030b884080408a0b000e06000902d888c3c483e684c2d5104024401100c0850040c40c55550701c402d001440710420404110403140d44406c1c4500c107000c807c000f00358001600c500c3d0401801034a4112100c0240e0701d403440c006000b500c1d000340300414a40707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 607595206 1250 607593956 607593971
    0x22081c1706060a0306080f01200f03040818061303031e0207090f090213020a17060604120201181412030c030301060c0516030506070909090b040303021309140603070807060e04 77
    0x244645d0194002c0c02d00f05042d03030304801082c2e9403680680304c1d85c081c06110040a03030f1101641d178036082c05ca070084103e036480c0b02d085942e03688894181da00009445681d601d441c180c3c51289544080081028088031421850b1071800c42c14020301c03d801c000ca1180030814500214250707660009030780302c200c40e600c031008628055800280700140c151543d0094008002c018090341036800e40d0068019060181c1c1d9114400150703040e02c404a20042e900306802c000c0800084c0917a040d80c030b40803c030072801030411303a61000304a0307491f80c07104000350300145410010407041d1b0242d24140b44114243c04070140210708000203188919120711042c407510341807080521015003005400c0c0540006e40450303200148085582c0e0500329103c01e411203003600000c000e0310010508009503c5035002d400d401c903800c00b445a42d2650194025400100c0d180e406107080742001481c1c101e14041d100300c2030841280d081d904c5c1001c03418980341041c0e0b030f005641c2039040b010080c80282c0e80312001161561040b600800d498 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 607596456 1250 607595206 607595227
    0xc011205060103060807030c0e0f01032006120a0b15090a09090203120712080a020427060801020403081b0102030912030a0f020d0e0706020606031222081c170606 71
    0x1044d85a001c0d1006000b901c10001c00e1081100c03080d011030b403034006941500d640d40c16804040b014240001001c42c9203010020004103d5000c00d000c280801a105910f00310f0410300b107113a00308046a1002c00140c45550510320750603d4a102e00e04100403180850031303c0c074444009500d01d400e60040100ca039594110401c1955020030103034820700c02c40c04807607940d0b15032410000310240001107175502182c0c118010540452040c400c8a04480c070a403042c114030091003440038180c3e501c00c4841114143c4400010400202c03e100901c01582304085042e41c074001c52100c107a92200403044101203901c18170130840d0031600402c3c80042650a104d443d65255611803200c1e00800c10301c6200000a407000c80c1044002e036042d8001041c031100e100455401c15a42d04040b030b07840c5821240c103500f5400205950250450700c502074131000410303444460800e800d801c2942030300f03040c40e407204403c0c0d842161402503050f125145600c00720310916000e119640d86c0c129610400602600c40e5014010004210000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 607597706 1250 607596456 607596461
    0xb10210302151b090a030204090305032202060406111f0b091302030604122f0610060504090b0a0302040212010317030124120903050a030c03021c0209060d02031e01080c011205060103 80
    0x2039a40248200140c1c001400c00802f6500104d03514400500c043c05180c00d10200e000302219440e50040c001e51401d401e1400803960780070303803400e0400fa07803181504461651200c4183c0b40c03549100710a0004195105404121151f03002a101c204400e00003000d000141e100400c94036032181e00181c140c1480d1450394002c0303a00324422000c581070344005103001500381ca41004006212180c402c1241c81c0f507103030b03080480313444400f500c16a00812400c000802180b001500200117a4100410010700719589402180c02c0c3d0744984510040c5c601c2034401401000341c44650300d40d0000c81413800034215810606040008010303061030524801071040c5842e00c81c0c2c442c0c92031f001400ca503600c0c00d01411541c0d00c0c1c09465500300f07904401c0482c0c00d040c1140040c43c444d1003540c8844210040a04100c3d441c2c0400350000d61046130030a4024504011501c014131007070009500442015069501202e5010184001c00406810401c8203801c402c0c180d00c11a0303809a41c1640900c903694001485031903490040e0300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 607598956 1250 607597706 607597709
    0x71110150902131a070b0f0906180a06020d0b01140c0a020f041b0309110316181b0207030309050103050c0a0e21011d0d0206040b10210302151b090a 65
    0xb1120021300080c101d01200c80c0c0602078261044c802c020a0b0b071241c1d9050408468200c1c0c9481c065448400092030400d40140a610b02031414001d484103501d4603120311041c9d92141c40310f050090f45400580c482540e1015190302c1c10541100303110306000c3e0300c1d030466840785c80d6508041d124200800058080d69155030250900310f0880e120000d0a1030030b440041c0c080d11040b00103070f03840761610218281ca03040c0030805442c161640302e010140d25042506136160300300721078064075901d5074900e49100108124008001440b455800030301c412469894001c210a42a07004141054101400d111068600310b007035810200460401c801a0b444880200d00740708440d0900010424070400c414480c4001980030940300c00380e520150b5030f508068051340d80e4650b10050500b00503840700d00013030080358040c002c01d43c01c1f1155059100310203540b0340304402c41030400b0740030310306c450b01c0d02803c07804040d01040020319140005ca00304d0350520f0011031240402c0064039800710301010002d00c1100c23968078000e0100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 607600206 1250 607598956 607598969
    0x6080a1a10030b1003150306021c060f030c050301090308073614120a0305130812120708010b040501050a0905040501170f03120c09011707111015090213 67
    0x15094461030070014050401c0080361030091480c40350100641e4468050591442c510201003c500c1c0d14580d83d0300025480030650b54600400f41c040b200008200b40240002482d5001d104071017582982056800040d8543c8003e1182e032400d03034040c0c0000e1304455400d50100b07940c10290361380600c0c5004207564490b0000451a40005500e03464003c11341c00440c00d0545160512003969501004180505403240710300c03802c000d034400d601c8100000e20950040000340a05c0c0041190141c1d107868036898006007000c118409500411280f8000e00c040d054513600003018681114254034006112a8500c5280901e40c10002d0005540580360f001d0380c6500010080500200925a520641500c40c04000381b000260380c01244000d201407c4000151140030080001412850b02e807151958000e500c819142810300040c800300c01c01c00b05820700c402d440750f03d20f42c070340511010043c0348031814441c14820400d20340707151000c04820314140c12025801d88084810040e030740d4100803800a21851241d020a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 607601456 1250 607600206 607600219
    0x70c0303021b060c060c03060a09020a03050103060b010e0a06050c01150906050f1002191103011410050d030801150921020102060a0903170c0c0d0806090603030406080a1a 75
    0x405074000745003902c958001040018150101d010401240b0454910f100154800030214070160900402035801140040500081941d103003100000d070f0300102102008a03550742c00400507c00280038480320b2000034644165000d00c1c0c2400100e450001e03018810410101180d280c50200095202850309055080c1034911180d030384020601500083c0200c500444840f4080b02480c00c0c6000044603e04180e0040c3c8010409400314001c8100c4800050790388488020b81d8503619202032045c02d0703a085943c20428840e117400004044c6031400c9a2100c0e0140c481310b00f0480100ea03001c207a45066594100d104640040703801403c69100c0c00c80e401003010800034040a60940c45119418041384d8401e0702960882d0751480081801c0b60a6040040e0200d01841a4054904849405075902900440f211400d11640c00c80306850710220900302c8010500e04814440c05150000515a000c0e80880045240c07a0500c00c3c018803180d009407560614580b03805c03800010620854010480d120003a242 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 607602706 1250 607601456 607601459
    0x3050303100b0c0a0b0415020c0c0307050607080a0f020109020d2015070b09030909090d03150f0b0703030e03030c0403110a080c010804050c0d1a18120715020d06151107031403070c 79
    0x2c940780c117074003008ac9209201d0b070000081c26040c0b0509440405810640b21420034003c03e00603206050241d5062045540e038820010042e42d0711070700d40c07440601811030001168980810480d01099480019102d07540e004010900200b41000f110f854940c4400501400d440362600f0908d180039a40340c0f50340c4001c200d01086035a000001c2e207040410895501031212045069050050151f940103c0c80280c8140b00d060007070300540401005103520a00c1e0000d81845498852411500140d80c80118124000350400521042c41c2400310a1081103070000000c6160400081d561002000001d05001c036480c00a01840014028410300d0384020f4050790b00516180341c401d814409841c1c00050710300e007603004202c0410046a4140701034070010f0007496184040d81200169400903101100c0b8841c504a19410720f66890020f031604201d400408641c10b410f280d5815910320044641408020b80044906c011520000d21a07084a0f000301c03000900750500c030b03611401c500c21090302404a0198420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 607603956 1250 607602706 607602727
    0x50f0a14070c020d060c0201091703040201020c01210e070f05033004090203040b0601110a0c05040509010e071d070c0c0506091c05060a05010b090607080a020a020a03050303100b0c0a0b041502 84
    0x1d42700c0351041034844440c1d90003e00c0c00d48c2a0000703a03400790042e1300900100351594000c0c001e0424511030704071420748050f00032040c03d080e240603c082d1300c3d03030703402611080000700c1c40c10101601811044002d05290b1515810b510106001c444250303140300c0c42001e80c4440380769610101d034054084d05005661b01d00e00303403d103a98200b00c15a9014006040d100624001c400040b51011049a1003c16000d45500d130004203c041e04c070280c40d00f14155a40c410701840c00b01c08004050080202002400f005051503211150802c1e000300b2240c14010312005090004a044241006507001260225119644a40855401070742020400c1050192340c0002003031041c0010014440c04000d02d0070301941c1c1e00c9284001d0039020309842c06400150500c0b0240024010b071010f0018608580b04641000900303070001000b425044d80161515080003044c440710145015160001c0d0861029183c5000c0c80c4141066840340304c2070014054201c0000802c0404c42c4444803191102080c107025500d600c690741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 607605206 1250 607603956 607603961
    0x3040303020711090610030e160303090503070b0c03030c250f0b01060318030e030115030f0b070f0903080a020c060409020901080a0b091b1903050f0a14070c020d060c0201 75
    0x25803e81d9524035141c0780d1205890b00441c13880c030450f0054442c140c2e0100608003940a0701103043c1d0a6001e01507131801095006039800001c0c019406662000040c5190601745418107090b0740040862031400c100b10100c4440c00411607030089200102941e44114038000e50f90f0700d001d591555800024200006010b12104055903901c0ca80289951405640e844a00740c0481e0768044030070300c0c602415041c100100c0c4c0100c0c40b0260100000d000410b1300500340c040710511850680044450300304a4404c50140010744403c02da116100e07040c14a0300c280b502c00007800d2540d0782e100007010342c1d200091110b0080d1082c0000d0852080183c5400d40b5591140e82200180d0403502d03009000400043c0002c50482c600e00894101640140c4042c455458184038034004580712606d400d0240400c004002e5001d00c042c00859050b40c10390381c001440d003004400d02120000203800362403085d041c01c45101e483e010000760180c114140f0f09159010105510200d054503a203500c0103802140791003030b203810054064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 607606456 1250 607605206 607605217
    0x7140a0f1701050913060605030a0308040302161a030702010b040e0f1b0f0907020307080d020d0e030c0d210227011b021309050604210203040b090f0a0503030304030302 74
    0x20749415884240320019050201d07824441e003980510000d0100d25103000c0356026002c1c80340603501c080382161312039000ca0720b0440c8008003180092107810801040c980c0c14000e102d0300a400e2100d0044881c901b072841a8070864040102214600010100343e80d00d000b5844521042f41c00381084c002811481503040c0c03981d01c84801c450540c05211034817620041152680c20444100900c5044010b844405000d008900249071206510003013283c0d10202d400d0300d001c0c0089110000b00035a0707a030304520220069810320302d050321051388284500d1440c03000115440b601100e4920341114142c00340ca001072445412001c40c201c11a00c00200500c884284001c840c10007903100090501c0c008500e401168003506107050078101000c0340c00e03030100500d01502c1080940e0104600031415040c180c6032103040000c1a24125440c80000004000c29154404041a121414005541030a1030003e20489510882d642d0900c181112a04185590b076840d0964003c0c05002d0200c07512450301d480c0180003036103c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 607607706 1250 607606456 607606487
    0x601080106061103070f0c05090c031608010305030901031a22050601050a021e0129030d030b0604060804020a150809060c1e030a09050f0102120901090c060807140a 72
    0x80403804503010f4064089610204a031000843c5460340c43e8644c3c980041d0b409004684802941c0000a12640c911070101e00401c904241c0343e80e41e0402c0300d4540d00303001c1301407900b0003403240000041010400210503680c2510080c02c0c0800e041c8000c0ba8014400709486600300e0f484441d600d544000015004c20a020101c52a081080a5202c850041d0345600803d110030f8010b90100038080c0c1000c6040d04800d4184004500100f0385030740f60442c030b02c071142d625480d14117511001d1740c07031100900e070400c50005214524101000413400000203e6807030b20845c05500203104142001c00c00319210400703800000c1c54030990f032046544000d4002080b10340155041c24042c814880458508021141141c0896160560074202c0e8544003008004c6900010000c400b065a150b01504c0460002d024114246452000050b600c4100518047d000b520281c5040c415070f04d45032000002078841c0c5002403e940c0c1c2410300c00b180d9035a601c4206c0d09810000b1100c004a4804200b41804640081490281a22 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 607608956 1250 607607706 607607711
    0x50d030905131b1d030705220608030f0c0d030c1b1406040c0e010b0313120302090d06060807060c050a0825110f10121805030f1206060a050d020d0b0301090506010801 73
    0x610608155a48445010f00c80d84032880d40d235554140da000810002024241c90800702ea8503a490b000755065400c00311013125032175800500303810500b0342400070325008441ca0401b000f2800c1a8040207100b80c400c110072407511040c902d01c07031050200e0900c00c1218408c0c81c8040791300503d0a4942008602001d2184601c0040c03a1000424240910f10036244140c11306444106100c01d2915220480841030035264180340d8200024421501c1e4904c06a0420b4060b40d004a00b491512400c24a07140007680010200035040b600400021b101080301819281c001042d00c0e2166080c4441c4030a032445910071640d0b003401c01004000700a0000c01c0c03900310a000311000c00c9074205200074806403010420039800015002d001d0400c081e4260340c42103900c50040d042c80341001e0380643d140e030301e582e001440d10400f058003c10404150948a551690310940c19203030241421400a0042c055000340b00200d40e0058020601c2d481c11119640140700595005000303100502c4035050050300d0f07007000e0103000ca0b10b50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 607610206 1250 607608956 607609007
    0x3070b04051c1a04060605060a020f0606010c05150a020f040906060306060f02301206030105010f1a0a2604030f030e0a08070c0807080d0207050d030905131b 69
    0x59902d8800c1481c070b60045103441a41d8540c014101660f40c000303104840160b66400082003948400014140d203180c141c006101041880d5805494000b00404250420070400080800640e01040c180005460460890802d40703601c680c40010380180d04205035000c03000b080025110555401010441e945510f04020f416103c52044851800421400025a10004003980940110781c03170f0008081118140c5031a03610740d10541c801c0b90b4086281100721820310820300c034003880c0a201c3c103801845e0207075003c074078286080d682c44014045141d00000799140820954450f80c0034042c040d03480d019803000e00c410307441c05591511800f1030944058000455046003411746034024424200981c00c41c2005001d88546907641200c00d500080048818291410b00000c40e54020040d2030090035600d40502100c0440c8034000745040d103290710807441000c0c1410f0101c0401d0300401e0340000d407402500c68a5020780144a6031000d040da49066040d10001400142103d59000203519040e1082041e20003042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 607611456 1250 607610206 607610239
    0xa032a080d1b17060a03060e01090209060607051213090c0309060506090f0a0e03120403030b10020312010939120b0a0e04021206010303020304031a15100e03070b0405 73
    0x2c0b903000c203078046140c801d03a030310045200c840f945034041001840880c09030340300c0c0d80c2c007019994148084262070b0345404170001145040c441d000e40c0041c0030384640c1c1c00c000e5280c4840355250810f0030300d4913000c80000303003808445604000300c10203000f55400071b005101014a00a000308060700083c0d404c01d241002041c0946070402d031043c02a903004071010b0311a12440c101c00f00031b1260500781d90ba240700030003506081326034045060303200314041e403800030340300c4803140a2000c280f810701e11590464100304120710130101c040d10800c1c1501c40e101342c00074000c107904641c02c41d4145500002c9402440081034955851300082c0d1242224030302c1c0d030300c16200d50780f0351086070300303803154a0105d40e8000c005090030b0009200046e101c6600c140024042105102e1032285141840420303042507006030800942401802201c2400c80001d00c91000c032804a440c01c1c014980d40002d180c45803034403030000e0458000d01c0900c02c0201c075411100083c15a206c25a90750b400c0c041c01d500900c80c0b07070701900c05005081d41a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 607612706 1250 607611456 607611491
    0xf220b190b04090302151905040503030609010806101401140c0705040b04020903070306020901091e050108070f02060f1b0406030203100e1303030906020d020c03070c05090601020a032a080d 83
    0x8140d1580007400300718940d881c0e00c6c50038070001713101d400a00006140d180c10308103640507860103a800f410280d5500d08040b414440e640380b058114489961040e4248003078805e0407181e1104544807010010310744440e00004031001529180d4800d00c0e00008905803d66a0000c6800400c58008503020130980020405000580c011540130702d926800403a0300300b02091064005280c80314051401600c0c03291a0400620f40810741c403070488800c2d02500d41030000d9600300b2002500000d150801030200e0b03001440c001d6850800030450041c0c03041e400041441c0a80e02540380c444062003104141c1c6031a15008010001c0d04221100c1e82226040703c80004c0307560703003180791074010708185102d200c11540c191015406441d203000219480e40d400c00012112181070f10241941c034080c413014540e00c00b0541028181d041540e000140f10758001000d000043c1c3c2c0010301041003592504000040072603002d50400321000d0b00e4800c05543c014441c00204009043e070040003d1009204100b01c40d02c01180c01005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 607613956 1250 607612706 607612721
    0x90414090105012705060f0a0305031905040b0a0e0d0503040801200301081c0512070806120f063d0e010b2a0327040609050f220b190b04 60
    0x700b00100e00440013450b107441d00135541c09400a8800e00c2e014078288003140403503000c0d43c82650700f0741002c9403c0e440308a01e0891074441c40824a8a00d04190400d44110214400c01e035034601449050a00e42c4103c1d20f45a0b181003d0301d4020050b0790f110743d40c0b020840d000e07043c0405800d40388100301f0400b1703008602c0130083e03030b050b0303074080000f00960300006410080c5000011034100500c202400f11743d80d0360720000c2c14181b064140359561600d07414020b042c41003c804608a00c0320315044809141c0641c0c0d0005241c0791f001d0413440d010000c09a40c564220404040c03190054641014403500d98860b003a08801c54040b14420682030600380c2e6600319086489c001c9100504003c0e08070005a0300400311481b2503049105072106507071804110801101450514804a00c0f6624040307400f10f080c2d242070301c80d2030020030038024207005926010411807003020b0020315415440d600b004004190340c1d21100d00b0b500c0c0d241e021510998900340b81800760f01c2408400810352045007860319000d11801d190058a0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 607615206 1250 607613956 607613999
    0x60516021b2704051f1b051308030d020301060806030319080c0d0524060403020604051c14060604052820070303062c0a020f09041409010501 62
    0x112400420401e0901c001d00c5032400e091211103a03091500e4100340c50390700a42c4204010090003a00b4170b0b114080d00c2c002c54001d2a298904100f08101580e0040150020340c01c41c504160b94103800e11000d00d00400369040104030b440003080b15129040300d64001c50680d4000d80301c014403030f516103040664034800d48a6400c0b90007040d015010386a4081c03100b054006d248510070794240105c001c2001c086071340448102d200e1030304452081c04021511074250f07004d108140d4117689000c0c19900492068881c40c420350340940001500c85008012920070014603035401121031158a00f031503402580c03080c0c141d80440c030540c506004100e2007098200c0390b01d1062898815990b2805440c0030800c010110b0800c042116200e55080050001002c0000d00c0001d00c40d8500048403400c1018410700000140442c42c041c1c2c07290842d154400200c11507250b44960990300140c0c3d90013000308026400d0143e01d840580160400617407810301c0c0d07081c011413803199a01c40b000300b0a80e0307650102e10344016000c00804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 607616456 1250 607615206 607615243
    0xb0f100b09040b0612160201020315010e040b03030f0301180203010e18280611030c2703030d050103151e09021203070803041b080705120c040906051602 67
    0x10451580c4540c0036001c4001c1c000d00000303030311a038040854102d6102250342c9900c030b000345d0200301c4a483d680806200308402407000310304500d40b1014203103816400803030040c140a400302c452151a80c590700060446030000d002c0d00d4a0307144900c03080d91190800e0181c21219079918280d541401c5041c801c1c1c03812521b40c05203440c01d80d12200100110840070050000d024061142d0000001000c41c544420007100b0308002c510103038040c04c0050440b0911890421032400030005d11030340141c60f0050302c401010400c2c0d2401e84404101c00920701600d5101d03030355018003021030008402260b175444141201e0042001100d66803001a407041100e02c45503e01005400750103010707500c8001e60340107011451000d006480d02031902e2300d00318603541000d9000c4590b05400810403041016039400c00e101c02c00750a034814031041c1481d5029440d00e107180502c80c01507484a0242d101302c00c1c108000440700303030302800421800030313241480d40243c10101e424034041100014920f0441c2d00c0003504004c1600001c180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 607617706 1250 607616456 607616459
    0x1e160b1c0e0c090a020d0905061f03020a0b0c070305060106120e03070308010b03100504020d240303020c0603190e1606050a1713050d09080d09061d12010204030503070b0f10 76
    0xc105115030f0103404050465803d008001009280740306141540d4040c50040080349403084035000722038501d0b003c1141c006007500d405c10060700c420121100341d1f82d82d06105600e9201c2c40321454900b690355800644240310703ca000051841e080328040d41c030440c58138400d204000d51500865600c2c451050014006200c000c0100030301030300c000c0a180c000601c056243c48040d6102c000500b42d8118003242c0d00510b40d5400c503c0c0048460307071507050340011603001150250746540c80180d1100c0c014811103006034000000078003400e590030b5485180781c84a2004000800d40650200e0307a03941b00f8217140c51140c1208002064544c098000d4030300201c919a12490301800042900680039809824042d4414a45644000150081c01100440741c45541c40c079141620741440709213041c1c0030180c50420300c08420414440c83d940601002c1010190f0510502010030490118404584d2448404895413000c0b8000c001c100000c401400181d001e422b004a4545401c1c244003510388080e034140841c820110f10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 607618956 1250 607617706 607617709
    0xc0506040b040506162c0307061710030c03080d021902030a140301050f2b030c0606050603040b061c0506070c1b05061b03091306050319051e160b1c0e0c 67
    0x14411b064045241242c10303142c1900300403070300d800c511703401c4440400c0e2603a051518034400c1d074282d103034031501c1001e00aa0071441e54468015181e850700015204000000b0004488106074045942c0410038a14201088904c46d100949a401c144e00460000d210900342c50360651880d0140c0341a688001d01c00c1c4c403003941c05010401c4400848a52090070300501d5541c07090001100001107141d40680c440034000f05031842c0c51800c5600a0b080644601800d0090101142c1b607030300210346c440410b0750501e41481c0b103110100d0310200454401001407013907004102c0460703405140c2038001c5d0700c1200e02a01c8480202c1956000300311500075140c100c0400c1c0072003050404981800851010880306403407400c030f02c1e01c0204501702282181c003150161500300c00c00c80ca007001c105007802903094078141d5224203141d80c0c80369140c1765020045169489070300884000301c00c05010000c07007445503d0035030300c0c190755640380b0b407185410486070120124100c2d5844400e29180c0d0160841810401c00501105c03000ca40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 607620206 1250 607618956 607618997
    0x160b0a0b0a0608070c062304170304150b032d0106050319060908040810021b06100e070e09090703020103060f0b0415140c070302030c0d05060a0504030c0506040b04050616 75
    0xc170586a4035111421032140d441d80110740071410100c18000d20307103441d0034200800400707124288804c80d984200104404180c030116038000d4205412004a00e02502d070340060b1510010410261003070200c0d0350391100542c902080302502e400380704000d02420703944504050322000780f0301c02d08100181448050000505503840711503c5441402403a0800313440340009840c100102c02c40c440e486500090303c1c0ca504284100e02c7c4501940a0010101860700d1b01043d00b400d0780f5446000c110f4809213000c0f4050034051419408c2e000005003e0082c02c0ca0991140c5a07618a28403060b40421314009000c2518141c0072000003d442c18030800a160034a80408407040300f400e0081c1c2002c0000103401c504046034040c00070540e04800d02c00800ba82c0c0e0441c01018101a115039a461007a21224a07000008401040342a401000803000003010342d2241010b03a000503401a00030810b0003100100010441c003480c009004074050380844050380d6a10f404130900c0000d1680d80004190240311190108103400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 607621456 1250 607620206 607620227
    0xb070206220f261f021c02040f0501090e04110301060308040603021b070609060c15020f0703080133090905310305160305160b0a0b0a060807 62
    0x101141a5110844050072211a142c11205901d040032004101c4490040303100200005078001800505040c038040070f59401050440342d08000300402881c501c68465030590702d001905420000607110f01c000840d0003540540940884154810300c04a619481002030200740c560601144000c1d45031a140c00c2c42c12030b4480f21865040d920f450303005c000a01c0c00c00143c80288038548000d81c80b0044204a1301d428041c03c0f40f824100d60008004100965002450a0031150241081d9000c041795040c402042d244203146680e0940c0001000000c2c000303282c005288140c020b9540401590b201c4881d404003000140a00f500320500140c2c82c0c0041410403040d40d0300e40c01c94107180a12030790799101c80301901e130200d0341a4810741c4400100c5050f9100c01042110240544042c60b80704082e0355801341681c0200741ca2090b400509070340c45420580500111f484601c0120030084100b401e500e00303038001d10011a003160b4060705003043c26000b401c0140032403041d15015124401c4540d500d80045645060b007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 607622706 1250 607621456 607621477
    0x1201020403080a110d02010e1e1e071d0f0a11160501050919080a0f110709050402040f1a011b060f05180610060c081b060f100b070206 59
    0x200300000008580e02d008225804041d165040482c00300c1d403400d420b001c490010007013503904051800c00394460104c1c907901040c3c00603410300194900c8490181c500085151350044c0540b85904080b180180058804202d03016040220300c2062204900740a00c80180c9005074804020004100000d615802c60040c440c4e00641c044d041c414680038000148c03050881c29240e90b55107034240300501b14148050000c00c0b0b04844040725030801c55540b41500c5c41441c1004080110708003e401d420b0344100c1e5503100100c411400c4510180d1135070410030007054151000c92145182a50320051000c550041c80c0c1c856101703080c3d00c85403500a100651750184e012040c01d86c503000c03181c0c203103001940031b2084103403d4865210001e05450f021a440c4004c020b90401500c007640540200114151111f150000f41da101d40703024401443c586c41c142c1041e028000c000707084000812039082603070030006603d0784140c42c080610f130314079195005100d0028265000301e0b803540d60200141030244c00c0800080c4002c1c502e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 607623956 1250 607622706 607622711
    0xc09060f0e011a0d05100504061202030c0d0203011103250e0d03030915020d15080102030609040f03050f0714160b04091d060103050a030f08160f020a050d110f0d0c021201 75
    0x1320109802112030455001d55440c01600061006040500c80d0402408103006003142000399500000d5a404002c0e0201d0b124111804801085450a400440c0400c0c0901d04140c4c507804d040040d10900300101c80001d8450710206c02105400b44209444082d141c0061302d00501d41000c2d88044010300200c07070040d00d42540d51171000d0f900131729900c01070a419200d0200010038109008041116003004c0e4803000190380103109114542c0ea401c580e05410070b074442030030b01440605140a94407170040f500c2d240120710f40441c80c501171080c400100100b110b6440d081c0c0d89401e08a8401c140f810450380280c13402403006000500c01245983e010039040c0c82140819503691a6210109180c40001d8008071040e8100d1740380c1070f081542017403c04111000d03a0529404030706e40032041c3c9030b84041196103002042002000c04144d103000f030008450316504502540d5031b841d20f00d40e02601c1d18222107489038041c45480c1e0a1100900049202c2100c071010380d072900c1414202d41c00b01b14030002c20545810541d503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 607625206 1250 607623956 607623967
    0x10903080705070f060f181a030a0e06070504050102150106050307051303140f12180f01050c01050411030f1204050d240b0108160905060310120c09060f0e011a 70
    0x218800340c0c09004100b01d9840746d00c06420b00030700070150107283c0319000e03018900e0034080c41903503205000415402c0003001819100e0303540081a01c040c105054988000e030041c00140250309502c1402001941d500b1303022510340f140124622540400e0910400380056024404a642c0e203201c0c4000340131030960602007914841d102d03212200020b1041c44172000c954015103001114180c14084c00260a0201c41d2560130021040801100d035804c0e240e003544540b50365142030003079a0140c0c054884803d8040020082c80c9021707d01401420040d01c3c0c064840e00c1050030b025003084000400d0807441211046a50070145080c0074410510710001d011900c6180f03410b1481ca0981050004100343c00340350304049803280b21000054000c100160400040034a515004030380346400201840849005840c1c807956590340b414403a035004a40d41216550800c000e032000e06100c00802c41000f515a00740c1c0411285941e643c50070a601c1c140e1244c0881042400010484240c0d48070a9000103100e0020807450312 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 607626456 1250 607625206 607625219
    0x2d131502060f06031e01090b010509101806180507090b210411150a030b1008040201140d1401090b09040b040803041b09020c120f0f03060607050105012303060601090308070507 77
    0x6610911980c4900c1e0b54036001c7c0401d000d03000520a0040c0310a44d80052a03043c02000c0e420b40200a02601c0c1c0000e0070b080c3d05121010b144c3c0c0c8498020481c003001c1c0e91680a01003010740284c9002d4600c00f000450050000c584464007508513111017140c081120680100c480c065580c0c04c1009000380c481042c0c6a0700642103494505420482011913441d040c1e4407184900007a0440700c200c0040c901545400454000c80340d08000d890349c12a409003001441d010341e09145592602c500b00c42001041c2c103048402c42c904d64000285810303101005028086041c041c4103000030990304990203800d002807000402d000c44c0b034183c01550040d001301c480c100c8099080d6845e00c0c00511a902c01103a250f0300140c041c440f803100703000031b0f080400c6c0591041c2c541001061044c1d881d0069580703981d103078607001000c1551036803040d00320b84602d64010020300581d80d50303611007a900d040120861802c0040c0f1800d140c103a140c08910144a01c005071100100300d0709540f9402c540340c008a41c00c950500c281c800103c0d50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 607627706 1250 607626456 607626493
    0x608030a020a1707170319020a020a06062310170f070e0a0305100c05090a2d0b041a07061a011805090a022d131502060f0603 55
    0x440d40d07002004030300c85501d005020b6501d0003a0400c5018818441c040c0083c01000030601d1413815000c0382500ca03214800344d00280c42a90305a00300292000506d10549500480e115040c28000c0100b0030074581c0d6400c4150410301d280e583c1ea8510021183e01c5059071420307000034007584a0510b0004084503110258041c0d000054615032454200e03035081200b810b42c01500241c803c2815601d6407501031a6a4a540d030356003040400c1e14250f0303240e503150564184070348140c40a900c03005042d01d110745e17030b80c540c105900700c510912807040101200c0c00340071084500061a0840740300b0070405140918002140f074034043e07600c11f070560242c0204001400300d01d05004e106021003580c034030702001082c400001741c050102ea4454010850704158100310319951110400e83c4000d03001d00260750348600d06c0190a40c0803c002080035101c1407140c0450981400c10054115044824403400895489a00082840e4010302e040d40040c1d005c0c20000d042102e610440b81d4100310094100c5418900880c40d14030f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 607628956 1250 607627706 607627717
    0x7081203090a060501080106091b2a0b040605060918030a08271b0102010b031b060f0a0503060a240309110d06050603100b011e0e091501121815060803 66
    0xc2d81e0703442304420b2003510554841c02c0034007a900c110b40800100c814002500c9035003400e5521000e0403241d050005030301c0e10401e10943d01c9034091201d0207a8a001c0c41c060b0018442565005d0140b02520000b1b0500d60303203140700b903805415100085003484007186086844038801040940e00c41c0c1075240b44034100300c1c42c0c105a41500502c80181400000c1c0c0c40741c8607844002150980e0442e0705102b000203d81d02d01190008162400c009488041c06004020031158420b1216400b8020000550300d13500903481340140d4040c80d42242c50b00419543d070302006014081c020002d8528101ea600c0f44040345000e68006000e4920940000000d02900d4000444503012040240c0d52542c0396000c00c08a45000e03c1451814001010b08014442d02c81e00001c0800152040250a8103400103007590b01c680580102c491008004102030080e240c0500302210701e21742400082d0100d5044142e01c200c0d0305140c050800d100902c0c50050660701400d403180549842c003a800c0d88901581c2d2500410f4514041c0300400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 607630206 1250 607628956 607628969
    0x20a080f0705060703150603050406092306060d03140304020a0504020a0c02040509030406020309100e19030221101a040f0b03061b0f03071808011d07081203090a060501 74
    0x1c0e1281c1180c24520304040000303210400305460190740c444406075a0740d142c0103543c00d500d0001855903580c40d0100c02010b1402000c0c09107031580c07040c03c005a560003105500602900259500c0b13480e44014080590034009005002c90416282520405000c10140d60b1090004080401003039403800800c040f80e202c1c41c000000158803606d281c0c00c0d803c05000749034110500f2401103107098030300800207451b402100001c2d4415040700c401c0070500d0388030b00034540c900c4a00810600d00d2082440000324581183e2100700e01503117512605078070010317914a00300c21140c00d9402925150002c40c4414000705400d000c10002d8000e0070502a80940302d510854000002c1900c001403400305002c00c062404400400c0003c0c01e52000309901c0038000c00c4019074011a860720501501c81d00c4008050311000d81c0c1c5150610b4070700301c4100000356a01c054204c840c0c500f00f003c244141100ea00100f4648801141c0605103c6501110001400c1c015070310042d03600ca1003441c2500d0500d10740d07a030b805095510a03403003071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 607631456 1250 607630206 607630237
    0x8060d0b09010f060b1e09010c05100902040e010213260f030706060e07050d090602090405090d0e04060305071712030a020c1614040b060d020a03090c060813080a020a08 74
    0xa060140c84c0314400141a0449003030b0308022216680400c040440b0344450003185000c20b00021a902a41102001d2a0b010301070f43d04045984102900404c1c410409030f10403824250303e04111a018800c17203c0710080311508603951800c207943d05114a031421403c0091118101c5840713035000e82807045c881c140c10540c0285079111128107004007a504550801094994810705106010340c100d400c0381d08040c00448040745614017400c25000a000c0e140e40c441e00542880108040c24502194900d945201d0b42ca400230486111418802121907502000300302c2d606c095000d00a02e01d010902c0065901d0300c00855281e40028041d07920650000d4a42403030154010a00e038248203c03d21a0070a45e4411210740316159141803c00c419001c1d1380b020040c020f9a4925004042d501c0b04404c503060340740359190070355480003e410000d00420b01c03204180d03801c075402134001c50707054400c45096029450b171001040c908a8541c684145a0340481d000e8400c0d4403801000000140301e0304041c00c424000800340703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 607632706 1250 607631456 607631471
    0xf10060302031507092d0e040204140c040b0c190311100b090403210c1115070804080307092105060a050403120f0b12030418110a08060d0b0901 63
    0x60620704490f0700541031815502c3c6041043ca41d60261a8100310380c0d28111a020141d003000541c0000d461081802419603c884004038041c1585643c0c54000c0d80700382c8040000c4c3d403032101050007480c3c1c2170301c680310440004c00040051540780c1c8050441c0f40300769000d40d0a028000c088055a07034001b0801180411005588000e007024180300c00903000000700001d2140e44010760000d406820010304c0142031042442100001809103000303102042d03403a50301049103000c0e40c080a0710188a000e0000c081d44100802040c91209039800c0714024a4030b0740300c100d21901c50380e403003402d6608024004420080000d07000140c0c003528460021219840c0140d40040644506016080410081000000c0743c20a81800006540040300881003c081540040c01c03c5010800101404181440036032110071401c4080c6920301c00b000902c2251a003040340740c08000d6414101c400d4580c2401c03040c2604d2418800d03903101500503021658840e00041050b06d00143c07990745c8051081e019265052240e5440e201c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 607633956 1250 607632706 607632709
    0xf100c0302390c1c06021308100b01050f030f04140601030f120f02070306050702030d1a03010c08041a07050405060703170c070507090f0e0f0105190621050f10060302 73
    0x102040001000001d05800a4030402043c0c0400050101400d50095902d504090100710b03810b5910800702042102c21440d42c680a4649d907000380d6403110f80e40c0b840c0c640c1d801003a40c0100d040b0750702140b00002c1d683c11030b0740d01d40902c0030402c0c0041064542d195012840c010aa40c14442503000e1071040707001c1c1c1010304890030001e060711420310050040c032409034908030799260005a05012030354001004207a503590403004a0131b501507401045a41c40c10000d19001c4410710f924080c0d101d03842607008100e075510103402103c000c03c2c155400350004c13486225505070300c2c0b103ca90240d88101d0701d040440c0b40c035646801051803940458005e80024005100324000d818801075126040900101d00c14288015615150703249c00e4244600084507949043c0c08044a040e07070042140c048441090b1126184010041406480111000303c1840c1c0803040300343d140746051095409661141c0e041184803c80741c1c0c0d428803a4070172403009a82e40e22440070b19010301c040820280032003031800400458114036620 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 607635206 1250 607633956 607634047
    0xf03060c140405030c09040203010b030111030f0a0213150903080a110d0e060a0302070f0b01240906051215060c0703060f05060108130804080d0f0e030f100c0302 71
    0xa8888500c410402c0200071565002604a0002e05e04642c501c42c9502d45100181c010000c13076550079015400c0c14084600340002c60055072003800741c005800c84c0385e580c10019074101d105841920190103901001401191450a86805681460b0905000c00760302c0b5200c54440390000c103149000245010504d52007078506004000c5461080e080c004849124403000905a000d039200b507008056011401e0000d10080550b1400c415400c42010021943c4422411178000400741f13849051040500c0300d0b5410920410f200c0044807007540e100c50a0081164124601e44005021000e04007407030200d000c080d50300d1138024103502e030900f0010042180f842c684207047d1400c0000b6200341ca4a01410080340c1c0c3d80040100e507100744980d450641c0d0041300c0c80c01e0409401607030003501c018499018038900c07454100009100400e0951101200c3c10412030401d41d440070700032250f24140c1c11000606004504680001c1680001410058280668028401e080006140d4051030184000398028200150300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 607636456 1250 607635206 607635227
    0x151206121b050105041e03060204060503060a120f0b090309040609061409061305091c0507061a100f02120c0102070309121a04110d030c0213060608010b0705070f03060c 74
    0x20706050165140400280c05805584034030102c1645040f0304c400210b00f07414458000d16480385e011515151241c030f005209400450340c4600600c00c2d404003062800b50800c81c80c004a901110859503a4456962040f0180014004480e103100a0112003000e60300c9004206c0a424240030001c1c00380e1600c001c0185411060482c2d030301601c0d40d00b050040c203440d06103410051b11540c444c04107d80d20f441410a151121031202c52645600d40d441040d0b8450380031006100d15402101c0038007101804072a0400314111608070207520654074214001440c0c011302c1440c805050a00554402003248051080340780d0040110300e00b940d5000500a0405400512031005002e0001321003000c076640d43d44154510400c00f4006401d0140080042c0c2002910011007100400113848580886101e00d006040c1e2031002d94100e10409100310780b00130b0803240d8481c0c88129401340c0d5808a03980d113410224411030f071000d1801c5d500c6004468020802e0b200885d0450004c511920300065a0100101c0090000c000d8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 607637706 1250 607636456 607636493
    0x1209060f04150f081f1511030f0418060b0d0b031603060f1b0c030804060603290c0c0706110304030b07050d0b010318030e121605010e0901030b0115120612 68
    0x264407008020407820241102501d07961742e181240388690403015201c2041c503030846100d1348000144040d2403000440a40100da100c2f00070a5200c00010100d007065070200d00545203c40014408600c41140f030303800420b94404080c0545080e1010117890040e100c82d590405e5500c1a00d5081100d41802070b1700c14410b82000701d5030b03000c816203855017008100340d1500001908200442e40820207215107a03002c03400859110240001052460300c15112220000b103c500c05030503440000b034251040413003110500d07040c100c0608411810700070140c0c2c001e05000000800303407005120100004000b07440305409020113803602d030340b00c0c0d1502210740e0a0f2281d4510300da04060401c003040b44003c5417030040c086c29542c503091468910400102062203401419101d80c401c0c41080c4013004c000722140d1200c41074030401e076201c44100340480c1c00e11411000a2000811640c2508010062803401e11146500140c1310303d132031a002842c050354001035444d80e40003440302402d00007403401041000321504480102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 607638956 1250 607637706 607637731
    0x2120610050306060c010e010203010f060219080f07060b0303031503060114010c110f040906021e04050a0603020c1c0e0901080a0b060402031b0c060114031209060f04150f08 76
    0x92920001d0003404081d240a006000105821902010a400030081202070100854596030348080c0c07070080d803149124102c0903000f100f80001c480710080d00c402c000313a074114034118541100c0b45400308190b8000b58095840d2541c0d412441256075046c0019401014107699800e190003004042604003081070340485d0481040c21002815660006100801d82d50002d40d407100c07614907140440c0410950464103940585003003101c60401040d5800303401d40c042c04454040207510503003242400c910450080c15070140c07401c0b0302044024407c1d001089150003800a50b4080e444081920030000040440040400d43c480b8404110b8284041c040703005140380401011054403648a00542e49405004030b40a1500040001c886061900c4000140c0c0c3e40c11035000e6803009401c2860b030b00e541084c010420301d0303041004411024540016900036440c2031014071440c0840c4401006907c0c0d20000d928050001c050200182c3e0150442808084d19003d450703800da1210740071001411448010300344804000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 607640206 1250 607638956 607638979
    0x7030812010b0c0c06070201270306052a0f04050a03080307021507052a0703060e010b0102010e06010e060f100509011e0c03050906070b01080313050a0612090f0b0901021206 76
    0x104009513890034140280da9980d0b5036003841c001281c0c080743c0c2180750890307411080002c00c2e504200c069050f00304d80c0203090400080d204c8040f04c0c5004032801c45085d041094400f441c0d44107082d044000c6c0000400d0b100a00d103010b50740d0b80814070042060f4010b41f05100d004c400c0042d441c2c0c061000345c075548040c11024401c4e01d4250800f9089014806004400c0000c5040b10084a044c003803407c2b081e480c0244c220b5280603a6464010003403c1c6a16800010303500b84100144154014014525072580340c1e00038250a0382481c0b54500300b144000d001a6114018801c2c8030941d8030380e01320b6090040020f581300d943e9040103800142109030300390102d64000d40c12130070900c0c4090f8800348a0520b16030514060381d84182541c00078043e401020310140c42d6450310b100020340d000b0004003c0c181141840f041d07110281d90713a4100064100c9910600c400324014007120800301c030155001160036071003910130041403005c503191490380200803034040d0110380d070008142000c0201d1001e00c07a070143d07040f90030140341e9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 607641456 1250 607640206 607640227
    0x2060403120b0301091b06030b0f0603070810030f140c0d05030405100c051c18061202090d050f070f050d0816290105120c011e1107030812010b 63
    0x240324909101081e070380c410a0800030394084d04144000c3da04856a12480802d50908540105840c032419000c01c1c508210480700d0300307009100440f40d0800030320160a41e600c1402c180e5800c000204501007500e001d1801000103115621a0100203006159020889859803102c51401412101c014818100840c5080000c0c070300200301d40a640041da00e0583c4010080b1050720010f0103040c000f0024014902c0840310041d20300020100100a980c4202c00e81e03d210250600070701c0e2038040c0d440003595880110300d07640420b4004001d003c202519213000c401c0700d9200d00e807d0500c2036000744841d42110004200103802070609002038035040310700103c0d1033030564449819100700c0c24210780001003100d8210601030480c0500c9241d1131488040c112040c00b40344102003600007401114401e01600385000c079000c00c001280f502d11003045c7c40e1030340805104100d08001c403041d0042030080080d00b05595000c0d0200b8801600114440c03da80f035110000000d40d0700c207401e01600a01c001c15414000400303103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 607642706 1250 607641456 607641467
    0x30a05070311030109020a03050c04061509060c021f0305061e030a0b130b131b0305061302040f0612060c030b01050f0309010b041404020102010e010e0d050c0f240702060403 76
    0x2120380c00b8415188840b0b1140c0400d02500700b00c4000b0350b005c0301c0d03114000244200443c403903840d40300803101003040d43d48403845c00301c00c000002c3d8960001141d421050002d58003640524034210300042c500c1d14420341c500103e003861282d4540080000e5120010320480e4107021800d0401d071a41000740303410f482c0040000c40e0b81c031002030f0806000441d81c1004200c4142d050046400701c250800e20700d80b01807030030b405102203480c806581101e803d403081401c241000400d00011003034a5122000c1d08668442402c070012a1111405c2642d00a0b620300d03d0880400091213403200800404884a0185000b802c126007111080007800e4107050030140d8003040e076a03000041f61840581500d103079490342c80e0011b2045c0149210382c000345d0443d2500307080c402200d850414141c4038034400d0b80240581404c16049501b40c0717000c52240001c66204002c02c8410a010f440030784491030807602202c140100c0300b1189880c0000c19203484032424181d00d1840409080c0e521029440040c90006160b07034105694020704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 607643956 1250 607642706 607642709
    0x15090907081515100c170403110607240b01080a020a090509311446080318070b03013b06041821090e070c030905030a0507 54
    0x60300c101c28400508291859440c604083c00301074503003800c0b0f4003200b101801e030080024042e41c5c041c00e402c2c00340c2014034426044800341c070f81c04181e500f4000c510b0b00511210b03800202007102c003400a4220400303501c40c1c0c65141c2c840003908481c041a0000d4860024284042c050118440280104460726803c1d811450f500120782e01564046003d41c0d41851214041c01b0300ca105600c1412608800f04e000000049100c018500681d661138095800898095450764000302046080703900401c40d01080411089161100b181503d01501c809032110500c0136100d2003020403502c0d4507020003030040090042d804500f5001e0503c00425929042400c3c80840c0d0105100d05503082c84084103142600c5400d4414014003c0c02c00413400403214030b941400c0000c401101c070340380110701d005040c2c450b034000c040d41010300b035402c07050169000c503070b540d00b95030040140002542448030f5100300180481c40758002502c02c0525503903648041c921391170010004005076005a01c0703580044010b07004150040744c01c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 607645206 1250 607643956 607643983
    0x10051302030f040b180708060f060303090d060b010306051801030501110a09052e0804120516260406020a0302010f050105091305071203030e0d050a1403060301141509090708 76
    0xa03840d550b176040001142051072000c001c01d01600000142084002405500900100d2203400140d5030344010f0507070b240205459943d00c000b100310544049401a03101200b840e006143c00b048031500c0b00049401c150b0004003007800e804000f8010000d008081c89203040146000c0b40341c41c50031246010003081102c1c907024091042840202140240c40c44030315802a48e0545088491320800b000c1c0302804940301204d0603103d0b1140300f0013406503903210708111a01001e85240d041440b410503214900402c1c0c010181d000c60380400c1c09201410142540500010001a8000c0c1014106850001c1c250b0312086801349032103080c07000502807665010710541e440030410100320140d030090705056203852a1680041c0c0001c10100004040c181c0c1504540000c00f1100200c2d6454410400200c03880e10450200c3c0c800035040950450140d190b4100454100000400100d0b500800c3c0c400281c075920142e5058401550841004035541088200250310240800180a000c3d103010352013030300d41a5030a07d40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 607646456 1250 607645206 607645223
    0x3010608071b030f120c12022101030503130f031203020a020c040c050c070e07020a080a03060308040b190c1709150a03020301030c0e0402060909150910051302030f04 73
    0x10700c00354400d02ca5116000d401d0404200762400c00e0402905072128508114005a0b04441100080a99000e55000f1103502da03504206070841e680c4c41710007508421f80c410703142c00c8946243c3c0d0001e10700040701c60285000b90050b550f69059003040303a21f0410366503c0090b002000c102c0401c0402c0c0c490100120806160a02580d560710188040b0300f040301c021100d90b405460070b1038654206601c200a001d07100740890440b658942c4904000c2c01c262001c41e00200140e016100c1040002c030048082c00c4180014140030030840c0d10b070340d500a1030f07400641116842030000308110448500101d107028400b002800c0008490a043d16109010100c003030b9240f241100000b18500b80b9164072040300340789404a100c02e911240c1c0c04000a0180d4021301c001d980c0c1101c608030104a22451548070360050341d0040c41c042c90000c1040c248068454014002d424000052400c0111903c6a018a0380301d0f111601301c00f03101c3c43c2080d0030403074400c941040b501c5042c1e10501c1004240c0c18442c059542080d0801d005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 607647706 1250 607646456 607646461
    0x8130f030c110406180c020109050a020607030519020c2e080c0903060a0902031c05043302100507020a08030114030703050a0308070f1121040b132903010608 69
    0x40440000700c2d05904035260402c0014009518600018243c00c4600184100000c42c90201c0c00d98805580291203600840c4940c00140342490051206a10a08015003400c54140800080a80300c2c4585000358010300220041d601c0e100c4c0b6441c40140640c100c05556080032102107012600e103014480900c036400b40419410b82101050b1200b28500404076180c610b414555074015140c0490101d00030300c0b502c5010090240e0f41202c016041e043c580c0c4880c1000c3c9042c5030b011190309120842c085001e0b001b000450902c1003000d03004880150b1b03400810320010b10505d41401c640300180b40c41c003190003014054000540e0081101d04503800038100d8070740c004039000000d0030030000e680020550300c2441c00381e00070141c000003120b21a45298450244442802a090303600803011138054170550008041605448031003404188030105400c0018240380e203e0482c03100c1640300c108002d800002896081040b02e564204c04000c0002180f1618515060f5542c41c0203280410b008034401d10000382d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 607648956 1250 607647706 607647713
    0x11511030a030c0e030f0313050a05090408030a06030623010e010f050d0203010221010906050604030b27031b060a02070f030c1b12021f080a110f040e0708130f030c 72
    0x21044500c0070002c0c01d1b5600070f1803100070103503658041421010031aa00c110002680c4c076080080360101c54010f4034a40295a40d0390318140644e20041c1206038056480c4d1022001c1407452048d03148a07160000b01c00b0f001020700481851042c0305034001944602c40100600030710303010003900c01c12204190b80502c11900c0e1840000d019000c0e480701401d019029903a86000b200c03891603180e040b00c106000c01c015480e2a082803005501c15400050310341442100841d81c619a00e181100a64140903160440d221507100c245085500040341401c06042007035040212403002c0c040c41d50003980544046180801c9582d44031340080c200d00c0007500380007010007801c05019051b08a0006a0035036401c0305501600d4000f066289120350b034007640241082020030704506403180068010305031a4803403101c95075030010440c028215034800038081040601c0900714401b2414041c00103818400a0850719142c1030f4001011104020180000d1101c00742112012a8007402800101c41d018603103e00c4002c141c3c01c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 607650206 1250 607648956 607648967
    0x1061704021c0f0816020a080a0c17031306020f0f01090210031e020c100c0810051005070f0501050f0903360303070312050606040b160317010e011511030a030c 70
    0x801c00340c40704000203600c400d60703461181754469091085407000851901c420003a40e503503d000c24001c1c00b16141110034024605407086a10001001c001100e180061004040c80c150b2800c0e4401300250340000a62542e102d41881404084051b5400800038002c9980004039820300303040041060545d00c50019051101c100d00c0c86003080d070054019940d69064111942e40d524526111820700c91804110685040c841c0010074020100700f4a414502800c080030000d580700d044a054040c440200200d5000030302d141e0391046031902270400081c0e1031a202107032550008000b00704600e103030420004030b20440d411076030842d69a6696420703441d0940d8040e100b8030380c070a03540c8403140d854480422b040c2d04060f400007e040c0e450795820000c2c031440d02c0315400c0c4500c034007a9010b4074014180034010005200a00b080d41c6400e10f00910b0324074900075620f102041c000c4001e03002091180c43c0c842c0180704284000401d8280017070540303046205800100c0710280c0b240100d010880030581c440a2080c2c4852042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 607651456 1250 607650206 607650233
    0x31213020d0c230906040b13090c08070504020703050a0503070306050a0e100605040501140702040f050408040303091d040b040c180b010e03010204060203071e06050c0301061704021c 80
    0x741001c000003076203081805440425201e031074451103181400c0483c1003500d078400d202451015015203c0b58481300100000b800c003070112241c014100f060900844901801140f440300d02848040c010a414902402c0c10680d041c2c0249020354010808000000c0d844405c40308401542e15150791207840d4410210003501c036651205a0241d0b0742640416008401c214850003902080b0b070000c01e45603141c1b004e035054003c6100d1b943c00b040d22000c140030480e88107001000b4180c40104001010541c200c0c2e002c0c200c403020b80e400c0d16424000f190034800c158100481c0000390001ea40c1020284100394a884140500100010701807000200403c04006e0003e500b20083c0c01c840c6040b910040401c1034240080c505101c80900181c1c2d103103003801c3c10b03003010b10071101900c00982c00f8601d018a070303803100e07040401069000901041854980b00115401e4428507019a0700b441c03041ea170b203503d0103800424820705100a52808040368080c040181e88003040c444844100030f80911550502e800c0603107860350310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 607652706 1250 607651456 607651459
    0xf030c01050f031e0429010602100e010e0102040b04030210030b13090303020702041e240b0906040b040e07260f09030d0f0501081915020906090d120908030c03121302 73
    0x10304090104206180c01da044140030501c98401c40d500392103200c0d01b1165000c0c4210b01c0581c203d001111a140c040740c1155020304890400482c0380021000c41a08990090b80082034083c0041004c0c4210320380442401c0c2c000790149828440d0100c16800a003002c0c940c1401a043d00c0c0c0e030760b415a001c01d802901501c4900384c008100300a1000c0412405207258024030140b00464504201e81e0840c0c645680d1400b40041e050354020401418050015403550025804543c02441403000290100410000f0800361003481e020b542c040c1040c41015015101d42e1002500e52109290414030700001400e5907980500584454a000e44944020780c2c114817030180710f40b0b000b07801c241e10894000110780142d4101c4006608552480c00880b103600042507200c8001007150300c240520060341c0c03500342c001d0b2a040c0e10043c00d07946001042c00020f00c8003100070781c00b1201d035124001a40d40094200b880c0e403006040c0c00000c0c502e00b00c01100c10648901c103144216525282c1040460f861050356071070010070341c0c0e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 607653956 1250 607652706 607652761
    0x1903090f05150901050907060c02060c072c010f0803120c0d0e0106140108090d030b0114040612110405030c040f020405030102030117160609063b0f030c01050f03 71
    0x40302d18000c50076407821210400c456080c0400700300d072198001241c00840e49996103200e004d040550030400c2c030b64800f4060403100c2c030540700045680711005180c00840c0104c0300101c0e034015001404542540816071242d07a0401207c1410005e0000210483d00b0b942c0c1031043e02d002d2660b0300302c2c0d052014000c2d0524459041d2400340c00024070401503100f00c3c00c0e500c0c40140303151100c4400c0011200300008036140700b01a0800400c80315400d000b500300441a000c141801c11f4480690514504d047d0170a0b4010310028241e115111540d405c64400c008940245442c100c1c6002d040401080d500c06915040328001c80e035070440403204c44a0f60b4142c60140100034000c0d13650b543d40c4d01481d4181044024035695a005419100710040010700380d420840d981ca8a6040d03006260030002e0782c6040800305401a000c2548001e60101c04003202c4464460100d03941c000c0e01c0e081382509001d405035207025080c0c0a43e000150341101d5a80101c2505c102030012111141d903556444d2241d03910b030303061003580b02d074210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 607655206 1250 607653956 607653973
    0x1c0501091401030638031b011704110306070e0f01081b1605070303030b031e0c010e030c0409061a0a08190807080414011116030201031a1e040608031903090f05 70
    0x14174548003040040800c501701c400308205201003104041040d0f4926000c6040344008052100000410b5903005029200c0300040542e01000309041540c00c0300c400300010039000540c280d030f19240d194503480040030700c4e0803600c41c6001e8500180c00c0440070003001d480305010030550902d16807034207a070801d554002c00381ea40b01076403464060701400b0095401032203401031450140201ca104000b541500607604010304d0316054581c0103490041c034290246815005040712140360f611940504c2841c00d200c1c440000c0e07a81e0928420550740420011104d00c6103010102c2000b20400000e240d4500ca00180d5000c9204680e40c90a64458428100001d00f21900410005142a460000750036200c80a0b03d17501119001c403c81c90f5190726021520004c01300140c079041c00554880d5000c0075514403684c8842500440950015509114440400000c46504008250142011701860004202a40086041003018031060056060000d141000c141d664100c21041c032903041840b1050641000540d10b010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 607656456 1250 607655206 607655291
    0x108090f0a050d08060603040c030632180312061c0c0f0e0106090302090f06150423040b24040e0108060405010e160603090f0203031c05010914010306 66
    0xd5003c0407604001c140110700213441030908104072413090341c0c45824034080740d0550381c1e003400034007201e400d03035881e81551100d00c4c4540b0107803094684454100740d2901400e142c03c910020700320400d4942d00c800c0390410700015240010600a094000d80c04030f40c0740300f00da075500c4500e0a40d03855840c405007a110342c20b0000940c0c11900300c0c0000c16111200d21302e80090b82c8610054130001954403009411180880010340d0b606000344807242c1007a80149018030041e05250250001c0e04030750401c4201c4051401141d400c40700961058071520030507170301400003d600c400000c0400303d44101c40c0c401c802c00511568a04903000c809c581c058203d0b51044002543c540c3d44e42c0d961200f08587c110740e650b180880c49010308000141c00c0d5800075500300c0d850073300ca080200032800f034460a4012110704005003101d100503a0140003410345845040c6941002110070301d014800d0300d506a101b000341c0c5103404041c500403000c860007103054903040701001c141040004103440100303820f00111440301c440950180300c41c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 607657706 1250 607656456 607656463
    0xd020d0c0507050f070b0a0809070f0f0504051014011202121302030d0306030c150215010902032203050a03020315030a0804080d030506031b033d0504020306060108090f0a05 76
    0x20f800344085600701a4844000c2d03076648194000d0b02e55244040c40031410032071040d00e940b039224540c3c5069510700c6585015203101030081d60020040350b032145005000c0c80c1418400c0d10303404511301d0409400303907150000c006081c02180c1e02d06410800d0310035150b80c042c011a0111540321071500e54076070301c5180a45444244042c0803004030300c2070045a0b0b1003040701d4840e0007403505890f080401400790615002c0c224546010080da1942035010700c105410740743d20300f8403056000b0222170134050b07549e141c60a401c0f0142001c0c1c0269904280000c90a0804243c1c013009440d00e4040d10f041c01640d036114043c841000c561001821a41440b901a2003008c0258130400b4000719010001203808080c40c5900c240e0903103104440403a01544039621b0705c0719410f40b00005102554028003a01e80920070014068542c1c1c2102602c1c91000d80004410340080c9001a00f019070b101c0d42d100200010b040c90b0340041e84035034028000c1030400c8024004911100310911100700d1600048085550761041032034040d86 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 607658956 1250 607657706 607657717
    0xb090a0303050705090a140f04241a0d11070f05070311030a05060415140112110a03110d060b030d0809151308030c120703020c1c140d020d0c05 63
    0x10b030815000c03804043c040e00c20f40c0c2142000409401d4494100a5042d04961030000820ba101150034903442c2661520303c204000c0e0038483c1400c8008689405051803402d80307550065285038107071580282e01b4051002960444c104800002c9603101c2c50b49c1d8030003040d0040b11005020900800b001c081004400a620400c580c440d0500b0208215403508043e19161440c001a00d03d030031503000100040c080c00e142005203695a0750001c4c0705940b901002e04150002d0300212021400c030f03c0d41c50188030403000c0161107244221400d03480c2c1070955549245015110401c0390081c500c1d01228030070841e0942041808240180854084a000c00402001d06005580403c0f42d80112401c1c03004890580030380500c500c04010208900f0280c55031842c10544c0000c1c81240114800d00510501c20b0071400742c1c40c01307942142d40140c0c03212804040d0301c2c20041c01e0f44840c013a015402d01c6440005820145505a440c6401d41d555102c95101c2c440501034865010807c8400e4908000290341341d400034054007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 607660206 1250 607658956 607658963
    0x20c01020a092c22030f0207151403070905030d050d060807050a0513270302060708090607120906060b0316030903050708160c170d1409010807020a0b090a 68
    0x80410783e44000c00e12000e4201004061048a050141001d00c8034443c2402c1d0000054a464003001c032401d4001c0c00d010060700c000b100020440301c42c03040b81c2541040440c0203800181550794080e00d2400c005004c0a4100c080c0212450002c800524050b00808480000300009016500740503003840c1c0040007540004203841030245031010100e904200011500d040d100048c0821480604010070403410b0b141d084802051582c84100800d0340c00070000c506070340e41c4284203070804161002d18000e07081200052080c41000014070400070013150000702c094000c0001d0070003203240507100040001510b80d00001070183c030f081c106d001034051031030360055100c0c890b004004450f0410a890840030384200d03180103000100188100d0001c506a240246040f1f801c080d55414407031050b54543c9100b480540c412010401d485c1000131458406104d5542c7d003405c4c500d8806201741c2c0032a01450240121030b0b0541c100030b1500b0020310411b00170415003074003a0b00405010b0342498035030b850b150340e00e0440350100e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 607661456 1250 607660206 607660217
    0x3030510090605281205060612150103230f06070e1507170403020405090115060e0d08250f050c1c0b0703180308041a04030804060f020904020c01020a 66
    0x61080340ca0b2141005446000b084070f06018212501c00400d0301d00124580e207403e03a0f00d40001030f42544004e04002c02c0f03220b41d001d0681c515081d002c1142d000c40c3e5101200c0c9a400608000d000a81004885815642c3c031a08280380c00d50841c07458203c01e6070800c081d81b000d1041e242c0182040d0301c0003038098402c00312035856824800080081c8160103054010b000c6513802d091008100044050b40d4060080301003c49190505903250005019030702c0641d598000c51b55a07000d030105213a035842c0b480b0301810380343c10100d6501000340d0200d040300840c180040e10006011850a140c40c0e10610030156240149126040c4010304e81031501119082d002c04444c20301c55050041610704015020200c21003503005145154007154079038122010b00203200c8410169a04001c1c82c20070001c500d040d12080c0603a40d00301030751400c1d01d40f000d0ba40140c08220072005000b04100030020354000d0449034080d038000008607201d0003690540e07003c2d00901965641c042d001103030081820304154090051600e055441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 607662706 1250 607661456 607661459
    0x120406080103170f0a08130f1b0807050d0b06042d051f1701060503060114040e010209030a120e03030316030b010f142203060506031c020628060303030510 68
    0xb60b4103403003900484c03882150240014400d007402021442c1e8005e21100000400101c00c0e5510805a00200070464940e5420300903004240c0b180d101c0d00010313101c10001000c1c031504100018180b1003110701c0c001e102c44805400629035440365040802ca80c00111185070b500c100d2000c450250903c02ca10b11a5540d10b010b000034011805002c00f40d281c0b403114004030801900b0050520668400c0c0c40348100c86640720000028280c404120380ca0091054102200d80c1028200811003911201903040c1032580c010700210005503070203d0000e50700350b40a40c0d8240080148882500c00030b40030005c81d9814000441081034061104c0c0701e501e652541030b40c0c10031486508a00664078240748528240001e070035540407010741e0840d88024000c001c200c01c8070b44030f1002c1c084030740110b840d09074104646458540091182900341008130001d401c520070350840c8900080c100c02541d17004010300d042046603190788a0405851140b0b80f92040300355060080c420350b0703220b09001d001340505a031128900011040f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 607663956 1250 607662706 607662743
    0x9021c030c08210703201b100b0307090501030203030f0c070e040b0708010608041515090204030f1e08090913140a0302070b0a02060a1113080c010801091b0c0302120406080103 77
    0x6e88550012101c1003010b51448186803d1001c5d04000014814441000601605100100f01d201c80d245a00071b40400d401c4110010b050078442164406124603080500510040e40d0100070340300001030440c1003035156400324141c00e140030110340c0300210600c030403424030041c0311134031140d21300c540400e8407011081e0341da401c421600d123281102d015100b8200b040000744100c40903080f4020411040c06ca2580454076983c0003c1264000e500449031090454000b0b0f08208000e102c0d0030f4416604125617000c1061902c1c1c0782c09510400c2c00030b903c81c084000c0090b540103240d51211100c150412817850500d2078200600da0342d0400c81000750098803039807000082e600d5501c2c040340c50002196000d04526212144694040e005401801c0c5210714144013a140751642c401f0712000400c1c0c5280240103059141e8005040f102060f00500b0815080100040d5916141c1c101244860300c80c0c90082d1061030725040480c04c03c45078040125614000090000300d0950103041181681e0060001303059011203e030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 607665206 1250 607663956 607663961
    0x212090a110f0906010e0f0a2c010f0603020702030a0c0b0304060e120a0e0d020315040b0606160201050702032a0306090c0d140a12050a1209021c030c08210703 70
    0x18002035000f00c0501c00520954855803221500100160400c00600d101d8400100f0000b195004031900c02e01256642c6450b190600d1105210801c1e440c0400495050008820000b003c90142d4003c0c5600014410110340b01001032200c60f5400a0081225589446c1b02001e560710a80e01030b074400d800c14400b03003003140700483c10b00301c01c0c00d0880f00c49241080c0010152a4011007400c1c060b88030802c0c52400002d600c0c24001c062250414107203200142c0b41500d49030101c200c014150364001c0500f80200d40c60790030018480b81c11075409003000c948408252000918241c044088100340100d26410062811543c500130182480704a0a4131003580d501c04c400c940c2c851441000f1030f0310140a10f64200411a5081103440c0c011500054544003613054540848046145143c40001003000030004401d4ae0300142c42e400401c01b84405201c4201c0030340010342403000706002c000c2010b2074034258404241c0901c50100b0000c0d404480301e42c4420800c00f8946d2541004240303600c006c455600050145071003031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 607666456 1250 607665206 607665229
    0x9011211030a09150e010c18050604050112201815030604020702010203040923010e09100f021312030305061801030305070822080d03020418050a0212090a11 69
    0x40c0d003880c155519101560050000742034151507040041c0d050603200c01c590300440c4036020185002081d600e400404c002d141131919a02900081c403694414480d907501c840403502102c10928141500c03800c03030f481640040c601d8002c5440340b85401265904451510006000d040403c10000001c4039000c0051020705000307501003400e560b40c1000058001d02d8581e000d84186401031045a061a0719041014111192480800b05406061086490141c581c4151501400c141040310b01181000174200e5510441c5007101005c030354840100c0d01c120a400c0d4140c0ba0030319501c04250040e907a40c0c11070744c0800c5419540550003c1e0410340003c4c514182a607140c4103400092081c4e440d00d070310f141c80440d00303904852000c80300b0740001c1282107100b000141c40c0d04400c0003402460310300d042c078091003540307080c900ca4059000d00d40140f00070010307544c8100060059076160040801d09a9549101a00038451412044040d41e40c40741440900440002c11114961140042c2803c2c921540100314115914 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 607667706 1250 607666456 607666481
    0xb0102071203050f0f030402040f02090d0320030a050c010c020105091c020a080c1b0114090d0c0e07020615010c0b0c0a0c1415180a0305032802090112 66
    0x40410040000103074031000e121070180c81d1550404044110110780303a03002e10500070b003074030000c018007003507180c03522650038080281001140340c5820a4081070f555528400044c080c030128800d03406000140c40488003040d501103080e2070f60f4807203c101c0500785400c40c103180c0c2c00039071800e0a009020b41c014400c0c540104020b034024500360031100f00103c03880700c0e43d00003c4218040c01032507100080280001c2e10106c00b4074000742624a104950869100d826480d07920b040011004861810f0401103080b0782c1040f40580c0e420318440e666080010507000c1c6a401419403900780d000700030310b25030701155080c002c0c5501d40351310107500d1042004440140212034050000350b07490021600f03100480004050b180028200182c801c0c01d00d44401160f50031014161002d90449103807540710b00344080301154410131180360403550b00301c11138000c2d0f070b1030008c40e10040901000102042140010088030550701440f010800c0d0f500380d170b900091020b034110100442c0419445660300e40c040c85240030385001c0303036030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 607668956 1250 607667706 607667713
    0x20705010e07120b04030908160306151809020301090f1407120201090608180a051f1107020f030307050d031b05030f06060f091504030c1203080a0209120d0206010503100b0102 77
    0x100d0304c030801c080e00d0107442142408248800041c10401c00c0c8420192206815450005246582461000e440b40000408150329428106004001c6c21100032680d010307131303450009070311002031011a00406050002500030f14240081008108800d04001c82c0b1323407414810b65070400c0c2c1d03401d1b800c0c1c801440c0d02d8009011400c0d03c80d0071b04c10f8074400c04807103034842c02c01c202520340709195140705801d150f9410000c1e50320340c00c00c042c051407648500e0010070902101000c10000c0ca040703907140c0340c0d03180101d100013440340301c0c001903020380381d81e0800c141e83e0b1080d008401e45021031000705018000f4003a03152480d0403e0f1030303045403a2445008406480c440d20a0900c0c5c4452541c41d502048074035400600c0500414005011030581e6407a1034143c030100403146441c1940d07503411414054101c0c0280d0740030704d0404510b280410002075020a0080d0040c40c1120003507107072400d560004460780d1030090440d0403449503c0403022445d03170000f420750481d2000d9040d103100c04440e080031010366503401c0c1d100e80580d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 607670206 1250 607668956 607668989
    0x503030f04170711130b0d0501060e070518190e0f01080c040e0604030804170a0503060a05030a050304030f030306052e0221130f0f03120c02013002030a020705010e07 73
    0xd01005a17803504042440c0095821017240008001783d00b48841507a0582d90351606020948c207043d1103a0300404182441c03030615146c0e02c1480444038551f0404c5009440140c200c06a201405034003174040c007030380720400100d4a8040b15540c500d5800b403041148a1190344407005541c20144900c5601200f02130280c151942c2d10f8030242c60191700500102c8000381d005205600d80c0e4102800351020b0310196a90b030b9075078144407041182240d1541c000d03502c0794008200c0403001a00c00000ca0302200d0340031000158081082c00c0640c000c025503840785812a40b030107002c40824109041c070140449801002a0b4a02c010403004c90f074842008a02c101030204d55080d40400350302c0300d805080d20ba0490f85018076505c0d1600441010108680d00070001c0046180041c410000f10046140d600241882d090000728242c0c0c00003810360912001110220941011082008080c03e4680b40558a511808d56482c104149000000d5010850699280d4a40010b00b084580080b8201040710702e03502c800c12118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 607671456 1250 607670206 607670209
    0x303050a0b0607350c071502030a121e0212070306050603010501030b0301020c0d0822031403040201030912052115041e060f0312051219090503030f04170711 69
    0x8510840701c8a0851801a040d104105070051303d8951203094040441c0c4911041200741d103082601d80010038245850103002e88002c0c0c0c000143ca010714903900e043d5290385c0300c0c10501001000c0140300805a2103510f88450031380c0da07583e002888540800c10701414580e5400e0000c504441250040c00d60003135040004006a602c81d4001c108441d10080005190082e0411000e10b8010614868000b04c1c0900381088620002c2041c50301ca844804808002410b406550080c1691000c0e003242e2a100000f0002c5015640700c0c0d449020015442440a80304440e0680d0203001074000c0d9a00030303100c002c1c400400e1144030b0743c1e107445d60042140d0141d5120213203042d4100400b602c5101c3c1e4000d0042040e480844044c99032340a81c0c00205940c400001c5071030700798101092007417490300251080c0103042060469500300e00503019400143ca4007901c504883d181c3c814000b802c403e010140c0603101c08010f011303000720303041111400380348500b04094420141c0b12003140b080c014020064040c181244501209 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 607672706 1250 607671456 607671473
    0x115020616030c0e1e0901050d05031e040e0420030a0309050609040b060406210b0d0209040201090b040609080106090c0801030809180405031b01061a1c020a0c0303050a0b0607 77
    0x8010f014108042c001040e14040b070360080004030342c0000c480c0445441c40590501c641481d02500c010b45040e8410322075510f03065900d1180e016011482400b084c2047c0c64405900182c40240a28070079600301800d0904061068260303e0541003181c500303c0b100301155180014016480300e030305403144c4040c18a00010400c41c0d40101c0795140d007041e00c58004011607503a002c0200041d1445480b10501c24101d242d0102820f01d034404241d0642f0b1400c4104080c503a0303000604142154125101c440c43c1d40c4500c0100c900d00510b2303012030924003000c40c010849942007c60217064425220081001c2a5194910f03001d40b03491307080349000700c7c0400c001440401c810000500800e540589075051054100d02d800e0613555017110260345940000c41c8031440c0240f0603411341c810100041c020300100d030800310441040010801c61306903030f00001400302c0c409541d00c01240394548220008640b26020640050910b51092074101c0002c3c0c03038580040e032114850310450364055005040903060150303599070000c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 607673956 1250 607672706 607672721
    0x12021c02160e0c09031c0801090504020d0609030c0b130b0901090c0b070602040e07031a090907050f04090212061801060e0402040207050a0501050403110d05091c1b080105011502061603 81
    0x3c801c200f0401d603070180e00c3c100710a106400315a8900b042414007410020301312a0b040e048200020308040901c0050b81d0380311603001182d604135100240410103850150f0301c603510040001c000725111700802400c407902031070f410130050260f1110181c9581e42c00780ba0f401c8942881000b002c14030034400030311920009602628420384075990061409031030709050b4079a80021904600000c0e220b110300c644181c07521300c005107501d60a5076490343c1410142c007500d489040700d000e05d80c010b5001081c2a4030325603854101401d030300e401500d50051444948001c03030312000e007240c0840c014140b9900340d102e8510b05100717040880c0d0502c0d910643d1030f243ca40c00c000203984a080700b038400b407241c841018003041086c03040a008605c69107800001e0204403224034146000f280000c41404424082050301d83c481c0381c0704107000b050340c0c604051054070915200004907000f071207460344c1c202d100c000801c0390081580064141c8030040f12034801d040c15803c0c2280d80d484110303021109410b01528818202c0d00a0f005290b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 607675206 1250 607673956 607673971
    0x3150f1514030717010c0e030c010e01080601200c091e071b050607030605100f05030a0203041a2d09031b0c030d0210150509010e070c12021c02160e 65
    0x9003820740c0c40c07051010280320b110154440d1795440c4240025145c1007139101c41d4942082d0090400303d00d90400180149a034641014144141140000c2030707a8444e0000e460170211400c4000f0340303090004220f070b6860420400750380c010600c02011a080d1002d03ca0400032480c01244882c60540c0c42d00f00440d540c1c07001c51080100d008220a5403400610180945032042c0350300d9600007202442c3c8410014887c10094070101030001040740500680c0c1d11408880d400422170700007599a40304c600d4001e061020320341c2c042d07500303544260520a0080406100e280036008203501c0e240c1049400200381e421706015628003c05600c02c0022298541d062640201d44800c44020707501c4010520f00401d0524496a81e40307070042e00600301130f0f80c50a00301e200ea80464400820610200e60811001c00c18004041c012841040f10250001d84c00700e1040f0401000c459000f00900c80301d90010401070340c1d40780c4921032280c01c80840c0da4003094140c03000502e03801084150000754003061401c0074403004808060a00c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 607676456 1250 607675206 607675213
    0xa0b04020f03040b0402030c041109120c06070c0609081b0f040b361b18060a0302030f0a05190b12030f0408070605031009020a0c02090103150f151403 66
    0x780340e80c0d01420090752140d8061070050b00140f609204060420304e00c1c0f203c8170710544c40e0500740c0c0c041d10502c00945003d000251180f0aa2141c4585050f00e0043c1824030903600100c0040c1030707801c21100c8400d4800707e5149441d02c6181c0c030380b2601c0458070384a4101c170551400480b01c2d2402051324004400c081946000b0303000017030001410000c1804848000b00b413400340c54956505410380100c03000f68580304500240d8006242c101170300040c9000010038200c03041300c0d4003c94500c1448203179180b00d942003e402004d10341c1d40d42c131086000c1c0181d04200c1d1060105a28400003800340007460203a61301c6510440c450300305030a800c00e514030080c101e107000c17590000080548010440d1040000b40f00c44040f404240b80c49a141452070ba1030110141c0205040242c10302c20320041c1000d038404407068400a49002d41c98501d5030a045610400e02e02001c1d5020344054000030a01003560b07140c0d08840360b504c00510000c5190b0310703240152218400342101c2a80c01203410084034a1020070b07079a170703400014142c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 607677706 1250 607676456 607676467
    0x60f02030319150b0c0c0604081903180806061e0d1b0f091b020f07090f0e060703090c0b18150405060708090f1203071101030b04110c010b06120a0b0402 67
    0x103e0302d00b000e640c001904034100040e5000212800b0401140c2c50b2104444d02c03480c0c04c1c181361400382c80f15404900301c3c1711400114100010940191414100c0004841e0810050355450640ca541c078542a0345070f50003a45a100d504605550003000e06003114800742040640160380d43d981028902812003424465541b40804074a07031420b44450320052103184404144130480f0300007000d80004043c608025548102e088661105011500e8021103012000004900d1502c542200180c0203541c5400c40d1801070108000b007039601940000041d42c05880c140342c4854440700718030094032401c00d0301021418200744030013041c64a032440a1440a104840ba41016607860200f1400d4208140c1242c89600c00f08007040507041c20826440d4900046501d1076149a01040d641c1d00e0f4400d5800140079100e40d00000310780759000380c00090500b0400741007005030382001405c0304c3c8190441561a80d0550811850700240c3c5400c0090b5031519102805140041e02c2d040c01801c010a0300540c0550841d40a126 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 607678956 1250 607677706 607677731
    0x50f0d0b18070513020306040b030a0b071d0d030503070f02010204140f0a0905240109060c0308150306070302070611090f0108130206130612090c05220e010b0109060f02030319 77
    0x22501c000c0d048078101581b03909158003084241c03031280c0b2119000ba403200300510041500307048aaa0003500e03500300211507402c2c1060382e0701c40103902110290090f800044280070103900c03000031031242100d0b0362038115410012004900343d206600c80c0000200711640001c90518040221640c000c1008101040e29a0b80360482000c0c2c3ea41192145440340c52a5005000b050000c422102000710900e403120714242041d001420007400c10b403010f8200024800080c00040490510500701c2c44010121500c6290060340200079602110085881d581400804807100102d2400d40740550f6004046055100343c003401100d501c4001061500300000e071180c45409030702c0d0440200162400d0300b0607201c18604054015021482080036800b18900c2c0c41007820200314110f140f0410b60300c04841d440c0d0304046c81804800550486200015003c1c50000044001481584892000c41d400e0300c803142d0056803103400340c800103040000b00b40941c108000051034001480c800d603080d801c501d500010f003c603000c032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 607680206 1250 607678956 607678969
    0x1170307060f200c0601030f060b090a0f0e0a021309031e0f14131a0903060f010501030c1106012112111204051f0e0d0606050f0d0b180705 61
    0x102d42c05045030350780f00c01d400a9003041c907080002401c000d5149250903440d900107035440310140b2005e4481c0010038110020014a6000310b0108100141500c4183c00c0003100c00b80105100b224000030700c1d1500406001c3c08801091024985400030040184003020320001000740802c1c00c001c80030001d4001d48051502c00c883c1d800020003003a40c1d1591148849084c0207404098002501c4580640a105501c03448000b84070100c01d481d100744041c020000c0800340340381c040c06842d00680d45801064100046000790b0302910341256001d03a01400040442d4205540e0b29403120790160864101a0060060700d0030b005082e81c0f03e010248480c20a00c0d29a1100400c0440381244070f8000b408282c68282c04110030060303031900301c82240c0443d140030300d4040020103104c1c490b100d2104044078003c0c09415a070048130301c8038080401a265940e118601d10340b000c0140307281c3c0a10707482565080541403490403c442880d05442e8010001d01c101d46425035605d0351340e4044103610409201703000000c100c82c2c8138403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 607681456 1250 607680206 607680221
    0x516020319051f020414040f0b04020724022110051005070c08060601050702010e03100e060a0c021209042d0228050712030f05100905100e0117030706 66
    0xc1000e40b6038990101006914252001d6074403c000b40148030500035045110b40c100c200000884000a0f01041200c0040c00b41031241d498603805071010030311506003e003100341101d040350000013810b04091035100c00022401f41e40d010f104404a0001070507021428065559003011007110ba8846860346d0360000f6448109052000001600c042000b40810103a411980040c00c402406003c081c07400c540000d14600400801a042240914643c641900e05216a0340c046126010074000c9903421205166207580070350ba4808007a24111490810390b2010440382a50b154189040d17280040d840b08000240442c2059407903442070030140341e00706051201800c82d15004040c000b40c1c607110984104500c4581c0e50250b400b006849050407403555501804803040c4a511000609250180100850041121014031100c861414040c89400d0304113151034403c80d00152010310807076803480d04042c503d120034400c6100341001e400c0188141c007003071441d01c10102032020841b0708020550700d4020545008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 607682706 1250 607681456 607681463
    0x1d0a09020a0e0301091e140a050705090708130b0c090907030f060501020a0210141b030301050901170604060c0329180c16080d1b0908010c0516020319 66
    0x10344280c1040e004007a02d074100300d00b103000f00b103010410b40300e0004101040f0038501c10008403024071410001911400e0b210f2003103110480314070340b8941c60a5030b42d442c2d16000e0030b44201c0440c40014407981c402c00c0400d00c10b0154103843c107801460755403a4107104801401c040c0b41c4260503c118445601c60043c0c0e40c1c4110103541d4003094601d0b001520380100c80460300204d04641044405801680310300405c0c5c4900c3d9860300e000000c0e011580094196400380c041d01c2c00004c0103c428914246030000050360680d441111020f015036682d4449a056401d417014001c0d20350440340014011503902c1c0e0240124202c0c0703080c04501c60388048855405c40000c8100d5421681a402c90b01415091000e2503003200e943c074082c01c4100b42820080b03540d0f180541c0c0074941010080c405200d08000110082e500310b0709035420280800d903100c0300d450400c15021445080010114000028103103014000e00300410001e4580904e00088140746000c004080e200591700351144c400e204c940f10b43c200310b224404500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 607683956 1250 607682706 607682711
    0x30307030f060f05060f0a0905060304050123010612150b1c0c0822020117072304180207020f06070807050d231b010f090201030b0d121d0a09 62
    0x90310706180c0482d001c2e500628020240284284110388407001290a01003501c1c290039201c0303490325012512800c05400c07d0b50040b10100a11003000320541200074103490303584415038500101294032030319071001d00c10b1b00300160707402c140b003009800749a0025029464094489003030319207c000508580d803000c40752880301c8000c0008400c042041c0e02c1a00c1c5405014502603009092004502d040d075440300305860000ca205680100441e80140b00020400040e4401c0389414540b0001c00740148005940c8425501c00d943d901140007020036017110107445110001e0660341480905040003504009000c98000c040100065420f6581e0b901130a403481c82681c1aa550f02400d2500c2230611166591000501c140c0c44404002c1c00048001c1c4d07060008002205a01c3d4040700a24908110000442c02c295506e40060f01004080c143c00180f9140c0c000c2e20288010014081409403800112401a103011102c64070f07050002d100345010402c080c80c2c501c0c2411403445600003d60061090703800a2036103036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 607685206 1250 607683956 607683971
    0xc090924060503072702070f02060a020a02150a030e0604080f180315010305070e0c0d09050c09071d011d01030903180803070201030608010506010e060f07061b02070b0c210c03030703 80
    0x104120060081c174a040e8800c2d41890010341d141c1058024040b4000d00c600d0000c01c84103581e0340308010a4020603001030007415141c800e030003c42c1d110342c408208080000d0600c0d51801c49294000748040c000c650054150386032000f08100c4a42a401c0042c05c0c50a503500101c2172002c0307603000c000e03001541421180e00181945180f404a01d07240c10745e4029909100e04c20100700b602c0344044141e0b080c034581c8070310200d109441032800e60300789050311a04a5204011900b80020715501ca001c210010f103c0c842042402100c035001510002c07212150546806e41640362100b50354400e410201d009842810540d800c2c040f400c0800a409455401c10706032075101140150956030301d80280c00080c405a0000c00190174460300082405552106441c02076400180e00130700c4d054031780304540b0200c2c0c11590800c180e141c40e0300e951501d000c0681802e401131003a800046402c091410488000c0c0d51040c0041800c0c0c0384540c100486440314401c0f03036406041c01d02c000d02c981d580a200440c8188102d517800103c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 607686456 1250 607685206 607685249
    0xe011410080606030610060e011b0510060503010e1c0e030a050c04050a020405090a0b1f03020309280311013317070501050d0207021c0c09092406050307 67
    0x1080145907920a51004040c000906c100c00786420558400d440c3c601c5c080c000100040e680e4000801ca0a407418945d20409410b000020801c010340394400390042c40196036030f01c1014240d4080f07903030030300d11504484d201c11440c02c0040c10940f440e41141c02c10950800c800000242071a108075000d541c29048421000c80310315040c0328240d440140ca000844c289418800801c42c2034400030042d14155075140c2c2d0044590b520440d50740e00100711900100440340b0700d007100074043c0d04199160f0030b9511506d409502081044c032043d0405860b01e03012403500303200980742124014403450b00c552455680d10360740001c890b0440e2110550700c1252410602d11419914031228501455000e43d4640c175814021507207103000400c0c40c0f0308840091a01035210101d07280c60000078071540800961001d0700000b41c02c0065500c00000300c2c0c0074020041d0490055859014000390b07405032000510080d000b19a045c8103440841a880d150f0708000000a411501c600201e440d003403064002074001c41285c419101035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 607687706 1250 607686456 607686463
    0xe190e10020a11160f1503060503190b0f06090c0a1701060c05060f070912020a0803040f0303080a020f0306090a0b090106082e03030302070510050109140601050703020d030e01141008 80
    0x285803401440c122451704420030034510503801a0070708110740c101000c1441d44030f0b42103000a410b008080d1400d02a43d03060102c1d914946a40854140706a8000100300b5925901c030644240c001804400c101e940d2104515001e500400c1c10701d0074800003540030040c142c49400d0303182c00380050b0707290380401480500b07006151010003855902c031100f008040007107050b0301200d00d80072940110500149041d1a200003221030100b0f400c01c01303882c400070500003441c841c03921904044a000e901c6480160716501c12a40c1a03104200721020300c2001080860ba803414007000d0142d10002c00b500c0041e46690220003ea503a00c0c007a40201c002031140014441c1d0020074800e000c01c491280c94440031682c01414060609500c0ca200c040c1c2403550200d4620180081440f90741c9400005120420607036860f50328800c0180912840b0305120203c0358000307a99075020328212059160190010403002043c29801c0b80a4810a5807260080d500d518584072040d010582990088044031004010726080c03008207403a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 607688956 1250 607687706 607687723
    0xf14270603040f060b1c0803011502031204080913020a0e1003140606161a0712020301081e030f1809060d031403070315030f0209010e190e10020a11 65
    0x1060004000740000610112074903c0d0343d0f40c0c4441c012410101c0c00d400604800940400c0d051317059184683c00081200190003141a00e072040039a030034800726a14100e95a00400074000400c1d850071011402048501c409000122401032080000c0303110851504241d0b0809071a10000c17902c81108151185402d8242c814040e546180803c9540d00d4001e1100010780d0190500f4012040080d648140900310880c0c1044550003c2a00c0d2189040000840c0130410440c1d542c80007031180038049001c0c2505008485c100d03086040140600300c4650014154004c030b024996070319110800a84451000b000060810744881d0803034400141c09038001c0c003007000c800411852051840d100200c1c00243c1028248668040207100541c690f80d03850307004e070300600900d6051071b250345005070700104100c1c401c10a1208540300b0348012001c2c0c6d0380d91240104880c5c05039400f1004000e41440d01801c5880c0d0382c028120b919001080710000e80c4040c64402c101d81c016a00840000e0031001484a180020451080c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 607690206 1250 607688956 607688959
    0x40201080619030f1e050601030b0a150506131e050108100305120703051e22080615030a0206031f1202011d031c0f020c03010504020609010f1427 64
    0x1004048561202c90505a400000c00202d07860790346605100c85500b074400840c420712090b03e008101c0f42002c07580d85100740310464283c405080020003011840c096038042142115022030618201400c100d11500030003994015020031040000d821000c0d0341018403001c07075136566a03a4642c241000140301610051010105c1501504100001100090400619076100b0351554540c01c01c0c2c602110340c0d206628808100c060710700d00d4007100d85a40b178002c0c0042c202a0a0301042d0030b40c4885a0b120442071031180346041d800900000f62442070041001c500540c006080e15041d10740b0b680041e0a035002030390703842d1804401000001c045180c40c4200030203007280c140100c02c40f00b00c5600080c070140040d61000c11241c0c12101b50051030f20300b0804115142d561151258000c00048001000c4411000301e00c0c0041c45600013041c1e032818184a1280600c1c3c028007428900f00f1100c0041d5040e40007100014200044650000c012251240203405280061a120748082c45403880300c3c2c80104a814616 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 607691456 1250 607690206 607690219
    0x20d11130f0b010309020a0306090309030c150807020a02011e051b010203070318081c18060b1f121a060a0e130c050d0e01020d020708070212060103020d0311120a080402010806 77
    0x1001580d1f0b0b100058084075802807000c00c20440c42e160841d10103501c1c0d0300040c002d80c44103002041507003120740240502c040b10358501e40940d581e10703c101d030707a00b00600c4041d0100e45507074003420b402d031b40300e0003121000b08403030500300d1800500715903680da011404000c03001c7e2654007109100449030f01d8010001c861048104100700d40b81c05880c2d9402d80c0c0300307501c00800342c12903400c82500002c02c41e4100004503080706001039658085400d00401030300e400c1d8102803144150f0346283c0003c030300f0130464280b031074441c0e0381e0400308200c111080802071130784011607800c2034150100a01250b480358000d140902c0c0b20307620410009031300c0c01400780c0c4103a0400d031601d005041c00410840e00e03520074241d903131241580c4000b280c1811600c1d40e1500921518918080184c0001118010302000f40000c0007901d10961b0a407650701a41942192100d00c00c2c00000d50041408040e2008a031252849000d203900301e02c01d81c0d03078079038800107281000d03402404030f6804143c09c0d10800055603040916594010425500d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 607692706 1250 607691456 607691471
    0xd15060f0207092003150a0b25020303070b0702030a02100506060f07020406150320030906061011070303080a0b040b06040915030606080c21030304020d11130f0b0103 73
    0x3a40362046400307111191a0368241000030900c41100802e00a070880044691701d013000074021440160810480340034086950000540c61000022a4506080d20301241801e0150068607680012101c0d01a6071500c001c0c1310403c0805c4e2115446401820b143d00256134448800c08060705145216014070451b41c580f80401940341c480704102c0d00030f2181d2008881c0d660045d40f0004008040c2d80c6c0220f81d00801c20b100204009d0f0301580000803034000351031480c1742840300c0d03160401e00c0e12044076006031503080f03100460380e80e0404101c220b0b071290503030910040c80d0300d600d000d42c0d150249036401900090f408900f8400c8100300d600c529041900c0548007404821b2868012603428072480c402d0103070407a907810b6100390040000300b100010310360048013440481e90b10080e156440c00050012440780c0c0a80c031101031030f00c00220b02c0380b070b003045030354055420b55239207400300072083c0040c01b03054400074540180c00710709551b01c000c0f4442c031007205000020000b0040921078215808070340b08505043c500490f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 607693956 1250 607692706 607692737
    0x120b0903090a030b09010e0f0607090e01030f020d05120c0109020126160201020405030307140706020303040c0b0a0c150603110a0317180a08010203010306050c040311120f030d1506 79
    0x1506403c0e0394000c446103007151144010a8010800c0d8070044030340340034040400d12050004144d940c0105d609a03120040151103454002406000384401001507006200240050074000d8003001c80714024800e81d1035000e1240c08888940e0f0010071080201d0b55248031490456070000c0055100c4c00c038050604502c0c03514035444080b41200a841c0c2c241c0c2070140b00034613402034404d404076405098041c0540b500c8104070f02c0d100a0111119401a860340902c1c0400b00341944004152031103a608900581200e0b464403c14805650040c0101e03010030041081e10000300e4021301180740c66076402400000c03c40c0c03440c201208800800d0648602c21144e036032040011409141c7d0718021000c8200c081540e440c00950b46103800c4440011103031308100c02c42d80c00588008194040c50489004601c240001d58809032032404601c03440c0402044000c0c0641000c0d842d0600e84048001001c13414200e408050350540d94500d181c0082444088064540a150601000c60450180180010300784112201282c24 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 607695206 1250 607693956 607693969
    0x2030606090405011514090c1219140106050c0c040216150e060403020d0206010506030c0f032809060605060a09030b13240e3f0301120b090309 63
    0x100090300c40c00c410380204040c44400c2d4800c0080d41100c4503810b905d590380309030100c00950341c4c2c40c2e40c511451b40320300001c0305140003504942040f1440c0b40c551401d43c0d82c0340d0b104031340c1c04100104489004c1e5160195664401d40600c2e0b503000e04000e4803405e031030300c41c10108907181c00310000703840d4013603030060101c4da1b06086507009244e0318035800f20900c1c01e00b85660003802c3c01006240d404c200310744108000d0100b80b5401044a0781c4280e0181d0035143c00342c0c1c951041c06214442030701c001042c0c1c14200903c281d4540381ea809560007120311940d20340c3c600107410b001c40501c100b150020580c0742d9070b01c0d460400c0104510400c401414251000ca00b804580b4001518401a03840041d024003161030004079a0780c0029012100c240d400b07101a06002401d050050700301041580310f90041d450419942410b1030001403070300321143c0c80201000105000d2a240d40003506000c0fa0044000320031180d0b183c158041c60185000c0d000380112142c0d2800d060074010003410010709685096001009100d5440d103d01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 607696456 1250 607695206 607695211
    0x50c1b03030d0b030a0501051303020d020c010203090d03031503030201020c160f0e04020303040902030a0209010311070f08160f11010e1c0f020f06030702010912021b04050c0702030303040b07090e04020306 90
    0x80c0000601c6a450202007820300161080003006c0d5407a080803c505854108041c84800e17009a0031900d0a2040b440181d030b40c0c01c0c07001c4809026910a00c056102e0307181c01b03501e51320101c0c42490085804080000613104402540d00b088002d0303500800d5800036901c08000e840e070f40310b2110b04400b00703031480c08040c42c523502c440e030140c410707550342d11030000b4159202001154014469100d0441d602e1a0502c4209c0c02500580d182c140003038140341780324001d00c1ea400305031a2001d80000d00c0d0710850b07401c2d41d600d01a661140b241c0d07104100300c900b02d11b004039820481c02c0304583d005011140c6907411810004202c25407030920544036039602001400d00d04245105110b0103640700700302c1c144a902d58000aa140302c0b0241e0305660103003000041290080e410340000403141e224021501c5032a2400e07006903111b00a401100be108020341d0310070703c500d10305130300700c1c54000040350000c1d8a802801c0d00841c0c1141d108803001e40e1000440380c24400d07080e502102c908000d00070618004500d00b072075070000c1d80ba42d201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 607697706 1250 607696456 607696477
    0x5012307060b03151f0e0903191b0c0305010605030d021c0302072003060a110a1409100512160c061515020c01020c180103030528050c1b0303 62
    0x540b51070710116102040002c6840c2400350038012a8945680b07800d03500c0081d030000c01400710720f0240008203032100604a9000b140810040e50420480384409410140d06001010812852581030803000c2c440c003e414110501072112422400d00b142003a5007074800b2035211501035442203040c420902d0b4042040307264080f414124040e03107907403508100d000c0e001e40c1381c001e8a40001c0d0701d2191102203940b05008010b01041c0d0658481c0d0395414007110881d400d01301031409105041004140c103911442244c4c0c40034001000032810031043d01d002c101d00e0301c10f060401010130800110604090341403070b504d60380f18450401700b0300d20402c0010020800c148a200c018030464681c0040c1c0304001c059004103000e0b1040703d44030900a10303038440c020740d6000d000c1e01160160260032039000b60340c03c118038220910f5803a035a41e001d00341d10b142d804030344a074014860710311020f02408960b45514002c01411401021030350f10380340c0f551829402a4100315002280c51010103c000313441c282a2804003d1b80d004140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 607698956 1250 607697706 607697711
    0x1030b0f090705030a150b07060b15090609010c0516051c0309030602160203011e1a060702121504051f050f1f03240b03062202180f010501230706 64
    0xf202c1622901030180134078420450807961b4400f10b60746024030f02602c1441d0140c2400c0c444100c45409125000c101c0c1c500481c1c01000400240c1c60500b0008020181c1c80e03418375014491200c41e4036040c0c2810001003010a605205450030091032801d4010990228060b070b0742000d418a0035074000d40000004c0c84001d06260700400c003c18803a015109010784150080c00911082c0c0e040118200010046902c010f001032070a240d6412450100340e0010201102030509841c011254080110752422481c80360700c28420b24031901108144000814003541c4a00000c0c04403982e50300111000441c0f802c028400149400c1c100b0100d5500190482d8001100503410801d062031060701c1000000e00380c2020f03015400109042801c400c1c1803080c1130f8145001ca904110340800c80041548038901a00d05030000e40542040315013014804007010f482910043c0032404000c3c070390410608107142210b183c4542c00002c0010000b41d60041c0e55100001c2140c001010642d80c440404c3c10280243c00c8003501d041d6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 607700206 1250 607698956 607698961
    0xc0102190f060617070816030f110303220608061008070f090f0e01180b0105030a020a05090a060206070f1b1112070b07060c1b020409020d02091501030b0f09070503 72
    0x1d5400f80740905400010341014001c40310070241d03a20550701c03560003103101e11491700300c060041c102c803202500c1d8001851400340540d034403510a0024000a0079505000c1048091100000340c0380c8151450041504d05d100b091403e06c020300501c00007000b082c020130102c10000303220f960007070b40c1540c0a986e1b400c01000d030300160003080329401c110350845081100406001710301c510302400014101c0b015a504504d0010701c1c0004441030b201d5021420f40420001d1010a03d134a1803030700500807075107042c50054240701202d00092100d80b00c41e4814400740e048078090080c030980c0006c0c102140407042c1455001c025450b601d12010341030450020701130716a0320700408546e03a20580c4910111b4210406c6611950701d44400c14603991141d101204c0440c07038122030012550241d041040e0071860b0180140100c24241c0900c0301030a4000b00482c0e10800c0b0b11b102c00b0050f034a05005a006403a0b0302c141035090008080050107d8242c0c00110348904420088070342c240c1e0703456403039070ba0084591402d5900c2c3e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 607701456 1250 607700206 607700213
    0xb04180b060a020703020a1a0a1101021903050105030613170702041e1d150109320613020f03060415090e060f0703020a1409060705070e06030c0102190f 67
    0x144000d4068550220000903102d030070550004020b8203980c000c032001d21010ba541d481c0030144c000055280080148240b01016030030b401401009400404c0c1c40015143c081280e019800c00d0006003820008281c0e00c00c01805182001c200c45a81300d402c58460074042c1a840d1102d0a4146500c42042c0f84440b00080040031504c42da0411200c1041c048008110f0225490b484c1c1e02500841d94501c000100f850940310303803a10000f9000d201c1d8104100014826400d001441c40a00100b211b9250a074151300328410300c1e9a0011083d00200703c42510300612410030500700001c08404019100e4076034014000e1481221076803045940000c41141d00007000001c0704001101103c499001e202200d150440f140c1000201144891182e42506c09400081c2d40c0e401c000d030201e0080e80715600020700c00310031803185040300d0001881c00050042a050070324515035141ca140c403440d5000454004902c000380300030745c02e00300403015000209001a048007203c00390401d0504522050182c200d170752524040f42071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 607702706 1250 607701456 607701461
    0x12050703060b0d020406020f0a0c0501140408031c0609020403030203030f060d0c0b040302090a02180d141204090c030207150525030c08010920130f08160e010b0418 72
    0x1000d00701840d03501c903042003e401e802504030340300b220054041d03069004c92000e00440e40c1404103501202d01034456040c00011100d0b044000e40c6404101c1c2c0070072010580070300c20009402d00e0b860f0102000c25840100f40010240d5485900c1110b03094014042840001d80100981341e005d01c0034040810142e4841d00003401815210380041c214441203c00410a00c0c100c40040050301e00a4510301555182c075040b40c0c08910a143c6140450315050358440190700c0d0019040c85014050341c030f007020102c1300c072461504061b010401c0c81c514800c005401c000d08501d45c06585a0b00101e07090450800395181c446412444060440f035043e2030784c0d0710000e00611440c00601c821450003000c8141c603070070f42c0c0da4054014200c4080f180d0100b00380300c000048003e0140211545100041000e0060203a07801c40f5210903004018140d0714036071806000f00700034490380c40e980002c5c001c0c0b10003030407041d548050900045246800803003041401d600140321040000c0c0440301110f400010104580603448810f000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 607703956 1250 607702706 607702709
    0x90f0f0b0c0c0a0b031608131121010b030f120f0f0f181c200609100203070209070503090d110c0405010b0c011107051b0a1a07030801151205070306 65
    0xc0c0070b840c012021404901c2000518411006c0081c106070718407554409440e0b81908454102517030b004800c02c100040c1c400c3c00828080c00010380300c182c0030001c246400000540d800d5441c01c561b0340d42c0d003840e01c1901c0c00300482060480800081e191502400140b07440d0342c4641e10000b151040b0000d04030001200d0b500c102c4212400c0b000d4a41c0e2503030b08500c0000c040c00102c25505110751010101415482400e20011408a620613650700c100412070340a010340f46502c034003860380901e05011484040e214400d42002c01c0340164007965031500240f041000d41840034000303800708a424400c00c14064030000300140000d0b2681001c401140400e05018940380c1540700b03541d0042d041c6000040c90707940e0350000d440c1f40c94140c002807160401120b8404454011031401030030507807058040c15011841d61304441d81d02d140203850a07080d15150075400e104602d07080c00c0309030148030016010052517440b01c6114007500740000241414040408024014160300403003400980e60340700411003150103940b05c3d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 607705206 1250 607703956 607703959
    0x733110a0f020f010609060e070e0a060e1206010e010323071e081b030d1b020609180c090103140610030e1606020a021306050a030807080409020c010c090f0f0b0c0c 72
    0x17124586480000000c1c104038454080780940440c00308001d903009905694a000c0041c0250120702d2038500119280103c084d031540d003021a00200303500200c810b10a6502900100800800551652409446550007031009100c45410b140c1c100d4410342c1d0110b5400201d8074541690a250306008000042c8001c0591007242188100134100c2d00d0302c01034003070700c4070b422070100c058403000250302c0300c04d6540054441e40040c00d40e258045000061800c0005072a10036806415189503202180d80e517181427005540400318024082144405503030b0600810b00030102000d20b42c034603801e02101044241c445c1f560000241a240c0e00b48021501040124421060801038120481503407004060344945004a0036801101d102080307080302401070242204440011707244c00038a40c51a1140c1ca12900042d82c2242e09000400c400a240400780c00600011240d050000440c2908004090301e0640980c2c401a610400c0e50000c00020003042c0408080740d0440d440580da0354001c0b4065814443d0741a02c4a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 607706456 1250 607705206 607705211
    0x912090f0a031214210a0905030304240b0609010f020a0c0f0e0907050d02010f050403080d2a080c0a02010b0a301112030733110a0f020f01 61
    0x81440062a400343c440112501c44003100c10140f00c604c8805d2144842c0c11103074071480205a00769048040c411540002d004400190780f00140d6241429030b8400d0f2070598100383d035210360082c0740c0d0308208101c0c003400c1200c0c7c1c100010105107002c203009004045500303041c800328034030720500b8170700a00c0740c0f0500560001c0540a07403500c40361240d14548480c0202d00043c41035800080203440001410350036500000c01411070525580d00449181d0000441c0708204a1700344800000614607074090402c2d0083e1400204282c000d50080e4020f42c806001c9640c9441110601d0746031094008014030342080303188200d0365035580d68003810b9001d41100d4041139007001e141030000460f00c40500c40c900009682802050508500540b600c0c800c17803100001a00f0034150548844c2d151400480302e6040c0c4d07003c402a00d00700030742274031540c912150020010f414021100301240d850780907040c070700b103140781004010002c5061900d4090030700d0051000c110140010580c60740d0899008000c03201d0742c08a240d00a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 607707706 1250 607706456 607706459
    0x618031e08090d230703052d06070906030f02120c0906040e040506060901080d050316030e0f0c0a06031413031e18050904020603040312020d110c10050912090f0a 71
    0x101c21000070011030004c2c181c0c0d1034031442215540030442c80212504100102903103403520740601c580e290b5071a07601805aa11345104144040280881d40c81000c42d5140c0c0080070386030803c05404d4403000021044442d1040041d0419080032158480e00f00000c0e844007600c0351640000310361030384900d405c0744528011100c1044104031780029001e205420130ba814009d03599a40c9000366550300c005030b184020450500010710840741111800c400d04005103004101b041014412500305400c003100102a81c0003440c1c680d60908200d004000146000c4c50300f0024095007030b0302490700d0751015183c42d24138140d040c1c0500506109030f0722035007541d0082012441804044101801403404429189aa4011051300145629210140500c5241c0140010340740d0381d915581202c2c50100140342c0c1322511741c240608080c240780f51050000d000f000b075440c90360301c3e2404103100d458207504c141600080e03070a000401160240c04588208203d1160741c20343d880300c00d0f100000b606081d0f9001c0c0356070001c00b078100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 607708956 1250 607707706 607707713
    0xa0801020f0d18020a03080c07030c0305161415070f020613090b0402210403181e05060a020c1201021620010e030c1c080703090618031e08090d 63
    0x1040c1d540303240d12080140e0703c800e044800009840d07080103540088454001c20210f420100142041b00d00d2006840c0e031580c480d6100f6052a01a42058031a40d1102e18070342480300a40c14510050303c40d1041d01c601400301d00300040c41c0c107100041d050058000115100c010444105642c44040b0b0707000302856103441e800201101c1860480c490020010700304a0cc030815402c0520071651151410081000d83d15150030160b03d0302000070f401103040002c035034450540d03800840b04000c00f424215800404000c0c41c008401c500c1801c54001a118280403c42910039940014040512200076101c10000350140403e990090017050a05092008031100c250104080c3d45000050741c5d0080344095803046034080111012510302c00ca031a09a8044102442a464801c009480800035803202c244500895510344216400c2484102c010070760402091007034603001b0308480e4180318000c0d0046112031458440407264401341c030b4201d0f1301d04421410f9500340300c01d4400b2580050b078003400d0300c0d1101d000c83c035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 607710206 1250 607708956 607708987
    0xc170712091202210301050a0e090a051507090519030605040c0e160f080411040f230403020105070503240127150905030c1002011508060702100e06070e0a080102 71
    0x1455440e08800c2132111074008291801503030305803007001d04855552402d00c5045600c02d0b00103020201b40344207910140c00001e10402000408140c09444601607050460340a000514142c1101c1d205120b14030111411028442043e400c40c0c0e0000004510340d10380741081c0d00c4181d025004001c4004826081082000301c0c002103180340c91440e03132404958020744204566420b81070b80c00070400c01480000100700c0c6071941100e0842c245c001c4c00007811042450036091418030b010702220700c0300d400c80b080200349502032040590005490074800c1c514070701000c079803000c503480c2c44184442d0040f061302c81c000b41c0d2164221103030000e83e5000041c41d0b103001d205d28002c191030900c207095585110350000c12040d03100d45405000c030b0710701400802d0101500010070500c44181c007509400c640d42d84450300b040040d0b0000500041c05a10082c1c20603060104000303051031a4180110700c1a0300f08028000c40b140d002032090340c4200a803420000d83d030100000034000c3d8605c0d50007904558004904d01c2c1445a500c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 607711456 1250 607710206 607710223
    0x20f0c0a0302150c090108130204060f090506040513030203030c0304050703021c15061d041109010b0c01061d01030b070c1b061b0b010608041506060507060c170712091202 75
    0x80006040f1a03558250050a0b8403454851030700082998020801b1403024210303003410148024804511962241642d01082a0740e0340080706042c2c440040c09001d043c50b104454001e0030140f076038010f00900b524082d5a921018001180d02c076000800502840300c10700c4003402860703006090004101c1040071264103030351107080940d08030452540035a840d0b515840303100c045078040860003881c48440701300442d0087e4020000d441d00700106080315040d075980b0280c02c0c0642052102e00740c90b25a9001c0f00c5086514075000300106d001130344480c1100c0311040e40307050b044a45c007843d4080c441c3e0720701c4021600c001c10380030000d010a00d00300490301000c0011580d81c00307030303000e907a070311200c00000040c80c1890307800109003c1d20741030841c3c00501c05a0320078901a58072900544c0040c1c880007003102c0e030702c0c100c428030f074405000500082880802c100d1540200900300340c040c541100c8135030f081100100029000341010f0b0034000d100c4151425034505030031a81c06d06801c000381c12025601420040c6d201c080302e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 607712706 1250 607711456 607711483
    0xd0513060b090f0601030f11160507120b0c0306121c020c181b0c03040801060f06051305060a0309060612051e10020f0d1b1e0e04020f0c0a0302 63
    0x200800ca50250402e481900d1003109003980500305a15450010f60092481755160246d6544400c840328241c00781800401d2480004c004104802a1508040b41450401c5c3c101c6840302c1230810404000c628001c444c180c2190b400c01085035241c407088002001e600c101003010f11280958001c1d03640341103980221071a602123135001c0c1e581481201c3c2c00c004030403a600100341040700f00e01c0081681121a201d200d80035404540c60b051400801c3c06c089440d54110b0382c0100c1c031603910754030248100e0100c0c0c040c2c14010085801c10500741000c0d9070009400005600031680206c101169a80c0307071500ca50010101c1e141c00900c01c0104903102e007903141c90580c10244c10b80381407182004041c0e9041040f06410340c0c5280c404007604059040c86202000303980680d441c420300c050300344101c2c8016186841030384150315017040c900c01d03140304120018100a4000301e05a6101c0540000312120035004140114030060466005a4a4826180b0340c1c580340101d2800010a00c201081c080826400040d4101c81242c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 607713956 1250 607712706 607712711
    0x2100e10030b030c15120a060806010801020d06060f051b160b0d1803050316050d0203090f010b06092407060923030403200409080c160e010f0513020d051306 69
    0x713400d0144444c00c072080c24120b030441d20821503400c1c840c02d0440e00e00d0f04140c0091011542e00d5075030000c60302d0b080342a0080740c40c60354002254405240d007032241c60000c0060b0b007440c440d42c0071300410142a07802078018001416014817900209042c0c103002c01c074105038049828041c5a5243c002d911a503400078101500400d03e0b2186103864109000800310585500d0758075030f45155100c40843c9240c429080803030050240a02080281c0022070000d1803003000458000d100741001040f143c0d080d2140d035111036000d10300c03c0020300c020f42c4441590182d540451811003440d200c0207284542a40300300100a040c04c4d15244d0580108540700c619800e88000080b5480c00d103040c580b109540b42d1156100061895000c26420b440c6040c200c0ca60340500640100b00107600136107525520190f070b20943d004001c94125410750b44d4100072004110000d8200384008112660412480b10255481402000e100303a0ba5007507400500483e9404813034480b00001c2040c001c42c10701142400d81c06803488001c4030501d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 607715206 1250 607713956 607713973
    0x20304050301060b03010f0314010e0613260421060e0f0d0503011503050402011205010f05100c080d0207080409020a0c030917070e0c070606030f120f0c02100e10030b03 74
    0x4c0e15001540c0c140c1300380350040f040da14610b948032004107050582c80489552500e514858843e418801d541c4110347c2e2201c0e0985041491400e840c140a4100032660385003014003684036001d442d082510181d0340303111092109100e54550240c0c1b03102030701100800c150304105101c52482c5001c07901c1c0846070010012112009080501070b502c6006c00d010300300c0d10406118900c1d0f081c910a41101d500a030041c1802c0001d014020402015100243c1024800e17003182038040040c0d003003000d021480403940b441c006040341407950395030545119042200c5009500800c0741420b22160400321001001c00090441daaa001400e024050111141080c1e01056020310002040420704401c2c1208070760380c0380078084140c10000d548103001005020300c5200041030102400080b10b170f00c1004041c40c05035003105050000b61402e84200400b01014800b0410707c4c044444c0b800b0b40122030341102542c11261002d86120b084001c40d2584040400301e41e0004444a106c40c6094143d400445545d50035010b442514 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 607716456 1250 607715206 607715219
    0x1203041410020a0f06090813060206060303070203030304060b030705030313050108010f08250b0a0e030d02010e071401050f0423041b050913020f131406220506040602030405030106 79
    0x2072820000c08000d070300002c01e070000207001c0c0300e440c0300c00d50300c00c14000034410010346414041d030300038500e9540010381c2c0398414080c0c9034041150a034814421001940342c203119901003078590202820003844e0541301d442100255900340325400140c00c014080760f0b21144407941c640d840140510885020400c00400812010141c1d4070a100340c07484100105030540040b000711206034941c0500c0803100f01d000001185401360f4074000c01c4c00c2103807a40c079901d101c01c81c0001c060902044525a0381560715042d01d2102c0745801082400440d00e0075030405030b0030940040180c07150700c20003d080030310404c00a07000c1a604400110080e05d4855200c0d40190340b0781020a01044580e85103d6040e2040c031641c03808a1140704000a01d210000548071035101d21014288070180d80260388200c01442c00890455104881141d249008000240c1004000030100012601d940f060081c81e0400d140d85241c45034600200810a800401c0c01803e410303034465075104002d449400c1400f40c14841d50825a0001c0c07003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 607717706 1250 607716456 607716469
    0x106020c0114031504020c0a02150301080a080705010e0105040614130c290705150a050c120c070b01060203041a030105060a1b05121902030a020a060b04060512030414 73
    0x40300c10307118007650415180c684801500024503042d0004054001c01c8519101e0380050403100384000001c2c03501070b802d8410000a00d503880000c1504d0001407004004294001072408030711900904040d03542c2a003428814094407154500541300d40c2030100740402c202096200c5000380429900b0802a038617034802d94040c08a5100000d0204401e4100502819544008d440802c0d00245007180c1d014562403281c68042c0c102400503290342c1c0000074000c60702484000c0403540241c07400c000b00300518100d02011440d0190b582130040e84041d0038001050402c4d9841212580c1d03030801340e03912507507a5424000b50360340c0c054000c2d81d9041c02c48403c84071201d4440c4003664140c840042025041c041c00d018116841d068501411907994629103581011800030302416481101c41500e103561842d0b43c22090520843c40035070f49003194010014404050742c040b40200000754804004107181c00c402000030060302c490307000560703c05100f048030042d41100000400460307046c10203900e004e01100042040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 607718956 1250 607717706 607717723
    0xf1a06010e130506030f0f1c0504030b0c16020301020c012403030e0f0d1e0302121207030e030903100212060f0603130516090b0301050a021c051801051608010602 71
    0x40014000140d5040c2d40015082154410700240407075204000c05081c07149410b00c0307566400c3c20344e00084510f0a80c000909464100f0b4100c0c1c0c14031074030380b51842c1e4032441c0240b0700800141d07840d2004100a043d600302a401d59503c10380090003903481d42204503141f4020120402d9542010041d69449509148050103840483c2c3d0142c0315124249144000e1014014450b500781d90310965001540d0b00041c4c20b103000362805500d903580c60846003502e140181c60141d10891302c039001d000034090303691074501103401c0a03070004a03482c01056254103039031203d1030b5018103040142c0c14010091100c0d2405400d0f809404280024007210541d5102c138401d000c200340380783c3d01150300138004200040495411000c407419151043c011500c03102c4507030307555041402c5076400c588455900d540408195103001d005041d00180d0300082140350007600c141d00c0044603001c10340710704240d844000141c5d207450740040796020b4a50201c020301542c500020301c079424036000041300b008120890004100103100040000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 607720206 1250 607718956 607718959
    0x62301080a200906070206071a0703050411010c211d040504050304061b200909070f060f03021201090605030609060c0a1d031005090d08060d0204020c07030f1a06010e 73
    0x41c024032489002d4460b4001c401081c2c114004105103001622080d005200c020302a243c02c2004500225031001c8122000e0514000c141c00d080910010400b04041c2c44140d02c1c0074205103170f0245091400c028185e000221010034940981001c1c2c8046810400000c0c00400300d480c000e010810800400044039001d072005041c07507100b400240200c60254460845000d400000a00004603554410038818041201410000e045000c0c2288508008a40c11b401c124035001406056041c00303004e01c4403022511401040005007001d019070a4002c0e4102c41d000c6c02c110301000c24030b68494041c81c01500c0f1600c0380600a20407000090081d22000c245107010b12036030010a454400002c20465031044060312070050042e81440f902c209a404104488001c03c0c3d00d1030110b1203151010700c0c9404c04400c032103010244280c4e6000c1041940e20001c54040140e41150010f0320b41c4121201507140031401e40000f0720001e4006188400d01201104501c03c07030580720003800c4941d0710100112030109070300b410755 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 607721456 1250 607720206 607720241
    0xb0301020c0a0b0c04150207031203090f080901052517040f03030c021507050d0f0215131b03080d06091a040c031e050103120f080f070201062301080a 66
    0xc0002103144120a8200c484c01c03030540e04060b22a02c070a5603442d040c404410240c0d110303401c06c00030000610700e01c0b08a0740b01c1d400c04101c1c004841c0c6035a085241a250010807070f000000749140560f002d2401d40301c0d81e64042c00e11140803210b20000210400c84da0200340c5a0007100c8000c2000342c5903070011902074400c90100c18014900d0b40d0ba0544440c18060030407a48018481403602800003c2e0024001c03041c040c40081c410400034a10141208014020381401c5410440600900c1080110000d4000c0d1800400918088031418850b504a080c0001000c0380075098600109001000001e86042043e203400bc0140c545e495101404031101c1c458180d19289044003026010f00d0950b00911401c100e5040c080382c10413200f84001c1a0a150100102c00d4982d544014070510904940c01c5400c4096410a140c03222080389002c0c081000090980da10310340b0102c00100d220703100790000401010f070b02c80e0140000480d00000184141c40401c4540098a0107001450000741d50141c0c81d4404c00b120f0f40c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 607722706 1250 607721456 607721473
    0x3270b25050307020106030b0703020703111606050708040e040f06060819030c0201142a0303041a0a061805161d010507081b0a02180402030303060f1306080708010b0301020c 76
    0x981c0e03036810052002095540c1c031040003000c18914030361f80b4400d84456070016a96031181c075000e410089210120000da9000f601100b401c2105020300000b51055800d00c2c1e0348640c0310349440d44240c403494002410b00c665810600c0100404e000320398180720710a00c1c00f0701c201e0b91a0b07a681c941d40d201170240e0720507550013460480040383c0240c000e200d0450041c503110407024003138039103030f91142d12030380c5d0340d0404600c840d40341c0c0d83c5003541d65000203884210070b000e1851802c150b22000d6a00d40c00b0f08109c54490f90941c045012443e16500000041804a2458040700d00c0010010010542202d41e51101c035107521450031060b10400c582000e0300400e0313445040920126004540d59001030408548500c400c000c0d0401c0c0c0e0301e65018500d00910448024610304400340b040c050800b01206414801400072020300005030782c040280c0754440829610050081002c9e0000713401840300e221a0941d03a03142c6040400e00c078401040700b5050300c103145c009205007480442850308038461056035250740c0d000b000c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 607723956 1250 607722706 607722781
    0xd05191b0f020f01060611010b0603060d03030209061303080a08010806090d12060e090304090b01020a030518010c1a090105011d0a0b0102030708040b131710090303270b 74
    0x41c200000c08544119000a008004080c0c02c44081d44c120401090b00d1007000f100b011424020440404401e41f0134905500b40800440c0302680c0d002e40080c207164000c0380b40d10707141d11400300b5510310031007420107000403036034a04010046902031140807000412800020408880004010b070203070b011040140100541c1d4a0100c13100318000c60050415620303000001442a08a19031710b0040c1c20700e0002d550b4540c035051405045401286816041d50000d07080c0c40c0100e5081000d03200c5203581e40360105012012100101e9a00f81e01207001400d0845900981c401c0920f120700c120300c41c1c0c4c8410001c12044e40c8030400651f4001c13062070368000c4030412030300080d45045150048103880701c041c01101d061010a64510000350841c0c2c01c4040350001c080744403521155506c42c440d004150030711071807104440e460f110503150410414003a10142d1149006001c041c840e61205620100e038448070b0302c69219100f619290400c0040098546820140108210741c500d50b103c0c0e0a104c4424291a081141460 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 607725206 1250 607723956 607723967
    0x1c020405061309050705090709150e0a0b030c070b1008030a1b0206160c0605091008090a0212010b010306090b01020303010611070803030f0601080a2d020f0d05191b 72
    0x90103690000b0b10400054114142d078021285194070800250260700c0c00c1106001340c0306070042c0501d041105200080000d00c0c069000c20780c0e85071881c500020340324041404500b007003100d03030302070705040c0000820070040c2002000603007803062083d044486503444100e4200d10f80da00d60700907e201c5400401000003d40d0052000c24440401d50201303400c031140c180c0014440b50441daa0900700001d407200f000301000468000007001e0251420311a0410040f2404680401074162028041c41509804203aa0810400941d0b03801a8001e08202d0050030f241c0c000c0340600b941050050100341042b5000c980c01c890b0b13004052124006034011411686001c000b10750002a01044103c1809180c0c0c0c08200c40100340015031103511261200c05c400c0c100240014620600244194652031a05403102501d03045a01d482c07100041c85079030a800b41c1c01211120b0002d210b0301900070021100010900444a06504514072561080740d202d10b10309900010b400c155410021515521034a80d4404041e490251 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 607726456 1250 607725206 607725211
    0x15110301090f1e140906090d0309080c120405010e010806152802010501141206010b1803070801090b0f01030812070c021905030c0d0c1a1207030203060f1c020405 71
    0x2e0350045411085044032000111204922007039060f240e04106840b80321000340c06802c0002000201494a02506607640781c031034904d1800201621450b00c40305202001056614800d90213054520001102c0c4c2c662925600c5403042d41c2c041aa503642803e025809840424805c103809007d10707526040b13095484003994414400458102c8012000e0016642d51041c6904608001d400001e1a94181030207a803a40c080c200340ba5110390420b0740102d203840c03004a10203044543c5c003582c080d10b07110301d2070158000b486c030300c0d5040760980704004001401150540200c0303451801000c1001c02d07a00c580c20b0808580200340005412030b0400c00240d00b08560700305416130321042c945003a1071700d04c10560000e103041a040340644a950b4655605202d60300d418801c3e5040031404071500104a415aa10100921068030509081500328030a02c001c61f90f00030100e41c1e03140000f5910316068a04180081c0094000340e810031b001d12a66050000c50341402c2e014030b070302c20b6030350700d015009030346103608000140400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 607727706 1250 607726456 607726481
    0x5010f0209030303130c0b07060902030129010f11240603010b060a0c0807171902190204090822062303010e10031203020a1713260a030204031511030109 67
    0x1c4001480c20b0740747c0d018150301445090041981c01c07442c010142036030f81d54071501d2048a04013a103041c03040c45078418124410400e0810302c3c0340c54040c80003940e0b0107444040d22503150140d501c000c0d401c55180f0204450410b510138044231a519148145802ca840c407892240c1c0000081100030305840c050fa4021303091038414400030340380400b180e44001d40d1410064160380c00071000305811020201440c42d000c0800d05a20041040f034040b2003041c0407a100e600800390150340d441c0003034420302041c2800c031031840f00703006840e1080410041040c141c1c10300360f1103200002541990b1141015103a0803c240d40090800c0f03c490441e420922184010036014080c4140e2201407000000005d000c10600311420342181c90042c3c991107048005003018210080c01041a03030404100040c5080510294480c01d801c500f00c201c8036500204100d0b02c2d121264194001034201051545000798143c006001f40c0780301e82180c3c4d2061f0320904060050300e04008212030306980900060040c45400d80c00303d07506050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 607728956 1250 607727706 607727723
    0xc03060d111005070506070806280e090c2814120f010b19051c0203030c010212010f050d11122a0126010612090b1305010f020903030313 60
    0x641000141c00c03501c190120380100d100420490b05112042c48801c0c7d01028500f007201440c60b00000050322048224242c0007107840140710080700c848110880d40c06010300d07496141140c104413061a40d01d450003030f402842000a1031154882e6403070610254a410280415501d166040800100341d1600010304940c000010114440484908101d1015031a0030000006104820351084c028401c0c0c4080410b000703421302c15410051500d03140b09035100d07400c0303806114000d200d40d40b0020782588259020f8480660000c503282d640c412000c200c0d24100c680c610000f210343c41c2e51341d05001040d07030300c620091301c0c003c408291502103082c00001c01d07103607581e10826109090307022040b040700303908901c0c034006901c03200b10b031503648958004a410100040c03051036600c00b404000110552960140250000c0145580e4103a40c100c9140d04044c04096200120015920386040c800342781d20b4644205070b40759801d1010b109450ba002c0d01c00c40c0d04050025001e54a195204040c614400c07091031000c540621 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 607730206 1250 607728956 607728983
    0x80702041d0321070306060c0b04030212040e07030b0d051b01050c03040f0e0703062403181a0609131403190903051005151e060d0b12060c03060d 64
    0x41032004041c5051044807422180414075000710f00000000d015070f00381403034103074280507060300710107040355180d4080d02c811050356607807904a01f002c80214202060080100e0085034014010449510903242d50707074100444071060042000107043d510000d41720303400400e2400007040c211280c00360b200c2070604215243c000e60740151451039029900c081d1411401440c14410341c000c0b071007403c1c1c1115081ca41031180a041952003541e060112a0045444c2c2208034049030403406900008003215440b13070f61001d80003580c1002c4004041c2c0c0d201040c01501032100081a034030341028400e008074284008211080701903600c02041000c1c54a0890032403100348440300c1900c00d07c296043c64101e442e40c5400d9443e2841c0b411a141c00701c00b800300c2e10130303500f05810807202050203001c0784541d02e41103440501c40c40904028505000004c011103800c103c0026041003840002e8024041800056580c41525030510001d1910f4240c20764111100e40c0d010070208000c0c0c5000c1d43c0700f07595a4010649643c044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 607731456 1250 607730206 607730261
    0xc010e011401121a1f083702061b010c11030a03020c03070203070f180207051203130218180304050f0415210c08011b1d1504030c1208070204 62
    0x11904454118585c1c40c40004121222101801d01c0000e003180002803044101ca0a040d050b80310b07118451850004000c4040c181e2403038003442c24280d954014000c1c6544096040354044040b580d5008001a507082007c010000f9114545070600d06018001843c1040710f2a4002c030040d600c015244c50483c40144540d9001d640c2c00c0c001407000700210020000124540f407c0030080156201041c80139900c1804100c0107d00003061384031211281c418115030781ea4580c10001320b804299000650024200440c404641c0c0701d00030f116000e0a44100302d80d191030038095100c0d0343c030700c9940505030b001022250549610705068101c000780000c00d049a2a01503202c0324407054804000060690841d00c42c2d10b04800c3c0100d120500c00a401140002e1001a548014005180803010362400422510f8030010f00c4081102c11178095005000305030422a030305000344510190030501066034080e1a030a000104004486541d40025521035a00d03810505290200001043c000340d04040046a81140f045807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 607732706 1250 607731456 607731503
    0x306010e0f130e0c030c01080c0702010305040c1205060f0a021305040213120b061e0906100306180203100e01050d0f05101d0105070f1b0c050d03050c010e01140112 72
    0x90b03c1c40c000800c5080582000c0602c0d0054139031203c0c1c103200d07650381444015040e5000311540d403a02030a000c11503488503d41540081030550050100040100d040c0b010031001280940c05252180b01801654a4a80c01d4008a10450203100c01c0f45032821820425400c140c0c01904203c0b0382c188603000318607075030820f00c2500340d40c00d502201c2c1890854100103c5103421303200c5221002c28546e64841a03040f110101d42504c10213802c803446180c0c118603041c01644070b50003d9000c2c0015410390b00110110300740b5000a0b40054910360190111000c002c1122180301c0c0e40303e8100c40d00100700810b501d126441c1c8804402c001340003642d85d4014814143c43c0c607030740d60190241103204502200c0b5a52040c0305c130a8210b4801910420800503401c90791401a60b01412506101c135107484440714808252802035403c036910340c0003c1e0070140540c501c1043c1078000d00505580241c150083c424403200c28850781c00c0b180020f0007031070190424801401f0307100720300d02c503001e08a11401c45e440b400020060300e03200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 607733812 1106 607732706 607732721
    0xf1805160f0302210a1209080f061612020708030f01031514060f19060810211712010e1b03090606040209011704030c030806060306010e0f13 62
    0x900b1028071040c11050350110545050252008000c7d1400265108401d00e500076580c80844140b4041040380c4a032600100010100148820a540c40421a52203000e099400d0186c8000254000011800780205000840c030541c035504e46010030030711081081c0115414490066000814070f450700d604141e048800007a801c203040d01041441100c12240110b0601154000904503040b0780c006018581e5a00c61300f0401d5101d800002c0210700104400e045a40807000d240301050050400942d4094800300041c0340004040484503d51401c0e000b03c034141c80c545044c00a003c001e0140108111035501c222800d51034a5050541c0310031008100074021500020359010507840760610b42c00122680b00d5500c030900f05410000c26100c0f200d42d0450100c3e1003103003c00c04a00d400380c1900c0c4a004140d4070241e02402c03840c2440100c803401c103811500213204104240a88500d400741e000f = true := by decide +kernel

theorem cover : BRFrame.Cov 607553956 607733812 := by
  have h0 := BRFrame.cov_init 607553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 607553956 ≤ n) (h2 : n < 607733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
