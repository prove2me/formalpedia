-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5534
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:10:39.662593+00:00
-- url     : https://prove2.me/submissions/afbfac83-7c9a-4dcc-b47e-1565fa9e3dde

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 995143884 ≤ n < 995323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 995145134 1250 995143884 995143889
    0x110603060f04090605061c0c060f091d043c0311031303020307051509010f0e1302120a020901090b160804030503120108012304140601030b070905010333 67
    0x24420490142513250200083c6400e03a003c5205800107600001003450030b140381500380754000c0401c0e500d01c1c07408000341c0f201c6900991807001e001c00304a001c81e460b00030484802c00c400000401d09071a0a290414110340d103113160760807038154900380032040302d08030501d4044090614000f11358110441070800300c9202c0c60440c0200c1c914000001c02941030490030340c1040990b8021000c2d10720309070740c0c1c10801800040644005812a10902814a4560003807100204041040c100031403603090100000c1c841e6440802044659035001c41e000805a078018011644003400b0f840440c984880c082c0080d260742e51505c502c0c1c020320f4002407040d0b4406003841301c01580701c3d4448025074803240c80c0d1400c0380e11b0360000c4903200f400300c2c141e100000c0d40715014090906001c0d4050f450100c6a01c44249064803150300501c03d8506400344681285e10a20801801d402180503010b09800341c145070038010301580c81e0b50712450405080c4001e06a105207c2c120010910300c50000500030700c1200724880a40c01c072980e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 995146384 1250 995145134 995145139
    0x5090409080a0216080c0a05041a060a0f020120300109090308060306060a1202041e0e15070503190b0d0b010510110a02060f13080a020111010207110603060f 69
    0x104160b540385400040c0c40b40c2040e40240380e040907540320700d502c030354415405894540c0114048010000307410581c1c418500309901154554001c00004003142441d8001015040021036012840301d0065080c0700710070070301c05034198410f010709800100c11a00e01039640d440d0b4a14000c0c07100e0400c41405a01440c4d0030f400c0c10340c0b0090741580c0d1805a02c004101604045c0c7c089401c84001400b90304c1c010500b1441014010410039030740d401d0081300b094a402c4030008a070429074070700504100000e00550060b04148142010a20030030520015041907071480c248203000c1c5041d02840071907604082500c1d0b005452081d600515610001c81c4005000b004104541150f0700d04107181c140320440b12002e041e51000c1c1d074081900309032040b0881340700c4070003004074680d50014036a5078014075240d001420184412800281051401c03942c14070040e15030740c80014140d20242c41c01c821541c004280340c0d03803014081e0003182003201c1c5894943d01450b139002c11921610700040068140daa40c2c000c42c40682201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 995147634 1250 995146384 995146387
    0x3020405071b05030702101107180207201002070605070213240603180302120a03110c0d080114060316050408010c03020315030a020d03030209040f09050a1101110d0509040908 77
    0x20b5052840c0c4a80c0b110b00b0680c090084144554591405042d07038117a04010840102280e915006d42400d443c1c13014841c500c5166001c110203c0842c0243c4c0d4200c640c50905076202024140c940100003210041f03406000039901f0840c02000020f401130b060303a11040e0107441c155034481043d081d440040120f00c03000e01c0c2400303c0104840794401188a40c0080e0380454404000d441d00750303242c1d6003200700301440043c01030b40603940100d00075040d48050803188c00d140c100420002e5880782c95109507042001030201c280c1c4007003c114400341d0321403080c50040040342483d50150f020080400d24503c001000700000c3d807810300591405521500031107005202c01c00c020000c01e691100700034040e500031744402882c0103c0d2010030f0110324010500303069441e80180845008038540d40c043d0080c0d0406e6038a01c1d4020369032045002c04d02d50314012041c4c0320744500050200c6914515011080c00c4015425034100000c03404802d6075400b0000300c0c070480044c0750a21946550743e040000780903050000008000303660 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 995148884 1250 995147634 995147687
    0x12060a0905013605040602070302102c030f030c0a0206060a03020a0902090349050307140d020f04030b070e0306060607061112011a1306120b03121b06010f0302040507 73
    0x594041c044c043e00c01e500703807880c002042c1380120540d0001c43c0338160000346c09014405951107024441c40c51140081680c1c02e0040c0040d503400c00380c00807507504018040014014090b07030750501c0941c0e030181e8100d0b0941c0c055402c6030003040856615000700c01c54168005240005981d041251641e106000c947c0254070341c040e105004c0c42c407086111401801d03100f0400407900301e00c090b2000c0030900c1d4071741d841c1821542c8101041f1010b8001c9660711803208010002150840a6070001384801024419602da032640781d8500b2003a4510000c041070200302100075035580c40c0d64041001174100c40300300d418603120011424038000504006503403060407100025003581013002c04403402e040f074005001104600340d00e403003800142c3c0300398101098040240d41c001c0c40351a000340480d00149040281c000b480c0c0c513110020038504112800ca000b48808003140c180481c00e000b020b40907518030450301030449545407503407042d440151400024880e988440001c0ca110740306055014084c0102c4010100d03418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 995150134 1250 995148884 995148893
    0x3090a03060b10020106050d0b061909270c18060b04030b0106200304050108070e03060f1f03020307090f0216141002120414100212060a090501360504 66
    0x8030003400580903d8803902d1110303100c1e006120318400c580e000ba004500070f04682d41c03049a002c900900460380824900104c7c00712141b01c00c811f501034a00c10714001004040d03031245140d0325020344191014a0280e45822001a05003089101112074031200c0081c280c5100008801801a07074001c1c080310600031900100740328206003818101c40042d1100c00780000c1410b00e600d40c201101600c18503540c01000100180c0d4898901c6036407200c1c40b41b61039280f402c04400080d04140054030b0704840340d1040020b10280c0c11041d074103210b481e6000841c0c2c2d0b11051640d4082074584040d03100d01c020b202e41c0ca803440d030750356621501100c1024107040321011201107149040c2040c06800c80a00642d4403030b070100e40045200c181708407100050006592611682c5541d03420b0f592404401442c4c03014003d03200060b000c459103002401c1c010740c0d00541e89109242034014000ca100c07250303108641c510305100041000c140300443e4110160081401d06080c802d002043c0c3d00760540c03101c1c014100c1480d0100b00400d02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 995151384 1250 995150134 995150141
    0x70803070609020a1401081308070807061b051306110708030a0203040806010b040302060906160c080106050f0405071b060204031b1403010e060105100c02030a03050415021b040e03090a0306 83
    0x1d8422284903030b501d52581c0150314603a030350b001c0203030100f102c1c7d1020410314611682c482c0300140c400c1120904d00180342d80c0e4131001d600440701c00c881207604c40c4240c0441190b0358400c5c90342000c2c2440d0071070030400410001161030600e44104070a01425a10b000442d850900000b8080c010070300c1143d5991486403c000e541c0d60140c8900c84e01c3c1d0081500104880b14030404850449400a14641c2270003045420030025511048000043c90010143d03075000440c51030b1104010300c445800090040d02e0b00c0148010600c0420203a44143d00d860100000c0f9500640c40e564002280356000800d0076007490258006c1c0300d030b600040d0544080d6800c000c03d010703000141c002035984c0700030f07826480d0f82d40009050070b036804c0c086584095001180140f180d420242c0c038204c1960964540180c05105540101e401c100425600b5000108005401d201e000008094410303140c0c082c0c030003400801d070010a580c180070641402a44503d403601d1500da0807140400940d0003100c401845004100e98030329124005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 995152634 1250 995151384 995151401
    0xc03021e070e01090c05270904230303190b0d080c07050109140f0415030807050105070f11070578031204090b0306010e07020a0f050708030706 63
    0x2c82c00d808001180804481c01400101055501d90390f00f08092566110a24907031040d513103407040001c2c1e8008402e03540351500a4011030095444440d200b01d1412496140898800c1565041e4000c20900890320a801d043c0358038150808400180c040c00007001a13050f1088000c0138012940119802907801d80c0400c01608903074090300c07403108065440b48445029503804242540c4208001000400f0342056044200d49012a42800e5881c90701e90307030f076500e03a43c02c0034600b41c4041c0e44d1001008005600940782151090050621040d16803420b07800c95030b40e03001c3e80502c46c0640740c1c001c8040164101091549440d0040c01c40200c6c1c40306401d003070406030021009840c69490b0050380e4252a240d01e488a0310707680300010784100310030f420940380d40014903204085c19816100b58070040342210350840141010308010750b00422400124002c1600c0c0a0b0b06811240040d1a440b050043c079940000c2d651001e558440103400400d81103040c0103060200035400075819000004d210001c00001d503000c2e202 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 995153884 1250 995152634 995152649
    0x91508100e1912080a0e030a0201090213060506030c090301110c3009040207023c0f0648011407020628060902070b0a0c08070c03021e07 60
    0xd85104111201010030904501510344070000c0f651844003403090861551050341c044000c54100c61004800786107038000080407006035924a02c6808600d071842040c0d1495443d480144400307400c0c900021801c1c031000d007803800319900000b81c00700c1c1500d00703400044401205200d119141c100700c40c10141ca40b15501c0c081c4000d08005420400a8510071038a0045c040a9418090403c04040144002036024030f105130707030141c814070505405d16a00e02d01c500382d16282c450341001c100343d800150558510f400b003441d80303c4c1011500710a160384a4500355a401203d4954013070b00200b00c019400204504070012206210300802c5c271000510bd0b0081e11300e11000000020003561074542540d140100c01900d5100058020030b000ca402d1440154031102d80c407140107003080c100f21031800c0d88402c90b841a80018082900800d090045c0108407201c150301140e00c16080c0004101070700d00030880390000b41150280142c10005409042c803c004403090b410b645c02200c0b162620303101110350fa586407445001e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 995155134 1250 995153884 995153893
    0x3161707061d0a0c12051501080c030615060d020a0c0209072c090606130f0e0a0c02010203040b06090910051f23040c03020d050a1e020a09091508100e 66
    0x1c030b00390300010320700d94a40c3c01c00c0b000c00300e841c200f00740450034904c1450142c0b01032080010381001c20060b0720f103044c000d04051b002007001d0103c01c0b0034103003040c10003071404440081c8950004402d0325080115052282c0c07040f00182d4400c204007055614852504002c0d4001849100b000a031a8028031019840d01c0c144000b1001c1d080444550345401c0c0c881090650486441804038110381000b20191080441210810040c01c4e202d8400c42c1801045500510a04010a003071002d402128810200d031218188001e501c0c0d0b25194032100c100750f601500c850300580d8640c0010704d06d07039810300008550b03e0303114a0501c85402c2c6583d880f54000c030f140000408044042d440001d842888040065202c0300400075621014251000c010041407a2a003060602d80c00300484600c000062043e01c2c818240c0030400601442640c10094445d142d40034a140801e10400c0780740403e64005180350200c8850b840c020414140b005c1b100110003216901411007841814000040da9029401c00101e0704100c40448 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 995156384 1250 995155134 995155181
    0x1206110c0d0306060305150a09020904020c0a0303090b01150e0928090209100303020d03110d140703150f03020f041b050c0c0406030b0a020d090203030d060e0a0903020316170706 78
    0x7c0e21040c0785c0c084e45910500503442000701c00c0301078000c2c000b41d41c0020801810300480101c401e0525240390402c9000a58601c200700c00c100700d103004d540c058640800f07401200322000ca0080c00303094410704414031030881d60300010100c012200000c082441d40c1c80043c61404102c0182002400702484101c1c4540d0440000480925110408608480c1c050f0700030040360482c0c103000d400604524461540e2080c0c20041c030003024207280102c0e040c0942500d81d03181c0c0da00d884c54004040b40c81042c4076003098903501108012241c0d860f00060241c2e501180c401c11050707d0800000c00400c07070407030503205e0150a40202d1000d2600000540b20761041c0300c0584c1c2500d0b61040c01c00040790341c64000107102843c10301c0890044030391030780540503020f0314060014210b01d958000070300c0d50f01300c910b01c004015102d5406200304880300600e55044441c000b010b000c4c141c441d5502035100c0c001d92612015001c0400790a0050164090500303141081e04020705070782d130184d0300380303100900302005074524400504400c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 995157634 1250 995156384 995156401
    0x201c02150c01063002090a0612081c050103120e0a03060c050c0706020105010e0c03060409050a0b061804051905190602070b010e070c0b0c0904020c0105010f0b041206110c0d0306060305 81
    0x101c840314200041181c1301e56840303508001031340001034030409031030703039540e90201d80001800d2140000c24021180c0703c3e10b64000d800500a080c0304001e003280041c3c1030000402c001100580e0140b2400070900f0710080b00402c200101e0040740260f84003904840c1001c02201407290000000c20301081610250b4600d15200d19060703080e28002e10541a481c02c0780302c001804540e2450246400100040001c1020700c00d0b40c035418502103585500ba1900808001030000d5454a858003e50341d20801301c0d40c003c00e02d4541c540c69240e02d5500b48010812044079040020803800b40583c4480c217200c188501506800d030b0a09000070340009a0450340c40418500124035680f00d00081d5105e214166503841208076540d0b41d6000200c0042c0c20204012010b1080c09800d56440c0050500c4035803142c00017816600d00210404000320325401208402c000708018010b1074400a0841d1311260401d1001c2124011400c1e0000280b281a260100342e015074208a403101c0c1d41500700f5000c89a4940c0c082c0000c0d141c1c4081c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 995158884 1250 995157634 995157689
    0xc09130b1008070b0711030f1015030201020303040206160209130317010b0702100302040b121f3b13030e01030216020910030804080a201c02150c0106 66
    0x19910607a405140104007042500c4c00600420b440b649103c94064995070119182200002c420885500130031240c4c0c03c2c10691707200d060500f60b0b080011441c00380c80c43d00080d40705d100141002e8003401001422440c030003148034008101c0c940c09025105d03245405060012528407030941100098440d220101703501030402240c5058420040030f01c1c1c5407104680c2002000e614400702d500901d82c09010014104440c20050b082160202496800760702e0503100d024881000651011100a00040188489008422080c9000040e012036442134109043c4509916072901a031281c001104000c01a0f410381c00194035140c43d1098484240d00403108005405a0290071030b4840c0f4078010314010409803905441c0540c108040f00c900345909500c039196151282c0c0a41c0148545034840079803481000f0002e81b0710701c00c030f07020040202c0c41203098030001680c3c00000c561049001d811704020206643e10480e42d0607000c44580e2404d0340d1410748092050283c0030034400c441036035141d4680d005c40d150b01c182 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 995160134 1250 995158884 995158889
    0x614040e07080604111605010e07140d0c0302220e0a1101050a051c0221130602030405011b11010c170106110a050102040b04050f0f031e0c09130b10 65
    0x60310403000e5940020860311008010507440d8495200c454410a9260740c00042c110135400e0645241c0c07010703903420080d0075140340200c0304c082035000741c40c1044403003036104503580703149004c80340303200c0d01c40240c242000e02205582010354001030500c441045142200c20520304100300501c14004d401c82c0c281000d8071442c5060f405468004031485800b0a984601c00401c0303250301c1c90034041d040c503112511000b40d0b440410140d00c0155800039103006006441c408014400f10001d0724451680703401740c400c035066811203030b0040c0030039004400725080003420741107070080488504017035000100c2540b0003000c1450840d085420307035103803250400061b031003140d250340c0700c00c00c0c2111034446928204048401400d110101e03d118054694041d001a20038002070000b06810b622070f0762120709140c1040751441c102c0c021284140100b4092a00d99100400c4d20740c94100b0360042c5900458441141d03a040036011140c0c0d40d84881551704210445188a00f00b25230326015140c8444266104d034140110f503401d50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 995161384 1250 995160134 995160149
    0x90c1202010c08090d0b010b031b041419080a150c03060e0c0304021f1206170a0308151306080f0607080a0b180a0209090a0b0a090203040c1a04061404 66
    0x842150b02148600d80145040351000e07200309811240c1d6140c50401210030380016850705c4c000001d01001001c0000c04d0719200415282d03c900d000d2400c00510300119541c2c4c0d1640c007400d148403540d041034000e00c13444001004640b05684400703403a8a0540d99103000107900c4451a0301d0001c503852014070910032401550f200021010250311421650106600000d000326800840ba41e00260140646052200b10b5802501c0704600c81c00c2841080040d0380c2035400412000945407518480004002a16003d080d0181040140d40d1158900c1090f006211012190426040c14642e140d08880e98031800880305440181c4034550041c0c604652500b0040d01c814000480d100041a000d01c0140d001d0142180f00038007910049158240301c0e0100d83d0200d411007031a50703010a03c039216091080c805e5901213503a0700d00300700d038142c5040000d0a1182a02410451582c08000641001461108000a050a0f0810005600034295009440c1c0e001c1c0c0165000180e1a0165107003240c0500151416240030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 995162634 1250 995161384 995161397
    0x6010b0702010c050a02040204030f06140f01050618040c0504290403080a090302040912030b03161802090315012309060d21081005030303090607030c09090e01090c120201 75
    0x340d001111540c0b0181c0d0241c0d55805411444401a525840140021361045030f003c250003a09062800807105080f07006527603010b8582c1000013580d42204513a0540c1c130102d0f80d01e0b40340c029901c0c508440000c580000d0303800602d00301624100035000710240084400845140950300c040c0c100f056024400b01e51440c8182c5824081031000030001400341040951130302d007201c00070382d80e900041c082d100303181c60175140c8024a00803140110b6060150001c00d0b60160020020461a20010750f01080c152140c80304210000d284102215625011529202d000034100c40045c4003008410300108420701c210002c62014140c00d110210a5101005203004002c00c6c07400b41c4c0d9941014840c4503088044115020745407134110120302d264400040110140d50740e41c0e500e0f1480d0100c070a616485180c1c0149100754428010400744500001c1c0190b4054254070300483e13050070004080d80c01c1c0700d0f0758210412907400c2c10b8092003141c005601c1100b20314022008c1410321a6201d509400503801c2c030304064000b500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 995163884 1250 995162634 995162647
    0x181b04050a060c030527090f04030f0f14042d0b1c1e0b0102010501060c0507090c020c0a0602010f0b0618012307050619020412150f052706010b 63
    0x543e40d00020901905000c0d1074140e8200036030800080c408500c94041803c6007052070b185c2809080036071f2054030400404040d05094070f0190401c1c040060420802606400f106242d901ca000054680c55102040e00c0c0c6a54071000d490303d800c04605800c86423844103500d1100c10109003041d0108a030003415107140b81c008120360b024807480071900c080c8801e0f500e441040010224141200142427155400000c3c1c0e80d0350ba43c002070035144107034013040030041100c002a001c030710049480d00444502c03000c001000211443c05a0400381c400f51000c0d4040581c0780700041303064040d0480440d542c01241d04120752403e00c0c04100003809440c0600050a201402d901c0303195000e959404a0403c0d12809805540f500318083c20443d441920100e949d908801c00784100c032a03011130304200003480354400394142800c0481441403180c4c2c102024041c3c410942081c1c984c03884a030300c4070a5022903607409100d00d1902000c03002404840d41c40e00d01e18101c102034004c021050100d40a81030b90114072030146481d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 995165134 1250 995163884 995163887
    0xf0c210102040b0c100528020c0c090c0408010c0c080a081305030a05040f0b040e06100e0418142109010e062109030703080403080403050702181b04050a06 68
    0x10008154600399070030800411000f1a00c1c000d401e90100760380c0101607141040110005880000d81642c500c1c2000c1083c141419048400645074140000d10068955045001c56483c12a4254102e82c00c003003002c00b40003840303c1d10801401031710701002c000c5c048104040d030704554a0b40c01038000342241c401805800c406a01c658180c2d50002c4034011148032840b0683c40e600e04580c49080003138041180024104002104440c0c4400100000f4982c2c504041c54012480c0c040c08001b04900d1040705451014140705014104016464402130700070802c00310503445650501c6035000c0b0560f8002c81c04903401c100c2000018200050315040a400440195501c0035400305810440403a4184001800c2305145d544415020b000d00412000c0c040000714030028518006078009002c00342150010130a02000c2608800d450303070000d03803501d4080c4040d07403107040c110b80358040c4100080d070084124020b00400715203800003034002c030b05182c203034500c2550214826000d48218483c05402400c811020400903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 995166384 1250 995165134 995165179
    0x190314071410020a0b090105011511030a050903100207240e0a11150304081201211506150c031206120209040c0b03070503100905010e06041d070e090f0c 67
    0xa80b440d00403200703a12000d6407415030102c2c0840301d01701141c0d940c000410141241c2d072040000500d0500701040075071460f0317206540b039214a001c0e103005c0c014006540070040c2c4003084009a01c503a01242107440c2c4c581c1e1714150403600380641d1240b02da81100c008a44282c9040d100d0850785200500c01000003040c1c0e607448034001000c403281d040c0e02019000400e11503520400c0110705c103e214030269540e44550104000f412001a00a8070b081e040b0035241c6c4071a440c5844400070142d81043d65641c0401100310303000041c185e40c4d002011244d1030720150008094000c500f05079803a10a44406040e19040306410088030018458080c41500084002000d4200705071a00d070031600600e0f1428504e510b8000c07480b40f0764010758214000601c00401c1020780e403465101140585045042031005500d000c18038050042d026041c2840b0f656956070031410a2210700d030200484600505030b41036a66554080d4401820445411445004104c07003031400d1400410388401c507080041a45490428100a40392007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 995167634 1250 995166384 995166409
    0xa060f0b151c020d1d060c040b12090102091e15090d020d051e1b040603030f080a1b0c031b080703050307052106031e06070c0804051903140714 63
    0x200303508001c032143d5540d00c1c0c040e14178846500d80c1e01c100e44e582d0300008180ba000380200001d00080d024442840000c50380c1c0100c8101600d880d48201d80c7d601d84542d06402841080c4846503c4251a81d140d076107507400404e0510751250496820594421000100c2d03c240b0490340f540f940800b032100c9150051400c40c20b10710320103002d0000c403051f041ca4010a201d603203903681c6800c0810f62201c0100028201400c1c0ca003600c420058070148241c80c5142d0b4083e10b46c0303912018500034400b40e94002007900f41183d0088140c0d41110004e940c3c1c8276040300014020182480082d4001400b41c1500205c04103c1c7c4420302e00e41e94801d412600d0010a528200c840c1c0d0406403001c002c20200704440d0781d54215401d507034108241c011100d0b1129007411030805240c20340d10040455824101e4418082100001c6480c5070b014803e420400240312030351500d02c1c602e200e580c10282e48180741c09030400d2002a600d0740c050131740788109074401305081c4106000d5603804584c4100d0345080d04214800405040c00e480302c000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 995168884 1250 995167634 995167687
    0x605070503091507020306090d0c17091e010e190521120316030c08041101031d0703020315040c0603150e04150b10080f0c0c0a060f0b15 60
    0x200b00d81c12002034106941c01c00040880701c030216940d01580740500440781c20004400041c0901101c1400150240ba050b03032019000700842409031403164a01c01c1100d08a510007000c2e4100300f000915140c3c001c180704005140000d0250030b01090900b000d5802015400c41c2d80020300030549810204490300d41e40709003000410840c45811040c40204101c003030559940a44601c0c4ca070b11f4004140e108000060681804040c01c180320000aaa040825141c001360401d50001c0503005001c01640581714031726413440b000e0054210b80e412640003061000a40e40f080f01a00c5106182c1d914258100c04c0550f000303012050b04010401c40c00b406a0f1106030700883c4111490b14181d680c1c0c00248030441d044800340e4000045c0c04542c51204914464507140c0541110440c0d0800045a00140600c00040c000b0491480d100041010010604160b4040079142030895400340018a4032002610500750000002401e1815001052074010710000c2e00302e03101503403c0d090030541003407072804500f03d105290 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 995170134 1250 995168884 995168887
    0x717090d0309060e1e01110316060e250b0a0e04060b0d0b0604270603060c05120f06011b030c05030a180b09030a020603040606080d0306090c0f090605070503 69
    0xa04a440d5042589100c500035100c5480491034070f00040d004240140080e8441c804e03849811115161082d81c140f81c1d20030a291602c0000038501c0307914503601c60303100660b145040110100040184941042c92220a18025281c5001c05180725102c0b150701d40d00402011401e44205002c44d248244c00380c02940400d240c0582150141808282240d2075a0840c0c0814000001e02d0403844407a0300554049060944100303281620b0016040c40302c01c80d203603010b694410181c2c1c649001100301c0e00702c84051a0009803c00c050b034403040d000b400303a034800004420425025000603038007154070014903210f4041a12002003200c448071102c0f1450381c44000403001c0c891900c01c40d03004980104080e0842c41d8498644114010045800061250345603100400404080201007080d440109100c060a40d05842071522600c031407500101030b0030030360001400c070310031484c5490350301d645600300804071482c0c09010046102c100b01c040310200c03920500b01001c140e0120007004039520503c010170b4000c1c002c8007501d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 995171384 1250 995170134 995170147
    0x70f0801050f0f250e040b0d0308130609020a15081003050d050f0c0708210c0703030c02030f060901090b0f1b0315041802010305010509010e04080f0c010905010912020c03030717 78
    0x2c1010b03281d12000000f00d8554000c5d2050800f44113038500e240d404c0355049828910f07658014508003001749541d105481c0e52025004010284c0c022118955008004035116900d810002480c144002c0e15200042e5213003011840c1ea0080a15140c2981d4024010302000400300b2403d031540d5008510788040400c0c1082515032aa0040c40006c0c007400703120002d80911440c101c11a819035000b1101085d1441341045140c500020000b0020f040300e03410b05100540762a10b000103418584c4040001d040d9004010400000b001e041d032086200501c5542401c0d1141c60384071806400007000c40d06140c41c241840c41c080e04c1c001007138000d140d20100703d4103074814024041e40418180da841100e418451102c0c0c080000440d81c0600901c3c0c003604083e51f200005624251007081d0111014001824003040004c001c81c01e10a0b04044030f5039050700d10000c1c000c08101e86011402400c0440f0280d41070441d03140202507061004c590070480060040046050000640f6040b0003000c2400c014400c84008100c003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 995172634 1250 995171384 995171431
    0xa0509030607080105030f012c15090a021509010f08062103030f150102031e120c07230d0e0a1208070c061e030e0703080309070f0801050f0f 62
    0xa040c45111940c2d14040f56515080a1614005142c00750003074507410b0a5106254500e1030412031485040007100401145151101d9400d02d203e80210604242c0c0d403e00300400c0050010f451240340e4426950614640c0322a602c9000c9400b60070030084c0001c0050307199411240c418070580360403402c0105410501c155a10980d14160700286c4081d6054101000f040206040c1030215680710103440c14464107806d0b4000001d44070300c92150440e100465a2000c0516020007005544040214406a41c15810b181c110346031550080c3d0b00482c0c00034510310078000e41c040c19980c3d22004411510050284140c540b0b003c0c0d58680d9641c40d80c9400c0340c21800300090300c2503000241401640500800c83ea10203845c14102c800005a81102c07041c00200118440d03100c10114411440702c109180004000d643c071403000c0d091511aa0026200314004000c2c010104d50200710481150362402c3e05120107030362402c426080c1d0b0012036a0b825100c95150020b04400c0c0c014400d02c0d032017a211a0321700b0500c03079603044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 995173884 1250 995172634 995172643
    0x3021305132301050d0807060f151410020309130f0203040f0b01090b0603060d0305120907090606031509020307050403060f0209010f0203090a03080a0e0607060b0301051018020a050903 81
    0x4410708480d207038404440d20140c0800020341031804011086560b604043c0072820024642d0801031403054001080810300100741e000502300c0d00b8540c800e0080310b44120403c10850700c42e00aa800700d03c40c1171407c4500b8907051113014202c806a030041c50a0200c07500400100c100c0400070740038040c2d11101303011920140c920056203d11b20410034412030945901704074a000700140c001401c01403500300c1c0c550041d85c500341580d40c00442129800d0032340c2c29504d811945402203607050b106410700e00d01400080b4102140c05025540c040400f04071541e95410200c040d9801c0000b40703c2207500c1c0d5002401903d00715001941c0c41915410300030320b05641c0e5912082140c444002610005501003999640c1c3d6034816604440045184001c60410311070740000781940803244001086400001a1000101e010b80444103448100a0440d03490f490581800b6018003645a01284294078000000c0d1403100d1446600096030b140b11010b00741442c2c3d03444814003d5100341c00c10000d01c90144650b48a45d80d0800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 995175134 1250 995173884 995173909
    0xf01151103270a080601120606030506190e030f04030807030507080a110705010f170907050a08070312020325030c060905012027060c0a140d0c08070303021305 70
    0x350780a0b140c000b409405160079400300c034094400c2294103000c120114001482034103440c1100c03255001c400042c82c00740700614030399000900c60b0240004000b01040401180051000081d80078012529041c072141d84901c05c80040c4400b01e00240018000b00d2103400203403080078441d040842c9048500c1d02c5080c881c0c1c006a182d0000580c120705040310380c0405100540c0207000a003440862010240005070401d000e64040d14002e0100c8800545a404200300c51002044043c005c4030a4507101c030b295035125406070105944072003500003000c0200c0e00c0081240c0d41140c5140d004400c0010620f004110181c0c5064140c0821031705c4510390700410000d02c20400c01c0ca214500020300010409c6070f91150307005000340c402820100340102d146030510001750310319010004140260150700136000815a014464820120340f0960b401c82c0d00300410341041c00c040714400000c4800001c0468401c41ea4100446002401040d06014001c0001d019801410039101048006010f0319141c0021800c02103050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 995176384 1250 995175134 995175157
    0x151c02190e10060807050405040b181807080a1a0702010e030415031b08161b0515150a03080c0f0f01290f300a03080c030f01151103 58
    0x2001030000c5182c1841860b4018060760621082e1840d180304050b203240100e120311303805a03403600505550b954524014000400d4504003142d91418495003d004c2e40480b0f40c030180b03c40c807070404045141200000c11080c040e074800c03400c258902040150400f280400740074907007590348900c031000310803500b400684080c1c60004000780d244908600001c054995a501c40c00e074005040c0354180907164800700e804c0c1c0c000c0301c0c40c916070b12800c44840100e401503140140c014002446c3d4811100f0071001180f2041d0807401d07030100315080e0729400f074a826558050a5500c1d03208140c1e0100b0400a00c0704005080e8034202c6105603091a0721440a26007001c21350344c4886d580ba50b4034800e101169507810b64034030646801d03e2050b40310b00c08440220b4040c5802402c80c80c0b240d4010030440c2c2442c007941070143c00020503242076100e049040400c1a5585c1c01c0d602d41200803c1c94440080c1d55803822000b52482a205403400284503403030000340345980c18080e4815010084101e51042c00b0700c01c100000e10141500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 995177634 1250 995176384 995176409
    0x30513030c080c040f02030f0c0a02070801140f0f09031c060b13030c06020307150e01020f0c061e13020904020310021c0c0507030504061b020d0308070206151c0219 72
    0x402042004588050002c10700040c811f0062084d1000d00208441d4881840d00c0c0c01d6654240b134003c1603140c402654810301d155070030210404990700413280c3c00e501451212b213840d00390307403117080d9441e02c101812143d0f070360b042d4420701c09040c102e03c2c1810400c00c2003012071000070307566032250301000c000c0d4049008010f42d06415001041000f03000501c41c40200390910195041034641c0ea12880c44010484c050f800c255210404030075901c000b03604850810b045800312590315006041e0140c0c850000300d50901001c2440d403420002a42082030701761141d03030f01094800d00e007160b070741c01c004040e00d0141090746c0621488001070780800c410b06c000c0144c03060096081103200698282401030380c074000440c8081240c14040040041e800000b41c074140c2e400d5042080081441b094a40308140e10800c01942c0664081e18840600d40c003c91603600a80c4103a00751001780d41c9030030401403095a0051030380d412040802d250030b01242880c21b80a00c0f9407000705608100c80d51803100c0c1d4180321494100d403650301d40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 995178884 1250 995177634 995177653
    0x3090a06180303030e07050a0f080f06010e040b0709031e0506011a190201091205030f07030501031203020a030f050928030806100201140109020a17040f030513030c08 73
    0x42045144004011500c0d1a010704031409200c04814040d51100078141902c0e0b482030035400000b8400700c1c0c040e0801422591003a555150015192121440b0343c40882c0a00f0383c041c001200c000c2070460684140e08103000c0c1070b4403999120a843c00c0b004120320104045000701000048407042020600d4680c0141c00c903084c225401c001d400c0210680c00481c0c0c207044250b1564000940c142566240d4050504a02e920001c000c4264003500b103600004008140c100f82c018005904900030310700504908031441d46550300d04600340e040305d01c00c1c007000d0201c59065203c0c0302e016109800421810b001e078640032416660078402101951070030748412405402581d20003030301d02d00b084003d180d0040c6d01120f11020b9521910007622201e000b0300090701035038050280900b0b03503000f500108468018010103011640e0354000c3d0200940100390758030001020889a142040301c40e0070118081e40d0041224612001c4540d02036415900020a6440c00e40c070303d540000219070302c0d400070001800804042c00344090f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 995180134 1250 995178884 995178889
    0xd050103030905121b0d02220c0e010302090a05040209010c021e03010b0303132c0f01050102070b1c05041b090209010e010c0302061504020f040b130501110307060504080412050309 79
    0x700b0b8503840403590b500c0443e0101481440740c0018005c0f10080c1e8000040710a60300203d90400103182e600e60729081003c9010000e11101c0c0c2c0951448c01165070f0b42c40d100c27019030004405911a040318203910448601c014022480c050b4004c01c10500141002034521045a000c103030351581d820031b42441501e00b101180322900b400e02500740d400c0c004401862a00e04403807142c040850310303030280d10010302808844480540c0d10801810a030801440ca0307061500e025849402441400d000d071034014060340500240e40c00d4050256465401010302106161814407966001000c00420546052140d11070404000c20164400300180c110108056030381e9043c0c00000d424070700003854160400020303400d0000441d50116081d50080080101f034030030301c0f00200018000e170103140780d81c000600c0001000281038000710020000450070f0031518100da5035840c01136409015031900302030150010001d501c00a40b440d40400da120384910301c1c00d810280c440101d50003007070000404071090391001890441a2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 995181384 1250 995180134 995180149
    0x1e0f010e0a05120301120b0705210a0c0f23093c09060919020a2304030506070513030c0e07200d030c0509041a1e060307050901050d050103030905 64
    0x203070f803040802031540d45007019100c0c0030107401901074031007848940030801030341c0b00394112403221140c6010720803410854241c0c00d42d80c0000f44d800052062600c01c0465116001c1c921002ea4a0455215010803200804280780c0e000700a078480300048008200f0502980d86800d109001504a00c0c40c0c48481110003210920200e505e55011210192010a4601541c2d030040b495034171003010f80c2e06142c1c9032510500802e5000c3d000c1035440a003800411511052a801100203409043c100300501c004405071218020f03d00c6240009481c40d0085400074900c80d0003600104a2401d0016840000641ea615491002c08140c0c1101d1b81c541001d07014000700d642d114600c400c0d030952140c0c2442c041803844100310342e26103602d407110050540720616540c1642c00344050742c0c0481ca001c1c005000c84040c140320090817801c0110000e20942c0408452100000e940303030599100c2c64054060342c07840c0c1320517400b59117582206842c0750420134104000948ac002c0d50180d0760007188641c403a40c21040c200300410062 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 995182634 1250 995181384 995181403
    0x30a020f070b090f031011030702070911040e090a08030a0605131b0f050403051005010317030708040201080c19120c02030a020309041109031509070501111e0f010e0a05 74
    0x980d1050509000b0704250800321404044103e94103800005224042414001185010340741c44d0329000f0400440740101c80150f10034113003030b826a0215510b4035200303801c440c02e241143d821818148802d1248050405200d40c00c60750007800ca8861545030313030340c0c1c152a602c200c1e0410741668540368100b02c141081c500e10318a0100b00c91040c0400e000103003011074480320305090b400800201402810740c0d80d000d40304941c0690b0f0000141d5003060410300c0c06101a0100384400c0303910120080075910001c0c0340308280c1c0d0164034140e80350b801036150344e001118016400340035003c2e01d150400120001418480d07800000182c0d0762100844110000b03c5181142d00e254601e80954008220000045501002300c030388101003103400290403079000900800c03901412510341e405108030035034240080583c4590b103104403246412140c42649900c011508141052038411703490384107800b0842001d04031503002031f0000100040b1400380d10503030159402d450392446190403e8114075401c2052110510036330780c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 995183884 1250 995182634 995182663
    0x9030904051005130f0b030d020c1e060a270801090c050301020f0d0f0f02270d0b281a01030f181205041805340e0f1002030a02 56
    0x8420b1034040071803000f40c0302c0300800342d070b845d03480082003001a4030303920032142d584001d001c84d407905900050180da40c130322400d40c81d8414142c0f414114810003a1060040110718094903940c02e001c040b107400d40f0002d9410300044603801307651040940d00d9101402150013007656400200d14489241040c0a0581d4141c100760b0099004200a0034810f00704002c5a26110701001c000a0f0f584140601c00001d0041068070211140009038503000500c03281e8844014179400302260a0142c500420130901c004688402440c50358411300165400c4007141c012800c2c42250400c01440d43e03860503050301120304803841128189200405c4c46c0441d603051050310b03034128400f4010000d000d514806222245005c080080c1030014111480e0a0b0610500a6800821000b40d0300c00380c0c401074860500c00307001d0494200c03031600840200496891042c0c20030040c034041011900d402041c080104581c0d2114036905981c101003040b0107010f0a48030500010001c440e5603020719111042c0502c000d0401030318001070031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 995185134 1250 995183884 995183911
    0x8041a07060e151501050702061b0709021e090d02191802040317070f12020106141906050f0f1603030e0f0d051c0207030906080112030903020607020a0308030903090405 74
    0x606040f0b0340c20080c2c1014000643d03140c0b0103210401299140308080c0000d42010001c039485101d0354208a45d284076903000b6040c4d418003500c40b41c00c04e04070300900c00c004101140350702c0c54071051100400180880382018004004082094012424100450181d040b440b002c000c410403c01c11102c00700305409d889031105529107072640d02d801c050000004003008082600098003001c0010000004e0940d07a84a6002c020000c0c4820001e0700a141c1c40c800d8104036220410600c825280568440b000001d141c0c4003210102c1c204001161507070080c003903101d50302c14200414041a820040981580300e200e6441420200f07440c80c2c010103880faa2404260240c1c411080c00c4030740d0a0126940300300342c4c05840d080342c54000851011022005130755020006a00c00101d010a059004503030706c040d100c0c20380b91114140d0703888101c852030209241d409000941035010510040c68094018048036000074070f080c0752241c03280c030341e04403a50081d110000f842c0d200043c240301034217041c05080d51000c820b45002c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 995186384 1250 995185134 995185153
    0x90b06040f0905060103110d050f01061d01030302031803031b1b03010b062502040516020120040311031c21050f0406200f070b0a06050604060c08041a07060e 69
    0x110360b20303201030000a0052131649507c414640317540c203c0c2e0001075040001c4940039404600b4050081119014508a002202c440500300b401c151003603e0480383c2c103900440c5000405203000c1010880b40d42c4440d411701003040710203e41030301060040c2030000b080c009440c0020a03000101540103e000d8064001d1341004c01a151a54400055840c05411201c1c0071134103121012144000203072034080290f010303107890180404018101001c031490801c0f0b800820603200440002180c09a0041d03882411040c10002800001c54054042d40743c003301400710341d18980607c040c1e448039100840e40900040b100d18102d00e4000c0e45054603840309403007110802290601207500700d525040108040e0245456201843d07100003e8090a840103480c0450b8948503007080400001950111000761000000440491081d80d40c600c00c4004480008162070714252420340700390b989a15441e42038a0056080c880001c8140810704031a40c903620003c4160380d01d0010385003031012512038529030040d80e803005000303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 995187634 1250 995186384 995186393
    0x901091805341a0313120914012c030f01021b0d0309081803150702010c090e010b0409051f1511061e0a020705190204050f04150c03020d090b06040f09 66
    0x1030a400d0340035a000c2e55941e070754070b005c00001c90348001c20007402d40b001030303210500d1260300c46050019600f5480e207520540e104030b8011100c2c0044400c140315568401070324415055100200f80d860b043c07026054440b1401510707203003800ca80064591096000002c1d410b010f80710f2040c048091100100d0a08218405c0340d074070385200d0b50240303030702450804c1120180600d441c0d07000c00203000c0d280180700261846240000009010340680c400f4200413440603c008219404424404c1e4140d0306400155030500707242005c1900900b0300904180a0301110000d58140760900744680c101034805240c510780c034601e008100510182c1480c180c41500c0c0c100c4800c0c030804800709844240802c031401005110390310350b1a0840000c2c8036911004105101e81c6007181038645040f03140c410750314000c860421650340c810030400012403049400038040084021221590b494662110240c0c501510300103040c14080050102200d4004034240c1340c0101c1e580401c50a880c290155040040d001c20080c840e80000f03585 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 995188884 1250 995187634 995187659
    0x70506222c01181104090207030e0f10080f150a080c13140714090a090e06060108040f0308130b0f180705130203040812010e01080c010509090109180534 67
    0x2c1a40704192149013441080032010242d5020786a4100d04541e655040d00e005425014100c030154001d103114091003916140c1f1301c3c0c024040f082e1686410360280e23210390011509600050000350150104244d5140c1c0d92038007002e1034017401c0602c00800301d0840f01300c2003060105d1040c2c001800281869120f192004810300b44e035400c142107050540e200c014158404955001e440521500100007210001e082002c41d000150b61145940560302c1d19103455004450222084a024003070701d050b28101d0002904c1261016442016403203101c1c00b0244a56070500c0c00c0400765000c9002e9a5040180200300c02c204d10f1620301d80205038020281546800702280c3c03150901c0320013043c4160702000240030300840404655284400c00d404408a6846a034400300d440e00a00480b1200e1081144408140d4014821079100d40b030020410301c000c1c0e1070180d280d0081c1252840080381c10408085440c0007403000c00c540d00880701d0700001084408008007818a0354005080b012080702100f0004105041c0c15a8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 995190134 1250 995188884 995188919
    0x60301051501080721230105030a0813090f0207110a050906010c030915051309020306060403060c020a020d03030c020d08060a0e1308041206050117070506222c01 71
    0x244542c03a40c0d0380a805075841740b130b080e218100194500400442c0c4038110760000d044040091207046140b03074048190200d07804240a125016842003080c00045150072024180c04280b03074149102c06a2034800742d1060307a0b1402d000c12081a008100c00040204011050150b84400d4600c429a680b400001542c0b0b550b003c0c00560511000c010b0354018275104e030483e400038000c040c0d00c4040851050300000c020740d010501d036110b52142504c01207401061402103e0003010300500c2c4a0405086403603c40061482d000080103520400b00740400503120080c018034614081e440015080b0017403c0c0c00f9082030728402c10034007003050341c9042041c20340e528862001903650366101d1150035900c90112018600d8a4480a0040d420100380002c41c80d44400750900f440f48691001d00480e42d80d5802e004140031070706400b8290760001d400900881c01e0500c0a00001409402120541d56126111680180c01900500c1e00c90292010701f0000400c11007a0030701243c06240f140603550b14080c4e00c0101c904805 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 995191384 1250 995190134 995190137
    0x20f0103021b12190f0f030f18060f05150312130f1502010f053904180c0e011e090e010e0601020d050408030913091e0b060301051501 59
    0x10500c2400103028542d0341d803089020008035000d03084880c6440c055900030120f00c1031141d07555442c420003588503814410401c41243c4594190045403d4141c0c054007a603189890141d5855208d20001070340c003900300803404e01800700016a448960f4140d801e80300018440b550b076100c0a14a600c1c20381300001c11241002075481480c0d00d81c0015001035140d6041030344048240345001002142d411b4007481c11044080180d0000c00046104100c40030070f849003110418013803050380d2017440a80042001541d0034100900c9000c80700c01106108641c0350300700340c100551004288103903407078a0782c051241c4549407959007005d0314090f0b0141e00003040d64401c0f80c55505a94414007011304407601615004020703041200b2102070035a1106820030307070300c50203e030610b00500c1000c00450032035000700d08450075602014051b514207840c01081c8020f103241d0080b100310740b640e02c00611000c00c0c003000401c0c86151401211590200550624440c1180040d010358400c3c3d141030280558040b8440042240c400203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 995192634 1250 995191384 995191387
    0xc0a0e0412021f09110f010f08100503011b08090a02280e1e0f04023001020706090519080d11040305010e01061a0c03160503120106021f0501030c0506031906090203070801080a020f010302 82
    0x903d6090ad4683c4996488290158200307559001031001040304c001c0341c1c044035074072652903a40c0c2000d074540e14100007201030341100d198490001009895a95608881d11140820840580d1380d10404021003084030403115008a0f00600b02d181c030380100b0150703003069071554052040c2c102074002030710780f940b034660200c00d041030302c3d02008001c0d01080080e100309101d03100841d141c040d10b003000b0700944045502180c40d07004403d08015904e4161040c0500d045c0c015140307074184411180d0140040030f00180c0910702c00340501c40080042c8007405040508424480085851440d00c1d003032116202c1d049100154100042c8401e040d81e440010a0b00c05006e5041094005250345081103419807080300c010300c84100710320001042c2c3c02d40010b43ca03107131000a40390342c9a0622883c00400100c502c02c0c0002461341402e104108101d1030990060b64126100800402c82605030151120441d40c00f80c0c0885485900030040181450300160600e00600202c000740c110022281d002401d030f462115040c41c14190b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 995193884 1250 995192634 995192641
    0x10c02030f0d1812090e0c0c060a0e010b0d080a0e030609030d02130308030a05040b07050a0503040209100e090c090606090904120e210c0a0e0412021f09110f010f08 72
    0x4100c104000902c0d00105000b806003004c0350010544949405400155a85400424080c124a40032a50400f5000028054984500f24180301425840d990581159281c245000780e45d0b0311b8582c050250361142001541c5ca28120501a111003000c190b158440d402078400c00810302c002000721444500b03200310040e60384003600081c202c1c41c10700b0381000c0d001c00b4000c8100601112184e10060096006100880a0b559006021142c5114600c801c50006000380f0100d40181441c200c5560005040e4464450072a1100005106020100d86208a6500421903603403182421a02d20381c10550039200685402c2400b80400c1c4504805000113042d00c030000710540c03400e842007068445005000b041405541c0c403c05a1031040d440310402c1c50076901541c0030300d103028a40b041a510440303155000e03c1c80740ea41da60b151a10b00c690310141d5501075014441800341c04010940781c40f816911b40a20003d0401d17040d003031644264006642c0c050040c42c40b4240700201c0c0c3c0e00512100311801d40c52030008041c4d039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 995195134 1250 995193884 995193911
    0xc040f050f040b190204060210050108010c2724171b0c0a12120f0605031504081225030603081c06120807170a0e0906120a0c08010c02030f0d 62
    0x83d000c9583c0007880c5c804503010031110360201e450400c85451601c00c0c00039980b031351242801c82c0c82403908200072451049900001c00c1440f034806000d1030010403255010f0390b17114003290046800a41400c521002070090342012500514190366104501c11342207840d00d0320071090420f41030001c40c1602082d802141d90006544c0c10000e4100701c642c4003882c0003500004000c040c0401805042d0900240e080000b080d04c40f01492292000b201c400500428940403ca1139140b064031001d0810f580c0b14204104251442c2002c20500d4040c0d80350000200c083c07a1100c0e003884040c580c44d01c0120805091000410102c0e2400c41510506040307581080e003203028180341100181007070707800304c2591811207100c5801d11041c00090581540209402240310260910089441c46070321640f20204112039008021803c00341842c42e0310140240003c3c44005415403150b1500303441110840c1c070100c55150500c107014080c06140090180760000b10300786010711490b14000c2c00703409103d186142c0c1c0d174101480c0c543e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 995196384 1250 995195134 995195161
    0x406031e3b0a0605092802010302070f1a180a050a1b0911090906031f020702061213031d0f060a0203070804060503011d04030215090304080f0c040f050f040b 69
    0x620340c1011150903003181c3c40c0040c00344c002220448002e00941d081060203520f59034041c01c02c030300c100700081414a201c0e0b0043d00290413041050700d14003008007501000401c0b0030410850291060180205442d00b06007129418403129000001508804c0040c0c00040c8001414080c16502881442031002d01d90000c09000019910940510341003003032101d40e20120030002d00b503c920603030340d15880d50384050a0503518042ea0000c03405610720b80300742901007007207030340035100580c4000d0002d0302d040803140d95007044150640e2107403013004961041d8420507800c1310755019080003034800d1807010100000010850700d0212030140c002c0b200000c488aa06c0c2c404d0040f52001d40d88000c030f1035243e81e103926000309181c10034001d18007510301c012400600390340100d41ca18800c5034103900800c4026000c3c0c1465000d03241c046c10398800d074442440081020300040c0200111070f140b4000901803c9e90040801080c4d8a000b1112079076a80b4100a000c2254119541640c1c4a900030050402c0d0ba111a03110a048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 995197634 1250 995196384 995196491
    0xb1c020f0d020304020a171c02100c080601080a06140904050f0a0b1905010f0b0c0c03120a0e04050103020108010e0415150312020606060a030c020c04020406031e 71
    0x221a000581911420030780e9001c0e50185000f52240c1420544400340088102c072640c0c0820320551003000610a180b201320000e0318404d961303205490800f64a0305044003541c00904078400820f04c404104600d650740040700c5a88914a076500788a07407464010281c25443d0f0003c04107000c0c059880c001008c0c031600b08007400a4401000440d5601d42036410f2001000d0429a14503408218114003461700038024080c05050f100004009520107190006070400c2d60b02803c118801c5006854400389180d4061081c00e0480b0b641d241084e5850000c150000c1402c00081c120b68400c910f172800620243c0d03480f0603418150b4204101900c607945070360600070b80c15040c40b0441c170f441d01d043c0000c0c030280d403044203030400c100c0b0321840c040d1814903060765050340c071000f04481c0350390800424803440100340e2003508031407800c90450040d02e103c9040300c4040340a07a442074020030040398864203d502407004500041d40010100b4001f00300b030040040c010000e217450804010032403105581d02507a1840c460500d95003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 995198884 1250 995197634 995197657
    0x90306050604051b1818180a02062b110a030605030a080a03020a05070c081507110c061c050c0c07120507180b0d060b030f0c0901031202010b06040602011407090b1c02 73
    0x10301401c4000284481341e00f16008550545406900c1a01b1a1f000807401d18183e4010519030400480300d003010850048511505203100042440081c00b004504c5840750800012500c1da80d640c40d50500036081d14502c2d40024000c0c2d115045140201d1610320695072008003074035001d662602d0036541101e4034044c40c40c001d014022115000154004001003001d0340011300d540c03c40003039031110300035610002d21446551507604490790042c100d2400c040284441d12114103904000618001d6146c110740d03085030391410134400004e02c003000c11800c114207401800744c0f5280b040c8103c10365035010f8a860f0b840c4900c88281e079003c148c0c82101e074200d0701b1900f12074001600c102c4c000301487c00d120f000341c40104400ca00074050300580c04480b450200790703c03508620240080042d64610740da1300b510061800a981c0455685d4070510086076100c0d00103000914840e17001041d00240040030140b10b41e00a0181c0f03003409803000040083c8180c27002501c900f6040c1a00380401c0c00300302005007001c9d1162084040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 995200134 1250 995198884 995198899
    0x305090a20010918020703031a1e2d0f0d0507140d020d1101030b1f0c0809030106031a0c16020111010b03060c0403051006380406090306050604051b18 66
    0x4d00b5005079400f800030300c0c6c0070799001d018580d569510006a0403442e4a01c6810982c010f0b0b055150343c7d80c0c94103500c6880c1c40902814952120450203c01060425619408100b5013070506807245c50a1202d25411174401c1704c604004000613035440e5034591803845600da8410a62040303c10585d01c1d03d00c2d1960042e000b1700042100811490800041c2d60142c80a0340803902d0480218028107107006446c08014440e440c1c10728016482c20251038602100104586c860340c10003c8142d151001e005507002140310300104000540103119000c1301c0c10001301000140794040c0700140c02c1d42c030105441564142c0a08251f044201c699030b445001d006210b038640c0c2c2510824081c07240300c04440005104a034020303016078120011000038042915400d104e0000480017030320f81010390401c000e0f1f6010700411030303d0f0000110905128a111150000da0100010a0200d1010014040c0034051181d028008540410482c9045190801d0303030405106d1042d941c480200e604900400d241103100e6407240014441c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 995201384 1250 995200134 995200169
    0x6051f0b0a17092e1b140702042019030b0f060a020f012a0c170c0f060c0307030612020a09151a2809180f020c010c0305090a200109 58
    0x100480034140c16696135407840c20464502600c0f000313a41360389250442c0c0d20400005000c21500d0002c0c3c0080405992003035403415000340f82007030001ca01805203440c543c1140c80701c0080811800c40e0007100c02c0c0c1000c1c507040023121002c641d250281202c0071542280c0183e1102c80b00e490403483c1c2080d6280b1000c580d8039048850300c000c21558000c1d6401540d0480380340301600108000c64a4134036007403000b06586418080c444c0a4090300000d842419a0710080b11945034440e981c0c14074240d410b9604914030a000024032180c641d00d4010032001c1c0c22140e0350f40c1c421001a501089511003d0b105119800760303500d0988902142c3c0e004804028105034042c610800b501968070f50542d0700c0607402d81c0081d242c084031100701003801c1d40d03a550b1821980c0c0784d2000c1140b40c0000c0210302481310844580320366a0f50120043d03481f080c8040c0c4130602c02040006031265065801904403500500742a50a0303010070b101e10000781c01001d0f460b514840480344040c43e40301c10070041c0d8000350903411040d00300c611070800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 995202634 1250 995201384 995201443
    0x4021201031209242d030f0e0307020108150a031b0906050303180301020f030f180601051e03071502030d0c0f050a0c0f06051f0b0a1709 60
    0x14581aa03014082d01c2002c2c0b550103500340d42003116407080041450540c946298032a6800403460f41030055400d20188201c04c154600c0d464192800d099504e40c1e0400d400fa032041907040c880c1d00302d01d0005a4040044500300c0d0b0500d551390141c504000c0c100903070340340020321101400c5c140b600882d2010f0090070742e99480345001c4840f110340c0b103031030404941d0031100010100c3c0240551011144041d000e589411680c1010340e038103004002040307800d59000c215084045940c00d00a505c26074200c0b510030180d04003036a0100301c0e0b203803607501846140d001c80c0042c07210f80c0e581c480504082c284400200203000401c00424201042c90b0b1064112841d0746800c1410245c02000400402c03107901c90802805103409020343d10010f41c070172080c00048040c40001c1e512802a40e03401c030f003640148005640c0c825699603800c03e844003203d0614030700c0e6020200581c5c007501c03c0450b2018024410300f03142000d030100b50007042c458448240c3d06907810640702080820500340403031502e03100703548541002d50b092200b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 995203884 1250 995202634 995202667
    0x527060d09060b040603120503130b0a0207030f08061c0230060112031403041506140a141305061212040f060503072001020c030c010504020312040e01031707020402 72
    0x101900e2503803c0100d00d032424501442082c041e20340c0420703460b81c009084002110560001081d5103140d00c0790703110502c00300c1d203d900d02c3d510420035024056070310311031450700411580702030521800340001e1105218681c3d4070100000311202031004084240310607070002400ca40e4010781c1030180080102e070318001c00040c810000380c070400d0302d1085070b400f6682d034100007801440020024001500d8089010800001500110b41007401500714140c94541c41540c0c100311000c59021022100360018905000e051100c1d4920050900c50f00e103c880034030382404030b080c4401c1d200300144a06d6072040042c40701c0e61a4400d294082c81c1c4241100c200102202041509900c80c1c0902244108514000544944103e048a2240c90341d542c0300446aa0982c003000d8042d410700741900c00d25502070040f640807801c00c0000c1c20781c00c41004004070346801c03e0300505080c40091101c070311400400300b10038000084407180c4a41101c1d0b01c120202d80507e000c1010713104601690340c000f50700c1800002c0c4580032805041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 995205134 1250 995203884 995203901
    0x902091507080a23030c0702010c061a0a060e01080a02091906030501030512040b0a0f140f04260d0f030b0d0501050615030603070504110c150f010801020403030527060d 74
    0x440e103d40d1a01d480b5981010008000c9010314545801c2000134400041b410280840034418104045147d090703698210603640e81d84012440e900c2c0510b400152403030b140c01180b00400140c1849488601e02000090510000600888002c3c1d00018040c0a98a5202e407040c07141c2d2542802c0844541c03500c60040203060207100c292850301c250711088003d101c51608407001c035900c01280d50700c0e0140301c4c042a54003280703407401402408a503501e850b1124100300d0007440b64003056505603a44909026000c0e48808001d1400b42856801d580303042080c0d20300041e00031070f0700000d04008400c0e6102c0c880c12005810303213881080e0401035152040e420840c054000c1401000101ea0b1408420008020069107010032242581e0503803011204210908003544000d0f03020b8041c201140c9403412026407140b6069030000000001c001c08000c01042e0b010644030307140900205002589054510f0720014000e0060011040c1c4a40c20700c11088240004201c814410b103c01502c01c81d200c811000600d4010072041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 995206384 1250 995205134 995205137
    0x61c060e1b0a0806010c1104110d050a06030c06180521010f0507050409090c051005030702070609050105180d0606080f10180f03210501050a05040905070902091507080a 74
    0x5030410301c091401c01c0c00341c40d40c0340c641d0341d07602d000313030740c60100443d03c25031b403420207440001139900074409a0b10385024664050403245440d5540e0b175898114413007117600040c90700d81520f1802030248001041845901e04440b41841c20b4691500308a4003c0b071b4100c0503138451580030380c8100e80c00b9410f01c8000340c40d120300c041603002040628140d60080e0141d9508032420320028004010034030101c42c1c1070b0f0003c403c540c019000650f4113500c1d24045500c0954061049021034000704c2000501941001030b01c01908030341c030f803035006d86180c90006002c5028941102c02c3d0303003d0003400c0001e2130f241c0001c1c10024980080080c01040d40e01e2002d552980380750200c02501d4090460907031012112401650650704e5001301a16011940740c4601400703804003401141000380d14081f48003618402e11101c00804250100021030354580310400c4400961580864001c0b03041c0408000030580209004085402200000d84e50710602c81c001076140e00500320002a004021803604140204180a0940d2038101e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 995207634 1250 995206384 995206411
    0x60a0c021605010315030501090c1a160323070c1701020c100c03150e0f070c05030d0c02030c07060305060a050f0a15121103041b050f061c060e 63
    0x5510200c1c0c8481c0340407148004075064010030881948030b640300581600d41c0942c102a0745d03480742d03945400c4d41c9440038103441d80e0400a405010314120058108403010302c919469141c1031840201c10070051420340c2c05418007000280b440002c0d000398004601003c80c81e41000c0d40d6401c00d24048104078610700403010a00d460100d0500309120510840c2c0303c10f03005200410b8240181000c1d02c3c09070200c0b940031005c05803600420054110804400d1000c1d0803250300c1c100356464004254955400010305100400c0b09100c11080851004000c03a5054600101c0c040713501448060f0503071a42c442c443d41c4001610610350700240c071651680c00940201c004468100b0b0031075554081090840e40c00010030342c07014410100f0001c0050609010356000039a00380510b041c0e000003c0d0b00b0841340d0141040568010010400007041550084000c40406030710501d5031803410b05c408203080602c000500c0e401184006450b00000c10340916048035100c03d01014004103440f84440b40704448107940c0e88544001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 995208884 1250 995207634 995207651
    0x30a0f1e150b010e210316150c0801050a0b090d080307021e0c011e1b0b0106030c2a0f02040509070e010b03090c101808061902130b07080c0708060a 65
    0x1c03541c560714103104c000744100c02032105d030703c2050000140a000c80d4542c0c803040005c0c6100c170650044258015005400e144035400d40300c200ca034181c4160144190411441c0001440360781e8a05c0c4644041e80c00c2031140703e4540b20480b010440c0340c20202e0007e0601000030042042c52507000415000841c41250075021042907001c400c1e0342c680060708001d000c14605c1030b000300e400022102140380072030b4915010942c20840c0088288072507074071500ba1504907400c001800403c0d010301401410070064074095006181c04011951240d40c1030032411300c500f10807402cac1c23018080c0e00c410f01c0c000301d60020310070069414006a0259204000e01c2040b2609000100000c0d01c030440809417841002190701900c0501d040c601004100d40741a4403072801c1c0100109040070821807140f04030301602c0980001c00c030390f007000c04181c200c141d00c640c001300b541401045503604c0c00e11204045000c441204004c41d448150f18541003101d8041c42618170a103225400001819840006801c0e00900882d4410002081d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 995210134 1250 995208884 995208887
    0x9031e150103020d08031e09060a1413030813140102070c0b0a0e010806011b0b090f070f1206061d0604050c0705060f07050c010204170d080105030a0f1e150b01 70
    0x103a0910000c3c0d405203ca00d0b03880081000003000790380c030010030f002c02d82008004001f80b540455055500812035400b0400308607182c540c91050308500c107260382e02d55080d803411341d01c4001d44801c0c0910003070812000c000071840b010b54040300c01851542c0008040c9240010590181c002d40100c1400d85040200d0f4000003a1003c1c0c21080341d06c03805150743e0b600980515107005640380e410242141d4100241c846c0c903c0340c091404030500c0d003d5031158040c90900c5c00d000b80d00314070301011141c2e00001c0d50042c000030071046940e01d40c64401c9590b014030014281d411428a00c0007003800350301c00c3c8003482d441d501c484440c2043d2490244101011a800c01041c3c1701d940c0c404819000c2c2c0d01d80103085a0100012400c2d0301913250030240d000c2c040745000c52030300c10b0141c45642a038020364094608955040e40c1c41e0b00e05001072004140c44000d03480c2006540d850480041da640c00418406440e90707000d44940c400340001e00048003420783d0741c0c10b02c4a4003c581c0e4600641144004c40e4610500d6241100356410317503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 995211384 1250 995210134 995210173
    0x6010f2a170a0801090b0d0204051e010807060f08060310090b19060f05012f1b0303190c051203100518151210050726071b0809031e 58
    0x80324540d64000c02d42c1c240700b1200d004001b01141c959000c09406188001683d4a010b12485029008100003110b84280d501c1800c2072010703003010042c4d400c400c00901c20558040841d010f544078604d81982c00340c0355180802e09005940b59510030880c101484001400030bc400c540e4060b8002c07440b001d2038520003555150840f4084d000e0f4941c07012540c1820002903100700400c8980817030745e4000354041119000248181c1030200c0061805400800040380c481d424140c43d980c2524090740034500c0c045410049204450b42401c0d250300344030244500d4000c0c004200301c2c9001451030030b400c0d00c0d568141410900c09010aa21138544510411600100801d4140070300c14041e95241c03086030071004d0414200010304001c0ca009114611a541480402001c20701581d409940e01e42c0f204000800101c0b0680d0520129203480d0440b50444418072038410b5200e104001c0300301090201200c40c400d54903090b42075200e011085907042c070600d4440e022070780c00c1000c94441000d010b0115080da181070710308103886 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 995212634 1250 995211384 995211397
    0xf1b090807240305150a0e09070b03090604030f140309010501052b12110109060b01020f0607140a0c150f1b081902040e0f04021903080306010f2a17 65
    0x4188402d030031000940240c0003d83c000da1070710b1218007a0b184013008108140d145a01514009102c202405444031040c0f0a040140940c803100c14510718000e07980f2a9039900c0030f00002c082100400a10700711038402c01201d0328003e60005440c0e0349043c40798001d4041c03c1c3c00c3c0282441144403030030300004661800d45029142d0244200249485010740700ca064841d08903400c2c03818410400c00700c2021003400c3c80350305c104a2042c0800100c5e80003a23400245080b00003400c104156022106005c0320035084010440320750200000a555048401e20072141540c800100400040e9520700c0b24116810130b41242644221241041000d0354000c007264280b10380c3d0051909c046201d0901007580e40f111304102c404000b54504016280950351203c0080c0b43c203040324030300030072101d140a000c114541081d045a4000315a48215542400d68581f9080e611000e08141d06003c1c0c00000c407010603000749094900130050809c411030360182200c94102c0c4c2c8511480854128401e88c111440141c0c100341507415 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 995213884 1250 995212634 995212679
    0x10e0a140c06280e0a080105091b0d08030c0d021206030c06180613030f0b0708060405010b04061815050d2007150f1d01050601020706080a0f1b090807 66
    0xb10780f08040081e00100c020050b54200841e88200c04c030300c4d480b81c4000d08002e1556500010303140c500400003d060141c0303001231400300c0c80c0e890303203034505607841d08120124660080c0240d66641c41e040d040070007520030700300441803082c008640c0b40500410750440714801d600c240d0940303607014555810030501c0d00c00c20600300710341c40541c0c8154146023840c00140010038100c0c03544000564903511200b5003241100c1d000c07503810144a00300300b005a4032032452604075100303a82c01e02c4030354181602c0301182d006501800d820003049940491308108006100b00080800b01e0056000307011466000b00a503101c192201801d07402c108004c84074904032541c2900c50301c0e0407102c507400c200240d910b20703006490510302c0c0f64a07036881e2220b03100120400e100300c0c0d040c0040c0a80c0c00011010034588e00342501c00c010407490540d0404401040341940000440c0d0f4810705021000030310348100c203000d00023080f000b01001070b0300d0f81300030050348a560401c0074002034403043d004680403079940c0e00325001d124060700114003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 995215134 1250 995213884 995213917
    0x2010c0c03050d1107080310060f0504050a0306092a060e0306090a0f0c030b10050a12020d06050603120d020a3906110705070f050102010c050417010e0a140c06 70
    0x8a200f1078661000d941c031013002003880d25204854507203850303e40080c3c502c0d8042c1008484100802c941248210b21a12542e06000c1e050514100008080050300c0c4030107441d858070344030004200b207940351102e403403006903600944107458400d64600440480740178001c0030442e0002d14000038500040e2041c41068440c00030120942c40d035481442d180d4514004545114400c1c10100000303004c0010036128441140011030141e16100170403005a0a640c8000c040106400b10400541c64044e012640240c104501240e103803902c501007440d00c0030092510807000004100340414003169002011201103d5442d207143c0c3c900e203031082a841005241e0b03d45100c24074582da601082c41d040500815600582d000580d1010143e22034410350f1080030202c81c40e40060105000e1544005c103020040c200a01c000c200b00914190302906520941c0162070007074251082c420048902500700003482c061410655403010480e10349441c0a040d408184c0000c1e0040c5030707103d00a814540309450310070b185940e140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 995216384 1250 995215134 995215147
    0xb040b0607080903031224010f1b020f1c021e060301060f231c02340215030a111c0f06050a12150b0f152802010c0c0305 53
    0x349041e9100450f0150580002e2103041c003e0040309007042e201d910800d400c0b00744645007440c8220302166025609052002100454000c10750007891001e081107042d0b0700e480c4848090000800000040c00302e960b01c0040d01840e8800b401288607801c003002d2003684c4401504000c41c1c842541c10f0a002e042c6600321030284010001076102d1800754000d1801420200141118116030b100c035005419100704140b0000143e004240381c0c4a0240050090061070031410701a616000f100d00c441c1262611a100121121400400100b0029000181c4e4000c3ca07500d1420f200c95440c0d001c1d0f41003143d940c1d00c00d0f803800452903003500c440c07822201e4500301d0400140c2c5800a101c4d9800c000d144280c0b144c2c50703250f50790704081003c0d2070320280e1001030003203a5a2903a852096283c5000c00c403a8040d030a000c01810450200703110703283c482c40304045801c12580050081e0440155002d03a004900c030b014103c607200c00e0000b400f9240c003168822807070703c264001d004000c442c00c000e031411107410f0f4008000030f8042102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 995217634 1250 995216384 995216393
    0x80703080c0f04090219020606010914040e0102180a0f0f090e1c05031005030a08040302061b33040f20180108190506010317090402070302010c030b040b0607 69
    0x9581c1c0280c11402480c1403990100c2c9000a80e00705810a16480e60f0010340100e03d00d0320502460240500c0d880103103081d10300800001c3c14541c42c2e1088050212480c2e25810440d40d403504a08100b0401100841d02c4880c004086000302e41d071641d0f11406861400000700b410301050600b4070a4a202200d00c8031250328014006004041078224648540150b080050f21010400040060864a541d07426128200821a241c0040d0b240d40603c0c480da0188510fa40020901c4080d101101c2c0c044800326200c0b0040c0301c01d80e64100e10800c0c00480c1e400b03491010500802e00f2144c414800109000c0b10031125800124484082016200034284289124980000511003208685c1c1280d013070758040104c40180002c5411190117180d189049014140148200c580810080e03d480b43d00c466080507003203964484c50b40301c07441070001811114810040584481042007211001d0001038011075a030b815a050080c0240301c100d007403200103401c1c414032101600d0180150070356128018a05441d1a105130788 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 995218884 1250 995217634 995217647
    0x9060513050d0809061204030e062104020409051207060c0306050105160510111b010c0804030e01090b270609033c0d0f0203030f072706020f07080307080703 69
    0x1001c81c1ca1183c20441d0071250f84807107015015100303101d920003800c0c3c206454050444400c001d401c40c01040c05200c4004584103503142a000034116100703100c03280d1581d0000c100604a801800340c8030b8130074104211404007000c030080486a00032002040b4107107400c60100d0aa0b08548291030000d503080c484441040e240e03a440010b624402d0045802a034450600d1605540804600c80040c05010400e80d03843c501d102e056a014065002c0208442c0459500c060410790014102804102035840303000c2150f40103100d07030009001c0011a040d1a5607006079024140c02c02c5480350150014a140c803400c160604500799010010700801602d500c01e50102035980d042d0040880c000e507410020342c4ac400c8607220003008041450503d01034a00e0080290001d08024031060410045602c100204440c1c03002c0c10385100e170010950300e0b01079480303060500385461550404103103e00000c00968000741c1c2c1d5070000740c0151500c1481c4140c807040c0e6610640c451703e0307004410028141c2c607801c106040c00a4401c0c113 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 995220134 1250 995218884 995218909
    0x70209011e0f0b0403031409062a01050c09100207050a1701060e04291003020f030f0114090f07082d010c0f090b072f1f0906051305 58
    0x1039401d01c0407a40c41c2c00d481200216980401d0241100040c20300500d54460010040b683c0c4003071202340788c103034108040707849841488102422004218520080c0003607402d00c0f0b4040c000b0401c001d216a04003038000c41029401010401d100e0340303c4007515500503002240b00e80c02c641004140744449450084843e01801c11904451941d55980c030020403404c3c0389803c818011030086c14241102200c4d4154215601e021031200c0010007111420000103120103c001810759038180c07140f0103460302a5021900d4201e06c0102c650b0294201444110a028074500c0c07144140d8659040300c1e091984039100300c2c2c0745c4510b8040d400d40c541100e215207403034040c105165015020302d0b403e8036048940d5020280c1c01c503040c9004803c002240e005480c2c00c030355405401240540300900e600c5141146603656000114500398091240e6600081d90001c42d0100c6050782004403401f900512500b05025070b107403881485c402c401d0000c1140c0040c041600f511640c1074415082070f130304d5003031000d074181410010f544540c0c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 995221384 1250 995220134 995220179
    0x160308340b090f060f0115111c1209032102041206050402010e03030408150609090c010809010b0402130f0e06090106030e07050d060b0f060a050a0309020a211202010207020901 77
    0x30002440c95143c2049000d200b602800880c0f4119414a10002104e04c11a4003000c00c100111401020005022034021a2810185614111000ca0a205a910340c2c0d65240c034241c03080c5080145000d06810900c10f04a0700503141500030b512241080d41c030200d02403400350b9654006d18030850320026503d503001640050050402e07030b44488080e0006441c40d803207a00040c0454005a1040710b00e804503511007500510111181089842d10301903065031040d0b5044418104200038001c1001440c0a510500110304003500039961001007854403000402140b00d100400111200006190400d110005009080c01000b43c01141d00c0e04c6401c5014043e1000307052400d0081d00000540c581d1100b243d032603803921400000c184140008100840301c100001c0440c01240200f1581d503075940e100d4201c0b004c0352041d050005d0020201d002280b0700003c0340d00503440c00001704040c00d10800f85010808201d03482806010750b00307400202c04134282d0003407003030081d0004030300340052205034170110401c00f661a90 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 995222634 1250 995221384 995221393
    0x1005090705061e0c030a110601030314030a15080f06010b0301140607030e06120a1409032b060f1e0308120c0c1c11071805060102160308340b09 63
    0x31020743d1403168804003a1090356400020081181038011640c0705d680c40f413113000340103258275589000d040800103018407501c0c1000040019003c0c0e203154014510001d541e800314a10640b607685141d07a61008a061991174403076000002504c81c0c9c000b00b264141d855000c40540107400020622902c0c0c1c0203450214140200f240c0c00345c400382c43d00005001580c038040101c070100c0c180003000c10700303c0798500080c000c00341c1604200417007400c000044800000700715401607a241d66520400c01011008140b103540541050300014107040300030514410350710b544c85c408410b2001c00540c400d0503105407100038007000d801e2142843c1c61310381c80306242d80880c0d15480303180b4040c0402811410040107640380d00c03001400c8416056020b9000108180907150301b80208400e234204201d800050356901d984103403290300c410000c0c40c640d100b80070340701182e2401d006455126489140800c41604010600c2e00c800e0500150802c0c404040056050042d06c4001c401d01c106510b52544ca0503c0e4004011451a124 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 995223884 1250 995222634 995222677
    0x100306180b25020a03020c063a2403080a030f0203040c0806060111030403060b21070503011503020f01120b10030617060f07050a090e1602100509070506 67
    0x311100442c2c45081000c00c0d44071054803005540826604605242046610541c032190001e42c00240800c40742204503840ca0b00d03418020054100c06031040710f840f0521050b040140c120492031040351028808404090284440403c8600302040101d800958034460f0010304102068200b402071140700c4d154500441d082040c050314200780d074401da90031607007050410401c01000c541440f0b0030b50040c0c802d1a180456101d4206525681d005500000d88080d54418a0146c40ea80d20f000c550640f510070f03040341c803000d110000005c1d11060140708281c0130f5400d00da0803840040301c01031030308183e9500074080e5491080300c00044074044000c4010700c101300d590b400315441d00d80d01c101c04000b02d1883c641d0007141007030421000d02c01142d081ca21401084c4d20060922101c10290320701242d0202e0385241c07154566440010407603403400e03550f1042154040e94014403108c00ca0705444007008000d180c0840d004000c1c401c110030200c40c070840350402540c0000402307000c02e250860061419000071088040b8244 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 995225134 1250 995223884 995223893
    0xe0d05070602040e0c07020405060102010c09141f17070c020d06020901090504020d020a02070e0c07121403040308041110020c010509190b042310030c1206030803011a0310030618 78
    0xc020317515448000700218000085140500800c0d500840c00c1c0300032301400e40107820107070a19103140149100352503c0c01e1140c28648074070b0104501c10f800602000c3e10304068010280c400d0101c4000c1d100000e002000141e2400d00402441c101c655014102d500000d0b1952640002904985130507410003514003000505540d884c00505501d24100318010394903148000d000c1e180c50707100c1c1e0040360320340e0040c801c000b40d1b034080c601a50806500604603200f441c2c4e910504a600d1410300140e510158030100c203000038590301442080c4103501c50301c0e45414901d000b10420007001889407080c80140c0c00080305151951044001e0017540034041c6c802e40c45a208881d1605540c09640c021005182c008141000420200740203032614032088078200e00030a0341800401c9900e03010f0072949040c15100c1c0c00d200c403a184034001c0515480d100a004102c0142c992400c04030031b41c000c0c0705207000107201402c155010300002c0112401040c0c9058405071441c510b642e0a00a42213400c2c0000f03d100c00b0802c10710108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 995226384 1250 995225134 995225159
    0x908090f03010b1f0f03060305122b0501140607020f15040308030f060f060703080a02180301050420010e010903120504080303091c300608030a1706040e0d0507060204 73
    0x207201300c0c0781d000101c800c486009000701c06541c258801c01d4181081000862030224180442c1c62030100141e0b5500004802c2c101fa19030300420441c6150107132141c40c0b4800903d540224166010340c2c00040224249104000840c0680d6201961102c2041d4070154a45010740c0c031340250280c2c0c4c00046050559a484a4000790400c545111079100d11608104551400144d50b4031648012501e04d030030000f81d138030014400d840050034001e519a000903c09626442260012100c0200038005e02481c40c1904d0400c10f0310316041c40b1141903030b0311554030590755802291041c4000c80d06030b41e904a2289076880d600e00d0321100e000001d00340541088080f03240b020034001144907145840c0200b100884007250342601540d00140703141080b50b4203103203000b190740550411200428040402d0445c1480b10000c03002014154825a4140700024000e19041c1d00103914819072410384440d07403ca590392030140000da03070324052034034541c0e080f001c0d41082490181c000303041c840d03002d89401810191034801d98501d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 995227634 1250 995226384 995226409
    0x40b130504050f070e0c030c130b071203020408100b0d0c080f06010501030c050306300d11010b0a030807030203040509190f0b0f01200304060e090a0908090f03010b 72
    0x426888000700001d0000c20480c0c03a0b10114400c005061461910805c1a21407030060041d0301a49400000308d8030000f130320010398040c120b000d248801000d50b1081001e0065101c0f4008440340d00c0252160000f05000f40b003038900310340fa1a40580004d482055500c0020301d81c10301c61036403003008910280c01107542080700c5409011088024940000c181600c40c1c94984160301c00c504150030074892282c80b5a005003625001030041d140003c2402025000855803103410020030340301c407140521001800e10000d0501c080c070706181c6480d140104207100c01030994001425075034004c86481030403c00100307140c006041d9a4040d1040d64140f80e1121300040c100c080c00c3d10101241040444c25030b104008500c030300c80a9008515003000005500c1010a511080b050b0901d41403140d9400c0b0764500d01006881d041c0d81d0740545083d07959817501d45070058220150030034003038010301c0740d44001110b0503000e00c07a941605400c02c0d10541402c41400401114000c10f54030b558042d529850000c000e034030352000a002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 995228884 1250 995227634 995227669
    0x516021c050102041d040c0608060f0d0305130b0906070f03110a0302010603060b030102090a0b0c01110301180b0603090307061505090f091c0903060207082515020703050306040b040b 80
    0x948500e010014000c061491040d17018502c2c04070300f0b2000084801920340111000c5042003207440c2d0381c0c03000145070000d608032a03d03040400b1804000805a11900528040400f400d4401e549621000c006485000341204075820641c2006554041048102c50750701d154800d1800c1e90508851031a1541008401d19085015079101c0d03070705004204641c003810300c882c10700341e0086003452500c000240f5012224811031721094400154040b29500c02c1d044841c25407000f16072035a80303594491190721540c800202c014056450702c9540e4500346000b81c2101d004c3d480c95401107003401c0c0c03d500c0343c1004062404040300d400000420000307240d29201610307403190400c155031011926110304030344c1c2010f0b603001641014100e00c1d1008052a0b4221101c54203aa410260050726107030149054400c6209599908038080c0c850303100207000540d0007400040561080e980c254070203200c0311921069006980f00240403c01c1400010418102607120f02000da000801c0480e6080300800400ea842082200010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 995230134 1250 995228884 995228887
    0x5071e030f0602270d0311010b0303210f07050d020913060801020315090702030f1b0627011404120c02040f061d06010503060d060908041518060516021c050102 70
    0x21440710100c4001010304c49040c0300c20b002c4092000050001d442c50300e0050911041c0c9081824142003540084408080034040381d5807450b004446202565030883d400214401c020b00180d10440144007480c01400c1c41d85035103082c504d00c0b50b003c801a40040400300d400081340280101b42d503460b0701a52009141890006a80742040e403611900c47d0001500140221200401d00c80555400011143c14081e01c684460301c2da1001003d0008d400030606410b03a25118103000c0c0302c00b82860401070031071808000701160700c200390700c0d00c62402c0c1c6862400e454620b202c544005004940540300f0404c103030350f0302e03e000208042c0c1a4000780855400c4a14010143d6891400b0b110700c2c0d070303482900241248104400c035142c0c6404c000080651200030015805142d1440c02c0c402045110340180d14010391001e4030f66291601c0700c6021050760b0b07842d12004001071000e4001400034941070302071000d6601c26600c2c0d528240c601d0f4034059030481ca01c40f00300d03041030344041803d00032915102c028080c640701340000b6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 995231384 1250 995230134 995230147
    0x13050133050f0f04061203020c1306030308040b06030a06060b1b0c10141b1006091b080c040e010f051f1d1c060b041805071e030f0602 59
    0xe404400e800040c8a00003180e880140810b989a11515004140454078454a0071620010901401050340a0038100000007000c804241e0080382099108005440d00a0401e00f411076204c2500c0a40c44017401090103040840e000c201a01c8100e41d0043e400350841710444216925202112a03960110340007640c08201b103686000d1903503d8031607002c030941c01007024914840c00225451180a00c110500c94821000040b860115040c1c9075004052854803409039608404503848130442ca01825181b032800740003281d044030500c2a260700c481003000465500307500000581e02042c0203400d8003a40d090500c00021194080100c0303c0c0a04501881e01d00014a44401d00c140c2c400c04102c000d910380b100c000d541b2030309540410341014116280050b0100365454802099010701e04401c001c2070b1230360860040c414446c05401c650146035040c0c034104903034001440052365007004404014215040036000300a6000c02c00480146d0701280c84030b6a0b0042d81c2c03969400c240c02c03104903080f2940c070707004a0710 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 995232634 1250 995231384 995231441
    0xe0d20010537050c06150d1a0f0f040803060409051006060e0306090606130209152803020c12070203070806130303111c0c030b1201020d06140a0e130501 67
    0x1444510b149007000f508010841c0840c0e43c482d54024007540c00f2110082c83c00c05940c1e214450404c0342500002c2008810501c000c0c50117034064208c61314518864010042408602d4a800740c80c410341e000505607045884200801000d0310042800b5500b51051080840c600300282c80307000020b01542e01c448500301e030554145410f01c880100038000c260000e100308080c0c0d480b00441107180100d45003005a0f50700c2d0200c0000d8224600e20303504a078901001c2003500060b6580341e030079950802c03001e00c0340d6a000c48c11f44040b4283c2c0700d040c148506175000918103070307111041c520182030400d1001b000c1d01d11890710748004034602281103844040045100140c1401d164041c402c6001d0a013841c2103440c07415810030101a149800208030144c0165650700302c05c1058441d42c01042c0990006020040e141040700c01d890203508481c1080c0b40e00c0b4942880081c1b403400b0050811204da4006c0c086548645c40c1c03030424150320a00610000e403000000310f000c80002c100b0710035212480241c003464081843c0c894070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 995233884 1250 995232634 995232727
    0x10606022503030806120313090608150115050715020313021201060e06091e07030b030c04200c030c0d080f060d0312020a0504170c010e0d200105 64
    0x80040300309400700782440469480b8113425441017060702d080d900482400300c070610f580700700076120b403d088501d500840e500f0965003080040300d0000041310082110b503401c00180c02000e02c03645903400c01550303404025500030300290440341e0060842030320f0b491310408440c0599004603488030050f0400f4010701c04600d0300c40c62410492640b5030080010078284108441d0611015250350b05c1002440c001070000340c0100c2c0750000b110301c071082c2c2c40c60508150f0400350180125504081c071034041d20a0483c52410030b48076042c42000c03040c041400c201450382c2d102c00c840d0301100031103c0034001001444a8503804012020782034080707554900642c600126414468000a06090f11801d50b0903081404294400034030751004403510740050741ca0100c2c01c0c044d01c00f4031407940403c0504241c1452071090200c04036030703111890749c2070300c1d001448050f0004021180030b04c590300800395248a004038191080c051711b0281150410b050451500c18600107100041600380c14800326102d001489591001340d206 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 995235134 1250 995233884 995233933
    0x1020c070306060e190b0607050d020c0901140105041a0f070f120302030408090f012001050a0e121204050c04020d0912021b151209160602070308190c0501060602 71
    0xc0c0160460606031707500501c81102c2c0d151481200d0f10f40084110750364901013111030141d8410115600484a813801175103540084540341d01c1171144000003e420402c84164041105050703440c00d01c0c0c2410040043c4d04661000420364800f203051181d4114600030784010070076a8081c01969120031280d2a161900b181c146801400b090300500900c80062120001e95044180850380640e44001c0100100c0b0400c0c44000f80ca01540600100081d00c80010740c0054090110f01201b4410080c1b046591542d1383c0901c0030504e0f01c00c9007000b130312900f01300400308650407a11400a503905400c10340002005d03a08000d8100c5c51081c0e641d40ca1504104442d1b0250741400c48030300107040701c00c9680c8441207078444810000c500840188941400c2c0c81c000e4000c4480e071200c441d49691050514440d89652142c0d00049509050f501c0180031800700c2c00040ca00b411640c0c480703030641c038103c030801d280c00c03003207854482c40e105000c04580d010001801c01e0040034090f040c0f941c0100424520403192154034111314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 995236384 1250 995235134 995235149
    0x5031b070f0f0308030105041e0501150e09060306070804113016090207080c010e01060e0c0909190b0a03151116034a01020d0e040f0e01020c07030606 66
    0xa01000020b5205050386c0c11544200d03400204c03500114002607544084064228000b0302d40400829250f200c0721000050b07c03659a1849178401d4400c050140100090f01d642c0d0341070307102000085101e4421514698042c0c4504404180400410007107005008504404500c441e0711154072005841c9484003940750350103203402848502940010309615100e940070f100b2106400089050500c1600c000b11280105454020494082045091030007001213002da10009807026011400001444080e035039207500c0200070f5016600c46a003071110803c0403000c808441c907100e0a500d000ca0f40d80d58200001103010f403c01c2e003604034240c0d8000307084030280d40c0007030369040301480079100c1da440c0e058080392540da040c28400c030800a0001c509032806195400100c82c0b80202d5000101c9a070941ea2124060142d02d80c41200b082d0040d00581e256000d6090380790000c0c9044102d80b120f8545600700c56842d0400e60b000083e03c40400180c1426a402a21101007641c4408000c000b004076910641c001820310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 995237634 1250 995236384 995236409
    0x7031406060f0103020c010e1005160807080a02030a0912030e10020406020703020d020409141b0d0305090d03090f0b04210c0614090405191a010c0b0405031b070f 71
    0x600011005040b5500d4035040503404210604a0242548880c030340c002482c007210611500c2c80a4000603000417260580240a0b80d50740c00f004d00d00551a0b00c2c0210840c0d1070304c42c119902e04078104000e40000308030a440d6a200e07100c8074040b445022184104e04a02d0ba000700b904050070b03a100f450b124001581001c8148100005c01882c3c0d030201d0a06c0549034120788400004181d800040c01500c4510009000162800440c1c610300b1030004000d15003448048040d410110310030304200048103100c0c40074001c95820400d1241600e4640d504000359807003400c01c000c1d210340341c88443c9080b4030990007100301081c0002d414446c2904521010760303044a20a02c00004100703564031042e40113000e10660092281c17031001d41505900400c02c3d24001c00e07000e4010019132030060b40700041743c0501c0802c840118544602008440414a400405541c0603110002400d00e1070b614240e104400404c142c8040c0801d100310100c150902110504602507403004028050405036039200c1d800c0c49038041700b40001e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 995238884 1250 995237634 995237641
    0x2010305070f050405130e0d1e093602160b06030d1e02011e0501030218251106090f0d21050919032a05060a020a09120507031406 57
    0x510404840650760300380e0300d4600511903066200d014140003064a004c40c0692090012150b5115852741041c50a203400460b2807103d59205031030140f0340d40102e130003202d90108450406128105082000302c202c400084d100e070603030741c4454100d0f0850784400c002802c1c02ca103c1800c0c452001c0a8980213842100030b800f6044403110064400c003001c4000078510110040411140b0f4000c2d4410642120720301c1c0180c07024031030785010000804003404124030400c500013a540003081e80c000306900ca44401d013203541084280032114a070410700801164200607074004244086602448003c5c060280e43c80109031131040c42480504004c20545800c0c20003014489812030050304244400022132803000c005090744480c11104e00305610103c9035041e0829051459040641c0003c4440009101410300300a48a801c0c00e07441e00482c400e04041d04550ec510041254620554000d000188260a0000100f540c6607440c100c1c2440003003042d902074028800800a01900024040800074168040c003060724 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 995240134 1250 995238884 995238887
    0x10f1406070b1806010b070c08030c0a15090c09020a0f052106010905040519050105180613150312181d0603033901110406210507050702010305070f 65
    0x1a6541c098507208070040414000f24082540301c1e0058500d00c1038920710340c0c6848100e24158003607803045490442c031101c00644002c0110640d02d045a102000c0e000c1c9a401e91115580201c034140c500c881541c1e6005190300241c0042000d6009052601c005a20741c2406080901140c0e11002c04400f40001003001c00c140403150b106038020100c000b4021802a160703540100e031002c5a640129401901d40020b2003000000380f001054607030540707407042c00a83c1e03e98040c400c407260030801c803d80c44c0c840303040840c07a82d240000045000400034000000c6810002949240d0241e0a5005484211400109045050b400803190800c0301d9880c02c811069450b086184458503001c103421f103071001c808004919199414030403100c050315081c034040308180da0020007080c1900444400100300c810501e003803034081d0b010f014000d9000140c4210310701340703440c1c100c00b900c0744202281d507650754403045880c1000d103990a07c103060141d0030550b0f4503501d5052610001d802c0b158064000350074006003000051700e25 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 995241384 1250 995240134 995240137
    0x180e0304050604090f14090a0b010f06121d012a0503041505091e01150f030b0c0703170103151805070b180406080a170c07090e030909070503010f1406 66
    0xa0f004c03103000281c14408000180024419030381460086040a42448107111001503030302c7d003803030140c91003a5203640e071061040010442842158042103040d80302e2000407981d9403118045481c0502c1001c010243c0c194607908450206110244281e42c501c00154140341601c480c006a12103410020300d0f505041e182e00801c0c9540c0f8000124003500c4400164060700b090028450021a0700215140a401e07540c0460180860303412820f14424a8140000c3c08440030740303118203e0350080460821500d4544881c01c40341d2209805030184032015221803030013426002c842d402540607440034100c501400600b141620582d10154404851918665002c203c02040100072a00032410769555950004403902c803440d076090368668443e141c40d0300056590004a41014103500c16a8070101d452100080702286000300c640e444101e600c6200706101e840b4680d8800d5640340d03003290843c1e00704001240020701c03d00e41111300d000000c801100401c8007030089903aa2026090001c2c00b41c505482c0c080c0421480d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 995242634 1250 995241384 995241389
    0x40211a0a0507120513140a1b05032107060c02070f0602010c0806011d0913050601030f0605160f080a090813140301020f12060607050609030c0d0e01050703120213180e0304050604 78
    0x2c00900110000c840d14042003c8640346a000c600c601c0b200b600040c074200001054800c0392b000b4040e20444540104213041545450744c0040c806500b401c06603141c1c1401880040280b40640c032a0440204130b0041e424120f1006055581c000305031030041c103a006281e0040038150310b041c00385901000ca2091054100c0074800384017965270002c60760750900c00360540101024042e01c07a00480c8004014411815248110140194014440b50b01d031740551191640070605c481c000200014841c10b0414498281503420403440381c80400c203d50185c5862440d50304c00a2840d0503800f40d04001c1010210003072901302c14102c100d008506004c480c4092080c81c1c031407585403a03103981c0c0c0d80001444070b42d6402c0540d483c041e0028201c0d2700d1450241c081c282c4daa0f100e0110040c1c1842aa09840d155501c00d00300c4420101d41030b1b403954200301c10f9a90a48003000c00f80c03880c2510980a1001003902c00405010303034000c040301d840b805140c80700845103408132005100b104603d50010401070000d0f88030304003150704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 995243884 1250 995242634 995242643
    0x90a0507050c340b1b030f1338030901091e260a050c010609020a090e0109050103030f030b040b0910030201090b0301051c0840211a0a0507120513 64
    0x40c4045d00c00d4101c0d003540b18007800458030384004a40c90150740000c4094405480c161500c0141341d1301c040c0d00894a0000541c1c0b642106090b0207815032290800c3e4000e075400c07100c22400030900c40741966a9503590800244d01c1102c240c00030072510241b140307181d540003a4a442c40e0440da0480c1c4610300e0740200384078202050051013800a01190640000d6001000822604500f1503d4911a0000401e00003492041400c90200c00001140f250300b2807007070904903030b4541c5404030f081e558103600360060f20402d40702c03e40c4140d0320161000b0507214030781407500c00c4500d000e0a000da0f90540c800034112f40c22941100f03101e0702c41030005210349d441d0040c0007400c2244078141c07e9a43c0400740b07445201c41c0702d080815600c807806074a115002c003203411070040020645451000400211400d180c00c0c45200f8810648120441845400c1c40c140703d41c0d45104490280c8600411005030080080684070240e50302103107940e803a4104001568003090800098280110501060503e8a07450000301c038441d00c00390 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 995245134 1250 995243884 995243917
    0x11d0a060311040f141e03030301142206170601030f030503040512040605040344041703091815060a0306081e1902090a0507050c340b 59
    0x30b10414015075004000214138584015150f0b002d4060144580c081240200b0b004141c44a10040302c1c03085004030030020b80210b0440e032800c20050700d158603c5070042d03045590003105030842221030510025602218030b010a40d5440c1422500d41040f8180c0e010409402c2140140b002450000e5804282d40d010304e4181d440c0d4441e07041c15802c0605001c03410f00c84100c00180040d181c1d4008000e40b04a9000700000b400c0810b01c1c0f41c0d10052700022050842c0603d050700d900d0348080c11744201400341e840b40214240d041c9170301d54a00703542201d02c5c2403150482c0d52020a000e01c451522043d00c818840714601241c80d00e003024412045014050540148608004140c02d0101c500c240c5c420f4005061500861b0035101c0140c00d080c9401030190820f045e58054040d00030b0101c5011880ca408156024000c038100d99a161041c40081101411000812108208413080060104141d040494042c054803102c0046074800501d107455a1180402b00344201c5001c108403402c0000307440c05158400890b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 995246384 1250 995245134 995245151
    0x6031e0203090c0d111f020c2206030305090a0503030406140919031239080c0a0311010b150712031113030314180d030c060f0b011d0a0603 61
    0x9900380f821080e201d98109140540103028000c082120b0003d814098940704401e0101311400c0c40c014040b41d4032200542d0203001505aa41000070002c0c0700100d42104901000016002c140207031030762a03100b50001040403034200400c0c40c223001d19070f0050408170000c501d058075092014142265032484181c0031030001c9503103d00f90300c07140101c101503080002100071154403441c25000510f0a0842030380029445110290b8044407900044010001200241800308281800c6258001d14482c02c030340380c4409100480e0b960000f004050081391203900ca0100032202600200c0c211810844040c1c401e0501c0300fa180600999607044680540d00b02660400075101204150040c0c0f01c40ca80003a9607807000100e0b014189580c2d01c0030000d0f01d11984c3c80c21044007243c00c001d4039a000d403d840d01400c40304403c40c10058500000c0841240e0b03c2402c00580c03050701601c9000481c2d40c0303410070030380309515040c448e1055030303000c6051310028150030380c1c1c2a2403c41440209140011501481c000c0c1076503103000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 995247634 1250 995246384 995246401
    0x606030a060504050403120c0c241d07031703010b07080d090f051605040e0601092a020703030f0201051e13210201050c070b0c0307030b060d0b0a06031e0203 69
    0x441c040c040c0a84144402c3c2000d1034020840c07406000310480c030741d18214024241e6031045210103000b64002c3d41948040e11141c11142c0e44180d0701c000f00c180581e8850304850f00400324202c54100c1403080d0082c0c402c640c0b642c2001500c0c0303180e001042c02003440820060103030104080070341e04d541d9044544161603907a0902814001c162603000909181c0d034080558040201c002441c00403094111fa01100c450341c0e0f007080c00185c0d00d83c0c0700b000b5555000301c401448055540e900400450840e180310942002241589112410b002024600142c01c9404140141500803c4040920410344001c000c980f40c030b14011030202c2107410315101070b00b2481000c12858141542c1071080d258200120b500c0c0b01d50380c0c0380e48284c1c4108003600c10016500348400241200502d10a4a83c41034100e00302945565540c03886103165440182280103065880065501035260000a8038102826990008401d4000d04c10000c40d00d145502200c00c040c1042052940031a948200d0081c2002d01d60001d40c498540100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 995248884 1250 995247634 995247641
    0x1302010516050d030f1a040b0a0f1202240726040e0f10060815180c0c010605091504050606090402030c0406030501060f050711121b0f040903080606030a 67
    0x4064040c91041d07540c1002d2100101e010b00c0712080513102080540c0b204001002a1200045800344074041c69140401d00d01301a048035414810092180d5505611340003802540c020a8000d50b41c01a1281c840c4011414040ca10400f401114041003046481043d0084641d11900d04010035198050044102c0c04d40d040f0441420006c0e801c034490303111601e8485580722f00c00c084940b10340d104000e0000c0756101200b001d1160642c0e8481e80d540f08190340b945070182903009041c0004d03070407604286100d040203555103440790040c1150400799641c0c2c02281407413825551703160002e0344104a1703041448108514001c14010702c03c1c0c00c0e200070805560b2500056228010351060030342181c00002044010108200100142e944645042240d039884050880f10507100320080310200710304000e0749000c0f441081c201e101e80a00100166078001c01d01045c0d0b410914405040480350700c12954813412450b06810041c0c0f034035010b403010401d800704c54030000c11000340589050701038000000401d88282e660342 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 995250134 1250 995248884 995248897
    0x31202130b3402030c0619051b060a1d0c032104090f1506020303040213110c010c030609060518040605060d080f18090609040b090a060608060615030103050613020105 73
    0x141c0801c2e4402e007400c407903581c416034881c0c120b219010b05001ca0ba80c620f8210140d6011440c2c1c11403100340205100c8090b07410b540051820540d020388a05c80349030206040021a105138040c1d8030106100c0c24a10503d0f41550031111100445e401500d5107002507240010900e2038800c48425aa4000d544102901607030b00c215000800080e0501312042d0320940c03560003c69080f01888031005580b6507440d0304a849003c02d490096020400c1c00e6498064010b980000340c40503030340c41400e0301d000d440d140d40b6821510464501000b00e0b031140c108003c01c015922514004000580d000c2000d83e4962540101407000100018151f5a130303003000c100329464074102c0460351035200450301d680e0302400d42e03800641e81213a40700d0303d102d40c00d08045031038502340f04d601c46018410103000081c0685030307580c941c226044024038800e55481848001c03804983c150144800804e1048050052401d004003800745551841c203804420358001c000420004c1c40000d0950303480500320540c002d0046440c40100c50300d01c51038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 995251384 1250 995250134 995250187
    0x60e1605090d06060b0c0d0819020f090303071b2c13080a05070606120203030d05093c060f18210309010e010e1b0409060504030203030103031202130b 66
    0x80000c201001d17064014500c058020b81110300044c203500b0120740c1d020003103400600341d0045802064400920303401421805851071565030608003494080784c5150083d0b0b6056580102c00e540e510070110710400f0410181a8400124200c8003464240743c15041c9045000c0700c40e1822031000640c03903044a0700c2900010b42c0070308015030f40d246041d00184144c1041d038041c0c0d41d02d0724095002450400c070221928005501402940c200f1601040501c020701008221b03440c1c034002c1c9003c1c42812100c00315071400c2c890b003120b41e5003003511b2072500707a00d001444040c20040c903034440008d010581c03075014016a0320a007151205401803c0321243c680c20910a1091807502c14070712204d40b40c403094408080c501c07940c0ca05008029501041c100300d0700343c41032210b102840c0e4026500805204054522820001c100907001140d00c40d80387d9a1301e02110001c0310f06a005030004070041c0101030740845a507440c124080c41c207604001d035185400d02010020300c40d020212400150104000601d10324944d00040340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 995252634 1250 995251384 995251391
    0x2340807080c0d02150112030e0301111e04030b0c280c03020d0c21031104090e1b030706030c0e1801050a050a0807050906010c05010504110103060e1605090d06 70
    0x301d00d0440d1240d0851200c0d14081e002c2c00312480788040c40003441840f040300031180006964078115401040310718000d0160200486a10001210344007405440384800a0315162585d6010140009a14400c000b48682180300304210420204241d40364040d0004082e641c16035445408905801407102961242c80002da460511512041c1d004201c0380d5055000e40c01303480d010f45207003008568600d0f4008000b4084240d01150245000c1c440032031086031003150500044c200c00380006c0e003145410540c0103c03402130301d90294211000c4180004110060304007082d040702d64403400040d44440d2640500c00030180c1d10010004428031500300e107884080084c010022440040c10b0300e4503088070901401e401502d29102c0001d590400c00c803000704a940c0100a006c1c280c0c01c1004000c044c60011340741504021600d9140d0b004254203109260146201c1c842da40040302c110f50000d1b050f200c0e1588100c03040c450741d10402640c96a1400507803150b194a03c2e085079144003040010322201254480034040030324 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 995253884 1250 995252634 995252647
    0x11010c2111121005041d060c031008060118110a0212030709051f02010b101b02121c020c0a08100c03020409140a0b06070201090314120a02010b0f04023408 68
    0x843c03502d03407094850680e4140502d00300c03185101c0b40038000b107010221940c007110010385220314540146800004070442121240d83d0382040c541b5002003a0001421042d44001c10385881125200e11441445c03844410b6040200d88031001e03454035581c1c0040b85440d00000000b0740f03102d00c00d008a1016040c0180303030005203004030942e1038046070020814030143d0b2900300b50b2a81460100d1030760071004695a41c2040401c410a4010a80c3c1c845000032a00544a91204040c00100780b162400d5600c0ba807880d1510382c00380040c0246850320b043d0105009070300c1c04c41d003400850360100b5842c0c1e5641c0ca00001081e211a01507080300240f181d54007491150f81380c010024400c070000d080b401d0080b25240001d1282618020400040c3d1107080c40090124584100410005082040022140d43d03040161154416105084010f6502c8110b5407001070755903440c2d000242c50101c00c00c03010400706803411400c0c07880c904500060300d214103582c41461205c031200c2081c001802c1080b0325459034800030039900d400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 995255134 1250 995253884 995253901
    0x60f280b040509150106090f050f120307050303040b0f0403080c160c140109050414180c03030a0c050d0c0305091c020a030602090a1505091c0b010611010c211112 71
    0x2c0c8590b0642044c90f55800001075203442148004181c034042e8100d1030314a407400b0104040b8403604040281c002c84e40741060b001c0018240b02404101d8000c40142d603981c6041c0c90800b2a41000512040c1001001e10034440400c0e8000c1c0300c01e43c04210f80000039503030441c01c01418400c41d6411001440d41012400100c1d034401e42c000c000c50024800c2e00c070031310150307100c008100c2640c0d151402c035070030303413072408000354800c3c0344070a03004000c4800302c1c25500d540c0c0410f00401d0540c2d00c04000708000c600740354110700420204011940021056103000302d02c8910541e0001c000340311740c94007280301e20010b034510b1010b070f00c0c17050128211030b500a04400656640e07103070034400ba4004010a5210700341e00300300060400e9852110294540c440e544451038407650340d082000303042402400c400f5031054428200001600341c4092406486a5150f0341c84401d031000b1042d00750354404982d44100a0080505d00e80c086003080902d40200034860089500140b12800500d24050b1240c040b0f0716104041c14000142c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 995256384 1250 995255134 995255143
    0xc061d0a0c18050112030e13020f0403111c030e010504051306060f0c0b0406050c04090203090a05240f060103020c070e07020d0806090703050405120a020c03060f280b040509 76
    0xa034002c0e40122199108032001c20100e510074030412003221031305011100003e2045801303603003070744005040e4207590418840f104100d0704480c460202002c40020180180004001e8840d0701c018200c80d200464801c0409092550106034801401d2082640f1341d0311a03a8000c00c01d0f9006458007402d52001d40c080000d454010b4103040c482d1307038081040d104140441c5846a00d144030216000f03440b4035006d4540e640c2e900c006240040c81406a070100b44408070b9010000d000540c0994400f41c0204201015070030854185540c12500c0204410500d852604102c8184c0910354491481050100300d41e0300c000050340a8499503071941d0300c0f40034280c2d011402200c0d1340304150043c03140d41d003110400701456509842e4100162242c13a070020702e201c005070f0014440c0e001a80c1c03161040c03051f101e00d000c01e013005c131085e40c2043e0414005a00490214003440c00c0400007180d00240380307505c00c001406d206400c29019006640b00d0392076071112803086c000c5a01b054200c1d071510040a0820841840c082440d19140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 995257634 1250 995256384 995256389
    0x102030c15010e01150c110a1502010207062f070f140a05210d05040f080c153106090c0b0918010819170a050702150a0c061d0a0c 57
    0x3d51140c0340089409140da071004404034110b41c4403c0c006061a460340c40c07001d50030840d1154403c11240001c241c030703a9080d07081c2c89a80f1a0380c0016071500c0c11341c40c0110980b204c600e00b01051180e918906200f503070001021111100345000c0040d0b803101c003410000400040c251700981104008044c1407130701c41d8005000040c450240d0b05a40c943d019aa00e540022152403802400042041c4071003514031915a201c0d0303030843e00c20540c424101c4541d07541c0180b280c010030030003e40382e00503103094850444004a182c1d0b00c407810000102038212660501030344500c500041d500d0300000003405804110303040e8001000d4a07044050b602c1c25640c1d50240d17142503800300001501030200c1d003031440741c95041d2207e0503040c0da903504090b1804031155104441d200a0505054800e440b50090b01c500301d030b100304000c2481c114240e46070359a6056500510102c1e030500600303071600c480d082004510340340d07001c018a2410380e44440003184400b0090803646e440e4000d000300c03103103c2c0191403c810821000c5e8108004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 995258884 1250 995257634 995257649
    0x1002151e0a05060f090702031207050c0d02010b15160818040e2a01031409010911100e060f0712020c040f1a060a022505040506040504030c110102030c1501 68
    0x1420740d20000c408042d42c00075660340390424a007882090780c07840d0003507126900c030340c242c0704407401d08501030306107459140f0a0303942c540441e42c001020725281e0030500c040017104880340000e100b00c0f24080b0125807001481e0b00406154500440e0311019109e03c44151064140c21120090700ca40e50555181c0c05494204849031246141002425411720040b44880c00c01c5280300c22081010018003801c80d40124445409041650302c01014002070310302d04241e406142903100001d0505403614200c501042546a0740384210400f2080103211544628030390744410301960040c3d00c4c2c0380c1c400e091041900031081e006080c030700020413200e0056400140c040c00f44504540c01d02c694905c84054808490401c000c0e000410461042e901003400c159000b080300b6003c510483d91007072801a2a02d1191140d83d40d880c3c020320014008002a103410700075250000001c035000c0205051a0750094106180302c28000c0842e010755039883e6050b0f0003801942c0d070002502040d10030607420f0f00c0340c0c00d41ca00700900a416 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 995260134 1250 995258884 995258941
    0x10020c010206070c020d1104110406031d01060323010603060603060b0a050402040b0a051b06181219030902030a0b1f08030a0e01050c070305030a03020712020c0f100215 74
    0x34481c9201c1c4c41034845007a0040c200308821645516400340030421441071680254588126804401401c00100000c00d0380343c1c3c00040f032a043c044500e9401c500900400d0150b8141001800071803100d212000c10741009605000d02d81000b40442400b41545034030240c032192400d000002808650b4210030301c001011140c040132545c1b2001040100e009034002c1d20701070700c020b2100c032440d54091002801c0002102421039081540400c0c2d06103400402c55200400e10401d50342d00110030010401a0b0102070342d01c42d680e007454009201d0340144604405190304068503a090207055441c10301000707090a80240c2d03030301c86626001c82c1c6d54004040b1000b108100d804a0140061a04000f00c1500d1007800e4a558854080400c80011a0b40e41c000004440f918041d050000001400400003810004403030f40300540c944081e42492102c0c69a804140b0040d504a20030f51000c0355501889400d90042c00c440955004102c1d600403440e081c0c2116604903c280003805200c0e41d901c4c0d000d001c400c203004a00815 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 995261384 1250 995260134 995260141
    0x30403022d2b1d0607110303130602160302103b01020d0201060b0d1116120e090601091e050603010906030b070215040605190c09140d0510020a02070510020c010206 72
    0x3201d90666142180451503403d42070345900d40b40c50001007510a0266580c2d01601c3c190342d002a0851784a48801c0000d103188650070452540c060080c440c4198901080c03c01711440c1d9004900800c503841075501c104401000d42416000740000640001c80d4909103014140400b40c18a801c00d04140c003001d4050300c0b41803410340d0110700c14052503069980030580181011000f152210240c01c582103078105011081c44850492100b40c220030010394021809000765210304000900701e00400440d840c0100406010800e40d0303600009944201d5010144a98580112150040040d181074018585c07040000000141a940c00d40240058902038010303d4203075201c42c0720503651840004082c010203959a0b0006001c2041c0d54070007544011100205544a03800c800510202e640c16980340001c100a803a0a01954484040801e0a04c50a81d2000295031290302c0d1650380300f1884010800450b000101c07100310750f2082c820000109800303482c540e85015a1040a5111809404014014441e18002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 995262634 1250 995261384 995261387
    0x20108090f0c100504081006030c092903070f03050c0405010e100311040b060f031b0c030d0203180d0903030e0d080a08090c1203040911030403022d2b 66
    0x28000c0800d15009110452814083c0700f9254460607440301400014040022054002c0c8026803121400c4200050326508501e00403100b06000d42103800030074580202180703e0710807180c0343c1c250700020340205580c0349203d000107441c1182c0f41e0440048081296030000800c1800102c022560310115024042c41c1c0e2241d0405a080c501116070f034100d0180b000e420000304060f1411069880c201800c042150300548001c038405500080844807604000030070084c2202e4190f04030510718003004005480c5c01c941d003054666901542100c06901a400800f042c41c0d95841342041000c0014641603440b00c105140c806050f811681c030007580450300b4172451054910304640e11203a031991085071a41401050f0100f1517000b1002011011729104103110003441d0f94689100300e140340d1900c0700459680381800701c1c0030300707803011010f0044a441040c403d1100003a00402d000c45900f0035040d10b00545d040f0a041c0303030110082031400c141c2500440050b2103016000c0d03480003d9403210758585004406403c0c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 995263884 1250 995262634 995262643
    0x21080d09050f0c0109180f2a020c09151f0c02031605060a0c14010f060609120c050f0303070b0703090210020f06040641060d080a1407080d0902010809 66
    0x24450004812801c00e001d40ca401604d00180d100e400170001507001e00403d400c004854121030006048680c5440c00481002480408020000240f0240113018805004250b2445018100440001204144ce0b5241e21550001881540c425070f01000c0410007203000381c12440c1c2000241d001c0c0c0502c180c007100321340c000d101070400c485c0003400252421000980445040e031103a00c007100c16805d01010391860320030034002e000324004039031030020703000c0d103445c0e030140c05842c2c036600c050351205608403000049440b2500103012240261451a007400c0c020740003d0541c46180c500800802d1f800d81480021036040d03006e004420710070356805803641800c1c40180e81c2c4000840c04007080d075020400040000d422070f00001030030540d2a0104881e62104406841c0c1c085101a0300d01c41003942000c0d4800c810100b108440e0000360503030761100c2440c2c1980f1203907001c0c810f609602c401e01050008030742e0440c40714022200c2068001c4a142d40700d4803003085030009040b000d41c0590001f2122400301710100c1000c80d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 995265134 1250 995263884 995263903
    0x160f05090f04031812230d2001020403151a040b090406090303111c0b04090c1202063009161e050909060f010602030708030121080d09050f 61
    0x45100840d6a41c9a40884074001201400000940c2e0040d0003d64541c0c1c83c00c080441c644030398200b4600c00007500d45c1c0074104000c070707452040b56441805121f44041d045a034407503851141c90300440f00d021421203e54003921640d4001045c6e00c20445c21805426801c4d0302c18181800c1485032042c41c1420002000700b5281c40a41c0c1707075030180812011600050550307107d094018802d0402060500b042800b50600c3d030446421240040d00d202c0040c00c00450611450f628094121020400004561078003100346940b40603a0380e0102815000c102599500b4081cac414800314442c2c0d4107076544401c00300c105650402142c450f501c58082010400225001c20700401c4201b8042c60f0302140c52904602c0e4030511480022550b40464480012800362104070219100f4825200204040d0600c40b60510300030130141d000d10215001803000400040c114021681100e04c84000400d0802c0c1c000805800d0100d52540100386076000200340d4004216900702181c80d5001e00140c582403244a5030060b03c07802e000c07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 995266384 1250 995265134 995265151
    0x1c05041e0b0306091b0c0c120a05070303050a0302090604030c03050c0108070e040f0e060a06061407331b14130902031909241a0918160f0509 62
    0x5000185a9007815004c1992210303d018488038248241d01d100e0000e076001c2c0802032225081800c903007825051026558201d000150002c03c0c2c0701c00c1035107a50b81c50b180180001010040f00040740382c810741c8070742c040d10418400104801e40d80d0780e03a4030300703080c0c02040c0e8401114913000c0d01d4000020340d0b010f051007a201c0d250030f40b118107000f107440c020040140022a0f0314181c050f0749030b85941443d401008540e200302c0d0120b50004aa508011010b04840a60030040c554104204070f1200080c01c14800380b03620b840040d4010000c1d20007600c0c014800b90703501d0401d802d4680b9150562082c030399801c8244c1c0c071007141621001501d26400e580e20340d0501c40d01c480c84080c1c4040520404c8504c03203950095034083d0008003030f20082000d600142007035850043c8141c490b21030441420601c0300c1c0444900c80c2d42000c0003010001e010009120040000c03c640c030701803007080d00d1800503984500340c02118103002002c038180c85a400f1040190130b81c0c0c10042c0551407580c0354003140800c00c0d0400740d60050050701c0c031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 995267634 1250 995266384 995266387
    0x15140901120c03020d0908180d030f03090221070314070303021b030309120a020301061d0609040312020c100b011701090531020906030303160804051c05041e0b 70
    0x5003034541d00a4201d00342d031401055400c11811466040c184211000a8030400c4043d03030b81c0150341007244400d0401c0810901c5007400c8040400000c2d04120403101c01e50403402c0208081e4034034000204400208840c1e000c4030840315280d0403441c007010651000342c0e8803906200003403660341444241c0d140c92a000090240c0e000e00c504140201c40607801e041c00100050403030703190480041c0860654010565200415482204e0280841c80d007030240ea40680f0140410030b0804114153b00c42071280007a10641c01120a54007141c14544100401e13400d80400182c02d640c0c40f2000020f507a6a024400c480e0034060303241070301001456116900b40c40c6104130300e014601450342803443c202c00500000d403095809408850702c1031100454414485010243d11044042a410314010f003d402d1030000c007624800d03081003040107841c0c0070015001e9103010607443c2074840c03541c41f03141540c94000250454584900356002116185a00c0301c000c2040d200d20b140300340c040b00180d00818811907514050600c1c0b0000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 995268884 1250 995267634 995267657
    0x103060602010e030904020322030210061d04020f0a080102210105060306030d0f0207030c0f03030e0906090a09020f0402030406051009090b0c03060414040602090a0806061c08070c15140901 83
    0x406c2e0b00074607000100141c5e00d1282424040a1030a84034a1403412409070b04030106034030b48099a441034000a024032035520340c0742c508111080b00c4543e40240024072406088924003001e848540c1441c006d091010000c660310760306c1030030b0038074840d800e00341804003a1042e50004c544c9081010540f070140302d002c0c0c000c00071001869815204000703110900421441519000000b10345212140d60060001e4820800168110308000303141034190b8045901030b50b044010b000d483d840d5400380a40c841c0551300300140502241c8001114912001c4045071321070f00100a001c240440d079031040c2d0003441c0c040354104030140c0c1d44213014242d40703100360040d2110602c03400080c09840883e0085611481c01880044d0805107807070503034000b090503141681d07002e070b01041c00c1849042080c0c4400c080c0401c2c600815503843c0c408009040001040e40100720039a803046600200b00f8684192907000e9030024070a90070704e0b200c6550301c00540c040d00311240007928055034000100c004000300c800c4800180e490310030030301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 995270134 1250 995268884 995268889
    0x40507121104030b04080705120307030504060b10020c040509070905010e0105010206090d020d0309020a0e0702060f06220f110304050303091e0a030f3605040b0a12021f05090103060602010e0309 85
    0x204504800d48c1e46020b80082c0502d070041d604001d511401d629200007503541040e0400000b11040b503ca160b004074020700e608100f00e034000400342d81c4158215008181555855405800e000c4654881905541000d001040341e05d100c102c82410380710280d00f240c08666440001e80c0d03960a60400d1040507801c0802c188150728482d0300140c200b1400500301084840c4c3e246d0304080242030480fa0a401070700290140410543c1080e05250022400c03103010074160307001803581d403035170a07005111460180e0300c00c0c3c1d0704031a2401d42c0080c81e0b50402c205242da20783c0350600f80340c0d45941c4210340d80da509014005510240c040c50b0a100600010410010003140515941c00d0b03602074185110102072006040b00c45a000c2080640c0401c14807074420202116102c21480d0210303940c0759040244640d0500c0404030b556124452030b00215414080740054003a01c5001040c40b254000f0041020428003d940c1e000c181d0b0840b004100386072003a03034100080750740c1d40400c908855034502d5190060704100a544c42a1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 995271384 1250 995270134 995270137
    0x705060d05070219060b01020d020606010207090b0d0503160b0a0203101202010e0a1e08060424091a15090f18030c011b110d2c040507121104030b0408 66
    0xd0050f00440c4c140c44100d01d070182040456420840784203840e61010741c02543d040c49400c200c0d640d14001441c03076041040020b501d5420034014090030340d6660700e01400952307416000007400c3d0307000402e496440d403040c40640910020a0000e0f9024006880400c06002451003101c2c0318110092075000081c0c14001c0d44084103030100c0d4184d0401200180701000d40c3d8401c500c50000341003011216044010340c12644110382c90315800441c560300580100720104243c0311078000003502d01c40c000208001d05100b00390062540306070280c4a0050540c2c002c0c0800c03e40b0010354020b452854465101840074410400441000c880c0c2024262004000c9450001c000380204840510402a00d0620b41e4004507503084404600d01d041034410540b404981990b000031000020000d042d014016840e8525809442c4440001d058035480b010011111110300641c1898018030400510500450500e504001c0010141c0004032011a00c2e1440c442d114400850450f42180da01c00c054070856070b907503101e05480d17 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 995272634 1250 995271384 995271391
    0xa02070e0c070606141302310305070f090b04020a1d011101020c01020901110d02070605090a080d020601031203060f0e1308030405010207260d05070e100e03010e0705060d05 76
    0x440288000000030f40d407801900054a4100000003052404004000c0340300e601907044841144100480881d908008000e040c004111030b04c111414001c4414000780904158009401805050f4020031a040c12007a410101c928083c000e10040c0c1150742000201d00c5034541d0500420107240304882030f140788011844080b42c050400c086c0181c15508528203a1388203140045580e503000480c0c900540c0c0140351000c4440a640040c02e401c079001300040e5591707a05010b5803040c0312001c04d00440640d07840c500d40001d000808142e48408030b4051019598070000e0004807001c403250b41e40049428481c0c4114000c0b540c8589003184a286041407034803818401406c0200d20310000c40c00200807170401c80c0110700880c8128001662245e107820050b1a00a404922000e01d41e0360400ca01207000865040e600e0f64029508001015203d02d0b0381550f00550302d0051a82081030b034a48110000c2e00b10151424940d0150020301c0300f0381103198215180c00c400d0241660150040c00307a0f0818201b0b9501076030f031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 995273884 1250 995272634 995272651
    0x703050c12030c070b15190306050a0501050d030e030118051507051305060f0c0f2401060503010605030a0b21150106020304030f05010603050304181508061602011107051c050a02070e 80
    0x4c100c03801c00b041c1426019180d4204241c0c8460023001088031622506601c1411118204084d504060010350030904145001d82005079000c0000c80300c0e5820760020700031305070246643c00500168a0850703250946000128104003940380010034090040c41181c0d010b402180c00c07200883d09100802034103402c285c201e45600c1806005031744c11031404000e842500c103103110003803020391b16007481c0c011a03c1c0c490104009486d9500c004000c0c0c181c11400b502c0c1540e9003400d206882e641c03820402d100801030f0a9000c0d41c4491800c0d4150301d075a8003180d4102c81c5105800c207650103c05100600421480700384295001644200010000300d07020303021242626216500200b403099980d103890745503410030341120103000c00075002c100d050203242c031480030143c58098644911900d08003080307440c2d000007407554241c003d42d461141600f601c00e500c020f59894001d80c8054079002d80d4146184d882c50302c914070300211b0003008621404180100283c400075181307940141020381c1844110308036a1000b806550 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 995275134 1250 995273884 995273911
    0x304030204020c030903120405031f0207050607031b0201020c1c1103180f090402100e0a0f0b070c0f0305210931110403140f030703050c12030c070b 65
    0x6079a207000524542c04010000c6850304c0c202ca00301810700040c10407000301c0110800041000e9103010403003840302091280340d526a00d01d000e5525010b407052140c01086400380904001c0c040703405601410a10016030b00e00d0000d02181e078001e030300302d01c45c102c0500100d17030280881d0280f0343c8112000c80d185011510f4040701083c100341c091465030300710f11501c801046410386880000d080040e1841d601040480d0003400509050300403801e100d4454a00008000c0c0c101d5a442c6c940e02c0d400e14440040010407144c4200a40c5c40e800011a034014200444182c140030340c0000304010012200400c1c2c80d00031018008903c1d104003c41c01900070801801c1c030031070702070010f20780075035440b02d003455081c0f00c0356004261906905400c411180c0d5085000e0a02d510b408604030454010b14291782c03d4950102404860031400300001d8606900f209034105203100000700201050741c03101c040c04040010204440c501c2d60600c4000c1018002100d02401599040c484c4c000031034440181d03a40c1141c5c0c0d100804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 995276384 1250 995275134 995275139
    0x30f150c180b090f030a110112380d060203010329010902071a0705031603060602030d0f0e011515020a02060a0c1a0a0c0206060307032301240509060d12110304 70
    0x282400c1c1d2625040c0c0e00218803001c6200c8a5801c10b14489480410a90400880c03403400300345803865603005040002d84121070164112041c80302d01e2b441c40004010b00c0261142d8403440c28074040e510902003142c1c14011004903424011290710003d4950f507980c80ca242c840d03070030101d002000b5081840c0503501a1840f401a075548007002c20035901641d40c3d680c54030f82d80e14103100204124441c0682031030400d807400c041017050a40c080b042d1035414401d0380010035400010042071001d4401e400b071290055180190078801e201d41180d08030700700c5d17903a40701c45d140c0004036560030703601c80480110194214004110210714180f00d403c0954030944101c80c000c0c8151007580e0f145081c0b201c200c408400079540c0707088400c44190104140c6911040440042140d1410755030744000c6010030007580700c0007001950342856403034803e400550700b110860b100340400100961807a9400c072150b10605005451a001013401420140b40c2005203070b42010180907096800401107509150400e4500d04500062001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 995277634 1250 995276384 995276389
    0xb01060813020d080a08181b0604030512090112061d0406180506060109051e090702151e0a1503081b0f1b060403051c0504030f150c180b090f 62
    0x141a00c0f14040c0b0071068840307100b041c010301041d00c01ba2406800c1c41ca189001c11809000056585108949130b4819402501c000b01249550140341c00c000c150780100d203903c00724201c1080141240e01c400b641c030071000600207c2500c023204c60a000b0381412640d15140180301805104810f82c02900c03481c0e000032003a10f5042c82050032402548200c0c0d40c0d40003902800802d6a0200c043c00103064102e540003040000460340c0c2c0d25405410204900401440c000507186500034000c0001805102d4614050362400c442e800041e6100101d00700648080301002c612007400c14032880c1e90110f0203000c0e41d00e0b07603829600d8005094200030340200400c0d41c41854000403038802c0c4103038143c4c144181c005001e00c0f4003442480c0240550745070814003d61050104101041b00061076283c1c2c400e00c48200c07000242c020004844500c12900b001e010803444038032540402046042c00c190b034a50340c040400020b07240c04012100240744c90700701c025550348454148104000c0000604e40f81d10014071000810401402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 995278884 1250 995277634 995277649
    0x5060d0f0606030606050f0f0d0804030b090a12031b030e0304211101021507030207020102160312110303270106050a2c130b070c021f12090b0106081302 67
    0x115201921000b0802c00c01510b4012440503203070442e01d40d0200d129441c049031405000c1c0c0c04040c46042010151018000710074121006550008004581ca1410203e0306075611303040102115159032001d0f828034020b00c640b05001500e501d03440000d074a03004e0315000700e0162074134040841d894042007000046140d2749081151650a403428060501412820013010030002881e0740c5040d5000501100006001c02038807540c0196181030041e254296400102c1c908000074003005508081c004000c4144507041030b600b09805030654888101c1110100865228002503402c03040c200100019a564040d43c0032240c0340c80360085c00005251070381da50010b12103514550050210316805880240c600303102c0d401401031544440c00c002020b0034146048441c070305244c24058215581074000c02c464501c2090100b4410350004e001d00740c51000f60031003100740060103400e0b00205200c1c40c1c1e1056600102d019151000740c02c00c0d1100348070f80c600b4070141c840102c000e00d000d0303001c0e036443c14a1005954106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 995280134 1250 995278884 995278913
    0x3070c0318091e06080303070e09180304091d0c060301260601090603020a0b130e180a080d0c170f060102070f080601050901060c0f02060c0c1c0b0618070305060d 71
    0x181e01903401500b00d60f007401caa14581001d54550010401c00507144d401c03076550070100805039804100ea644a555281c451030041d01e85082034040002d00140d04040f503081103c202c0c07610031001e4850104651071540e60344045901c00d0b00300340b0078070041000901c900f4083c07140c0f549000c030307003859a40c0040071142080800d030460041280c1e108018015404c0010b0101c02900ca20b0b0f00c030324070b07010300050080c2e0101b006100b82888040c0880020f045000780f0a011403500500340c00710340d154600740ca00380c11a90480700350902d03030f107103001b026000036803040c0e00f14420440c1e4070440c4030098a481050301041000101810305510841c00d00107407844950300d2500c020008a000b50002d541004200300981d507040e4003c40030400c0404c81780020446804801c03000d1541140c0c00307035070b42441244282c1800030b00030565500c403e805480d100c0400d0100c80c045d41c5035110f04130006240e55107500b0420307049100444800d00c00f10420005007218004e074006074001100500315a00b00c83c0135030f030b42c001602108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 995281384 1250 995280134 995280161
    0x307022107060e060f061e0301090f2915120703050a050c151c110705030c0d171b07170901020d090506180609030d090e0c03070c031809 60
    0x79281d070500285110b048079803112200540341904110458124103440030307041d60f1040c2e445040d21540f19158600d44690080040c0c020302101c2d5403800d1080c603002d04810b00b40c584160300b81e0301c000484420000b04010744600c2005c01e003103865841c9803101c021a000d201075000811010a50b92440040220714000d40c071540080c4050010f620341a420302030840364007409410380f17102c0c0d45859031441084c1d4140340480c0c01e0009a21804031180c2c00a01078603985010035040000d645401c1c40008001403802410410442d03003004104841280c0c0028600008243c040c088808220805c04d402d00398895050113180076400c0c02d205445031810000c5410020300200c0d40000c81c001d055030140105e214040c558100b441b032051414005c544035120b1540c01d900781c5e503544480c9008070b5481c00181c40e07070b0007809000c80b040c0181300d4002030700156003401500c200103001800103800d40e08070411a403207030312550354210003440c1e950307025900d01c010745651003107044901c140444c5840042c0305003503194500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 995282634 1250 995281384 995281387
    0x50705092701140103020112060504020a050c010608210a050706180320030f09010302250510020c07050f04090b101a072003030d0e0303011706071403070221 69
    0x1444011981c0526024201d4002c1c1d04001c14100e00910800d8040e044940a0a200300640c1c000d003200700007818a40c00469106102040d403a0446500c000038103644041c003030003041080d0700d401403039690300c032401d0101130046201480064019a104050090124036041c224204804d607520a410340e500d01400f00011001140d401d41895030240c101c5035100441c08400e50a44007800300d0300e84034031400c00c1e800c007278190000d0174040c140d02c03270382c100d40500c0c0750322082c0900058151004c0000681c0200e05944610859206240d00c1403180f00700c1322205d020100a0a400d450304050000411790008625409680d402c030a001013407007044480e05c5141c1c1c030600b121603182442c0030020b10002c050400340d03d040080c41908005400e140d90b17141c80085400a070300d00f003c030860000e4610710034400d46410040c02c2c000c005215800c0000954107030703400701442c410456103100c0d52954842c803c440d144001120800e84a03210703584d10340290381200351441a03415019120302e0100083c2031340c003043d2032070a00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 995283884 1250 995282634 995282671
    0x81903050f0a020703080f0603150a0e0d050f161518200604030f020a0f090626030306011409041a030c04021207080a0f050a1521030c05070509 63
    0x69601d48558401c440080850810845440042c04000000d02c0d1a54542c02034012400c0387c3d40410150804a044041884040c5414420354004d800003544076085c0d40304140e1000c28032030040d000d44201494803070b003c070308016823040c800e503c006004030203032040703010520b1406000116002d00c03014000034000360002c1304030038a8541003c14036404141e40ca41c840c4c1e06440348a60302c042c211811290403035230492512000e03000042c11000d4992110b09138600c81c0707000241703000c203d80002c400c46440e01c0d80c00b05540b42e440503040554031f1352481000301e900100005003007580940c1c0c0700800500c08581e49420300b15417802160840380804001100380ca04030207a0307000b9140421000c0c141c0c034001d503000d60800881c05002c080c000c1002e0800e00600c410b1100164442c1d00d154481d41d283c440c0b5080900c030f0344c20040803a900510314140d031a182d0503021040032604049458044501c002c000300c12510108480c0c41c11980e50246001c11106400b0703400380007680d81d548000450045038802c030702143c0c030517 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 995285134 1250 995283884 995283901
    0xb03120d1107030e032e02030a0f090f06050f061f030f2313120f1106160206060109030506010b090d0212010209130908040302010e040e1c231608190305 67
    0x50007a0001b0580c5440c800003c00500401b8121071550b1000c58001d41c4980711002e080b00548154000c40304124909400034061001d418808440c080c0a5070042203151980c1501c080408030072039110303801029250102070350444182e07070307544800c00d0391500040c01c1014800510aa601c52211200400900c61800c0f1404031505441900000060700c2c8184030491a624410018540c20040c0280903480c0d00340c5543d140100046803450039200d06451452500c90402e00c410602e812003040103106402c002640c03540205400d000b80c0c0d40003001005140e00c1c0034030003406680592440754004456000c1340300182c481580301d40c0c2807a078803c00035031500c4d170610601c99002050340c0c0d0100f40c2401d0251000218160108031000e8a0302840c1480b880000400800d02900c01001c0310003e5101d0450840d09031103240a0402428138280c3d41e0a0041d003840700d1340100f030100f00340d00e03403580c800400070f00110105e103900019589102d15011410800c0d05000c842e00c51002c815501c0c08070f903c4204104004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 995286384 1250 995285134 995285143
    0x302250f14030a11061b1005070c031d0105040503030d020405120a0c05150f0d0c120605180403030e0f101b0804060e0102040503070303030f0c02010b03120d1107030e03 74
    0x14081c01c0c510020040c08800000c1d03031040e909001034195003840c901d00c44180c0343d490032281c049000204d002c6100074003101c40e075074800403a2403c8044074a020f0100302110721803c1144182d0740c065440da44040c01e2904504400d07144195001d050200c100000111610144058907030384180c00e40051320741d07107004140066641c0e0401e2031709031500039003541d100090101c3c98803001ea4400b520359502400018035140d045100e400c072101001c40000c10b680c041c1e150150012800c6c8210b079644c0c0b6841c130305844482c2e0140c03956070007070710350045c044107040d1880f00300312b07407560b9110340649008203042c11420212801e040c4000c610320030940290031400c0750b8078131501503d200d210381d00000c000c0e0300c0301444008000c6840540020841911004a034140e00360035016540588001803d588038903540f03140103801001c50041042a10782072190314585a40188034810039024094090141000300c0d502d2002c05902105084e4801a5540703030700700c0d204505201030040d052003a11403441403d581000c00d81380 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 995287634 1250 995286384 995286389
    0x10f05090c0a150503070216030b1603050c0403030e0d0f120215010303090e0910050106030b040506030109020105071205160c052e030c02030903030304290408090d0302250f 76
    0xb62082e030004102d0090502da0511800ea55032030407a840391217000c402c0781418844011501d40509918001c0248141e40081500408240d107c80c5902c2405074001d80503070300100d5001880c568140820004a405405040c0368180001e0504241c0c0d0350590f103001c016050075000b03a802928031903141220303503010404240c0806074000c0b80ca0f0f10350702d1503a0042c0b0b210203038042c0b1000307851950013081100d0b00401c40642c848001501c184a690b13142e1000070014066000c101d0b10650030080491254201803080a07074041d0180d41c0c0070b107418070648480a081001c008031604000c02007042254685410315107611440c0704a80b008071080c0b8bc1802c00c0410030994521002100040741a880c03460704c0c40986c010710340001d09000c21841c80180080c1d0030b50064800d090f405002c00000c1008021610f024031f03001c0342d418120118519403c210410580d071f4100c90080c24043c081000c6c807054030b000e2107401704452007403045901c044078242c0d407120200c8003404003d0406d80700f11410311407010003e029102 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 995288884 1250 995287634 995287639
    0x15050d05070f170f060c0412031b03270f0b0901051e0a030b030d0914060f160303110f03132405040b15150f040b030106020304030501050c0a12050711010f05090c 71
    0x40d50520301ea40380c9103845a40300701c4000101c235508520405000b801103d2200d00c1600506201c0c00d01c80c10007401c0f140b0940f0900180b00c332003103030005002c2d8105901c802503401d0500d02c0b404403801c00e543c40c490340c1d00c40390400c1e060103800c1c007504090058003e0701c03c0004200d41880c07070310b5886c80d10024040c1c89400980910a4014400c3c18009aa0221703680e0100c80440d51564841e42d02072010ae4400d1107510070090011500283c41c100d0354041543d030205040c0309580820044110100c240254042c2598800c1c801d502000469861070b50303041c0300045c0d60701600300c813075a1701c039400c00c1d103a80d403042c01c1e1400e0016a00d0700300708410f0090300411141d0041d8034802c8180005000342c000303620780c0700c0800b40c090000c0c40495960320400d1020196006081c2301c443c040d980e540c47e090041e64903006480100c8a82d0700f0100000d00d61000314040e11104102500c0d0380f0120002480c210000d000c1c000c046034100b1180e4040c0c03061081d0240121852190034000004143c141100703494201107c5a840d5030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 995290134 1250 995288884 995288893
    0x1091212050c190804140106030b010e060a1503020c01060b2d0f071b0e0c03040c0b09150c0a02040c03090c080105070507200603100806060415050d05070f170f 70
    0x5103468805840e01c1c07202500c51404c0d042603030315490540071070b1849400302c0c110340d071802001200300f10540c20b51605a80150f1600f40256440104000010003107015079407804408982e001ca01030300a4010780b000004507030001c9035554460f0030301505e50300880b2440c030150886031110200040340d00103d00d85411542009490410516440d100701c1c803a042c0c004009009900b2aa0440b4204854060180900e000075280320b0030122034a640c0c82c0c0041e1401c0e150150f070381d6400155100c0d14004c03503280c61006800c05401590700c600b810002d8221010501c428040c10031604c005984500c10103200040503200050b008007035051281d601c0b00c3d540c10180c0c060b89800c041c8446e03940c000c010b4502e0340358042d20800300c5841c8074804c0e490741440078888a401030740100038801600300481e091000d56016078111203d5a440004000940350352103040b50360301d400d100050040341002038003401a1400342088a440766036904070b1a0780c4101e03c0c1d00c584080d00f03109849499401d414041d09804030355250050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 995291384 1250 995290134 995290147
    0xb0601110d05030705160c0e0f07110c1c0b010603020c120702310f0b1f0c020108091f0f0c02150a09111c03030605010f080a02030901091212050c 64
    0x1800c50303c03014002c4005c1c42400726200400c224580003411031180c1c41310b021110941e44d02e45a0311503031002d583d070003a40b601e8a400070700c600c4c0c406c005030075502c0c8076040209000402c1d14144810300540c204040c5000282008000105518503100b500070281a50010307074400d40424101c0c00c2c07000c0b406901c82c0d8440100140c0c0c0150f0f40e0407400e50049161021b001a07004050a0402d003405981104071758102d041c0341d184828802c40b513026811088042da84010040e411042081c8502062428100810002e250706409035104400003980202c10303034119140f640700880c10010740c19281c04500070f010348a80c000845607202e8014039507100407c0c0003c0002072a504003003c0441001000c04c0c0009035640c6a00b400e00589400c03205c032940004d8041c1e962030003440e09004103140d10080c190f0200c0d042000004042d4420340c1c84011180381035690401c40c0d2905076a200203580050311003101e540d294103007800442e0b0a01c42401c003102e09521441a50091002ca00e410b172403005010400241050000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 995292634 1250 995291384 995291387
    0xd0f0c050a15020601050405090715030207031803051c020735071a070317040f170a120f1d1c020115051c0b01140102010f1506081504090b0601110d 65
    0x21340d064440448001c1050b0783c0310074290f440e000542d40110400c08812082c3c107001505640181401406a82c0782034800e0741c0312011002c034000700e12001780700d03500c51400d101441240350308a58400c4010f1040d50754031607844080c0071030200000c11815034001c103840c40200420b10720312100c0000340641d02030505589841001101c110403041841c104540005926080500c02d100124160155041507541410603084c04c4690808080045172103444c14515250314200d2030b0181d626004a940d80c0c0c003c49a9507292520151007a80b0b0003910340c94603004e041c403880720140f2080903030100c00e0700106800e1440079991500485501054020369240180100004a440950009886081d1451400c49003002c8001f07900606011003d42800c50100012500f044000041100c07224244d00a0241762107484000080310310b010305080c500001864104080d5004808655002001c804030102003505100070405a40803101c082b981e152081e002c000c8150380142e1302d4143c1e104100d00070b00081208000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 995293884 1250 995292634 995292643
    0x9090b0f0a06081e010608041505040b220f08070c0e06060403030c05030d0528020f0301050f01020708012a0c0506010b0c0a080708120106170c090d0f0c050a1502 71
    0x2d8404100c1803400040d4a2515002d60540d20304103030341903000c11343c0d460100500d03401c011350f01200c500d9800c00122102191500071a800b5036003001c2d425515866041800d1814001c07011011280003d1030280c001145442d9081885103014007003007070740e9200d03600d0001d410054907005042c800d030b00ea000303001840d01c030a410b541c1520b0b454100741c020104d00342040342c51402541100001e66003401c0410802000440f08170560220078003215011030b41c04c900500070ba010740c0b110401c09a2041c4010082c52a0084142d282c0c0715041c01960301c02c0d41c603024100c0c290b80280000c0003c010084400a0b04a80030030b1550742800e400f1303e0211008840342e0340d150703200c030f40610917004051404a0292026007060040f800c0c80e5510010213030341c400302c5107016405a0004201000f400c0f590b00e00011b8114082d024401002216079688040c40d40d030f4100c0e0030159048001c00c1c82d000b14200800c540000e4031503002460950040c00c5080d402071410041140c12403030ba40040e000803e000040883c40741d000203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 995295134 1250 995293884 995293889
    0x903030411010503040606120c0509070f0c150236041416030617070914090d0503070c0623160203160f170c0f01060b03130204090503040609090b0f0a 66
    0x20b0304030380e05d4445050000c060a40e40e00603021300615402c84404005641c1e1a0508550342a0ba41892907515687e01382d41c0701c101c6001c0351000c80c80035444840001e401c0003c10741141c03400d40d0014103012103000c0e012020582c0c0d105032801c40501428102e1042446480c1d60b424440c21542441401c104681c0300500a401904858511100014516115020340c0181c406440c440d07000d10031046138400c2407070380c488051040e089954600340440820380803c0dd80c451041d10440000d04004160f108200c0c2c417544000e100e40c007041844008107000a259009031402d4414000d00c5c000c02c4608050804108500a0400b103e00c80040c82d82c04c8081c3d07000300503103403181c075022400300002c2150304000750200203d800040c40295080e04005161940700c02403c40d10a12000702c905400f0000d200c40c2c00c0350054000c00c1d21441c018400109030304982c0100d914140c0c0301801c0400c14001c0c5079036451564100d5001480880c120560a100c18000d6100d4030307100c094200c41c11345007d1070800200302d0190090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 995296384 1250 995295134 995295137
    0x305070507030b1609090e03030c0703030605040f0c03050a0c21060b0a030203091905100c0509041406030c0d32070312080606180f03190c0e090303041101 68
    0x1042400a011007441001c00031900f03d1100c4580b841c002c00382d2030403210140700310404501a02c0010441d9011441012400c00e0480d008511350344902401911580000d0030031030800d40c5410000c01d00351210300030480c51410b070a05c0400c4501140d03502505452008100300d4482d441c00c03100480c01c0f030348004090413008000c8940341e1901c903026441d0000d494540c000c003d10300313000916030203c0c65241e4000d5206100020980d151203600380d0015a4031031185c0c4001d48241e00800000c4c0b802e107880e9020808140032802d14901d04040000443c098407461007039210080502c1c002c2004900381480000034024045941c81e0402c2040c7e660b201d02841c19051031101c011605209a050501820040c0c07440c01242c001c94128603960300d00040440301d0b00816000050031280070600d01c0c04c20034241c805020440c03820000e0703078604606200000b500c003003840f41e06208210580020506100c0d1142002e07014851001900e414141d82e114815000b4040b81c0650b8000c104110100307080b081e464242c41c109 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 995297634 1250 995296384 995296387
    0x1020306150d0e0a0f120f020c0910050d120f1b06020a0903020d200f030a1b0f0807080708030a020a0f02131409010c0503060d08090d061d0705040501060c0305 70
    0x2c2c0c5414001c01800d0210383c0c1501c10300d003064041c000300320042e030f032024070617214040c688206080486c0e0071540d007942840582d00c011031201d043d14100e000d5a900100e040600320110350394000096006050301d205840000010640000c0c003a0312a011038200c40490070548480120741c0a0411400d50f0300f03201074005a800f05510031803030720400c2d0074002035800803d5000c948159042c42080340f02d804188038118049072141c030555003480516440c0c05900107014280f009180d0f21005800100b2082c0d010065002c8100410120b0f014040480942210001004900d00788330341285031010542280780e083d84180003040155034000782c2944016071024020703188a025201003081e0b4042c422180e607546d030821403426030101c08000c6562161800304002c0c003030f100c06602c09881610042d104a608161010303900c9010908680040c004004080c215440090058035020111001501189000503c50f5509109000200076110251204403010492545071030b40c0034000012405000b03050200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 995298884 1250 995297634 995297647
    0xf0f02010e0a0f1b0803120f070806301b0f0d03180803040b030f0f04170a1403090a05060a0204080705090901021b01020912010510060e030a140d110102030615 70
    0x11341424403a02c442080012104552221034a030340303075000214065000c40c14180018070b00d281d428a03050150100c0d80703400302c0c5500c07650107005000480410040030030101040e0113030041c07001c062151000244501902c04034180d5030214441c1525161580c0c0700b010042e11040b07490740d030b0403041c1c00d0b00c40e45414040344402a01040300311310202903000d11003901001c2000901109203500a503c903000303081400f207036035881ca240c100c030000c815500905201443c500320a15426108002d00c7d045081c0e06080e0000340c140c06004c0312030b0b84100e41c2218680c110542400811804100b45034002c2007110302903040a081072101aa5011030b44030709481804107070b02040e8100021340c11603109080f402907803080310001c0c1e814a4041d500c8140c5407409600c3c2c1c00e0341c070902e10106108940c0035800d4440c030032090f00d1920130100d40340b03888405c0050f40b5018001d01c460002d0840c0f404501103440003005010f002040710000307802c0071902e03520402c01381d004004000140c1c1c0c688000c40c001c2d00c5440c11440c1c8030030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 995300134 1250 995298884 995298893
    0x315220b01180f17031e0a0c0f110109080d020a021c05100b121f0504240507080c120601110f032b020a0c0f0609020a03030f0f02010e0a0f 61
    0x1604500c03030b02c0060102c1c440100300c14000c1500301090f95851603218460558540a069591041a4141c20070f05080340c0c4402811514070300810702c0c041580350094a500c11038a600040c0d101102080b078166140034203c10792035800c500030308020114580600344080d100c3c032001c0e44a107000785001f449650f180c45986240d5004c050010340950700710702103c0052041c0040d0714010400000d0561055198040030f00000c5400607200303c1d071880040140d101005071482e6070b00540b1001d0011140d2044144180d000c511200341100c0024840e07500124032804c08c0307000501045800703004101d856604010120000c1d100e0008250800390a103460340b0000146508581024041c03d1251480e00000030320030040340507904004800c00ca140817041c20015084402400c0744034450b80c1d4408a0103405480c40401c0192a810803c0380c0144800b050004c0c0d01d5001898498003500210007040c0800480c0100e0380d8400b024020300280c0b40002c10003070710410b003207035581c503c1c0c400010144641180c0220400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 995301384 1250 995300134 995300147
    0x807030c0b0913020a03020702041103010b070b1005030f0607030b15090105070317090c0108060301020a081906050a0e0f090a0c0b0703020709060e0417090a380315220b01 75
    0x11200780e1001c45d260720f60b4000c001c1c065405030700180d219505010101025030f820f43c003104d040307900481200c0c2ca400031682e601d60038840020100e404006081c50009169101842003440a094400140c0071525200c1000303400c54842c000c4441c0a000d2034000060302c07400020403150f1000d824203200e51100d00d2480c04961000b148071411403410300d0755052100320600051900882d0100740c035170040e6139607403005240c201d014011080c400030340c0b0240481d03203048510909052000c4003507000b1030000d0b1510041500348403103078048040102c81c801008400c6200100c9103812403421406085e03104820f480302c4505162034051a5100c04c4005150f00406008100c0c090040036100004d210155071041d900d01d0300042114140c41c00403038040e81c0c1c0702c444825000c0b00c1000348014904a485800c20b0100103140384a0a00751817a0303038514034000e080001d038946501c0e121414601c035550b81c1c0340668200e941703c2c83c1007800502415080300780100d01141c6000c1d205280300301c1c040020301400d040004807400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 995302634 1250 995301384 995301409
    0x702031e160b1f140102010605031203060f0a170c0f030a02010c0204050a06030b04061a2706120303090714032a0f120109060b011e03050403030609240807030c0b09 72
    0x30010140081d20003807030791208210130003d8008120b0103a4950a02da2109001d00c0f44200c00e200c200000783d42460585105a00c564001e4200512146c44d4540c16440c0711401d05401c007980e005c1e00c001801071900c081021142503090303001c1d0541203050350000c0d00701c209020b00240702d15100c400141c03004a8650105000319000640080541400d0034004014140510552201c00c003088100c0080d04110340d0008403040101011a808000c88002c07000c2c1c61006413680703900010101960020032010006103010f0040c20000d02141c038500300d550002c1d20000690103000e80c002108520704403801c4d00e000828512a2443c654100801800242ca02c06100344c415034461040e400c1845295015408409110700c1054204280030002d001928011130070014100c440d060f400024020790300c42d401c01a0854880d040200b08141c0796050340040d601044000f0380507840ca5010a160700303281042e03103c02007041201401e182800e584800c1e040c40000c0c029550362480010780c59000da120400c142c40b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 995303884 1250 995302634 995302681
    0xf01051c03030f0b040f0605030111070f030f3605031609020d0e0718140f01140f0405070f1e050a0c1406010f05030610151b08030702031e160b 63
    0x448031b005000702009101c1405682d0003036107000d4040c0c404000c00300444691540000703c6a011031510342d0103d80c030401e003691050130400210180440e4104030f0681d845002c00b0200c42c1d0100d941c980511021600f00d940c0101c2c80703503011008000910381031b5608103094400100d0051f07a9881c2140700da00c080c110412281741907204060002035010740c2d01d50860610441d5840a00000410910380c291140c01a51011500d508802c01041004615040e00780103200180003a140718040c0800107085850468040001c03502c2103041511170341d84000c0d214001e6080c4c41d1850056030218030001c2c40c074001e54268206020503500441c0c180002400d10030301d5495010102c40c01c56840380907000740d00405105903802807007680c010a1131401c44007000030035618603a0f19410324a00000d800c0359402c50090304004003010964000f0003041c134000c0110f1180ca900e400650f82d4140e05448064420200c00107034400910600841c0707201800321031034100340364112280d0b800c291203407861200d2241003000d4000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 995305134 1250 995303884 995303891
    0x1b0c060c0c030709060e01050108041406010303050a0e1e06090d05070b1c021903200403120810180504110301020c100f270503091005030f01051c03030f0b04 69
    0x260300d0980040c281000c880268251404190b0f511554400d4a6290080074901c940a0740148070325403040040a5029002e5240b0030400f2150792243c906050302a002a4006600050852213440c0c205060141c0c0304405d039409008182e8203004446441d224484a900c101000500700309240d0340c10340380100441d00001030740c190a9440d0300c800500d0740403c1c0f2001c0ca13414a9038000621900510a070f034640324450700340d05106a06890300b10000c185106030700d0711450440d00500c04980208002d00301461083c801851641c0c40d0000240c0302c02c20081c0b00d0040d42d581d10000b88101c00800007806046030440c100401c02d6203c2e490144c2d1117000c55562035825610208441c11859000141906849000c42082100c40c10404042082d2a65281c10304404c00085d284034441c0002e01001404842c0100f00740d80c184004072000a40d00941c00b42000c0015001000340700c842241c00d00600d004103422954070450070200384400341002183e060140a040e1303200c00140400c0c8881c1c01c2030b201b1140082040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 995306384 1250 995305134 995305147
    0x5120c031908040c1a090123130315020301061b02030a12021f05010f0315060b12190207110103051b2a0c03190c0e010e0115030c051b0c06 61
    0xc140090494003a58098107180c000255460b1080d210040440c1c4041d201b841d14040c43c2c01901e155211a502c40079500b82c0c1044175084103010380140a402d200200d03c04003c91460600c07018200a20f40346881080c4100010011240c01a40340c0070380d0784600741d112060385214000603091820420028014103000d07680c039513100741e0100e06040105050001c0c548035542100b58441161003d004000c0c1910780e1241c01e00200300c5904107107104505140c0c022456030303142c1c82d07115195000b03002d1f1083e100c2580814400e130040265040c0c1350f403842c02c0c003007181000c4040d2140113041e041c4040036030600d0b40e40d2000c03403012480c4078005690b03502c03a824860f03590b030b40184000c0510005115904184400411402200f0402080d0305012000040c02015174209000301d110b200a42c004040350303032400c4820001000c001c1d4041c241d00910300303007401d40d007650f141425503502d42420241c10301c03c0524140388501c489821409481050401d403600344403040040310340a291102d61000c81c1d41c0b080021440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 995307634 1250 995306384 995306387
    0x4150b09190e01090c05011107091a100302030c0906030a0f05012319090509150103060b090105040b0904061a030610050a080609030a14091908060c0705120c0319 71
    0xc200d2403590710a0802045450100031800c80e106500000e00c801c4412070100300030761040d00840140d411040c1030320a2035070388445410440c1d000c840e112282c024420f1a2402a14082807003c810b00c81c1401c1c10744c55403801054111040c8640211a84103c0021000c2b0b18051640d502050707400c240c016042000396150540e40c3c0e84044d50201d8a020f0030b92400000300c1500f0816419545050240c03841801141005440c40250400a02c3c41c2698030403026041000e02000004500a6001301400940105100e040c00400503058100602035800e1003010a9507407129000c071503006030030900004800341110f40c0c041410100561280c2c1c58400d25007070017100f400c3d20300050120748044405030300e0b0640d80d0380d10b551104021100080d15402c01c0c44007408040c0600d6285000100070403d4610700741c078000001d1442604c0045404c0841021041400760003001c000c896045020810034904204071a030301d0959802105000308a4000003041f141801e020400644070f1451079a004000701443d4843d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 995308884 1250 995307634 995307661
    0x50112020c01021c0b040207030c020607060b0a030819030b0102190c121a0a05040b040f110918100506031908090d150b0108070c061d1020040e04150b09 67
    0xb00040c1c580c41c5c100c014400d4075040c801c84440c0340e0b054640031350006a503000c0001a40003080c01351040740e120006111250740d4442c10310040d500c25a5075984800041d840e00300c400e0713040d140305d00a162424088080c50703078001a144c0ca0301651821800b00301394031860003880e5110998005680e00620150030382c10800e00c00ca03040045101148954120381d5040702d400151102554040d1108040350041404034951500100d403840c01520014a12844480810f0300035104403034800609640c0d00310094030b81d01c18004500185043c0d00c091249060040000c3e407a4004012040103001e208019042004040d2041d00c0c04c9450060008a5408840c18443d0560683d000d81640c0c045c40d00500300295030003212060b0060036181d64504040e941c40d5280c60081c8030b0340e0340148010418002081c803400e4200003c94100302250804196900280b81e503c8140e50107140d112503d0340c0070f220502c600d40c500e04c03180b54031a40080314958601c201c02c61440050200006494010010700100940b00710f00e0b00e13 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 995310134 1250 995308884 995308927
    0x61b0507090c1115070c03080a0e06010902070b090c010906030e010e010c091701090b150120100c080906070813060c020a030f051206040f1103090106031b0807050112020c0102 77
    0x5064444d4101c0030707565040e002208803004c0000ca4035581c00440441d01c51400c00f6408184500300003007101014660911b041002d900040f1131340e03000110002001554200d058111000500810398545a0000a4240a018010358080640d14602505030326000d401025602107182c0003085a15010100101079402a02400300000754684550501180501c1083c0d18180c11001950346500e4421600c0701d640000361039141000011409100c001c502d071060780490004820007410300e64003c40d141002c0d1a580386406041c068841c00b00311800304003040351580b1045a250030003080d0f41e684d0903c0031020142c40060011840d01c0c0c200500c01703400280109999000f52210b6050a09a8070215424400d040000007089503141c045082c0d03003040d0700f040030510144107011502c0085580d401d401604116208003450b07440d104100f0500c1101c000140103103000d109a010050f0606052954038401c5225060420140e16091803003c06241d0507a940410800002c0d5586c9041041c6604000d10b0030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 995311384 1250 995310134 995310167
    0x1d100b0105071403070309150e0f040b03011401030b010b090d02090612060403050703030b0904120305090c06070804090606050309033103140705030c130902040b03060717060307061b0507090c 84
    0x80202e604c60b0220002003c10108c0d60fa0605060b9070f80007400040b04501d08482c2d0026121900c0d00d510780c1e0203010b80c61603985c050a00020940c5981444c801e000c9041e0701645a2900421105900340ca464450030781190701900d00b8115520390740c01060010050844000d03003030085400f448101603100008086a0f40640e906101c0422914200040ca120507540101949880b1740d10a440705e0198000580c092001002e83d806441c010780880d902c0c2e40030031030465070351030009814009110248a520040c16041c54102d0035481c044909960740d00c20344141c0c08110311081420345800c640d00c0d0000010010700940008480e9582c5026680e60015a03900e80d80c40c0503031000410241000511448040f800610043c4890701c08000407000b000e11000580c1c00588804004440307460030040079002e45816a500c251072200d2a0040f0703803a20303000d0b0a991103071300700d01010001d5513484080c00000e013404108445c29440c1c58a8050721301b2246030711a08081e41008440f41440303800c1440014020041d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 995312634 1250 995311384 995311397
    0x72108070305101e090510030b0a111210051e030f0a0c060e041b0e090f0c04030b0606090d051606081902070f08070507091d100b01050714030703 64
    0x60850640c00c0c0c032000c882949028482d00c50800445004484d8001c0151040c031403401055128204101925811140b0300901500600d0400411205140c000da000911100400c0f810f10340700d445c00e400307219103101251038002400c0810b82c0b0350000c039101802810300a04c03078079441810410300d6060002505413240310f030144001e03c109a50020480c0b90700e03294050700003d0002e080c4101541e10004080000c0e410030303a00d030b0805801a200e42c3d01001c1050340c0340c650b52003020a100400400f44401003450030060403440520800c111401d00340c4095a80c4841220036650711503011803420301501039070316840b40e64150b9400900c000410300340400040504100401501d07403d05591780d200a076240b10700801403080d55024800c4550141c800940314588600d109002501e074080341e41c00551095540740c004403070410a00b0b1607485091050100000b40c0310100a684d202c03d602c4d401c800101584668070b410803100310780c0c40707681200c030759540c40f04901118030300d884441a900e820207102180801c1c078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 995313884 1250 995312634 995312641
    0x50d022209060b30010608030d1b18030803130f0b090106050613050d03051e03010906050a140409020f10030b0f0f0319080d05010b03101a0d020c03072108 68
    0x20300c0a945840841880c900d503404100c1015507904c0300c016040361003000e540e101c0000c0746048003880288880d26800c0400b14865110001030b8101c0d01c44500500280302c2c166800000c200301102180c4200e03a0000741c00c9413240d480c1c101c681c41e100c0e01454005c08020605d200c1004222001c56241c2c0198072590003040417a45450038803400344070b400e21440c010040c940003004030f440c0507a00d00e018944a458068205101c440d14000101c0c510003041100c21404801841502d52034811900101030441f0031403c094603240c130040429101d241e115000310345a100d00d10554945841c0e0b0754120070050900071070aa104800100100b401c481c2c582c1c8606141d2810303d980b4540251000c038541c4004029003076170001003441d00d8005184010880b412941030080200d62041882070720f00078a510b01030560f0f60302d000d40f071805401d2500c0d002003406151640ca140c0e08413011506864039502010001a40d9001d20030030389107503000e80f0710000c1110100030340206c590040301c080c000c03000e0b819445e4646640c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 995315134 1250 995313884 995313889
    0xe01051324080319080c07080c0106030b0c07030e0604050604030311010b100f080c030105030319021504030309020f0d0b0105010309170c0a21024b0f06090601050d022209060b 77
    0x644074900c60348424885240810200001003506500140c00051904c1c1d80c2d903200791800a00b00c40044101000fc6010028143c104440300510b00084503032619003400c00380007440c5401980005000c01c030550010203076800095009280542c40108852002c80300b40a0080ca42d41051000100081060003c114207040729005c2d41d0585000602450038190003003803105a404032100c40c14114860112048c2001070340201d0a40107501aa80214442e449070041c00300e41180840328500640541c40c140012510b00c00c52581921780174a004900c3c5003c80c2002c1d403508002005a040804d03000940c090b1801700060030700342e1644617045d0300e000c15505111420401c07100c0e0070358002580124003a240c102541c000c1d881601002141c060303c000b10140100d280820601458051030803201c114007405500c2006203005101c0e44000404007468070007000c0b43c44d0b00c0c043c89124000c99122450004541c0c60303000c1c2c070f101c0e1606000314603600c5132260747d04c2015181c104415100c007403070030b420542d490 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 995316384 1250 995315134 995315147
    0x1009060f08030a0e2215120c0311010e030f06010801240e0414030a0f030e03090d020d0201091802030406060b0c03160c0515090a0e01051324080319 65
    0x1070380c0e100060350030400d5000060b5207002c100c1c0019540040210b041000d0104842d00c03041040740c54400000d854002c0024120003c40240c210307001c50356840c04140c1c00900c8541c1000c040d81d82c04440c900c48001070f180140c0d0100001511079905004200c10030710740920002d800c2d412a00d41c1030003032003104c0310380c54400000c080071142e080780c0d441c2151007441031405034903225410a2007a01c01c820200900b40e0310a04640000f1303c5c3d60005140520300042c029494082c00c10b610107400003545c0390009550002d80028004000280541d6008000100307684c0500c000c4002070118011340c419212844140d4030080d40700301c1d42200c01c18034044001c9000d6882c9016a100002c034400294582200c40080d4011201ea41008840c10400c1320070100d45601c5803003107050307503407111000c4e03540380e00b400000c0148024444d00310040141e0b40c40c00400c220350b11040540004021a1300010b10044000403044022076080b0400810050303200c0001000c0c10700100034540d41f498009901680310841c1c0d02110344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 995317634 1250 995316384 995316389
    0x902041d03030a050709030213090506070806060a03090519030f020f15010603090f051b011407081c020409180303050f07051911100e0d08190203090c091009060f 71
    0x1c0d40144005160424264441ca801c4007007410036103882d5580781d0000720800e100300f859040399500c90030308500b007103002c1201942180103810480340c9441d03c02c003c174180303001e4456288101904c1e48405814003c06100030310484182500303000e01a0780d141009080312410000040041c070412058685400c008205001000060b0000c040309901c0c2c00c4089016180c400700680b0307603840e19269600010340c100322000c80d2251502090700081d1410300094505500004a01040703041040301c40001400c0030100d5181080a9403500405100510014000e016039003080e404685401403a0108000401101c14a0742c40396800b4010380e5a08541c2414114054070b010b40411414445c54445003ea08040803007580d40e483c1900074000d0580b1100d28160300d1301070741001c803680c0d00070000e103061050005501c17041d01ca09107102941400c54610a40c202d0320a0030030310582d800b0000c2199030005021407120680c00034200045820070b040300780c001340c250b0f210740010185403541c00288180c100311142c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 995318884 1250 995317634 995317691
    0x1e0201080105091f1e0602070b0f0a050c190b06010e09011715250f020a0b150d050d09060908060f0403030e0601060e100e21070810090204 61
    0xc46910b0142800403c140250400c82030001642010581d9152449810f000b0f248540313003038142d5848030545056040c1c00342c1101045400c034680034400030a00074100c41d10206940768181c1e4074800c3d010212428081c80c60b00794100d0047c040f0fa01a1070030f001200c4211580580494103050300d60390010342c1c0110407940c07003541102240c00100003840d085000d504899000800352420410081e1107141c00032012225103520400c002c2080140401d02c00c6074450b458600c2c100707402c942d49084006075450703249480003400000044000b075001140d0100ba02d25072000608851940070340c030302e48191112032a02c402c1303001407240100082d640f40708900d10030854000c2e90252005031200e40a600c102600188242c0515807680c0b5800404541004218000c28403907031b0701c051040048041110225030300030580204040b5030000607491340d952851820344400544c4061701005040f02c0c5509000a0f075101400c1809200c1d081250384c1c0c400c0d000340c070860380300719010400d8013079446d59440c5a20002d9083c81 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 995320134 1250 995318884 995318897
    0x4050f0402070f02220c0305100b12150423041407050d02120a0b010803030f010902131203020f010606110624010f110601060f020d09061d04090c080a1e0201 69
    0x2409030520f01d00f080184221081d0342c118180c0381185c039005a0b1032000144000903621010454080e50f10b0946101070101041e00c1440c0800c0003652400580c1e01a01d10305100c104007680503115540d81c1d028000000b00b104510303145800f40c070403003d521002254191000c40326014000ca10800106400066030b1004200c5180714400c3d800744005486200d00c0e5445500c16240c0240215603c200b180e4000c0c05001c008580e240340141d0400c110440690000e44164014040304903803241c0c88803001d00303031206140849440ca030b013810200c0ca44050720400c400d90703518152001c11659880703000f0032100c0f65007008039071180d00c800c0940c03041c05d4072460b81880c00d9510380b82c4803101903120f820314440c40c1e1005c0c40c1401000b50032480c10380c00e1900a0b40011301241c4041540c04400350107100c94440040c07181400b80441707150680160000325800306c10710008060f544445059034641d44102c0c201034000f40d104022a481d580c4090b50744030105400d480c0e100c076540041d800d0f92103500d00c1c0341500d41e0694420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 995321384 1250 995320134 995320163
    0x60806010f0504140a05090f0105030f060f06010c0201030f1104060912110108090f010612030f0f2f16090e031e030403030e030d1401080d080f090a02031204050f040207 74
    0x100c04001d50100041c0d8081000340c1700103019600d120740316002d2a884080303400307294906820036152254031910881182c000008201d01d4100c0c40100c294041403e0800c080340c01210300c0124001c182600c444501c05182944082e40060118081c005486a540b205015192541403c20607600c940100500891903d5426580c9510400407640c11010b035074100c4000300d04246159003581c42c560811480c0501207404142415809500d01c15220810b0412078104544000000c01101c00c0301d182014400314820010f455200c84c400101c6407001c4003086d41d0100e085109110a10429485175009040c02c4c010000d204203004001c43d031a2030480c5402244100a482d015201d61f00020015070506546040c01d1030442c80510082102c24051304002840b0f0340c03481d0026030324010613086241d5130f900020000320800d400c800480c0d04800b0200c907592881d500c0c00071b0603142114000300250517000303055940c3c07000c045c201d0242c02030b524101c40702c4107a5072542040c802240a4034a001e4216030f80340740341 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 995322634 1250 995321384 995321399
    0x210e0414062d1c02060a050307170402091303050921100c0f030b0604050607080304060e07140105071b0e0f0a1e150b160b1806041b0f030c060806010f0504 68
    0x1040e041441c41804200f480c040e9400241c4203400c00452400400d10010401c0346555200c41000103046025800131854109500820300210b00200340c1e2505150b03401c03801e4145401281a1900080d00070580d5202075580f00500100280c8841d48202030310960002c001c1100d2340340501310700d0b00c24558400c580c1e60006001103020b405d81c01962600660100404222500d80b18001c05406000c0c0158650380e041510b81034048032401e6200ba1080d800c0035800340200180341440005030902440e02c4da0700d0707000b00d0400b80d1032a890103128043c0c0d00030070703000041d0f0680c0c1c25428600c2040e400300311030030f155241214041a2030010417141107501004407001c00180c0c05510481e050000400800ca0702e40d141c1b042642c450f480055400c0e02c89100c04a02420004114245030740181c3d03021076011b5050030302c030300999941d40190004194840c0306a107111009103e01681d4002c010b800b02c1405066500c2c2458420700045008032000071b0f009800040382075010303120000c5e03c03444550310710f450315203070490 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 995323741 1107 995322634 995322649
    0x810020307020f07080d030902040b06070b161106060103111b1f20070201111b0901060c0f06020c100f020d18210e0414062d 55
    0xb4050000200201b403c9952203000e050200e04071040c5e04c00034019043c0c10a42d140c0104010610800384200362848a010340300c80b80d06034000c1c20001c6001c0764010819100c1001c56400707803001c1501544668030500c111a0001c202c1e80c2030495800b4062241a0301e00b50000f43d50b0300207500900e501501c0d5000b1002e074031400104208900400b01460700c000c188043c5000074900210f103450559008154140074000e61600b501e0901e42c020848003150422050058082c08100c1c0012500c540079200c008812074104103160b2030003501e80e85210185d44562010110760040e110640c4003480c03035000748000048012809600d8000c0c0c41d0700d0b03008884032190301c06002f081c0f0040c41c1300456032a9801107d1002229070b01c04500c1046101628a0b00c1c01c542c000c0c1d00b0a25004800c258800c4600c44640030b44411075048804d540b5070b035018810f0120020184015a50100c1407180c10f140441 = true := by decide +kernel

theorem cover : BRFrame.Cov 995143884 995323741 := by
  have h0 := BRFrame.cov_init 995143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 995143884 ≤ n) (h2 : n < 995323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
