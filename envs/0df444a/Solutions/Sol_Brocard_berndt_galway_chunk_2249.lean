-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2249
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:42.826972+00:00
-- url     : https://prove2.me/submissions/65877f09-6e95-41b1-a6b5-6af28f1d496b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 404316546 ≤ n < 404496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 404317796 1250 404316546 404316551
    0x3060e0610050d0b0a0603170712031404061a090a0209041503030c150f0c1d0d030806132a090e070507080304050a02090c090406140306010510120905010f050a 70
    0x14060101d203040d40084000380c044d0701e0303d00c0130801032803164210600440c1c0085060400c80d1140d68500480da101130011501e14580512820f0124003901504048401d0804000c001e40c1d259101d81c0042c02603192481c0060160700c41c04215941e5150f5164050f921000005854400c0714043c841110301d0a20640a05686803c1c1040042d5000114052041d4000b4041141c603412201c03460103061308090b5145518280210444103541c01a0b166280030704400d5001507041921084c0b1442c0c00340d40e2000b03400640324a00181042c01c10250345948030049130400900d001d00380b0f800025016000c07040d80580480300b042001c45580c051010000750401004001c1c1a0620b5140600144039074180100304276130100000381070000c148280c04400e50041c0101c2c42504e003c445060503648031050b031520940c500300c0f0205e9542c030281c00c0c9041ca800090010000c03a42842c0c10030069030400c041020030858404038243d22160b042c0034100815118000106080030481c00b843c0540d10003c0c02070710340c5803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 404319046 1250 404317796 404317799
    0x10914060a0317070501090f151b080702120316021606351302010306080c0f0405060a03050a0b010317030c0706090314070c050a080703030210020a0e0a03060e0610 72
    0x107885500960449900801c0b0403000c89003a40001103500034064058840d500e800d2600b002e212803032440c1e0b1145441442c8942d01040c0b000480e034100c44c02031100e00780d01e802d2024552004c0380141703041504205203004803045840183c0c0001b80a0380b04440107400c00240c4500d003200c0e142c0400071600c52000703600c03c040c4410300b030090060100343c21411f517440d0071143c50803044c0c8410802a40c0900c0d811a50311417041c81c60302143d00c3d1254180280c2c100d000920b01200060703c41804240000d031030b00010110406070950703904100141402400c103680c03206808000200040d8104440c2c92054412078009030a580755080c9000c201c080c014030090035a10410401c11141c2846003160380031948548002030b094164102103490b480d03d0b040348007040e03000040c1602800b01000442040350360868500c0d41300b40c0c54403150f540394602c5200045c0580c0c007503025204039071607039009840300c503865182c02401340d00c3e002d00285c1019456030060300d60603030720744081c98111000e200c607a901c00d0301c0c26054807480c4d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 404320296 1250 404319046 404319049
    0xe0703020708250204020a0522150c0204110a0c0b0a060e13060e0601060909060b040503060c07150c0c03020c450408090907020712020d0f06050702030301091406 71
    0x83c462a8080e02c030342c81100140034800b00600c60340c14102a0050300031501c41c88400405000c41d88440b42c00000740d1220030892100b0321400a102007503030004400c0301c0b89c89050500c2030726102c1d84800200d174040d84446400003a0f0300782c00d0182000d08025039500c02c1458103030074107400d00f28001e42a02c03d081d060200c2806008a0344015a800c8000610500181100c6040010040511007203000e03040c0150000001d41c41d40c8000b440003a141a0001009200c1d030b03e81d131503e194411485100d81541051000401342008030002d4890280550380b18240301c0d8036008030400b00c0f002c40103200040303111170200000313041d8100940400103a0589283c100c0076603900640c1e2102c2412002964001c0708460801a50648081000242c07a10980448040e05080c5000151a000032166600450012000400140c400500042110448109071120714076a40a10484110700e040c04e035081d50000071400c0c0080c0046c49504d00c0b4902a0703000c0d40d1294140305c924400c1e030326440c0d1036111041d40c0f841488201d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 404321546 1250 404320296 404320313
    0x5191e1508070203120907050109090515040e0f0f0d03050a0e070e07110a0c0501030509070f06030218090a050a0c0203040e0a0e0a0c030b0928060c05090402040306060e07030207 78
    0x4105850401070031640c2c1d409401c07440d51240914101c04071a00e00203010000c08001040302c2610b00903240e00014035110380790302c41200d0007141c443e418078055006c803202d2410554080000c1680c144141e03500d000c00f00d034026103407180da8403140c0c5060f80001387c00b4031131640c54400c0c0c80c0c0204032142c1c14005c0d01d2a4080e000c0e55071696024102d40210700c0004100c0282c007500001c052070f2004010f4030280c002714207064115005910486011a05120000c0e04500001c00c1c0e1605030b810802d14860403605010085000b5040361a020b41258030810b130301d10541d9030fa8240c01d841780003480c03408a02071501100000648040c030220005540c014402407000c021582080c583c4040911000605900c00c21603407403a1011004010f0540d0241c10b0012050101c41c84109100300c4954007210f8282a1005242a107203500440060030240c107080e00c400080e203150008944aa013600d8407c0c280345513500007400302ea2141d0300407900607a170b41d50300b0458003c2d103a141c5503006156045c11424042035403102c054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 404322796 1250 404321546 404321579
    0xe0109032a08010c120b0f03071202040609020f090a0504020c070909020a03081c0b19030b042d05120a0e060c030c01091a0906060a0b0904020405191e 66
    0x48030050507038540c903128002485400a281840091183d040d08510141a1141c60003d50100600301440703a80c032400d12440c4001d51000160080c00300d07620342024010450342c050012a1311544507040051120101e002034401151905c0c06503075034004450810030381490f41d0380300d103002e680140b203441e125603030104d204012a5074010010440aa251000900f95000c5820003080b0440c04a482180e40070710b00c550020702d00401c002007190380c10b14800c1104107290f0040100c15090101c800b403000400040e03926403c644203110403031190500324050b202104610508509140000c0c0d41902405010402c0c50042c03160b0000702c514210114500410741c24020345003038081c41001907841d2642d0401c1080f44c0c20082420001c000540c82ca10b40311aa09000000c020038240d080d802299101d80d003ca120790081d4402031a8540c9140307000c80da070721241c1003140004e90140e428800042c0795124020b01201003007908500103489401c102985050020b00c410180c12811134020a1000794a01340a540c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 404324046 1250 404322796 404322833
    0xc090b01120507080612030f0304050105042f1201020c0a03050a02010f0510051210060b070c1d240604080106081504050304050d0f060e0a1110020c040b010c0516060e010903 76
    0x6d41c555101004246548580c14001c5241c10000003040305002c2d0640c44903010b18850842d44041003019292200c2002d9540c002d6040310030100d410241c1403400002030304003c4480000581014090001242070541f068400d8010890008050715499070a10a02d10703800000034003000982014a00346119211a00070140524101890400351103810010420f117040181c000703000440e1554000003840d08402021240301501c1071000c04d090034080021605c4040c0c03080344440320381d1100384904202ca0420f44100c0059103440080b111078403040014000780100c000085481403030002031500d0704200e0f10350030000759481002d0000080d0088200c03022903100f11036040185000c0c2c1001e418250304940001c04c01d03854005080030300035000c01c1c00e074001406000110300c1050300f00700344141c0805c840a0100141c010528000e158036250384540c29004042c074100d82c01c0c280c161f40e45450100b01800c416001580030758200b145980c885010551101e0070300e00040d401e45141e0712400c0156800d040071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 404325296 1250 404324046 404324059
    0xe0a0309120503040803030705040f05010e010c020f040f06171014160e0d05010905120a0e04051017030c010e0d0c03121b09030215040e0609090a0c090b011205070806 73
    0x2030030b01108205540261001d082580d50340d0500900250007507005219440e0135041505000030320f58000c07114811030203c180c4491260107003030390801098001120301a60b10580d2150314121069103131080b14007a00702c1802c0f40000044850001d49442e43d001c07146000c8a00b000610301c62221001130180d006441a8540b103030000c1c40c2d600699600f86a200050740000100c4001c0c0b040c000150055240306001e9002c1e12100a80c9000f081d41c1442810500d0001c00d9042003820780350b00b4035900c05a4021a0220201c25244c0c0b5820100d40c2c4462544c241c038100c2c0d101003190054001c0078401c0140101e010f1f0000d04d00340c1c00c5202e01a140b84000440a0700344001c005104443c801c10390440a043c05150b540404441c1d0004001303801000031340000e03030040400398120003201c00b03520100d134241d901c0e1200d104525901c040400006c1a4018540700f120702a070399003500000d040b101c03010060645942c02049800d11400018030b8449000c000422650a0400303102c5110342018419800c03440030b40c4c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 404326546 1250 404325296 404325329
    0x2030a1404050f090a0b031c1205061f0c050d05030f13050606010f110a050d0908011104050603060607080c010c110102130e07020c03032d0a080718080102030f0603010e0a0309 77
    0x9840050a02d1b203075094040c085e0030046411000d0b6104c24001c02c0038070351a481400c80072014528103c0e0b00c2207904581101103540d03c021040944c6103507075a404042c0c41c1c0508100650f5580394140180e03000401d020034004014401e948540d50f41b410f901c01d03020484070513000320ba5242e0341d50382c0340302408660502c0745100d0b20200d443c0c407030f459152040e4111004c6417a08002407801603560300303581e030a10b0000f400c0706201182c4650103006100522500340c59a9042c5414001080041e500c06400e40358041e0b0100031444c00542e004020700300c0c03007009500005103406403200c00351064150301c00c03400940e4410403206c00c1102c8140c61010036a19216514002c039520010140d1900303074030303490103070741444049100b480940c00c8683c0320202d54569000d11000340c0c646000043d06006541703246021540f540001051540314005a1b20181c01108101d00301907650300e14142282e00668044841014540400450b0b007000d018410721146400c5c0100500c00d49074a004241034090b00801c0c007a40c8002c0507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 404327796 1250 404326546 404326561
    0x6010303050f0739080c040c030b0a060908010506090c0319020405060f03060415032409240614030a06021804020301060c150c09121a0702030a1404050f09 68
    0xd075843d20b030744521960952136140c2c1e52504888241d0312041c0c0404a80490045080844450003044441d0100106042d550000401002d41301904a882c00c0507510740c0c00320b040d40c1d05e012030a40249903580782c000d11030341000c03402d60a685005011a01075440d52060106015005045942c4002c190800c0e140f00801662003401911031075010705c0d0f000d02c0101d806101001700c036000314040d40342200e08001280500f0500501c0d20110b20000d04444c9041007010841419141c1c12201e0f0114140001400303102651005407000007a6984c20a80c03042e040c00841d0031106200f444054009440d481048900b65030000b0383d45e00341e5070001000c20341c003c184040300110f00e9900d140c3d591030051081d0744039a118003004208407055441621114042d0f110100074280520424515900582d5071440a504001c00c0c0144030101078000c0340c412a202170212840864502c0c043e02034040e55000d0743d501c0e503140d44001c00010045030402600c1c602008104030680e03035a0031441113070034141d458007403540c1c3c0c0d4003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 404329046 1250 404327796 404327827
    0x4030b0c1206030d0903030e060c1f0c020120180303130503100605033f0c010507230703030b040f1e0b0915010c02030706090f0906230d120c03110f060414030f120403030e0f0601030305 81
    0x741c4341e805200c0850a568030456095540e02a620290100c03250300381004984d0096a2140c824245c1641121426240c6c00395100d0070485a60189144421590001682d03810441509400984039040c0410701ca0341410088c06100e401c8401407400e03107007000c03040c0d00c400340700b03084c10101c42c2050f41d0003e0b80208050194000c07480594005000b0407040c290b868800c0e0240030b0100b41b480811040e21084986134525124981d440c190243c0b1845060b51440c801000e010207001c0003e050260701042c4400680d000c111035400f03884252365094507545041c1e4a5180042d103a0132901c003244c103090082c0046281c100128101300b43c0d0116200c180e01200003c214006c0703444501416604c3d51084a0182a030003c01102c1c61a12036907a417426071507184140354580705049510301054000c0b1010078003080c90030081004c040210005c0d240307442002c455444141d401600c031000303806c411008110601d41c00d84503819603050703a01c010b00003d1881d1412240c984da4140001800d11002140000c515641c0c035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 404330296 1250 404329046 404329087
    0x9131e0509071a07060c0c150504020a09090c140d0f1e080a02070e070c050c04050a0b0d0303090c080f0d030504050304030b0c1206030d0903030e060c1f0c020120 71
    0x10640303c00400345180302c0f03203d95202c1c0da000e48410b07003043d5684100c540305101001c006074000103124001714424a8640241c00f0140007030703074820f0560300c000c0341003032041c0b042202044c8506001d50f901d0340703080c2c40d40082180701c5806070b12440011090802040e08a440c5504c00790b4400c3c10450450b903102806031080203105400f4160004c00310740050001c0d0001103a00c1070b1a0001c210101a07070b0381800c22603047c0c4104600a066801602e64902d403402c0a40140ea00040c50040c04900c0c1d5541d00301040c041d117100e840c00e4002a84500b211402e00c2003c03540d240c090080c41028000c00003081c4034840d91440001c40e0700003010742d00d0000400317000f0107009403400346a010a0a042c14100b02e046481550080700358803410304450004034515203000070381c40b0580d00454480a0f001480d41e06c0548807412419404c1d50001020401d402147c00c051040e20585120044c001420001414906045400203071001055a15014095441000d0509152240d4400040b0b095644110f501c000030001c0b5135 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 404331546 1250 404330296 404330309
    0xb12091c031812050d0f0c0f080709210c230d0c030503030a050108060a0603120e04090c0303031d06011410120f1b0c0c050f0d1709131e050907 63
    0x22140305540d0f80341d009005007040300f0042c1c001e0001d5000041a18120341003c03190601241d94240039030343c8113004030040ca61140300c03410001c50b640e0350f13010381c1d00d40d42040f0000c805440900c00c88140c20480d5862255019241a40c00e10725070001451401d4140c04c1c030025914412161034010004114001c60078001648c2d024040e01c0d00ea0401c98204809490280075001040c003071880011500ec01c940b01e29400c4a0300080c221902d6014940300744e6549104041e403d4009840e402404045a03801c14140000d5100fa82c1c00281d9400301d04411105007030446000d540d5401406c01009442651022003a001400b00c3c2d915580342c0362610140e0b481d008041d220710b44142407502d00170064807580e101c0201d00c80100c910b0b8441400c5000c0c111011251842c00074071207c081d090078043c0741459000540514405854841c200d1f5164440da2456030900c0c0140a000700c1c0081c4905041c01e0020bc10300d001c4510807014001c80302d0240d2001c04600244008081e00780c1da900004011000411501004001d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 404332796 1250 404331546 404331563
    0x9040b060303160b01091b1205060409051504030201050f1302040527060f01050a0602101d06090d090902030f0a050405010209100203030402090106050a050d020f070b010b12091c0318 80
    0x8079454107004e411400d100e0070740f14600d08036000d181d00f40034410210b071008a1303543e02123245201c010840c0007800083c056640041d500c102030000100304005c3c040d02c022003484150240e141c01e280017070942c0d02c01009410001e0780d00d4203002d0308850745003002462a50407100461669601c455102803041c0c00324110b61411030300d0180611000c8082070a90148001501482060380c0b140c00b40208040345202e45801a032100c0f41410f40517500b5446032500304030500e4950308003203400f842c4614041d4286c45000480d040b07460180045030f0400c00307103c0188410710096096143c010034501c851000200030452031500c940000c2c0c00c003e001c0d8110f50080400901d1404209182d03040203581742c0040310304a005100782000440e0356030140007600c00388542552104c1ca8030a0f00280f4001070340040703075404456002030110b41c00040700d042c86603000c1c1004c0c0f081c0c0c1e501c884088920f101c84500180c032003036240e000461303144101121440c2c40c12003c00349040115081c0100d484070040c0311007100c4041c100b6034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 404334046 1250 404332796 404332837
    0x9060518060d091211010e0312150604030c090506010e0d0818220509030310060f0203040306110a020c0d0b1311060307030203060109061121130f18050609040b060303 73
    0x800f00001d0340000e885917600c45100c0b0821720740702d0803107181c500280e4165006100940080b07100094141c2d000f80c0744942113038205001404a030042d00f16030401c8540c1c820914051060303050500c1a180e0190003482c2c22000c106031a4007107200041c410101408201d400122481002001d030840080040058000119403e5540040640c0300684480c400c8860070b10002c688603450000540b0b02174546480225681ea1804a00307460f07440e1007881c8942540410310000020034298451105440c04440c40c2e969501c0815800034104499a60f5151148500040700c50220307164170343e003503403042d2100c030300b0040000281020700071525241d109030381c400780000030018a10780c50b40256020304401c1e03c40300c09564413944181c41c1c020300b101c003413080ca901040141513841d240416800600d48420020351510300840400342258a2580044c96a900000c504004400c0b01d0b01c107011101ca83c144c000c011a0400e20001014000043d102400100b448400308000c0d940c107104460301d00005021180600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 404335296 1250 404334046 404334053
    0x1603082514010b1504080304050d15060303020c09090f0c040b010c0606091d0a03080406050a02070b090a200a12050c0d0c1a0f1b01180503031609060518060d09 70
    0xb4002e0300f0165008040e078440d00003803c55140c1c291030a50300c100300990304040c1030606101c00a03500ea4419511900755038940e11348503d161040303801441c06039029004581c4070006000c21400d015215808540c014280c24541100114407502804401c8401041004035100101c0b807241ea0004041d000358607007100002d81e01c40c035134001503500203100610f200d01d400c5da45100d40c0760305000c40c000d40892955000900008d029520869100302c0c1440014200a90f54031600c81507501200d083e900e6520841d01359091080c511401c4610390f0300b0400030350604407100b000c070b10000c000d4031420041c2c040a199840401c1414000c016061801400c1c60000d00524186020364103018810a020f28810b1307090808000c00c0b90381100d01c0001c000310000d1030315410385100050224200d0000c0f0141d580d41d0341c1c103500f00706070864420307040340284000c42d141d003810328042d80c02d586d1030f0302031a00b0711200c00020400d454102041c1e80140003c007010708020703d0800046a502c3c8640f4509003d190b1400b180f00c001c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 404336546 1250 404335296 404335301
    0x15040606021c05090a060c0204181101020f030310060c0213051015020613150b060c030a1e020c0105031b0f040305010b0910090c050d021308160308251401 68
    0x4038519040b10b0b030b140034221481502c00e440741c110069040000720805005440c080e00704100103d101800008160301c0710103000071401c400a02c21031314015480b03584181913030704010a00001c0d0007000a035103075007070200605002481621881003800704102c080c030190b41e100b00c40f071407080030301150034007030343c40e0075203904007100c003240a0032110b010340c9055151154400074682703101c0e42072807404011200032911002c4444e8942d490f4000703030f02d4943c11003502c19107400001d0401c40c0c5034240210f407030f2002030002070106080021001e02c104440f549824110358005182c900303094007030804660340d4840000c11402d0b1445200310407000302e400280c821440b1507007001001224001d80007008410180700400109800946403403d41d140210700a004c50389182d40021940b00d841c0c05c040340380040764580b00050341c0000c40f820b07051080400341088182024400c2580172801d002051411700d0859071501098000c0c0b80110100c0001c2400000e20b41c0071490000304a02c0c0c02410f140d0402180d0b0404502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 404337796 1250 404336546 404336563
    0xd050a061d011518090f0602040614030f0c031e0709030b0c0307121a1c121b060b21100c030605060d1505060d020309070614030f1504060602 62
    0xc007014080c6a0800060107106400f40b80d060840b0700d82d043c07890804104005440342c00c4020740d42d03a450140c000040c440c0b080d60301d0308030711891015807554a04a4058900d45000384125600c04040040021241022035003030742c84851000300584a80710300328180c03444142084429804c001900511411a42100c1500c04680c071401c01c840c00c6654200f102c24290105031403680100d071070364507031850341040d0b0b8101105090b00321840f1601c07000c60310009142014411860200d001c900c240b41c4d82030041d102e1050701c5034489820700314242c0c66403440340c40302c00100200103407640b903076000301c89840d030b664520b607031000c920442c04244e801c503010032500d07210002c0703101009581c1e01d041c940c815228064003540702101d100819150400303100020850144c0107060010401e0030240c079012802e6131302c5a001e008040c03422400145c991905003040d13072500f034443d0081d4041c0202c0d590008003080d82003080ba5440b40c09103a00e86d24545868140c848904411101960b02c6803d000c030118603150300041c00d44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 404339046 1250 404337796 404337821
    0x70213090204050a021810300b01030605210304030204020f0a08150102070611030408030f0c0c040501050d020f01210207110a08030f030c16080c390d050a06 69
    0x42c94441050a44c100e06c1840154006e900342d03000b042100703103003615004150306102d050005c45111280501820742401c0a500d850140b6091120781d0405058030900c06d40c40000c1c01c1c100b1401e41007000060007945050407071241000101e20310a40f030b10040c0140d4004650141c4155102c0115844c640740e01e8000380c60800000e828100050741d130914480910100c84411b801800307405003001030444241e84903800d2454144810000080c80346010002030503800000ea030807503154004940c03400c0c24900f2100755188150308160040c41035654680640c440c4640c100c8054512640d03500c011ba80410b085c69034040040000400000690055001051000d00c079220003211581c4070030420108140b035028840d0564800d1144418542d0000021904500209103580c1002c40400303034443c52039140901140d10341401324007519401c0d02003086800e2506440c24101c240c00d1201e803081004a04110358008400003002658030548980d440b003425550064140c819070241402c099014010030f0b10f558 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 404340296 1250 404339046 404339051
    0x203040803150312030604020705190f0c060e010206072d2015040303050403110a031709030319021809090d0219050c040c0e090a0b030606100c020d0305070213090204 73
    0x107050740fa0102d1003028100000c02040e0545d2a04401e00000750040ea004407424031a140d500326031040082c402c1e440b041d124800309241e410b800e14080380c204200c0d0f40300c8402d0200540b2072080d10382e0041102c9078000103520b8600022800002000c0d90740c4040368022107500040781d045c000780c41e8800c40320010481c124a100821015000700c9955441e002c0c3d0050328803042043c0454006886900500d030098002d1804e030409a00f1070802e42c1c18100300400440c041a1503026000c91040c9541203103521007081800395040d40f03010f04800e8903480c01c610000080b15030024202d00100c90710078018610710006400303000103240a0130320969803221a160f40d00544901d54000402190303040034680e04a501001404820741d080c014030002e440d6166200050049406c07100041d85c5407841502d124420000340801c462410400f4103041100c00341c8000d0050500c0301c1c98101d42074102035041102039058074840c0000c0005d04080b07a4600031010000e5004100455620701c1c1484d50704450b2004c2c0c02220308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 404341546 1250 404340296 404340331
    0x1505010f1e23060a0201020d050f01030f150f0207081809040218040303060302090f0f0114010c031206082410030b01090e0a02100216050604030305041a0c010203040803 74
    0x1500c00765000c00125a600c96441081031200321141419a545080c1031880c1ca4100c0c10a140000c503c1c1d00600c0e400d0340146c4d030100707801d05040b107240204c0e504260300541d42c02c6154107540764200d43e448240740140800c0e0b40d48503401c0c007401c40d6070706c12038800c03035113080031034480d0040d2414403407940c410070894403001510403203000d0a10705000c0c164001c56004180412404010171000d000002c024010b4013850f5483c1c3d0000b0258841e078406522038203c0b001d1040644c079100591a2050b8010303001501c590140b20a046000c0e41c01c10305081c0a20f4250800031101c01c55115200050911034100411030b0248820018422240c048182c028458108404242d55100820606154585d200160100900d0300c01000071120303591001681c0e019403001da50707180010742c000c1001082c0303124540005034000d28122080a2215403000003510048410600d840d00e51b40f0b005142d40a40c0c050303a40043c1e201260008622002c0044035400e009042c0203640707034909800c001140740c104561b19001c0d4455400d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 404342796 1250 404341546 404341559
    0x20306070230090d050304090906021213030f180314010603050f030901120209040f050c0c0d0c12080c04030f05030405010806011106011413020f091008011d070c1505010f 75
    0x101a9441403070114083c1803100e500b08024968034200700640b0580000c000204002c84580108064140150000b507920020700c6440e400640b00141084043c041c1c81001000081d8010001050140310385041c50103120000c180c1014804107900049c0540c0700da100c0c01401c80011340100040b00d00030340a0b01c3c0082119101603480340300381a43d03140024502d0308104541c005541c00b406000c140a032000600c03d00c10601d90084420617140001005000329003481641001c002d60700700782680385813503950714103181d4071000340c808448854824080c4000000381182d003d28195001035030040b184040c10102c60410603280d5016005450000308240300140f03603540214074070454010140010500f50b0701e0b0624a5410f0884100349941c0000031305c10170030062581c0d001034218021180c1c140c50399a44800700700400d280c0707210100c40600c0754030300040110010728622100c05107454030480f40c15548001d01100c10b00f05041000703003080b070001c081c11041d03162507100605981031b940711420f07199100c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 404344046 1250 404342796 404342863
    0x3150b0604091d0a031b06020906130e060609060304060f1b0906020c010908061501032405030606311e0c141801050903030d0e1501050a060c031b0203060702 69
    0x101c4c0540401c44d48182003102c0913900e10740350700050142c00c0040c20002d0b08400200d01d54800580000c030724425103018019a400355811580210080700d00524254142004c0384190000420142806a46544141c02070302260443d24101c0c0d148008405141039641d07014112450350f015000051096025001c4a54051a001e0064403102e1004021903660080704200d111a032020f45410952103010300d0940038580c0850303141c503100e040000c400031410001070620700f010042046104400306030b4000c00741c0e00041543c14100c407030f903000c1c04002010620900301602105100d49150728035005c0703011481505a000e400c02c1103c546e601c1c1d000c034000746c0d0719014500403c024943c01c1c0501d156040c41c40d60060008159520014040e00d0900d42080d0800c1e040700e001c034052807050380203c0d2500c4d030003002e4400d010303000d840c04480780980385040c0301c0f00030074000c00c1c9040202071203000d0680750000c0d2500380d00480320650041c100c0e48103180c4027800944402c0c0391f00c1038003880284088001281d03400f09 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 404345296 1250 404344046 404344063
    0x40b0706050c090d081b060c28050f07240b090702060f010909030c020603090c100908030904021b010908090f0906090403081f0905100501051303150b0604091d 70
    0x130304045443c01552500c102c0303540b1200e41c802e41c0c405864608000303100140320052141114007240341e00c0c0c00d440741400d04010201c10b113081c40f0500e290704020702d854104d420340d401304018030342b070989070001454144000d252480410050000c1c3c001d44101d511502d8010a100b0320b0180e8a048151b21058026661241c0a90b5001d0180800170018481e060680c0c1c08660124064580075506a0858022605990080d80c840c211034005450300051f900f007030b04500e400c2e110f00c0e15041c021035150220103510303070094100703140c130407900010b80c3c040b4183d1442c0394044035a8505c0007000308140501c2d042d00c0c241d005524030340c02001d070040f003050140307000c5c18181d2040c0c802922146440d56103540881d01128000e000e891904a6104040c0c83c1c0031605a800c0007802c680c280019190400f000d007003561562039484241003060401001840311000c64600c000c0300c4e405900040d0a034018407010016000d4060340e0307a084600858006007046003a00302075803500120f02d00407100c0414015140e2100040d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 404346546 1250 404345296 404345299
    0x30303060a0308031905040c0504061508070503060a1e0503071e050d0201170403090305060f04080d200f031f0509010e130b0705070203070603060f030f080d02040b0706050c09 77
    0x10700c4000c20200c2c150000540d40030304a031409080b2202d0785140034003242e40940e0143ea00207002a01402103090603c42c40000c1c04403000c2c01603419210030001803405000410410070003901102060154850481c50800780024501c0e00e43c01d020b05100c0700202d0b4400c0e108082c401d109a071000a0f90f0101165402c0c002400f0000301501c040c100003c2c0041e00c8004182241000240c55018a1010070082e190740510721a98440f2141d601c0c50030441e00d4018003030b0842e141a403006041c4400104c2c88000c80d0050408200040b9640f8044103010302e01c1541c41914030381310240014803e01c211801401544209040060b41101d900c0d449401c5d40151024007880d41c03c000c145c07005100d00d5809400c51603004034240c207402d260811b165991203d100041d914400461008140d1204518050055070082e100300c1c80c1c10040d25181c00340c80b1282000c03902c13003c1d0844031120789400610012008603041200c50601c25583c5968400030340b9803c0d8400c1c04107440e02440d100120b070b83c094041c01240e591820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 404347796 1250 404346546 404346559
    0x703020d05120c030414150a0e0f10020106180e030a050d0209100c0b180627070609050a06080702032502130e211605070f08010c03060503030306 64
    0x46900380502006904000d4550388105030019040c2d8032401c00508989800e00040d540f51850500d03c00201103050311428030a044050741c5540300748440003a50712100702c034585442090080e00c080381710b243c0610040f6800450064981c21842d4054001d203084826800c600615403141c92051401c40d8101405c01c0c3d42500300f04a140d440a11070806040d03900401d000040c9012a141c0019040c01207610180c400f180b0010104014440f015003c10f60021103000700311001182d540700d90380c0350540207050340310026205c6003a80c80040c038003003100d1250210201f11600e030703919044013400380041e5100345840344c0003900001c12964070030340c1010302900d070b950015428511807048840318a804141c1d048522080c0002c05005070359414040340c40ca01d201080008e03580300d142c6500341091100300c84400e00000c01030400003510044011659295005c82d42141d03100781c00d14069080070040c0c1d0080c6100d0b0040000400c1d222019407005405030070702c3d01c0c204822940c8009043c1c4034001112029401036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 404349046 1250 404347796 404347799
    0x80c01020c0622090609090b0c0304051c0c0b0f10120809090a2901080c040f030b0a02040e010303020609071505090120010c050c0607030908030712090b0108060a050106080907 77
    0x120f002c660340c038000f01d0400d0640315498596108400302e85071035108241c01d0751910056800c0c44103c0089680117100e10b800a480e524144c4c8030306035110483e25256044104100c80407181c0d503c2082240b841c554010170400440c02c00201c061240241503030032100003140e895001403480941c01c0c040540d254001080e908180154080001c42200140001d40503520303000c1200c40c00c40c4070348500f05c0603000741e003036040d441c0650800103020480040080c820100100030610900b81600140c0088a60020540742d0550b14459204083e01950740f14002003d1030200110805401055080c0b01f201c081d02100d606659850200e69001c08080f00000460700801081499510402614551101c0c01002c0391a200c0c5044030340e07084400074004031001803000300d80d06101110900109401c8509803800740f180c011a03481c1c0540901c0054828000c0c002e60085094210900d40c1080c60100d0b0090305007010f9680d12010036484880407a01e00380c00625000002c1105800385200354004d8070414028501d05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 404350296 1250 404349046 404349067
    0xa14010c0308280f1d19080705010e0604050f030a0c0f02031204090f0b09040302060601110705040c0507030e180c1c020403030309031101020403020618011b0c080c01020c06 76
    0x104000c3d100010308500000c0703444a000507480c200340744020400002800c2402560b0300000c171001c80004900340d0200e00d14044414800042d141c0d01d14503e142c802e140c0301140d1903c0303030062140300b0740188130f5402c0408955000d2008200a44158020420b0300c3e4a542072415440d224818020780001066414008101062280400600c0180f02078110380301251038840702c11240e0002c0d8414800143c03110149540d440c0c0c1401482d4851400380c81482050405640194aa50001384a80c0c104480f000e60404841c0081104c54000c0c80d001e032040240c001e08240c0200650b004a4080c0d01103045410800301c24106070800f00311114500d004180103072600078075080580d220301242d00411404c074082c8050081c5600c0108025446500c0c0041c01e215649000f07080b950b1441c41c06082da074414401000583c9a000c00c84034201d45490b01d40c041d20018800684240051100301c02c0480c05503003807201088040400c61098501c1035003120146000d138001240d03038020303000300150000011b10401280 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 404351546 1250 404350296 404350307
    0x110307060203070e09091b04060b0f070f060204060c11120718060305060907030204061a0f0a030e01020711040e0c1302030403090308070606030308061005180a1d04020a14010c03 78
    0x11510340b0300030325500c50400000c5e64400c2c055410700040e400403903404514880c0c03030000381c031040020f6506010f0b0f24540140000103010f00c222981c0300840c00100e1108000d4030103281a00b0f41d500c44c0046440715125100100301200401c411119040c80e2681c0c04514a41b000c6030603100c100355002002d05d1403d010130034068800d034810320103103a921000044002407007405403c0c4900d00c08002401028994010001654100d074010100180101c403609885c418000880c0d680d526602c20459886140400480c010b1910052100341944040780c540104814005400d43c07a031000c603000d001c02598940100d032248174204140e50711500010f08050307450840e030082c6034041e0003410040e030340e2580c0c0e480c3d203003981d8000c1004890050742c449080c01010b401000f035940080c01910710074500c0503581030140443c824490300d403103a00301c0519030605554030b80c0342031000341804c4104102003021104900d620400c0594089104a0180c2c4000c40e020440f5161507405160503901c9280c1540e094409a54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 404352796 1250 404351546 404351551
    0xb04060b041118190503060106180e090a06200405010c080409050f09070e07050a0804150c0c03020c0906060306091312120c08010807061d1008040b0106110307060203 73
    0x10402d46905104408040320b0000d40204040e40d841c4041500082d401c0003240f42d030480c41c6072130510044509008503200001da06064480c01d0400c52000c0f460941880d83c5881d46510001d90303943c13418100080e45c01c0c08100301c800c440c803e070028072419443d81030007404640f403140305130b80c00d0328103200c02c00440d03101c8c031318560881307001e000200c0c0761503100e20f410000c1e01c10803100b112182d28120284036080300d040000800070444500c4100c0f45040c030700e400500c00d101d85c0b8115030400c031140380031505001c0010401e1101660307401c410040c000003640098100c4c1c0c03040c2c10580c05805040381c030707130000d040036080c40f0700c075100041010380307190b50310410410b54034400b80140e402d50301c00c003560310005038170820380569014441d1641d12134a1000c00843c000c0e00e11040507002004000d0703004115103080080c0c40c0007034880e079091864801726646003664031000d00c2500250302070703061040404020780051048d030069010b116001116038a800d41915441c4101c030403800550300404c4413a000c0ba200c2e078044d42c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 404354046 1250 404352796 404352799
    0x71b020a030506040c030c2907060e0a030e150301081e0a08210112030c08160c0f060207050904030c020105070305041e060f030b0d0b100506030c03010614070b04060b 73
    0x1988681c498690515050342118100c40100002c041441804820003244004101600003000040584101050301030030f0016400d04071000840e620003088203d03084940e90b60b004c1800c80d0601081c0f41001001002d0400d1154011200401c6041401024404690582d07040d000145020b0140022050340764402d0264040319000310030b500000100c6902c014468042c66080c0e030246140b9400203000e00704c0040e03001c08001c403095130001d40000c0d00180c0c4075404175001302c02203454039103903804843d400440100c01401a220b041c004200402c42d02042c4060700c03500d508480d8a80d40364070031300c0301803002a00d0107404034040c0c00c1c07050b00641c403c200601c0f50611030700c0d00301d05040e41c8800000e001d580703200305031070420b00507c0305008485d40034190000c0c10703036680340c18000c01122101240344245210000b8101080034000a640c4000c1511240010711014104980e0392030154801a0182c00a00a160001719290700b4407401041603819030341415000400100309450700d58030640103201400015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 404355296 1250 404354046 404354059
    0x21c0b0a06140a0306030b1305070603051509040213060b070c050a080703062a0f0f0509010c060513050604080a02070806010e160201060f0b040303180f030f1103100911010305071b02 80
    0xc00090054403065002d04a81900380848e03070030078509642000100c1d000301d82014940400c120b01384901400c11020f809003a05c050000b034440d40007194647d02601c5000083c1400c0000005040100740010204035005c0c007403d0120700d458004206828803241306507580740c6e108082c10b00201748160302400541d021741c004200f00c4007070505150082000c0140003008681524007511a0540100720515108040d1030810710700521000007034200350b650f8030064407495540c2c00146414040e2081d4400301508401107800740c0c070b05803908150030750040b08004014003811200182040000410a05a07180c8981400e21a40c41c01d0904003010050180b580c02c6648505000480a0604c0901c1c0d015000d551502c80e0395900b542805020b580002c8d98071654021a03030400c005030020781074428181c0354003030046201182d940c2052506400f500321380c554940140d982010403034101d07500c5403117100d101d43d41c86e2080409480054049a90032100700000c00d1200003031114600740410720032079503880148034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 404356546 1250 404355296 404355299
    0x1b05010e1b0f0303033909040e07060801061101020c030d0209030d02150c09180106091d060307030f1a0c03071707020705010f091a0c06060d05101509021c0b0a06140a0306 75
    0x280e01482c11b030b40300c14000e50a00040b18095801d0034000c2900001d50b030402001101d14100006090f144140720300c1c41008400049900c01c20000e40440b1500d00141c01125182c00003289100000e43c44907040b50b20a10a00a480d881a0300200329005141140f0741007001e5503403828440c1105500504095900000d00f69581d0100456086030313601030031640c0c0e0b071941c01606001000301d00d100f4880b004130010100f401000110340c0c00007281780559074007000c03010380c015052a0203004035650035103400034081c0000420010310010b00c051445807040ea030b25114449403040110721081025201400141c0103001c00740219401041244140911450034801321581c40354410300c0e0806405008007080d5000804c117a00c00720030020b4641007171040740c42d0080d2285907602c05598401055805584503245e05100b40c0715004203024500415070340209540e03a2401d89031440c01c00d910b09480c01512803910201010504007203240d9030540b88261100c02000040d40c401c40c580f500070a02440030035848000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 404357796 1250 404356546 404356621
    0x90c080708011a1b01050702070603140a240b0a0f0e01170606040503030703050301051e03070932060102060f060a0911090406030308010e1303050a1b05010e1b0f030303 74
    0x4c050382e01e40c0b48000004150a00a80082c02c0c484aa8000420141040300764003401e02d80800f0389402c042c00200c00a0044400411201c1c055000390041c0c1555421802c00034600b844c0d240100440d0000780e03288413041300202401c0c1d41d00b084c242009030014007500001400c0340201c0516a4114000401c481e0900390786400003490341e0300081c1c00318006600840100410b0424a00003007403940000c48401e001200c0a0209075164114440c4040b0a602c0360045900444030070619103180c089403102a28803840040a04254002541c0d094014455a00000e0080b6025900b00b4080c1400800b03510225150034a880080d00c4140340c0d00b8507001c070403c55140c02d036031640714190081d4820340382c6d29560740c9004030360816103600030b0446c0a941e4a41085000082c0d000040f40c1b812880d81c00e100b812403800000c0b05c010756084500c000c0142d0318004550710784000004007110007000d81a00d600f030560705c040901c40a0480c2c0a01c85415034403e00c04151904502280700c404035240c0107201185e2002c43c00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 404359046 1250 404357796 404357827
    0x12060e01060b18060c151302060403140607020604080d27060615050901050a030914101b0311030103020913080f0a081e07050a020f0610090c080708011a 67
    0x340880408480042c501d0b040d800f0011400f2903007801184d26034100120500d850b621207803d441c111807a20204c900150411040b44000ba905c030350068841034035070f9181d19184d000340303980e41d0a098203485280c00081c1502d20005999201d550704c819040c0c188007070851094080c02c51483c80b020052201c04c0b02669929144030103001407030058001188551400e03000c00d1030650780804a90401074200b00b60750580c6d810904482c1400f0251800080c5d00d0b40d982040d107215074405800704847d0140d82100600c44a60790000c06222403980c4044203554800300e0150119189240d0850320031409000410262400382c000c1070740004522040c070010142560b17421220303030040e28050b0307816401190008015501400655125100b81d02414580301481425200313101d008142600b007050000714510031078801e004140c08440103c007182da050078544900320301074255000310034801d413412290805c214803460500380941d2880d00c410803ea400c1c092155034001d81e107450f04212480070044001c0103403424 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 404360296 1250 404359046 404359049
    0xc02040e0f0a0c1a043b040c050109052205220f0c050a030b042003071d0a0203160509010e1002010b2d0910050a0611010c02061012060e0106 62
    0x880034010030500303280c0e40b01100e5030a9011124000c4041c44207100810b82c50102c05400100d80344c1011b245190382c8040044940c100d4056040d00b40c040040c8005c01403120307030300000e860090707c0303606c01c00c0e84074818441300045800301618060b04428083c4081041030b031000d50042c0c2d0201404050002e0910a01401480e40f081255aa41c42b42c400c44140480b44c002c840c007a120490340c1d009064656107c211031820003030809070100c8030030f440f2000d00c408110403200000c0406070590314080d0b40e60200701501448801001080403044000491803140c41c82201d00c07a017403400b4000300c0f4540110080380d16420081300a4148050078050380b0056a0701d6035200525a45640049404621002031101c1a520b07040b0091210fa042615150610f540d41c1c1c0e0015503803c1510020416a65566814840740040d40f1103900400101d170003040d95030b440100981d0454104009124004440c41c0c22a560507044860324442c040008003800f00d140008e01e08803040b170090001040304550074182c1c40c21500103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 404361546 1250 404360296 404360303
    0x80a06030c120c090b0a0923130201020601081207030c08090901150f03090305040501031509060602030306100801050d1112010f02030a0e030403020612090f0a05100b100c02040e0f0a 80
    0x1054401400c1000d800340c600003400354264180309005505c0c0201d034002d40107001c0d5403d600d44540340303000c00c074038036a1010800320300c806290901030030b0444941201d802e602c40240c1c01402104000306200b03d0004903031a2003a103080c0300c00d2800c0129201110305045c40c4008880b550410401c0d4007059071180071013400380041942c075200b00c01e504030340a4240c00c41044103205141c10041810301094200701907030304440c0203007000304203003a104042469442580d0002c1c1d90322407404101042c1c01754000081c5210b5407003034448095003505120141d03a003000900c1001d510080a4800200150740c42c1c9442504801c042c1c40800e50751480022582565200c0c05081e00081d030102c1004081c09a50007510300304050140958035080c2147c0110b113117841090481808415200d02150b0542020018405d401070030f00281c8000e1070f140d1901c592201c404a00b104c04150034214145018030f006010300590084a450b03000d140c3d0380b19030a2201416420880b440c0b14040c54230075002e400024001d0203403c522 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 404362796 1250 404361546 404361569
    0x21504030806040e0d0206011a04030c031547040e0a050c04020f0d020a0212070c0905060f03100b010203040f0f03060501060302030106080a0e101a040b0603060d03080a06030c 77
    0x1c0120602c004c0f250703002c00c1107801e50300804031070107500d40108100e0706445541e41a048107455029441d030591040e030b03000403d032024122001051103d0240074800030b64000c041400344801d10101b1a6a40300400c11420a07050f507000f48000a020341c1c4020300c0300114050244100000c9200010102c1e02d002c08140320a81140000d0020800103008141081b402110308504084c0031105040f51400b4550007146003aa000410112040c002c000b142c18186c580700c1026038400c3d2626140c0c0c0030350342600c10001d20318280b1000c122949481203428800d246c0190041c5500e040310400074010780344a14006065000401000c10782c80c00400c42480034180418007921045d00e185804405c440d4140c1c405000c052050005018059010401c1c0d50001000000421894140d50710141000c559a000203c0c1d140b038158105210450b89924000450003101c0411901100350700303005c4284011200241c0c0304e002c1d4041c05000074090078000341c00c04040300e00000c03802d0301c0c0d641d40110340c0c5454109000345507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 404364046 1250 404362796 404362801
    0xc0a0b0901030e011e0905030d0501060f030f0b0f01030207170c0c031212011a0d06090e0d0e0f0409050a0c060203070c06170402010f11060a060801290603070215040308 74
    0x50700b600070b030b210f000e0044000304420b89105d100540b28460711301d500c0d40f40c141c548035540c0601600f041507488440b1140002c00180d6564040030b00410307501242e040c0407038186070440031084114810602c0301c450103015083c07424282d40044000f9400711000315003841c1508605c2c0c803600702c00c00c05000e09103041c4004004c9030901030100740c580440c42c41190b040700000c21000f4107040b404845141101c2d03030005400f14003c07800501a03e0341c001c280580280c0340c501340b030000b0b05540e20b4004400360313200714040c0d0781d9507101340d80c0c11109005c25002071074208042d900d4201c400d0a0641c0881c0210b4010815908a10002d5403a421820103c2e840340006134804145282404031a01004c401401141000b25101d20f0601c401d06141c00000d00190601c000500008900c6001d40805d0054040c01070030741d0450b150454826000300a0b5000711095580b0345000c03a002c0004000320014001246042045080503e100308481607200400c1c903001c41c02010182490f40f4000524240200c0c404e4442407220b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 404365296 1250 404364046 404364049
    0x80301050102150c040504022b06030b060402031b1b100c0801080318010e062b1a1f020106211a0f130203160602070f1e170c0a0b09 58
    0x2c0400081d0380d0f03030b00c80c9641030101d0b00c420f0724110b4040313a0382510050380340c1c3c0e642c4000440c2e104081c4000c4a01d84044444a00c541c1c070030ba403041060701d11440314040c0f95180e80050004a0100320341c0d007503c4410411060700340c0b00c1c4460140620541e002c500c840130300100c0b04e4242c180b440e0f49400c40a560788811547d4003551b04150b015003d003003408002c0d400c1c500b47c100148030040440081d0b034148100c29041e4480c540b1000b0442d0340c036012000b1480c5107941000d819405101070302000d0701da803a1a05800a07040e04414100c070a52100040000f03a0155a241c8401a0f03000001c600405640d618200011000d1000e40482c800c2402d00900c45c2401d806400c103241c000c500e401d40b58021840c8081003040d40c107074080c0081d411a40d41030a04640140302d10100e8076004c40c9860403001d2074180000001c01070f60014204040c1e0303032007814135509650390305403803101026102100d0034541401d200c144983c0c40d54600c0c0300c6482c91240f007250b022441490116484400e02c1d00314214400001a00c0c8030903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 404366546 1250 404365296 404365303
    0x60801050c090d0b0a090606080a02040b0603060307031e38010f0608040c0b04181b0c020d0503040504020d1a010e01080109020a020109062408030c03030103032a080301050102 77
    0x1c0c0503075584610348410075000405003150680300801504004000c190304a240d40d1001300095480311082000544456a00e0340d80da944c507600301d10440c105134031a100381c180300c401d6a002e9003010b0b00500800c1d0540c0d40764450500e00394020381c02a9408205035020801d8117610400c4a842e865580e14400304a444144200405000b20703c0444281c400401620240000d444100c46961030070185035240c7d0700e0628081e0a10703034005031142c103010038081a440380080303c205404010440c200440b044bd41c202241d10031508227440042000c103401c1c040075050280215596a00c1282542c2c50640c0361800075080381c010344048800603680760381e055082c4010310401c0300d4051090a103258805030420000308600360501840300a41d4000c0b401e011201d001b5080b4038044e6612041c288144032984030a02e569400030380d60011003203004a8001000d0101004031070031841c119000e5846c2d83c3c2192800e581c989031000658803800841c102c1e041c0303882e03802c08500300e0031441504140c2e929454036000920303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 404367796 1250 404366546 404366551
    0xe1903031701180e0102090d06053c06030f0f2a03060402060d060e010e0f06010f0804030e0d080313051c05180102010908040905010e0c090d060506060405120106080105 74
    0x15000c09420040c0f00c01d010700214100814890b400103e1002c07001c88410f40640503d40015403c503035050190001c200154004d40c5c89285030a600c1f0095000e11010b10000b141c046202c210340000c00190380c18141903498241d5400003000d012141080d01d100301052421150404080081c0c101e0b4030804804684a04448004103610b407914038200c1d0504006a250000500002d1003003000040e0700c424911150407003c000c000b01107411000f90303136134041e403041088202d8007140c4a0000d1000120158004d8190070880082c0c5e0381d07401c0050740d859405490f8500b02c002030b60341c40b036100401100024810402548500781102500941120910707005150206040c07a04026059000e0b44691840d07000040d680340705618821070601c100310310f00513030040900c0703180600745020005010860050b00c0e08a00d04803004841c0c083c0c1940e0b103030080c28a060007a0100d155010461541c820082203052b007080340c1000c40282903503e0a136454002441644450703020066a945441003000511b801380700c0c080e03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 404369046 1250 404367796 404367827
    0xc030a0212090f013002090307090603080a08040203190f030e01021f0f02090a080a0308010806040201050405040903021c0c2001020327030a2f0901090b010e190303 72
    0x18202107040380010104821800c809040044040217509002d00c0e542019920600319400e00c0340e49019110700c1c9001e5842502d40328000c0c42200070029074501c051045604403500103030207505003400c00b44125003401000d00f082c0da051045031111503c61440e03150440c8240d01c41c09903550444c14030319000d8082c1301e4003401c80c1d056421403041c0419092180c000d40807000a00d440010322494410540c4000380241d44415404c003044050200d400800007500d80070040c026101c6d1b410741c5e03980d541070b103030b5908046500070700040051004025504003908100121807203801500d0040b01152421042d55807440c540d0030000b8050032030401400040200b4410380c81816012000d109805400030b55284182007800c180c0742203202c0c01000e64190746040e44044c0b680203054414000d05410f0944038518200b080203060050038580518103421102d244203842c0d0b024000003001c0c4e103410141c000400920500c00d0501007080408041551007428000162a440035002d00090550034000c0c040c0030b0481200d07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 404370296 1250 404369046 404369083
    0x105040f1b0c060e06040c08070b040b0a0f0c060524040204030b040b04140307050615010c0c05011404030f080703020607141909090e0607080604110304060b060405060c030a02 77
    0x228005996114001d407800010704080070b00081c00e20f0701c80300402d074098600b0315038010007050008002106d10003200701c448100483d002c0589074106240d0505c264454400d1410080012114040c0141c01d0f000b403410850410f00e600071041d85440b0141c880423a410f2031049180031070841842842c00c00d514040d402035404504143c195514606601e0003d071000c1e180e03101d800002410024001610092480d607902a00c1d02c50b4038a00c0c00d6903950a041da0038842c60511134040803d6544180c0780c0c3c0c0d401a0704510900c01c03c500d004010359448080b8060001c820354100300100104800f2000b0b84500c3e417288980030355400c402c3c14000c2c10450090000d03010400c002400264151203081a00d9030741c485203100000004541100f541da00000d0b0f4444c1403168104034003110594404544c092041c3c00e151a01602070f500d0b007081000305c4011440300d0405510a202107800b061507544844c0b01135401074a05880c16840d030700040c1407a0410503041103d640000b440800366a8103000140440b1240c0c181d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 404371546 1250 404370296 404370311
    0x71e030506040f020d0c090902030616050d090303060b041805010803070b010e0717070201020910020c01050a030e0c18160c02090402010e0301090602220806070f05031902040603050105040f 83
    0x60340d841c0c62000d071020f0060040042054103665948004e801c103540d201c1e00d000d80590741c90f4050400742100d104240d102c0d02a520000d1410440032050050328070465681034505844081043c00030f1441c00016420503903600c0300403441c0b81d240c030010000740c02c031307d07050000c00d20030119101c099941c160040c1d100c42e00188000f0380000c5030354101c141034410407400807480303a9a016041b507070034050890300740c2000d4070601804940b9406600400051b034081d07650402030046000c003665a016808502e0b800070300f00b003100b2040f0502c01e51001d204908450b0594185548410000c0d1101254607403022101c13000c8400e00c2382c504803049005111403124102854100c9241c0c0000380d45150003000a030610809100c04041e6650030f41c4070351030b00341d8040380c11500c40098900c1d14803e94011041810160f400d200081500306001803414440d400550310046a134145c0308080b1400c4d0009070a08003150000c0d03440701800c40d032030b0010744041c10b0b4039540000c05600d8001080150fa199151555402e85040078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 404372796 1250 404371546 404371553
    0x60114090a0c0c02061803060a020d0f091101030b0d0f0605070906030908040302010e220b0109081609240617061903060c05070507120209060108090d0c03051902071e03 74
    0x101d041129011101107840d00e00c1c04645d03031b040c80140340d04580d05005480400c28807203070710782c00b50a1201e11442c04008030f800750041803044501c2c0e818050500444085503c1c2103600ca40c211103402074001e00081c038144180d03603a000040800020807500ea9031148100b0001503030141f1141e00404a605e424800c0380003940380c1d01603900c40c5000c06410402048803201d010740316484c440c3c40b89040b4007864a8101d88040000c001015401d110b0f600040c441c650004030f000000071081c14031490700c0c030b01c50981440c0c418844000c0c500c88552408200f00b02603072a070113002002c1c44100810031034a48000701408044454410301c03005140c3d601c5040f2140d414a105880307504040c00f0303203a02080000d40304803854410b90f82030292481c014454402c600000c00c054900c02c114a0020340b0a903003400e0103172140d100654048008030380c2d030f440320b501a191860b801885160303400c0300d01d8081c0c1444d618081c81d143e1300c24541d0621411480140c0d024520030400070034a0714080982c07104003e0340c65070807800d5a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 404374046 1250 404372796 404372807
    0xa06390206061909020a030608061005090a0605150304020d080c03040f0b0307080f060307050d0311010b090112061a1002010c170106200c090f01060e03060f0a020307030e060114090a0c 81
    0x2891030450b80c0446c4403415213000c0d90100015002c2c4208407442440d00c100151850829400740c1c03400b600f5002d001c900741d800c0a01030b182c1952801000080d020308a13020710f4503d908000c10136a030020350400801c0114840f0002000c00ca0700c4030014603a183c1c20007401901c1042d00e07034411501c03000d0800070003540079804500560081c00c01403a00521f41c403070a0003c1c6c5070078030a405c11a40842c44000344020107400c00c560810322007000c0c000388000800b0204002820009204040c08060000072440010f100c0d5801104000e174843d550b14403c008080104980c0e14005000e42d000d84c0d0740340c0c100020250040c160421500080c40c1907005ca605150005104c0081d0480c000300001e03103113100d42c00580040c400b8a0401d00060311854417032503c080386411101081c8140703000702d01d140344a10054140450010702c100702d00350700b0005540342c00e0080300c002e50004043c4020140e40d8420402010418080d180c020040510711140f036403011002c00418034405080805e1440c40d1001030800107030000b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 404375296 1250 404374046 404374049
    0x10e0610030209150307030204091b02070e0a14040818031209012d03050f07020a03090e0402061605071d0907050919060801021305060a020a063902060619 68
    0xa14001d030321501c00c40081145013600d010680401c440220411000542c542e000c1c00481c0e0b94540f00f404150f107807040000941c01002c01c10001a0000d1a0510041c0385525032140c000c02c805200040d0a6481c2a040349c1960b4145c80450b10140300291038203181c0400091826010300442c05403404000c18500850f90348500300c861814030030012012145000c14100c415031030202d02000d00025403800000400402c0f08454007000c81401e180420901840001c0f8040a55819141c99088904082c0314845403000240f0882c2d00a00c00c004940221020b00d1201e541e80e4415801410568105003440740003400800203800810544c0d0f041005203070000444500303d9106641c12955511055007601c102e455003c14440c1140c202400010321b100e05600624010300c0300f100d8030700e0080d2114100300c2948501090880141d00070064100803d0441c0e12900e2010422101c1310b09506580d100304050b0b4640443e06800711803031000c011400b40c2c0602019178441021180340f1106910075001e1074006245 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 404376546 1250 404375296 404375329
    0xe0a0c170601030b040905030316020312010303051b0f010c0f03180609060b1023040b0315040b0d0507030c0f0b030c0f07020d0b06010f0305090a141005010b03040b010e06 75
    0x580001c03070200d0b4003c0d07010245080b4003038818444d03030905083c41c999075070090760f18224601c2c01011421440b03102100307482c00e041250309154501d1b441d54070300325210b4100004007e910b680da4291189860410030030a901c1c4603120001080b500032180002d40070040d6070050784181810400d51407001540341500c2070b00f5a034000c0000a10071180d0410a0040c40c1070b02d609900411000051283c0540040f0701c00307001c07c0a445443e4525000c40c6400c3c13000d0065100b51003401b030b02071020070300384d14441d5042550544041e10008080200100184605809550507543d90b0000c00b07003032082c06840b460100c043c00b909644c80c09030070b24151508034507110003080543c048902044203e556200e4500316552260000d00890442e01c050400c1240200c06403001804180c0701015840c00901074010548165440401b409c182800c40c2c459003640031182c0d4040a2030b004092104e56041d80302d01c1194046c4c40442560b07074072482d0519082e405200184c1200c00308107182c1c000c00509541d071003483c6102d1900c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 404377796 1250 404376546 404376587
    0x603020418020c0102221404091a060d0b0106031416050a08040f020904080a110601060206070f020114010b0a0f0507080906070812070230042d0f0e0a0c 67
    0x14045400d030090082404c0c1c0004080010500000b020131b0842e180c0658100301d824661200c062001c04c000c4030480000200700d030816640080000e0544494944d2001c40541004d8182d1110307642c041c0030b803500740c0042010a40d0342200c54410412032900c5503002c642e0010046024402420141c018003071495980c00700803464002404120780c503811420303481d0340a800c4100078103080c9019800383d04240d088100140b1441c031503201022000840307604039260341d0081e0410340c4412100702e54203070365645001300b50346d01d4a494007240000c6204260082c20000e2000b07403580c603420801000c2040000c0c00a04002052200c1804608004125120b1703500c1150341d555190002d00c0e045007240954018045415503900800009607000300e0021301d004c40d0311038480140d80300d41884070766007180c4002d5180558400d001c20f10902c01554080411205146450703c00802000044200086650050700110400c110308003c01d55a4074484da0b00300f0215103040c0581016040f000300481101d4001032034055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 404379046 1250 404377796 404377807
    0x70f08030c0c07091e18080c0f07031208061801060c020d02030f070f050303040b030f09070f060536010309020a15031e0c02061504060e010816060302041802 69
    0x701400c11a26108442400d50f150f50341d4130300b4000000c0000c0c00c00d200c20648402c4280070034a007244691402d030100c580c1d01c405042110b071102071a50700840c1400030940301d4100c280b10860300c10440f2000442c07190510300143d031b03103202c4000c1042c000030300400c0c0142c0400383d1210784e0740d000c0741045040d1861031521520010580c000566652011030010703415025254410174104400310f15481a43c2c0c40e00f49000781c2581d10002e15940380714a00c558045a00e003030020030b1015099403032040c0c102400c181100c6131079485504103204d037003241e4800e4000c6800010705640c44c100036000c19044802010740000303e1000c0e280c048500302c031180c0d240c1d410541c3c1c0d85822030031540c81200b8400030b46022841c01290f0303c0503a8015000304603445030180d6600500f00441d040c48014000c207440404c05501070b001d030740c4462540071100950b6060255106485620200b8080c1100ca0480e009019045c0141ba415190403031064408810707400680405004000c14008500203d0003001d110309182070043c0e842 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 404380296 1250 404379046 404379061
    0x70b01150c0210020c09010609060e09040f1b03151401060e12100911030307030c1401020f1c0510030b06010c03091a070201021b180403050721090605070f0803 70
    0xc03281d0450003580f01c0503000214980550003d401d0242400c00c1e510b1316080d9880c0c00060716004610312904000a0300c011100304c041c2805c0c3e84a542082c800c90209920310050b9841603100100390100804082c0390000800a1210041e54901403281d10102003041c02040540903802c004140aa1001d200c0030140d620f00303588403409020b040c0c600d010305807906064102c6201d00940884d060546040b40c1140c186101850007004172901c080d80350700d074440c40c607405585028a45100b44040c480a5509100d03803034000340e0300f80003400c03c45025800a500d0b20301e41140141142c00c090649403080c90086014400501418420750700a00242001601d01407189412a074003d800e03008400040b070031080300e1404002180160490794800d03002d0300c0e500d0b100c0b20a08100400160350140e80894440c0d03469a0444071030741c80300d8000d4040d2505030b00e040c0c0c04d44c03a002102d0f90f19145001705400c41044c5402c40d640c1c81421a0301404031480d0040ca8145981c42d814a0148580b04c09030200c400040400c00c40d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 404381546 1250 404380296 404380307
    0xf0609090a06050708010f17031801051605010902120f0c0613092301170a0312060312090512010c0c0206160c03080c0c040902130b1309080c070803070b0115 69
    0x559120b0001d003c41d1a0102004020070303000c0c810451010720b0098080380342c46102566120310003241c0010740c1811f0b520102c4540024003512840d042c0700081259504a4400e000081c444034003a80020400d200c040c4107006031881191400342d80740c0c04c06514020708400200c1c0c105111142102c4803510744100400b0612111800c0e0700507201e032031400055050100e9119144180c000b1610442600c1d070785d0f6410404807080050f4100d0410ba0014a00761000900a01d86004000780303101000420726107030398a00c0c61980d5515029404a0510b880c10015464650040e0130000c0d0030a0003805416407544000d00b607041210b0340203105240100c2c4040d545e02c0e1108440d20940d41024503524019a40c0c1401505540300406002c41802011100700c070701d0402e40100007489a02030b1417641c8100c8440e0041000345516898240d1180400400030075864a40c00780048103401203401e10b9894245042e003d140c4141030340603111356002408060040313a03916005a0448003400190b000028645030211034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 404382796 1250 404381546 404381563
    0x20406020a032a0c031a0402030a0f05070902030c07060b01020c060904111e0d0b090f0105062b0c0306050409020d0816080a20060c0d0b060403050a031e080f060909 72
    0x700f84402d284000144019110500708882c0240700150b03442920b0314a085021404850183d056803020604000140054442d522028007070008c4c0d80d074071a04c0c0c1300c46078207030707441500e40300049100821a50240320301d61249100e000070900040c002a4040e1001c6102c1d4018940c08500c01c0d075888000400720170032079007214840c000d40d807108005140c0040d014809a00803405048410345041e000d8042820440a072901882203428440b103030f07a01e4001000902d0303028898060701c14644981d0031024040301c1d02000020350601d50040780d100c40199008040314650f40c082072282e0300300808000981c03616140444055085030318255101088030f0000711222121308020020000051030066a650200d0183e42880310705400540c5990040e40c03455840d00d06854401c19810b04004402c1c5480c0039901400320048050690f5003001e80d40d4540a003400000501a8086041051340c4e9418006c00c101c0c03000080381d5070501c4000380c101052905641d08005101e18001d03110100403520501c002c101011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 404384046 1250 404382796 404382857
    0xb130204110d021e03010e0f040311060903091014031f030f0602071205030405060c160804080a050106080d020307240504140106051503061c081b10020406020a03 71
    0x2e0365580703000c000c00002d52203160780101c200e0300c180680c100a402030044904945038030130300120640720030000c3d01c900c00e00540b08401740091580c070001840000c0c05094070403280310019640350041c401c00e105028124405070f00400410304a80c0340e03104100000d0b69007049600c40c0300c0c004d000168101c481161601d4102400755000013041d80c0400c511a0005d180881c4540032450842035609800d4945000a460040080d04800001104600b036980948a82e00c0d4400c0402541502e81d11055943d40c02600140200e8110510642c180542402803400030807008006102440128800079142d00035003900600582a0030b10950300d8001440d5141440c50400b403041001c1d04092a201000802e40034940310a542040d1000402d03140c00c400d030414040683c0ea8542c03071559020100141d030007500d400031401c1e5207880344082c0440c05540c06410402811b524011245040941ca1480d00c10010244c50045004000074400303554086946401c01d60f250820f01410103d10b10900c3c0d80fa04098200c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 404385296 1250 404384046 404384081
    0x70317040203071802070215070305031b1b03032d010e10230a0e0c040506090301020403051501030506010b04060518040902040c0f0810030804061209060c03270b130204 74
    0x44c02c400341c16402030541d41d101320b4801c001e08030500c0c3d1021840c00b07402d01c00b801154013440054161610304082a0b07100000782401d9140950012070700b4900345850400319459030022081200000311000314110b071104200110f110208000d054181e41901409550704520007440400c07100400c01b4000c1024003404050f104814400003203400356140d00303050007072151410400000300310300f086201c075010f07460401c201840c0c03074200b1061000031390102040c10341541d800c100000224605111003814805a00d800741c1141d459420082d14002041c0c100a8010404210800c0600d410904880102d0021041c1121038440301e00002c000b0940000087c0d0050304003041c01000c00c0d03000545120208445e280c6400a4035000f00040c400c00f01804010100f0030200001c0c002d4a0040c1c21000e2000302c10200803079603c039203a85c0e2a06507802d00702c048010070745480c10750000d01082c14040003040f18a80d103070000c1e001c0c15100c00000da44050702c20317801800c440c8100c805545079a04100c40301289560304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 404386546 1250 404385296 404385329
    0x60303250c12210e0102060703022b0b030f0309010804020f2707020106060504050303090d0c2103080c1227030c0706090b041215020d0f060603050c07031704020307 72
    0x4040c001e414149250482d01c160400400f9030150b4420310032154181d0007050240e071010403d80003540201c1075050703840a5048420142c14540e010360b00601e018440102d80c0009a8007498a041003c91350414540c005204412069a21410b0960700503011621900302ca17030350348013240e000b001c00c0c840004080c2c10000d6000f071180e142d2020038000c2c1000d5000700f003c140c3c5d490044981c0d006a001d0301d6890307041003042170114942401643d821b9401802c032603040582d15020100000008610614102c078407441c0f29052507080000581e104525982203450800c86002881d44088010701c6424801d203011140081514a0065040d0310401e90003101d98646800b41e0f62aa01d241900c90b00c0300040300c0c82800708464002d542501d044600b503680f100c1b00c00b0219030310030040800f0000020503442d0300340585140000c607401901005440030400244d840d090443c014280c2d038005240400b0290b04014500c0001da014401290104200e4081e411545892001030b04203070075540035000300102d854a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 404387796 1250 404386546 404386553
    0xd0f05010513021002010902011e03020f0304030c030e060301140d0320031b1903050309010b1c0b100f180b060c0618010504030522030209130b060303250c12 69
    0x180b803080280212041d00d040c882540d801c07801e86504503002400180b003070800b407141801c0004035a0954a0500780542020000d22078140150002c0f101039000500401d021410f040d00b0940003d46110159440c40ca10340c117041e0b06190031810107903480d008144a40c009001c0c1481f0311010161941040214528121600f10459803a040452507466840420540d0200d40c00c00061100c0c501c0000c2503c030b001c0900a8806886e03940004004030780e555200c00722500e103aa0381104004416024613903040c3c4207905410002103180006140603a070080952040c00880034010031201195100a00080074012030841c1001804038150a035400070702c0030a49a07820640480d0640c4111007003c98105070b022303040d100e18284d0b18107940280c0890020402440452142c04101c0c80c11030f000c2c0348640d4140d03034942c003240880300308803800481621450224000c2288581081303800110440046050070140241480c034441d04118500c4c01c04c0c001554801009148074840004180c02010824849030505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 404389046 1250 404387796 404387821
    0x7020d051f0603140a0302120a110d0801030308070932060f0403200901210c0303020303070905030a110d0c12060b090a020a0e0126251407020d0f050105 67
    0x3c101e0704105203034400400350000080c21201c043e0558020f00f04e02260b280b412285510125030349080151050640007880d208000700000c40d00d0340d5444983c03542c55420000c20f00380000d02990f00300801c99400304030384114407960300501018240c40c013942056155046422110800502d501b0190100d1000080320481018108070303806035529195400d460300800d82e2840c0f02c038810951100c01400107000650802c0303400301d0450070704000c01c01e040070f05403580030b48525150301c2140142d00c000100601154811003020061200341c004140c0303000c1ca80d0710302226440c81c410705c41c0074242c0c0303205103428800c0c1c819049000701003540d074840f100803050604401516080016034014a1002c001c00d9101040f8400c03540602e040c0d0b9251b1741c604820000448150318000c1408030b003040c4200700c01c01d110f08800d9078540594440c01c0740310030034040100d101ca2030114155450062044911004080134541401c80b00c61560449900b400303030300f00345801021140e1080c0c015000c2d620344410488200c8519 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 404390296 1250 404389046 404389049
    0x51e04080c010206011206020711040f0c181802030601021603050a0303060b0c0c09040615060806030f0105090d080601050d06140a05030706020703030815040903081f0b07020d051f06 80
    0x40c107039801d1007125030059982c0e4100788581e494001c820150040800d1f1164040c0606c18032172500c41130740302c0703840c0005015100446142920716a0700c81d1047c0090340c018081210342425a150408124030785031074211000440304401d1b440a4000000843c5d5031b209000408884000c81c2581c1c40017900c0741081990b072904c2c24000c401203440e050011401c07000200550313200020303240c000c01261480308180820203801400c2120b009896102c43c001b12101501d80c01c0c0549425070b10021203240c0342c42010300e0300040c203249202c203900d40014032043c51000300701404042c2490410b52907540303030f007001210329105010b08070004034980680481e590491100c0000350400803070710030000c541c491080545400c403606c20708015074071100701000041c2c0a091030550240c1031110180c04001c0d403101041c152043c211040340040d01c0082084980040e50394454804540341c40d021013614244508040b2600ca0400040c1c0b10b040b429503030200f002410410070034600b61100c0880040481440e0b58406468503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 404391546 1250 404390296 404390309
    0x50607030501060e0d12020c091e060f0603040f030909050a1d0f1c091a120c041a031f09050601110610030f050708060c030403091d0610051e04 63
    0x1480000640d661080c03c4101404000030170403502480300ea500d04c80303845040b0740c1000c00e500034010350b44d6490381c401401501ca4448600c024040311a0890b42c40c454543c020940c600c21844c1020644458442100b07895005600c40802c0701c086001d03040940703558006600c44002d441c2172404221142c690390300a1290720490222101194022100b04c1c1e80340e0650b082840c0043d4072401f0082a4001d101d0b052190500c46420211065900c601c0844424441c18040500c0c10b100040c0d40205544540131091303100c83c42c2800d45082c02e01307040340c1c0040070140c072456043c6100040b0101e17420305003041c114246a00b02c51400516544d54509a001410b02200c1755404a1010101014021008902c4920507900350303010b54241070a40d83c9008203a0b54101c0240c038607105a81c0d0200e01494208000d03400740503500e044a0b142d00c0c00b03160003448210340740c200e100849101066502483c44141100f508154211992541e500c50303c0c6044843e4011440f4074110b2945c1200710791400c4030740c08001c0c400d41d40d6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 404392796 1250 404391546 404391551
    0xa233601110901080c0a081909050109050f071d2404050a0506032e020d060f0602031309020414040b06190c051006060207060e1309060506090a110a050304170705060703 74
    0x21a0000e01c3c46038090030106d003001c10011400100407403889545a01101c010910000b8440304540b550f9084a01c095070886450380b040b091000080800c1220400801c1c02c25518000c004401020411006d4054070141c0d403c05440800d460b40d600807490b0788008500500308001d5450a551040050441501c60600038094940d05080749181c1c085601a402c041e441000b000c1540c480070100203501c00800c080802d55074150106145004180c510014038a6134001c640360140c0c041c210641c45240c1c1c0c41940258070400042010703059042d480604030408030f6001070515200404900319108000b1003124003105044481d6001c0d40290042e000341d0b01510844190702d00b60811102259918001c00c009688001d00400845d44944031401280344050103184e00e03004066061000c2e103a40203803c885094546040111600301a110258030405480e030900c004a005541146a407241041c100d041090000c0003030240402c16084061030f0540d140207540c0c4086505165880324416182e6100203030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 404394046 1250 404392796 404392801
    0x50a0c020d0b0c18040203090705090402030a0605160201290906130f021c18080c010608100e0d032c0a0203030316090f060509130e060a23360111090108 67
    0xb014402c1d80c0c0f00700085801055000d007800208800740c0bd00501c00c076450300c242490b250000c0c1050145e14000d0107507041c1d040d540c505c0020043c1c29201d041440c401d04513442442076030f144000815040440d0b00c20381c2e20a15076191000072449004075114100c034283d081514a4020303105a0b4020803039040c0d03101c4a445540c483d51142c5058070580c13800c02c08172821140c03113400410004c0000b40104540c8800004060f40c1e90741c000c9040c00381442c03c01002990b18000700c4a1108103121138112000d503172604011984002d40c48220351455019001c140c00341c4181c041c1c040c24401c11424400540040440e07440789042c84054481c0622031809000040c00010000780800d003000c3c010702910001c2e00d449040c0320554052108403141c00c0a40d030343d204d848021215519801b4000640156000c1c01c002c540c013060f01c03807d10316900c504059084001d00150402c40d40780c15080210895480d80e008180044106882d048c2265501c2152640c1c0c6504e040030300303d00700152100405041d035007030b26400b403941d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 404395296 1250 404394046 404394049
    0x90123031501170a110d0c0207051804240e0f100608070303051e0405090403020a03030c17160c0506010605070c0e0c030708101a03180d050a0c020d0b0c18 68
    0x140f003c1c58003110003a08200201d4000111a0400c2d4900301544c01c3d03441c288860400c507a42074035003859400001d600105428003481c2419584890b14110b01014a40c050516030385d80000f02e641c0301e40c40c141808801031a00305903807161700000a02c01e41d03402214004941a002c4e43c0e00c4d00c41d0205181c1d045807078002e0014100c24003054403421240c054683c0740c106a00c07184008040703a41d01314080d4480c1000c12011415035103c0140c00e00460003640101748080103840e02408460107581c0d401b040c0800d4062448107600c2c400002c0d80e03c09008400240f074203010900580d0050907580d401402e0703024920001c940d8640c81030103800103a0040f845000d0712030b9514180c4c4c0030360600745c40000140504000203403216004040311500645d0209409090550b81d81e071202115442da0498007803c40c002003800b04140c000a5000c54101240000d82000410213001514038426001e00e81c041c071030414032010642d61403090000d1400e80094103c0c849191142a290547d481824440311102e0000001c400a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 404396546 1250 404395296 404395307
    0x10020c0606120a05190201030b04140405060603190201050d020c070b0a090504020a0c06020304050a140a1a15090915070306031506290c03070605041421090123031501 73
    0x40b1360801c0240031050350551410022100c554400c0e070500d074450004003d9a01d491180e51212002d4104100c06402c051a01a05000000d000d59109500280788540f00300301001081113030550900300b08c2d80c0c0d03112840190001c1d028880140603140110303480003405002c0d1307030002d0152210507515000d07072a0711442080200e0003281e024600103031004800d54001950b581c0215000f074010002c5440d410000e540d40d010302c11882c0e0640b003a03038001c000d00104000070825a0082d0343c0c129140a42c65141540c2c800b03c11500401d0f00620460000d030102d09a00c0c010f204006425034075514071041e034548007101034040d045900c000c88468403503032401040b0454600c0340c1d038141d50b84180452a0300e12800d042101c0c650f00640003d000c118200319034809054100000c2000d14441c0d000440e0b2403609091040c10180342282182040e009981c00c0c0d6240944003041e04150481d80c2c40040d03c580880c001203520306110a4100d00801d2403250621410006501943c441c603204407640c46005020b1004444 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 404397796 1250 404396546 404396563
    0x904091b0e180c0d030c020406060917030301031511040e0f0f0108010b130c0905090a150f0b0a0507030905030a0c21080d050c0f0d020408010c03050402030c0d020310020c060612 78
    0x32604684040d007810703d00140d060704d00a001e880c00480340070701a00041c04542c0154803410104900c54170810a004404058840d0400d207640a1401c5614540303131218104920070f401c0e030549644140343ca480844500645000e0b004080d03400100d4545070f08080c50b1130200382d44a481d0780700c040c0700004408405008070318001c0c00117480421034502441481c4054040700c031010003070020204010907107440b260403080c070408504101089500d005140616002d50304e8002402000a00714103001101e01d000c100c9840ca0000c1c41c00075642c0740d203800c0450fa03109103900007580c18060711908009120a44e1803041c29039010b1024100b82c0403000060741d0264150782d00040441105003f90031902c01c956009547c0b060700600e10b140b500c0c4072100012030356032180c500004002d81c00316050082c0b06091058102101e4181000c01c00b5040c40e800280d907441112030b40912030007030707200c0a070110f44061000d481c1d4080c400744199280d40e0061000d40d2142c504070380450240007039658004c003901000030b000b00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 404399046 1250 404397796 404397841
    0xb12071b0326160c051e010207150903050f0c1603150e0f0a021e03030a050a02060907051309020d02120c150f030c030703180b010306050604060513020904091b0e 71
    0xc26880300e14041d1002c034580d13071003078406000e204d542880b110999100c000380581e2480005982d05143c1c60310b903820300c000380c4080801c06d1604c003000c000a80c00108840e00d003059181a10f17100c00c01e1060903840c02c05011103040701c24801e100000200074070728a40c0c41c0129024201844245071416856a035044805107010541e07005580030405070401c1500301080300d070040907084038050310201081c80d60340b00c40d02e1540000c2000602d80000c60341400a40c2d003000c1c80c20060003605207090300040314148803815400751555a100000115905c07114050901075020b00300e46440c034a115601504da0b407100b10420300441400c81c1b0010102d0303c82e01250402c0e503050503601d09540b2240b0500c1c2c0660001088102895520175407414495010400d0b5080c032032242132841c2c1c0a6045107003032400e07224041c02642c0200d0a03c1401e001540d5407050b0070304084568400140c80d41131400000f0050081e007080a00501603c05d182050450480030070010b942c15503031250025250110a440340300310009050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 404400296 1250 404399046 404399071
    0x40c05030715030b1f03020a020f061e0903040f170a06050a06090f1e0b211605061305043204020103111303030c0c05120705090603070b12071b0326 65
    0xa143c061b006c0d5016260382a014030407690001848144985407400030b655030039550000780ca00c3d40405210722091680006891f0185040c05d2401005410341d801d01d001e030211403801c80102c0c4640240402c03440980b9504040c0034011400c1540061005003c0d90207201201d030300b01083e2034506622401056041300c40e6000c200395203400000f40c01d00600e00484107952010014001d10201d6000340009410a1004000761004e80d032188000c84480070260302c440c1c01588140a620808a9042c1d44102100e20913503022034a9044280c80c402403052505000340b045416584460b0340c3d604408000c0d111701c1c403c1e201041420701d403084c1c01400d80102030f00704480b044080320620001344582c0103030580e41d00c542c6400c1c40d020b44450006960048010058038540e01c10380f0300f041146040d014440d0005c40540150020782e040003501a4a0f00c10000da002580030b030340c2d000c50030051081c1101e0350090f6001c03605020a03a140d190083c492144041c1c04c04c4c1e91611b080785450400404d2101e0350050142c0c1226 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 404401546 1250 404400296 404400349
    0x1c2a050a0614070204020c0714011e08040f17130311060909160e1215060906030a081c0603030c0507090b10260108070806090d02060708040c05030715030b 68
    0xc480960f00c040c000301d0b0815024400c101c11400c0411500c40600704550307a0b10110380d4000001400216400d0607261034100d201101401550003141d42074000d504100c090101c21007504118407400c525800151000310300040789480c0300013480403441600d119081403060508402c0030000f680c0604015554841440c80125640e41851084141c0c980c80509217000c1c4107000c400015490780d080380200e00b40d0303081112004003c400f8031007425800324003200c001806090000100ea5a50342d04031f8000c10001000450b1056200c0d0010380182940c4070301d6003030250300e489280080041203003010444040c42000c001244e002c0c01401003000041c4050440150b2000c8d04d50121030102021041c11041314402c000c8503200389038641804c1c003034102100100101e9181c44503070392070403c0081c03e410321900601c20310221240d0128000390440801c1c98441c0c4540c49a003020703200240180c4c0100c0e40751054180015150074180002c0004028503281001110010011b0042d40b002c000000d4078504403280f007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 404402796 1250 404401546 404401577
    0x10209030d0f0909021621141e0412050d05190309060b0a0e01080d02030c1921020c0405011203080a0c030e06010803030901110a09051c2a050a06 64
    0x90812440da91600d024015511302980c0c0c100c0c3c0c04100d0314065541c8042c45802031040504611681146158078000044c8035600010090700b01c090303002030114000110500740c10418030f2403ca10b00c42481c040c640d21591410048804080b00d0800ca40c14064580d0204540340140207480c2a480b50070004c0e50301071720f2484210b0050800301012100b1f2695a4024401da4035010001c1c0040d1011200c042d01d42e5041400352480c06484081d403400b10351040206400091000c540301d080076224152907140d801c038500e400c1c16416100c840b07804011243e8501c0310f19150303000400d941001c006907810045641c8803041c2640454000c100a0702066131100420901e0380d45034480e0034141418980060001e02107030545081450a87c400030b400c4c0d0012007888003450085c800c04a5140c100352200c2e01d844a4441d002d0103440759441464411040110020300440a0700c1000c142c81d5804907841488040c1c00301400c0040010300b000c003014101180000c41c05090444000041c2c0c2e465803100070403c003c046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 404404046 1250 404402796 404402807
    0x70f11070b030a0e0a0317010801022703030915220303170912040b070b010506041203051e1204150c02031e0d051003030e040c0804030809010b0a0609080609010209030d 74
    0x14008903a29580301360b4a40c4025091100c40909403080c0c0d1201060b0130b03120341401c1c0a20040e0410100303644104045a8000200b00307171850f80080140c0320500440c00e60001a055002d0300400c190850201d407082e001c5000e140008008a81220710795070203101d40c10482040302c00080c00000c01103010182c4003808950443c2016901a090710211094a901c034030030341040350800d0b44401441d40c0b001c28a101041107005486005d424203035200f9003414500000240cad0039190340809420722600080713082c0d00a0300c4c2da0451164001040007c1d507603113000c0300445080c41040300c0540300d6440c04070340d6688071281030240000b1018103a0040d401d00f4200c11a100704040b07002d41d144000350080182640251180c0100b61084940b00000141549581001f8108058004105100310701d0940955011034100c02da40742c00c0f0342c245c42c011206555a1380203e004101080d8501c3d40301114010024a0641c0002c9007019651080141c80e0a034441000e498240e004184800e54035411500b64452020b1042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 404405296 1250 404404046 404404051
    0xd1b06030c1205250f030b040203070c0807051203010f170109080a030b06091003060f06051c0f02090405190c0302070b0606070309030b0c09010f080f01060302090a030c0905070f11070b03 82
    0x7103551080c038404c22480c00140d010710f030541c1070100c1c6540a14440041d0544036034100b0450603581546103260a01005204e10212038000780300001c04035440e014480c0401a4404d11502542e0003a525612080b04401031255846074079843c51508480380c2c0c500b03006025040501d50f2001e01c00f424002c90318002e40c040c100307104250707030024003c0c803591070703a90744610142140e5406a100091645d080202401003102141c11144c2406010410503401c4001121100d05007400710b1030010740803002c0000c90010b44500035000d640b081c14074061110305500300e40f1504c03201e01c0a05040050b00e4401c20141c2c11390048850103001181041e0018240d0709040006100032403180c50210044ea0f00c1350344824548109507180c0000b4017010034031500c5540c0041c0c40c5081c0c060f850400510702e00c2c107170b10140b40e410414001c9004240d0080b60302005074440c80d105c58041e40d0300100500060381c81d00301407001000200c44079800100504601600036000d44580c005102c0d410000c0d1840504081c164912a07001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 404406546 1250 404405296 404405311
    0x1302010903060216230706021207080a030e0313140a0e04060207052a030d090e0612010f02040b030f0f010e0414100903020609010e0c0a1e050d1b06030c1205 69
    0x54010040045c0c905541400c059003010101c0f00ca20310900c0e000e074501040c682100003075500c241c0700343e80c103a040202540d03092540001402d0343c82117406c07400c0b0080c000100c4180300c3c6100c04a08082d10345015101c14060764030194043e0034861001c0304000418130303680f0400040001c030002107404191250003c1500e18080c03000c9a4000090712062580d08d840148150801807080310911000e1505000d00d5400300340724a80789500c40c1c10a404440c050001808091142400c0089201030a02c2134000000310364280304115200d82d170300ca014842541c412a10340c00207111090002d03464829444106050f15810104444a55101d9031342c0d0507540c0e504c101140b042d100c0c00200082c665a00c0c020b02071040d1295000d0308103814203440b003909440b80c1070008a055000f40c40c041c041c0d6110034540c14100c4520903c012121a500362800040c0c1081e50007654004c00920709072000d100041c40d001141c081074074403450703c640c1d03038100450403034001061550020381e4103010828034508507001950048070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 404407796 1250 404406546 404406577
    0x30308041b080709060504020a05030708070212130e060301060f1206020c030f0405040c0206042105070b0114031002070b07080a02090d060e0c011103040303030e030c012313020109030602 82
    0x4055501d0040c02540d42c0c00610303203030301840d0103000646440c001c00000705806e440550030040c5900000e052804018241e104222852000030364540c400c00040c0c9001c542100322a617103c9220100b0800b485050246d950202c030320201040b070700d080c140b090748125040485600700c65801c040c8601c0745480402001c0e02c01a800307000800d5440e00a00c0240442c0e0b851000242d9540d161a081c4019106604030b80415904044104408904024102e4408880c903040316aa12858004165010302403100c000c0d2840180400201c0d04501e00c0300072441022040741140d466040c581819020b0340700d4404001c141c202c4070004140664021038100380c125544200143c14050b120012400f4221807030780944281e602d0359004008000c5c02d04c9030713901400c000c0ca00303403880c0c200141d281c0d5a41c0c0304030322004040545d1070001d034105a8092003a20200607ca000074020080c41000d00030070002950f0440d50700702c40358400314255425030319006107010b41c1a154039000901e1500c40c4c8009400c128201c80b188003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 404409046 1250 404407796 404407823
    0x9090c1c060f0302010e01050c070902031f031a0f04111003020d0510050a0b131a090a080d08010902040e070e03031606021c09050615240d0516050403030804 69
    0x1400c1c001c560160040e00d10162880d4914000100501d09214500741800410001c0307100e64500451040103552003a1400b503545e844518001d05010a9078480c02101c800c0b1750800301c20400543c42540c140e102050028201c2d0715007683e803041034442035400501090700c031900750340541401c614290019074642070050401d50001c0c010740130fa51040b220f14185032486c02040c0024940324085c00c01424041d4800c6050080300e5508580d4044a805041502c16000c801d00c0d0481c03038180b003100c544510181c000350380d4036a04e0004690340c400c405094404100b281d8000716460090303200380c40c1251040348001c5a03640707808601f40c924205804505825010030030405520280906040e01d0280c4a03060050b5103564035400d0101b20381350704031000022410126200d020410002c0c145800400328071112142c00c030b071503001810300480b400030111300070702c00100040300e45640300140c07400003400ea0080c07004d0341c2c0b00c110031090850318511520215070144018030120f0b2040e10055030041c071a040068440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 404410296 1250 404409046 404409097
    0x9050601051309020a0f0509132a09150c020108041103070b040605071110020a0215040503011d0c04061a2d040501020f07050603010308030712090602180609090c 71
    0x1458207400c43ca004a400081d107501030b42d8001c1c3d0b01c00e4100c465140031420318441500080343c0c1400b042440b091507480c0d01e030341d0807005440c0803131400a030004d5612100202c4150f602425007001407151420104c021800d07010818060504968410b0f4140d464201c1d42d41c8999a541914500e2502c25801d4403c0080118000c0280c0d00104003130032190b01d425444100d1843c048001440c20050140548141d031300c0ca4428030b400044076022941d04417004501a00c0c1d048518020707000d80d40c01254550700340026402c040712800748240d034052101b402d650301c2070031410030300c010768006100308454180c40350a05e42905c3e100c00090956110a00250483c503074425207100b01c90040f10003210450200014108003070340e0100905c0c42065404805018030a16040000e0001d010520000d40b00e40000800902e000303110714000d005a0700030490420168403d828400020342143c40310441c4a0584000b203070760751410205236415800004e140c0841c80e6100e42010041e50400802d01e801108403c040001c107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 404411546 1250 404410296 404410327
    0x12080c07020306071107091b0309050a0803010f03031d01020c0613050d080c0610151d040906050a0e030720030a12020105150603160c0203030417030c0607180905060105 74
    0x3c1c000c1c1751340311000003100c150403500300540f5034840c814041c40d02401b500c00b138000740400141a09039080008404510f802c1681c2031040b80701008282c03540c004008612400c0e029040d000790380c040c0e611000f0442c030008100111202800b861750245c3e00950385480c1e5864941d000b04031520004c1111100f10355a20701203038503113000a4045030020350102d80d00c2e4000c481084500c1c4c2c007241400307040081510b4101000d4248951002480400007111074a4864644264501c0741e0758002820070800c42015040120003031000ba0346020640b42803030343d03030220350304000240e071102707500100b000040003c462200041e15014120541e014040c1684940c0400c0030b20a2408000d8810340012400d485c01c48603000c000b01c07669811510440042c014880d02d507020b03101b400300525040c144810050384500009245000d03a602c0300400107076086804910301030102c0a4a08a8089003c6035440e840c0c0c50340558010021070520011500015802c03c00304010b504101d07080350060505504d4460704401003440d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 404412796 1250 404411546 404411551
    0x180627030a02012403020d080703050f03090d110c15030a0905010612050c0409110405090705060d021209190f0c03080d0c1e02030301090f0b0612040210080412080c07020306 76
    0x140c0d6540e10094245512410704c5618003808051207411641103900184514101c00740c080d141800200d00d030390070580600e003202c80c1d401d60b002e25140c4910300b0110f0b4555030300404a103140006c1c01c168440300100c8000801a5286000600c0ca41d64000b5140740701c04142c0000700b10074541078840400c00041030003842040041c1c070441c030180d000000d080c100070349805116403103140541d01e480e040901254403c101050f1100781100d012400b03031074004c001c51030031005801035a0f02800c00140d844400300b41d0740c01000c1500100c03900720000d5841c2020591202c507004800790968508601e4040000e0a0544003280701d44291290321015403691180c10340ca03000b00102c1290203a6481c2907071802d40d00705400314500102074203401101e00a40300000d48038001803041541e95619a00e201e5000368844d08500e8070030745c01070043d0b0349407250150b55003100601503506078015000361003400340031842212013900c95900002c00d80c00c8502c00071001c440005000381034417031a03501030040d1401640d043c0f00560 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 404414046 1250 404412796 404412817
    0x120d0909090f06090c1a030420180c0301081002040f0308071e0c05042910231b060103030f0c0f141501050f09060f0a050d030305070818062703 63
    0x940c1c0d60925504101111090702c1d101c58046d0144104000100c5500c21220003c206000c0040d00c902c00c5400b00303140d18410090060340c0f2070307194100200a1300c2e020185040b078091108482a4150350000c1c0000c038070650040050880e1903000c10300210b038103440248282032080c00801c4900c601c0c090520041001031200312004d1441402c01c018a00e4a03014060000c1841e030400c0300610502c010503101e54012072604d900960102c6040c0303000380d014a024007490040140c07103d04894100d02e08080c0c1d036000d10b41c3c0040016640380410f21500e00040c0807030690f07038903840351003040c6017140003543c000c01003280c22240d540030340c10101b0000d012880c02031400000000140041361302203000000701c45050b000140100c51060707251066660303010707643c1d42050702600e0014021481d400850040e000d103801294200181c0d1940d030f01010341c5648060721a10304d03662080580d4448040503030b4128100702c1204220781c00303039011400c8040c4600000c09003501445400000d02c00308001076065401a00109 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 404415296 1250 404414046 404414063
    0x5091b0309010902130522020609060703030207051c02060f0a110c0a0c05060f0403081305061b250b0c010e0f0109110a03050601030b0406020702061305120d0909090f0609 75
    0x500440c01e01e2641d1040c42840785901b0f001526006040c0d050380d40030815003500c000440700600c419521600d08031303519068054081992800c1c5814090069030203401c0c00c840920901c81b00501144810148803042c10040d0b000d06203a8807214010000c060000d44100011a075a9010460381c9049000a109545161014141d81c41903814400c0810070541e01450280b00d0030016503070800300000844054a80c0000020340b00c071740ca0100128075807240d800482d009240010503007600c64030050420340d0305039024101d5420034403040002d0401d4a0603400d4680e88040844180020007200003e0000b443e4100d000007040980f802c106484c16414031030400c1c0e0360b5564644c20003848159004452000401c0d110b1200143c59a5202941d0340310500c400341c11550f500010a040001d40d030102c3c0e5050350010074164603000351104c40c800e0030000c1d00c1001d101d01c0c48220032101414001c160f0710612035964030382c6c0180a1134150000050003206030300311340501c404040000003c1d0703141704105400d80a1500d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 404416546 1250 404415296 404415311
    0x702070807031a10210309030b010303031b0c11040c0c02090703050106020c03010912081b030c27010f0e030c0901150e060412080d02120906071b0c05091b030901 71
    0xc0b420f00d0345016041012103049030005200f00c4150303401d15900400c01c90510503003110036050845801800f90001442c0341444000042410345c5900008248110020b0500c02d9801000f002c4e50090102c100c010015a410501d03240c1d030b440c0540c882503401105e82480c1034400c1980d8005690b04404071901d0b0701080d80e4000600100da410045000411000d80003082020f0301900c0d031407401200c1d030121404000f800000682d41d0355124480c11007043c0c0031080c0e00e0310780c20b003d13a0810f8281c000d24001c00b0080c0001043c1c80950b80c0018200d0030515040e1101030b0b9140140038100ca0b4074034100c0141350180b00e050746003596a180c100c1028003c24100b60181807410552000a086041d501441c9100b003100380014044002000030390904940d01c0f4054554800150300d511010b80210501c0d1046c0b07600ca00100000c400021400728402c00c500d6681402c460000c41c90141c9040c400034000c0e000c00c1d0801c205000038100404004d8001400d90001c02511030344948261076540100c50b1354a03141d444011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 404417796 1250 404416546 404416583
    0x3070b040506060409031704060e16082a0d1e1a0f04150b0a170307020301110c070504110c07061107050d1e0309051509091302090708070207080703 65
    0x642c3d03040f10b000c460500152000d5240245420340c90381a41456020702d001142c20041c0c250b00203610203900b10150b60800341410700c840320b8041c0354403a48503117000f00344400e50072810b801e0101845200d1901d0304030914503d1070a02040a550f90b038221606100b44c0390462030114540e1039840c0c414801d2401440304070280c6c80e0410161005000c3c21318000315881404005000228105071040d0084000202c03800f540e000900204015441741842d43c0030321009159484012004051441c0264000e0008d02c0d41140c4c062850f1041290703041c06d0340c0009800340000d10f01070304011101101000f0385070408485015070341c10700c1e50035448100401c031040c2e08040b00d1700c010b0142070028030b0708840d500d42e96052600c1d0701101805107031035042c1000143c49001c04142c010b800c40005408054000300f10003500142824050b8000050030b07219080348030008040e0242820340340c8007503902820102075620f035102c040c4d4076032002401900a40c0078405004c0b6072a074042224500440c0600d0041c0e908103800030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 404419046 1250 404417796 404417803
    0x11060417010e010203040f12030b060706050a05060d081b0724140c031e0c150a1a0a0b0702061909050f03013c0f0506040b010906020a17070503070b0405 67
    0x10700d02c1e04244d005000300000701d8110175842d4240c0b5080f48604400380c00340b000480040c00400e11040d80a40041118401d0001c107510503031040113841c0003009540ca440013005004101014010400481041264003460090030100e0320316400c03001f21444983c568082090b2035412040065054071a43c4032282d00561020101c2500700444084c6403078805080251601e134410003e404a18405585042d0340c009078010031940c10b4011001a100030100c58551540c4240701a148910194189000811b00e000d110000824140c0c1c018610070700346251010030b60090b0022402681d00040c140500364a01c000c0143e00307500d00340e00d503a40403e6142400100090104072480c007074000e07890078560301c0001c00440c082444100c1030b8034900000f00c01040000300035068205a01100034240503107444030400582245001d40f078201c8080c0500100e110044510b800300348190b500690003025030300d02040504035008489140149910300d096010713151689140e00000c41126140401c10410061210070b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 404420296 1250 404419046 404419061
    0x3d090809090c0304030804080a11010c020c0a0b041d06040605060408101107021309110415051809070608070507140607180b090603060303092701060311070305071106041701 76
    0x1c11190850500740c8001b010301c0d000402c001c11242d000500458502c1c024042154100d98a200901034800c02060017915030303e0400c20b0074003956011a01103031740c0d507144017540d0680700000e10710003001d0960b9001c0304550901030405600b0aa9422001c2880d45a11000b00003419580006040e070b90070382caa407030040300c007202d031204041c0a00340401c41c01030f6641e8280c0cbd5141a0800804a0260042d0500c1c0383c4215064070a0b940c01407422600c41c9112891902c00b100b124402c813450420211880e40c1b40c120306030101c03040ca4594010030070a11074203000b0b007001c40e0404140e1800f0380c10301c1c0903941c98000b00707140040700c0f41059124600300948164400c911001203100b0030207000f806407400d0140c88a1780500d000c000c5c892400440000c039aa00c040003551200800203080d21048568406040007030107d1002101941d0340303102c000f040680c0a80030720385544030800c0c2410702c2c2c2a81d40d1800c13181c0341c1151804413100c00c1100d210044039603880d000740002d0400f0007046c118041c07506100b030303003120440d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 404421546 1250 404420296 404420311
    0xc0b0729060a030834111503040f08040f0308090f0a21020f030a0b010806090f120f07061e061a0405061303050304080d08093d09080909 60
    0x646042007429159050540d0442e940b0030f449544a038815540d00d06610700850b802e145050030b0b580c0c00c000c11a03c450346160306074043c10000c48044410710501222551080c004000c1c03140400215002030100404080d0960141450740d007081e86032008080000304682c02a82e6000c0c0100e50401e1916002ea80c0f5444070000300d4068115074a00900d2146920812102d4000641c2ca50b2024065440300b4038840c5880c0f00c0101030b109800034514040d944407030280aa00e459214940004c0c02c1600c2c0000d9480380301021130018000d603d071040103481e26601182042c111003034144081c000185045c020301203031001103194801c1022208402d201212a00d43c064080c1c03901000e05580662106802c840546000b910a40c0d40d1b0041201080612102a80010540d2100160001c4c01d03400105407560800e03a42d9450714030a80f5400403850b9916000b141d1003011760f5240340344145101907000e071070900d105280c545809040f005040b00049039071410007038a8040c00060f00d00800e240035816994031008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 404422796 1250 404421546 404421623
    0x203090304170a020a0b0d0902060c070305010b0604080604020405071209120e0a0e011703090a15030b120d03050a1b020a12050316110106090501030809090615070206070c0b07 77
    0x944c3c00041035400e25109401c001400020240040d02c00c42c0c02c070328032080e00500229502c500083d030003a81c4244a11041e903441d46421612001031501c041220300b12660100280300c65162602080020301014003204d082c001218040360880031540984000103004e4020015640600790002d4000580060150300c03503090f2070b5007404110000712101e0f0640f901c169101c807144203004016451445000d01c0954401c40022000468180c3c0c124a21aa040c1e2680c05002c0e010b1102c041c0b10701100c0303180d56441035412600a501c400c0b8030a82c021940302010304408a112002c00d0903180d441601a25104010707000020321340280880c17511558070407071140c90440c1ca1840d000ea0381c001d450007041c0307981c000c100c2c0026640a0442c025001580076098010040000d565030789000034843d0701592351a4010b40f0f041000480d11b00e41a42e401e502d1800300c1155601c3e05000d17501b080110341c0610412a11041a00d2010030000155006400090b1081b01c90345800a290308001079000403040c41c1851401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 404424046 1250 404422796 404422813
    0xf190509030a1103040305010207080c1908070209041511091804030207050d05010e03040e060f01090b0f070f06020412030908070b0a08070e100203091302070b0c07030210020309030417 81
    0x41000040b900c0349100340c0740c081080050041c265043d84901d500c058103d60021030310105200c01c4030007c104818000301211a0b286406042440d40d0f080990040d203003000a00154007d81050f6000d030b6407140c810284040798020303640b0800111010345114410f000d401103030142490400d41e84040074a060741d030741079080d442e00d039900039a01d40b003901550340a461078516450400100350402c4041440c1c150540f0340300e035290300044111045c12a08248600700c04042c0d049154000c00300801a6422035180c00d203001c6510283c4000b03075012030000c0303a099010b01909008a022440680f02034614181c05601c1200d00b814000d00300c0304107800202d59a001a00208602a04a4129800c16140e800d04d8010b680c3c82c0c0c0d8007030760204a1259110307080f003180603d1118469010000304078200b4125100c0407580104000d0030308a0142d40c00041a01442d980407819144145025003c0c0500c00e00c1141e009082d0910715034141c2c2c005807a000d055a0000c103040c0300c03020b200728644010802c10b800802540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 404425296 1250 404424046 404424061
    0x10e0d08040b21042904050d0302180301050903090f18060904031b0f02130e1b06070c03060204090506041b0809210705010f0b150306180f1905 63
    0x2441036101d007224801c00003e00b22120106201021014110503829003607520f41418400210800042c0c040c1c0c0900003400540510001e64001d18040c03600040204008040d0a0b010b4000350700080303401f980c02c807129000244a56090151740c2c03045d40004051070300c407000441444585458240707024414980c0d1803c0e0850070b90402d5400c2c0d4800740841d0384031910b482d00c0c00e003500d81e80401941c00d0fa011800b07140040521514800500e8024401e440300042c0d4039080802c08221168170440d90565080302c4450080d000d0454503800090600801051a0842c6591011a800c0f4190300803071f01c035500481d040040d0001d500c00c1e0b90740048142d0742400f5403407540b102c0381e80e282c0e03107035a1201c11307c0112000300741c100ba1708001d2003440c50701c001381c09000d8000d41401c01400b500600001c0b0380640c2041c24481e0715113024000c0c0012260b014221050141d5121300f50611500010101500140e03a06002205010440e601c5030080110144082240c1060320a12050007042e240c1c40012500b0a010310210 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 404426546 1250 404425296 404425313
    0x1d070e09070305070c0807060c0f050a021b1f02060709090506090423032115180a0e0102071a0901060e01090c020106080f06090f0c0a030303020d02071203050105010e0d 74
    0x182030b8078000a15680d950010f45540ca60318001030010302001c202042001003031380c0941c2c107070798464a4035480c0c00076401d000ca40b10f110b40b2100030016040300030b04940c2250b040e140c0b1400c24000038240300001c08455018a51034001c004a88016440725042c40314881d00300d000c400281080341d90034005480c03d80c02080c2c0c03d640c0500005c04403603003400038200d40318582d02c514040070655400c1d03030f0347c40102c02a40c11060341c07045075581113021000c001c150324a03240114800c07076001c040c0a0400d000e06c042e01c0812a036800078034044d00c1c00c0d25201e42c04003145c020305c02000700912450901003c20895406015240740c000e000c8810b50303260600034448600200445811602450b9012905a0400d0002c038054515607200c00040d2141c003d1072040c0140c0455181d118111210480701c1c56981c20f090140d44150480185400203880c202c1030010a120741c008045a0b482d00f0340151810681c0e41d02c80c03861001c3c045e40c00c80001d56400041c4160760f4030032140300301a1022100d6003c140c4458440069 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 404427796 1250 404426546 404426551
    0x504060b2d151201080d17161812051c0810140a050307090608010e0a030804030c0c260105060105250f0b04080301140603070e040c0908071d070e09 65
    0x100d45245050101e94480c42d0341114503124096104001a50f50350084998600016401001040c0504c00c0d4a000900096049215120444410140780d04900e0151000b03154007802e80542000000041003400114041e40e40040c030647c020004441c1c8030622145c118000d0101d00100803509003400300740c4103405c0c1040c09483d01000081040c07510b0301d0010380010305035400fa5405000d5040005000c0d45103920800407500c08500030b1200c0e200c10030040b501c0b40ca1805d0000d0200313118a0200f0046445807442e03c401c94440c3d40b00b202c40a4540010410700f84104240e101103142e110b0b201e81a410082c054150810020f08010b410030010b85070004a4040071801c03d40f10700008188501031004c80c4000843c120307006880400300d41414280b0f031203d54800d00070b00c086042c021500b2507242c00c0850490784520407a03070322103041c40c08080c1000098071500d0469810001010000700c0c69000c00e0043c0f80062100a080c0b05440c018542a401860070090800061200e0202030345d249458101c000341d07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 404429046 1250 404427796 404427799
    0xc0604050c1c030e011e09080c03010509150408040504060e04061401060e0904051615091a03010e0603070512030d201b100c031a0a03020618130504060b2d 68
    0x74034080d00000100e50b1102e848607401c40350088846c0c4040510f0300440c840d0140c845402c142c40c0494070f20401e240c00e83d07400740d03030b294003907030004140d40000b000c1c4450040d0041d10a0490078505540c850009098440e640c000424048a000c144002c008651003469002a0424140c1103a5031404002030309154400c012507000b940064000b0b410440f09100d01d02003000506a0391414584078004071000d01844002400801c0d407603200854001d1070004410100700c2d400040c1481d513802c1c140030801d079900c0581050342502c11014003040690b5289820100709800c1c000864503170009181c20000e99450100001e80074909001009401002c481114141d11900c283c2c0c0000b540440c2405141c0350b0350f40c4014024034540b14011806590680010524102c5030b1440340320001e500b010080c5141d8140300084d80040c080103040350705c14007000411842880180107024290780c3d284900c007a600d04130317012070380f40303554601450f8549440c101c00074855001400c009085085040c81c0d07a03461042103060fa = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 404430296 1250 404429046 404429057
    0xa030503091318080406020d020f120703030b130b041a06070206070f051c120c120e01091a010f1e0504051305101b020c0102030415140c0604050c1c03 66
    0x103038490075081d0003041c3e05501c500014040c80885040940150304903014000042c05088601e1450902c0010b018075259070030340c0036100e41d9040101580040d80200d6048060544504c3c00001d541c0d203d0100408150b0710b1034020070010450020042180c05402000c2034820221000c03180649603402a1910245c0c107545169a500050520350f010281f01400203042d40b04905100d00c2d54040f03818500c103c84025211230401d12407440c0888103946595802c440002d400c03011000d0421110b4100161610510000003100181503c46401005000d20300c844c503602c5203070041000081c070610364070041441011003140d4030320051109917450b4031403207514492a20307000810440b0f00c0c050380c0a00002d60100803281002610103504014000c1c01440c1038021001901000b0514004901100c0f03080050b4007541c44c0c18240a6101c0544010b14000b000b04078082c541150320300380b4640100b031102a0180140311503c1e041c5092842c01c3c04402a42d409040d07100d84020f0017040042c0019034090749030419 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 404431546 1250 404430296 404430319
    0x309060c0102070f05150601090510080a021902030c1b090f1b0a020f120a0f140705010606020f0105010f050a180b130e0c0307240905090a050a0b0a03050309 69
    0x581d001e8040c980300604111444070000c420000e0020383c1e400803c03070920b400c40c416503a4800640303007201340740700786070700001903040800e0b5440c0f2551f40564070001001005040c691022448400c0d03043d0340c0403900250b400002c41c0310400c0b10812104078107141041d420192000c80e08040303503c01c03a000d4a0100000d02c01004a07256407954603c2d031200e11503200410740c40e20043c1000942d120601d506104150003003204070a242208181240c0c02501d050b2560400303006401c1040b50f14039100c1d4210f65400000303001d1a400210203001360f400400c8076500808000e52076603010303400c490042c1d100c9244100d00e11020466911503803d090212244940035500800c2441d210303602a209540409034480c0c2000100d52526503140e1100130213004010803598000100f005265a42100340640b603044030301d00350200129400040d41c41d001503801d20300b519000307545102003904540b055528850480d200d40070800c422082c0d12604c141d41004a482041403807440d254182c4078800c2e14440d60044125001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 404432796 1250 404431546 404431567
    0x801020f0403150908120402040e06040b19090816210207090207052e06081603061805030d0515040c0903061505060408010f240608040f051501090b0a08030906 70
    0x8076240c205c0c0c01101a51350f603420352004008252086074128800c0d86001c001c41204400081c8651145030300c010100c04540341c0c03000012140912030141c03001c90b41c441c05104009981880500702390030813200800c600d04401d251846c0c3da54030424491004503190881c41314020b9000603003204542003c00010303928240c0c0e01307065041246424114414041c06503c8080c6010a090540c000d598240d038100004c5448940441d01d81055000d0200d01c50714001c030500c00b080241d8403000a4040304250004141c0a42d07455a0031a0080d00014500755074441c00c00000140c1000505101380382100c0400c4003001c15071015041c170308039001c0900340b00c1c3d45081007081303070301079481c6980034180040250740c40342e0b0b5441c4158080c20002c6113213448181869250b8082d01c0000102c4020040c921384040b040300d06110b001c80e032001c0d00500544d852900c03e1042c40101d501400b002c0307000f005036032001265604114030340301a00c1030104500d0080a03101c00800222402005075000b85c1001c5840742d90b104403502 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 404434046 1250 404432796 404432801
    0xe0c0306130e1b03071d010e070507050f030405100c050307062d0209040b0a1a0703120f1d1c08100314030d061e03022211040e010801020f040315 64
    0x1009151984140c0f070443c8200580c641118002d840220100d820782ca803204483c40100200718131010100074a8001484407582440e80b1550000182c58150304001c2d203a154607149c005d81441d00401c54100017002e20581c00e000c06001c82d510140d05040c64181c1c6960741d000da07640700c0c009024051684d9050301c011089c0d03d00c19590003807071100c801ca9241300c048000c07040003540403005041c819481d29041e1411414164018800c81d01c0c2c90088100c01c0e440008180c00c0f40e44549011803c104220308014200c1491b80b080c501c044611102c00240250001e035051400c080708144110203620211680564440302240c0d0424405c041c503000f0450380320004881c440f603036640c000808040c015016250741c110b0001c09810419200e80e03044c00f4050b80c40c1c259004410b4050f00050001c9056242400035080000d8003007001c1103254261413809498403d050201c1e044c400f170400e4403a000141c10000c4001e80c80310140505000002185400e4034100c00d043d03c1e104504c40208411900b03e4800050300303665 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 404435296 1250 404434046 404434061
    0x4030207170d0206090105090a02241908090a0b060111070902030408030906100302010f050f0d0e2103100302010f050f031f0b0a0c14010b03010603080d060e0c030613 73
    0x16a2806032514044103894850702c24041d0310300140f0030030000a41d24070f4140910f60062041001828810f41c09030248202151000c14084103803c0b21820100902c196400425140c003040c0c240c104d555076690300080c00c0b2000580a911343e40d01c061b030808086540101016042002400c0c4958040020030703905003414216408400c04a1000c41000244140d110040d441ba00c0050203450056035600008036880040d400701074000b80002d00402c820602a100820b143d4041d500483e0600b1020b034890004d40e55080c280e29401d4001d8a0010444512004800c1c800035807151928150324140040540760511884060b0421841c1c0b10910002d60043e0110346980c00d018150a07901d241480b01d640c01901e14031400c55a4080603500064210115802d807440903d0340d80d248a50452151a40c2641e468100524641c40d583c43c1c0010155136000d02ca581c2c0254030440c0110b0325401e40e200a40201c45869000c0e88240d10f14500b0800408403000440c1d9020204503291a95840f16491070001807811 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 404436546 1250 404435296 404435309
    0x929090915040f05010608071d0c1c09030336240c02060c0322020303160309030614040302190f020d030e0a080705060702060c0a0c03080d0507051e0304030207 70
    0x120750a02003031110440d1500380741406800203200301390395903001c00e40d560200d10820a0103015400b004048600540070355800c0100b18ae0010300b4000000003070154611540c105010850b0345180350300402d9090700580007044030140c050b54154001c03113a410086140d055809840900b01070102c0300b0000c80e40d501c601040c24032414001e1440e418060000240480400d01015101c0d80000410030306040080f0f0b44900c0d00c0c2959145001c0d05c01c581c050020b240080205c0c4d240c00288070000c06c0c968000305004070280607a0b110380c1541e03e0360924604580d80307222004041c80c40380c030800001c83e0700010450403401d80d1601460a42d1441e080c2038030280c851100003540b01c0804900030082c194010034984241c2412070b00340c09803a80c2c8640055990001d481880d030000018072404001d032074038602402640341030707109603524000c5690303078410542410740080780c05c40e10225a400014456200c0d0581c8008541002407034940c0003264444038040041c0e00003c0c401001000a00b00761007070004074014000e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 404437796 1250 404436546 404436583
    0x4120c031a0403030b040506010c1b0302041a010e04090b060112060f030305030108060601230c030708040b030403090e0609012d0605030a0b0f090a0c1b060609290909 73
    0x1844100348080030542d400d500003410b10664010074030300b6209042c0140b105841d81100304038599511a21103812501c440482c800c014030010150301c42d801100c500d480c000007030383d0940c0081c00024100e404007162190150f480d0031a0340c400941440034050b0416000d00300480b0f95022005500b01614540e001944510005840042010342200c06141a01c440030240d54481e41d0364401142d00c48010440c1c480c1e000640c90080c014045450002d0600e901130310b06807480c140090304c80301d0b40c0354403980c000c0c4040f00b0000700f04018540c4c003414034009043d0b40f01c2a0000750034001c2c00030340f41000c18021100034980051010140030482c5280d0600100400c441e807041c66668030000d0b005030011142902c4550402c801030145140c415044c644104001700780c0c88450326640e01040013030180e00300e52410b0081e000488180c0300003100d0040d0846224450210740f2a0070700b905c4401361100000505a0b00c6008180f1410164410154041d604000e0f6a00e101554920304e4492034800520f5a0200c03203039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 404439046 1250 404437796 404437823
    0x9040308131b05130e0c060c1527030a050a0305130f030903060510030203070b030703061e03051b0607111c15060f060c080c0705151309020901020304120c03 69
    0x5020074041400c80c3e00032200f9080d05105101d18100b500d00511070100150021315001c0d96034030304a000b5004090004045032074944070101240340c00c20303042d508203400581c52b18002d071400c000b6090f1540184820006107003800c61301032024109000300754144090545650000d14560385111300002c43c5a081446a8041d0220781405019001580400d070303480d90804002400882812a08030b04407a800b4005084041c0707083c0480010b9040070741801c0802da120000012040901282040303081c1b035a804581e1894910301d0542c0c60080c659004031501c0004410f84841942c6000c10b8072542ca801c122a1280c1c40781a10000d82e000b12203542001070380202c5600300c01440403000160021000e9040c04128043e143e540b0b40340412070900c01d540000385030b0120040040c00d4030f8084c00d180340e404030031520029290380024031055081100c012480002003000031140701416540d00007010142d40440c40c1c54100740000b52a48168090030300b0012486aa1404125030641c400c40110b8104640c0681003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 404440296 1250 404439046 404439083
    0x8040807060f0e010e1902090a02040b0a020d0206060108010f0b1608040927050303010315020904050103150f0605100c0804050303041202031204231201051021020904030813 76
    0xc042d5800c60312034640c13a01700c0580c6401c000285449801c06803c1c0c0314a0744c031005038200070800c40000c04030f0130072580038400014030040d104054000b01d0b982d038015010302020080c00074648840141410b04101d1501d004000c1c0c11694007840c41992000c4e0741c0c5075603075103102c00c145406a00f00000200703030450016000519191952207003004ac201c01034001e2000c0034020a03000414840500605a900704200400006028a030820000300b1034120150034201c8100003c2c0c1100d209a00c00d580c0c03001049029808401240305140344040350700410000207090101254084803d80f00a8080c459840e4411003032044c5001a41c00410703004080b241d590362150202e032001030022008034001c2c4030750750810058485100a540c04d55400b001c1740040382064154840421100b803000c103811620743c2400c03242003c800c3c09894812070442c80d850300030078986040400c100e1006040c03251021480c030711020042c1c0c2c071280c14642068040c646100540ca0701041c070030b004203d0b080003d201109808051030780 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 404441546 1250 404440296 404440301
    0x90f01030c050f030a0f0320060906010501050a0c0501091208060405071e0908011d0106080303070e04020706020d0c0c02090a091a18060412080708060d14070b0d050a0501080c0102030a08040807060f 87
    0x802120f1a0a223000ba404110101d0307464500381c0e41000c058000c0b00041c0019407080c009490001e500e40b9210407581c03441c0e100e0508440e07500d1401d4421244030a00041c419421045064002c00159400c00070303407600f5a001001451801d81405d5461072940c548550f50348078411010240816000030810001c01c02c24800e4810702c211508030003542008000144040c3c04000e03a80301d0f8003681c071418030101b00c501c10030000750300c0450100d44143d42806103a85210716440782d480c1105098403001c1d000c9034140100108400000c00c50100d49080c030f024400083c00c000358100c8001c0d105114007415413100328041003100c48110004140d8410340c4200800c2c44000760707000f2501c10860312a40da540e140c040c0304441d0030004a41254019480c0400400052102c59105c04402c440c0c50070f592141e0b0305c070075410382154070084a6643c0a500c40c004c2c07080082c0e271413190a00601d82d410003441c04140c8000040d4490140701003d0050004c46c4001406100c11442110312042e0b116200304200f1000c003144400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 404442796 1250 404441546 404441567
    0x910090e04020112020c01020a2003031b09010903061802030f0102030705071118070f0f021b09151557100203010806061228080a080105090f01030c050f030a0f03 71
    0x304102c070aca0102e80607640100449029903039580741c001d04005d03070f28100180b40d4452505181000080b4500002041c0c09200e0314084407000a10070840d440390340105807074068408030001190744104140710300d01e6004001c9030a5964040c040500703034119000020440701c1c1249500c81d0504646c000c003c016075018213182c00010342038a07203605204140c00c00300d17a907000c044100070321a104a13a18451520302044426800200080d040490b00c0c040b401168042e008540b88079000340f800b103520b1180c281d1340c1c1c1c201d101021409020b541d40204400240d1004041c0d19221800f40700801c0c56001da041c5c000700040d42640c605000c941e030981c501c0101400079030003485210114058000414454504a04000c21800001d0021705440109103002a01c001714203e0200e07c1014840b1018005803030b48014000d802180d0329001e0503580f401d424004241b9000740707100ea0f4800324000500010b40f0f03206c443d109844003580c403c0080b00301400802d20b081110f2038050840580b42602d00205944100c040a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 404444046 1250 404442796 404442827
    0x807030f09290a14040b04051e0709140f01050409021c03170705160b090c090a05070905010c05120a0c1e02040e01090f020904020f0a0b0910090e04020112020c01020a 73
    0x300c0d42d543c99428821505a00010300c134526010000c5000308544050705030300f1a004009403003402e5903c214400003030f00340c0305840d402c58100d04c10030031034146581706003c1c010740003086001c103d29100c1003028040005019081c42103a440464000f552198907444400c0c603200400702e10076412509019040f8243d890001c005070241d0400240d045205400303682c0e11030741502e147d41c103203c2c0b10340c0d071316a06000003005940940300b00c5103100c400d940c40d441d500d80540c0c00000009482e003402d1800505e41c4086401550502015a01c2c402c00141c0015081d01c1d6507404400403a16401120011200c00f0000d010141c9001c103080c81e940c0211040709000e0380120300c00c80782000846c1802401d50b0a80c0c600c90405400b00d00400135039005428081e44040d4003500c002c01c0104180c000100090500400d900111442c00020505140c07034106044008031541d42800c004895601d8014010b91400300140000c1c1000840410f003810342510b501694030305198840259104d40300f81800500c600000b01003003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 404445296 1250 404444046 404444123
    0x50c0603090a0c06050414010512370f05343e0105060d110418210512190609060b0c060c0f030610110a0b250807030f09 53
    0x2802e9070080c02100d03880700041150240d46c2d40c4140322101c40000d2080f410b00003010040d242c0d86202c4054a410900744c13884080001c05404c1e0500b4102243c2c0003c02441c1000444801200228582c1a4000b8410010100ced0f83c07c48052030011114090020713178070030740b40d1203001c2e03d00d03074100031030800c4545945a03079818140c4034402202d540c240c9105640403500004581000004034060300130440781c001001d4804208540c03641150072903c3c5a00303606454261000081918424007804010300034490303490428289041320302007411032140600f02c0010780040d140100b24151984c1c2064000341070135002004000e82d1210140025402455800c1c01c9024032300000d40755240302c00a54803247c240680c0c490442d45c5080901c400900780c2c1440350144441d90000d60026642000407641892117000c688045051504d9030000401400f8202c500c041402e07440700d100f090713214000304c7e480300c640c0c030f0082012806001000010006400080c04680c81949500060000f0351813181c020341550103507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 404446546 1250 404445296 404445329
    0x9171614010809150c0a030e1e19030806040b040e07030302030a27140121020703140a171e1503060112150b010311070b0105120703050c0603090a0c060504 68
    0x1465180c2c501d91554030b100350043e80c04aa070700c1d9008000b03400e61011b2420f0008040324805a40c6180c50640407400042031208002650711410034020795000303044007069102e9140c4182e4001e00442d41c0205545d0040b60b99104002e44e42c1d603103411090503e00c0d4282039400068a0b030400070348a41c040c0d420040400d074040041c2c89020307490445010702c1402c0c0204c032190310b0b06202d5074441c00c0b030242a106042001001030460200c4064800c40390071540800d005903500200d19018003501e001e500c8150503640c0510152080755000352111941c54028280c000603565007111540843c10904e940020300d8504004219a500c5101c007105404003040b42104c506a80e102001c103a40480318800a00f0320401e4072015000003e00c0d00700318001d0b601410085425648013801c1061600006400d4485400c13140040080b4282542c42d0060a9200409020001c1c11511282d85d0344498000302801108004000f8151030020f000f480c100e00c2c0c0c003440c1100c0e035a5a0780c1000f043e503082402007105c0c511300d00c0304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 404447796 1250 404446546 404446561
    0x90a12020a020603042910140f010516080c030f0301081e03040b09060d0c0c020a0501030e0a031b02121b04090b1f09110706180201091716140108 64
    0x80c00c070301c0d9560041c0090724542e6580e4482d042100c48003681328441c0b440d5518414081c00888030648100f02c02283c82101510b40104a002c0342c2c404400c0d54085c484001180501e079030300c4821520424044095500c41c4503003807070039907224800d003041e0b01042d010225200c14404200401141202d00d44030444141c144081030999107c0c444803292101507004110400c07014108101602c040d040080520b401c06010841c0042515402c10f05d2000040303564505008521b4990889405040e01b842e040004550030900321b680d0300060b200140901012003a454408001624103002041d0301500510350b40714000030751561140054103d9a07800c02e4089020f809041c40d00c00c0c50a0342c5d0b0400c504c0b21054540c0c8144100201c7c5503080e40720f041c03c550700302045200c554001c10b000e580d1a0407000340d44800c642804400c580b002403005410428140110015070703400a240f00c1075031054221030106094483c903080c54140d00c0e0112082e03000c00114001001404003042c110508070a891341c0000f5950442d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 404449046 1250 404447796 404447803
    0x90501120b061e1e090415051302010219081c020c0706020609031b1006080f010e07080c190906090207111906180e010e0108070602060714070614090a1202 68
    0xa40c225500c4192801043d0340b40341c0315401681340035004414150b61070010011904c0003000311030584002c1007582030090002c10a01c99264051030f10700d024003482100d80e00003521415032a440c6906071503140d5800c1d0900042d401200c2500d02444c02c691041c0d44180e400708080e400074003510324540074465000a8590020845621079030703c60002e5450484524817500800802da03542c001240b107031010b8900c00071140d200d4080507018450003060705044100003079003502c03006103005146030001c610810240c0000a1040c4569004540e5200c4241190300f40c15940c01e515800025201d080131000180a00560b005014540c06440f6032400c842903c01030000301f00100404107000015803004000c018410b1254485070142c420030b80c2800c5030760b186000d6102d42d0030303000801500640b800400c404a410041c0d1002014180003420300c1e480d0800c0040c00c1d01250055800c0c60141c002200c200b00559680180000700c02d0380185600c6050800005544600c00401294003c4003030540307019860000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 404450296 1250 404449046 404449069
    0x5040509011502151015050d090b090f07120b06150a08100e0103021804030203220f080105010305060112080d060603020a0311130306020c10050f040b0705130915090501120b06 77
    0x28014183c1b03141c0488440c10070030240740541004000d00c21000602424010305284500a40c42804c00b400c200e044903040c149000d0b0703000ca0030360041d4410403c98100448180142e5001810002c20791f460304082202c41c440c0c0402c4071a040c200041d5030002c0703504150558003500d05405d440c0300700c60300c410305060313865020702000e9804040b12840c0050a80c40d0500345a000d0302c0381c8103480c207003000780c0d010480034109410728049440068100303020001c59103040000410540000784141d51450316141d840712418001c42070700468076502c841c1400135481c11a0300d018001e9004010b0640d403810f00038002d405c092000d000203802c0041d05200802d4550680740560f0502308016001d51450745d803807009501652000c1d00d5070048400e400320421161040e01d12400d109042a5410310341380c5000c1d211a00001d2009050140620801d00b40d0004038024400395401c003480081c400c40429400001d260160f8010300c01142000300200b5141c2054800c00c605900c115441c40c03080c1c4580082000003c0007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 404451546 1250 404450296 404450311
    0x3010218061303140c12060f06270709080c10020316060914060f0a0216021027090b0301061d10080a0308070806010e01020a02060a0504050901150215 66
    0x645801081490210000d00c2d2640e01c1c038403000b98640e0380c4d9072038030382c1c44041440151941d0485c6814840c1c50074200c0c0443d104419060103400c0919069115860b40d0310064010350150340644107510144d9811170744103080304040940584c552500d1000101001001c1c00380c50007500940f41800c4003803d008000c00d41c0241150060350a20008620031400b0440000090318500d0729140c051022480c41d04012800c070030844041e08203403404010700e001c50b480c090032225400703104020f032110341c800100c14018107640c100c41d0700c800d8070700c00e42084810305600c800c1d121112156402d20181080c082c00d079907048030f05480e010310804200f0000c06007222030743c0c810490951400f80c070781301200310602c0d05158480b80402e200c8031039603240c1441d0780c64500080c40480200341c1c51024005096080404550311020900e80b0100c01c08101c00005c2d01c1e0319020034024015240031a0910300d0394003920642d0007824010f08608081d60391031409584104007901d4101c094010058011011064001072034401c500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 404452796 1250 404451546 404451577
    0xf0b120a0506061b030703090f0e04060c0c02040f05190c021011070c270c0c030f030b030114041b050a1802120118060504020307170a15030302060103030e030102 71
    0x110140303000c01900006150036400308042000120136812800141c1100701050005e507202c25613850060000429a04894041801403400b00681e54403100201d91180c1d00090101d8560b0804100b61210b81720a20003c0d032150400682104040301c40c0d0200740300d4401250a00003182c00d00c3d8170b1030116500c0001c4038005810071201e00d0545005a00714100358904e1542c038500c0c0c21495100d07242040e1041e0003460312010030055101140084410810403052811402c02543c45040700c09000e051048800030b044c08030324000500d07030900961042c10300c0c000103030003805a03540c142e502840c0002c0c00c030b41c00c0707601c04541d01f100040d1518017100302d07094450160510100e5800d003d010842c1c0b24841140403465902003204860007041034800030b000b0f24020075803480b121210a100c10603151640c12040c040e0b0320500420030213a60294202008503503641d80080142c42e05940e1002500e11859a00501c1854070400000c00d5400a403440c1240d0090b0780d44515002c3ca4410035081c0c3c4203a2034020213141c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 404454046 1250 404452796 404452801
    0xa23040504210906030b01090f06080a06230102011112060d080705030a0306091802150c010b030307080910080f07050c0c0316210f1b09090803010f0b12 67
    0x2440d40c46640c1142c01603240004070041603048401d41c5600020503800640c0c495420800b19401d402446080c58003424068401030400c00c80b4004841d5a01c078000400c099400400c1801140f42d0041c00a009401440e8440728694410704407183c0190360907500642c03a00000008600c01c100aa4402c1c100211b43d840590715148200701c0d000b5440c0714283c039034183c2006801c001440c20030050900c0007403614040341c800d02e48055a0100e038142d40d210541071150348030342001691560703803180300600300d0b00e0700c641c4130540015402c1c01407106c03000003509440009000c03810f006001c0e016000c00c01080311003c0c0360134201202244c100d44141c90540f43c0c508100d0120b4005401400540864400541280c0a00e503840000924101c04d0013000b11081020344824040b003201f940c0e0892042e02c0403040109440d400f6915000000303124400604061030400c414100d403481246008000e1031440b07018002102c032414a8503451b070080c884c908a901151400003481590b03101551403600b43c01013444840d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 404455296 1250 404454046 404454049
    0x5071b1101140d0501080d09080d12020a020111130f0807080304060c03050c1609050109020406020a11030715080f1e04140c10030e0c030f100c140c0c0a23 68
    0x1010701003400705035884207001000c3c0c00c0300107104a034000c0c45900003c003d828059032001d00300f021907030413203c4960080909071802e96005102d0b03e00500a15400603036800499404a006207507501b50f4408003100024682034885110310300c1801c1d01d01c0c0c10342c042d840b6a40c803400710703039030350742034825003400340c1081c0f00412800d401006486034003800303414640c0c5442010041941040c90f4207100e6203801c485484c0c2031208846c1845140e000d0800c00d54218602410311901942d500c3c400c0b580180790b005601001c9a69803002d004038002405881e501210101003070401410a10049070268074141e0064000395100c8c00000c000309040303045080c040d00c1c2d41c545841c0c4d40c14002d404d84008842e40b159104c404130681390f080300d00405200301e640c00142460810704150400000f016114480e52001d4060302e889100402c601d102200d9070100010071264921080c2c411000d11110070443c1c200128061200d07113004a411400d100e41143c46406580d150400404850204081118803000c0d008400f140d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 404456546 1250 404455296 404455307
    0x11040f120614010308030703421706091501030803010504090212030c010b030c0f10050d0e0102030a0c080a051030060c080903070b0c0a0e030a050105071b1101 70
    0x1264000c900118010b46a400940d450440aa10450340c0d11000400c0041c04d0354940305003020001d44203202c881402c2e5846000704103110020b0235010003015083d8200000400c996654010208030405007454007950002c1500c2313850865054145000392041c07000807403e426010341c181c0380d10807100d604607400e240c00d000060250404c103e0308980190358103200b0311030400160078005441c000100707480a01e9810315052014902c9950301440e0540301031021a502c3c01d801c80d810004c14176055499410701c1020b18040c0400501c460041d520010900100900d00e0f0132400c4034030b80325260a02c2079159902850202c6404031135441c06c04030918001c0c800d03040c1024080e030303c6004404241985440034098040390f80502001168141d0f80c07416041d21040e0005411a80514404061802c062264803194a1341800030481c5404000c005644000305002d0000c0341d004180190884040e40f01a15045008100643d079910115031005040d241000f071b01c003181d440c042d6205183c183e04140c0074005454 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 404457796 1250 404456546 404456579
    0x625080603011d0705010e06090a09050702191b08060702210906040f0305060c030103050607050313080c0a0b010506090607060b04021e1908070f0e01050d090606080111040f 76
    0xa05540b5030004002107039640c8402c80d03e104009000d0b00d4071600e010300150041c0d240c450924081d1070240700203101ea0b03480c482d03103074100c41c82000c0c04503056850a00072410010504c4140d4012680b180c80d0001380945100300b03100040310641840c0311300da11034000c01e03a00c0104076410740c0182c2c04445400702091030000ca99a000b102d00d01ca07075082c40b04000c001292500301d81c2100801100c004410070503c201081240c0c1c125010b50800d600d9541140c4407151a0b0b0002081b40040c4100040410404001c2c0c115510b16140c004820710b40303907003881602c84e484070800c01064071074a07030302c00022400d86001801c84401d400001d00041c03400e4080d40e1090050502e410060b540300c0c0c0d090021404020011030150a101d000c0310543d5501e002007188600f0403e100001e2404000c044010445860b400c0b0004070324000307980c03c000d40340c0c407510070048a071481060140d6050300d0402a00c1c0c0100000c0da00080292960b41000780100c1142084c0203100b40a00d01c580c040e003206104041100800b003611140c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 404459046 1250 404457796 404457799
    0x901050f15040f0801051504060b041a0906030c03100905010803070308101728111c120504061d1f020c031c021014070f020f0a120206250806 62
    0x141440d030740d0050114680550b900013915a51160108541441a0f030760f05002618121002c004103810300900040030300403030040054007400000641c100c540080103451044000416480da00c0c90f00c8075400f42035410030b486841b00301d44104e001148240c2240a03180c1600c5102000354103013601c5807800c8a0390b9801404400a0b240c5041e40403a0308042c1c807218000b41e40078240208904010020409100518140607045084a41d444100041e43c8042000718000044a505140e100a040b000c66410b41140c801403a500d2241c0022030081d400c200900211a0300d51564184429407003c030803654240e010b40580d100c41c1c0c001c1c804080794070103100d0034407905003441221301405209010030304c1c290104004002991510340c0c4555003560405c007031403110b00910020f214139440341d6031406694601500310014003944c0001aa00b9078403c00814041942c06001c0380c44410850810850a01d1460702c582c0c010700900c00001c0c0c082246a552120f40402d90741907003461640031000309d4580a002e450306 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 404460296 1250 404459046 404459089
    0x12060a06020c0103022a0607080f01050105030103080706021306350f1b070c0311120c09060103180c0f0b030702030406140403151d07051e04110a0203090f0901050f 72
    0x40419032005986c00c09107076a42000302030030300740b448028110460041000c4044500000103002999214013640e0460760300c5900103440d00b510313240410181c05032081e0400c11555144000984590001c00d01084080007103104041860381c0c03030030030781c54400348032041e6950b00c0c00004150882c4cc1c0803803440d804140040c0d280c1804051032841ca1440d80321290036076480d0612001401801408103c3e04c8510b5011954040c3e80d011903610702d0740b0740000c070901c0391180c4000c400103003c0342d01030707000320744403410f41d001c2e110800303c1c50326203049808a180208169101103140110310718951804a0f401004103800560929103440012030f2142d40b0b41d00008a00071051100000203226000f0070101c00071004408039003400c0c0340c2d9030010240e03250a00781103a980800402c10464070f50f03040b40c10000200322440b052220b141400704020340045036000350781c194002107962016601001a0006030b40454040001040900800440740400c0c06142d90100301710208083d90324028440d12280b00744a00070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 404461546 1250 404460296 404460337
    0x150806101128020a140103050601030b0102150c090d031701120201050d0911150307021501121b08030703090f051905061e210109021201050d1104060b12060a06020c010302 75
    0x704444c006954030440300b161445103411401c2da054000c45034003503c01c2c45e04009030414000000c0d581c0a00c50f003a070800d4100c0001040c0d001d08000c048854458000d0080e111980c00380c40e0062035102c003016104400a0307141c1c00400c084005460603001c650b0141e50b064200185030311514003e04400c1001c0f280e03034040318110110768444417010032403004110a61912131503e06000b0b418507801c643c41c44821140880140f04625070142c007106025005080000030f03c100f000440c01020740f80c0c00101291002082320000c150348000b60405030303452021754074041c0d50b0320414402d0002c002480307400440c4c02024180b0080c24180040c00c0791000c80760b8409800c0860b1000c01680740e0000070020202c404d82d840c80e441c09441500c0b11401480c801004510f044c0c805403410400300010f01410340301e100101d1040c0c00f406200440c0d821100c074028003c0100e10781c0e071501c401055001d0000c140d0101c0c1c120000501074507101d405c0b04202d8010750007038803454070640c0046000f54000c40c0c0803045c40118828 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 404462796 1250 404461546 404461549
    0x60b120f0c03160201090204050f1602121c0b03030d0c172206090212060a0c020f061503030f13090c1706040c09030b161e0c030c030915080610112802 66
    0xe0070300802b010160041182444050228016510050042035500803480d6010300b0005c80c00b12200342071804821680103a00c542148081d100d0440311320340c140f202084980c00d00c150745d030041c000051162039107814924561201e450b100c404568800300700c050150307140300104800c0c1e0a03105881c411100000e40c000c140e40041c081c003503610f00c82c0215500c03040400070105614840c2c8040d910840c0010300c4031056118241da644d000041802d04e51600341d410406240e1420401c1d542c003402e2501d4030750344071048148400018500b5110301c2c144181800000d0462074001d90003200e10142d28034820380d80b0360b206000d00c8041c1c13140c2e00001c3d0812110070300001c041a840c821260041c540c0811805602d900300c14000c00d0103034000c561600c4d0266441d003000c0125040b1240010351645070070900e03842d102608055920701c45581c0400e0350442c046186001e45540b0095092080d40c0844540348080b118030000c850341c60402201c08015804040c3e22042d04d0244245459040000d02403404031642a50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 404464046 1250 404462796 404462801
    0x1202090709050418050601080a080304060b0604031421030105210c150405091f03030809030f0703020a0b090718021309021c2003040201080405010906060b120f0c03160201090204 78
    0x324490070601308101c48200308002030113494018420030307000381680742c0c42d61035140c22803201400007000f0030395079100c110054454609a90086402500301a454900d200303e2544500c04920740903451030340300449071034201c005c1060324140c9501600c994583c0c4504249a89054902da0700301c08144100126501c140d5104900e00c0110101c8002940c2c403070703240c1f105000c0400009003035442400d20b0300107a00c49010983c0c41804c00c503a01031803c7c03919600c03090486030031407183ca4030800a0f0304000818101b416000298031b004a4812406140b069541882c3d581c0caa07a001e0154a160000c901c0d000c07004111150003a0a00000c080b6540760640e03a45d10360388049920040b00303039480d0317520071040c0700d45020b692140040d01d10000724403410758000050100c3d254800280000c0c10300400c0c0001c00c0a03c002580514440d80d401007003041850f0311040305000f00c0e000714210521403c4144001405840403045c0c08d400341090941980c10754503900b244000e0410110001d100310b65840d011400560350700d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 404465296 1250 404464046 404464061
    0x131203050604110a09030501063305130b070302150c030a11090925030b010819090203010921180e070212120411010e0a0501120e011b020609060112020907090504 71
    0x141c0b40c040d17070303a461490100c4c2918a02d034410000c1c0c10140a41018000943e0b0b140040358400c440321103040b2a19210669140c025520100b00458030380b1702c0421006418001482c0e400d000c0c0d002c680c3c280d41e010355040038691040312004148101400419042d48107500890400c094411040d400d01d2218000716140c00b208030394102c441450820842000f59448424070000d00b064503050250b00c5e01c403c0003070440000500105d50058074902e04009406c06548041102c9a00070001d000110242c24102e0002c1700c4032051030b80244092010b21910307806044490301d01c1901211080090340350000c4a2038400c402001c00c011f40c060944d182000440000007011452551920000c29040c14207041c2e00c40710350a44180d0502542e100b01c0862651102c10b80360031241c1c02d18225221410b0b8030400307405003a00ca00c900066608010014040b60008803216122062070750880c3c81079a80d0700003030b0303035651030078828030152001030000880541402c03c00f4560044d514244034407007030350307980103d0100c40c1d00e03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 404466546 1250 404465296 404465317
    0x112d01030f020304060b040509030a05040e3c130c03020609190e01030c05222a0206010306050f0105012307140d030c080705040513060504060605030a0513120305060411 74
    0x29091441d28601d0282302e460303041107241d070056060060341d10707001d06688a68051030364070325841c0e000264962082c1c01580c458845401105410f004410b482000394007032510a010407081e424002500c080104805110301ca03007000741d80701258070399002e0108079400005100d41244202d03105032100303550700c0c15042c020003580c0240000c9600d14103010410843d02c0e04410312469000c0240c1c11210380600c841d1303401000800d000074251091000d11203050303002015040c45600e180d90b0841c0c941d500851011304881c00346c0b02c1400700d41d40382410418141003d0094a010900f500b0031894402c1410303001307074145200701025510f400b0303454039031203c0c52880000c0505107a00c550715072181c056040c058881c1022041c1040318031821705000c0501180594010030740144103003050b440302002290825401810013a20411005480711401416135000300d070101d07910303801c0c42d020410742d41700d508030000c2c10b41e00003046062021201034114090a8003404943d445500c801140c0c43d1000100c1c01444003014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 404467796 1250 404466546 404466551
    0xf151c1d01141603180c060f08010b0a170403170f04050c0f0306070e0d140604030f0c02010806041e06090203220803040803100e040c03112d01030f02030406 69
    0x400e544a82554044502c0d0720100010100703000100b0700280b09a40c0c11030990501164040c10494451050308503118003a0200700003c00004001e5000070110402c0c802c00e0341e41c80c0c1c40d6a214241c00d040392042d02c10b400006400501c803441004075100001d60483e110346828482e078400b2034280c04200000f0b032503804000c81c1c40004d0104100f8204680c00c1468420784216905500c4540000e8179980003c0992080c0006504400348a85d41c44441131055a07114120240390032055400c0c079500c2e10212003c4001c40c090f141d00c0b00032903000e403d035050201d90503521203400d9510f07101840041c203640c002010440007207410103181070619004140140c05940b80042c1c40b0f140082001c164803083c3c821020319003031440800404102c481040301e6106802098159580e1510350758000d8440c11a84130100001c080006d02c020032030352552000450707004501e0301402003281810010b502282500700100c400314620010685c511042420700c03040414180024459100c1a1710700988c6e0084070101c50096 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 404469046 1250 404467796 404467841
    0x71e05030d1424132304050c090408040b070311060901150b0f030c03070c02030f0609060a0b030c10050405030d0e0a0801020906070303050405010b0a0602010c0e0f151c 74
    0x42400601551000340c1075403c3d5500d10342422503a1070b40720121610740c040c150340030506201e203045800c245440c503814404114058201030b4100c0703040d2400e88048580380250002c2e80424a800402640102c0c0c21040f0507150600d4004002b4141c0d000510407014081e90402c06500c0c0241030200174495210b040010400203880c461501004240303401ca043c00c450280118440c8080010139281d00c01c20b1501d147d0f0752603d8004059401000d0b008000750705204a403500321200d04085aa10b0040415100710360458444042d400144c0f4080151250554499144180c4510340030032107010480031418854501034484000c00e06100c80d00e500c410124a0124041c509402c10511081c024803180c8002c50408100d540081c040341316600340074081644400216040c41401e5000c14814480100102c181d599550780c003034081d01480441202155038504c52600d0b5041054540503804001008100060300f4696007804541001b00142c04074240c020f003683c0c40c4980b5200714007110001c400c41518a4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 404470296 1250 404469046 404469071
    0x120403020a290c0406231317120a0c02010c060e0d0c05070e091f150e070e090402031011040506040609150c03080402040902030a1a060109050d0206071e05030d 70
    0x180b10280c035030b500c1100200b00810619a03c19035081e80110708600c0207003141c5140d441941240904450041c803000c0038400090b250020041c5000c0080c4901c0c240e918100100d260500240035444081020540d40e040a50040d131051079803900703480c46120700017a8000380321300703440c03800003011920b030042a8610b02032001d2000401c003680081c20205800d010314605210350503210000400c6030b0042c0991204106026046504001a105107082003c056150b03141e0100c00b010805440001c0170600400f060401410981441445650064001d0240b42449041040202042107900c440303410705200104941d44c90794000c5c0b000385565900c040c2500c3c20a00316801d801c0b41f0812100500c140010001c00003034000084c6544a50101c07000501d041850000c24208400c1620007401c0040001040c41c103049010900d038020082a030300e0040d0303c0c0e202c906109048450032406540910140820070005a03840c0200303201da100160300000c10038560b51018507681058411110a40d207601d54901d48 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 404471546 1250 404470296 404470373
    0x100302160b100e09072606040b01090f09120509030307021906080708011206020f091008010e0c0a02030f0705010603020d14011a0f13110705060609130206120403020a 73
    0x1e0b1488484040d151300b002c114699543c0190700c690b105c14611a01000c0c17180208810035245410700d40c00361005440e240c0b8141011380c1c000d004171424140303040454285c040b89440385034002a80f05100038040000c2481c16184c80e042520030b9645803200b040102c0042e101d110705039a1191402c14040070f16401c1460191030108010b1111003000b05900040003405492417180e460560400001039507080e104994010321b1040c00202b0750031a6100d114040320350342c09403609040b5290f920041040741c844463b14882e520920200c0d00069206100d44c10025554200422803a403107030f400055402d80c0c070b03400705918603140b0105031b4650101000810300d681d401e0150b1100f8021041e040c2c00b81100360707000286114581203002e80101c502c0b080061048050354030011410740d0822180345c49803802e140c850b81c0c403142116180d0003100f501d0081f4200803164085070342c00c207034000c040c54103081c1c1c0c0304901411400014030a03411803242444040100b03454403c039442605880030504076584001e401c0000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 404472796 1250 404471546 404471549
    0xf06270c050a020a080702041d060405010e0111071b170312060a0e0a0c03140c0d1b0918020f120115020607120b0d1b06020d110a02100302160b10 64
    0x1071080401c42d0620681d0302141d102c42c4180c0c45a0165100d0042d400480d004115500000c068022a10105403d400d8000750f0355103c0c501c00d100a10040f40c440569501f41ca0110144522004d0244000400100b040032500414405945142106590740c00e401c20060584440f040036078200180c43c0d602452858001c981c0108281c40d1050240c1c82e121003d41001c1c1c0081c41600c189640d03000804807140b00703801516100c2c1480c0746946190401280e4942568071103200d2241d01403500441088040324650500807605040c0c44540281d883c003d204665400850910b10034194200032440c1c0a03015800030f015442c84000c00e8040b95810304852007410081c00c1c828406540c880c00c1085081c5920031210315098400100101d00c040c8400c01240c0c08546ea44001044242071140994684c809100400f04a56160b400c46451144148081d964591076034013042181e0020364200015041400000b144008140b0b0010f291212164180300c0d008008070089540010002c01e22400a01580b401c1c0c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 404474046 1250 404472796 404472821
    0x1b0b10090b090105060d14070801050414011a0c100203040318090504170a02120c030d110703120207080403021906140a051b0c060708120109110d0f0627 67
    0x400200e400c40020030054051013075a10407a80010b0b40800b0f08519000384110040803a860300290814403001f520000c0240212800707180340c00c58081d032003940061a46d04030390308560842110401e94507a0072490340322441174202d0341300c1e12a880c110b1081610013944182d001c0d65a11441c01180483c1d42d40881c401e50010050078100014000425401169001c2500d04511941e5540d40e0000c020703400c0c4074a03100c100400c40c101003070305a40e02d540400100008080d1150030008400c800c0340448080c028910301900003003242160310805503059009120f61402005010b051a9403980041d0440b100b08560346403402c40c1d5502042240c1c2c010000d0740c0100c05c41030405003000d0301c000008195012701e21920b07040002c00030130000d0299091244a00300100071b0f040c0e84ea00c00769414000450b9001c42d519120000c1c580000050a1001e0f22820b5242c00d0416481454003041d07040c90000b5001c0c0110058841ea61050002004409540100c5d5520307041907a00003580d051309000c200302d8503403500c4032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 404475296 1250 404474046 404474051
    0x5030a1e0c0210080603120406020c03010507020d140c0c1c14012313140a0c0e01030305070305030907090e0f150105030303061c0b0406050103211e1b0b1009 69
    0x1c40166601461600c0000c4140390000f02691890002450801c00740016641325000080110b030865010400e41c00404082d0b000b40202d4481d2071049a880c2d0032070f991900010f042001301491446850000c02c100351151044441000031a4001071f0346908900e0307407061030480c4800340020000209004141209240020040c45104241c50f000c076680c55400501000d803840b0000e040e98191903408214070f50040c0c13030f60a41032070910729907642710003204003540c1005160000107400c01d1054100b9041e86d60607a1041d08244031075806890540005e480940c4c140941c580200d401340d0180f2641c058041890f004046140004c0380080c1407285e00328426407101d480800501040d140041141d4106600b81c517156520101c4002c14210003103007503030080903400507205000034030240f0740209060381e00806001107410401c050304845007044d03801800126010614040300c061020f00041827500e10760800136000d4188110803001d035280300004a80a171003a205100003000c401d10000c0c050015883e04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 404476546 1250 404475296 404475317
    0xc01260f0f070914040903022a19030203031b1e0313080102041d06010c20010e0f0a06210609020c010c1713030318060f0b03011503080705010905030a1e 67
    0x541c0e40c0044032400c13240076944070010a410140308000310310f210070a2900340f07400140f000545c80100403081c43c2803403189803a030390b250280140300d103801e03070440740c0c01002189402d1070078040300980a1a034a005255000303030001c014020541c1850a034030b081420015607995000443c00d0303a0840c0040d0071001c007982c4144800c2c81507600e54524190b000c80c98400020280c1c0d1024012100c0d43c0160800400b152042500c0b400e5210b9a22418403102c0c07826210304940b10781300350030301001c01131071500705601528002c01040350030302810005030340190b4144540d1081c288030410205a413450f5002e01c041607400524400e55020030308c1909441c50b5189000c1c0c4401c1a9000c80f90701c42c420180458880c034400200d06001c15010307a02100c81325a0203c4202424502418100e0007040075645040c9042d0034410702028510301840741c00300405102002c02221403c3d611251103642014404a41c150340c1c8590355408200204064800c130400765440110750341025030030421003142c0c19a01c4040c070090074007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 404477796 1250 404476546 404476559
    0x810060c020622080f0f1515040b0310020c060603120301060801150203090a06050d0609020f1b0c0a03050a1403040b220509090109021c050c01260f0f0709 68
    0x4640c05041d0356401805515a2400315405400c055400f0000701e10810340d071703c400c0c1040422408030701540c84040c1e9106800151030f9402c0f4442c1101c0c00c5003111490b5060703090501c0c09601203400701700003a044841b510b0b00510040102d0303015000c180c2d6680d00013402c00c0803c2c0b804001c07807a0811000c2e06002c0c159450181c001d06489010301841c0326819500054000c0144200242e804514000381075050095860a025045138030240302414964100b50010514480038000c40c0d010b140320351745085c588082800c440080b2a05000e540305540510f44552070155224901d64000d5400703203000d040501014642140349a10b60f00000189400c1070004002c1e1001784415100c01801d230030b000c0d1480c0d44005400ac40d4925040d0001d90384044500301348160b0090540c81800c419100b076642035081c200d40c0982020341000303200c0061041d07000b400004965480317400c003403040e03495043e180200d0b410005505e1600600c12240c5845901c122400c114444843c120740c142c22150b83c2c00c0c401d07601414000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 404479046 1250 404477796 404477809
    0x40902091303140424110319030204090603140d0806031e1504050f01150302061806130305030d050c0c0c01050c0f010f050a1104060918060b0a0810060c02 68
    0x2410210101e0541580310240b500640d500c81a841e00c807000f15607615280d0703665103a200c03c1000507400d034250405090201034010030f650610007943c0b10046044c044801d84024900c0c00f0081d04108154003808002020081801500040c603c99801c510840c0300686107103140850302c00d6403504114508040c010640c41c04030b0001c00449440a992100c941121031840c0791412405009078038000303550800c010b0002c003182844a940c1724078003d009030084850700c04080309160102950280e01000304065100c02c0c02841d140c00d100c00382c40b29040800c0b0b204801994041ca500c1614142c000141003035202721030744610380d130085462211600705907104412035511004071541505000700000c10302c0070a81c0c10028031580100980083c0003983e02541c544d801f0300010364030030300060305112030764191a1462041e1070984034550748aa26807440e002807046651080305451030500c1e40c801d00422101d81c08401420584102d45481d40c50341803e036000c040302c840302e03170119003041248a80720005a40c0e48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 404480296 1250 404479046 404479051
    0x5191b020c10140a0c051509010501050105070b0c0a03061205150703020f1b120c0708060705031e04110907020a0309051e040f060806040f060c02060c07030c112106010504090209 78
    0x281e49481c4c0aa110064410000c0c2840140482c41400b540303c180000001e146841102080001d000d648da0340e00c01580d190080700c3c401010020103500140040f03408c03038003410000d1020300e408101c2035601c0c01c180400890075401610070b60041c000c0c2000c05071800307642503002810b92408501c1c1c01e00d404090308060203601581c40703035040c0d01c401c5510031b40802c003c04103034240e04020840c0d54200400d41e00350794032450f21481d0094003502c400104d03810701480a4030f11076491568032020500d520082d40301162001401250210030010a1600603200c61039680d100b0481742d00148003540181c2000b07001d8007410f602841c070980d000e944115a10b103900460311904c2c20162804245000741d55005d90203048550021035540c82910200400d200c01c0c1c4503503860300b6000350010450381c02051800c81c0c490804598020940404203c054000b0b40310740b01c040f109501400e841c6414200710400103040c0303031250901c080144400101c00304501c80030f02c101401010b04603410032145905501140081200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 404481546 1250 404480296 404480327
    0x80112020402090f13020a0e0d020907080717070914031f180510060513020a350f01080114090a0b04020a0b0c0319020105071205191b020c10 62
    0x20030342100503100c44030130040900c402059410010039121034034001350001c900700c40000b050030482d01c0d90307410300901032a1456000340902c0d5041e40d90b00c00a840201c07001c1c4c400e43c1040000b100720030024000e040e00070300507a0140d4403452814542608201da02280b6103942d44690840302a040340000403020b00c03603888080d400081218503c1d128070300c3e00d06401e07070b001504500905950f410829070310b034842c0c1c080d640200c48101101a007111010f089014542d41000416007140c0e4075090180d0b0810381e042240641ca101c42c11051681088209030304040e102140d81862101c010b215203903080c000c1502000318054030042c50b240c100c425030741da49400c00c005851810050045419034603001e280e103001c2c0c4120300140366a007140c0d030b02030b503035030b5020b07182e003c010543e5558407503a0184107001e01170003080e195968503955102843d10a00515015000142c116074490301c8010ba80e145001d00400c0c105070320155031351041c101e172020342081e800e01c1c03d052142ca40e06410132440d541003000180d0400d0f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 404482796 1250 404481546 404481551
    0x2030a0206011806120609050d1404032d0b04030f021f020901030204080604030207090b090402030c120c04090b091b010c060c02010603170c0c0a0b07060e0a0b01081b010801120204 79
    0x7103d00f000004104540021005000314a48142480300d903812603090030f80301d2012a103600c50350160449502c2d06100c0c1d40c11201000704410000f083c20180c040c441000e041d20421610080324091140c1d4820403002114400070ba02c00300018160000445000e865041c00030f012001c10301d00b08111040101c0310a100704075400302c1c445c500ca0744640e042d01d001c1c0088070201ea1030f5050a003800b03542d80005102d03c0d0300e8075040c507207031005600b0031508080c052075001d40100010400c0c902003200154030046020391910a02b60b400c0003a80d2140200e019150241100c5060b0303080c03c00d503140c100903004608420b4800400c4615802e45d81c407050389000d01d500b2440010350700c4501c5504078050107440c4d00140200075100718030403a01c6501d48c0200003003a0002c2c226284e0034140d0082c029101a6440f404040180500c1b0410114500750024000340000d00140c40c00e1a400742d4038420300403020b80081c05a64408429201d840582208000111703109086c8040c06600d048600c51410707084000003401144c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 404484046 1250 404482796 404482829
    0x3050c09040504110d0b180102070206041811040b120604020a0e090703021314011d01080105010c0c08030a021510030b010314010219050a03061202090a091e05160602030a020601 78
    0x801c14208004404c01171202020440034240703003140b06d00903101ca02444110641e4490000c0341442114085607026201608041c506058100e0001d11841480348458840c1100702030041d4003001003000d8450340000c00d0700c034a04101d084401060060186004034410440206010b8011003170892a00003181ca036002e903503500340201d02030b000c1d410202404032200a004200c004010842c29088042a81c035801c04040d1020b030b0820a589500e00ba5000c9803444c001070106500c502d020038141d0303006208041e00c5641c2d9104080c81e5074040383d88600141c11085519808010b000d24154008034020b40b05c0d200d01c4e0454a41d03102094040c4801000c1d8640a142240c0d015800c1d01500e100c5808a049030340001e90303581c0064403503031000d10110002850316101044142c2c0d903c0c0501c1c1c120f038025108003442e56841004100030f2400000c00c0d50600d00307030a5140d02c200003103182c00681d0751051015000d080c48115800940f41500d40020065420910141d5041a0700003445411690301212900910 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 404485296 1250 404484046 404484053
    0x180109080601050d1506030c060f0201021201141809010606111605060a030e06040317070f0203220305031303060501090b0102061501110a0501050f0a090206041e09090f0203010c03050c09040504 85
    0x84117039242186a003810420000184803569a2003000c8410b2900c800410310700d0840e089080307118890f000f004550020300180103404c108a80205a400c002d0041a9040301148141c2e912000840d0400004c0e03454900502916900090f00c4202c070040318014044802c40500b4450b24001030f008090242d00e0114a01a019110350850640c3d01c020320261000d078101420f0090180b40030710708040134015044089150b5071310401c66074001811b140d02440c100032b00c0c019200b00d048020b140711404400e502704007202003a8140000d0801c4605901c0ea1010180345241c014151001648019440341c076102e91038903140d0b004a44540d110252241d804280c1c9070f20030040c0d0301003801c036205d034405201c0d1060b03a41c1007240561003240100781d4601031110301e0790b84c0c50b141e005441503208000d401080520040245010307048001c1ca982c1200603c4152940c1c464070300398212420b1402c151191100c007040300040d8103003842088417443d01d916042c855450714032040030040c421884813501441e43c842c0000e092 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 404486546 1250 404485296 404485313
    0x7060c030b04181a090d12060308042907020f01050306031c0f020709060506070f060b0607110f0f0f13092012070302090f06190b180109080601050d 65
    0x450100410402c0941412001801e060f05445800c81c4d2034240c1c200341103265101602e0342d5106007200c4004048044684200711149240e0f00d00d48000035403107405c0400061074010160014040707016401d41c1d08071070501101210350107841c210031510420480803000d61140300c482c400c400000c3c205a6629150b61000c245081c004a0340703000c2600c0c02c2c043c6968020307070048030078491443e80d03400c590386e06d0740b10f240a0b0215071b550301c07600d0740c0080200044800105441741c81452a400380d03400140124030000803030810390051100315410224602c41c80d249180549070060031000c150b85640d45080c0c1840498640702e0340900091280030801c0003208c0e04d90340364110014695224a50704100d0355108546801070300d41c501401d106040f000c00c051441a00014840100c0b038008144121507121000b44010520003d08115005101c545500802c1c5034034411040013030540d810499910b101c42203d1605c40d00c55403181604000380003004129000000458038151402186da039840c1040510740000b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 404487796 1250 404486546 404486561
    0x2030307080414010e0313080102030f0609040201050d050106210e06180f1b03071a1c06211407050f06130323060105040e030304030c050705030a0c1401050f07060c03 73
    0x30f0540c28283c1d502c40c000710220103005495416600c00c9480c0d901d485109081c0c0c0000c441040d100da903540001000307450038400c0d46070000d00604155240c02d8154102c401510805d030003410100d03517881e0b5070704180c0c3c001807005500d4100d028400c00c100b0758000d080a03100d0704041d0041c07100c2d214840c00140c01100902141c0030000c00c0c40300302d885554020380f2469045e00c090320618402d0256010002e07800c80103090304d034105240010224074100d1250000701300904064903e1580c60350301e0724003160050b40c1c0601601e05c4103d0b4800e01e010804989040007404803610b10b43c1176990046d0504128540710120780515142d8111003943e12640c0000b076900d900122070388043c020101c100d0180c00045680c41c50000480d0502080e10700a82c0c07580f05010a88071180d6040b16540e000b00300044c0460b100da40c0c4065032521850640d034140c2d43e140002882d1418480003550041e1020750b00304102c82046058904040c02802d009080021100c55200e01c0d0040c980e010317040589500030800202c0c440c2d440500c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 404489046 1250 404487796 404487833
    0x12070f120224010f050a062007090606051b010b01050403030302340309150509040b040e0318120f0607110a1a04050d0e060306010c1b0303020607020715020303070804 73
    0x515042c00c2542d41400802803040b482e011040e240080b9442c00d100f20414155001d98a074180c0c840909001041c0329004240c000c104c0b80100400805e103041c039402564000c0c1290790340c6c961140c03030a1486842843c4103c981c1441a803601ca0500b5a42c2d8001d01a1401c81c0e405080042c1c88100c000b00d801800020000480282c8041c401d04000c17407085062610740c504d009584158055032290301084070000c0e0407181c00e000c503c060041e03d04034901500701714a801d50140c80480e04103a851822031440d00080b0150344056440401c555030790402030303111514048900024040e9540c10603040d038075454050004420000b54844920340e400341080f0000d0141c1d070244e03106121030801600354042c040b06540890b07580c0180224205494030a004001c1a108014480d510790b07201c2e04d0054841e001088002c4820700405000e980000a010041c02d00450007a0003601c980d14144000030f0600c080c5400407094601407050304240241e0000540e948840241081052601c039803c28001e8042c03c0228513 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 404490296 1250 404489046 404489083
    0x601050108180f0f070f1a0d021803010515030f0c06030c0903070806040f06060603020705070b0309070e010b0711120318010e0d06061403030403031403072a0512070f1202 75
    0x4400004c001a00388211691042a00c190030384400341640d5000000c00c1e0891030039400c0c4604050b01c10340c0e44c020b00001100d01c00d42401d44801d000803a0a4400c01c45207041301840c0c4030702603980c4ac1400e100418000c0380c0300001c0c02041c003500b00090b42d50301003d89030991041c0f020442e0445a101000003502800141084440382e1501e4904126020380368007040700d04505055001444a000f030090300c0c1d8031503100c0e0181c10000e040500c01007540c2c01c0248140b117940b21f9401d00141803882e201d40c86010748005029035030b6504503400d107901e080c403071580600d004600d2003017000d1851b0030210540741c403130100c41c103049640810ba600480b424200000020b13400a9641150010051107500080445004d1346c41189504140405c1507200d000e14800a00803401d103003204048018140021584034240b030404607078040b49202040105203000444800c102d40068480090000030012401c4440490205900d4180c040d13440c84040103170300100412540519142400090090000402c4a005603062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 404491546 1250 404490296 404490313
    0xb2205030306011803231216050f120301090c0917101a0123040906080304031e110d020d0501180b0a05070905061308030a08070e030601050108180f 65
    0x9600c0e54001c1e5451030201c3c00c1821302d12003403900644a041125000131484201c0480c4c104c01600013101c6c2d107501043c1e030240c80d258034804644c880240411080c1c0600c0c51810703400760700c0c0c81850900302c5034215040d9408141f0400c07603000300c0000c07203054411401000c83d00014108080da03480301f00d0f400131049011030304040003003040c0c001040740541c0d040c54000e01c800408950f503500722000c078040682c0000c0103260035440c6c500c00e540749047c03081d0400100c2854155103c5065084070705907004281d56800c002000c1003400004c00a151522903001d10030400d640940d2f0b03403501092011009c050054000c00748140c1599504004045101c5c1c22800901000d21552444278070344001100c2140ea81d40030750007003600905684141c40c443d9100e0b03111789003e0390071700302004000d80250400c0d801c1080c1d40100450b51800500140c011141c08d510f48201900701184064110001400f81d18001d0348504010002a07030b200190541040210031180940c0c4034102c13842d0700309800102c002055109a805 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 404492796 1250 404491546 404491553
    0x16050d1e02030a0f09120c140307060c140c03070b070e0d061b03090c060e0d0c090b0a05030a0f02010f09090204080304030b0702060403090605030a0608011d070b0f070b22 75
    0x71072150020303c2c0308010011074000b031402200c140340307000740a44440f00c1c3c1682e42c09000e401c80310308890003412920702101d21800c21300d02c1c41d404403000301c07401c54480c20920b44603500400c1d5011042e81c0c0e124420708084088580e150349020300e0a000c0d0440c46400003158070742c0d00404204000280180c2444c1c180789030340c20904041c2140a0f90413405255107845060b5407440f0303120b075005041d030010f040b500040c40c0280c101c807020901041f056102106490540020715400e6010380145117850b00410402e40b00c20400c0034015a07580014040d41100d01c0800006007086502c0480381e41c2400c0c040c01221074142c0485290405402a1b0155840040e020440c0c84000011340122407242918100e9542e402804a8441c00c0c10354008000c00c0400005000850103035010f140d021200400002e8241d58416000d406d486c080345c0285103010b40c1c1c035502c500e148420710074200a0540c0d41c030b000385040140008499a8401c0d1040a020b4449000200e14582c0c0c0c1c28510030b5440c250003803c0c0b44038000504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 404494046 1250 404492796 404492801
    0xf030f0e0106060207081513030e090f060f1203030412120e0705031b03100b030a02060a0f0807020102190309020f040507170a050c0a05030402011101051f080616050d1e 74
    0x2410f000d4411710340300085440300011540340c2c2030b1401c100078259403556a1386403000c885000c1d084083c13106c0c180205c2625202d500c0f4551044000030354560791401d000050000c0c040800c10380c2e41c000c000080703c00112100c00411250001d07400369410020f12280740b01150380c2c02c1280800901c023418480c4000f00310b000080c03150b050700c0d000c8040c0c40b005018800c24080c0218402925501a003188508a14812266000030940d540c083e080e1179680d00c0303035400203070b403071744803584035400300c1d0720030b080d02c0b0a02c4d600440307555100d12503000842c50305200003072000d500c0e074007410090708040e124000b5008640300d038020745000c4c078070151061059050401c009814400e2900e400c51b05029802c000602c5406a0301403180200041a41149049010802154280c0c00140182d05000da04000400b10301401d2060b41d00c1407461980025082e4181c0d0300103462907100b80c0c0042e00300d9002c24180b200032807201c074040c1021035807814100d543d11401036030000504111004e0340c03c45054400c0312005c010302d0742c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 404495296 1250 404494046 404494049
    0x906030501110306030a08030c07021809010f0b09150a0b191b0317060402130e09010e011506050a120606020705040b0d0506041704080a0501090c06080702030a0f030f0e0106 76
    0x11030092125400c1c1000608060104548050f4507900c0024600302240305400216080f0001d582c22919000f01074010030743e403039250110140d0b001e00d50030800c081070030f080c81703501007d80c0307658002d0025020901c0051084030f400b0b440d08420b1207001c52070702e425aa4000903076000b4180d2600301c0b0344a09036104005400c802040f01900801ca05140111040114080d8103900742c2d45a20740c60050080f403125281038010003814aa0440c0d403c0122200420300340c00a00b0080080350404601460410080c40c00e540c00c10001c1e0440340c1c14012000c16600282101409585d82480c0c0b035511030007544422108039590a4036200418a06000442c049502140c100140e0364240c0e400d00150070f01005102c1c10070b203c02d402805039084100413130300055100800392000d054964519007450340b120b000d9400d081c4500c0302101c80342c0d940c01d074040402c95400745000c0100400e0030b00c074106103007081c8040c0d105c3c07140f06014002c00c0560a07415184030f009900805041440550401c03942c880c0313000040c02000d06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 404496402 1106 404495296 404495303
    0x181205311d31050601050a0f141c230c060703080601140c010e1e150106080a14090d1d0a031403070602161a010e0402091e01090603 58
    0x11107402c82040c0d4000c60107080e00e5490101089181b5070941d10450b821814880200100310100f01c80410180c42511100c40011107943c0d800e10000b40d00d44024030480d108000351003010f024010342c000b040107800440d0b101e14289820412240980480100000c1910300010690352089044e541c0126445a0441c00c00000d00d0b481c034296000e5900a40301e0390700040c6403805c104105008a1390005091016202c00c101d0ba403c08541d03018140103850031b0018000106405446961000004041000e05440c80f801c004206503181c2d1025441180000c40d8450180b200e1101f582000c1c03502c0c40c1c001d24594081e03181d60340308440b580207403002d00200e00041c4032190204c1c11500080c40070343d05000b021540020036190803000301001405036074400100c44018440c0035021400b141d002a011511750f10541c0c4c40c403000b10541f00541480400428900000146288644d0008400e5902c0b = true := by decide +kernel

theorem cover : BRFrame.Cov 404316546 404496402 := by
  have h0 := BRFrame.cov_init 404316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 404316546 ≤ n) (h2 : n < 404496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
