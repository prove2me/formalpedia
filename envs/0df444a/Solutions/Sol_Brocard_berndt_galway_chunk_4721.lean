-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4721
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:31:12.828777+00:00
-- url     : https://prove2.me/submissions/bb28d602-3496-4042-86d9-8340e3d1f8b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 848920863 ≤ n < 849100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 848922113 1250 848920863 848920883
    0x1703150f03120c010c3906060503010903021b030a050c04050c090319260d0504061118090108151f1d04110a0803180423010305070501030614060a020a 66
    0x2d120a01c0c007820608003204085190054900d1101a4000960a201b204a80c140210364a070760400141e0000c03007002515800d031605400302e010b940a01c580d0a11600c01e4000f0015200109078126103e540312818500c25007201b2550000324002003080382c0e00e03600899002440781e1350813540c0c40803400f9a00865406100d0301d078400450a000400c1000340e580500d041d00c402e03c0203082a140ca11909910701c01c0010400d11000c0e01c0c1c3c009a800c0542c11902c40d500100d41c00001c914441280d4004500c42c4100c0a00310318034040b1410041041c034050021680034260904200558881c04440980801d100d84070340d20b800c04901940075068000b902156010a12140d00f0302403003034032410262000d9a40a0b50710081e08401d14020141d01f00302c404071000385003440000800c5d00282059100700c16085a140d21010710482041c04424131352400700c4100d40c1d525415401c02600d00380c0c581c0c200c00c0c181490030000b401641c80c44404250703a03640c121001642c410030500700324100550000010241491 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 848923363 1250 848922113 848922127
    0x1802070615060306273303020406140904080a0e03161d06100309020a0f08060f0112020f1005090405040606080d020102090f040203060121091703150f0312 68
    0x1e0322141c40126002d5075020301140740c59070005e0f280010380c601d4000d606016409440d14142c0c0320b401148070b800135030b040c00301605c1c030f00010b4107404001041024102482a2014000c48c43d091103114080c0804c0d94409081c0080070740860302d0f4507009400500240f50105070255840d00c20b600d00d01c0881c8025051300d0000404148260022035140030b003021000041d03074803903c001c21850002d4820f02c8003e100000c040d15140040c3c0061000090980e0403144000000c1384403070004007140c00a0003141c009208900d41902001000070781a040840041c4d0420324807809681c44090400104108661800d400c454a42c02a45e0a2140b20f90342c41e001400c3c42c0c200010b101c01075010300c0c21109030b0001c1e00c03120550580100e0803480361686440d0301603482848a607035404e00f5409181c0c0071106040840710000e0100e848502c028251030b03200f110b0380d203421201d01040740300351021861303e03a070307103a100e045003400e2800c0700e8013810020146020380c099040c801c800307503010005808d16110000c80d040e0780b240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 848924613 1250 848923363 848923391
    0x1b050f0604150c140d0b090405030408010c020303040305090915030a030305040c080d08150f1201020403111509130f0212100b030403021c020a0c15090b1318020706 72
    0x941110151040e045401c20100501c1c42d40c01220f5419195a440c3d880516034a5510340c034a0b04002c8482c41c8040d516150304111362283d020060003180240019900c66161408550a64404107244000c540060050000294014080c4c84056004845289030341d6101c1d090010784007030600ca43c41e0b1501c14090580e05240d016031220b0f000d64020300740c01d0103142e121940a55a9010700300d620000904600000700c034640b070003403251280500104880035058004c00040e204440d00100d40745281d600003401c1080104103148407580280540e00c185c40219030140f016800d02a40c0c070b03145d010f90b01003981c1031074001855110b9210301003002400c40d01d421104005c150182003c03661700c2c01d040541d9001103030305d4066009507442558940d00501c4003215000c03800000030041401d0400750310275456920000b44201d2420300280c41c0003d21400402070b40000100404820303401081e9900d004c0003143d89a0706501540320954200700700745448258040c009000a10036000702510031450000741d01d500756 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 848925863 1250 848924613 848924623
    0x1107050d0f020316050118030e030c0108190b030a02120601091b1e091815050405042f0306070e03100b030d05090a09020a081b04080706081e010603052a0a1b050f 71
    0x9c0194200d582540381c00006580c200c0041d240740003c074050810342400c4400d20340041e9491013029003a580c406001e603011410136540c920070300449401282c014403900320340740b082c601390411580e0102c02d0091000405820a4607000b404941c1d007900c0d81c40d00f50f003580078541c42c41c004e04902410301000780f4a070b40c091000f841c40c5172500319180c2c80c0d50800101d80c5014010b49009075004010740b10b441c0a48013154225851000401d0100048000b251a02da5000e000c62440303421903844c1d072019401800c04240c10010003101b41200b0074038140385a409a1000213035601c1c414101c0c14007960352121503000070f0701c2c020990702c0062050300005120b103909612032503080c012040304154402c680340d030001c00002400340c1d000300e4049038460f10003040111b01c070308025074214090081030303503641780200701134280c0300c038260130400201ea00c65007488406a61318040d28803440384010509450308490f12441468440d00008404211aa5540c2c0241100203986d407c8407036802005c813084d4800c1038000513160 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 848927113 1250 848925863 848925887
    0x306020a111501090b12010216060c02030c0d1b050a1421160212160509011719020a080601030302060403172203030204091107050d0f02031605011803 66
    0x2a90101c644030316180c0000c040e100c000c500032103030906a0030402428020320600e04540d502503041e02200001c03000a100400c10b8101c2c00b4150018030703206003001c40554070390f001752604660003001617124120001c140c07401c00028900d44a03d0751140500c48048032044084054214002c45003008204507e0f0000d010203903140005454000c2d01115508103020740074001508410f02c20810343c0e0b14640320303111822011748020103180300c0b10308442c80d0601e80f0700c0c1c0c0c015902903015589014006860a0f898642c0141200f01c030b004c0744025130a40789502c48190101c00c0c81a03008a0702008219510400148003402000b001c981c0340e584c6d0b034100255159426030b01a8089034031088025003280c01618254403510945040d031855602e04210142000000e0301c3c1034040607070030300003c034481480c1d01401601d840700301003860301ea420354148182003100e088800ca05002d00b48000b07000310f41d0080f0648400d540100b510143c29000c2c1d08005001d48280c0c8640300c0e0403260007101d4401c02d5005100c035070036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 848928363 1250 848927113 848927117
    0x111213140d020a031515030503031905101e0506120a150302010c081b061302010e0d0b041b030c060801260c19030f0305093102031806010306020a 64
    0x2051800909200300e60103400c10294224030902828008942105807414038170310407160004041441c8a281d0f04954590340044950360400414802c44035030040000d80d8440c1500010011402e191600100300c07282c0341304001e0468280321014100b0506100208001d02020300306513600d0b40c09521182100790b0442c0c5070812a4540751915654150768000c00096950603102c4010301052a03c031186242c0055440d0243c4981c088180150818103226050082c4581c01c105100c1000c50320001d000e55800032007450041c00250700100124a01500d02608207400c0f00304500840341c0203800da070440c8010340016140341240304c000588540d2148056048902054240780c8902c0300c0055004849001805048264080d6039202e507a0329082d580301110091410100c2202030b81c0b552400442d0403598804e0340071440218441e2182d00340a03289000704a06080711120004200801105031085441c444c912113a011002580700200c5600590015904002300d035104e40c3d5038a8284082d50141c2d4600340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 848929613 1250 848928363 848928389
    0xf0f050727120822060e0103182001051209150105030d0e010e0f0a0b070b060306010303020a1b051806040e0d0e040b040908070c03061a010503040201111213 69
    0x5401d040c0c07405490a460080c182228214103c0d211480c0b950408056001940b00c01507801d84031940c410358032402001d2903100c1001c0c00d02c1030000941122640c0c101d00c03004000150a2a000600b00100b0300384241700ca01c20141d6800400004032100e0040311106600744401c4001d100f10b0500000d02140702c2000780400390003d0380c807441896200c00c0100909404280c12082d035444640c007a40c01041148000f5080074088984200000e916101c0ba42c0268000000020b4031030620400042281e4403d1081e0020001ca51540d50000d595196001c005401003005000c20b40194808a106000404004143c088052a0791401d810001001e41d881c9120700d1504190030b00f59407004c110259840311945420116403856801c1c00040c14030803d0565210345d40300140720000710190044c0c00e10f00d020f29604840b075410f40c500101280c04140c8000026142003160040682e0b0010032030354400d1f03089c41d04e54946091501c03a5840d00b0801e40e03071811002008254010402066442c0c2c00494048902440c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 848930863 1250 848929613 848929667
    0x20f1215010507110411090a18050c1905180a180c030e0c010809282609010309050c030f030703090515040b39210405040f0f0507 57
    0xd07039507106100008184c1c0c0c010806101c070920305540710381d84141c0740080c91464603242c00c00107507081929070041e42265500304423080c0d8184007803195950100b00b2122407450212541101d6404a140d504480c0c100500010340701d0b0381c5060030458510580b00501040b00c0742c0e488074400c1e40c0c2e079a9101d08422216180240082e203152282c001d42d45e940206002804d0141c01d40e4004441980004005441c1d40c4584031101030b556034203e50458207041c082400345600380c60351a010301c28001082c000020303945003520218800034690102e0348144003d080004a0f4002882c00fa414146003203049a4103024801c04955441008070080c51001d109607602681c0386e49a50400560380f6032000f18034100c00c0103100034003d50000d2401045155840c800b40c11402110480c845980c000302c440300f14008030b05d48107043d0541420030520ba144400c04034403102e4100c2600305000c89004600c10a8440d5482e03210005040d030440c1d011118400003d0350510180c90800b0010b01441c00d581d02c0c0300d00a1045103d41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 848932113 1250 848930863 848930867
    0x42a091802031014161b030201091509030e010507210918020f04030f03020708071d090c0f1003150b09030705010203030121032604060b0a030503160303020f121501 72
    0x484d81d02e55280021007100d84502d9443c290031074200c0070807414416602e01192030046640c004091052090b80045004401071030135401c072a800e280c803107092904140d1a44000398101240001032102841c00c1600c90300141007120207108803103600d2201c01c000242c3c0060442d44003906c0015502000c02080b0f80b02401030b4040100d1066950120f80310800f800f0600008020307044a1800b28028812a100e0030344903181d440c141a940d91040c02500c0010310090244100b00034400e60007404800640703000304095002c542004035200b0b40341d1180c0c00007042c1e003000c1ca00a80c07005001070901e0000050450b2102e0080203603034024205580303c0e200f01200010300d0362002080b42c0c140c0d40f44020b5415071204a042000038145041d10440a20210880316508000580d003141c481d81303914401ca4100b8241403d000c0d08440488058901820300e0380c0302480451800022150302e01724441007002c01c61480d05007100203001d1090040107103040040c031842e56510050780340c0c3c0541c03500c0d100340140b090340c0401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 848933363 1250 848932113 848932121
    0x2d01150c0803041e0515071d0f09190c050d1113060806030c150d14100b130f080a030305330d060c020109110603042a0918020310 57
    0xc0201001400c200041c0000c0ba40200c3d141c0e060710078002d01a81c505103654007810580000041014490f0038001c0040305036100504003106000010348410300c505410200358603802e9462a18024002200403610758a84c60061000008001e50b08215400006000800340d0380060040303101d07641400040160700701d8510803200305078040c080629071107140c04025546c40b9402088281e06000300d04d8110029101d40b440012074460200007070742e640138142c94990032103900352050000c0409140800401d07020305512101560369110049841d1666940c03024039591440d04280c40f5614a10400138451800107280a000c80c82034606000f1656800c0042180030305085140c5401014202c2e40d01d104000341e004042800d0000d0443c141c5124030313407520419220b8401da540e0061307558906000c00e201c03040b400c080c035007502101d856145042030b86035246041400b64001d440300c00c0100203800c03e41c0720b69094100821410f28140400e0080b880c000003281400b40040e40640129000c0c0505481030b842 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 848934613 1250 848933363 848933387
    0x12d060602060601080a110319050a0603020114070f0215070b070203030c07021302131e0f050f091810091403070203150615040b0403120f172d0115 65
    0x700500995440400448a00e00c02409400340d480e80d4600d1800142050f000031403181241f91000d0403020640b402660480780010240714400b07151210500040c1c1e03004031091b4084800c001825218440b600340701000c0344500c90003d5000d120503d1400032501160301400004c2d004481c1d40042c3e986d601801d90322440708403070100ca142d208020f018010726001d008045d820503070800060903e528803500051550840c0c1100307100c103851101003048010704149a401400320700c0000108035207000041100a404042260700ca02d0f50303080028144100c20448014031213121049071068442c0c00c006e540201401c10040d2500d003c98440c0107010000007080741e140c0c950103001402d000c05045650300780450007504080d440010b010340c44030706407441800340014003aa48051642e03189140750102c043c402240c42141884040710030705003a181c00100b0f003498403030001e00300103c560b9800c0303440c0e9400031005103e032180381c07003034030107042001c2e0945016050752074140140e00f80c4550070506503085000c1c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 848935863 1250 848934613 848934617
    0x60a030b0f04210e03010b03030c0a0204051f060f020d08070806040f0f0c030608010c030504080d05070c17120c040807061805031509010f0203040f0b18012d0606 71
    0x16000c544660466805280e110b806403801404910003004500e000380c0c8043d1800c0001840c80c0c011000b549800c0c800c0200c1c94008900551414001c0c0844c00e40360020054068401e6a48200203901d140392400010700a03421140a00c040c81e40320b0034041d00d03086052a5140041c4644a81030324158000e01490707024030314076111004036990300e8041001a04a182d0344000258455000d070294001030f005480f0300019035140860010704009120b401c44140c200d81b8020141850240310115004104440c506140d9810110742c03a07070f981005845254230304500414041c2c0281c05500c2d0f075031000015100300c5030146203240040e10303084a03541642c001c07400362092a030411b5404100190182c04c00c100407503c804000010143d44500287c2010562824000c01c0c020782ca08012003810203100b002c811048080c800c60071400d094032050001001c8240c001c1030700c00c0c400040b4001e16609070700c040e921040c4000900041d0043e0880030802c0c0c00395201c401001d4640034640c41f80301482d0003000c0c06d0300c00c00c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 848937113 1250 848935863 848935883
    0x30504060b19090e2d071e181503150b060708030108060f07021c020c03030d14070f09030201030e1f060f0e060d020d0c03050a060525080402060310120f0605060a03 72
    0x1605d01c03c18513143c5640c80c480d88120000011a40c103103e490402c294421608803000901c2c0c803422451110784548000310007031500050440801e001c44114013506c2d00210741d0103038007c58022142c01040c05800c3c807a0320110229041081004c4100110b0590710303c10b0540f412521581c100c0341145c94291200b40160304034042550318110154060703008003186104884400580c03a000c03d0465010404030b44140d500d40c0e00900842d8506250a90042503d103080103c8030940c2400421125031800000c0c105a160442c0c0d1590325010041d003841d80c3c032800c2103542409111409100100034502c102c0208200240c00054184618a28644500f10241c2400e0f06200b070769003048650704042100701c2c1e05c1361a1140100103c1c108001c44642e803841048001510304050881c0c0c2e0119010030030840050032480d5600040720343c0140f0080e0016410380c1d13070f03c0d02c80d103031910720032980b4101b074111000340d035500396082c01400a20000c25050a02400003040b1944981050020b91180b9010240c503071101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 848938363 1250 848937113 848937163
    0x201140a02030a090209040b0a0c0215130312051315060515030a2403032003071103011d1b010503010e04120302160f02121c030504060b19090e 63
    0x240d40c00a50348810340781c0c00002c0c4400c1c00d5000419002c800d580c1a02c4a01140c8104010f101c1103129448802c001400140410f03c13255217a5480303618000c001016003944000d08208040c062400c0c00c90740d000d11041070140c0d03d03128007810300c9510b1409059403111550110008042c0c0e40f4441c500644c0c00140c503030910009140e00010f4640e0010f07000c8000b09964480683d00e140c80041c4440d1800d04400c505507240b45507080c028a540101c038180310104520004054011200104681015a20945a1909112090000e401440e0030220001c04c0d0360b01000c420184200030505107801c082c2020b4100b962203001d0b0044455002c24010340203001d40200114000c5006070f07108004052240c030780503180c4103422054420020304070034225401d0301c0d104203643c1140343c440c1c083d041c034100410040a8190700c0c0e451004004000d900708805141c0d480010500f0f01819800c04807103284c01401c405284c1c154029180034058641c0b02c0c0c0240300e4a0702a91500000010807004004000c0c2042045482d0b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 848939613 1250 848938363 848938381
    0x1b0305093a080409060f080d05090108040b09150a0c03151d0c22030203150606180a0503070f0503061605040311010c0f0305210615090d050106091506020114 69
    0xc071540d09031004001030000055003844c5000d110040c1101503100020185010b050a1070500c240c400c0b034040c03000500501e50070b0790303010b040c1552080d082001480c16031543c100072400c00000c0303581c0a03540a07000e000c0002c4402107421610310700240359410406000030a0428061041700c0c000c103012031001080b845002116020f0710785d003102120026500e4000001c4038400c12409003140c114440031001c9040003985000c0c002090201c03042419406507251460000d6414070949510f0303002c84540001c1014241c4519003004080c2a0140864404548680301c2c04031403c40c1e449114801e02c6840c2c0016105100600c0c407046281e150388a0901b05400c582e0303012801c82c8100c0c151410811a400014003041990400821050003600c8082e650146080000340c8001035041e11200d4194000900c01140c94014550400300d0f0030019003034641c410341c00003400503c04072501520b150300f00343c8041a42e074200c1c0e000d030120070b58410b07070042100d640b1501a802c1e11000c406044022111100044480b2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 848940863 1250 848939613 848939719
    0xb1815121c0f050d05100302120115180b030303100305011d06010b16021008090606121c02010b0303030a0501050a060f021c110d0206040c0f03170a1b030509 69
    0x2c034041c14007504260100f400e0404407102140c40083c41c082041c4204154100320f010381801c82410b90090140d03c810b80b824041418a038412826031a002211116111925600800b80c0000c0201517954030706141c1207140450580307020554295207803080003010150308611400c030406002d800342c0800e80c41c0649050954012201c45e911006080c4001c0005076101401010f400500b0b8440440b0340c1050910300d85030450080c0300c0c42c01071484043c0003501c03100004002d40c00c0d6250350050000155a40001c81c054008581199018480807090200c0d80041e0b41010703060b078400b41c40c080441d070b03554003086521742200030507900542c0103100c40d41b41c055204c4480441c000418100343d070040020b0205545002800701040300160011402e00c010014142c100000a00e400100392140c40d045449080022440c012007890390314000521016040c0240f07030141c042c2c00610141883c10066046c06000c5078401d18a103849090f4040500059201305030240c03146c040c0144c005809e85542d0001a0900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 848942113 1250 848940863 848940887
    0x41a03010507080618060102010b10020109111c02040b0a05120304032a05281401080a060503031606090f0b04110904171608040906180902130b1815121c 67
    0x11354031044822855115006018503508055000250404140c01c100f0b07240c03034016208a100310e840c03404e84124170b600320340c0710350b09c0310307012207002802085100001d01c00c3d1203650701180c2c0007281b048448a00b0a0040040c20483c0d0240d0040b010820400024030401c8000362104d065403501814180401d081c070f50781603003940c01c0340d003034a45401088001001c0f142d141d580c0b04440402d000768968496581c030291030b58128214400500205007400d001a4880c044c0403110a140c0040032141d0301031000d260480d8860b039401040711260845141800700030488125425a0041103c408440e00c40c00c12092662103280c000d6111900d00040d00d88c04041544101c801400110303000584101003080d01d00204002e04100000103070081c508249030390a00050f10440420078607049440015843d82081c1120019010400040701902480011000403403118004100d4030540100f140756005005203600741e100840e034403e0702480c40c12409a8408d01c50344650b0040170a035000c01038403406240c203250700d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 848943363 1250 848942113 848942117
    0x1050108041520131e03032a03030b1519031e0e010c110d0509040c35130f020d02040603140c1302121311041a030105070806180601 58
    0x10f040442c00800e0003c5940c40700014005400203081c040c80300a68125001040c6214440002c2540090070740752800c040d202c040e090080d03200404122800406e0382501c001d1030300c206a0303010700300c904000300200a0303c0358050041d10087c05036441c0070402c10a44220490300c4104004074200200101d01401c0e1001460307400c40070100c480c2403014801d0250401282c0010000074a404454070002c150005040080b0b645800014487c0043c0d0b0f4002c044650445041ea00801c100a4408041700d000203900400c0050f03e00200e1800790300804a91484050b500c00880d603c401c0e1102d2000c1d0b286025000401420b01e424845410010b0070103a100c0020319000500000d0002c0d600e840c2e09044000d401c44201c8550800d5012000c1c1e4640702004145001c10b8100440c14910415603c849400c00909002e590a0880c80200c04008407001c3da4004518040c20038405c884000c94117081519441407454802d50034100003a000503c1941e42c144075040040865007000e030306160105210402812142c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 848944613 1250 848943363 848943371
    0x306141311040b040e06060f0d02060a0c081923090319020d120c051c0f0e04060803160302010f05040305040308030408040914070305060306010e06042f0a1205010501080415 76
    0x11440d41c40d88905c0c000748030ba07980130304001d140034010050702e14842c5408612a0040e000b0341c40141e190340341514800d586505002c103060481c0d040c030700224061623070b0042003542002c9906d052154440c2600003c940c400ca41d411070070428183c0500035010b0382d01c50a0301075000d490a4849000740000300303100d07140040c2c81c07140120fa09817240b5190264502002e40803c44000100c400c200080100c00d1521140503042d80064a0405004045410384803c107010040800c6281c11030b5599a40044020032070704088941e076106e0300800a540a4900d0803e0740994684880b100c0e02c0a02c2c0d00840b84500e6060b9941f40c82d1030b080d540c40d803031950800380064992284c28003000c1f401140303c0c401d170403c03207150780041e62a40c0350418004083c0c600040072a4080e4001c1c50040211080221610390800c00440340869103c01210410400c2c80e1250042807281c0c2c0c2c190702c28012541c00340e00900403501c240d0780f0111031240c82c0c1e018a065a9080c03040c140000c0d80d074000940030407130750741c034005100594810210f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 848945863 1250 848944613 848944631
    0x609030706020c0a06050705070e07020f070e060a05040e060f070903150911180109021605150105040c0207120807020d02040203040c1e0b0712030b060c010204030614131104 76
    0x603262060542200c00035078002e000140c854902905507500034012071034200d2801c07109650f0703076444136242d214401240192001250800b80280080815603400d0301c103c603110740d5100700300521300c1c00c2958018000d016240703000c6400d04241c0141c03001b080c40b01c0c0040c0100e490301041014540380040c1303418104032a0901c0480001d414080c455a100030030b039008211100141401168500340520300c601c1a401a40e1044450020410240c1110300301c0e4030040c0c48118a607507190b40c420001c1e80042c142d009180d90322580d00300c05140241602c4090b1401c100e10b410b801c000783c1e1794242c0d602401d000100c0b624000710028142c00000e104452014090380054081a80810b00346c2c4c0055408488c1c1c05040d0009100070840b03c003079105c110241442101c016443c00c0840000307031080d01400743c44101074035070f94544a0302a4010b01442d120180240c2d41e212400313513442d8001e420034007040301c0e154100405081480c2c401081103000f1401c0c01c0a24461060380c0c0e0b242e202d4458602401a0007a84840b865 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 848947113 1250 848945863 848945869
    0x18090a0b010306050603010605041806110c011811060a1b290a110306150904022802010b042a02070f09090212060c04030b0c07050109030c050c010c05060c090609 71
    0x8507008610510300400c107400d0801c00c15081d10450b4020b18001ca1070640c50103620503103204500130b21500b0a50028a8200501e09030400d485148540803841d0300345442070b940d50544000314005540034519520b4088105d00803c400c0e445148100c10005082c200c40e85070341c1c0c580c0403600b001e03244604158596400101014145108840049c5002c00750074000c020041d5028042c0d0144215800040791840c5440c0c400900340624594030914203600c042070034007203902c8550440b21a1404100e541c00707121305041d4001c40040e10b441756600194240034581d078940c20140503d410310003c400103543c10041a050500c01c52103001c102e0011442408070001e10321400c448904060241c0440c08100c80350365006200c02c1d040c92003040c46081c0d00020030030841c0c202d46004c4c1e800340d0f9440700a4103444e0300c4910140d049406000700181440d460165940101a005490203005521910980d00766100000064540d1340700c6040140c4030360005c03c0001d26050b02c11005041c8400c000302240d080c00001004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 848948363 1250 848947113 848947133
    0x4031202010e011b110703080d0b0303040512060612010216020f01120c0e01032a030b01050f1c230423071508010f0303020a0b040303060902070c050a080c18090a 71
    0xa0070104d203801d00302c0141264410b4810a2520f0034074010000c140c070350340c1d03040402c4c490034640740400307580c0e030446148030354041c405c0f2001480001c159140e04128520002d86034081990030070310903161118281003000040c000e8030703a441a070b5010350142d041103800f84010290851182410800c460020314550000c6100f41d200120700c640c0c89200c03026078440090215466500c80318810612444401c02d180d120080b010b11884962501064000e60b080050300c0900800b5500c407000300d0045102500c2d82c01c000c514902c3c042c0504002e00801d0402c22401c030320b8070201da202d012504504e40c0010082100c00061085401c200b032002100f0300c0b50302c841d0701d003041d8594001c10080113103c00403000e090750003500140506451364070104030f54038640e0060364856040c1c4004281161400003e000d240c002d074890300c010802c05130203655440152038204e014078180e0081030310560000e500400d0b0420000340c0120300302c1024051855550120483e1480b00d08000c040700c3e2a03100b03c100510001d80c0e5414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 848949613 1250 848948363 848948381
    0x9153207060626060412030e061504060603270203100606030e1c052b1a03070f06170907081f0507050304020607030e0d02040608070515090604031202010e01 69
    0x10740000d0240c100020520007424400d00c50003e0040e41c01d0010b59a0b0004c0f0707045422079030100c940c01d0f54103644101640a40810740c1444003900501d820003003d152102c0c450710310300700102c40402009031110700c10340c1101c07003201000a800b0400c1c1e8191003589609070202462500080480e202594000b1803102552181d41000c0002a00c4142c20391080c0000c001d980403002c020110540500d407282e0300107045001d21150740003441c07001da42014502500c081041100340c801181801100083d0442c8401c0c03d09588174a40680b0416800140b0000c8002241c42655903c0d910b4205035855a0550100daaa0113071204049026041000602004c10820706e4464141034500420725001c1850290840707100601c0002400310810421006039a03180441d00301660500b041d1021645403001304100002c0028000d404c80d01d0080b0104c0c48400010703404089900c204c4814404d000103041c030718a1030048840560300038030305100610010f0200b18444401d1105880009660100242d0480c291040f041d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 848950863 1250 848949613 848949623
    0xb03010b12090c0102060c030a0b0d0c2309060103020c0c03190210020a08160516030501050a0b01051303030507051218090a02070201020618070803041509153207 71
    0x141c4440e2248000400c10360044081c00038000d41160b920001c0d446210081410718120800400119425400c2d030080b001048040d0034100c0400315864003000c0c9080901580380000744900c0c800ca070f10208880c040d0000c2c00301410f06105901c410006402940000380d1140d1203004030380b6a24002e0720304104940d004141c0c028040d05144007401841604500c588641086402940001d00864084000c85010b080c10303204084c039404a5050032070078100080b0803403015449c2c00c20f001003400300541155000d142160020403170b5035140c0303005460324400c034200d02d107a2006448080012030f000c0c10103007004501a0007640c101800d014941900c0b0b80c8914075000b23042c0c40d89092844039080100c1210703403000d803400e030440c503140e0b40c1e40011350742c3c0b0030041a2604628103104401d40000341401490014115441282d403100d4940c081c0b84009401d00c590f0100080f09440b0014206401d42040c200307082e11620741d5099102124070300c010300e40030480c40b640000c0d089250118020b07001001040320038016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 848952113 1250 848950863 848950867
    0x30e01051b010f2003130204060305060a05040c060f12091703180613150c110a05010209040e030a080403120902130b0310020c1b0d0b010618080a200102070b03010b 72
    0x402080000c8030040803420401010000c515282904e0540880350820114030006c0320f4208507100180240ca40b58000921034041c10b0f0500c030034044136807c071034055445900c4155985482d0902103525500701442c030400290800d03040720b080105607000d40056030050843c1c0314040680b0b4548030040c0d05c1901d007030481c00702800c00d4051b980000d0041c00c1d042140e03c80d50303040c5110350391500603d0300101c03032038528219078803c00c2c4110f807409045854031664001041d1a00751a41e414624005c1d00441c0e00c030b43c00381b81000440d905080c0003004454002101c1c1e01da400c0c942d1601e4404841841070402c0010b40b0a43c1c40704210050390b1140c41e0208e25103a20500440c8281d214014181000034140304e2814160061050311641e240c003180d4200c1042c4000c201000c00d841a80c001021076084980152019120000100e00298801d41050440c8484681120505d580d144003d03076a032080741c0060101c202c040f081d010200124900c010198405104441c26280c0750705046406500c2070380807a90803140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 848953363 1250 848952113 848952131
    0x19050304050f010b060f0901032909010f062c061c15150c051f0905060108120909060f04140601030b0105070b01091d0118030813050a030e01051b01 65
    0x1040200c2d5549001c0007000744040c9160202081c2e5600032521204060003012031420640d0344641d00694007403030031140034071b500c01c0c840c1c00c1b00c2130030365180212138058a2104000b00b0350090050403141120f1050355200440000710085160b469070155941d030140070b034000103200d1707640c440c070140c041610304410107008080c102d410030080751590040590342003c1440100601040340b108944801210304215013500ca0600c1c055042852522a4090505e4078a5111043c1c1c0c500d64041d1454500c104112203603030340c81d1034045a64100705000f00c503070703000b08002c2420030341007240c4400e0b0030a0010341f500340500c16100010301591020516414803071807402c1003003004d607414051004110000e00304685403000548550030103a0050151500300c0e40ca80301060450310b114602e0405980c025402002410a501e40440810407868410307400201450040342c80303002c51a4008802680c4800249606801c0d5507049c2d03168121401c0290600500380204460b10b5407456007440042300301c0c8000644010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 848954613 1250 848953363 848953373
    0xc0d0908030f0f07020a0318050a03060f060b1c0b0105070f03030b04051605070b13021002150f010b0d33180204030302070909051c05030f060415180219050304 70
    0x50092105064140c46030521005176000b00b0420280b0b905890240034844e2101c40284c20308540b60300130790308441d50384d5000080c01410b40c440c00800788a0b001c2440b031241d44004011070390064010500c0300c51109064101d1120040d880f00d40305800604196090aa440d202c00c0c1030300b1001751090740405e44070b40001000e8030302403040c0c1d070740720b40761800d206140c040d0500020040c0c081c480f00140007141d80404100e81039040c004003500d0a40c0104101c11411003028029169420009031100840c030b260003040d4245166124941607070384945040d810a201003140d140503040c1c0c41c28551201c000b204405c200c0007280c1104460100700716510404003450f0007070011107a844030b90031003452441031000b4000a540464400e0407078a50804c08a110b1090f81011810034021840c01e11001e09400c80018840b038000c0003552003840c1c0c03413500c60121794bc0c42c0309000940301c1c61040324560b090864402d00881c0441140e208151041c018014203101400381440209102010458007054000c010001089 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 848955863 1250 848954613 848954641
    0x4110711010306081b04150b130e010b0906070606030c0f14090906060d11040c0806030f0c100f0e033a080115031b08090106060804020a030b0c0d090803 67
    0x145082c039080121529024485407900d0b203200702c800328454800d050071920307030300c540100c0c1d0701004d0703054010b04581c2d0f1441c0714100c41d408603214a0700401c800b040011440d010307a42e80e41c1220ba0b0303007609030328000001c800c01c0b14984c0302c6401254a240d0307400001c13012454501070100a840d0794107080000900b0080511106018080418450a0018100403880300d004c00c01039000401900d150f05808076030f141c40c0100840d92030405802c5072800400b0028254420b128601070481030301a29609030100e4003a98403105208109030700091203202c1d10b01c000d4404c5080499088840c0b5015090300300c500002400c0c1913402610f41c10002d03d06881452001c541c04008003000c4521b9409202406080406080d680051003002c007007507111103403085001e000b03402401c0e11100081148030040002d0b100680410070644180d50075601e407d0002c9a224040c07107a0a02440d0002c00400c500d03482d5507900003015400801c0460303816014488550b4080a502030314121a2081540948a1414180b0a100e070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 848957113 1250 848955863 848955893
    0x73302010e0f190204020f040e0403030603030f1e0509060d020c010203010306060e0910051902130e0c0720030f060103050607180513090c0f0803041a03090303071b02041107 76
    0x50f004502c0d04007031240741035003040300a5815100580c6941014240b440140129400446080c00007400c000425505604c201c0641307200b5165003480240d500300485221070400c01c0040990302040c210700305180600064291070b0b0380140b50b1480e1001504842c01a40c000c005540040c1e90084018420451580210b401815003103078104081c0c03401960300b80d81d40c10001e001c2a00c03990784002007807003403201480b83d540100040c070096648005010214500b01c1c102d2207210700300007030600414400c581550849070707031a4024030703002c05040388862082907900c020034040e030f418886c000c0d00201c4d407542440628001c41c01600908014648a4006400f0401000b2040d082c200c50240501090ba108059038a6050030f01c0d8001400300c2141c6407451062490703401c140c20303100e880000010400e20001c002c1c401e540002c400c14500b8001c041a2040e54041994050000d400510020350307103e01c2025400d403101d012840780c0c14404490380100d01200c01c0050100c3d24164000342c144288000e0110754005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 848958363 1250 848957113 848957143
    0xb0c06090c03120406031104120803070905330904060e010807050109210f020918010b040b0f091b0a030c1107080d0c050a1707120c05073302010e 64
    0x1405800b840300035611300c250302070304040c581e460349130346003001d603210944000d03101e80701c20707071000801da400d0100f121340007190100d002600d204004191401c08500c030251442e1185424407100188400c401680386941200300c2250f07000380410030080c0e07264003d04006001030322104ca85541003401c524102001600050b05009001070100f010350005504044400401810320120040138901207040b0384000304e02a40c01400c1400348004004210710254401d62110000c0140941c5001070001382d44501114544c800700000155009061400d411396001068101c002c440e0b01d082c002d4441203400c0095080d0000343c1c0c40e418900460307001910011a001c0000090014501c0d00a916030b4030280c0d00c07400001c021b20300d240d01040200c01c01c14a1039a45d4001c024000c010a0902009460f8101c40d400f0f9038440c681803040e4903840e010302c4058a51582103806040180e007000d03502c2c003481003514101061585e50880c02c1c4c654039101200640340e0f070050b47c004100d10481d52100c503d0b00290000200c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 848959613 1250 848958363 848958373
    0x100318111207050916050c0a08040617060310020307050d05101401020307050607050901121b0e09040804030f0201051b1c02030f091e060301121703090d03150b0c06090c03 75
    0x210342d070340300c1c40e4499102d840c50350b01c03017140f03e40000f048400d0301807040d007050148100710705101000101c901030000d4400755580c188408564141e68007480750309a078240c3d010b41081800d0541c0c21556001198800c3c1503041403031404442c60301900c1218070460b00c508400203008002c1c000c6c2c900380780704051840800d02c000d46c203000c150380700e00b900c1e098090410400d108000800c0800d9901600c107040c44040320b01c0e410026505010150400c2200c3d4890400005145e5850003505140982405029581286c0b1842c1007900f1a0303203111400300074400c160306110050081010305030030b9003500c0843d403500320081d118910b607110341034480300042500b6601b503420510418402c1442d150030f460100c102124069403240000e8103030f910200001c1d400540280340000003081040b10440a900c5540c810344080391103180d44091222140070030b807074040311600302c818510340d5a80f003500107607079546981c020078000c00d5503000080c0b80f603844120007a030170390400740800c64110030601070520310400130b0f00a00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 848960863 1250 848959613 848959619
    0x40f1202010314090c0d05071203050c0f01020a0c110d080406030c1e022d01020324010906080f100f060f0315050306010302061b0307080c01180b06100318111207 71
    0xb80c50b542c0340c0001c03e000740c00000c00041404410023604008240343c260030307021492681001070080e401320300e030030041e44203c141c0e010204405101300c036007410565070383e803501000c0c42d602d101520200c5e103442c560040b550751000d80415000e000810050040341c90008101000e040060240d02c4c0204090025410344408007400701d030041100b03085900003049a86c0743d6005400c0c10204494401d410003020361011007080302080b0b0b0070140b120546a1440900e04d038010301e86c011904201c440c05840000385255000c41e10281d1803182168006100f0601000510345403454005654005e81c03069000400802c102034490760075100d005001d4056088090381c0504010100c0d0740d941040c403009000b104006003800305400304ca50b0407244c589546044c3e9079102541e06004085420129984510354a800c020303402c0c006000102c80c4c00d481d44580c0c143d03d65512802000070b41114a41c0d58010f050b102d4492207200c04031004020800d511030860b0451002580090142651a0182407842680f14030014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 848962113 1250 848960863 848960881
    0x3051e010c0e1c0f0b0708010e0109090309050f1c0c141f0c1a0403090905090c030715030b0303070f0b09120d0507091701050414120f070503040f1202010314 69
    0x643c0300c0355440030128446480d46003a00324030000e404003030494441401070010729503100118038104c8015030040401a6240c2886c442101d00040e402000300d1000001041941814804606c0341c9200400441046041c1031000f412011034403000c440c502c0b400c220030b000d0200300e0b004183c0000408e840380e0041010003001044000001c41c404070a0020310b48029003044030008911031882d21440c404c40d618100380c600a896441e00d405600200e90400000510600380064003e25540009006110035131400034400f07108113070b4001d0700c0101038480b40b0915454508000502c0c1183c0705140800200b82d45013406ca5402c100609619001d400081000c0390304840c4109035034506120f220b002440e612102420380f00c4c050141d02ca440c28a02c0700516902c1c240701948804c0c0328901a21510010f511060b9085440e128070100310b416441d0b0500c03506800560b04400f82c034103030344282c080b246019110714045030050b610b64407000c50026040484011540c0c140107210810748860a81c19950070020f4003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 848963363 1250 848962113 848962129
    0x901050705070c090b1504030c0312080f0f100b040602061012030807321902013b1f060b07081602040f0e01060303090b040312110703051e010c0e 64
    0x3009509500c6105120f03ca0b0703600444181218000301b034013551a5601e1400000c0401c007440151070310035680c40010400303030244d10f10502c980076992495030a0341d00c0c422000000d18000d800402c4a40202c040442d02840010081000c0d0100e60003c20643c6420100401c0700c0d0510380062032107010301a0760200081d00b100d100303a00311a550600e40740c2019521480c1c0059400e00f2241a034448425010411b00103080f40241400c0e10320401025840300040c070240d09851321a08a2081ca05d103407100d03c0714448070600000c0314180290a00703180c1d60700c0030500e00e2400402002400d00000b28204840d080038803481200020400031940c10b003403a0300e64031912014020f94103e01043d262841103e8215550b59001c2d4200074044102004901c00003030703106009000501007140460096400415092110001d54003200d912038450b1103401c800140481c0d01680320001c494a500c02e00e10f0200c001740d0305100b441208590041511516400c001e405400d403015500740d0307418045000800003940d250410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 848964613 1250 848963363 848963369
    0xc1e1a0a141207030b120705060a0c0c0302090106022b050d0c17010b031806090c010c03021f2703120c230405030609030f030114010c0210080901050705070c 69
    0x4228061800408640000c0e1044280e01c800c01021181004242d42d00b40d17011000d40c0d00c0030707100902281c90402c50150b9070040d0b80030342503000d04180300c015490340c8500c41d1500403901c54201c001c0081d81d07a501044121000380c0200300580c0002c0b4094121056222040b00e680c04041003030301c0d00307001d08030700034142d403003044140c1007080c0c0c4441110003180c1c001e070460039140080155624443da520341d210200c0350415a00b40c2139420381501881002c2c880020454041e001d45400713400031000079401501c4580e1a6a0100c00790b00038424562042c850011402d00412032840d400310301e0700300480521401c0e907400130b00c4012281e00700d030215020139446035100700500030240340041c021804801c1691004100ca207a0034401000c1075008281030311000c05001140c0342542150318680318000e440341c503400f0710407070b044003040d0500040121010421051260513410705181060705000c0e0085100b8a0406504d0b03c04582c01c01c2c140800c1038000d100e5964062240e1070319609001940e900c804a42081d48 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 848965863 1250 848964613 848964617
    0x10207030c05010509181302030705150d051f140109090e0d0c03140406031b030b180705090405150f0f01020a080309030f0c06010602210306120a0c1e1a0a 68
    0x20540307800031b032559010380300400c16081c001c43d0140303403590b6442d00c40301070302100700c1c0680103001d40029281403001c02020843c00d40135040342404c0d803525014004020007400900031f1442618030700100d041b034010300300160003003950034a990b01c101070001d010100c1642c082003215183c621500600d100114400903180318600c0c001c01d41c1d803030b01d0078121292181c0708004d0f0412000003d0005030f098056000b90010117494a4586a45810075010f60485250507400f0f60040c1f04020030704880c41007407400b1584403405013402810124040302203003c03100d0440304c0e602002061030f55007034945042443c81c5c04518007141c10f803001405141c0000c0d00c0c0c020356900101143c1002c03001c03e902000520941e188a4840100640c4440c400b95205a03141c100384a03480c007500032862501d00101803602107004059118247c0361454580d2818400c51142c034003130024150281040c080d00050310380b000700f00104409000000711f142603814004090340540d100200095807007818001c01c03000081500c00e0b40c04030f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 848967113 1250 848965863 848965867
    0x10c030507150606050904060b1206060a1103070b011d0702030a1d0303121b090d0308070302070f06270c05040c050d11030f090c0121021b0a050606010207030c050105 73
    0x40c50140d0542d07110780c2561007181e00700140882d4140d40040540841070341203900b4881c84c1d82e03480310010303a48030701c120000484100c000007400398107068000703126034146440c250a10303c462829803404c5400c0918125142c0d503c401c01000340c0804260000808060b034402c8000f1740c1819103005c4d50b01d200e4035900405000c0c05440a0281c4603110307209030061000a03060703030b035183c2c2251059400000f08640c601c010602c002d40320114002107009480c03048401900300f54640c2c1c030a440c1529450301c01821142016000c102c80b800051135410405c1c06240b00d00404603c0542c841c0a101e2000d047e461085100c0c40c0b00390403038012420340e558240407500203440000c4e545402d2202190144611003000b00003a0520307801035400d5584000540c45171480e0465690300b80c03198a89942caa0100303600b0700380069a047c0d1080484000000034880641c0440c01c01840d16022080840d6280b403c8250300c0741581100d040d110a005092001d03ea03c4030003480540107081c207554071203112000e50b010780c41c100800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 848968363 1250 848967113 848967127
    0xb030309101209020414070201050f0709030314090d151b0806090a180b0402040c0e0121061716060306080307060e3d02130603090501020403020a03080a110c010c0305 73
    0x1603600890f04140c000e04140800c0c000c803078801040c0f000548010006603e8000004e00380d150048038203020701d0703595071110580c42c519202280c0d0444501c21503a0361a000700440c03002980c900b001504103d101d2806442ca01d1908000340302140c4ca0b16015a81d24135a210440072100c2c8c0c010a038650052003180c1d9030301e15840d00038140005090603a000c2241d9001c050210f4140040c4d40341c0c051140c1c2c0700b11810b01c0044880c007401c5420f0381c0c00845e92030101e61300c1108010780281410a004040700075420002e03405580b04205042598818100016600102030042d0308580700c10601c005001182820702446240c1649542d883c8240e0f00c010300f01c19500d10328004444000e100c0081000c229a403920824140b01c9001080170700d100110041c0c03080c020f0b40708a840c01c15030080d80c00d070700200a480d8050a20b0135400b40c0180c89800c41c100c655544c204004001a6514005007000d140944810354031141020030240540242d41d0303221101f584500000050b981e0702c0444807100583c149006900c85203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 848969613 1250 848968363 848968397
    0x11060c1812030f030c1c0204050d02100c081b0105060a0b0a050304030512100608070e0108070309080702060a170901020705071a1317010c0513031101110d09090b03030910 75
    0x25001d5000d0101c070000050144032901d0703c0240540c1082c21141176041b41800360918128802c910503e5005241c4030028030151400c00e0f40c107040140b80c0d040c110502e546940e0356182960010300711501c1d00042007040100e1410901c54145d1211064450b030014506154142e045405141200300030010000f001a007050f2160051f01c401120b1008490380300e003001350202c040490940155800143c4500010314074621031b04141d02244410307103880711140c50f210170480203082e01071070070356000108100c00381c01a1500c0c00100507282d080d5541541e502c84480c2001c900c42c9014210003010782c010f205200100b100401c100007241d401450703802e4000410300000c84a4010841c24050052680d4030000d140c2100318018a220800a00204040d00c002d09042d82c0a000f10200c40320440300b55181480010b60300009545190014180b4110780c3d6000304619180085650465002913080c9070300300300c032452a0054104a050840141d800c01c104034000c10482d80346a0225001c02c02800c1d6a440d400c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 848970863 1250 848969613 848969617
    0x81620092a0f0304150e1504020910030f080c061e0a1e02070b15060f03010504020a021507020d02060a02040e060d1401150512030301080307060e07090c11060c181203 73
    0x160074042190f03160300e0b060034452034104821202c070f40040e0400603060000c440115402c21006081c01001c81d0036243d0380c00340000c0b01e60080c840240c12000c00c50200100748600701442c0d007944a11500b6545510940242d0f06203180a40743c0038004040340c3e00505410034030410700e544010307521800a1b030320040c28a6024841104880622500e100290103418041c0300d0740c450b44984010002c4036a440001d4040c0083c071300c1501c14100191106000500c51807405070001c040400381d0388100d404070303461001054250017007a40c3c0740015038070001080c5499a01446031b280e00031280f1004504252800202c28002d070801000c0c144035a44c813101400030005840003004869450400030455014000b82c1142d0f8101d00c4d01801c1d20459200b102030044c8c00c00001107a040c0c40ca142c01860400040307a6401000d0490045007140c10f006000000c90742d00030a1003840030001c11031741c400c6106200880450f060203405048400110002c1100d41204a130007460300c2030a2100703071407110078144240301c498214 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 848972113 1250 848970863 848970877
    0x30302100e1518070806070c140a140307030e0103110406030902120f030c06090c0d15110f030a0f0b0907181509051002060103020a0603020304081620092a 68
    0x440a400c10b01030f803040b01c0400c200341d040c4038030112203c1075121084642e80301002c5510b00d0019030a42000d000080105030306503504a41c030700865426103881d80d92030305c00705d460750382a040540c004155001495449040044000d4083c24100050144550499120711030f07400341c14207150300c1d200c80804540381c6803081001c183c0c0c100d0542e00c400e003400d642c59840f41c0c400c1200000510800011071a07c1d8800324003408460002481c40c6c2c00740145030344070000c690090304100790300c0b50340d4071040c2d40c2c00815400400400c0d41e054000b564918040762883c040b10000c0f52031900e803501d000032854803900c40f000c1c900d070418928109507503950300440001841c0c4019410800c800c003100340c00070701e520381c01007900000e85000700c13180e0f0010700079050200e940720b00900c40030354000d102410070800356010340c0c000c541103401003224034680754403028400450101c010045404032041c2003114801c0350288800b0010702c0080301c0d000803a08181c3d001c40303900d4150300200224a02c0501c00800442030400881d041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 848973363 1250 848972113 848972143
    0x4030602070f170a0207060e03030a03051b0d020306100e030d11010b0a030c030201230313030c140606040615140a0c0203070e0f071b12030b0a120c05010801030302100e 74
    0x211903040d01c3d1a070843c03601c00c1c015101e2a9004500c00b402210321035080c4a000e00117600b8204011021000303408084c0960451000302c185000510100300c0c0103005da11980e01c4050b13680d0a000c400e000c295503031a00414200282c80700341111903500815041c0c0341048515100c020101c08403d001d00501d00404c000d5400300c007a04000042010b01c0d141d50040324000d0700d0f4041003a4166003540c03007022949003200140e100c1000000d0030f08000e1050a45154000d1414800910842d915600303ea0321060f104c4506500440400450f49028003070075014040c0050050660003601202619005d41e82011103c44d450104030740f0b80d003c0c40346049c1c940d8660024100d401040d030754503171500c03540030a07910b41207541904000240150300030f208904030881d4445085000303002c0354980710700e442d0300d0800326010561541280c0c040340c0d5030194a08042d00d818064140001c09504d020b02c580269a40030301d041c08514801000801d40208203104a0b09440002103100c850700d40006040007910405902 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 848974613 1250 848973363 848973383
    0x1118040b0409060545030409021b06070905030304210b010b070b090106030f12031506030605010e0301110f0c0127020315061c1407290f04030602070f 66
    0x1040c440c0b1604544d000b03c1d1030744051080e4464a02186501d58a4100048451480300100300c0d0007510f1243d0001c441c403901426242410b44500e80641030b80d100c1030380c422118040d00ea6220b4ad8480c01d108058019285050017200180741c10b010940f41e001d035204900b0744d525001030403a01b0380380e4407004801036a80045041020340c1c5807038481c8203030b4010081c1512007003440000103400c40c0c014451002600c0e0402240c50015203241c1e100c056850b0341c980000205038448021007129080e4000000280103203403400310f8a641828001460648a048440d100740e0421003035103c2c001c17070b02007103407601e80319038003006e81d54a07400200c0c5015190a000030700c086011250311680b0707005280b0354ce00c0e2661080b410740b44103651840e011108058240ca040d50301012400c040b00000d41c005981800303041c4249108070744104036034040c03801d01c80e42e80e0103252401100203101c40b1420101c1c1142504540e420b85407405d0103140580030043d40101d0000810441d8001054001d21200c0c1d110404095403107080da00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 848975863 1250 848974613 848974631
    0x1050f10091403101b1d0d0807050f0105040302070515031b09030712030806130c02070e0628051008091207020d061a040515010203030619150309151118040b04 70
    0x2100e030745001081900024201000c500d0300d00b21100e520809101c00500c141f050010305e4032210881c0e0703c44282101ca912602c580141c000c50203001d210300c603500940103055000c1c41d10003441081401d1000302601070b502001000100d0b1404285810f0f00600b10140390744941c02000403a107440466004070340c07802603091024042685c8560600d10485003911900e0154140806560a4070781034107c01025070405242441654401080550b000c400180041c07000001c8804040410b4003001007088616001d40c0140224100702c19484403e51951516071500e250030342c1d405454003444450741c52180c10020f6050195598002c09052482c0c00007802c0280c107492815108404d54030280403802142090f000489046d00140360301351010060b0040c1d45075030380b0001003000244074840882584039260002142c00e44080315101070b07260554400207130b40c404a0401d00401c1202d03d84072001c060501000107001c01e0418244d81c00c10700240b8021021495100024010307004c1010510340280c0341c0b0f0b02003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 848977113 1250 848975863 848975891
    0x31128090611060a0b0f19060e18070c020a150c1403210a09080a020f010606050405100e121f0b040b0a0314011b0c0b011a04050603041e06020301050f1009140310 71
    0x150f402c840c030036203074100d04c242c104080c000c0c084115440c03044480ad50200141d29540906000c2207020710042241b142d19445149205080704050520300009001c03201c504104021590024490740c0d4010055003040e4418400d41030091941a92800505419010526140d125000703070190f10b50081c0c403aa03c0b04203504001750b071490b034100071029941c240440042c450b0300078403c690a864014002e08003d120b540d80542d1990200d040994202019403041c120940d0113000c3c0d074000e100d140084000300043c01d0082e0701603d1603800000c0c8202d10380001c000417955040c0020084039071240c540c41d0003a9840c1250360051110080e0402441000340400d0807035903104240d000741c184203404908041c0d8807565001c9a241d040031490990035030412003800586420000346a015100380b80f44403882c0b084464007214012040011030f2125004070043c03001c0e1070194110460404152012043c407425500c0050061400744540781d112518007000810a032014006000c0110a4160600518101500c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 848978363 1250 848977113 848977159
    0xc01091a06131104090e1005011e14060a08060f042d0501140d021903080d0614090f1803030f0a18030e01031128090611060a0b0f 57
    0x105104910840341d00b10103015521030300200301c00000c40c50307040c9400d000d0910000d01038981002960710803102422011201382c0036035800307031000c400e080e810008006205c101d038000e60b412034000e032000c038040290039882d582c040d43c8101503649002107050b01c0314030204a03001e40346440c840c0c01c1030906d4040240846d81c42c1050045420418501400c0d00d002d803030110803075030280507019a186004a1885031440d040409113165400180512402c800c030650741d01d4100c1080d80111110540032403404050f812078451100140000841e01d9101600c1c2d20025046c11001801130311012401d801041030340150720309111f00d50b606001101d580781410940c805050400725a040704042c03c1c103050385c00003451b0030740d501c09130f641c19101d60548680d10001500603014804656103036600a216000070808070100e002800140842e04410344050502c00800312401d0341c11440502002120110141c44005480d030303030080442e80009902d01810000a40280f040d1407001c1d40003805d0b01c00e850000c1040c0c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 848979613 1250 848978363 848978371
    0x409080a09051c020a0e0a0e07090606140c0a030c141b190f06110c04020d2003150f0a08150f0708040305030a15090c03090209180703080c01091a 64
    0x2981c09041c50303180c5000f0b800d800300c00fa402900040f181000700b1180c425008a580c2000b4483c1001c075039006840031440c54040a40e016918071901c0f032400300006074110320480c2c4000e00b04040d583c6000e644224141d80c400c2400b1000f01044130040720741c0c080c00592b5010040b150b100c101034034282e07844540f0141c0075410f60145070307120350800095403256546003000030717007160690032400402c2c515285003945d01807070700318210200303002e41c01896030030355220310040051116001e000202d0003003070042c0c5102003484006a05004208005000c05180500420100d80500b12001c10080c4030000200d030089000c1d51081c0240c1c0700d1801c6011580d0721003950700d0700c103e0b80500380058031340d502002194036a03820383d00640801c2d810004100e246003542c2080c0580c892b1140e40e0416582e0381c1e090803084400d54100c8000080e40e440002046261141d0707000e402c180c0f11711208400301c2800d0304d00c0d611003d0341d100042810070b0008202034494021b40001d40e55a80003070150010840000723840e40f40f150211 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 848980863 1250 848979613 848979619
    0x50a020a02040513031e0206041202030c010603080403060e0606030705040c090803042403110d050402040b030a050706020c0a05030c040e150a0b0f01030e151506220626060409080a0905 81
    0x100c212843d140131000181000720039030300900840d149c0d920b4900c0e04070100140441107000402c40c10740b100c40d09003e00401144111a03c50741d861850a20908076110207042038030070b070400401e01c12160b400003400401d2350300490f40040c41c07503030485007502d0100080d4845026400003150001c1c002c144000c03502011a00c00d0040d2161440b0244100d00310b500d076103410780c0595030600a070400c814266100a900070b10207800094040030b5000007900d012480c0350201d800d544081c02c01d109071941408441c40390041130b14003807002800c01c00000c1d1101c801e01445402107135140a02c8160390410045141c40806e140c44110582c1080c1500002800d07038100303000c0c06560040c28500540d4840d100b1002c80170f11342000b0b48070720092000041c0c0e03003090203000344188000004044045607504001801080c40000c03140000400d40c5524100c121926403043c01805050f10541045e58090944080303042c800c038030495440d45e68140018010204800050401c1402080d0240f42a030003007802e5081d21421 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 848982113 1250 848980863 848980877
    0xc03120a020a09060c0b01090b0604030b0a09150605030703020402250818060301061707140a02030d05070206040305250f0f020406090e0c0409060e0105161e080601050a020a0204051303 81
    0x8141c00d17100045a1030008086042c1a40100403038280c5034040c0d8595900104428a80f075a640c89481804806403007a0340202d030b44010510422441021100c004400020b091065074a03280000351940c80e40e2201900894001070818503e4a03c054544071004001c47c0351186100d1a0403c400b0a1b0800c0d00031100c0300080007044806864410305590480e01e840d5184181c03816560380f29840b943e4040c0030f001c140a1107a002200c0300000002403e00280683e009544aa56166918007503a030054058000d6400180c20f020200340d05c0422185241c0ca44440407841448507a140340600220070009807201c3d00481429003003082e1400307900c200364000c80d0300b803055945607c10042203442489144030142e005000108003030906402041199015070000150310441380360450030340c0c4d01204d42035620344a19031036600141e0080c1e8940740720445545203031004086880060410000604514103006021666950703082c420010040302d070b075010780b00703004504162121040004071042c0c00ca02203012 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 848983363 1250 848982113 848982119
    0x1a03090106151128030f09033309020d300c05010e0f1c0e0a090203060a0803030705031b0d09030f120207050c0f18040c1505090907050c03120a020a09 66
    0x1160001000c200c00500c6010001320310703035025200703d04022980303014020011000400300d2403a0015043e50322007510302c40f00401d0b0001007000c080c1d0f484d59141100600d011300300341c0961103081030952180c0d4490a4031341d40b040c4503c410300d175205490804003007640410480211007a032040c0b4002d6802d104c0c0c40288044258074407080c0c1c0b50b0022601c0c03403046a02c15003012204540c2104c040741d0600080c280703907240040c0c206c0402c808045a4024412042e00041404443c0c1007091002009150307804c09075045041201004045110140841495403404401c801c00702d480c5200302c0314108441c000402c4000c0603480d024206525131b03c03419012030085000089414118000c849042c0d40c07040180c61400d081c1070822039008015035600f03030041e104904159404403c40c810b940681e0250500d44581894000c032101100030343e0300104100a0184480001030325411500f0f50045950b041c1162541c548600f102d185005200491142c07000590038459a200294001c08079040160703643d2040f951 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 848984613 1250 848983363 848983393
    0xd0c0201051e0a020c010204080d0816081b090904200a0303021f020714071a0c0a24090605010f0504020c03030c25150f05011a030901061511 62
    0x2088900410b039401107035061110550307861186911419510005040c183d0b41600740d1b007240c1068106041c0c2d81e00003503552940c180c01c8010294042900d181000c46c054140301c000b01083d001420180d10814103030841c0002d6480340e0140d5100d003a02504034441850709040070000b101101c000600c00b0700007465281c509040640c0860709403a01070700140303500b44c050040500300c0040c18241d405015800d200400000b450ba071101c2408030300724002442c0d01820040b40141c200a80414a420314500300a00d400c03242c0e0109004941c0c640202c01d0010030820304100f000b881c0c5003441d510b5200d03450502c0710720803c45968400c40c161260007240003000b90301c40c0d0500c0100d1041c03068410599200f4000684c0110001004002600b410f40c0e08105040300500205d07944140780804603020b1720b5204001194107603c1c0701d4410180e440d0181482a03515040814205407003074600501d1407100000002c0416000b504010001c0941405260b1030500c40074005000b43e4600040010a0060404010f6454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 848985863 1250 848984613 848984621
    0x100c0305241c0203070312050703020d09050a0509091f060f080a021c0804080d030b03010c0c020a0510050c070602010615030e1b01030f050c0a09080f060411061e0d0c0201 75
    0x1c0005040300140c80001e006021400e025207a0499251252110110000d00789a031003000e003032950b0325481d4495500d454044e0400315a004040200032002a0401041e5a001904400c0324026948150705407280909142000594000f09600d0b841343c84040250b40c599500980841e4a8810000750194540c40481d4032a101b500e0042e600000f49174010b0705030000b000c03010700c540d07228140a5140036921f401070f900703046000110501081c0c0e00c1109460382e050a015501943e4014039140417a00302550000301c08a20300c1c00307940d0042100320602070707510b4000d03012552003203080d404980c4010740d6108002d01034216401050061024546080c2c4020b00a00403401c4059800008d40142c0c2032030b024151040e41c0c00402541090345600800c80c107003960f40b107058020340700820101e40e5094000c04c09403138803405a200350704650113951718140e4040081141500705030f01000300100400060005031481c099543c0c4410402c0045189101a02c41c9600a00840342d110a080c001e407428000c0c207900b29 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 848987113 1250 848985863 848985931
    0x17250609050303041d0c0c06270313090e070906090605151312110603090601081c0207210206030108060f060402120708071803230304150e03100c0305 66
    0x70411104c0d128170300301d130603d075540c014007421410b0b0404842c1000c139458070100760746540100c03d0a0745400499824404404603552a04000f1450028105046141d128142c40740d24103050b603a10400d03150300700500150005002520040c400306840b0f070020380c0142424030910344104480d0b03806450801015051b10583c08134401d41d000c4040ca080c20b07001c2848a001c4e002c4403030b05854008081c490355140301450240306104d000700029030600da8018600f13401940b100420900b00700304925a60345c0090341d003068400e0010303a5020740c111800c4c038000004541500035402200400042101040002c49901c00c0e0b02c080d89846141d03d58005000c2280301701404503142c88c150f40300042a09000310100c036001840c0d8600014552072600c094841d0750001d40003259140300101d40a003122198007042e14943d00b020020718946441c01c04400109005c1c10111010310040700074201a50750705108003100c4a034013201c180505201218010001c200480302c43d9103070002101c4a0140c2103440e1660846 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 848988363 1250 848987113 848987129
    0x151002071e0b070b090d02030c03040504180c0314012a0e2115151f0c081612020109020a1404091202010b01080708101725060905030304 60
    0x81414001e1024400411018450540c0209080026091a00d0000303182c07080c09058081c007281000c81c407860808400382d100c441158000d20824403280008000c071004c40320125000141c007204100040c6820608004c00f07000d4006408000080c0b003850805912070107100c20003001100c500d0843d80324998840f80740c0c22024840d0b5101000601d0040380c405c41416001400e19454000c810032101c0360006a0542d600035822042c4100010002c0054154004954140d600311007000e10020440c1d01d9007610981090800d10744004c03c6950044c215290f00b07a4119425664030050300303c8000f000422400100e400c0103c00e0350040e0070764410312074503501ea580206860060392074806c00e00406541c01000981c815601d034160cc000400411880700005525000401d00025400025040c0c0a00420036400d11450000304884d590700d200a08050b600503568020402e0301d0131500341c2c60410510b55806903c880340c2c855500c1520120350b85070468009644441c801074407641807540300c1c01988100c803a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 848989613 1250 848988363 848988373
    0x7050111031314060c0a08041409010302060a0309170403060b090901020705070536062b080d061517010b040602060606070303092405010605162303070506151002 71
    0x2201c66403c42003008800401441c060401c1180d12880e400c01d6203c1d01e00300d0300e00b07a00150410002000e0404c0762800c000494800c10158503580202e013151240101d5801010354503c041801c1251025049020741d8023070103443c0d21603449103402401007101c13081c01d030700c55004200018076219050013107895003980a4007402e00e0500e4042400842050b51050a540c17200460103001b06000c0300c0e200b111140000502c051281c00c0020074020903d14800c0000c03030103240c3d014007500311480c0c0d0740142507841d40042c0c1241d441481c114090020955500712146022030400c140c920305900640400c0e140020b480400c0090342c0c7d40361281d0301c921451182c4e8000da0001c1d0300141a52a1210241203081e002c0e007004200604140e41e000f5031240320840418aa5120000444d007141061203070602400c80d6080c020f04d000e00c10080b0b0010712542c1c110040008121b0032492058549072041e00002d001c415007103944840c0e4a15020780c640604850005100e089030114090624005030024003e045a402401d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 848990863 1250 848989613 848989619
    0x181a090c090c0a111c02011a010f081504090804090506130b01021e0a0c1212051c0e01061802090f030d080103080a18030f0b06040b01051b190302070501110313 70
    0x65684a42c101e68613019000b850000603190840c40c6059a82c40304c541d0000807890403110070902200403100f6064108015070642d01c0e4010342044000f60044200382503046003401110000b40640300c404401003800c00080307400201001c01f03400460007010211000580303003118114040031500d5042c1d6060050307125040c00400e116003140700307200d40c1e0700034030035640c009486480302000303c2c4c59035002d5100381440740810741c1070101a21408107010f400c0d00d0028035280d01d41c06111050903044019120f070a544040c1401166401d6000301c008003110301680d0001185903203081c000f50407618005018840901c4156054034010481c21901401612802c04070390940e00c82170066042664000103000c00c0400c0c03403284110700605400150301c180681150500b079031404100041e00900b000f4055418030790078000680c0c000c0103840f14140c45001c3d1140c28914015000d00d00040b00c2c807804c200403e071080e10410b165000c1500342c1503610a03201c050801b00030302c1030f482d620310540400d807568103c0310200b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 848992113 1250 848990863 848990867
    0x2030307140c1203162a030e060a020a030224010509060f0301091115120a1d1c0306081f0e0705130b090105090f0703020721080703050106021f181a090c090c0a 70
    0x46e00c2806458400a0706a520b408600305501107410f100c0540e001141c1e200400d80d040140618200101021049905001d291003403100c206014103840740c8019400560b02c0d448030070102114510042c000d1001d10070a040c00c0c212110144c0c01c1a000c0c1800007403640b0100e004d02c04542c94000600c1e42c0d40c1e516a82c840d0030a00500da0505034001029400c1c41c62191780c1010007a440031601c1c2c85040b44c0341c1090088028007100c80a0740004515042002c00451032071464400340b031110030301c00010851030b24044600c0d0034260a9000142e01c40c01b56010004142c500342d00c08070242c481558451740a988440800031114401c584450b2184400c40014501c1803217500500912032241e0520104003582e9070592050300801c84400c0001420310041005056150040b540180f0aa0015001081c100b046200e0003050060350b41c40240c0c3c403142d480080380c914001c01c4149507040b41d007241062441620340741e035071502950204c2c05485144a200e07414500343d500c00d4025504c6002c264a844912001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 848993363 1250 848992113 848992187
    0x70e06090c0f040803040806060109031e0203031c05150906090a0e01020405060c010207151b1103040b0310030b0105091302040e07030237030302030307140c120316 72
    0x11880a078200340100b030301c10009031000e040902800b2000d16150760412401914000000302014104501c04c0c0303003040032408501792842e0b50303d22514001c900403a01d0001c00e26512801e5070020045840c500858900440c40d4017850050343c47e00f51160b2005245010084e44000c1640e4140e4010884400f050786990150f21a00064489100160800e5a6000003802c4da4000d42c9100302c099400144060400a0003141c0084280140d08104280c03071098210f241d0510b195030401042c0907441c0000d1001003810010358004011003118640d9030303c2c01034442c26082c0070344c1c84100c800c070072640300109261802c040b0031031190003c04007015030082180c0030072002e0318001010b015170703000f42c2d000070000d6100c44440c04c01e092103118407200e090184101d00340c4203049580002084800f600c1081c40001d50100c21a900a1014074160480031000c102040e064890761061754141d00c201d130f15400d49034030303070901941c40ba045e68500d01b102548030440071340f10030780d00107139844041802c241c50303080794404014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 848994613 1250 848993363 848993371
    0x12050f030a08190e060f0703181e0f171b1f0f0219031a06030c090105210103030804140a030210020c1609020405040b10090608040206072909070e0609 66
    0x107400305403407100044130380c2081c2083e00c040900200308410403043e9a01805480041c0c3c181803511032943c2c1c4a074030b1fa0b20101e181c902c41004100003001c80041800900440301d0842c94004120040e200240d0780e4403402c5504c444081f401030b03214602d000c80700c0c080c04501c10403405000540710a09040400c18800101964450101455428008440e82c500180380040c84d409141c0c800142c00502001454082d44080e20383c0c510a4100308100a040c1010078299124000e0a0900c02d0b00d0304400901e00a44c02944451207200b00803040000013459801301040b4011401400d04410050b02c42c4e20150311040700b140040e01583c80f4426840341c2c80910b9004041d1100b0001c25076a4455094425072040d104c40da20000305140c012505105a1609104003042020304951003651001d06c103c000c3c088921500c1b0300010f0005030740c0000c0135901e485044582c0950300c541e03070141a01d0300c10a40d0002401c80040002c5101d035800000c0c034080e83c00908902601c0d0040d0503082c842d0b444008014103644028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 848995863 1250 848994613 848994661
    0x1009051203242101050601021006060215060d140604060b010e010e100e0604031103010b03160b030c0d020f0703020c090613020f0405120706120501030c1205150112050f030a08 77
    0x101c03403d03400440c4141414003400400403800d420003100080c54028020b1100840328a408000c228207078000840c6801d0849007071040d040303030755002c0c0002c41c2c4c40c00700000942501c00c803449012180c4004a1910300c100e10501c001c2111700c2c0300344011242030804108030744c00b003001419440443d03e0311040f0b080340e8541600d080096070390b00c4804140a50001c0e1300c1180ca0a207940408150f5150a0040244001c029401400d800d090041034482000b0035104100d18420000085415412900111000c2d5218580159566805107220040d1540954010340050040115003d0700c0c0c5400c00030031b03005100042070b002d00c03142c070248030500a5000003601c26405c10104000030b241e4803600c82c03c0b41681c0600c2c0246c0400f07803074030710050101c0f110b07000340d14041c038603040c018000240c1d40d260410644044d41c5820b144c065980c0351507480c10340c000c00d0f000b1681004100004404000312000d9800d284110152603011a6410741d10356640184503600000c1402c02002891325454102040d203503503810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 848997113 1250 848995863 848995879
    0x31a15130b15070501060e060f1002030d0603030809010f201303020a0609030510090201020312090c130b1201021204031815050a0e180105040c030905100905120324 72
    0x140c002981c00c1c0008a1809040c00b000c200c810501500f072240340010304c5058030981c800e04c2c0c10400540c0f545003551000e071007581003e0002c51213905c00c000f42c40811121404c00c003e600d4403401e0281010310304591401d80340d0700340f40944140c2065805070311900110b56040c5860102c115206810582041d807440c00c0d10042c0040000142e07480030b810300010700300b0380c68035040f050031810f020f07040901d1411003542c0c82d810104c4840060740c1c00001c59002c05004d00044502d40c0301c0c85c508904140307001c00384a60203524181002099a803940c820402c240084980009903c4007002c031718280d001e15500014441010400030303012900402038140410692002d1541403501c510f00221503150a00c200c03c00a100421003c104942202c000d0044101c01c48070710781ca00000200400090105002d200d00458840d01100042c034040d804c04500d09034070105603a205244420761070300401c1005000c4d030303441c82600c800d00c40748103a5100b180e0045203407100e0540c960900208401c034410388001c44035046182 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 848998363 1250 848997113 848997131
    0x603022b09170705060108120a0807090504090302010e07210212010b120c010206010501051912020408030c150106051c0504021504090b1302040b0a0305090f0d050301031a1513 77
    0x307498182d216080e521084151104070b02d007070085c50300c40144c00050140d446203030016103040c8001c0940c0c403940740324a1f201601c1d5989690440c0d01ba92545e00c55500181040344400130550190800300801c0c296038100d0707081075038400414443d642000042c0b11504070000c0da0300090305201d895940000009000860120340d150085280c00091808a0140345c20000802c0550b41e41482207078010702c02403070003606003100340442c0440034640c5000401881203100c44650081c03541c1d0152002072a101c0103580d01d50307070100041307034403400000360166401055a00108143d8061001d88940c0406186d443c1042c0a19001400c0103003405001680d200c2c0e1b400000b0440d0303c40000040014008840000c81c0300d040040500c9a0800086420508140148800c0c081c4415000a86603100501d02d004280b94642e40307801420600c11030001d44903401001404c940303654002000b5030407a4860a02002086003945c41040522415280d40261014440c0400744e03030300d8170008042ca04804d00c44005540c840d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 848999613 1250 848998363 848998373
    0x1050702032e0b102106080f01021e071106030a2009040b0f1320070602131401020d0c080909010303120f090b060121021201030c0603022b09 62
    0x8000c010111a1524001c0c1c03400002c80c2402503800341c1c9403d071400e069030444244003800d0341c03c1c014003229030303006108007854811009400c5034000f0300542083c3c50064601441040c080c1d88180f0481c442070141e1a40d110485460104880c1c5558004030494556480e0380e080000340c2d4800740c07041d1803803502d0303c0300d1480700b924a21225005c004201e5240f580d6080079418401a01e40004043c6d108004d080c640710401d8541450450105410440000b040400d000340c64a1044a841c0c0500d0250b4001c40c6030000c120050780101030401c44131001c0e400d5180d8a14070080250b40210210f030068000901565400f40070740e04403031585224141c030030f0a1100e4840400e048910036801600014409002c0c124140310520800380343d001c00030010311580301607072505104180f015000c941000041501c1c1090440c90056205494072580d9003599500b24001848000010a02042e544048008000075440c0c0c040e20803100403080c2090401000325406800d185184113441c940b0301c0380703922070326000c0000d9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 849000863 1250 848999613 848999653
    0x812041a070e0108070c11090702030708030a0e01060803040b120c04031e17040e0402060a11060709141206060103050411100309060b15070803091e03120a05010b090105070203 77
    0x281c0581d25510403440e0700c800100102c902811000612074403030310340f1002c181d00905280041030b06071103099040d141c0490491852040d818094018034001c424462903400b213800040c40540300d440280a41c03078440d00142d031030384610b100da50b148110400040e003400451014080e84191510012400c080d41c0e0340700d07485040c020600c0860004440310001c41006400c2e5a5007585010f80f82000381002c1c1029680c203194a406080684500030214021900c0c9124a89611700403001c0c0c805d452150600810182001101d401102e0200032418247c5e405403c24042c0140140c060000900040d1102d100540081c2000381041c0c95583d018898207a4a4a58844a001c0d25a00303035400684a0300d1820300b03804813145103107068803542e00e000803034186508036015180d20035041444240e03640c9800c03c620345040400303000c0102240043c140403a12000c044080c1200e14209203c1040701c1d5244031031401281c030240202c1807944014080b44040b9407080014140d40d40c80902250001c0c4500c1c29510780d15 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 849002113 1250 849000863 849000871
    0x11070210361a0319051003030c1b080303070e0913030e0f100e0301060503010e0307120c06090309030212060106020601210b010906080d0809030d020d09020916020c0306040812041a 79
    0x180000000e01001c0300d0490201c0200d00c111383d4042083d0305100d0398011b01e8258a04c030107820020b0703081c615402d003e01c011188a09175085910704040c540d40b1850103450b07800459040b80400c40043c1200400d0400803102881400d0901ca0340146144941d01035039a01c0b00500610b0300715000e000c84041540380c00100b0707042148940c4032041200c0c0700204050948046421040c0aa414200701740204800041950203c5174400303030034045a00008012140140340a001400c10350a03c0584002e05030030030440c0090ba4003e8451020f500b824041c050354643c82032190000690010004000d01c184950f040ac540b000380d070548a40c02c4006840320020408281c004040240e42d03007004100b0700300200158960000c00e424022040d00c1e0210f00b641c1c0f01d004a801d60003210303030000740a20f140d40450b03201ea43c3c8280d0081050046041802c0d02d01a0030010425080243c4120007800203145000106127200b030360310140c00b525085a031402842c0503c40503204452440b1042a00600000001d0f80740d449 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 849003363 1250 849002113 849002159
    0xe1c0609110f03070f03121206030309030b011e060f0e1908060108161e05130903030608010b0603010b07030302090904031e110c0d03050408011107021036 68
    0x1048103420400c80742c006a603180c02c0c03090707105810400c26040c000d505102281e400403280c500c90b010300303c01507680b44004020084054540780c0080201178200d080301e010350780254054105aa00c580e0b00003125085800c2c14545080008000c00c07003d0f2045524552001440c03402600c2c1015a102041703c0d4218007840d081c2f03a00b03001905000c0814100201401000804000d144070044451103014140b454010600d000b4044e15150802c00224450704c00201f40140900380709041e9011901c005004200040340040c0c1004d20008a03002c05000740d503103594005081130300d964600b020443c881c0d40070140031020f141d024002d500582c2d441200282c4514001d03100c4881d441009240d1120388200340c03045030700740905000c01c0000c0c21400181044a40b2054619100a0800e820180c8041c06103a01640c020360920103248400d600b001d0107091000d00c241d07503d5a0811403d4002e507224184488030008140750881e090050070300e0102c40307000340c0c80564584070074180c4504240204443c2040c580d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 849004613 1250 849003363 849003383
    0x204061d0901050601050306061905090d05011b050a0e01031a0307081015030b150103270c050913020d0c05040921030c02070b0c010212090d020d0c02010e1c0609 71
    0x7503004820f000c0c86502c80002d18189195280c14400607015024150059002510300303021808614012001c50f00c0d070b0780b07004009464181e034901d0040d0180481c5600d150585288810100299000303806840e803091103601d504165115075001100142024440c2c900e000c2e416403035918880c3c80602c55040540304400140c09000440c014181c2620b402c0465400c50159040f03040001c1803011521a40105200c0c40c5a2040d12260004801400300d0315100003100c9070311181c580380c1c942e9000801d4a058450710000c1041550380b0208513030614211620f0014890410202005140c2030b49007030200c1d8458200900426295400701d4122460b40b0421201c0784003800a641d204007103583d1a01d0101d815150900a80440f10b0001b5110355991180c911803200102c1c000340c8290702901560070746021015000000d240030504141c2e1000300d550b488025001f1080c10000c131511882516101d0740d01030b1925414540e10301c00b4425055400e8103004034200c081841000082c5582c010104480d002d407803558 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 849005863 1250 849004613 849004621
    0xc0513031407230105070204090b0a15060203041809080d060602060417090f37030201170f01060f05040305030a1701090e060c0307020a0b010f03030206131e0204061d 73
    0x191400100ea00b09400c0310810f80890305000c41d40f0300c041e0903503e9083c80d00e00d8a418151002c1409014415001440e054100007040030318001903100032140d080c0701c0344403c442a91a0740680c0c0708d01c220b000c1c004040d03403c0b44142009000c1c40d046071800c944901350203440c2c2290300555500301c5000c0e4004a0058120005100900803207600300c900443c900c0c4041403800c0705400008400040402e03000303004020500c1c149110b00d406005410b03204c0c01114645404050152807880c0500e01804101e000c50b001c0940c82955006944006201d2030b00c11444080d640d09040d02562a09030240311081041004c00c00480004c0090001e410500b0b0305841d401d038a1000d24000442961050f005401c00600d014904602c00d800050b0007a044070f00e02c000b45589854008041303081521404015108424541c000201a0301d00600302088030300030303820b035545a01c41541e51542c85018100140c14020318500c000d441440c54100903c025100603c00155540d51355404a140640d2980d20415103032000108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 849007113 1250 849005863 849005903
    0x90d11043215060409051512030304170c0106091409012009060f0c030702040f02031306180b04120809060717072003070605060a06080c0708041a0306010315050604090c051303 77
    0x48030141101b1a41d065013007208c507070703c01c0d43c90200510281c40034821080040b9440c0c0c211044480d0412250000c0c84090b80760340029010300600b0f03282e6640040340c1c00000b002410184940560b40c0040c180071504040b070003140d0600f0740c00116170300d54480410800046048010390084c1940c081c0c840145445609500410040b11000081c250030b460040013003110411403400c00c21041980243c0010b400000c00440500d920a100d40c018101d03618a000c0c0814040d020f0740c1d1603000c8406584040d4250750300704c0c1841c1c03100c00075904a00411b1100442d0b0341415010003855501000c02d18011a00107100e107481140542d821070420b4440d0800140754007885858041c1030b40c440001d4500001207440e1040080c000c0070002c21968100a01080307980c00c200364001150002c202c05494911151050b0046102540c001d9a071140072a00e400090b0203030540700950b05080b00c0d0000d041c1070429207004502c0c0050a1500d010304d0420104100a400d40408102c944015501502801d2502c0643d4040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 849008363 1250 849007113 849007141
    0xa1b0c11030a240209030a06090c0b13030f030e0a030c060f0513050f12121c0c08040b0604060f1d0c03220206090d1104321506040905 59
    0x441c000d400082e4990003083d0412416010411804080c100390304500c1c03501d00090160400b550341c0b500510180c40207110b03c0b40c00c82d0064034000e14030040075a90745c841c0c40001e4880d180d41c180384003e10042c10004601c040c64407a403024060300308080550446c000044001350603030402c40d031b88604000c052140383d40c0444546480103070b41c105a031504461203000740e143c0c1d0b0b2920070284580300d20182c0d0201900c0303801c0000300c1240d41008465118010404400d2982c011604a00303c1c100d0061068101450302c6c00f8880b86503c20f52180d42441e1140c3d00c4650740d254006004a80250b22141c000811143c4100180010300c1c0255201e9203250503011500c069403800340142040c0345082c400d102800040d05458140d407084440b0302580b12a60348040780d0a4042c88001e50b5200201c1c1c40404103221134a061119800801c50301005402d810a548080d0006080c41c0c6504804404424640300000384681030741114aa000c0c07140882d40040004816502982146c003181c0d44880510240d00f100c028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 849009613 1250 849008363 849008393
    0x4170a0f020f151605130e011a04120209040501060b0d020d0606090e16031b0203120a06290f0307120b0105070b0408030a0e010c03060509011406040e0a1b0c 69
    0x2a010190ba407507540240c40d03a016020f4101c0340144c2c520b41203500c1c080c808554400d00d80301c1c4c000098541c0c500040304000000d101c1d204560701c004590246040a1034116001d4441c110389000e04105a078080c401c100c60001c0c0101c50b50365803090301180ca41410030241a140c0308114003d49d842c405160303500190782e04d55200606014200e02c040c8000c0509e950503d5011138040c011402e80005144110007a00000e14000d8421000030018816540d000c4000e0905a48040604079aa1640c240340012900c45e4860000c0214159880d21f8442e0855003180e26100701d2844161f05107408040e186840358829035031207000c030321520407640700d4410705d0040c40302c64402420b01c141451000c1d1a110103450b80288000c0c2a004008002800940e080d4001e102401c904802003140d0412000060010021030003104e1056107001c0000030403004901c801415100c1c05003c3c181002d2400c96001c8001c81d002d860050740a4a440c00c80c0b111140400089003120341c10383c1d0b2134580400360b090500200001070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 849010863 1250 849009613 849009643
    0xe1e180f0402060708120c03091e1002090111070b0301150201110f031e010f180915050603030706050c03101d061c060501080f071d010e04170a0f02 65
    0x10842100422803009900c0340c0c041c2c91080d5226600c0c54241d072203225554000d40c90180810602480c4001e4202440c4144815811501c00c03690200c99030303c8408804628000c107602000460384a80079903006040c40d10740c1070500b0f0110041051380c45040c042c4680140f40c00e01c40c08401000100003d084007010714255000820010b0314580600c0d1040c8151041000c5002c00000030503000b0400f054002c8803802c85507400030340d6507100d01018140c500c5a01c1049085040035029030b100880c548200842d0907882010002400c4001a00c1809080002e000700d40c54001803000c2804600180a060b100f040c00c0540380e6964542a090b47e074418641c0d400002c00c0602030001140005110341c0c0407600007100300d07201b03151030001c040c55420f80c2030360120017444103003080000506c4140000300100d54440402c00c1d100165110030b00040e00411145a1340701c030858000042040e02c1d00055100d410901807480c485641c0d40140c0134489540c02101240005107203998040c0301d1a03030510140c80449491 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 849012113 1250 849010863 849010909
    0x304082d0d08061c0303052409060d0303061e03020103060b09011d0310020a0909050916141c080901020601050f0a0b0d0209030a2d0b0a0203070e1e 65
    0x84030109940e44072100d04001071000301c9000c0388481d55069031039180c00c0016003020104d0034075840c0080c05400240c42601000700c014801c0b940c4407207070080c1e4000e598005041c3c13a4481e03644000f000120304001070103809040e41d4960100d07114141540d89503520030b010343c0d02d04c1000d1a40c0300060441e102640606489042400164000d17a4084500c20501185401d480e551000510009081c45024699146000d2000171140000f07a040100d80c41103a020a40403c82a5200414151100003600250003201800b94050244045412600b400030101811000340782c04424140035505000700d000707486054001c101d805d56503030304101080c05082d0985512440c04000b00c082141e5000320300817051a22404550a0110341d441d50603608003030001030031114168503e00702001054224403030401c460384a00d1403030504103800800c4500e40c961080c03180e0350035902e49550900039040585541c0402c0012085c0040c160380b1800c60801810480c10340c04102500d01041201c00805827044403089254 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 849013363 1250 849012113 849012193
    0x20303100308180616021c050309091302180a0506040b0102030a1b06020d0b01080c27130c11010e0f03070b130605040c140102010b030a12030608030408 67
    0x1200d4400c1166884010291100c03a05420f20b400180c2c0094801e0f00103902050903000303400e1103101940070b94000c1d0f410300081e907111007a0420741d41d00310802030481da00800100780715091032030f413081d8410140b041c0e0340211400f90b40042c051040680c44c610300000840e00b03105a0b1502c0b842100d4000e00200e604000d1f000c0d202c80041c1d220300a00664a060080070005140000101c1900c2c6101d50340c050700c01c40d81d030760002100c0e100421002c1c6407280090048030020300c0140100701150f4440341182da00644044e410002042c0014541050a82203413440108041102c0030380580210903009031034511848120313528403800c540510006410342d038807140d408a15540d000c012200c055402160400300d90b60b07028082161414002c2c0e004181034541420042030040240132a815a42a00070450301035032502c004a09940d010086a03901d500a00340100024040d20fa030080e014403c0e0801003030a81e550210141580c0050384080565040340d0061380103d562880c0c4480006004451180d40503c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 849014613 1250 849013363 849013381
    0x90703090f082505100c0f0e0402130e1305160513050c042c010f050907030e0f19120f0212220305010b01080901022b090f0b070f020303 60
    0x820690081c02c1502d00041200c032482200c0c050300300080005240285140480c544641e0352020b090300e002100d8a0125001501c0d40304001c51040401c0e03540c0d40c01d01c5640501c00700402540b00c5003640d074020614090000d10616118103140c031560000500c0400c009041c10580d0400909041b4242c0384150390f6014081a0b07600b4840400c40c00d0014000241c5584101e0302403810b10954000352120079441c0c0c21020102511580142c0d403103041c01401c049640c3e1020240b60240d02030041c03a40c00421070300082c480c01c0c403c0c0d0102240750b6510303003100c04a01c40312034114189000d00c61b01c64407035912168140c0501000d42c224418945051400700054000184025115001d07050508048400002d0010f0b00c590004800c030b640c0c240e5503141d8142c040d601c0c81c1540c0288815299a4040350200340001c040c0b100600c00c1c0c031100304c489910b4130710504198821250740000c2012100c1203a40d20300d10340d000b00e810311034802007451281c41c0141203420800f034007600340c41904103844c00b158400c00801c10340b24 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 849015863 1250 849014613 849014633
    0x50408031f051e040e0a08040303090f05010f0e01031d0705010206013309091d0d110c010c0206040b030705041e030c06210c020c0f0405011406071b060c0209070309 72
    0x6000c0075050f1124030f00c18800103002c3e1109606000d05441003404140c140085903006108881c8070340c4600602c607030f60384d2134100414510320031680880c2c0001740b042c0b01d05001c2c0601d086c04040500d0300058680400700a004070076038030442e01400703a10010092025580411000340036201590a1101c8014440080342d000b1b080074080c40005804400d42412990151042201070403401d007060204001c20031020300c001441503c00aa14418007140c0f010013030050b000b0403680c1501c80050890404c2e48001514000e095030030072a0000c1c01004001410800100a58050340300340d80e0b02503076030f031420006035280000b0980c9040900c206503000c20000e01100380500450b0038a0070304117500b0300718105402210703004840182007282000080c50f400380e40451840c84841040b500556107000000900c81250424040d480c440e02d94a050301307581d0725001e800b51219601c242c000b044d103400454400322010341240e00c50008200390000180c21403800041441d03000b000d0b031500301b042075100c1d03c84002034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 849017113 1250 849015863 849015889
    0x220c08040b0c090112020a0804030806011704060b06130e0907050a08070e0a0f1401050a08070303020c040f060f091a0913060905010f1121061e0a0306050408031f05 72
    0x78840000f1208040c1c0d0140c200300490203204201151610407015015003914401c0700c048000410348800a4240d40c01a00501c503400d00040c1041e080e55920395400d0020a0010282139101e0800e000c0c0641140f1107400002c0a441e031009041182e080c0b090840c6c5c03901c117858001030303c2800c030324000784000c0b000055a081114254008030029868940e0310030014103402c0c40510b5134034102610803e941341c00501c0f16040f00d00641e0303401c07051680e4008064031144140002801a0443c030040d0070249040d401102c0c0d1000f2101c00000d40c40d6030303400310727141c90b10040d8060300300c00e41c54803408142071015180e65003c00e802a2130b0b105040c13600c010504c10040f80c001000b4495683d9500781001d01c81d00b503010408103030880c1e504000100e0103604405440d00444002c01001079a07031140d01802d141006843c1c01284041c0440d00005102d1076142c000000d4003100a4103c000c454001020900e5801442c3c060303805121805d54908011380b003400249100c50510180e0360a0602c100081d0312103500845413 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 849018363 1250 849017113 849017131
    0x1002090d031407170a0e030d0914030c0a080d02010513020a0905040614010b2503200a050d0905190305030301060e0d050102032508040b060409050c220c08040b 70
    0x106030720040b5100a0296040241071081000045411945590010300d40310350300c0d0301c50740c00c22489542056950031a8850040000345101c1e020400103840000360503080d5001015510b625814001140200520742d21110380e55204088105066030288284c513040100c0003030703400407440c0396004070b4600e080320f101d54000c8555400015043c01440d030311102c482c41e146400c018840d6911081002e054204400c8114151200702d8400e00288008060b01a9103925403120f8502c070008240c02d4070041d030103580d610f68a000f03401102d00040c00900440f408000c05444810308e03c0e08000c18420560403410602d003200074012414000308600100745d034115540e0b8a0048a940e800390017146000c00c0210008010f07600201c240454481464020741120410062401100000382c004039400c510270b5401801004800000c25801d003041d40151500a00500c110380007040c400340403a046054180b40580400c110520300450800c05004102817280c3c01e1138140c02500b0301c0d0725000d103603080c06080940 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 849019613 1250 849018363 849018377
    0x302060304170d090c05130b0a050d0f050a06060617190b010306081005180a2f031603020102060903090307050f1203040909060c05070b190e030403080403051002090d03 74
    0x30741c4540c41c02c1241d0b04600c054109101040e100c2c80d00360b07040b10300c40c0150391040c1500b41940d441c840c140c0c0728184525100a00b0055164070b040e06014060518010a403200940740e000368021440c00c000c1d41071414440c9000160361b502d0024000c1030032030308402c803281c802d0800040c4850004041540c48000f440080001350321100500140d0080a103544030903414011901c000406040070b901031849401d81c1e020b0f160104860050981c0c03160401035005280c16400e0504000c1d503800301840031100c841510b0700110002a05c4002864282c0e20900e0011480c01d10409104550381840343d81d803c83c1c0000000d60400c0800c00000b81c4400b124001d0502803441210003090383e9a50701c0880f0b0400c10544241c81e80c90303440d55894000340040f100291403036410300041341941c600c144c0443d0100783e08842004c4aa484480e6250174104c0d15007054801c050f1200c02000220f6028401040118071922003240e0707980c0395141c11810080005224626640b05006400c1c083e1142c001141c600c50f8946010301c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 849020863 1250 849019613 849019643
    0x1012030c0b060616062705030301030305130f080c1305010f0324050108100b0a05010504170a0b1608010e0c030412050409050a0204031412090f03010b120607090b040302060304 77
    0x40d5540c00788410b2002c00b803106a1444c0140a59640240e15825522602007110300c10305042844110b4803000080565004000400203c2c0c4203001030900c0000d04407140ca1030383ea0b100300710740803a0056040350040380c2004132400414078019404a0b00c600801f0402e0099602d4820000c00a41540c84080e10710b03c1c14140d5030910aa1a1603105001c42201c1420441c1d1350315859001d0341d8101c0079082d60b23581031600c9019215444c14403098800c40f04165242d518150808004400e152411403031160944246c0c0003640c0000c582c05400b61180140030101c076a840350550005040c08410303800801d0f454240002c0c07101c4012a0412071750321640181c80c000e280c0d503207420f04452074407480c2d2015211501d8007050042d44001e940040003200d004801c1c1d4903143c40c1c0621011b498421015101800ca0010004400039040c07010005c142140000d00000e141ca07201c2005c28414040b1800800c280c0d0040d4080006160b00f006009029014900c2900e0429083d41d01040d01c0344400342000d007002519600f50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 849022113 1250 849020863 849020869
    0x220f090c110f01090c24030c230901180b0a0e03070f03050c1806030c0126040807170a08041e08071a06030a05100c0203040e0903031012030c0b06 64
    0x400748611032441201d4103200400d5180b40206440c000441c2c100c28000c4000410481c94401c0110440101c51064480b80c0011400e90040298040307490901c0300341708070030502c0d03010360100c5d10540c58a410314036921070b000e800051101000300c0c440300000c001214284001c26a60701500d02c4400a030402302d19804000c4000b91424030181c0c8462113103219040084108000070464000200c0d0503111004104c08801400442d09001c5480d41c9d0035a110032032122403584682c80d1801c50070311082116020070503d42c1d0281c9107060480703094a54010000d0307141c08118840782040b002d07414405045050908400d001030101c903000c0d002810711003443e051450340700b41162600b42c0c1c255001c001a980d401c014908074000400c001c070000409158440011103504010034000415540f10000e0458450109207503c010401080c0010071840184004610f42d255521800e00884201004585030b01e0601c0c106800d0b07620307541104508d980507038041ba00107908006080c10311507000101c1c418a503103107004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 849023363 1250 849022113 849022127
    0x314180a06020312070815010e0402040801020a0804050d0e130b0f0a031b09110a030e010b030d02071a0a0815040b060d060f1418070207120602220f090c 67
    0x118550040001800040c040d40000040c44401c407601e591001d69550980d050303a103441e08031014220080c0040340c0d5811984920f070002e0f00440001c0c001030030a03484980f0a070890302b000180b00d0118810000740810b01c60300b04107001784503403980f03001c50005801e4030214850400c6030020201c0c50352034114030500303541d4070300162020940280c808503e5658130304010055500420680c21000c807010b0012801140d58001c0f0002a119041e8480c0741990b180b00131001800d50000c84c0310503542c0d0382a00d01c45c07175805001c2e030101200030758020302c0058140b0b1704c0f41d41c40e03a401145000c1321542c10820503201d0b03600400105d900c001031055602c01074110300040b0b80500307404c862882d4420000216a44c0a41c00e0b944040155446100d29180c1035440e8a0074003524280c40280544c0140440c84c03403104e1196001d4816402010741c0b06942c08242c3c2e90103594080048100100c0c1c0c00b80d0045403007480010f441801c15018400c10094190203407a240d00040b844e00d03140034021082e9202c001515145010f40b407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 849024613 1250 849023363 849023407
    0x111c06030605040c0e0a15060e040f050106111204080c130e01060321020f060406020a1407120e0f280302060c03030106030c1707080712050f06100c0314 67
    0x1e4140020310b01450130000303000050141100c0341e0741c1040440e131400194441c0c400c0c50b103060842007900c2c500f842e4040d40c1c981d5103d0941c41e445610b88000c4107503a801c0340502402090a6242c15032100fa4480c80581040c0803408003d6407007805000070020700c400040c140850440c2540c055850005810005001e4248010340e0100d17982807010010400c0449070f904501d0b0150001085054004d00354100c1c1c440c4500d000596031030b0b00003008207010600940c014984901d403803d00b5806001034a036a0322030f81d0132182056600e038807141003402c1007941001c81580300e000100e440e84a07503100500007d0440f8400c2e15455523040040308442900070241961a002c0d540041c04140c42d80400004a503480e4000d01400001030305010421409500443c4030711003116014101c07407400d9640780822110070800030032000802c407501000c10321000903403240794000e442e6002e50301c15600d032030001e02400b00400c00d40501002007059110000c0b95100c45924051030041c2d45403a6502c91a111442d4800c0c0460 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 849025863 1250 849024613 849024623
    0x60c05550e030c0108040b090a0b072a021807050c0703051c090609090207031b0311010c0e131503080c030c0601061d040c0c08031602060a111c0603 65
    0x4441400003103800490200d2031034565942a00741d2019024076884a141010960110b407101021800280200544035032000e429803c031603612046440c1ca00340c5107025101c210200d403142070224482549081c3c0b8404000c0b080188083c010b4080d404540c03802030803080b0401c1d050900c130128101c280b040c0c0480d00e620745004101d504058907170070040c0d00d51301d0940d00281d00d9010f200703082c2942c90084a00304200c4140da00d45d00d2406103020301c42d401a41c0100c504908100c0340110a0b5074016041c15048401e45c0240c0e907440a021040030380d44d013120b0030241070700b0a1000c0c0010f540c034640d135441c4180608091188010513440e00402c685200751f14250401444000d01203081310014100102502d00d1800507011160b02d03036615001034902909501c0b07104001d00174044001c401313062036000740c0052007451074a01c1d6907491a45038046543c02c281d80000035060161001005154100b01c055008400014100104078000254405600c20548940007590000c01405000f11455100c81c00454000e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 849027113 1250 849025863 849025987
    0x6041104020d1515030f0506030303070c0302030c101a0a03020634050d09090209060a08070c06150f0902090d0f050a0f0b011502030712080a1e0504060c05 68
    0x4d000b128100d80603a40e6400c002403a0109140c0540c441d40240d07070043e40050041c51031501c4411080b510403090308070a409501c0100301c1608035900800c003035003401d040740034000341c6100c2c8500e20580c802c1c00315003224401d15402e04140056601c8030110b804810b014094599211107a410039000d0001d081810404416a80380d07510500a006c91821301015507562100c09007500c44404c07008a0060145132900000c050058041242c0540081500030911f42004002410036503035003800e0b038450440c19015a000400c042003c9000103104201030320b1118415400c1c0903500c0702064840080001c050450030032002c405050150512031015662781051005001080300e08140074482820700c15104a5007503144d00801c803506c0802602e0241380d0210100d03490804001c1e0440c1c1e0b8a001402c4596441d40e6000106440e402110005200a02d80075020840d45031506000e01100d80b01e105820510008000c40c0c101d210308410f503e50300c411071041100c000041d0403141c810300340401c80d81d03500710110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 849028363 1250 849027113 849027119
    0x1b0c010b0f03070308030c070c08061e071416030504080609012f0a0e01030b03010c1101060909050a080d140103033209040e01380306041104020d15 65
    0x419041640180d0040d20240d0203210100e0a00d6a600d01c0792101034880c00c0b060000c22010181d45006080003406060000f07240e0380c44c0d0301504e00b011015a4114504081a040d5001501003070f41103d610101a0600d0f481c081c203100e080c0c8049210b08c1c0201000c081a101060b030826002e5002c0e94003524442d42110401d107884a2040e001700406041c98021104c0303049400c52804461020318545c001b00341907641004003950b03064400c1840c2d41e40c0c850505849440c0c0070740d603490901c6002c51504c025910303841044581001c81c0e003114410b8002d0256075080513082001f003400010003009266005180544e9010b003019a000141220070f01c040702140c501c0000400e0640c040c4680c101c0d2014004400b9150300340802c10038a080d51013205600f440d50070301101103207203410340c80605402c50315000801c40c0000c03c29980380c40d00b1416400e80780c10800f400315015503480004d0031001017134107900900960601d5200d00861080c1114100d100302d40024035550400c18035044281c404480c0c4002114030740e2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 849029613 1250 849028363 849028387
    0x1403071a120414120f0901031d0f03070605061c0201050f070c0e042013090f080a0305070801171c0c0609030e030f0712020607082511120705091b 64
    0x40d1060f4600e131054000c8159401840e07400c981c003048140c0009813801d4007410055010309004419004450490354482112140620980f08040d0f50840916500c60152400e001100d40c080c1086004000342501c060003a07a0452100c00b80ca602401d01a07255601084200c4e10703032255660060981040d8030b000203050403444e9465010f144100044000d408156a801802c4404d4400b01c0d07601800602c003811040a070340e40003503101030294800e01d1241003107071100340159000f40302c4040021790703400401005070f47c004100341c007510000300240d64140b40c1700f05003540c4440d141d2281c56461000c40c2d081d12003d01912941d8046a84480c06211440e010f00b400340002910311182ea010380900115914680b0740400c0c1c0c0015540700f0f0258000d421841c0e028014290406901100c607003c1c100070345c0200b046210b1607031100300440c3d180c10030040b030b085c41c052403044003841f401c0c2d006a021112030300c00c0c1c020116500c1d081c0ea405860078559942c0c0c00a81b4841c11a004074214086200051402d80c0c2c28 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 849030863 1250 849029613 849029633
    0x903040b0f070308130f14011812030608191104020705010e0d0f0302040b18010509060309010605270a050604060510031a0f010c1403070c0806060102071403071a1204 73
    0x16020b44c98003182e035a10141e0b04100f8011010b401400b042d4141410340000d1503425007080d018003c1000019080c40716200381c100003203100ea080c0e07880c00c080c42141180a43c50b010b0400038080d52000340170b0071486003181403c450342d455002003a5048010b9111420340703076681541e441c660801c00900640d101031149a0301e60b07640c2050100006e01c0c00035040c10703082c02402214221170a2050040c23425030058050034208180b200702074100101000041180e035034020145000c0e072408400081c50307070f00d071104120740040c0311540c403410381910308458494070740d2200c5c001d54400c01d4110080769503074611001900600d0360740c1000b0750101903c070b030552080f58168000040103540c4001000c045110504101000100090f01c500080800d1240b20010b1300b6207803480449401c3c0402c8909100b415070751440540c40030f1f0844a06940281c0800100b0360341044407500801c00c20718406028081d9a0200e500e91616004040039080003044d0440d0700d181d14070031170b500780317a1100040620303013401e2030048401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 849032113 1250 849030863 849030877
    0xd0f2003030f0d05091009120e040b06030f150907030b0306010b09150a1214090607030b010225090c050306030f0708071a07020a06180806010b120903040b0f 69
    0xa405008a5142a080020440724480d00070307107074181000d01122106000e0000140941c0742402036a891820b44a414014250700c01c0c880d031070b1450072400340d541c02004020031300600e42c412420200a540c035621030100326034002003490150340036035a4808010451428010b070081c0c00140f544100045c0e1039165010800c190021000c4d00c1c29642c0e00d40144101d4024042d505030700041c1604024000d2610f0030042010503400e0400c1004d00c011038004030700310780011404400422500d010829000f03418400b5941c04459414200b2240c810040001e60f41d803e503036003058481c0340d02d0301c5030760034488880000d600400b0703052414000f07a4410040202a81c0081d5480d5019100d8044c0301c50b02014040b40d9241a100018001c0000318a00069810920800c400440001c08100241000f50b105c1001c0e0740054040b5440b0b400a01c1700801c104204218680e02c5411141c101200600503044035501b1110100038040c0c4078147da889000f503050540c8190b41c440c1c141040002040000310400001502c68 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 849033363 1250 849032113 849032153
    0x130909230c0f1909020a180e0412030504050c01050d0e0105011221080a020a260609010b0403110906060c0714041407020307060c051c050615041809020d0f 68
    0x100c000c0d000305108900400f50b550501808554806204054031680030f13001ca13108500c2d2108645800070f20b0f81c00a90b801350010f82050f00390b181000709010200c0102c00c9c4071001881c080025103000d0302c810b03440d074002c42d2804c1d040100009200107a14403a401c0340400a016400070807440d69100003604041213564412640340740401e4000b419408441d03420320744010b954844c3c10f40c07036981c84d46c0900207512413071205090102504007504070715500750038400d00355010010301010703041030400c008100005a0100748040010002130000500c2c51180c0d010009043c0c0e40a0b4141c1c44180004001d801104d001064070b00c100c0b0f9001a0181492100d010b13400010b9504000c0c40e200d684128a812504840071809a8010045000050304c0340d4084403103000c0da890031600b001014040c10610507142031014000310b440b1428801285068054500b4107217105850610303180c94250150542c0002810220f5015520382c083d80030364482082c40c2c0c050341e0340416502e002c550301d40341c00d08054002c0703400200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 849034613 1250 849033363 849033379
    0xe0129211510090e100b030c091302091005030402060706020313061a100c060f060602010f0e06071b0c1a0c0d111221040c06080705130909230c 63
    0x69903042c1401c80c80001036155941c1050076080c41d00b603c54584003d0305021402600e0580010405004009140030f44068420303540d40306000004c00c0006a10318002c04012481040302c0c02240d40d43c840a520784500a041868403556240000790880c0a11040640300310700004c1000090810341c00c030640400d1040304e04002c18004400c1003448640749100d100d800c0316805a4001e8005d0003030305110301a910a4002045040aa141e00b005a030007950250016079120211610113000700d00400c203071080d009008094901d014500180300c02d00c46d0f03600018542c00d080007038050241e0000c072480a424495042c806100f514802804540c2c40198003000a0050640e90b000480c4105860000c10b0300308001400c4d0450410a905459802114a01c0d0380300090400c03807404070f82c0170312428405c1c0e0044036050081031a00c3c03000b900d4008000e050302e0800804104c04010003084128220548800000c0082c1d103450900d00120030902e00b141c60910070b8080c43c603100204034000b4803001440800c0c2c820320 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 849035863 1250 849034613 849034651
    0x25050d060c0212030603030405091306090b07090504020c03040b090310020a0c1a04050c131508060a1b0f0c0f1505011701060501021506010212030c030405070e012921 73
    0x10f41c0c2808190740036a8142c108210030843e518184010641100c1c2290300c1e07001c01242540c031142159580302007182d00000030300401016903002003800d80104429203040d460b100a40c0740d07081c0c4922590240c540500e1001c00c0451083e00e04003c00f402d031060b0180119959001408d001c0c0050080c8441220300d20300310390302c0407042010464044c0c019075100d0010000351028904001070b81150186a4100581c0c0d400340c80070090302140410f00810000c0d004c0c0006040086441d015109984403404081940612504096074041d100d501448001c1c0f805103182d00d0a89896900101c0c0500003901d850820016280d1a5000c0e0b4411070407508070b803030030140c107401c0140d455098410360b204403800350700000b0441450b07040d01661290300510500c140d5450112507504841140c00c2a42d2022607903d02208200070094108034010140c500d0060f2800c0642c0f40045071002c4590021350a480b0000b40e440d141a41d842c20b00a544081d04900034421030f1154000c0c12a031100001c841c40c40a458005003d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 849037113 1250 849035863 849035893
    0xd090b062e17190f2f0f042309040201080408030a06270609111c02040503010903022410090e1c0f18050a0302060307050c030d2c25050d060c02 63
    0x400e030105e504844060008000d1406600c0d62284d440c04d400f0079400070410741074140310355401400948600c5603c0f04110740950200d1940810303110f07a582c00383d10f0b998180005071f0303000503186922031303030064145a0342da840d040c600e0702405542d4000030302e0701c0360b914003102158841c6c54000384041d0380d10300401410791740e50301c88016990640320400d00c0100030401081c0040560682516009400001500d01591403002c03a00311002c241c8260016000140404650402c1c04d41b2200a002d0301c030340c89800e5003442e12070500c1d281814030030f000f09507944440001c0001d106001d50200d061055021184000850b07201400081007401c00b50300290030b1381e807440200c0344250200003d40700003030302503541141150700b40502c0d5813024000302d05008041c80b08000070352040005250130403001e080860703002100704c41c100e01e0300d501000044403820300c1e0350400510070b8001a000e40405141c0104109181000c2d91002c40020a401040c1c2020f09103220909100140d04403200d404420b900710b8440244030120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 849038363 1250 849037113 849037121
    0x140d050702060907030b060d0206070506090a0c0807032102010906060602060615120411031002040914180c01271212020610030303110904020d090b062e17190f 70
    0x1004004600c507001140d088d00340f02c0c0316404114406090350b0f251140e16110f043c5070240444020820703512244130202006402040d98004143d0000117149050941d0703904407441080c0580300b844100c44050381e01e0340c603100350010540c003600400104441c40c0c4401c0c0007912102c007100c52a004034040140304010103401d4040301e58103134600410043e03689947da52114030306401002c60761325104100c1c0b80b130191440313840200f0041c02e4180300003400f102e40d00c24a00050000820502c0e07449003105035070076040000300342c01146504c00d1074890800c4a4003101c41070f6001d17401d038504182c040d00c0d030000310b200121000a841070074003401680d078030700140030303002c90381c8100481d03500550b800001010400a13010b900810784200345004d80c2030030494498042070490f00250284009641c850020005104408100a0304032009451032907003041d900c1200c2d81c124088130455201c803008504044221442180c642150061604041c045401c00c081103840c80c0303c0010085c0c59051030820000012409442 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 849039613 1250 849038363 849038369
    0xa080603010c052d1209100c170f0a15090f0501090b18070201110304110111010b1e03030405120a062415030b03010608010c03050c0f0f0a140d050702060907 69
    0x6045800a030078a01301d9100640c00c1c3c080c14000001448000705e900400000703a8400c14031503000b0115004c3c5115100d00f42c420840440c0c043c0510302075005288100001101ea0101c0c900c4a0803507a9281c07001f070b0385c008242d0940c060002111065000c00d8a0015030441c200c040c00d0900b05000700d0f41c8810920b004c43d88614401940041d0300350700b00600c0d4036440c02c246e0344102203000000352350908490403ca254400c03207045035009600c0580f10f602d5030300051000049c18111000708841034010b0042251544070404c6414610480300400081e40d07010800c48014100c054296400355034600c41e5140c0c0c820380c94404480032420500d07032034403040d18110b0904400d2041c5040c01c0c8110b291101003900c240c0c2020404003019161030b540c50321a1000d00404d0010a020360000034007020b954001021544040d10440c41e030582004030702c0c030010900094400001c2d2100d2000d40d40c03034078505c05540d401040e800150070013202041c01c042121450380080d00c01c01d031315002d9030801e40da04d0f400142c0310360f4240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 849040863 1250 849039613 849039637
    0x6090b0306060d060204030221060a050708270714090901050402060a03020a03180c090c0e031005101706010f0503030304020310050705070203030409050105010201060b040b091309080a080603010c05 87
    0x50002e00345140404022070524080c50300180380c1030300c94000c01e03d92811100481050740102d1341201c80b09004114856010032507010030032240c1003500d002000910044d04030881070200304500700c001c0300e0a10009140e0340e1780c4000c0fa40105e070b8031541c620300201e501115603c50b41c503010014110f00c8040c021584134940c000c010b1440c198a01d10140c00a410010a2008141d43c501c50106408620309201c02c401340a205060307507052418021005458a45202d0801c002c3e0001d100059030320009103035019450326800100f500e0380c03000012001c4100940c032446100c3c0b0483c0ca99402d118010469505a50f002c16030722042649030800d041c1d4901c000c2c6c030025016849030700c9400c40f81905501441d00724480b480e12038540040707030b00000c0c80c54100350440811aa55400100401e60b02489a01e0040c5106110a42080e20700150340c00c03030380140603c240c020703c60702d0803011145003541c1c0304040c85070340100c0650b103400f582d030300040c000c80041313601a00a6280c98942c2051034041c00c1038541200d018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 849042113 1250 849040863 849040873
    0x60f0305030a051303060f0e070603060e011511030403082502010e040906110a02030d050105030a0f0b0603030d11070303060608132009011203020c010302040b390304030606090b03 79
    0x2c602c080301c941c1c0c00640c1da1142d0101400001c00022024020003502d0b0351280c0c0c022030a0b581c501c0704141843c466602007011300d4505a42000328070a44002c07181128090740802c10341141c94282a0f66420500c0300a2002c0d0000040c00700c104601000a05604c0014210ae00700e1b4950a804415802c401081c0183c00b003240035500d042c0c58580340d007140100743d03c41d482c08107110318601328000840c0c0050b4040c5016070008200400041841d00c102401400100c004041a80300c9840d002d16107000a20080c00141c50100068040e031020411a5030110300140c007004044c880400312401034118040403800641010000559140b00d0300b015405071050000034200c02282c0da6680d15172100305c0004640c440940307601c01c1130558490030418000c07e040800d0305541115071074000e051071150b6036803a05046c030500c818070aa180e110183c40080c07076010101c100359941039500c01c9511280c85008580c8407032a85220312441000700150085900c1441d05010054490721903105480149648580607844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 849043363 1250 849042113 849042127
    0x9010c0e0d0309050a0f0503191208130b0c030406050f0402011407171305120115030210020f0105070207080d030e0a11011e0201230f040311010608060118060f030503 73
    0x1c41c4411919100341421495150740c4c078007041d04142d01e9809001c81080c80f01c01006541020300203004e09586040b600581440c1565454619050654803102080080d03000140003001e04036044558980102c0741c08801c0c54a1031100c8003550084400b282c200f82014046600312440114641c0039a90584507403051850b80703c501c2880e900400000d49222240a82e0f4140500180c1c000348204204d4081810426080400780300b480d821321100d4103181c1c3c0c9048034403040086035218802c01c1d258100d40c4200c20034010b010807454443c1e9444400019482d12061009094001803440308841c1000140c44588030014800c0e0b007250200b850140c0c1c2030b0000e100780c00002d8001d107150241000141006914100c0c41c1c229400c011510b03a40240260395101c4500500880d03a0300070804000107110f4051542c44c05628884803098007510007018001c4051074855208000e40202001e4810700040703514540e540c0c8904426000c0301e042c3c425400b4070309070300801c81c00c549820b0901070381d821000a51030b2a007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 849044613 1250 849043363 849043369
    0x30b04090506072102030c09040606050f04030605060406170109030e031203011712070c0801142401020309060a0c0c0503071d0405070911030708060619080a020c0106081509010c0e 79
    0x1c15803560089444110000130f000140c6071010b103014042150405403506019002e000c02c0711240e4200100f41701041c44815140840d000460303043d2948001d0216250304c0e41350108002d804070307411141b01c102c1d00c2200d000c2442c005501110400740660790300e605034402d200a140c1c0b101e000701414590020108014818003061000300600d581010044648440144404070358580051f5011079401c0e000707003130400200b03509010f214078144c074410320018941404c0c00c104000807031074080d41e042c04407000307440d158507070007842a99440000a010940d50701c0310100000c01d0704541c5c040448035a819034102041c6401c00003403034401d45030b021001180c80004c00c0900021404014412a030a1244a0010030101c1c04c0d40a0402c440011148a50b201e0814a0000d03120b1100142103601601d010b0000b25245045c580b900c44200480b81410501178032000d111802a00c600b0f034542f01c1f15030a0100004552234001a034400300e03076203e480e00e00c003a210780c400079080e60719a10102000541c094041c811030b00e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 849045863 1250 849044613 849044627
    0x204020304020a030203060c120916121a011d090105070c0f08070203101b0c030210020a0507020904051e010608120c01090510050109180510111b0607030b0409050607 73
    0x280014103c074103441e034030b500091500b4421280090350b024040f40e000b1741e10b81240400390704615000003400c03507101c00c40d541e105c11400610070680b854500fa080340d0148203010582d91002d0003c2e091204003903031035049200c4282003442001c10040c40300030000300d1004043c400c0500800156032182e0540b1680c0e02c030600c11144005060700d0041040041800698041001074141c114090f408100040228840b000901548043e281070165100f0b82000007075001c03801e460f103003c1c51400180c80700840d0034101c0d154019078100130b41101e01c0c0410311060000c0000c40000d1040904869015a85035124003406d0762074503c240042c551080603140c880304541c201411254010400005a005654481a00c1c11030581c0201c1c0394959110010f0010b50712034000c802144070349210125000003140d48103955546801c8952880c186d882d81c0424112905408543c0148078158045900000d01a0020b0301d0310703820b40d1000082032503e04d2600580c00c050040000300b0b40c000c405040c603541c0e0442c00f80d82070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 849047113 1250 849045863 849045871
    0xd061e0509150907120203042f131d070305010509160b03071d0316150c11150f030f0708100501170604150b120117100e0c0a033c02040203 61
    0x2010140038026404c085c20f1020b5071060b4002c00000c120103008910040c4103d90904401d00303109584414013110340ca513102000800074070001c00217140c121209001c03446490407280314015004900c0000280141501b10501540b850002d0b0750303401401c001c038400c007584e0900c907699070a0f500380700081d601c900494400a03e01004082900c01c419000c001030b0030000c8200d0740440a2409071024006400e4000480d04c18030028180100400425141c454441c4050303202a48150601d0340c41c6a0410104400da606003084030032100d48034107110000c50751010003126001c0000f805e8200040944020301411812544103840d565810989040c03a0206500010002600141c542804000307071840100d00340d0040100d02c22480d1104030740b41b0240d48403401a80031403590901d4445c448408900030403441c1d40341510010004003840c60420a500302410407440d554807045000c000020710401181c2c00d02c10000304d43c2c1030302c81c40c000154041c0c060008003030a116040150309a060050405178015030304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 849048363 1250 849047113 849047117
    0x10602070902090406030b01180506030c03280f030f0318080d02031807180f0510061227050d081611010e0a030507020a061409150d061e0509150907 65
    0x101900c0391110600c2d10000c0c3e204c5030040c0c1e844a00a4071409d094030841d5088101140505080e4490600099860a1500c2000d00c5118900c03611468903208140c0641d1507640100a001c00c08058180903000e00300c240d8803140403d041102e0285403401620902c548150300c00783c071500b8440080505402900000d00b90320808a41042e00002c41e18104440350040c8405c501030048900156840f4007903030803804050390380508020a004250840c8003060040d02e025281014040809843e20005820040000500c0b509074403c40c880d49240c62034001180c1c0e0095044946400c0d01600c00c4a46c08000c4448840070710151916468003031080a002d080e5840b0440046150a03035142e0b1942800410501140460301c0050301c1011801c2c0404501d00520250a25440000c400071080860384035072005184103c02d400d03405c0c01811180e80994800009048080151a849199200700c0c0c0c02001d4010080e1414034000150178548803460601c9905c090b000c104c80301c01c001080c4102806c003e0440b0301 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 849049613 1250 849048363 849048371
    0x708070c150b1509040c090b0405010c0318081507360302090a24081b060705060906070207081209100201060b030c04050411191d06040b120f0106020709020904 70
    0x1016543e802c42480c0003e1001403240d6101d16800400040b5442e640040c0d0a000c031000080140c2c0300408240c0e011141c0030b08202e100007243d840e0403605e1400f401d00e0705e00f80c0700a11902203140c903000100541d03c40344c0c02c0c0640300d441d15440006d40d000002c0420724080610704521040e544140441c200341d80400f2103450751502900c03a40040c0b1000300466402418076520070341901d8080503104913104c583c41c000b10306401e29040421090321182c4d444101c01404e41c1722404404241c44500840e460341c1e802c80151891b9040c10301c00140c4450054030756000600c2078084c0840c0092000c203d0303003102d081b41d0300f100e031034a9003020a0120010861500c0c4055560f82d450000f40800c1010045100c1d594900350b40e541d55040c0000c000481c5c45803c1c0408038900203100c503803000c44601c201c1c0c650344540341c1004079956a03240880514003118070a11034101801003400500700d080c0030050501601c8108070424181d551640d100d5200c0340c02d10507070300140d000a43c1000a42c4099005080d040790191002c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 849050863 1250 849049613 849049631
    0x2100209060a2102040b030a050c19030c0e0a03081804020918060a031a0405250905040c2103020c040b01050307080c13030f0201020c010c0b0a020a17100302090708070c15 75
    0x100c105c1c1c0007903002200b140340000400482c1025481200d40c410044002e00342040070198101c5c02036075000d075480041c56500d6a00011681c041c2190303250341e4100405071465142c5a141440c201d80180000c20b025080003044a821440d0038001d6601c022400350000c3c80c0c15001480c1401000f00291079650841d0324402c012000c1441d030740d0011304031103a9002d04000c90405141041c6010f6401c2b4080610a42080003500f038a0018180c0c2e004649045102050300d45980c1848001c0401da64406801503509589040d410074000b1080c1d01c02074080e40a81d4507105800040c8001d8981c0039a100303000070030410003e1401ca001e89988c640000e40d00b000e140c06d0221100404408586a40040d2403040240d0500c90440da810040c8240c2c8030fa082c0781444039840e5aa1ba00700300c0c50310150492001503004205007112034890003c140740080700880c23000160500150b4070a40c155640001c1c2d000300c82481c0001c050038000e81c2d219000310500d6640580f0b907030160321030000759a07940c070f20321041d162100100e13 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 849052113 1250 849050863 849050927
    0x309120c0809060c1507050301030b0105041e0c091706010806040b040c120b014410021b01050606160609030e03030a030c0306090b010c0809061c0b0102100209060a 72
    0x1804c00c07040c00e03400504280842e4001248118001007480d400c020341040180002510211403604440e0107072070100e03004000100c10044c01c01000c2c000c11075580b0340418000303250343c4004803804540352110700c049490500c03040f00f0b42340d020074000c05495500c0b1743d02140000701c40400e8658468040c404140c0c000351100001540c505031a41e0a0b038440701750300018090f41110000360b05804e9522241220b81e4650410341e8006072003103110b01c0c00041840c03010610030420a00c5901103640410408540e1031024041003e000c0c13241c268803500d03039840c01c000100c85013000d000319421000551000000800c596503008058502950308404004141e0a405080e0318204054109015035460110389d0001c2d40b031009040301c0403548480086403c0c540b20609030303600f00c3d040c1483e01d038100200642c0c500e80c0e41d0224803148a100d1401c4400040102340081c445516405070540420907820386041d00d2807807003098260b010b081d1245500c2041042560120f41c003801700c52981d25090600c50703890350000b1405c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 849053363 1250 849052113 849052117
    0x6090209240c060a06140904050a0b0c0c1f0b060301052407080a050c060a0b010c262208010c051c0f15050a1502031c0e01060609090506010309120c080906 68
    0x7130000c00e292120401e12482460300d42c10201c803007090f80d80e40d26901e07094541c5076542800c40400b030014941d000c00f2030b9402e84054119041d081882003101c43d04e214810700640070141c1415840880c81c9052100f0321540f03040001c503412184020900d030846900c1c01d0348860030440404100f0300d075040400107031000541e0040a030450f4049501ca45480389081c400175403d0a0006288840300e030324091401d046030b0b130044514031120b60445828030700a40940b800040840e011091044541d40115045078007285c5101320400c4800d48000c804045551415580e00781c44548411002182050080c0e01c20050508030102080102c40c0d4003103007440d02e002d0503500f00d0740b21082000014268135810300490a21426100c001e28140c0c4100c005a02e250034000d40ba0300410030203424580155201d10b20416041d04002c2d1003000203c000c10217241d5440d00600028842d100d0301c0303269030400001a907958000e01c40c40a12903049900020f14001d032100c01c503050a040601190300300c800b4000a0304d41d46500c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 849054613 1250 849053363 849053371
    0xf0405190503010c09211e1a010b1b0613030c0501091b05040612020f01050a180602010c03050105030109030906032706020403020117070c0605041a150406090209240c06 74
    0x1500c0f4a01030401400c03112800300c1b40740208442c1c0504c0c4c041e2000a005c3c0d0045c500401c42e000280300000640c7c6080c1c019054a00484002818404000b00b02d081443c0c005110301d00000076440c094a6080c02000d864500458248040241030005000800d005003a0080a14440d1000080321481940c82900c4803290b24110303082030750881c0c403e00650410b4460840078040c242d488040e81d58040d800140d92207800403e080c108030008c1910302d60a4011880342c624a491511010344085d1207140c002e0081042d41010b50000742000000141030a0604c5101c9020b03400d6550140c150f82852800d40c003502061500c45100422401a01e841028003100605650710032100540c0c1c8900d10b00004008226103200568001c001104dc004d41681104011007900c0d8408008034496880303040c9118021702c100784200c0707113003d0242001601c1a51120081a0b08011103042000700e4454000200f20700482ca8100d40040c80d9094500a0181010410b8090300e410342d1202e142035000480c150411905032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 849055863 1250 849054613 849054617
    0x15080c0c150402012a140a0f0b04031b0506040212070f0b0d0c1b0b0403050d0f0203070207270f0204030606060c03020705010314010603090f0c15140f0405190503010c 73
    0x19040c082150307800480800741751030701907248034400c103031320314500603c55040130050502c41442503620311142c040c0020076034242c214103401c5c44e5441d24245084a01804c913000c400240401180075150111001222200d58011000b080b003640c5a90070700c261010010700d8007a035032143d040d0000300c1d2642003610002078100340c03102e603444042d000d1010060324110407141d01400028032171110020406610300101d0764005020f2519502e4505042d103042c4112401c0040041c184048115048640c0c0c00450060340341da400c4540055540400301c8250740c98003488012010a1a480341540c600c0d504403003050700a180300149800ea0360b64861007120721a034041000305508200340760600d074040c4031030b0b8000d240c02c3c2010720641b440d9040c1e685480c6414040da605065903401c801050001c110b580400075507000a044542070344030050b0402c4070130060031100014141841c0c01c401750000e2000e660381021500c02a03030801c0c1c200000c0101110031a229907144080b00b05000880d641e0074020032070000321a1f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 849057113 1250 849055863 849055903
    0x7030c0620030c2104030c0e01141519020c1215070503071b15050c03090d02011b21060e0a05090c01021f02090901180b030715080c0c 59
    0x640120760044005421010842e00280503e1015030404941110070f00c000c000520600400010021524011500050f2034110b032a45c02041003012031000301d050314409052504560502801c100070490f62860110085038281b0000c1c11401042e40c2c0004040f45038016035000d41c694038040390901d4040b00c44180554410310b03c00440d12089483e0f5504080380b0b2924501d5458001c1e406403151000122030100707008800c0f001e4051160240100512107401a02400381c0c0c03e10100c0b00c92181c00a5807000802d001d40900c28007140c1c01489a907101c14000e40c1c48a0150030241426560300c0074034210540820703a40f41d11601d0320840740c0701c0c82c4050150b03100744c0046800c1c100c2424048410051441c0034942c08080e406040b0380c2c00081aa01a0703402c6d450344212092004400e00c0a402102c00e4030360480b00c0b21001117041d202e407511080740c000e0103240030001040c0b01000c1550394880c40c40347e4112000d148040c031000e5841002001d5101845404440c50300105240d81c41c504404094040d0202c400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 849058363 1250 849057113 849057137
    0x60218030f0c01110d05120403111f0c1d0402073f08072c0a0b09150310060804020613080a02030d0f0f08190507050418020f04060302030907030c06 65
    0x5104c0d110441441002000c1c4814a90005813041c071881c0c0480680326150000201018400c40080d81d10a44500c16601c8041c0d40b01c185164081e92074814183c1c107401e00344170103c0c0070f1242d4450140d8a540100603461450114107000007540700250940d11040c50480c1020110140110072182d4a41303401c4015031100034080b101594004124480c4c10407014000b480b540726030061004060078640c0841404c02c03a008041040031000c00342c00c2c3e6402c02041100001d1000c006030140132004c00550710403c805181072401d014074841240c102203c0908540180030092241c001d09501c1385c406003c10b407038440c070701040e0340c40380d00c85603ca0421544041940e00850030148030006c09041c0300d09102d030512110080181c070043c0c0e01c40c0207104015241d070004400e842d00003400d4007403280103e0204080c1c1085503000301203a201d1701030b080c01c0a0b2251141041201c4a1088409601e40000e00750304150504030100c000e0360000c2c2807100140b19050010000c0b40c4441c0c86000102a1034442e01003110b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 849059613 1250 849058363 849058367
    0x5060a12151103150a060f0f02070f0b0c0613020102031c09020a0e160c050d0318020a062d020613030e090a0501060e030c0d0201110f010f15170a060218030f0c01 71
    0x130024070081d000e8000f504003080410703000104820210400c1c00d203101c1d218200b010403460700105c5c3d44070348403000d081140050325150f40b10003424035401d085c040c0c078400c1d0b9910400ca150070001402c0240142c1c000c103e00705403041c070540480310311401c00402007180a46500055040c800c560443c842242c500310038840e00c241c40b5100c03808034565074203010030205580d84825071111070b010070031002d243e103030141020051651112a0a0f09034010034801c411602c40c040281244150155807100a4101c106001d05410860010b0607150321640100350039a01c04036841c8802d0b00d044004c9042c0002d5641c03000c40341d41d801c03019034841e5510b00000112585820002485880c1c001b030310a0290300403000f40481074030b4554442d0409602801c00703000400f41440300c0c0f4541802ca030380141d00c5521b03104003d465002c1e540c000d040d000c2140703234002c002e01d502c620498602107006204402940c0c400300e40c01e00000c41c80d40103001420900014040e8070b0442c080440c0c00c0959410b107178121600081c507003148543e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 849060863 1250 849059613 849059641
    0x809040b04111605210a110a0f060f060b0c15180607050f04030510050402240f0315060703020703110405150d020112020a09172d0a0c0608160305060a12151103 70
    0x1107030140c010180c00348c4546401020b50340003040541000e480f590710070200b0750310343c000c40014510b800d0116a600b02c1200e455442e900004120071f004034114021900492410340f0380350750b6981540c045d0051742c8861405841070342c894080740345440014407001002c40c00511001c0c0401441c0301020076103103040d1040000403c03580041c86202c10040c100002e2210070001940d54410759105641d540e616241860545a1034034440c1a0f41300300000394480c105680443c03940c00b22842002042c11316004102000240d40f4102d030007003415049000c0c503200c02d00c3e080001020450040c100f500d010390907500058107a07804000d18501081903c08100500b039662058a49650407503805040c450301c011180e0900c010500c0500003802e41030461503c880103003842488000e0f0790104003910721070395968001c1e01000085405101013074008000c1056507000340a22441a0b0004000c03078400c034140070115001c000006000e440d2428410b4031013140d0002c9100d615000d20b02812070980b20b21785022551415 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 849062113 1250 849060863 849060887
    0xb0102031914250b0c0315040902010c05010c030b09090a030f1809050a0b01180e060d1403030c070c12020a032d0809040b04111605210a 60
    0x5510070480c00403900880c40101d6901c18840c40c1c0807001280e5034a282416014400207034030015030305003505014031900303210302c907000744148034044440c4d540c90b0725062603000480f80203008151700d8440030000c0c5815800040315030300c1414130215442c943c4e01e480e030031070304115649800320790344147c0c1d03925614000e010300d540111101c0042c0107100c86590010000c600c81da1b145401e00180782480041003050402e900041d0018180410070f500c1c042010038047c1400e80c0401d400300b4401d80030018000161a129425541c4460910360b1030f46520341480309004900200740c0700c960010015800b058002d1000b140100710010400d034403450507061521a10800303038040422551020040300050300d0f50716040045030340060b00382280318881180d0003a2a003034448055080c5150415941c100a00580600000e010030303502046144042070034003040f80d05564031003460701d00500000c40418a10342c80d40c200180b15a055842d650720200355030301c82c0710b0100801c0c2001040800d04161007a4000d900b1b40c00c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 849063363 1250 849062113 849062117
    0xc010612021e010c1505070905060909010b0a0e030604110a050607212709150b1903020c0609030d0c140904090201090503030a03050405010507090320010e0a0b0d0b01 73
    0x250140c0d40d00081d140040403980400740114680c08420503030140d07041c1d400e19038001001410360345482401c0c41c001d020442e100004200003d0f40882c2e0790804409944070564054105943c0c4d03400c00b0a10400303900110f083c0350401c13030380c666020080e032410706c1058001c500c2190400742a0120408210406280f0b4110070302803407050105802040b81c842559217a42450703200120703c18101001240c44040048401c080405499072584802e9a0414020101e8581100421070071300c5188041458036218403501c008141c0134420418101a103041d916850640741c01c0046c641150075150600f000d204a0308100a90000300c1d40b600404803e009800c01c4111510348040041c1a5011085160141c00782e05801144d980801404690080440c0409450028101c0c0d03101d0114400c0180030700011035045485500340800b152155010344020b01c1940e6200022038208040f0703401440c03031044114481c41c100700624401007025115001c41d0009400802107071a560104a030f440c8056680c0c00038001c0c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 849064613 1250 849063363 849063389
    0x20c0616080103032717060c130b030a021b0d26010b0307140f072021010209040c0309020315010b0307050c01110a0228170d0f050c0c0106 61
    0x20300076070198801c0c1c1504d0341030a0458404040751070950110f2800300340b010b034051003544045025140190110700c01c0d1003031030840e000c540d41d1401a40c85800344101d8110300076010002030110b00c1802003e5603101c040040014207145109030100358032400c46403d503d241e00105040044164001c43d02c242200d5400c0c5850040d14200c40901c3c00b243c07051180c141441d038003202040700f082c1703d1840844030004034040181c0702c8040308a00a403d0384156000c484140030001c4250503003135000c400030306035600140011006c4000c000c48070344045000c0c10140301d9560030040c0d000990764505c02d5040d5080785584c0007428640354410300d442c00010700c16240c540140c5a00402116021100700c03a40b040b11403800680b0750515544560143c4031203458500c061001180307210380c1e1640000c801c959031150400740007035041e100c001980350825110015206007024904503407110010002080f00c011001000a202e240400005d81180c00550302c0341d441d2071000079081800c039024001c0e00c01800ea28103c482e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 849065863 1250 849064613 849064651
    0x50301050a060c021207080c01091e0905060315040303140a020304021332100b040b27060318010b0f0d060f110d02030106080f061c0503130306020c06 66
    0x200d80701074a200d20300802442c100722004549880302d4001a0f0440041110b00c0380c3d40703801c85c4646594540001a002840030440011510400d5079003141400d120640c01600c0d5003000c020f8006880010001c41c0c1503c2104281305004100c600000c0c0320314003a41d80001c41b011010106152008003030201d0329400d00500130312001d0307950301c8070240280880031741c0000d40485c007851038a103986040c007030030f4030070030b141c01e0b0340324008696601040c882c6110225010800f9214500030109001d0741c01a2440c00d20103020342c200044080c00b000301c0c0c0c40120f00300021122228000514250310494101c0140c51404684403020007090040c00b049800031145241840d0310301c03010840c800f240e6080a8545a12102900100045588001c042c089591020381d600c405803006403020354020320030030300011514000139000741c42500000b0301940009268258028071800344102003d0b032208152440e00080000e11100900c1c903d6101c02144120400768440c8600e40c002810803c004194150010010101c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 849067113 1250 849065863 849065869
    0x50706080a060f240e0a14031504030c0b10090509010b03010614060d02070c050306011d0a18020d0c09050a060f140108190b04020f0c0f1501090b01032a02060705030105 74
    0x84c00407604d1280e003400310007540410480d600e6400c4950290801c140c68004a5640b51898001e40501800c0c0e04440e0658800c48403660240720407a0060009840c081c401c0d0002201c0110440c0c0010b480304c03c0c80b034182d4941000348112102a504c040751a035654884c9800c0d42028022000100000440d0a03915149480816424032604101440095000a901d0300b0807440c141098041d040c0075048071115a1030b016142d148142c248800c0f5822a08040003542d204d400c1c1c060800300304c0180e0f440e0420700106074280411184040c20131610307000c0305400451082403034441c0610881745003d001c529180f0f08a001090111507400240d611300103049800c2040c0d030400d0b517441d00a0340700c0c648104084001c09a45004044484980c0c2d0320500018030709680596200103408200305050542e0f8602c14588115903680000c102001020001c07440100141d1009a04c6280507807018107000c40d1074804803040c44114000010252946840400039031034143c2e041002c43c0d0302102034103155280d54101800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 849068363 1250 849067113 849067139
    0x818070b04050625060501180501080c01050703050d0509070611070f14031005040615060302091f02070834060203090d0c09020313060b1c020409020d050706080a060f 73
    0xc05000765800192804406849104180c0c0c040701c003401c10310355441318900b04000e00001e100b0765103e403900f0751190b54030090502c0707454100d41c5c0e0000200001e6905000540b50f44d08000c20903014000c0074800c40013420803500400317104001e48000f41904c903003070140c042d201e20850880010144e002a1050040c0a00341140000f0340e1101101a6501140c200001e40380c403901b5112094128100303001d1100b04081d40e00511025030711401901c600549940703088040b07000d440b10107070b44a00c40307040d103058202d01d261032016010803510503969080c0d250202a13140a81405160203002e03103241c88513400c0c40081e8020303140503058800c2002c6607442c0c020020b40c1d038015005200d00c81c800d030381d81c4442045050b001860040503140c00954803850598280381120440d4402a240c150a2900f80906031802001d0114000d032205d031a901d03090110b03024800100540e04040ba0409055440c00d4007145007004200003c102994501c417540c601800a0025a0040e600418034100021402c0c0010503207411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 849069613 1250 849068363 849068369
    0xb070302070b0103021309150f0b01260402030c10051c060b071502040510020a0215090d06020f0405041d07080c210c130c2012030a14070818070b04 65
    0x5141644000340c0081030300601d0f0820000300750200c81e16625648100e230b1307000440003550420b0100014918480156504c0c41168403012081303d00c404050313413060b0a140115082400602110080020304000c20010088403443d81d000c00c001198606ca4140d0244034081460340043c010300c0a05e284c090b140c401409200002040026034900e103500f9050568190f5000304402800e40c00c0c440c401c514080d496841c450400d90040344940003003002c0c00c0c08142112198040600804041c50154445000a4200b22024640740b001000001a01c1d80d4a00031800c90b01d105c01e89500070515440820352511625901c045295000031030710b041c40745c0e1205006d17142550010307000e1364882030903004141080c501d810341990006500c9880016401c00c0d40c01070507056602d407074049600300c19801d82050b0745400c008038215540302302c81c000c004412050140d50080540da0001c40c040c02442051900e49500b2140b280c00a58110304203c0e1214140c14526012035049015040036400c00c1c03d00350340d034030a0f80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 849070863 1250 849069613 849069619
    0x5090f061e011a0a081f0b1b0d020c06090f060a03020909091203060f010315082805030f0705070b1210120b060108060117251404031509050d09030b070302070b010302 73
    0x8400a0f841c5800b4480141d5010281503d207241b0a4454a126540e504a60300d100c1170540d5880c00c0b0b001c800000a0100309400c016001403012420072000c003e0342c0c0c1d000300ca40c5508a089800d070000c082c0c0350000039019680c00c9450140e101c0d8021014030042d40b80041040c80e60782c0c0304c400307800c0e1010f00c1202202d410810599079030080492020060340a00150355208007141c00c01880005c4010002c1594800c1c070003411000f440c140510400e85000c0c0b255400302414030b0b0403c0102500c60394503200201a254810400d59880603540c01080045420035041d15515416610030001d000502c40b4400c40a000c0450b006a0790318070f00e0b01d44411185000704039034140542c040201d107050380070b00c010540070070a225110303846140907208034880340c641c1007450740002e00100020b500c0c01c1c003420100c01440c868000050900b46540c40b03842254504103080d0862583e80c40f81e0b00c01281091018035035642d826203c8540e03180c0b5600c0c0c40c92031500c004014104061040c00000300282c100000380741103a03012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 849072113 1250 849070863 849070877
    0x7021510030618081c060f06080606070c08070b130e01120605040c12061a060f031f0312020a030e0f03030912030c0109030915020d1205090f061e011a0a 67
    0x100300c030201c144000c9014202d21404076069890010f5458101c400d9540b000c1c2c284021b940c0c514a000ca51400d034051040802d030b20701c00040c040e0030f02d44040d0000310f000e4802e83d0001d0340c2d20000c03c2d042400340d130802d568841c800611200f52600c00184000184900003070740c20558507080424420a0391850024440c940343c2020405000194a034030f000781052040182402c102494980300820300d111114528101002007442c0c0b5161080540d41a603d0b03231b03645c8504d5030f50b811440312800e000025504a80f0400b4040200104003a44800d030003030381c00b83e00140001030441c180030302815800b0b100f86200705030300b00325006162030200907100d401e50241c51011203220007505c03c90440c0107a1820090940ca17001c1c65409042d03100204000701c401e0340b44c10f100300403802d0400b2038a800000c200c1340081903040d0402071100c0519030155920084910559510701003e00b14942001d60964440c45a0b1615561018a1405440d507241c01012002c00c4640b4102103100c08440034061010094280401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 849073363 1250 849072113 849072131
    0x60b0301090503130911030c070f03090b0a0906031a0609040b0105120a0603020901080f370b221a04020d05070e0103061404051b19080105070215100306 67
    0x82500124001c80d881002c2d2a104c000b545400411342c81988500e01000e800d14440b21845601c1380c080ba401124142c00e21450410641c88d5a50200001c1000302e00b00003141d01c001824000da40043c0c01d42601c59503d007042c0e603140081c01010780e120f030640200c0030f55005010108035901e5100b22840340d9002c0e030b404601c0e0403050005841d02d0143c480744218440e83c21041004000e0702c0e5115009417803084604d46d802d641c83d02c24407680c07141c20200b03c8809500c4541138810010795814140070b495a8400d01091542c25141c0c241c405654104044441c10504020300241044a43c5c03100708601150f5800100c1034510346032800b02c6003080074000303032401e0884d005c1020b5403100105a2902604102200c1c06070f5540c2d8a00d44100a00f40b0041d900907241407400458450104070041c0940d41200080140c0c18844018007411900c0c1404181d0221050501a007280c0d201d09805004100f418000242898040c1340a41848180000b2100c0c08604508100070004070a0300174050366003014001803034402e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 849074613 1250 849073363 849073369
    0xf0103120210050a15151d0f041b0f02210d1107050a020405100503031c02090d03020a05071208030a110906040e06011e200304050409151a0607060b 65
    0x1195a610034010342c1070400700103800485400110780f180943e10300b500310300d42d6410310303506c3c0010a19503580015010350340d05071035581c10310b01004003003001841038113502c072400001401c40e4a0200b560190702182494900c0302c0e50440a0840d0100c06400500aa088844000b00d080665283c03030790140440030800ca892030b4019848001150711602070160303640a10306009070b0300e01485100301d1040741041c000407140f52100301c02204690340130f0021401c103011f2140d41408004400c1134400529030078807021410359241c1120046e0a4069005001004124144036041c0801500044e141e525010010360010b14540c08590340030200c0500003e90502d4a079103000d146c0308460415910a00100b0041a0501c1e42c0d4a0280104030981710702da009040310781c2541044015004038000b150441c1d2b604503201c42c0f0354410080d00400581900d241585500004d41111980c0900303441c490686500805084035510959030000c400e9000c0b101048a600000f03080351085800081002d6158216690366071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 849075863 1250 849074613 849074623
    0x3090c1e0a120c060203190509030c06030a0606140307050301050108040c3f0b010b090a09060605040611010e0a110607212703031407050f0c180f01031202 68
    0x3040c024150807245a844001c001c0d080382c0000280c1e000380369201c00249a074000400c45804442101081c2c10301c482c841c038291a82d400c011a016058002c0800c0c950b600d41d80c01c001584245200b11001400e142080c030014a4640204540001c4003401c0080c0510b203604a000ea80c110342c0b0134600000301c6e0350340d850651464a0300b036000001c0344c529900d4202c0002500700341c1c40c618510722100007040d00303040101c1c0d0f41c410f00c071035001800c41d494080050021181d018020f200c2d00002400090f20395030f94003064421100c42d644034500240c0c0c0410148009540140c9d200c4c402890500240203c404040b40c26817200c0340080002d12645000d540555180c070f6040c2070301d0b0180c0e0401005a02681510f4441d404d80c0981d8501d41c0000e840c001040b101c422941d54880841e0480082e041c10303860560b0b03000c1da0102ea040f0b003010b040b040103020500c00540304000074400358040c0000351842e03600000030700109090700e80e2001c0304800c1c618204407403080d4405916045941104118030300c40e05503c400d900388 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 849077113 1250 849075863 849075919
    0x20a110405041e23032d090a0b07061d0606010c0312051806060103090c05120c060409140c19030b0a080f1c0e011409040f0504060f0c0503090c 63
    0x80c0c0080070618140a07080062502415184e20301d15480c0480e1240c9036264031460700700c001c0c6003051441c042081010804c010007442c2150f4001c41c80d281c4d5010004403049075560040d00c0c00d03500041c0c414200200c2d03008103070024100a000d608510301c0c1c410205c0d1a40742c001c141070b0401020104002c1490b218110b2451846003a000c20056418142904915149510304100c0d0b42d10503400442c3c203e500c0781c8140002c058005111540c40c0342080304020f14001e0300902400c040c496030f00520015607815000700010000101c000a044800086803441c0c440014908001001d0a020301444549030350580000d0b07900901d00050f2140540002175904ad095400c500c4c241c3c4501601d02c1558080040c500c1d921180707000c5e020801c0300d014942210702c06a00039170980051139202c0340305c807507080d120301070141c80100510100708540002e601104030b0f081101d05941c026140c1c100f03071411600b2845071901e125420700d083c0d0314614000d400259280109100d081c000e102c1e051000b1b403811401061000c0c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 849078363 1250 849077113 849077153
    0x2c071e14010c0f050c011d0a0302010e030f010e06010e0a090c050402070303090606170105240105070c0e072609120f040504050a0e070f0e06010f030b090124020a11040504 75
    0x1010a107810070b00d58410170401418042500e10300c40d4a9a11041c0d60700d0850f400f801011816094110350044503d580c1141900c0d42612400300c40750841c0e04280221480c4010403402000650324000e03641ca0742900c0500403a425518106250340801ca1141001c0c050307600503034000d40d60f030107246000c40043c41c04035000703806949030020208286190640c450280c040240090004d622821511004250001101c60440d03a908149074483d500510103000d403513001e00c100b03011640d90784100347c0043c0c008485010001d02500401040460350351500300c081c481c454400d46283c0381502105a580114069001c0306a60200342d0310300e5010104101c40203041c01030814407890802c0030f61580034040ca21441d0b8828040c180000c111064071500c000110781e41c3c0440c81a15444810054610303121014000707040507200d0412181a80390250f80310b008041540148240b8000b581074800d107400341c400280110341140d1055800b1890170308004052004c1214001455220391170300001c01d441c45094450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 849079613 1250 849078363 849078383
    0x51e0a0c05010c030b0f0405010f050d05030c01050708060907050307020709020904020c12030a0b1c11040905011e06060315090e1906090b0c040b0a122c071e14010c 72
    0x4000e0f816000210841740030749109041341341d40340411050310803d01805420401ea004101b22500c0c0c40075001850902500a4a107030112004450f420744d0411600900800d41b02d0040c4104c504050400b135500111500e0141d0560401190007501c820591140c0d606040d00401d00500994482d0b04841d5407000b200c084802c0c2980540d69060b460b001118921812031408a00005c6400d02c407503105510714819026801204080c2e95a52000e0040c500150b0003541c0c84605000159007440b840350051aa823902400708403982c00c410701074031050b030030000415050200f40f00520720043c20000985003101c03800f00d01c4000100c1028078058410101400030105c0582030700a004983d40060034150003100a0841d0760b40d8001402560700c00e500c102e41c1442c2c010401054068810f115202440e04801008240705111685101c1d1035605034100f0240d000301c28004000c202d504014804c002c0ca02d6034080c03030021008508041c01038441c0e205004480202c031000c000306d03030312401e91000351582c44880e0722 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 849080863 1250 849079613 849079631
    0x115091a190b12090106061b150b06160210030204060903020d051213140a260a05030307120f050103020603010e040501020903060711010c092106110a020c010f051e0a0c0501 76
    0xf00c120305090710f000529518107140402c11740e00c03d160341e400c0d01081550242c041307120b40d555034641005140c0c668010a998001404c02503460030005e009001da94075540342d941c1420b00400c2a120900f40d40f00c018140704000811240f0341050000003280d8045808110f2800207080c510f05040c11600d617001030f084001401e0030308502040c4260191400340803050400d040a4090000314007140c0114803103d01c0d803051a03035079a020040c204400e074401c00e060b5032109240d555468070316003094a41d0400f064001c1c00040c01c400003031046401442c1e607042d05100a51454001c6260b902c4103029a1b40341005200000c0d0500c603094044401102c000f504070303030491404001c001c04941e80d210a44105500700413400c400103100301c6054054591070002240d01440040c800640c40d80a4681140c0756a00c82501c200d0301e200c110040c10b1030030302d02d4000d000c401c504000010300c101030440c5940140a000d01070030000074170300700c1d20040ba04119900c041c0d90382da11500c252200c45907068018069800d1040d80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 849082113 1250 849080863 849080887
    0x50906010e160509040507020a0507091a03060c0a0c0318060203361e040510080d021902010e120f01151734080115091a190b 55
    0x2141201c0119440d207a050b101d8402c1c076007075005800c40a01c006201403058848501d455032040340c1022450045030442c4955540b41400c10406501510a40b80e40d9a00200940f580281c1010b4012048003c1c00c528540418003e0403030203504507034000c014280300c002003018000c0c0c40900700c130410200c3c205902603642c00000c0d40c0351b001041c140105210b40c410419450414a921143c410b2014600340b00c0702403140501a00c0e8180020300740c00c2c2640f01c100d2100d181c0b504d105141c010030214001007d00b9003450252464a80542a450115030000383c01c0c240881c444034400082301d50910749a10050010b00000c0c0302c0903090020300b4151701600640401d0080150303c01c8440703610402220b102d03d40d5540002e0041d0060f15060f290980040a918100f080050f8851100000b1107030002c102e0701c000b0b0404042c900759500400c40503952540101c00080c20000d985000b0007003204140428400d61020711020610f04584034092006585170b807845071451904c0001600c50301c13600c580c507065a0303065 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 849083363 1250 849082113 849082123
    0xc0804060903030920010f0c030e0f0102120a031d0a020a061101060f0b0c063610090507030605010906060c0221030a02010b2107031e020a0e0a14160e130509 69
    0x1221b4040f881c81141922090b00510144c10495015202e01c4082003e080030f125441139444c14190441c02003510f886c5140d060040a040c0000180d1b800003202e84200c41c0030400c0c540c5801811170594004044100140d864885d2201a500300d440e050724294007103200341d400b6042503081641e1090000e4000b09071000340c04050012500c8040888507640c83e003030a4010309801102d000441d40011446518480600aa501c1c4586000300110341e41807103061542e1044a0310700108840540100a0400602c100e90180ea0301404000350204011450098068044003a40758028081c0ea00c1240c11040f0039010b07521003506581031010b80ba503c60380d00b04000e00806051030030314401c1100c945500c801c1c1400c181035680c0c903d0380100130b00c1c2181c00c544034184464095055044403529103004900141c45005e4124014915040c90702420300f4000303940030548450004c18048010200104500041d82d4500c6020814040c100111000d4550b400f00f92005020454420386500340780c21301103a5800098 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 849084613 1250 849083363 849083423
    0x190914061305010e060d08040f120b07031b0e010203090306101d040b041b081f0c1107060e01030207021804060606020f0705011d0d03090501120c08040609030309 71
    0x140d004000016144071000c40c0c20078000d69980c200f1240028044e81040005c24201e00d026144284c102070703903003000c0c1e56a0010741d0400d02075100d40040c22400c10141400c0c0e190050160700f001e010380e0001c817500004040300c4100d84004c203c0601007080e25640248122400d800028080e0349051510507601c103540344840c4140c102d0703002d0b02411648a4448408028011984004c80c1d84098a50b40c5032290314203992200089400c03814000010314501c200305200c8a0050b070b0590704600c0d610500e00c2000c032409210032405018000211419094010601c40152826070810040c8480b1020040b0000c0c0601d8000a4101e400b40c401c03100031900d2075a00d544603600c1044140300c06030f00c411040341c84000201044996610400301408298003032840f07000720921189c00382410440d4240000c500701c40ca0841a8045100080c0510481d68004420311881071700aa007401a82071511008080e003e0080002c1c2c06540e03030300c00a1040503c82d4009221a42c1c000101d81c510340c484038a41c00004850391 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 849085863 1250 849084613 849084619
    0x62218050f07030201090b211f09090203060a1e02040902041502010b1f0309020d0b1e010506070303020c010209060a021507030902060414030f030414120a080919091406 74
    0x7100c500e40a4200242041c1aa41d041c0d40d0080c80328a001c0480b130160300110f00c44402c411041c0225140040a02c4016228681d142d8010320080f615005049101507641c00080f252414000c6501c007680b0001a0b403500f11024030000110903c1485840e0b004009101e12281c40a000140005d4000030a801a0081d01c240a40c0581d514813104026420ac82c03200d0b0340141c0101c984040c001508c0b0381503455055080881c1404294103ca903400607650b140340407000c5070002880700c18401081ca005505107904400e00e00c01d0350082d41003000041c0d0740d000d80d040c0101056000500a04851030a405454080c080a00000c0c0c1b03417026142d0103500c96804204913004016410001002c4030b00c6801243d0300950003500c01c130b24040c1400d07070920340e07110022003040d0503202d0840c00c614a4501000200f008004010b5000a0201c80314204810360001118200349940880030060225100e02c084420480c0125450460446900100034500d101a48414060b0740b80802440c0c01141c600c0007203120300c1c021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 849087113 1250 849085863 849085873
    0x50d060b0301060903150e06071d0103091e052d1908090d020414040c05040b0108060f040c0c0c0b0406110d0801050405070507020d210504030b06221805 67
    0x180d400c1141901091189500184c10101d04001080b81e00c0c0820503201c0f05840081034012045d540140380003070698400000400381070300d85804840c02d60005200700703400d2170107021642076074840313100c4019008148112004000042c0040280410840c5e11800c1d8507900a113440700030800c043c901100000c51078200d0b00038100c0041a0252409140c0340003076100e020203080014000a00c0343d02c1c0701c0d03140100c0c1c120381d48091543c04407480280c4c00e4031031403148007903540940c100001e010076250640001340c148840c81080c040c00d5615030512444510040d14001441c004030030044802290445010b00320861070a0085201450f81c0000e0040d503d45850366015900f801e40c140340d845801081070400120244018440ba1610b50022500104680307030190610006030002a290100940212008285800480341d4270408600c0001e10113158100075003410301c1c40c0c45c0c0c0c51100e000108018403031250549032020840500e0085d0303600703051990b0200038800045903155100c80c1e03c0441622a4840d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 849088363 1250 849087113 849087119
    0x90f05130b090c03071e062610080102031003021c0317040501140f0708010b04180b150d02130b16030516061d061810090204060803120a140103080f0703090305010c050d06 75
    0x142c0541114015000e030305010ba071340041c25000f0b0323601c4080e00c41c00c0c9120001e940054800c40074000381d4001e920390100d1600a500d1407040100b0138509005000b094096945106d01090700690680022804002c003810556618500075004107d42a0f00200030381d210002c1c801141185411684208140c0e212500d25903204d5030340d00c042d4003a03485811000443c0c10401c60a40b502d9402103000f5410140480d203000d8085482c400b05500034141c0c0d441a940e022a0303144240052000310030050440303422061410f43d058035100399111003c20080d05200001800000342030250008075401070300311508001c84603d402d2202c10206400302580300c94070403400440c803c600b0031100d140e0b010110000810030349441040d800050840e00c54203130392180d6a00e00c0010a400c0a000a0007000080c0e041c5d80302074608910344c2c030708451100001c00180700c08a001407000802542c00c89186d40244441240c50b85414501120381b041e003a04020400c0d400c0840c501c4149400201070310072004640c0e000d002c01c5423 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 849089613 1250 849088363 849088367
    0x305041805040f082101060c031e1b0516090203190b0604090c090f1502070807030c0b0904020d0f230609070c0302120c07090f05130b090c03071e06 65
    0x740544000c0d2082d408400711100180d0480e000f0180c411000c8990804948507005070240c11400340e00c00000303c2d082082d05010140e20480d1000e50f5003114140382e6209611100040400c0c0650351902d44d030000181c21f00c01481810805801d921002191824a039904c9207081400b0350000d840b610321401d040d6408d21050790960103036944140380586900d08151801e03020201410341218503a0074000c1c07030340000c1b07005180c42040c400a00140d550b50030003411811002450440c003540b01d00540c2c1c011000900000d400c3d4202c40040340c000e15a110b40f581c0168000500034801c015120041900d403240618945050b5008111900045403010180340d4000e60040e142800c100c0e0f180b503104c6800c00006242c50f00920310b42054500920455030405d00c84452030080f584007070801d081c103910646080240e4243c2c0c1c05040944e00781d000e414003c5090a0503d0110140c02e5400200140344510008081d40c0c810010994420001811074402030fa0304c0d910b15152a040d5682104c242c9a11400411564 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 849090863 1250 849089613 849089621
    0xc1505190503040b0a02030c07080c1b19090c0e031606120e070302130908030708060a0b0705190510060e1b0405010206070c020d0215130f050f040218030a03050418 72
    0x260880446515645d0714004803009500c02400350410769400c1c0561000715144101a0000018502c010042005542d9400a01c603010b5400240310b00c65401c1c20140b200d0b408280d640031580e1081c0089460161801c0036211600850100d903014480d03039a0003c18072402c07250301c10850300c46888100004240024540c2a104c10784510f100c5a409a50708000504100511100000c5850000244600c050384c03180c4140d4810307500700c00014100402d008151510003485001040f1880340c00c3c2c6040c41c260340b0141c44085445a17039981000002001c02404024013424a40680c0303628104062a00e885001030f1070f103c2608c1048480f03500440d103e00d00d01c2c412003200c0c02d03684143c004080700c0d510f000003103c00120800c41240c1210f2100035480041e103501d00c11001410006081d01d441d01e1448008104000065000c8408801c8220082140e600d0360401ca11b089001500d0251b80d901e16914501c00350803106940c0d5400d441015828400d1513488000f42080d03400c20014034480402c81415101a0b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 849092113 1250 849090863 849090871
    0x818011104030b150603090d02070b160b060d05010c030e01060801060509010b1309090c09050a0b01200a0b2503050402011218020a090c03140f0402010c0c1505190503 73
    0xc0c000030403091000c29074054440e64020116500700d05038800c001d01040701504240c889030400e078013480e02054125010300411000d801d00c0c24006003020501c104035001420004405000884a14049400c5444618501c50742c1901b00d002131054420b031490090007000301e2410304905501c0c2c00381c08561494180505c0c0d045580040c1940302a03400d00c0001c00300c650000c0c04c03040c1c841916240c0003509407441d00682d4205d80c00b90306004c0c0c155141801d06001e4400007407900c1c4c1100c3c549141c00c0c25a03038001c20108112a5110320035103403810104003d9103440c9003c0d0340680382c05004010460800014540c820603220010a455000c0c4031400c8154151081520000d01007200811203c041041c185d0054940e55510402c08240342d0880c0c0110f07480c6103031038000510440e00c0744140124950513001e20f40140140302c080311a140340041e1411000c400c0500000e0400801010300c000303001020000c20064070038502e00403106101041c0c060300d150300c0708098020220f0745d080341c00b240301e0260082c0c070700c0707 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 849093363 1250 849092113 849092141
    0x70504060b1201090b0d0c080c13090b0c0318062508010807062f01091412091314070906090906080303040f15060f030c05100f0e0a050d03081801 64
    0x4a03400c2000d06805041960345d0740760440c0080904c0c1000c18440e681d0345000704019405070070b1004400017032002d480c4225400703000103420b00703160f940003c0d0a10b9190f5400b02c41001103540301d8641000404002914904405061140b841401034140194200d180d040e8940c5001c144240a000d40a507224002403050001a03084402c04104090140480f00c0c10107080270070f8807107050359010115150300b14544a0700c445a40d140b0148040021001d00c007509440288024a180d0101c400e40c441c151044494050003005416031000f0700902a0b0808120803107680c0358174840d0320b0194001400b4441c41c3c4109000103000081c0003510704928451103087d1207100026618555035522080342c0300045440844065001c40a0880d04101074802c80002d0940711200c07458452030350408a0b03110560740c1209103d046154892072006800c181300082c1d19007542040d803030b40d08900c4005100421039501450708810740040c50800c269020484c244900a04183c0340c0146e901c0700c1400f0300301c403003804500320 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 849094613 1250 849093363 849093397
    0xb0405070c110f12030c0d021603080708070b090f06161407031416021201020a08061e041109100207030c060c0c0911070302070e060d060207021f02070504060b 70
    0x8124039554600d0035003000361900141c0140000070a00c07420302c0b0043c43c06280c00100312050780c00c03420711140280070b0b8030341b000701001d0300c1010501e242009c061000500b10b2500089070030803c03100c40166090160030018201c001d01c0d02c280c003180c54020200e1000d205014107800039000c1945650003002020459880c03070303080219070310787c500309501c01b540980601030b400c40d600e12440031a60003171401c43d210800c01038003260184180320f03d000c0c00707104d00100d0b64014810301c07041170390100d0502d80c000b4003103450908801c80f20007a0240241c4036103985800504000c010001030401c000102081c1c0000d840001401c58186412078507a84240001400240b111a041000f10b119828480107030740075041c2d10b07059641e158841c600b125a21000180ca551000c10380a082c0354040c00078200402e0380003140c042c41d04d80200091034a0a40e000020071a69001c01c8040c00c0d500c40c44810600c1c0700400d404176a8815540c08003943d1813210740300c0c851085040020100307505014a003500c511a2180070422 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 849095863 1250 849094613 849094637
    0x2120c030103170a11100c02120c03090d1a0c030f060d02010207141215070207080313090207110618090c040e0f1e04060510050109080a06092301020c010b040507 71
    0x381c9a621210006080003480c0402203400c517402e10415000015485000480c042c0076003001e410042c1c1101001f00c004401e00c110b0b505c982c008011560005021110748001030030038903110717064142c0070001c00c0c600e031105010003802400307034001180580c0c96095100c1595480030f0070001800720500b0b000b40140c010640422044c0618104202c0000c002130000446421040d0303011310340f100002c42410002807d40c28891039075010310045026081d498050b503e06110122003114072500c0388505100d0ba5800204a07090040041c3e40140540000788044d0360360141c03039512906d04e500a00054801c0642801081881d204101203808803820b044811540e507407442c450780960740b0000d101c8144000440d041035040080d10124504c11445a9400621418844aa03401c014055000b131414000310400034000181c0004090444580c030000104941a140c58140c0704905c245070615440f19042c040c8d0460048190041c0807034880d1640200b014960380340400003900c100383c0d503080220b07001c2d0800d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 849097113 1250 849095863 849095903
    0x30c070f053f0307050102040e0f0412180b0d020c070f060e12030409050c0a0806040c0e12070f0b1b0a021f0c0b0f040b0708060604140d0501020d02120c030103 70
    0x20392082080898a041402c0051107150550348180c90441c0c0b6a5400034041c46801202c081c4950080d141c8224001e0310f1034940d85540d0100d51000d0400240581050b4180e14400103212000281c11100300058483d0000d054020103034100707201c402c41764001d407a03010820319880c4a01d00e013104c4560303580e02111500401403010b20850808003036000d020801001c1032074001c40c003515004042841c0382d160303a80c9040c54018803c01000e030060703125505107107185a12690040034007140442c200d03000e00f2045a151130b100d01e02185030340a0300d2031140c20140003a24807002070240c8110711254061148484940c620b45444440450009621280b00080d45800c0d039840b043c800c008003003a04120b00459041c3d203c1d20b511001c02c89500784102110003c01c010400050312058105035a41042840f50074540000b0340640600d0080c1600001b20390b01d203000e00c0da9000308a154080d0418000c5564407280d8844001030340c040408034103010300250215000d071980404581c1266000034200c003003001c4034001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 849098363 1250 849097113 849097189
    0xf1a070e010f030b04060e100b0406020d080c1e03060a27020a05120103060f0b04050f150103090b01080a0314250f1e02090601110c0f060c030c070f05 66
    0x10b030504165448680200300d031174600c1401c02410040d060052240340000c0e840103402916040aa1032860a2101b0450650000b0b510440c080603810030f9000c81e542e54903004040e0003914990908501ca01c40900b80c1d6805001c01107000f01c109460404104d510342d000011950224410034800034000c82030146041c0041e1301606403c02d41d854818604201041d1000500100ba002582d04650300c1c8900d1820754a584540c001540098030240b02c00c2c5010041200d480030001c203090007074032030380d00b864038030740e100b03501803102a64800c481c03251550319603040039500c1541c0c200440100390f400e83e0342482d21540030203640c1180da00680c8220a82c100342c3d2590501d051020085910305401441c20000488803c4503560f07802002241c4110900c02c1d0040000c60140034058034181f050001d4201c031a5040491080740600069a1000440908101082103803155182d02c5819020100b03181040c0e82000c80e0907002c0307860500603900c0700b5845004100a404200341c4007031480510302680914854080d41d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 849099613 1250 849098363 849098387
    0xa080702040e06090102030915010608180708030408030d05070804020604150201060504020d0f06050613030803040c1d100812190c1221090f140c06070f1a070e01 71
    0x1c004210600c402030344a00c0e1040903184411907035008010045559020040c600501070342418030451949060070191541502615010301300c89400102c001000003001802d0062020600312969541d58042440e201e410044024120506050101c0c1040303100342c0f0414004c50f0000e100601d05894041aa0b445818089000c000d55486800c0002c01d43d80e14406800c514082d81008603900c0c0103040c6a030708464040e00003c7c81401d052240112100004020f403041d40c0d4010045035807500c403401c005c030046216600002e06030060100040c40c1102c0c0441480c002c0c04041c404452043e00c5d2a0400d4841d4400d54056000d02c030244003000740349050140c03e0600c041c4a05180300e13400c40740e0715000d1f62031221440d4070010424460720038801c52003040000511585014040145110707603664207034400d0400070058410010400390200d00501071101c0005000010240d981e20310a928010102d428144000e0f06d4950180102482504080c0d20182c490503c65803030000010301c00c030065805540200e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 849100719 1106 849099613 849099619
    0x6060905190e060f0d060c09051c080703050711030706020115050108160f051b0604021c0201090509190501030c080d020f070b1b0a0b01080d110a080702 67
    0x359200740c204a0031124902c1410081c1300041c3c40600708240070302481d2800c01f0441c0f420750803100885c2240c100340c903000700c42118010f8142800c02486c4024041c0541040200300292080d070042c00360a00c951112580301925501092500c0c210760092805070399141c0b1621300d41d000c4900720f01c00a0400b487c11240c00d10b030100d41c056017001d004001405004401c14245000c82c0200143c5001e041070303864400d4008904184556940020b42e010703030196080035601401044490718100e105501070b103c1c00310072450034007401400c1c8401010a0305048401c4a0440c01c000a40034042c002c41c020051b40807480e0811003810300740700300241c4000a40d40300100c04c48005030003284410440314040001500e1701580300d0889002c03030301d40c0c2980b10b650041c55260001c121034620224141e40e182c508680498206040607039200340000b04080c8240d1058128000151000c0003c00e41c4902c05 = true := by decide +kernel

theorem cover : BRFrame.Cov 848920863 849100719 := by
  have h0 := BRFrame.cov_init 848920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 848920863 ≤ n) (h2 : n < 849100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
