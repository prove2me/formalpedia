-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2258
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:09:48.645253+00:00
-- url     : https://prove2.me/submissions/8ec484cf-94ea-489b-822e-889f01f41cdb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 405935251 ≤ n < 406115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 405936501 1250 405935251 405935267
    0x4060504060507140d1104080d05040810090c0927080d0b01030204033f020c0a08010b0d03110f03160618050606102706090501021908030915130201 65
    0x8040c3c0381c1079105035000300d04e000ca01c0c41002e0b10408026220103102c0314480b0f40008880081540000f1a1008040c2c4c02000e45140c000f0721900380f190188918880d24482180180889168840c00da1101c00c0e0804813588024031040e0204440688845a031086044414140c002041d00888500d43c450f13052040c00002c1d2041600403070704060050008000207001403c51410100380642d12a0f0181807000e000c0c0c00342030310851120031030096202101c44658022811540151081d181c0140031600c9042617070a032550f07007070207540102900c0642408a80f14030041e1000c000c4040584010b184809115440e540201107100c03401c2061005175410444603102d1044046501c40c40d10140700ca0030b45800d900c920b00200550700a20700c4803d0280094861341604208030401e950315100840d280c1590341c5100141d02400000c117800c0301012910b0760000850301369403070204416101e02032032680c401015800140c8007412901c075907150039070750031002580795115043c003408141d0907150500006000c86 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 405937751 1250 405936501 405936511
    0x1050306100305150601020a0f0c05030c04113415140606070f1e14010630060e0601170d0c030f080403020a0c08031b010b0102151905040605040605 65
    0xc101c0346001c000144000c40c41c0071080c00c580000d10426034883c0c00507130800d0300301e00c0001d10140105000c4000c020030001220141c07242502280d031082882c200740001c85a805040307000e922424000d64003001321540c114142803070780004400e5500075100b1950b00c180020501110f107480c140710032605402083c407903031000c00c03a403092252150800c1404144103101d03500c030150000c401090303010f00748200c610b864480c030180c6450b0b5148002440c10186060780328003a81ea1215400d28030000348242c200440c0c0c50308520200501034007038a0f00c00b0300031900c48c5503440407035403e07445540d10758089506000143c000e02070a00340e06642d401c000d041d0340c1008850302894050181000c81c036000b1950013500c44622403070504003061242c5650900341d141c4612043d0040142c00b030140c011449100220181c80380d8003200d017400103413400e410b00346402d0701c1c200b0034101d0050380441c00e00156541d0321100d5a4000d00c44a00c0307101000e103100c4bc00e0069400440702500c403952038005002c1000818403405500c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 405939001 1250 405937751 405937771
    0x60f0918030905060d0b090a06031b0302030606011209060e0304170d08060111031b01020c010606021506210a0f021c0b010302120114092104030308040b0a18050601050306 75
    0x11207954050501e01c894001c5a00840c004512080d0101d02944401e0f24107200a015020700d1803c5120603000d0201030000322034580c020140701001111102c041406d40382d008020304610741d550001126901f020601c3c4803200c50f280c0d847c05000c10828402d048209400e10051542c441c108070100b0403810271b20820b03200c158081c80141001907813000600d07400180918018100d401a400355a00d94025008401008401c10802c01b5694105600400700349003d04001d110303543da928416170b00c500040c1011507848000c0b0b03002130820b14188004000e00e501c0c000e00c41d159419040724003807910505038005c4402140081d107020035490f14801c00180003805a854200b904003988e1042e04c4d491040c40000e000d45e00c0751003140300344c450a41000d01c200260604030301c4680f4100b6041380c4c1d14601182c3c00007800c906000d0142804403554116001e407605519a198079032074a6603002100c00c0024031a400c00303030741d03540d0041001960010040c09a406000189629410a400c15041100180100181c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 405940251 1250 405939001 405939041
    0xe0402090907350102191d010503010311010302121612110a140f07060b0a05030c03120702010314090a11030105270123090607020d080105190504060f09 67
    0x7050320039a5000250110405480300000300101402c00c218480c0f2010700d0a0354000304210134483c000041c80c0403010019959551540413a01507104083d8409000c0c40c0001d100300014400300b40601c0d45000192010f14005140a10302a6a180212015941881034018003040040c1e600d9000e54030242d0300080c0401000340181d403c00490300b0b4802c105030700087c0b08a070f0080c00d0002e0120760664907038800030400d440d66900103180800040c0706141c0d40c00e200d607440a0010405040004603807100000c040c00800c007542a624010b94582c1040f0422170415440345049404903c0c030100341c038000c41d400030040960721480e243c6180200903038002540660702d40800c024030340c50b0110b64000ca03140019010070f031001c86841d6090140451100005018041d04203503002d030201c00d91058414610401038982580705c0100880c0c5505100840c1e000280c01403005209516000e00900d41071510f60b41907840d016a9000420151451981b244481169030001003000750128022880050808084141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 405941501 1250 405940251 405940259
    0x608070f05090a0e0702120408030a181511030408030a0503191104050105180a06020d02070605030103020a031e0b0a0b030f0a0b0c0901091208090a061805130f060e0402090907 77
    0x24103c582c8981034400e070440300400c14250007840720240700c4222070070a643d205c0d240c5d089513a69500000e0240300090400e8007900351046111403120544038000703100b8200550700c66003190314103031585c0c0c0c42040e400b0400c0001510901080280f0000c000d0340c0702c041c2c403443d0224480380c40c440b03164a00e070310060400c402c2d00400e4213070b0401c032010f98109003000c0d9154590004080b8507826250100d540108502c100800d1140d0002050781450101d42e003201d22080d06d5900c110340a0100f17100083d00301070000024400140303ca00050b15030b10703d9a050b074800001c5611241c01e0410203840c2c1c006c01175501c0c520a42c0504090007808002d440c6000281052066550784480e4071000070990251150b010540d1510750384070344055402030136079448554982c1041d00302809640c1c85002c03164424401684d00041d2640aa00f10480c603490480c040d041c030600e4007040c096403804410b1140000e40d0340b03540c0ca40c000e0441e0311820002c0c10301c14102c0303000fa10782481030140030302c8003402d60311903030380030a600700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 405942751 1250 405941501 405941509
    0x10303121103041a0a020918042604090b0f06030f04020a050a12061d0d0f081302130e011d100605010206040c17031b1507030606170408040f0608070f0509 68
    0x20713603600e11241d1080071561350503a9000007070180314100e5038045005000e480f041c0c0300caa04100c2c044c9002d05204422401611000720311854000d00c5160221010310082010260a500400f0b02450280c59440f401140c50001141580101c44103140b03039610380c0c20320003581441c01d5801301410050300c04030341c094107242d01c00140144541c401402c0c1610f07204503880894007960382000d4006c056044910b01000d803080900241107005003c6c0004140c0c4000890440351000c0450300550040c01c142000120700002e48040e00c414103401400b5034030381c3c7c650b2800310440c4030b071104020400000f41c0740c55048203000c0001d668965100700d04560081c003d220120300200b034480120741d101c07000c01041c22040b4a43e1401c41c014041500c44410382c0240c8580344060100d8403103d60740e01c2c044c80b0380503035548580c143c0491b550b40c040e2400107070204142c1c500c0c01e15110180e98101307029450b40d604080d0380e010010300c0000541c000f080011448418841015006a5115908006400d00c1d50400d001c13003000c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 405944001 1250 405942751 405942773
    0xc020708010e07180b0916030c140909040629040605040204051f0924020c0a0605031f0306020c0a0c0605032a07050607020106051008010f15050f0301030312110304 72
    0x40e24104901540071100c6510340c0b10a02191700644203c1643c640b80d240c1d01001426031110101007804d045407038107114464000302c2c0d000f0304808421070514810b5000d005603d42c0040041b20240d65544d15403c1c0d003c91101c034032244083c00501c080c0d40c0c030840c00130f10058901070760003030b0b0140d8018802844242e03210410607015030080d490b02c5c0f0140c4843d140807541d10b07880d5031103100c0d845690a40c03c0e241c0b0f4034a00c0200c0500f19190211840c0344411004d04c6621030080c850840000c80a0000c600c0c001c011500172040000c0c21a6074000080e141d48400d8201d90140c2e401c059181d00000c40041004036400900c0020031301414000e05600c0c10003c2c1101440204007120070001c1710042c54480010400151590280c019084a06624046001070300800043c001d0b64801d00484c000710204034441c2c12080c0c16500082c0c81c0c0c0c2a020714207500c1101001d802c1c907a28041c408188507005066030002d0280d0300842c00303551203e1f01d000003e1041ea003240c02c80b080f030705c295007402c10400001c12404064 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 405945251 1250 405944001 405944009
    0x30d0e0304080f150c1e1c1b0f1209140102070506130302030f030a110c010605030106090c0203180a0e1501092309060f061605060901090308040b1009020d0c020708010e07 75
    0x950740d407051404940c4003000341b0016140360690104411031100744122414401c110450f408202e18210040307420b2140c000c1310b004000142d16a2003210b00c040c0700b000b4541411910706808034540c0d640d0340c0c1c1d200c03036482c0c00b01000f8541e031340c0403c084c414413508020550b048500c0105580900c2d50986000791a0301c20741001c0c060199000000c104007400741d9104401ea0841800000c2d1520701c00c00b100c0f4041c2c00c6c1881481d03c01c0d03082207408202075070a8411040b0315411030b0010340c504107c00c0d0418040700c0d10701c04180e03400b0008050016400307041344c608a00c11070400342c04085078a00680058012112a004601e0441080c101581900d1000c00d000511000031956010156689400120346484450300150000c45c041180106401003d805a40c564840c42c1a2005503883c000e02034221502000f028000502d0300011070040340c020500280c01c20140c400451600e5210454013050780e00403460200071079542c00400d4101c039810300008002e040000000d202041c09085429524412401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 405946501 1250 405945251 405945271
    0x912030528030e010e0c0f0d020a0504050f09160f090b04061e030c0b07230c030703110108060307150e0406050a03030503010e090a05120705030d0e0304080f15 70
    0x15445148040e48000e00881c0d004048464405900181e0050140a18844560f1150b00745819407101e01c10220301c07000da0b1400500b00c1214211417200300000e0003124501a80c000000050114203900c41e80a010300c03a95003a5901c0303e03207003041901c052800e41080c42c4181110601e16090000304a48034075581181c00406c404511464000000340c020101c0764819420481000b01101440c40543c0f5440100e81c0039641080e031880d03030358110b00312601c034244000f00100b404540c4071010081800c501405002c88408840454841d000440d10f840119041544d00004184048090f90b0f80007504991112050300031b00000c81c0340c068140c80f2110141c0d556028000004040301141c0c580c1d5010500401005203561010b950ba42005040d5500a000d801e940940d65000a801d00b0360000c0c1c0c07901c106078400002c000d035001c55002c030b600701d0700031940803074990204000205c039042c0c160082c0c4040c2100e40010311b540e0fa2400c03c0e15481d1100b01d2141001a4011400d001c94441c1c018000b1540441d00c09 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 405947751 1250 405946501 405946507
    0x40c0b090303030c031e0a0c02010b0102060c0d020c1509030711012c010210020d0c110a05060402010f030b0306100e090d090e1305030d0b210c12011d010e01050709120305 75
    0x50f0030581d1110000a044041504410801804100d55042034050780b5030f40d000bc1101400541c0121384448084500500c2150208840d10003112a0b60081c4000004402613a4205101c2c8144c29140b840540302d04906030310101700b81c0c0c1480359000b150f0003050401d080c40c3c500040001c8070400200c19280c6800700302c1c507103c403144555900900c5124080513042d47e0455032200004503c1d00144401d403c020000764600d00061401c0c5400134000310b007a6000002030040d980e03203600440300750100c8840b80301055190041002d03140c400f000038a00501552010000303041c20b1143d5400c032a0700c0107160028030b9021500000c40190000c65100544800b0060b8803110b42d5400c1c1c600182d4841120300402070301c0000303400c11004a00d0f0303104849001d0115200e41500c400b0b00444409105500d14010482e0050f81d480c030800d1504400c00103c4045030310010070440341100064a05000904a210b096510740c16000382c02c26081c41019440395a03070600e001d61a041c0134502e21300100744040142402000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 405949001 1250 405947751 405947761
    0x4060b0f0301090c03060507050405011211160f0203011505240c071d06040606050406050d14010f0518010b0702010804080909040c170c0919090b0a05040c0b090303030c03 75
    0x8032008020035000e4003d12a90040d440d055018403501d02c03080d18054548004594064403900c211012904141d540e000e0710790321300d1410310090803000300c4101910010803650b0007288a20b082c04000501a00c0e01412a1030240185400d403a0b8a9205010100300d6000500030355850742c029245041c00c2112910110b800b43e1505081849540340c0020288111803000581c9680e0394541150503100340c4210b103598640e00f06100c2a20f525008000214030240014003c1521901c0607000f104c00143c40400d40f49100c1400206404080e0400c640e02d00b8200802d02442c102004000c120000311207100b04103600d0010408c40b03d00032154002e040049140c0072806000e106816501c40900040280034141420702d41b4200c46100d88c070400c0413041222181152200000c6412055030b00003501c903c00700d40d00c54007103030526940d08a02400182d903450180d004a00500141031250883c041c0004941c186404c0043d035803134036a0300003600c0240410020396142c0b0044103481c0c00801100c080e50300da0300c3e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 405950251 1250 405949001 405949009
    0x705072a06051e030405010207020312030f0f0c130e060f06090913080d020d020a030c02010504020d2a0b180a030c091e0c080604060801060e010312020f0313050a0608040b04060b 78
    0xc3c0300c90a10014040244801d1080c19802000114400c40860b060b60a4004101c60180002c640d0b00c801046150001a01e50188610055004118508046c03500c11902440003290501da04100801505003040081a046c444510681031030111072140c249042e03440029015a00100b01c0701c2c102c0c80400c8444100040340b03083d00c003091b901d88015916411903d40c988000c6d00f2010450b00001d0602d160341204a0041c0b040034083c68000d46188901d4086889025a4092696495602c2d00c824124241080700a1000d40054011820010f9641100049041e000442c1e888468800c0b6500142080041c01403020710301141c251000100b02da0303001c5110b69142d003020301304220345c1034244a0b03c1902103500c600343c40e2203900101c400708455511940c04074203c404601400c4150501d50005102090824044600044452040700c20540d1001d800608640000039002d20350301d501c0d1824070803848c1641c0014040c00b8285000101c80c5400e4039980b5080e17030302920207012207a0381c2c0307092801d58403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 405951501 1250 405950251 405950287
    0x10807051315030908120a0c08060d021020072d0e09011407020a1b050d02011b020a03050a1202030a0813020d05010501290304020303220e0705072a0605 67
    0xa00030f0102c82d00c0b40b001800e8050301b00350890300264402d01d0700004d014028040c0720b00358041c140c01741100b40003003059400e20210101d90300040043c80740407030601040d66482c0e0480b041080d4200d000d03210f05071030045186600e071000c529000700090344000818102050304030300390445a02c145080c01c2034a4080300580100350b11500d0890b80746810003000070030f50700042d055140c10f11565000100c02c150782c02007148210a40107091348619110350100143d0300c070b440301d42101040b190000c00090040c0d07000030601c0040358070854058110200c100240b108130762402c810340d1f4075400594582441e0820081115000400111901e030002110b2130642d00d602c841320400d1540540200482d50312800700701c982090031400011821704044281c0098400e0006481c041e80d40500114205050b440700c1c0c0118204041c0c0c1e00c40801107014000a0500c0324407500f500a404a89810741e44680720304220440800c004010790760300098640100462408440c0b0030112206031400b9078444a00d003203180401c1d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 405952751 1250 405951501 405951503
    0x8030708072a0e01050306060a1503022503021e030922140702060118480309030e0409020d15020d020d061d0c04050d0c080d0305060108070513150309 66
    0x2c040c112000c5442c0038250f5003541a2001103048030a595940400c200140805005c0c0402c800700081035a81c001e80641c020f403443d500580d60000041102c0345420301c80080c1000d056005038000b0840342c064100c50100b07031020803080c20103140740c0000440428100c483c0031030310469601c040d0f900901c244050b58002c0c4141c0e6035800c9003d89900300202c0007541c41000780107100180505109003155140540708a110301c80301004900500b02001002c0701549165901c210504040c40f158000d040e408641342c07070308c0080181c40c00144804031b414010641050006583c0c01207280800010269603608010100706038040c46010300901181042400707800b030865840883d0f400420701001020564101c0015620800000714100d07803c41084610300e0301c01d6401000c000c07004c0205001c0c0e0704040c0c03800181e41d40070700c1b15a9030b91591003040502d8480c160042c8000a40c0c0c50091262075039224a05030303041174652411504142c01c003032000209007450b10410b44a900f41d507012041d500d00a403c040486 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 405954001 1250 405952751 405952823
    0xc140607140609060105030304080c06070f1205120c0301080a060507020c03071410020c01050316020c06160209100515070203071706070305060904120507020f1c020108010803070807 80
    0x40072441c030071140e40d007005483d60308080c041c100001c83c60382400415a812211854001d03c0c200f2581824004150322003207064984c04a962107038000b281c1c061118010021603652002d9451082c0c003440b0803645e0700070740410143c980820040007504070000d00e00d903255800400006080d1610fa406918003015514283e0301401440e030b00007002c0c01002e006441c405000e56401085403c0e101040362522894040ca0b400705805102181008005449041c0c8150060040320b4a111184000400540007038131a200a00b04c0c4510103c00c50524a040a0304081313611584003116007440000340707111191b2440041000d0000c50080c055640170001c110017400c032708001c209902c0702c00b00d0407500c07000700700d603407501103810000031036a20304100e64400d00c0b554200c0284110070141c200100c8444e8800101a41e002183c46442c0c0e0842d40c484d000045045060f88402c4501d075201d1001400741d04d03050303010340441e41051091310702040c0400c080340c074110303449150441c542074111426480c0d01c00b50a120052 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 405955251 1250 405954001 405954023
    0xa09060c02071802040e070f02150124080712020f1b0a050d0207050102150a020909011e050303040e0c0703050c01091b140a0303050c070b0d060f120c140607 69
    0xd26401241c890700f034071041c2540703001280c6044200000e920692003078803005400c403c0010388503031080c0d80f800410384079441683c0c08066191454140c3d46001c0e0004464560240200c446d880107106e000d0a1034801801d20b00507914111801411481c401001890f000d50000360140c4055180b8089803040041c45110b403c02007504003616a842066a82c1111244201d98000003003500009203001101c00590081c190705c0b20101c0b0f1031b0420702000e89102030f000d40a0014080650360060114080d007038409a075540c03602c9410291030300b0032903603001c04c0c0a5081003006000840c2450020741d030089074522150b40c3c4850307501d41280c3c14030a16030150865440c0240c0721b000c20401d03c2c106400000c1112076400b1164440404c0341c0c0000d410703200c080c1d0122890702c040000a001d0b6001d0044803055905440c09556a40c00403109640702070420103102c0d54441c0140302d10b000070300e0880c0c040c1801e07800b0a020080d50740d440d10305540341e070700a48280c55409694030310300d5600d05044580c142d5015603900c603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 405956501 1250 405955251 405955271
    0x5030a15050703230f06030a0b13030302040302041d1c09030204091b03030e04050f010608060f0f0a0b0319020a020a0b090a150902100e0a030605090c0405390a080a0906 74
    0x5034500c000d681070442194000081b444500d00040d0101d20103800a0403200252580c04c0e0140c0c4012007c1821000c0c580c00380000005640c484c0324000b541c00210030071042080303501c8115410140c10880031200050a1800c04240c9a4001010b40c10f4030b90589001a04022074100a41103803d80d046d59607115044c000d0201c09c0580c4100c0c440c40740e420a8034284115280c10004080880c000d01a910014a4810001d84e9610b00745010801d141e1001c1c109140e8401110080340345420700780c20008426100105000904000040c80c080c2042c44407001c40c2031210f4024025114100303003102a22440403030f408650041001e0000004155020350042500702d408204000504090700c001e030b101c1c514610240c203810303000d0030340501c00b010002c0032196002d0460707803403600610340030701409454840c000444d46a900d652050b0b0b8000c41c801c6c41160054412080014104010380e040d840c120440040c07404030451090040d01c0c01e6601a0400f00013655510920000410a144000c0c014038100f051200c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 405957751 1250 405956501 405956561
    0x40f0609062606041808030c070c050d0f0308100801090f03020606090c0f0d06051314011202031b01030f0c03051f08030901050f0c06010e010e0105030a15050703 71
    0x400700c0e021a1514a80c000e03040c5250300842000c4103080c0101c070360101c0080d0042c41c0c241d11407014000d80064180040145e510380341410f400844945240f60700c0040c000c0140709100795024010001140d000d403400849948041c4418000d400050901c445040030401d26120b10020340003520051000700000d80702814201808024900c0980c00740c01401c0110f011410144182403141680b0311206207454041040610300341c2c401c2510802e400d5031840d002c03c2ea076075140381c1c07034140c00200d0402091220700444580070903407060303000748840c442881e135140041c0ca0100d40d002c0b00c3e24001d240505500740000041c0e0117449003440c44030b007061504003203404c025056442103028840c00c000e00b9030750088100403016803102c10300030040d1079803052020742a01e42c0f04c1d06c01007001700030b080c45050504d9a05d00310a403802000ba00802007c07038a5000620054807142034480c01040210010140d680c2140c40f211031130710820300b8249441d500e55000a411600a8000303440700c3c803d0000310040780f11f0411a007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 405959001 1250 405957751 405957767
    0x30c16030504090609290102151015090e04020d022101090330050c04030f08030402030d1409101e2f060705090406090e03030f06040c2003040f06 64
    0x4060310b02d0918007003046604c42c421422200d0789620011314042e2450706c00c144414416001c02d04611613441066081801d00031030b14010312000412440485c00d003588500110312016070740c020400384a1040117a03e640011054000d50182c9001c16034204074008900807e14451044007194428289000b81040541c400c00c4040e000359101c00c00c055041d240c4500444010005038114100d08000c0d21340c40321346070302c1035420501c002d14491030565a591451611a00c401090300c546038080104000d42c2014052003d40c00743031a10f400420510601881015802006481c0d4042d9040300b9290b1150b5024841c401d1014030301201100050151020091020711400c459110b02404400030380813080c0c02c0c040ca00c00300c65510300500040d40e1418002c852541107603403210360061b00c42100280030b034058454440746412002c00f46030780e8900781c050441c3c041405020a40240c2c540000101c0d000d50042001c812a1150f8204240d0391560108082c41c40c015604505015004100c00203801a001816 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 405960251 1250 405959001 405959009
    0x11b08060117011203050d0f060f0303080f010302090420042c0f0601150c0c0e0601031401080d1b0b07020c10030908030c0a050d05010f290f030c16030504 68
    0x100c0b00c01d54030021010071403040a100e011a807070003420240c40080d0050340549440c00100d140007038402000c035040d406485956004407000342d9454001d1040c950b02400060707109a41d07004000a80d4903540c00716030800c10041020b098035482a00e500c0d0072204014043d0700414009009202c0d030040d52034502521400401421421000360002401c00800807603018100b030b90100140469a190520503030904010200d12020840d460307040800060403450303000050644100c0b61969464100300243c02c44115903001038503500c00c130004010180c0001040c110780403062030008209030021901c00c0ba031001060380204681310350300070001d2490740001c0c905181c010440b480a0601031005050f000c403500c0d40005003000408200107841c072103517680204940305031858410300c5c0410312002c00b02100c5003078000501c021f55120080068401682c06640030f11a43c4584c54544191700b1080c00961140502004007140e0202c001000c80e00982c2c00d0391820510914607000308401460300411340e90281c05 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 405961501 1250 405960251 405960257
    0x70606030c090605030a0b0a02130b0408160e13020f01021207062c060a05040c0e09010608060901020901091a0705031303150209100c150f021b0c0d08030603011b080601 74
    0x30f00080c1a00e03001482d40000d5800105042032a101d108002020f984280440649191044d200148544001000f04001e003030740c402134a01070417032030075949a081081c0d001d8600101e00c24144100c1400c0307622841c1d84564100e80c840900000130700182c1c18145608244404400e01045034024011581c00c0b08840411001d007046000d1812994600e031071625004441003a8800000241c3c1003580350b0140b0303003190080c00c0c803114481d5128605000d00b402140c05450f0390b5144e880800c03001000300320b1180c0141040000790700301950800002c0198140c0d1046054960f06440c1241c02c9805c80e4044541260f0400309495480c3c1d011644542c1440c6244000c45401d402010103250341a110310981387d5145004142d10394006035a9411546150124400c1c1c940341c0012020b804104100c0c410152807889400c80541c43d03102c010492032820031840800c0d00c850300003408907074407503403101003c61410394014502e42c0c0740c2c1c86040c0407900400440ea00d0501d070f0307203091414a103020f03040075032580305620980e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 405962751 1250 405961501 405961511
    0x2040611100606050d050402030c090406240b12100902040314070605121503281e03081f09020a120b030d08010b180d0809010f1d0d08070606030c09 65
    0x46801c049441d9403040710000759061201005008480e04100e8200e030004007250b0210301100b00203140c4803400c0c0c130119100e03907981c4007001003c80344246a0580451000d0081140c40c44c0540409803440b03100d0b83d804461200e440051110510b8032030f101c010301185942151955268074103200515822940d0080520a5820014015101d00d085814144413200e5800072600c0d4040e10316a400f21000c0e2090b4136000303d4a840d007002d400e809500e2501d08003031195070742d00e00031400c154042100c00600e9070111080e00b80c810380442d401105650b041078410000030012041d402c03010810302c060750044a0b07040e00000325114196485400710100f03450751b4904022080440c001c05540f40d454503404030110301d41e0030042100c6044200540755071003076460009841007218001a84014145408503503540c008075000071306507031110380e10560070480d003814040543c12411001c0c90303401a140d468400c4060030a01000c1281840c00c2e81c080e2030388800709110090312440c2c00c0040002501501d0441d600d02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 405964001 1250 405962751 405962773
    0x905120c070b0c0c01080406291c05060105010c1b0b090114160633030302060f0403140a05040e0f090c1801050603100b0304050c0405060a03020f01031d0102040611 72
    0xa98121800f09150f2801044040f403410019034510b10001c0c425100d440da581e251240c42c0810070a40000d4200c0c4250706400003001408000e000c4405e0f2006545c01c01e400d4142100080000900b00d043da0000d01b0f0000b440b42035481d25032955149162090b02e00c04c0c507408001240410b0001610268400340c07900380c1141c0140860132900d020380d603003c000d03807508410300c0d0000c150180c0c00f0142c540107201e0f0912070102213503c1000c1c40c20131a0010351118140350010400c0c141c0c140300300c40c1c02c86001c101005060415840081050390001c000d80149000000d0380121a0b000b04c088600403c1c03c40031408140c9041c8a00103100b0342d04075441c103003a01402c0244519440c22480712040404068820400c84e402c0106100740b0f41c200804404001088440100782024404043d52140b03108200800141d81c802040c8001e9540241216001e140307102c3c0306200598030b243d8021401c003000c2c41c1c0010f0501c040001101000ea0784100000c540d44001000704441e54009480301e440700400044a03150b000d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 405965251 1250 405964001 405964019
    0x3140903031b1218130e060103170d1d100e07060e0d020418031d060409020c0a12020c19050109060f05040f060305060906010f080a09060905120c07 65
    0x901548540e0540080040240940ca822008410462030703508481540c08030400c00d110340d42c042409115501240c6404158a25248890000310600881e003449990300c0313100c0b02c90741e400060000070072620036803131090724420043c025504c610815404c00c1c401038044011004121140c0540400c0b24010f228106070891200d0140103101c41038035000707003c09480c0c03c40884240540e041615030040d816815a005a81c07180500b00e05100d510944929a0000780750140010508184105025041c0e5051684035a40d40c8107640441c0c10003000560764042182050b400c02841c410024080d000f02510346009d564009122039020000383ca00344400034607007104548a01c52031103024000f54204d80148003003031003244c01c0c241340c10050803d00d00f81f640714850240124003540104001030f41d250301f04030712880d24a45680d00041c0a00b04035942d0400094001c3c10b01100418951400c0d40311400c5001b00a21940030310ba15942000a407014542c907095407800a034082482519a441820804502800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 405966501 1250 405965251 405965257
    0x20a0807020a020603150d050a030e03070609080703020d1401050a05011e08071707090e0c0a29130305100209030f1f0908090d0f0201020f07050112021e0c0a0314 71
    0x50002c02d44c030b0842c0d84903505107003620800c00d00c25401c8407146181d400003403000c1281a05442c86900c0f201d00e480d6115050500c0c1c18819808071003003140041041080760000314041050341d03015505514120114180041d2030070401090790300f82d43c0380c01c04201030b080f0190b00132410785a0f02d42c100083d415801c6c0201c038005510b4000c2611740d8110301c8041001e14050107031416100d1205043c0d60709a5501c01811003101d4440c00550016004000c41e0b00c0246820007040014012040301c103004650540d968030804440400b03c070340e28490018034800c2a00400c208a0002c543c01070072903007001000710105000c0e401150355030780644111881e000b812803002c00c0710350610301811041200c40c075500c0b92510140001c2c07901910542d0b070800680060351143c042404e40f041c09018201c03000c1941c1e1000910703001c10b00070b030070301c9a400445e01400140c0e0700c60300321900611104d030096282d080803481e9034144500c0411500c070540b00015074480302000030448138111340c025250f0824040480d1904400d0344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 405967751 1250 405966501 405966503
    0x917030904093210020309100507090503010e0a111804062a0e1f09050112060815040b0c0301140613031506080f0708070608090a02040f020a0807020a 66
    0x141050001441500302540b00c9100c03240100000d01180c0f120495050308280c000c0d50071084816091480b410b80c440c200000900118913901c114039615202d803443d6110341c00d5092200556032940c020400e10f603c220405005088010000c109404a031582e0b6541e804003620219254080d00302e103074042d4600003960700300040c1d02c1e003800041030ba106d60f07c8030024150f141c81449401980f0343c85108a0034280d85004152805459100c5028030307001c2002440201d684000750b00c0345483d00d50707c1650741d010044504541007030a00005107158440d80801500e01d50304092860708c40c00b0403619030b020083c500075001e9230092075602c0c029150250465610b01c02400b440607103081c40c0b180d10106042640080441c0101075541508803a1240c0e21201c0848405c4086d0100b0741d100d407802d00001c0d809020108986a45800500c02d95140404880c0c0b40c1e0403a20640c1c041c0901c0c0f0303001401d00c000038880860190f80c000c20070081c81d0300707031681c210003504000404400981d0034400500304500000710798540d9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 405969001 1250 405967751 405967753
    0xf1908030613020708040b030f0a0b030c0f010201091406040c0801060b0a0e03010b04050108010c020d171314010c020120030615090307120819090b1207030e1501060917 74
    0x15558090074004841d51482e0700441080d4200715540105c0c12981c080c001400c0306c41004d540d02d0a202150020505014151612461411380341034001c0c2c0d4002880b00e0742c80816901340315919844001070b801072a14440c06801a01407852884005130045801407003140320b00500590b0940b03641c0e08500703c0d8054010240c14207810420061854001d40702c03800840c0004002081005040c3d001c1806d5172401e0740074503102d82d151110000d01940601c203103e4494000d142500106e01c2104241042c002d02030002041810303501038060620519800b221b041040001c000d00010351586002802400d802d031500d9030074994024100c81d0021490101c0c0e0241000a1000102d14844040c2d0007044d4003111002d0b0f4184240c050005036080e000c0720841007140654092071300e8050f510b000100f8143c11400a400f0040713403800c180900c40c412030680d502d404208140d0725203955131031010350041400e442290250321850004405d60344058080e14180c0700c4559030b20042e030f07580c0c490319144946803501005403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 405970251 1250 405969001 405969007
    0x17090d050310150c290c03091507020f07090e030d0b0109080703200609030a030320071b1502250f03050d020601080a03090302042301080f1908 63
    0x80e2140c0051a04200c8040009500c6540d8102180d0300e03404810042e400b007040e281c5158240045030070740504076441200c4c030341c606140051030350004c504010480300072640e0101c00324240407010080498401c2c2c600b6000c50880c02c02c20b10196449140c144440c0661041d0400030500b02c40314040c400c8008a0394005508040200700c1240140818065150400010320310005402c4004c210880080d806170711102810368020500406421400c0d41c13143c06801c0422090301142c0300080c25080c525003600c0d0020304c1000099180c0e0018500e282129540e440110758203041c4415241680402240d03100c00750602d40e076a143c001c1c9210041a1030a0142c0c01c454090340d00d660102d2450072500c3e84222003860229220b0004085c2451141c0007521941d008028151002e030301008103d001d0885a001050110b0345a5001848101c95000090280740c43d40a0100307441d01c0c01000111910901880d20300ba50307128880307140d4070510a983c40760b1070300c20b4460300381c0000c0034040c200e407046402020181c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 405971501 1250 405970251 405970273
    0x705100b0415330f090503010504030f081302040606110f0a03051603051c0204030b01080c0d14030d050403030b1516060b1201090507030c06080f070e030f070806071709 74
    0x110140b0041d2502920004075210140e06060500901e0303c1080c2c60b031240d04100003070480c0103044405981055009070f1414092001087e00b08e40000700b00d8140b880e0581032991003c0720102c00c0b001c141c00081d002410400080380d01500300440e01082001c0720125685540700109081d070341c080420300900480c4080104503c6080c400c1c1070344080c03d0080c01d060b072400034050344141460090300398141c0b00c039601040900c100140c480801c1d0041c400d5800070620b203c40c101c0081c41d00303540311000412714144a00c2d0020100380900c107550030821180f004011510b051300b405401782c0180d0401d00e10036a08141661041c00785401900c0d40f01e106404200d0a212490365800002e005e080c40943e0b10202c000080940c0075024011480c030903210b080030703081c0e5914520308030f103051000e030f0881c00603c600c00b03042140701074034403041c01c2d1301441a11308000540380c2500407030301344424102c0c55075003405a1080071a40490009480340100400d585181c6c0001d41d00905510100041e170f1240b000d9003003254203031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 405972751 1250 405971501 405971519
    0x909010c080c0a090f0b03061002030a050a0315051e0301060b0a050d0c09051215070f0c0f060b120a11031906053d050121050c0f0705100b0415 63
    0x2014040f50900141d000e4607601078845400c4a90300c00543e1041c000100301090030b150751080c010141d01c3c0011800e0149020000d0141d0042c00600401c1580e41c400c0d81000d5040d481420b4003c000c041c01c800300b5603030b44000504050b298880d00324041e40c20440b0008801d948070701245c5030350209507201400d207040100a034002c0c01210703640200304010240041610f48c1d400340c51318040f407143c80082c4100c9040b5610801c000704024204800e0001d035080003c241604152100d205990046100b600c80d0b00c14545040200b4426031401c0c1c1000c00401e1040f034690b400141003a659001d200ea884461a60604042d50785e1440e9403000840101407501000089142d00b02c20f800000c014480f110700c2d61106da40c000c02d01103104030750110b8620300006c080020110050000582400c3c601161407024881e6080d608100c40403880145a56a800080900b0a840c056031501e814400103030b595210f1504184c2ea55400000001803054500940c140c0e080c41c1500c070709002c000043c0843c4110a28040d018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 405974001 1250 405972751 405972757
    0x11202061308010606020307050607090f0314100f02091903030905150d020a03060e060f0a0605090f0409030903020a0f050d032105010f0602071e05090612010e010b0909010c080c 78
    0x1070001801011000300e4884401e00410014158030342c0150349800c80ca0a06602c1c080000c0c2c042010700c040f210043c445010300000803010b0b01d8001200d080c401c1143c001162130300d207034110f2060100f450300d520007940c203140360001c260101080700d8030003001c400d800c0e1308004030107144002000710340418400c200605140c9040c07502760440c0c044490910790b004882c08240e0b0302801081002903500c005c144550780304005020b4001c0d006441d2141c2e44038070707403001c07a000800b140611310900034080345d00c4100b030742c0340305050b80354150192003848010140c2ca000380045100e030204074441c24076443e000c5100500080d501e002c9402c0244461f0340120340b51410381c0e00b001001d0a0300d410300c00e500f00c0d03254a200140103a0740202417000e24104480c3c80c1000007418030055410030000ca04202c5822107420150480b0b02054900403a8005015110034001401040d01000501c2c182c0d400d14010003a80b40307041d4000c4202c1c40e02034840002c640d44502c01182240c0003004041d020660300004659400f0344400a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 405975251 1250 405974001 405974017
    0x60b0303130f0e01090c0807080a090c030b0a1b050702090a060b1912020a09260a0602131502060f18030c1e030306011d010309080a0210060e01120206 66
    0x64038035041d00e06a004200c000190080c2e0901468000d04000e02210082120300610600b10100f250302140704d402003e401740984488204920300c0040340d00d070201da03401024999400303002e11020690b00e00e07012801082c2210f0400c26030345498001c481d603500d101400710030400c40c1e03900c1a213042e041d5400c00c400003001608400390725968031808a00e41d082c20004068200b210540c1240380710380c1320002452542556003600c0364a006001550b03c040d00000f0090660704501400b8152036130340c8038540510014440014040d00c1100c4100c020300c00f0f95030003001c45100000510710700503150415507040c600900b01a02c01a0b2000000841c0400940030882c2c0180070503901042c214104507850303103142c00528841c0f1312030b0001c8075115004120b5802a000f14880000614110f24040c030010b0044c1028140c400706c41d1041c4e26002401d60701c2030f40200b8480b82e2103180f003611500f894800a541d440c4a50f0021442e0346017000205580021000300f078100c450f140701d0070443d0f84c0a0381c207221150f001000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 405976501 1250 405975251 405975253
    0x20a170c1e01021801020102091c0f0506100807053f011506020118020603070f0e030a060c110610090e010b030607180e010302030a02040e030d050702030a1107050d060b03 75
    0x2040c8005a03440740c11590590551400580c40350800444031200e10f2032003a103d0f042da88108403030681c43d06d4402c101c200140c5521001d242c0001c107424056031810030008010082d005003010011a040404e1204e810f0300d482d10120b0310050b440741e062100f065409641400c03002034030003c000d51a18292200030341512001c075007130440706584e2007a174290344107000c520076281500d440c1804450350921400845001c0110441c644610340d0b0003090461001401600030402d2141d00c051045000318214008510046c0440380d1403c07150070458002c01600340003000290310400340c2c80c01b22070002035041c011089000c0451443e031906000c10700034409202030900075520b505082c05a9503050010a101c0c51042d160b044580c0c511500c03490032490103811200c3c0210100d0018005030300c000130b8a451080d0306031000107401501c500501e20b180213183c00520a141400c04000d00a0750210107062040011385580c4100c01408192584504050058541001240545070080f508507004004e070710034094 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 405977751 1250 405976501 405976513
    0xa110909160b0a0e01050415030905190c0e0a02070203100b0f06030a0f050c07030e13021204032c030a0209040305120c1e09030a02012a1110020a170c 66
    0x1007400798880400c0c1d03024285000000c107011480940080b1a40c05103102441c0140c80e0a0501c07402000105035090114105550b51a0400c00c1000030040080d048034020342e0780359601c0461401d9819407100f40a501204400c04010515415a80c0292105140d004002d8901c0301800c0803040020400080e90590010307018044c0000e649544000b5801a4160800410005074440a04007a40c10282144032441000c22903580400d0340400c070101e1600040320780300c20303501a90b85180b0190250450806600212006100806801c4921102402640381d599191010368850042d41d15800108072038064200d10130781c0006203400a805503000e446070400e103081c800e12902c840003820381222601c0d17071200001440c2100c00c40100301440c03246407290b0824504950800401e88540b0311502c024107111207900380c083e2820f50003032111548180c0300b800105100781414003120b2070815040e01d40c0680c2d0900113458045201190200840d078001030700b00001d50019842c400795038060403404145018030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 405979001 1250 405977751 405977773
    0x40f0602040504090308091204050a0b16120e03011d10020309010e030307020a0c23040203060a0b030709031103030f090904031b08030703230105040c12020a080103140a110909 77
    0x14810412001d020f031b41e64000d945003980d141e40c0b80040c0305519a000e981c051204200541e2081168001c2c0c54014005548602d0f403000e07265516180c50b44014020204480110a050f49c070110720001100110000d20000816580c0000d07020b45801d42403d80b82c01c081514041900590000c42d0405c07121400000c041824109035811a00240d42c28001600104901c0c02400813241d451409880750f03400324212088944101540c0b121005280d030300650f008000909240d40314250040141549011035642e483c00c0c21006124000c41d01049a40c860042400c3c1d8172420008280d82d040880007ca00703117000ca81c5000c00c00300400042040f41007050340403240702551804102d94424601c2055401c1d01c0c0d0815100140644203d02c000c905041108030003200c0603e90450401d0440700c040d41d00081e03204180c401290014900c611800c031982c000209542e03580d5001a201c1e040307a0103140d44030168020601d505440302e140c0710029000201c05e40203030340e851038240b900d140c111400f00c08031000c1d0281 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 405980251 1250 405979001 405979009
    0x102070f080609060c0c0304050919050106023d0b150409020315060c1c17090304051203041401080a020c010516110a0b0c0a27030606050109030308040f06020405 71
    0x250303000300c0c0c0305410850900480f500700304041a0403d040c0c00003a03080c03000203040503a49008a02c50139104110100c082458001548140740545800c0c0905002641e10350740044d41c0c6281c541c0100c81c04480f1001308103e0147e0490013102401042a9a0f94803454003802c1c6502400c0c8a5509580c08654240b26240504254009000508801d0b0015071a8030309219a0711020040740d08560084408022040400c18081440640069455001c041140412600310348540b401c1d8001c244903184401407000300c02002001e0412203c044412800800d22840d80d540ca80c02144252071200381c803d10051100d6002e000300c070380d002203004001410704001c404c0721400d40b0401d4610301c0e44d0419501c0c20400450f8483c203144107821110300180b0b0242040c0d5240c0c40e004000070700c190385040020841481e041e101e00100750f0828140213100000451007d003070006024240300844525180c241d0004182d400350414104494054403043c04070360b580c0c0c03103402800d0100e10040b80e20560070000401d040d61 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 405981501 1250 405980251 405980279
    0xa0804060b0f030d03050405011a0d031d04060807050909030a1b050309100e040506030115090504110d0b100f0501050d020a020721020a0906031707050c0901030b04110f060406030b010207 82
    0x440c0d50701041ca0b0606003001401c44600d581881448080c1d030862ba01c0340d1b00c1d00317590802e2081d414a44003042901690f1100c1800b0200154607178018202940050b2248002076035070180c81040b03510f812151a0030092950764419131f0300c400f01081c0540d0a40036140300203201c003214540240b041d64a800f330f42c00001130700b16100e80c4001011400000c1c0014040c2094440d043d4810381c194001c10010380d001318070070600071061044817001a02e41d00010b0822901444002c0d00c040054403441d111102c510740070300110811140c0303202801e100c640c00030f40b424807608540c04582060319414548034040b0b18450117507012105178002d511070030200041c2c0620117103107a40010591076030014020203a20411102c5c080940c070103566281007240a0022901d48030f0701c2c55803400f031590015a00c40c0306180180c02c1c0007103251080e60100d0104000824031001d10652441188520b0311200c03003811709000c205891070b030800f80303640260040c0300900c98a4020b41c0b00740440c1d14140110740025682c2c03980c59000c2c4c1c5d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 405982751 1250 405981501 405981523
    0x911120f010f06080c030703110d0c030206070f031701050a12061401140310060810230a0f05010e09060a0e0f0111040302031204030f02090c09040e210a0804060b0f03 73
    0x1e0360f10001004000c406000f44551144101d014084080c51621039000d4001c406081c2032050300c02100003000c111000140c2d400860740544100d0b100c0d8500d05004c403500125004c1500411070740300c00d4000c20b0310000101c9060b20720007010482c2c22414000b40310744101c2c1946040b944c075550303000031078403ca034038480c002e0080c8603141841910310107000a260501c58440301e000c1107581405000e120010011500d484da00301d07208400034000803a0091440d00d41d40665051080e6400c40050150045040d00b00900e9421214030510550740e8540c042842000c0840c1c0d52940340d00140041000701150342c0094118014040440f481c00d20800041401c6a03000240108a0a030004007081141410f010034103241001c59551070826103151268002c0c0c0c100700e000280b207400c503280003440c1c8503500707019580d0baa000a0800c100864501c07a003155101c5030000e50038900d40c550310003101c400d03070174200b00ca4000c0c5141d65100c00f552110f94610001c0c0030f11190041e404480000301141545007001500104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 405984001 1250 405982751 405982781
    0x902040e0c0a06030603080301090e030f0f1e120415060518060a0603020313290a1a090105060927091c020607050708090a18021b010911120f01 63
    0x1881c03480400034082e030107500000c185414040100b0209540c01d060301d044a03035035900811200d041c2d004c0e0038118402e600d081c90000d400030500b4005d0400e841c014002c030b801a00d04100810030b428000b80320a0264150300400c500c1781f40c0025000414201f5520b014007061040807618684400014115a403212031041030f1440c21000c0082c0d524002e40d040d00105407504045166040150600d08484150380010b014000401070f0302c1c6800c00c90180c861101c00c038503c42c844080c04c118110001174590600c4038100601045680c0e0b04614003425120304035a40200810300d0002c60100f0b00080c0da0709460f0300b02141840140700d8445a0042c03000300d01c15110240039042194544c915107091012451015007154000d60800109a400900700d410050304203103074903185d010100006080e607855402c1b4450480840704070300e00005141c1c0140400e9404c0300f4042e07030780d0340390050203500325000710801601e00d10303000c502d5801504055060801044040781034950032030400340c045003565a224482040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 405985251 1250 405984001 405984013
    0x60f05191815030b0f0a120f1703010b07020f041e090c03050307080a08070f090501112a010210090b0c090315090d08090a02090f2806060e09040b13060902040e 70
    0x50789803074145d4002103242240c0c4061081d003003540510403640350500080c840344954506406102e0708000c0e421a649030307030410a41d01c2da15048034280542010f0800c9010303503c00c0882c03106520f001e0042c00c88482d0041c071b0720000500c0601c0e03514081c0804401c00d43d1100405400030020078400d0000748046805601001da41d0005900c00070709000d0300908100030048140b0006901650040ca00c0303040310b00034a0007040a94044000f203041c4000c6001c0805c0c003100760a050362421190003207804454900f40c0a03a00d100c01162082d0080d502c464100400000324040040c4059001101402c0700c101c001d41250121031944c240f242c0058801d4850741140da020322600c4454941c841039403903103da4108054040b420465012407440300d00540710640e070403c00030014580803403030741c895011a042251a5444400b10002601c01001503000d4180000c480385119119414003032103850240354890980030140e9640b46d11640c0583c00c5220460700c250b01c410750305001d030f0348a00031454076003402d2010b441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 405986501 1250 405985251 405985271
    0x70e0105040824090a15090804091503061d0a1407030b0f010305011503120e01032c0c03010c1707032315100c170702031204060f0519181503 62
    0xe030b5500c0281407110b141d01c04000d500c0000d5464101111110f0444008261401c4c10b1408c2c1035580100c0e00514105807820140c000e40e0710030035a0910850380281c004000c850201590120b42940c481602815940019103c80024443d80c000a200018240944130016100c1d0b840c02041c03042510580211a204401401030240030301c1440b0003100580e80380c0003034130b10356901c1108210904020505000c01700c0c0d2814083d1b4000d800c403020384680e281110320400c0b45185a44000d007501e101070144e51060700d8540b0030fa400c0500c235411b40b00c4403541f15805c41c60150721428910100c02400b0300d08060705c4003100c143d80c0c07040c4800d62008d240c403016404203603d48211000a41c000302d903041445040c04400207205103030031030a110103142d0000308202160071590f00030202c0e4418104003c0d01803007070b002400c01090410b0080d01c2a98020b40d0b425400719013101d402c44060144010301c00c0308071051601c13041140e005000540d000c080e40c10190031039503a10304003d82d8078024400d03280301007903e41321182 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 405987751 1250 405986501 405986563
    0x30a0209180319170f010b161217130b1801060521010509010c1e0314040303050603060106050c06010e060d0614061c110603090f2b0c0b070e01050408 66
    0x107030007401c0c0c109145013600d081044021501c0c01845240351441001910401113134080d00e03940400c9800c2188100e00c1c2d9030070827000307010405010b104030b410340803080861600713145400c030341500f0fa070420843c9002d501c83c404007032202c480081c0480e0f03180d03584200014454030f07902c0d90045101d2416590080c12004042c82500b520402404001980d00d0102c18802060b0000301d5800c075424004c801400d0102c043c00243c00403caa43c102c2c09414a0110803c0304140c0c0c990070262040d42c0c00c1e4250381c4240d984034804d507000c0c0039588004c03d950300903a00610584128203001a44075074000c004007801c1140b52114001c940001c6001003038401c0301001c0003401d0030500c500d0720b0f140020420b080c0008841d5107800c8450014511181c0c420300000001c100242020411140149080000c0e01d5411460070030492608a0901004060843c08180440d040740030741c241c850615040002d103895923035807140843c0e140382a0310031541481020310003c0b070301700410000c98040704105000c00c0c440e00c003010501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 405989001 1250 405987751 405987767
    0x405040c05030702071509050306010e04050706020601151209021206040b090309060409020d06050a1404110307120504021c0302031c0207030516082701080601050405030a0209180319 80
    0xc6414031008200b40040b4aa00240c004115041c4605030300c582102420112202e0b03d081d48059414400c40300040384286216008500451090049461031543c844013644c1340c890901c01c5500ea040c4034840484403a0060414084204070f80b8030000d104c089035400118801c80c3c460160340180e01100401082001c03200311540c00070316060081d17040144803800540c01d4840ca0048084050700803451030881241034200c403014060040c000c9071543d40304c031101c41108c0445001c49105501f02807500042880220890380a0b000941e20403003440750007450400a454040c2089030400c5080303000040c0b46c0d5101c0900a4102c0c401d0740034541d0354240d00c0400340c480401044540700c0c0707841000102c001070380000c22140000403062801c04001c03414145a942e40c0540e22012444e110320109640810110003401c4211103002d8a442403991200c40045030180201c2c028242c165000c0110440907107810742c4030661204800e4002d508030548000910300b150884101c0c14801255085502c500d66080010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 405990251 1250 405989001 405989021
    0x12030f0a1d0a02060c0c060715050a05040206090607020a090c0c030305092407020a20270105242d030f0c070f050d1d1207090b12060c040504 62
    0x26025146401c028102e031101c2c0c044030001c1c401e032000a41d0807001802400030040d40b80703006004a44030030f0b02d4107181a800d00000e141c03041483c1b8200c00138074111600d20600f4000c41d00503180c58141340c0d115041c85000c2e800240701740d130f12049407200000c411545d8041c07460800f13a00e9a80c8000c0b10107a207001340070750b440a042214960043d00e00e50851540c0514040c000d2500951424456210390400781d003014200340e00a01a1171841e100c5000d41c032803001d8010310b134120640c2e0383c00b500042480c03011034010700c42021386492000340c001046a0300d0406a03c000005050340780075402200c4a04402560340302a8544400c0ca092080c00c07500c80c1c00ea51901c0c1c6182481d49640c5245d49008050740940ca54000c1c0b46410070750000c0760410500c002490031101456001d012203014140094020f0180c952066400d40480301d00e02c80c40c0b0003420700c0000751031080d100030000d0800e9424030b034a0b500a4038681c8456600700501d402d000e06191404c1198031301400b0710b030702819076680c10700f014401131700c00c4062 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 405991501 1250 405990251 405990281
    0x90b01030c090e0a050c01050a0c0c0b21060d0204050c13031109060d0305071214030702010e19080405061605030a0c05120307020c0d080c0115090606020a022112030f0a 74
    0x6800c1e004100c5c0403544020011003441d06a503100e0130340d41d090783c02c00e071a982c0c080d003101001c1002040340322503500100140060100c207a0001a05c02c42105200300d402c440c1ca0b5008503c501005006040907000070740c02c030501d106098101401c0702c03040c0d580141e940c0d0050312017070840d0090058a0030082425500302030240d4103030400400c03a890207040c0d841180c4000300540411703400c0c0d1076124412842406240b110920301a0307a42001c4000902a007154006888140184805000c00380300011443c0400c40e48000d1880c1000d16210811201c1c1c2c002c01e50003070950381508204000074006000421008104c0c1d15599201b000b40e0a1880c603040c45800e00044c0b400c41002840400c580026541e600544200e503805c1501060b490300510318001c94503820429824044014462040302d8035000c242c0700d661804210041c2d41d07820403a42d811811030040e40240702c0b10514290b1010303d00c21807045103501400c0355102c0c9418a070301c9819a01c101e5203c0c05200b081400d11000282a0050300c07a0623603000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 405992751 1250 405991501 405991513
    0x70c0504050f040f0f0203010b040504061406030c0a090e010e1507020105071d090702010e060709051807090b0f160c0e13080a0f1101050c040501080a060f0315090b01030c090e 77
    0x1a88822020300080809404405170940781002c6603001d40040c42c444a0180041c005d40c00c0915081c0c015185a0b40c20303581c1c2e0030840000500c24200044d82e80315840b4000c1507441345a18000301c64004002110822001c3e54a8070030201850f0010446141c00c0a140603204a4030f24080200074216200649400d0800a566003c60221005c03800300c0c0000103011141b1560b6034031443d078260300628400e410750140e400391000b00300d410f82c0c004d1200c02c02c54405641200d004010f20001820015046400c580407842e554418040c429808003d81100402301c4565803800780f070442480844501038204644203080100103011103000440c3c826003001c032090042d0303044c00040d82d0391020360181c05011070400442046810350140300e813241c0d00010102c90300800c55802c24913044003a950050055501086054002c940300311a01c2c4141000c40c0c8200100b091400c0c210396074614003c4d08407081522a54440e921a404110a0100709008500c50b041d00440c862410000005403400c03400c582e01d203a0440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 405994001 1250 405992751 405992753
    0x32106050a210b100f1406180102120403120e060903060606210a020d1104061b021503072312010530010c0228030c060e03070c0504050f04 61
    0x24500c4410b940c2c040b20480140022001d19220541c5003480282c250403003081400340d94400031410f50103a419248580503801c0c0c076290003005544041407055042401000403510035141c900004801e0a414410b0312041c40c0d03040000f03102030300150810741fa21080c0000002555030003110f070303980282c01601e0b41414003984000007078903084001c100c40e02501000441c00750031084a81c14808a105540c1d41c20b50074107107018076000039003041c65803c402c14500036440c040c0403200801d480846806603030348014100c1071a0b0004074500d820f08100d070002500200120070900b410040c52191442d6038401042452014880c0300f4800c505008050148081000038081030a00f4029415500e044c1d6504484d240c880440c002c80c40d40c54003c03001a101044410301072518107400483d41e400d075650898040c0c030494540ca0601041718440380000c0d80482c201580028000d02d030307081c1400d02402001510048030b18610f4150b502034002110280203043c41402181340c42e214040d04200c0c035001000d864585 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 405995251 1250 405994001 405994009
    0x10050f0709051008061c080c19080a140d020304050c0306010f061709071707031505070c0209130605090f010e0c09010b130803070b160806010e040b0f090403210605 72
    0x3d4000b2030030400c81e6a0300068031a44900101c0c1d80044e00030000400244010b06144200d03400581e019000d600590607011400400d01169a1034a41c00c0400701c2c2c074029804000751092498031420344181d440a01100d030000190744051032140d40107201070300e8411030090406007404016048840340c501d810200740400d0f94002d088424801035682d902805482d16a200c40c50319110341d20414801c4402004800324000110f58102101e1007021a078100d56480d12108003665030441e074040020f26100c40707101c00361400b2403a03150070003012501380e00348000e961100b0003507413811a040301066000c03191442c6100b00c2403045107090b40200300030b841c1d07030070a050000d48078110600c550013070460b012810700d40d040a22200d28005083c004126503603650b192500c0034040303070100c4400741ca010300300e015518802d014002c0710707201303a50507580c111782c491040c01040000c1104030b0a1980200e8190550541c50b12000b0049024a0003522102c5003034041680d080120381022048a0000d400e200c2c04102c40d8032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 405996501 1250 405995251 405995269
    0x102408070f09510c080d020711040903050406020c0102060621070e09100b120a0201120e03270a0b0a031125050d020115090b0a030510050f070905 64
    0x74200e468a8051000715503180e8032010032000a501000c0c41128030341c00311400c0c1c0d200c07025030483c2c52440c41c0c250054a080c0c6190b080391401500b14a0304100803c100102580180185441110b04460600045020608a6501034411804240001800d108a940400c20810b088009100410035072601402007040e1040c52100d108036500040c0c0ba100820009005007030280804040404240c5844d142c03580e500d84403220403121141c50060710700024200291100403d40700c4400400403103a2940c0115a410301c15040b240460ba035902e03011803110024001001c81c074100b9505420100360300d00680612052083c002845600c41500400a4001c170b00c1c152842c1d180301e401c000884076200301410300544504103254032140614200004941c440700c018a20550003941240d120180d841c00581c00c8400c04030510490301540c910030010780b80150440d0b003c00744082c0810340926669650706103448965240c10700c110b5150800c021882e1075550540d81d000400d4900140c46a15220210b0301c0c800b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 405997751 1250 405996501 405996509
    0x4050a03080901030b0d1212090b130804050d23010c0206131a040f0b01090606050d020c01020903060c030a0b03011b030c0905060f0c01060906081203102408070f09 72
    0x80c1c01003210032840e03000354081c0ca102d05020744078020600c00341c0b414183c03e0010302500b2002c0380e0806201441d00b01203204c1d00c40d08690246c003000b10b584540320358038142900600e0032038182070300704004119038072400007200c41030348600440f2404000f00d840400706011842a507071303c961315244404102660000300715412101914070600e500d51b550800c442610020f828100c03810388081c2c03d100c01c02847e03507042d0340400d0041011401d02c0e43c940b42c15505850042c800d4000103141409005030b0440e80c0d81c0140b01c48100400014034094103607011900381b03201128001d42100012081000c00c9038a4000c0440811049008101c400c2e81c0380c3e0403128103101100f14000301503030b940002082070700908000c400350030000c05040d144d040c1e100040290382d004080c854465402c0000000c0c1c546010b0040605030717040c110241040076503030380441d022600001c3c0320160000203440e00080025a58849100d026010100d1810640803100043c1c04100050403040410840e40d044a000c6a8050403c505903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 405999001 1250 405997751 405997763
    0xe040c050f0a11010513050d0c05122b091b030b01090209030f010f0c020f060103120c03120c0504090c0f090e0a230a0c050a0519030906180302010501090204050a03 72
    0xa00002d2908403450b1442d0100c0309401d40c42c2c2814015610000108440d035144544100c0700d1041000c1d5040303441d5800030000400e0390703005e1042c81c4c07410011040902039108102580210302d03041b10286031040204c41e540046560b603514148002e000070784880a155100c00c13118100414507650b44c55940040c144900410070754041440f600c5a9414084100c030281401c00134801c44110a120742d000380203005216015100b0880c10101c1a0008118503048070f80083c031040c49848108000d45180e002c29008508000400e4007007400c8030707418070910101da4420354410340c8035410880840c046414003007411007801008411000501d50054030003064980700200701602c0c1c3c0b2600001d801500307544404841c60b10703450465100528134a000984030394401c0c401800384802861094400d0703c40d10304510b0000c0e5041000903030b5106440014800840b262900240d201065100c040844103521415115189451600000d1560901615001d007100178021450545400300245406846210040203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 406000251 1250 405999001 405999007
    0x90b091506040c140a020c010908010c02120d020c0a12020714030624060a05120f0c0d1518021308071202010c0515010f06090815150d170a0e040c050f 66
    0xc0d5034840e28850380310340c0902d010291174904014010b92030722031180b1200c7c002a084900000c1c0220140910809900980c000d001d000d201006042c905500c0240c0c0306e82c100c0c1e001c20903041900800c101c80d11020f4052001401a01c46280303000303042c04001d40c03100e42e0704584451010340d03603503002c20441d401c050440308035034444105c0010b48001c4640440c04076070190001c00c50316141500500203050901d903460040e51a0b58500d030303040192540035a9034185616052221003078aa504d544503441d282006a14006001c0d607914080038504070156001c41641d4000c51050700280488a150028144100c0500f0001c0c1c00c0082c0700c0e000384008000a41048499030421060110601520000046226440245684038024494622440d100358000105034802c000750820020500010740300c1020a1980d4a0300c030314400242190440040542c06101c05c0d17003100009002015042c21440c40070a9140c0b905a401e0010700f03580030200502e4002c83c100900c2256041d40039013210310420180483c291 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 406001501 1250 406000251 406000271
    0x140609070620100c0c02030123011a070203071202180408091e061303020901120f080a05091206010501030e03040b07060e0307060204090203010e0604021201090c0c05010f090b09150604 81
    0x124200003500f100900500e440720082c0d550b948502003a90950080e4000c2c03000045880500b03070441ca11254815140e192040103000e40c04148000300e802d0000442c40505204098000031308060603541303e146400d00400d07802c01103040101700d0103142030150540441602e429100c405c901c1c820300810a12550310000c00f00344000e549406c025102c3d0000d000c84d62500329070600740c050300025000c2a8482d210b0403000040034400700d02ca10b050141d011800400e41451035a50f04500d4204452036803d10a043c032030900305494010803070000c001190010b00842d40350000245c21992000c2d10383c00c10b500200818441484c01230304481c00e16a00210002d41040c2e41c00c400703400c601403050000e107258000580020003102039000744d810b961030b500740c442694451100304002c9100b64148107082d910710200420000c03407107901180320103148e42421404003009988007421200e00e048035190b650740d203544030024010072468031940690110000c0ca503017501a440b03268a50002030140c1e10968440707480c0b003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 406002751 1250 406001501 406001503
    0x3030f030603140c01020f160605070305120406061a310e0103030c110109051e0a1a0309190f111c051c05040b040506030c07050a140609070620 63
    0x907004540103020320049000900d402c43e100c1c080c000780b640c0144034010a2010410300030032407c8900103948514420303180b4092041d62150030003c0e0940501c013082c0003d0001c0c018400c03085200c1c4c0d10420000408a0405485410903418080c12a28111007400901300706046005859251601d640c07030350722280c620024485040d03d69400a507007503414840000b02b0142c100d41c2d06844140305a900104146c0035100440e40602d080c401c0e1540100c0c070f5500320f50003540700c1500e44486100540b07411511074440d094260962402d4132981c0640c40000100038404000740012030004940003004503401c0070b10781f01c40d0200d0450940c05045c50286041e40b0b4800d5507003209500c540c403040c01c070140d142032160070090b0b101d2034030600c0307811a840e05407001860b030340c0b01e0400c4134140d81c0011364040c100382c100700a000ea15000200202d030a01d03010804100850301c1005070800461203a064400041c02c00f1800d68248000a409109641c1c4000010b21505400c0600030b0b45400844810080040c85580c0c51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 406004001 1250 406002751 406002761
    0x50702040902031c0f0206010504050c0406030f0b0a060c0c0e06091b120a0606020607080c03012315040f0909050a06050a0209090702010e0d08040b06060a0221030105040e0309010903030f03 83
    0xc0310400081d513120403030540c00841d9903030384004513001d0f100300d40e90322014482070b02c5c01281c00b044900c8040100b0300489009500440d062035001200203204c1200101003208001285c00401c045201060418208070324014004013511011a071400c1e5400c11a0101c0c00000c40074001000c51004e10311100c490196403015a41440b07444030074540340341081c8180d100207010314010305005001740070004941e86d011b808002d0047c440c216483e891603203042c0c480411112024095540512403500012603681c910f4044001454000001d6030740768503040c03030740e00003d4095102800041c1031581000c0824404500351090640110010070150f8901200c007000384038140782994828004c07010310110541c158026004079440d5011075445d4088070200f0b89039001d00300c900030700d0007081100017041810020302408000d81380340100c560441454207906a08044081018802400480108201e29003030142e51140464007000e18a8810301800003443c0282900010f03052284294001190608ca6400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 406005251 1250 406004001 406004023
    0x203030d050a060f090b0904110102120316030c022b12020c07090e0c030601090e0304050307031407170303150f03100f0b0604051c17030a09170a05070204090203 71
    0x10006460b2001800000304402c0c09400820802c248000c00c002016115440300100c0060501c0c0e2559102e5a41d00700c0d440250044a04601a030070b10580c6040722803020318003c010940520340110030f19003001b0100c1e00002152411544410310981e5840801c40aa02c030220451125407020b40310080180d034480c0940f1030007076030240300003844a0300c8030010a1400c20337510f0403030007849421078084600750b8039015464030648c180c00140040000d0012a882080000750302400c2c0c0382000da551001130f05041d2164005e4900808000203400318000511070b242c040c1ca070324604001c2e104050500c0c00d507a40002000d2000840080715402c4290b40d13040b80b40a10040000d0440c0c100010002d14000544010b5403d040680c1c10154000c0d0640fa050702a2030035640e010700015404044030f1120f0582008c07400e0140d40011944101941c08084d0b0401540b02c2d460a1034003298010071403500c020715000c4520b120030541010f10410204d10352040458415540444011a8094180c0000303400c0c4241185 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 406006501 1250 406005251 406005277
    0xa06030f1512050606061e07020406080d1101061d010b0c0703050f100f05090a08071b0e01080d02120301260a030201050f0a1e0525180b0c03070f020303 67
    0x100040d042c08061485041e01d8072500a5509a031601c0c0203009590080380d103c40000c24405428550860004000c1d02e60395000400101c0e1203541c3e46002400e0075181c101000014a0b00001c90442c03240074000c0700014441c003944911010f0380c40010386044801802070514140000480c903e4001c010844000a180c00c030040c0c481c401000c3c09400da45030420001d1000441c10900302d17a4421880307200c3d0074868408003020300052821a9900c2c18181e011800c200c036034000c0009044d0800080001c020060a500c031192040d5504008605107020320003001d050866208617070f1101414541400c0d28111440410f80b4940402c004100d2202c00300c0036516520036102d041510000e06034150426400b0300da000714040d50540b42e62541006403801d41c00c4540014140d0744642c5908080d55000030352200808070034101004260818444407800600000d00080081d10320ba503a12020f40010b4000301040b00201d80340c42c555400b80c507100e01031410080d22101c9400540e0065440502c01c641018018034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 406007751 1250 406006501 406006541
    0x150901060e1318050d09170a0203030910141602040501080c0a0303030b0109091112070f0f080a060b030709060e01110c060d150905160e03100509010b060403050c030c0901050a06030f 80
    0x44003c10100c81840391f041c151b416480d6035826510042100e22511350040d000d1032810620301c0078042000c5101c8a41002c021000b80c409400810b544060210041c01e50312100310402240101b2050f04c1040e0826111a0811071040b0802c3d40d84892523800c072a414280820945548001a40c00745c440d46d01800d082c500309107030b60128200c060010410381c51111851a00d9840b0408112041e040184404c808228504103110841e40074203401c03544043c4032000483d1450b00c0d10811540c84d002274640b240401e00801c4184601900300d1001072442c8028a402800c1c1207a201080b6038440c04441041e020313480000710188804407a0300a289201c0c060b81c2e500924607600e0740100010b200803070705407000e617003d862605002440380310210b10708c80d00100202249902c45083d0030041501030039140b2107660b03449001c2c0c003548822015100070b600900c082d00c0d900c3c11100a140c10300751011004e1f48100040b00040c0035654404510000f500e0b1640b50002e40c14200071450b400610688040c4070a0503421 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 406009001 1250 406007751 406007773
    0x908121c05060f040b120f010f1b05030c0d150806090106060503090304120615080d11120306210106060c0c0504020304030912060906060e061f21060509150901060e131805 75
    0x150032427190420340c11800c1200b000b403c42c082c0c01d004060101080003480c1007020480451625001c1c054040c00650300080b034806c0c001c2c0540004406500c0080141c1000040090980007032040c540140614101145140b904181141d201e104a014208c00c2200003010540ad00c07146521100000021a403456142500c4000550313451446118840c0010580c001527607070b502005ca0802290300c0a092124119180d40042015200c800c0120500041c00701d4451500e034902400340c00c0041585403107420600d13000c1d043c802c1c03440416802a82c0030314010018080040d920504078408c0707038030043c030030800c01801e0f107020b6002c2c0810031230141031a4103112000c0743c1c0b4021542c40700c0c0a01001c1b200e4120081c10780040340d145650a4200c00e003c10030078554800d10424500b04442c070b43d10344400c0098003903200c0000801541098400c581c010260a2005501c0e040403440140940500d0500400a801040c001034009000d01e00e00c021070340d02c501c808003080c0010242010740d56070103420b407000d00f412 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 406010251 1250 406009001 406009003
    0xc1b030605060a060f0206040210120c320a03020901050c0d051b3403051b03010b1912020a03060203070c050c100801090203070908121c05060f040b120f 67
    0x58070b0b0944600c0480340c00184042c01203040125154864000e80166940c81c3c081218080020740740c00f06120514030a5401e84581c0d100c5c0d214091000d44520302d00140c003c5141d2600707080d6000100081040d0805141c00810010a8a480d911103240c0545c0c3c5805210040340c2074007602280740180d104c0e6114000e01c3c1c5400c00098050111801034640031081a020266984c0c0c0b0030340c10000311000c01403010881d044048c0101c00c0034000c122001491a9642da03590b0b132400c0d1048184400b000c4c10280001a2440c1c02e001d03803030806000b280d8218000d07450620444241c03480388685900c4500f0009201b04548800188000450300594215200c4c80c08200181041004602c1187c1701e02900315510150f15110415228070642542c804009030309043c1d141d13000b540050300da01c042c8141486e00041d4024200310203080c2034102d40c80e0340c0d01c03001c01d422a28415001c0d40c010707a0001d0b0034403003000360640310f465415007444011540070800c001200c0202d004140c0c0212142203074000c82204021030303c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 406011501 1250 406010251 406010261
    0x9040b130507080c01080606040e0a1d0d030e0705101209020301060909080912070b070f1a010612060801020a050a030b0a0308041d06060702030a08031b0d090506070e030d0c1b0306 79
    0x100383c0351712106e6691a002c1009601c5240648044222030740d011030302021320742d4031a4903200e106030121000b40049841c490300c0c00301040c8101e000681c0f941c58158180740f050058900130282624004040c40c000310300907202409400c4040032441e59140c20f20255034003500b05000810040804120781032407800c1103031840d0310a8030341c180070701205591452041800100242112440307540d2500f0010f20b42e172503600701c4c46024400e46056000d40a400b244c0590100000e008020548440d6140096102910140c1c0c5260717201c10a241d20620184a0241c1c200e0304440c1d003e0410310b00050300144070800140e4403001a00090040d0342c0224000c2a1350280d07868000401c0781c2c03a000c1840c1036440c2c4041042d24421004001c3d016008048200c00003402400a180c1100031540c1301d41c1c4444181c404866190811000060050340301c400440a0010510002d608001c0500d00548140602030100303a860102c0ca082c0740400ca01d0b40219001d121041042442109041e50110840d5a480c201200600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 406012751 1250 406011501 406011523
    0x7021c0606090606020d0c05030306040b01200f2b110102071a0a15120b060a03050f0307021003151a12090a0c06020d092303030a0c0605010f0509040b13050708 70
    0x2c814441b581841a0240c103900d044158024011803950751140140400380220142e446e05100446186006c6209000c6802c0c804060004c020720509180401e05480e28110412a25012540110b01c01402c81e0225160b401900f960901d034001c19100c0e404540284a40300019016590401104200c09a00e5000600840041c50148041d60707909034000c01e0340c03038540b00310f500c2610030140c0d80c400a004020030a60100c0018850100155a40c440c503040070440404509150400a603201c118a050f020140e107120b864a804c01801089513517540005034039004a0040c1a425844c05003075068100840e45000607690088400d030400c200d4165850020400031103410500c0000881d00c01d01c00243d0b038030b40c10f1180e50f58003216460001c000115a202017100790202d505103540c03030255242040104182040d681d03034180c841220341824421508181c05c0b0300800107200408120590b1100d81c82e5030044d400c1685122a5280c251326200c0e4081c025000410030b008400340000c0f9a0404203031041c0c00c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 406014001 1250 406012751 406012753
    0x12140702070506041d060a080703030503010915030f06050604021b0c03101515020106050402160203010b01050406050d23090a060b03010606210605060f070c1401020307021c060609060602 82
    0x4070b849000308910ba02490003070300045e800704903e00124464034001182c021401070181ea4245844800c05428920190010f50204000200404c80402c4a1284110400c54000e002004074119a59040a0030a0314000740c803c54841c00401c0e01d680e215030407541903110906013202001000d5005503140d0038010041e91103402405e54910000925016501480000d00201760490703041c5103000d54800b1090018004566031480e0104280d280c81c40180f80d004103101b205805502d05104250030345160700034241c10401c017407004200554109003600c10200c00d5076000f00d0701e00b2400746020030b00da2070320704c806510000c000c061010616001c41e4455500c0c1c0602c000748011011002854240e40c26880b40000064802c40d101c0c035440d050403003003994207404010200b2015500e900140c0d0740d8204070750848181318002544810001442d6440d4000d2291450340da01400100c0c0004c1e40780e02a01d000603000350340303a0201002c0a00c0d41d110020700140e00420411940340c50300114402021140150303009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 406015251 1250 406014001 406014013
    0x20a0b0703140c0c091302033003151903081605160608220302031207120905100b0103090f080310090207060903090608060a14010e060403120f050c06010303080712140702 75
    0x1d254164600011b01d130050700416031a4010503481001d19000403c4061280321640504102440e180040d80148003001e04100b04041541c104a03827030b04102c40980a1070150703141013000174601c074240d5440307520500362042c80c00f443c0d003041418095406d0072040031001c008004590306820004071401040700306455810a1070032031100c1d00b0359404000240240e030040c481301301c428840e60081c0ba8014420f01d0710b40d00b60300001c070310b007020f680060300c0484d0150081000d020b41e2a44500c9500c1c0c1c05002480c003480415415110803c40948001019240e80d10010019207444403859440300213000c50082150303104540e08008004200b18502200090000040050f07001d02c540b04040c02100000c1410b00e4052074810009400c07902c01e001c40381400488600d0384c056035180005040198000e908007038941c0c4410320010907114000079030009110050003030a180f150300040041c1902d506050503511515003500a8940d16086150b0900080c284031650302403100004a00d8041c411503001c40300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 406016501 1250 406015251 406015261
    0x2030f06060f04090b180702060f091501030212030c0601061107060c0b190b030a03050d05010e130b04051501030f02010306080d02150408070203030c030318030403020a0b0703140c0c09 81
    0x140380b00c1d0408000440005001c28026030f041c50340003554402c801801307050700c5c142e07070360308000c5078507044446401580210080003c40d0000b951020741c1b1981100c0501a105100e4020076414101800080d0181d8000408032031450000c01c22500c203000d41c40204ca550350b035148402024803084100b00a0103000e100c000150280c06812030f4001598007000164080d503800d12200030208031140c07070101140d19014149507a031014004c44903414000d54800380c7d50403106110105540341a40420303041d200700030821404c03e440f13000c150b49241e40320041031501c0e2130300e0a20714075181c42250049113000c46000000b00f000140d48403600114401e0300d043c031525039514452500c981c250805440542c2001648180001d42c0c080c03200d500a20031510242440b0242d004245141c200c0d9800d840c0d51742c03002080c810300305170035444110440c280c030001313500c2d09003158046010342155100b40d20180304045400001c150040000d00000e400ca9200c182d02c44a082c40010b40d6501c030416601d00611003000411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 406017751 1250 406016501 406016509
    0x903040f0e0106092c0a0b060a0302130e060d020112060504110c0f0601051516060203270c0d150f0e010b0a09020c030a1b060c08010302090a09030e061c050a02030f06 73
    0x180082c030658084a100145e038918856140302e00800100c980e40c1d0395250b541d484d6a84402a00755100d103030758016141c1c0b480035101c001080e216006254404200400c020281e034030014180042c0c8d80c203203000e40c000d1a00902c007601816094004540c0581000380a00d03100c295400580026040c2004070b85100450500481e2656828090300b41c202c50015864581c1294810043c020749a1240a2442844560b1110f070201e0700281d0b03501c000f0603003108a4140508005071a01c0c856810340d405400010107540000d5006240c200c0020004250041e01c440410b030b49500c55260001c02c694240044e40e03450a03403900070016000d013588101812500410003080500c03e40d080349449200a624007001501c0c00d44d69183c1641780e00f4640d01d184800c620004003180034141c4c0c201e4841e160001e881d415481084410480146034903c154a401641804a139202802d49a101c0b0240c3d119aa1821031000c0d0a003004014508000c100d41013009021183d03240e0b90007035100c4c0b5900341700d0500a0700c41c1d101700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 406019001 1250 406017751 406017779
    0x905190201360b0c0606061605250b2b0e060906040b07030b0a050f04021308030d060608090a060b03030c011119030209091501030f0c020114070503060a0e0903040f0e010609 76
    0x300d1440c5d01403c0003860390b0410b40300a00c0c411184190b004c284000c2175032a036281101803185d0341c0c40c6100040641c680c0361040000d40700645030748a0924144031507442d40d411209503540391b010714141105108a80c4410f82d5109003010308070001503c50515041502c0d6039100f00c00e440c1140d98001a00000d8000380c441d1280c401040c40040c0310b500000d140a080006c49010b4000c01c1d0b900c5a0b0800402ca800d003d21a5428001c00c0020302a546460035055075000701c0702d40d43d10000074007801030100502c85501180d07104209911510001e800f401c0380e0302203459401034944c03018880d842e1402015114060b42c01030154481c58425001d144000c5d42001c034140d0003010405500301c0c02440100c2c10410030390304480e01d44041032500190005c488001081500c0d4101500360250350f440b810200a041c8a4100b60303441942030525501c0d504098001c600d0500440c8240b0240c0801400841c41e401c2c1c080c41220001d040d03501c031423088580c07140001c4010030002c0c407500002c5a07400d5800690300c0e00014607 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 406020251 1250 406019001 406019017
    0xd08060f0a0b030916080d0e01020111070618060f0e0f0705010503040b070203070812043c050a1208061c05030a0509030a0c091505040905190201360b 66
    0x40c40307007450325005061005803c0038082400714001c002c10b44c6040008031421000904c80c884c028601440046405040d101c40850b03200d04590410400c4064002c5030b0b01201c903103036448a000542c001840608840e80ca880070001000c0c90304002a48512081c0790f001010380c118203c0a6603c1031a81e00c050540c0c03a121886000e001c80c4c01400058049071941c00b00990008490068a14107a031030790b01c00f0f0755540048081d000021500c401d100520060b0044a015006254116102042e44911031801512840c6900207466601c18041d402c01070700f8400720901075849401e00ca48001001d001412119040702c0c064040d80f602d0210205104050007181704a0303401901451a18205000c102d61540c400302100340c051150001c0507001541030908103000340490300001841640014201160740300d903510081c0300c0c904011089000c81d101165a010300b6a1741e03200c48000c2002da01c016960a0400040c00c50600f15610000010b1100303070300560f003248010a001503c1940b0385920119902960310 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 406021501 1250 406020251 406020259
    0x6040509040f050a0503130906092003070e06030c0315030313150504170106060801080d1403040f0c030b060414010e060904080c1617030712180909050d08060f 70
    0x101040108000b08203a480c80341c003550583c2d000200640b030740e1786594030060651510b404d19a10402c038200852003408090061648180301c2c88802c40315180000c0072031401500d18a00001c04248254001c112000c1e01d504c010b00060744900e01070707515480641048900420351a00400b01e9016464040111002d00c22030f5800c01d5842400e14460542019419690809114041001017840c914040c0e810040084200000c901d460611000a04084040c3e03ca403d050380003200c01c000c4a80c1059002d105286000300c9140c49964509140d100c2580d00072011f42454403803071006c130901030b20300043c920a00341a1814411400c1014034001004000d10942c140659084045661443c3c4540070351781042c05485e142d4207080d107500d4240d0070003100c1100c0301031415000008006480c14503018696440c40d040280d42800f50544403440d6403a00c0a8000701000700900c0789010308580d4600050180c20303581d008104142452400641d604d01d51500c10002c244050001074851074001130380e1041d0b0384050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 406022751 1250 406021501 406021519
    0x1051006050d18060914010b060f0a2708061b03040b061c1506030201110d3c120b09090c0d0c17060105130510050f0409060903051305060405 62
    0x80b48200050000354020b009800b071510000d0b020800b03a00480090a00401410340000702c0d004813207007101c090303075111805902c1c140314445549182da015602a80000c0c2065910045001c07808891070b911125400c801c811303c007070082190750b4001202c5200d4099007001c040e414404905640c0c1d6408111030040c551005000001c030f007800c2015207508003080800c08e13482600495981e02c00f4040e01c41046002456030303900c08105541e44078002440002000016040c4042940c20040210700c0c48001c40700f0400081c028082c50860011034419014440c00c10510302c2d8013034100040103058409006440c850034001d015000d07207481c071030039405854a04001c2c00c000150700c00b440b4030052102029100f1020200300007401c5101c00780c4101840340818081c1c00b0541c1031004104001c64248035100217980b404080100216440e110702d8140d0348200c42200444040b04001130180941c400024820f40c00c0170001c404054100e00030f00b000410b19000405010785400a011641c02a8840c680e4046807032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 406024001 1250 406022751 406022767
    0x20319030b03030d0f0c0f05030f070c2a05010e030d090e0c1b010209030d02060f0c07060e19051009050303060f031203070806030d0314181911030105100605 69
    0x254040e0044110242c1583d040800c120042411200810000c4584513140c440705404ca13035101c40c0d03070074046640c2d0812500b10300b40101020305c2108028100f00c24002c4200180c401d20100c24a08503260280b40c03010190f070000080329441a1185104c2c00e4041410403070100c8551601107800c0e1104901c903511602490720b4989164140031b0040c00300c00c03600004100d50b6204140d0001c4140c0c9030200c120000d40c2e80c4200005041c03404484001070710464102c8010300c04603120076032100d5000f0305400459501c1c0d50090501c0030007000001d4078030f8551703c20741c0030100b0320600030303441e40c0070070ba000348280e4001042c0c11858078103603145082c0040032a00100001415864103003407100c1c1800001d000c50f402c6005081544001d80d10503215207010518510821107035180030428041562001e140501013071248080740078074203f02902c02c0c0d01014003170018501ca80420030008140c1403081062404180720f41c200894016400120207010f0b50070f00d000101800074400030303101160459070340c507460601d038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 406025251 1250 406024001 406024007
    0x303050601110a030314010b040e01120524040b0105060c0706051308060f01090501090b0109093803012f0c0c0a0b0c1c0e0d03021606020616020319 65
    0x80285030605020781e800070000c4908042050f0075600380f007500c002a40241ca940e81d10a0104168007404140204020a10104030034280703043c1111500c1c0e507003821012242c6051401c090f80110b241507054110703c0c0c00ca0709070000000c002d00880c0a0007410b40566200c6092201511441d0401807990740242c0c010010b03980301e440100500f0320402180c2d081640c9030640203040c000b059980e480161441d80050200240c98820703940101044902040085044d40000c1e00030760082c400c5903003255032105510585806a4883c4d500385040f00205c2e01d940000e101215009200e140d10b4500079841e10300503507a85040d955020b840c2402c21341500c00603c64002d8030350b4031070f13019441d580064019800105100d440d0408144064182d41942c6501c5020050030303d807409e21501581400180ca4ac1041baa2440d0802c0c12242c24440544804070200210706041c0e103040b64402510b104804401d00c001415a03000c01c015024980300203c1090011204030100e80c0c0303008030400b01240d04004a240044140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 406026501 1250 406025251 406025261
    0x708160c020a0308030f1003020108061003090f0602212203090914011a18060d06080a0503090a1502060a021b1006080c011b14031e21130303 62
    0x102480c00380050341055001c2402050258402c60340118040284460300c00a03224183d400011441c0103030803140b841d000213003d02e5001e00580d0054100c0211800c01c0ca01c00d800515001b41c002c80104001c42c0c4915103500207620003003820000b00390344008441010003e4000e54060008088a04115580e81c1c000210045520794100e040c440d010a0000f100c4609018101c00e85494446081d11585859031400d407081c2c1380c80e1078480d204010041c1c012500c0314108016000501038a0f850b40380e91026400f000141041d0301302c00d40b140308600e640d4040000020007084601170a4070b840907145e0303942c0c0d01841a800c60070144000340c1c2003800020801500340d070142404600b40c0910150b000b91080c1100c3c10076242e4500709104a0300d80c6010f11510004001307a9030510400e02e404180200d20340c81c080206846074900400e1120402c98a842070403003082944e1960141c05141c3d52000e041842c1d02d805235001d03d0b42d03814008903104581d400d642103448040e10036041313641008415401a03034210000c0c6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 406027751 1250 406026501 406026541
    0x4140607020a0e070e0a0303050a080c130305030319050405070b0c010b090f06010f020c0102100f09061410060215070807020a1209031a010308070201050c030409140a140708 76
    0x18414000880582d9884410340c00a01452100300c2941c14a4540101021002d60095002c3c0025035070810000e6405003c03649066034510303001c50381d03403100303104d00d44036218511041c20120f80c05c84010040c800044020b40c0503021220a41e004071070a000e80c030003505c1c0126806025504203041c104550114030700200110207142000051200d00170f800507492040694011245550100400c5619600640746020b912001d00041003142900700001f90740740262100165985e4a0700a03800c802801c0d07400c1110202e07072205081c4a510200b00d010f1022442c2101c0c1000c0b0300d01d1041000400500106081100b800c2c10768000700ba99841c940d00365010070010f0a0701c011446034080070b2001c00c1071010203040c0192542d481542081c90b508114060410324210710060081940040000401e068200d422095081c00d10b07035110b101c51143c207801c40c0660b5020100b12820810005042d0072641980f0344908072419040218504100c510355184100304c0340c0101150128010503080d84214401c80202 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 406029001 1250 406027751 406027759
    0x70f1502030a2a03030902030c010201050f0705090d08030a1b0e010c0b090c0306040605090d02160e07050c0d1e0806010c02130f09050706020f06040515190c02070e0a060b0414 77
    0x4040024908030501d6000b83d8160002940c4d40040821031400f40510310324150300344000c1c00941800b07511f4900300e032800f9003200284200040c140200e03803590840700b0b00c6180c020080355103900d02180701501170408100c00980c0d642c48400c1144c029030299807101e111810694030402e4880040e0359081d0304900190205185101d88a18405585c0d01000150f120380e10a24021526013028100f541c44c20f944041c0203400e541100107481e503c45920985a402c03a80c0c6880400c80030b17150081b0540382c80c443c15501c0405405144841d5041a4001003162403c1c441e009000e0050b44505508540c01c2d0b200780c460600003914030381c0080144c6400300440c5264801700c02c000401c4c2c07402030007040c1101e405c41c0c003c584507000769100704682a014440c91404041100180500e858181c1d2416210041c09404d03080c0d05691802042881480c0b049081000da61440c0401240c081910040d584100c01d204151100e00e0410000d045c001c0180111002c64601c822500e080600300545409403070843d04d036860704 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 406030251 1250 406029001 406029047
    0xf05040b0d02060d0c031a01080609071b03020607080c0c0a020d030909090b04050d2f0106120308090705100c06021c06031a0f222102070f1502030a 65
    0x56074840f0028005000f0440c00002d03140c1c131400024055485107c01c08015001c1131916000590308021100c2c0c3c010011250750000d40e440f0003064070100c001d151b00c5000008140c42500401d5000a001801101c064a44035515510300944180a1284403204c0c40d603a0046449440107003081400c840c0e480c3d04c28102036000544544001c4105c0c0c0889600703030340c0b10b60208148801d11006101a110b11003107481e00d16948880c82d11405001107030524040c20b400c080d89005003441c0c10079800321019044900280682061314100100300c940241e840c0a03150040d01c0f0001b4162501e020303c40350311111a04c0d03250400f0126210100250096061102011041414080940524071400000e1403050070141d284e0540e11400070301e21a0020301050b5108450014010b0aa110080b032160315810421650700e070300c01d14905150181081003002c1440000741400c0d9040640100320541500d020204400c1c4031369072010001404031459040e400503030030411007031001e0740c40b8940c08500300e8a80c480b0040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 406031501 1250 406030251 406030253
    0xd090b0a110303070507110a290f0a0e09090d080a111204050d08090105040b0123040c0e120c060f09060f04030501050105210d0813060e0610050a0f05040b0d 69
    0x81103920465104c0d00080d80010702400708a85010408015002643c0c204000b03030510710354079000440908101660350b2802d0003042580a01000c9610030200c0c07112807a121004030f10007804801a801071a84101c0034500001c05e0504001040690740105948080c031984508100318004c220314255104440c2003000785192401c0400d02c01070149200d44010920203a0342c4500402640019104040c079034101403d22010a000b15100c03415038080c1844080c910700d00c24078920034031110b500940c3d0042e090030040f810041e000540a05c0c05002901d040140304c0042d05a05d0311007407942440d0b80e10180074070106421074080c2000c0d108144025145c146040c1c418010090160172690003140c50743c1d100c8005100e581020101d9022404000d10420b04038181c400e40d241d1100b0310710707448208005180d4000340e020b48540000b03c0c55035410800400003101255030441c3c07640400c8a92108904100000086504094003421b04403003d460790324440504100070400039103085041281d20240e480c840c08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 406032751 1250 406031501 406031503
    0xb0309070506160b091e030a0c1b09180c05030109020303030a0c02010b2d04050105061905130f210b010e041a01090b120f0a150212090d0806030d090b0a11 68
    0x40c0515550740081540d10a1b1084400414549440c0d0100700d400c01d0086881446d00324640d080782c030741d0244102520711400d40c40d0384580003060b03015841690810b08500500c0034009820b00071140a01880c8180c281c664041c942610040039009425038002c10004040b510140d000b254840454800071030002d60103000503600e500da850f0a96810710f1207180410003c0703980d00000502c036100b41c0d02800a0340c5890002031450142c0d04010400303000c0c5005014240d4801d004403101440c0d03030058144015110b0aa8031940030003400b0300c000c40b00a24092071280900c2403900d0601c0ca611001c4100359030309110380f41d055090050411241c0207018200c04154040c52800680a01440c240000d800000c0d1030401117021011910141d080d000814441843c003170115546130150b070808900300e41c00c42d2100382c840c000d10402c034441150004440500044a4000c83c1500c40b0f034000f0303651550180c81d030208041d140c00c07483c3e408078042102510100440c51781040a40304509090804a0154002004071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 406034001 1250 406032751 406032773
    0x901090501050f0f07170105210607090e010815010b0c010e1c02011b090b090f150403030f0908030d09050c1917030705030f070c0b0412020a0b030907050616 69
    0x84010300712004009007443c0468138180d01c41345900e0000400360b182e40e941d403401c40c018040c6502603080c2101c014401c0c2c03101100c3c150340c0c441140c101c3d101854070107001420150380d8028070030b0b5100c10b04000100000c0000b1140001c1e040803440340d0b01640391004191042d800f00d45a00225501e03400c00c001ca10100784107110701c02847e890035002d0041e000800a086400800340c50566414221805c14402e5104981c1000d40310040380c1c040e0743d10f081200150005489441c011391118408140b6070a100c1450060b001302c0b0b1290f1a55415503030f0010741a00c09000c039008040d1198002c2c00340b401448480e4103c1c0c008180140180c43d07040140001041b01401c4001c143d03503011300e1101c0204140c0c40b82c0b51441c0c040704c2c944405035051040f0b07607850a03100c0c8240350b8142d9000001090383d01c280141c84201c02d0051442c504a283d613996071706a50100d0510040b004d80c0314070042d0700000703000701d13504040340e1241c00004054101d16090408202e40e542124070541c1d552103085114400080740d25540c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 406035251 1250 406034001 406034011
    0x10e0102160f141210050a0b0a0906090510031a0703060b0d060e060d2a0503071403010b150a030519020f0705010b030705101209120e0109060801050d0308090109050105 74
    0x35610301c10381022580f04111601c10318480c000c0324000c1c5643d420703c1c0d001c90510b0062044035004107044d1038014000008d480050307006580b09600e2640094a10300c2a403000049818a14040c400c036034800000d003400e0106880003410414101a0100d0902103480a00303900907010300700003805503124101c1c040d0682003441d00c02034503a81c40c0824010b1a07801c00003668044001c6401d00f500c06d019688145c260b080f111441c64000e2800f0003105500390ba4000450007515001c1c04540c1403da4490b003841824020405140c0203502e02031050480341080d01d00c100c074014201919078503051100c04201d0003000c00a241130103038400d14400251602d0079000609140f607071403c030240c0790101801c0c09030845120200d210312a5000c010b0421080d11095200b51043ca014101007450599102d0800090301102100410030300003400c1c1800c07551340149400b40c100b402070346e034a0525500d581e01526660b00078010203070320040016000c000207104200199000500d03500110320320341680d0b030745400e40324241c40b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 406036501 1250 406035251 406035269
    0x318080313090b131508010c02031918150917031e04140d05030904060321080702031815040305060105011407081e070c0f1508060f010e010216 63
    0x11a81e1030340078040440c0002d0070485804100301d10542c000502603400340300c0310201d02d41d1100000360003070b504d40c480080140b00312002482440f2480500035205d0b0722151070b8039048950841816405481405d41e240e401c1f40907030208050904010400c991032a484c200c02040082c15000811026103106450390fa0710401001181c981d400c4403506903a80070542c10308050854140020050b8524074401d8015a1005a070090a1010642041411407042181d504d401c00d00300f5400008001d8009511103081e412002c800c0d41082c1c40c0071084070304400c25600e420045c1d00a0020b070003a0800c0c144540841e01006015070180100c00b078006001c0d400c5940140d50a0700034400400065070455a09220181105140b40c9480300a503640d2040c3e0191400505c0d030401c003c150b0140035080f0700104c0d01340640120440300e001e6911414a030701e16255000d141304800d0003440380050f25000c0c070135a5000f03030001010f11010350f10007001100c003141056410781c11171085006180c0e06808032039804c0c020b0b00d41c01c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 406037751 1250 406036501 406036507
    0x1a01031d120417060606071202030d060e010e060118060f26060405160207060c0c1805040302010e030a0e060d060f06020c0a1a16110315040218010501020d0c03180803 73
    0x400c0403200c5551244000302e013070b00310404000541c0d03100012a9a281d600204050036561005422440e50162184284609190980210b11130140b421001d040b5004204449034641d01c0000440c5c40c3c0c2d85000b203110038180c595000b0701c01640140103c2c051516140b071f00440c40140440c10349541450b01003803115034044242800040d0030715000b01a4084000a002d64416000750ba000b582c0b40c3c0d040c41510100541c2111200c108610b28402000a082e0006280c1408100e414404000d1000b43d0301140950701c1c041ca1348512400100540308110300a8440c0c0a000d1f46460911003503030f012440e00244165101c02c04a40c060921003068003409456004107900d140e804180030200200b030f0030482d100c00c11030100c1048825050308440b80980c2000e03d1004504c40ba2500600040005041d66414050f038000103030b51403024944140700714000c1760301c994403e0184100c020005401e002e00f500581117030020194141c01a4190002c1c40d22a1030a031460030003010388804c0300c0c04250003091140e0000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 406039001 1250 406037751 406037759
    0xf0a0905090c07050d080a061a0309010b1e040203190c080919080a0f0c24060e040816050c03070b03040201030f0b0102030301090b130c031506031a01031d1204 70
    0x1102607160b02c408440c0b42c0e180b070802643c45055441108080e044100f00311039000a080b4003c9030400c00090500000702d024680360885820300640081b1021201c03586005950031842c942020b00c0b001130903508994905101822041c0406584000c010858802c2800f03415261303030010384101220409950f030b03010020f0801c0410241041c4030038800c002c8080407002e405011900e2403046404041c0e05003401a4140754640381940c0b105401c6a014081203402410349d22043c090795043c031000c500070b040070002140c43d076a0402c0341c1503090781c014145d8081030100300304030f48005195540c440c1c000c0c0112602c0000040000740b806550350003902c00100040103101c21940c05020390b40c41a441c06200380842e5200000003985c0340014814207441c1a1604000c042a4481480000c0340e001c0c06041848281440403028004d050b00c4c1c603c86107020414040010341d24403900c87c032000004801c03548050018818011400f03848440441044402c001c40490030914040040280704685100b840e0b440304e1030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 406040251 1250 406039001 406039009
    0x60c09210f0b0112020a0603052205150a05060f03010e0303010519030c0b0a12050f04030f050706050c040501140c03040e0a0b0d110a0503011401030605040501020f0a120b0f090402090403050f0a0905 87
    0x1548101f01b858200703018407201300c02c8404010401e80e9150300ca40000e80c2c550030141d20300503104685c5140301c041300047c000c450541d500181e129003015104540c18600400038182210024840c40005400510040c0807070310f040418680e261450003030035040181c59403144d86480645510181d40b004d000038002050981010100508041d00703007040001d842c09070707011002600003c00007410060441c103000c56281c0500150b0381080d8020004002078580a00c0000040c0c0c06406883d021035020030320203641031102c00c02c942031081440702940c20329140c208410b070340086c06800c00000d151070f1401607801c0d44840c4000040180035448880700110804140038410714103410a0b4003d9040090410340d034940f5061250449504c11400103050341c0b58100b890080c058100314108101002030b1004070319501100401c02c2240d5660100001c4003030004002d0580140503000d070301301c154003002601501d4540c24240c0c2c8580a42065031074001d91004078251548010741c0d0030042240010140702e1428 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 406041501 1250 406040251 406040269
    0x30105010b0702311503140703051908090409030206040b0606030601021e01060f0e09070605090d0f151d070803030c0306090a090203060112060c09210f0b011202 71
    0x100890400b480d2031400e40100b001c540041c1c0100140b050480c15012000c1a00380c0b051070401040d01007001424100120944208101e2009550403568400101003a00011400c40e0403207600900500c2c10030150f0540101c001c4600c03c055a4400d414400c803203094445009296620344a640038000918203890043c0f0404030252090b03004030380c00c1c020070070266000286101d200540c4004220031103c960031a84c0942032980140882d902090030020310803103900d0546004e096008280c1c0c202d00d132140c108491901541201d0b503403281c2c1981c0c0c00400f080c12071030b41030003042c01800381104035601289a5019601600082d483c1042c425400307103041036042c000ca00107411034102552550038082d94070b05581c00b01030701003407082c00c074080811401011980400d01c0a9409400e4541079070f907902c0c01c3d001c0d04911030815507426003024582c1c00c105220307e0017036003521840300c41545a03081884500460404140b4200c80d00140d159002010980c05d481d524001c100991a0388007100e0f04d4418400031b41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 406042751 1250 406041501 406041509
    0x303120906070c0c06230712020d08060102190204140c040911071a090313031101090504050f0c0d0b040e1b060a230d151a0f040b090301200903010501 66
    0x803106002100000e51000d04000480c4d419107010000a0700141e100d10540015000d00f403046d1400040000c100610b01c0e640386607000f015025a14121000b00c1c064809100441d0b0880c0160841cac9044010410740f403e40103c02800604005642d42c0030f024201d9a5403010388580609072000f00f0100700480c141d000b40d000c40080381100c40c1c10045d540c0e4071034800c980e0401c151350b841168400090a591010000d850881101002c000c441c40e80e2820a40e04403801003400c240050220707d0040364030b0616004990048808111504065458070142d0380c2e035030001c13207090301c81540b500358070150740d5030380d004d4050808501e80182481c6640c612140081900b8213814501680040c024401e4107608030407045d0340020004150719400c00c045030400109d2203180c03200100070f4a80700700c0c14810b4083c3e010040654100b8641d04407007603030b0f401c940e50886c001c24500601644081005015410300032020308000c00c0060004540300312170900f9503d41000803030840340e5208010400082c140340034043c080c010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 406044001 1250 406042751 406042757
    0x1305030c070513020f0f0318031305090f160807020c030a0b0a0615050307050c010b060f360409210203130504050c1204030e04051f05040e1911030312090607 69
    0x300d542c0e170841c200340c0d0162071914000c1d4540800007480442040e41c0d6040c6141c0705031b0980781d8440c00c0c0e082100702145607020b070384e0084551000250003064100c020b1402212000d181070182100f03c5021501128003d0905086008182400c1c2c1c50b074a040164000c01d40c0308640612191800341100000c80304d07160b001c180301c840d4449021100c107400ca02181d401c5142454051340d98540c3c3c5000a01408a0025847d0041800101090840b041001904186258403075081c003104030841d403403008034060b5149440507038004004a40c07a207400d40c0300c0b059440c0300b00021484160070300c0741003c0d035040c6e088008015070000603200621209441d0100041e210882d01000340d42004809102540a0010781c0742050360383d0000b182c1407601030100788500755030080090020389498a860004e92100d0b0000d8020f126610002103900d103003902400e20540405d600821050304c004518201c0d0103401c40c010b4a6640300803241a580d501e081c80201601c1d41101d05140d07950400c0c420846c03030110010700c1d030707020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 406045251 1250 406044001 406044007
    0x37050108061009060c050703080a050408010e07030503042c011706010e040c09090809030d0e130623010908010905010507140703020d05130918020901050a030f0b1305030c07051302 79
    0x2081c2d0f0854114000d60b001890b1030880c0c5046072401618085058001400c18100400d0303203865076034850010419110340d08020304c140104080c2a1b035450717069000044c030170f400c144014014001013000c2100868a07101c4101000782450040404203c020703003110b44420906401921a1482041707402d0040002c400007010503c0c06413603c0c04848402d004100302a6201c060130f0f0140b10250040e0f4500044c01000d030741808403c0040680800350740308015008444420480b07080030f0451084030100c032048030040c2026420108145030562604c2d0055040c0704520602041e07100c0240315410b40d481c0304400000f001d0500c0b08010703040c9502481c90b000c1c0c1c19410880100041e030b02044851888031641022034440c05074111402003001c6035003007090341c10301d04a40c1c2c014514280b44c1d840c04d410f00070b40d0721600716620760702800900304040c00040e0030710f5240307400400000e1408480a03030040c28250701001c000c06c40c6e918507003158000010707080c00e903111010511162401c81c2c00882100c1482204610b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 406046501 1250 406045251 406045279
    0x7030b090607020a0602030a1b0f110c0307030f0203070e010e0603070e01060509010807030e03130e06092701200c010b03061e06061e0418020a0c023705010806 70
    0x1d5a40f69141d03005103da9008004a4008180c89c0c0140d1102c03400740800c10300000207082c0043c241d0003404a00400106502070681c0102d5001c90f510154003000380c0502420b038150f446104041d0740c10b090490301480f0394440060b86070090030a8501070096060703844e2560030110b040602e4240160030048a0015107001002002c0e0040c0032191800f4080c241961540e490050941c024100041e182c80640000500380c48201d06284002042c0c44e01850458603c2d1a000244002c90340300311f448665250341e64003100040304d4100c424580c002d90072800030036008850300000042c40300407002c05081c4400403d82d001041c20a004600300130806400501381441c00b400c0105100410300d44201e00000b403900883c0c100d84a40003219400300c1c54460b142d940031903524280301503920603c20000b82e042011000e1000d4032941c022280040c5c1c007551809030b110090b0302081a612041001c802109900b0420444483c0c4d520022640801c3e4500309698814030301070024100b28002004607100e2651040000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 406047751 1250 406046501 406046503
    0x7050a05060304020d020f09090a06140702070e0406060f03030903060513260912070302100f0f030c030f0e0d02010606170f061315031104020c071703130807030b09060702 75
    0x740e03c0364040f521690010581d0010940c44007120b800c544d00125440104050b8060000d03c0c002c1e030701d104880c00c00606ca90740700010380940c1c2c10307560440141c20149e4204038284882450380c6d00b00f80903181c0000c079165902d140300080340302c543c4102c000c01c561900400074020a840340b036601414028402408080640d1844d44d070052403428950300602c03120110403580e038420255051100c010301100715442c81c00d0403050361410326202c1284200e201c5103c0d403c5151086510301907a440a0f11040c08412a0200a4000d003110342c1c4500304069540d00e0950030f1201900455091a420a01403c5124007000d002402e4650503005481841036404060441c00c402071ba01e9980060340c3c548000c41a05c1d8180015103070390b04091010389103400c10001030344d100e2460600030200d03841910b02c00300c540f0402c0c0501060340504083c4228640007071600300305030502007514007115400507064034680a01c51040300c0500503c3d40000d46e003580309071014004c1101c0e42c080706400201c1ca60080580d40b610080003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 406049001 1250 406047751 406047757
    0x120e070303110c04090605091c170a0902090f04060609020c0705060a140f040612092a08010903020114130f11040603020a1d070503160804023007050a0506 68
    0x18108007402d46441e00003401800120b0405000400504c0004014180030000e88801e46110050b0702912a48115103000c558049003025560b0710f4001c0c0c0081110140820800000d00c0c890303401d519003003094016601c1004583c41101c8441e200720f003900f02420078104403003880d000380b41c3d0030303204211004540c80c001480c841199070403039001e5903803921080c08442a100030480c0a51050f00072400d034054502002c054420746000350f450006000101c0c2c0948240e40841c1005030140d00301454801c0c8070340085034406011104441c0320381e00580c1c0c03601c0c4d050840e00e44480030740050759203a05c4e50000044a0071001c2e0811081204c00c802040252503027144144605401400c4440e00000031139035403110341199000b0350f002008129100c3d60346401d1207040340c1480c0034070b4951031803000041465028030240e0303000b4420244020b030039000d0110f00752403c02018205076404620a10803450019101703516203080400782d81107500403000c0014080ca810140e0704914072a05407520b05200c540c80c0d11082d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 406050251 1250 406049001 406049003
    0x515070609170a050a0201110a351006031d15072a05010506090114040207021906030b090c030106080c03040219090b0117040803070c0c2103120e0703 66
    0x10024401c1941d00c1c000c0e001c0004903501e0100c0c95000b00320129410b4003c0081c0c0020340170b9800a000c6c800c40001c801ca07207440341c00d94050100e11903610b0b00f5440c0c0300c204001c54180010b0034290720801c00d0000340d003e000000300c40b0303901419965401802000e5050082841c80600454000d4070003000c501d02a4803000680015050550004009032003288641410b80152a01e2410103150b100a01d40c2d01640030946601075400351300340700224680381840d4461a04880103034007080000c10a040402010358441c0c00c081c1c0c0e02c40c031b000e040a1096074109032104001c02d443e0720000752140640b000e0002d0302c0300003800c07040210414001007011541207900b507a0302809400446580350758520028050320b4414001070900d01003d030300800c0c0300600c2c1c0c0c011401c01d8800d880b02e944005000e083c0d04103c0c0403c49005101c010140701046555010310040c3c19200d10401210b48020389410f000c1e02c40308141047e4100c0c0c05860306100d81850b4000a00c0032803003840c00303024803100e440e201030b0f81c1e503500b510701c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 406051501 1250 406050251 406050263
    0x9040305071b061e0806030c15130f080705030a1515031a060102060105041a09040204021c050406050601050a0c170d1517010605010c0308090a0b0708040c051507 71
    0x120030042010100750b07440000402800070a0050301d901c402414060803804803a241c1411040a4140d10b005102d02c62045c1d40040040261800100600c1035211841d00c90a150040501c140c20070306e1002c2c5120390190071101042251546001e851074034049040c1c1c09240070b500039040302030100c1d8510b9050584000d03110b0340400d21100d01480021514110391016000a40344904540001c01c0b0f5421030703001d003100340e084074203d980358001c110454401940c018580d0150845100e601d060501000740d125000408c01414001181481550254811031020300582e640c2c1c07c002c2080114420300c0e422140c00c0c42c20a040100002c0060314030592410301409451080c405107401480382021128100c20003c820312103102040160310044e42c1c50f009108588440400c40042c41505105140848405a46900b00c1c0581520260340300d0750040c1000c65680110041c0401080a08420307500407020b40e40c4510f05440e00d8280302010b5211030704503900c6240c1080d5070b22040d90010301501c0005401070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 406052751 1250 406051501 406051507
    0xd0804090506011e0e0a06091d130203010e070306050c040b04060c240c0e0301020703090e07050d0908120907030b07030f02040801050903040f06050306130905250f0902030609040305 80
    0x6940c00352400803020444d480d000070340c04601354000300d03004d500c010a030f5101500ea40c40c0d803400d65500a2900815002412159000c17225a5000031260f400030010800040c0074140b940200e07094502c2e95050032580c0d48242400c1082090f14403d80364441030249042d410181010b40f42d040d0780c81544121400c0060104c5a00c080c000d40000030b0342500122010070101421515058014003035000720709000c50614000500300b81418000c6641d043d0781940c0351840d05c4d040004480e9020406413010041120520521382c06000900c2100a80c900500c80380d520313440c506c104a10030301d00043c08100c640d00035003010000503070300f071f954590007004606003c5642403000315620024011070f8402c08540d801c09062101c50362020008000751ba546540c03100010ba1100d405803034903c016100325800070341c4010056152046607004e204034a102d081030b0b0b40040d0039840c5450118419500481160b4442c20003040515a081007560081ca01190150306510b4180e0024515010007800581801000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 406054001 1250 406052751 406052761
    0x7080709050c16060f0e1c0c0807031110150e07020f0a080a030b06070c05090705130b0a05072f0406061202071b08010c020118020d150f0f0212060d08040905 69
    0xf58208844045d040a810031a201c18609010341d110080300b000c0803540c5070100c0c0d0100c001c0c031404150a00c5500400990301c1e101c8a560200d078040c1045230703d8403040c016190030243c51107480c052580049860040d1703200c403900b1301001050f10ba42c0940044159801407481800d040f00100b40540021b40104041c3d0700d442240b030050b0080c3c00b00c0380490b076204070009082c0c000c21a640b02d002c13095031410340f029240c5544440041e5004d100f034038082144c41c00010020050b4907020001403a100a107444d1103410b040ca44d41d01c54080b1420070000b10203034458403804440c4881042c102800a0f50211001c0c815145408405000c80000e00278110003950002064018000b00080440340c1172480c0c0303d0756107080e581b140800d00911010802c1030065007050395181b0310a1182c101c081804d500142800b001c412a0382da40050020700300000114251241484610501c69100d0031562841710a405680ca40c0c4001d080741c0340290080c1401e1051040054074004a000d0005903004c0e03030410100000c803500c0ba = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 406055251 1250 406054001 406054013
    0x40b0f060609060c01021201060c080f09030a0206040303020c010f03061d0c040b131a07020f040f060905010f090f02040b070312020f030a0f0e0c0603190b1207080709050c16 76
    0x410302c1040d0003010000c1ea90b50007140541c010040005441c44585160f43c80d02411149210301c42c1000d482c082007031040200d030510340002041a0b078001401c488108880e98040340d4075400640c01907000da04014040f20555030007180590110201d85020003a030360034428045c0b0603441d5540c0050010b400070000030844c0010720119070150608801503612025100c1110340d60312000c0c001c5814034070074480441e1440301e021087d1410254000c00121502d80b44905010050010150350114140c451900141a0810b48a114042d10403494011941410011102d05940e801d2489811880c8100010070a688185044e03901c0c0030f074546802007070703100e034028102d010303009080080055000000501005e10007551218208500b02001481650b000d0075003035440e44108074035190401e000304001000c0da003d288050b41c0030518000c1c000f0700c901c407180116804e106a8043e41c240c41d1710044051184034020032029004181440e020b01052030001c032188c0c0940201c3d2070b0517141e031000301504000c00c66 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 406056501 1250 406055251 406055257
    0x307020301022a03210613091101020127020f0109030b0106020604110105070c030605100306060b12130507151e031a0a0e180111070c08010b0603040b0f0606 69
    0x240040c001e5465400112a0050300c805005004000b60402c05807000d04280101c00c1d2400000418a80d40120300322a01d0545107610080605030701940c1a02d582144428074855040801c0c06041580c5050324447c0000e4219134491511b1044010055039002480d501c1d0a0114101075050351078450f40a603400040c0c514240c4c45d080108200d00d82000410f95950014205106501824811189841d14001952248101c90020700112203440701071012a403641c025641054042e03801c00d002503566142c0d0000c032641600100c020a10015842219034416220241c0013000701e194608503191a80d80c0c50354850103442044842c10303000e01c003841d80a01504051000440002840803221006000103004140fa00c4450b80280030f0f113a1000c61600b0019110b506882140d80f2100319602c4605050503a0718001101c00b1080d901d800e8105e0803403236280f010300402071007980c2601031f0504000d400c43c2500e4000300b425025030414002c10010406080311180c00104086d1050450b031586c601040c4184 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 406057751 1250 406056501 406056503
    0x60e0f0d020621070207050a06021009020105090d05011a0f100806010207051e100203030c07030320040303080103060e03030c09010c0c15050705010e160303050f0d090f14060402030607030b030307 86
    0x1c440042440c8034540c2c0c0c2e4240701d11604c5258266070581e0b03154030401649076401d003c0c2c100180d001119080007410141d005400e9107005041c40b81c00d110103200002c1380c510403058202e03101c0e5101d1141c10f032620050703081c3c039060060803210010034506004c0411034080400641d581080f10210108007143d009204010203050041c0400380411403020072040706121a4000e10b024441280242105c5071000c41628002c00e24001c9035450060345403811409092403a00c130200340c2e1083c00880c121034000310001d2008512903181c80c01e01d9031440c1804030454007040c90700c0105070420401c1091001c540d0044520984003400c04003e001c1d1a03081c03511824440b134200c018802414514034840b940c006c030140032510b21840084c0000d01c05118815260401403140ba05850501c6c081400083e0044002e4081943c0690040307082c41001c41a80080d0340701440b040d2a0301d03d035051444140705c030b075200100d24049030030002c0c0418101607011a644940080c82c032010195a032441d00000c1d0303400c0c806c860300b503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 406059001 1250 406057751 406057777
    0x108150610030216080903100624090e010801060807060509150313050703050c030c04110706020f131e05060a122c060106031409060a1505190f060e0f0d0206 69
    0x2c542e6032070017100c076500c101c1549220780b040502c90f000320b2426009140070f940400040094502000022202c18102c5040360005d1200030b05005c40c4465515040302e00800080002142d0113140110013405c2c04956004002086010401828142c4030010410848004400d0465507603070b071011a01030403210860010401e0141c04800014060009506000c01004406590204501c08200801c68903805150340c1124018041440403940c107501400804951008035498400003c0c194013582903250400d14603e004003e2003c182c02c81d01181c40301501c0b05030703651842c0071115003020f001c2082c00d05403005081c0d2101c01022401e2005442045034a00140409094001c88841141c4070803090103006c001a02d0321a080b168003176990049402040c05201410113500e568000e500900a00229a560b100b050940061240c607100b11546401c4100d04219807a1803c14030120200f41069100c030341089241200c80200d07035110a44100798410032100b040e90050184086040b50080d020361960b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 406060251 1250 406059001 406059037
    0x5030c0c0105040b0a05090d1205180712170406120e010609020403080d050a1e050403170a09031403010f051e0d57030501020a020d0801081506100302 66
    0x403c85210100350140403494414400c6d981c1d00c0c55520303034404801c00d60074006000000001241145503014a40014030b41c200544110316003195203107030550540c00009040038495517881846004820a400940b42c40d12403468940b500900808114146148504584d030360400c0c1e40f200c0a01b548050003e14000b001503407610b980c1d003866040c40d00042806000c880c1040009510341825104400c1419181c401140f09001103140b118000c2c0310080c0304809000c0500514035082c000910a640301e070b205e84401103a000303c2850010140d00b500381c407515000c1400e10040c070440046140f8034003590416a25100e42000d80d8942201c00305440f90383d02e4220713601403103060078030550b104444880082c0c0d2085081014810040c00050155824801e4004807588030300090402011440390000c4903554144004a469490b45402c903400345070410090390110b00d550300c1f4240c0000403d03004080d0103024001415100140c604054001454240300b65180e00042d2300700c50013130303043d00c10b000c0c06002c030844 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 406061501 1250 406060251 406060253
    0x3200a051606030f02030906010b0d110318100b030d0f12050a02070c0f030b0402040902031c09090b0913080901050c030c0d09090b0f090a0e061e07020706050a05030c0c010504 77
    0x62003607002e005260001c1d0503c0d940e8500781c0030078001c480c040e400c031400402c034603840c1507a5441d83c0c0d00080340c1d40e9262600d5007051002017218002440c010310000d14004106c4c244184424a4284c51250150503070f0700744043d20109507004100d20003855020304141d080d018500d00c045030759010200c0035460300c03898002406000050742d070142040d80d218086080e20240c85030b1a11407080750ba4407006103206042c8000500600b81360300f01c020001d10140c01c0300c2084581c0c0c210401303d000b052074642c0020385292010003103020b081c043c3c0d06d00410706540718100c5050481004070024803401c1c0103400f80d10005013040c0540d100d0405c481014800d0015a512540480780f0306403121180c0940000081d034468020480c445a48151043e001c002011002280d440600780860550700824000c246640d40e080c110712900248a0244039407070180884804907041d005160000314090101c00440d0310101c404d00400c1c0c3c00c10112110b0b25010b00701940c80340e80300c02c1a202ca81c13090703111161443d424007081c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 406062751 1250 406061501 406061533
    0x30b06040e0114010e1f0f052d040b0a03080a080f07030204030b0a09020121050f16051801023d0e100515120303060f040c0207050d08040317120a060303200a05 70
    0x4003607410449d40d01d0800e01142c1d02c200000c200c0301400c1c5034164607411b1140c5280c5410b500007400c48401612503800640d5030b40360003156402448004002c190508100240314043c2804203611840700d090460400d1300715150020004002801039052903036400743c40b010740e805075032982c1403a00040a01c5140c00f5038004140090724041d01c0950000038001c0c0851590802d600140280120544c2e0b410309000d5004003400140c0c911980143c103600410101307604015480c00c407240d1300021410381410708054440b5051000036a031040d111554500000c80c0c2c0701342c201003030015000c044400041a2601d441168151820501181329403003840303c4040f0248101c0800614480e00c800c0760b1201c420203404047c807040c0d445030080400142c0007400c080c003107440c000c2840380300f1901030282c0604207502d9a461500180022401a5000202041c4400b460a02a4103640d01c030700120020711005185a8001c1d000040070032254503c040c0c0300d81c0c4d011980100701300340c079286500301007226030f801c0c121a1070f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 406064001 1250 406062751 406062779
    0x6050301060b1306020705060909040c08010e010c0e060a0c26030a0f05090a0819020a080c0703120311030403080711074e0213020301030b06040e0114010e1f 69
    0xa158034803401c5000244c45400412034604845001c0c141e00e180c204298104260014010070450320b100f402000402d00ca80c0910980131910411000020419894400501031500007942684241c400300311859907036500152b0812001e5012010354910740b190140859201080b15200000320340210400884510744c6c1c00200d1902201d410402507600c9903c0707501d4a0713020000d800740c80328504110181c0d0316071b504185071400084038415104d40d80002d685540c01c40d0700c8403481c036003c2c4c0d01000701803050207006e440c4800b44401c1d0341803c104e0340c1c8101c0d140b41c0341408011700c09070900080c0d030001080716000307016603041c40e401002610252611120401d12007410b40e05200300f008014414411080d01c00e10a140e080303240c000e1803031518280e01c3c004030740740c00503848101d030405000c0e544484c010415002135800f07948500c00e4048185030000600085408010721001540c2c18841ca210721071713074080c0416040d10800440b02e009640c0c0c02200c0c003108180110041c0003000c12440000380105440c01c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 406065251 1250 406064001 406064017
    0x30506130b0c070302060c1303020a03060501140a0f15051b0d110d020304090c0512070201060603110909060d0303020405130e0d02240601090f0e0601020f0d170a06050301060b 77
    0x18401d11a101c800040e441801102c000401590004000c2420280c0c0070002e01b1050368080310141d0b2161312680407414032802a0300450b80c1646900040c4030042009400d4101e0701000c1e128029014a44500310340c401c10144034103510903103070084a080340c510441c00c0302c07851400000380c0069101d00ba84280d603101c44880d4004002a02580100e24152000c990000f00c2085c0358000c0d0300301810500031000038002ca544000034014100004048000b6002da15442180d0039000001c0c1030f481c02c50040d00342e8800e0840c2e1050500308010a810746d83c2c031400c45580082e41a54200341c81d145516090b0000d02c6588c000680c44003651540e0600c0d12200e40115040d07a041106483c41c05145d41800c0e40d484140c1c05034001c20101401c01d03010034181c91507203140d000b0014076188800580d00c00f05040441c01580020380005038070010030845507010030800c0140c1074500000c20b0744001c1e44c04010048a01003903001030800502020034042a0030b80c10040c09407000400804c15190b60380c00d83c3c0030603071040d04e07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 406066501 1250 406065251 406065263
    0x6020a02121f11070f0b011e05060a0e030c060412260703110a020d1202060f09033114091506030604020a180b0a1106011a1303050613 59
    0x201a00c140119882100a031120b4900301c50b0407800d1074290103001c0b2030038041007680c0140104400304070783c9000d100c9064020740701e4520395410700341c400c01411040031003100320841d0b902080080d40c60700011074842507a00c2c0307048070741d1954181c0001d0515501c15640f0780e0208012902040b800c0e54000155105441024185d03504180340508a450700252000c03001c1c2e1032014081800800e009140e56003942841074281d4551000c9540040d08001c1c00344003c0d10954030f84208020110b40410030305400008040039241c07585495850142d90344289126501445c10000d8151031411503e04001c0c0e10010320b6102101c003548803c1c0e83c046041c0c01400b00e40c401d01b880d0010071a000300d80391400c48000c601900045c80c550302c1400b44800796000441200070040101d0558140310702000b0b43c04082c0a0908500795280380003d8000d0075501c03d9407171180c0035000b08004010046804103e0541c43c241e194030640c80fa0005c0721001061219903101a0480c040d20b030030018001101020004c40b544600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 406067751 1250 406066501 406066519
    0x816050103090c03020108091011211603151d0603010c110604081b0303070f030509010b1e03070b040b0703020709180321061706070e010507200a06020a02 68
    0x4004500b070701c0d61080054030030782d034081080c00503501c45d240c401e0b8840244021207400400105c0032400302d1300900088400700c1400304001a400c4a948614001044403c0180d049401d1040320b04d411040c0314005181416980c01d14a9104039090400f2070051003a029502d6030150002040801c840b4111001c1f80700394a0b1000b600c0d0080c0c0902d00354608664640024552a500da41c0c1d0195561f03c00007c000d814940c0c200d1200c0311400800045100b140c1e40e0b0340d1344000314070420014007500e00c080c0010f00d0036414030520014544581490100107103a80f582c004582c011080800d00b048900d401a0024200c001004165100540c00810505110360708603004e1560303920980381269078180c1c0b00507494040b5002c150101e88507000c810202819a0701800e04140c0c403040480480e4110351254a155580359010b0720040c4d8140850ba50107500780c200004510326003c00200700d48141031004003604294031144640e80c1c0c2c3c00880152100011340781d02003107500d03140043c0da1190304400480c4152122 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 406069001 1250 406067751 406067759
    0xa0506130212100f0b0a03020a02070b07080a0e04020309030d09110d0b070f0203031b0901300608030c0606090a0912080901050a1512031202130509010e090a030e0409020a0816 77
    0x100c071a24085a40c84617109080c00d40d001d604a0280d400700700000114401d221012410192107002043c0a610800f01c06945440c0100080c0540e140202c560f8403071403042c020001900d00c01300489510345901c000020340c0189914040c0031410400e40c50b1070b04450708110802c100484030107101c1c051003042d00d9140c0f03846400813089940cac3c4403c403040e01e6007021304200400702c503141c0809000510300c14100103100009120303404084003400c416010b4240b45100c0200d540f082c0038860040502181000745140c25250b441499940744054021130240e4181030009415508070b60050f0f00c901c0c0d0190540b0401c051803600244900d000780c2e2502d2055181c40046000b0503090703c19040c074910310740d01c0d03098014a00726510120030b0740c4407000d5050048540620720020400d2005080c0b4001800b2564100e900700414080b5510303050f003044200759101d6041c80101340d0005911440b140d81807030300c0c045100d141070105000e040e00c540000c0d0005100c2c0c0d008580041c000c00c03035204070340c090403841c0892aa6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 406070251 1250 406069001 406069019
    0x706080f06030a060e0c04050f1602191101110609030304120806030c01050306060c01151d070219060204031505182805070b0a17130b0a050613021210 66
    0x41c0c0c0c85581c1503105002c1d00340024034070b800414940d041d8901344c0b580c140103100402c0984400f110300b01e45041e6642e08004803030145020920b20341c44a4401805508088000d4070b80d580603444c8007501410306400719082ca6881030505103804400071050783e100d400c0020100b6070342e810584007280c1c1d440292a001010a220360b90042c807480004004200d025010030054a840d400640300c0da0f0814820800c00304a800d090180303900a401004c00c0c881c0342403400c1100b180340c0751144100300a0005038410b01050603400183c80c4000c01c2075201c100001c680c43c0c50002c0003071250b40d02c010500120483d00c410300708007603070065209005042e005140340150400c42031320340038920011195200e242e980540515440b0b082803611600c0365048800640d1a19280b607100d4215203071000009a40103000e48901c95100101d903005854060f858207650b502d0b030380c1ca0303410060007040031415a5031400010083d0740c45421001e0820400b2038115034171900e0f00b1003194100003c440d10001e44039034190005403008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 406071501 1250 406070251 406070281
    0x911040209090a0e011b09030c0e040506010b130302040c0c0c0801050108031803070f2d0f060f0e090705070506011520010603150e061602070902130e09070608 70
    0x1801440b96905540d0302000d5001050b0780351080314690760700c55140b40045004503e10b040d8600399210700161b5840d500c0e10240e011201d4120941c1c210058090000040c1c000070842d0549210028142d00c80040400043c00d583d99940040c0d403003400d0101501c02e880d0000c406040583c00f0755480da40554540e0400c03800c0c1c410a2103070b0758207076008001e01c03182d10054550f10b564030200181900c016568481d90f0301500082ca4101421280b101c01c002001207940c0303014141036000640500001501d403580e10782c946041440b4030014000e04110404089200300c000d0b4230f607214018001c180906003c6401052904144e100715014410103001080c100a80c116201211101d5543c40070028070401c0c50300091803145009400b1036484500c01301c0011998030305d00a10760034094000488d402442c4e0003903d04540940105617802c021501000e04c9903001c00c05805a554040380540e070785103a000200072094a9620580c0c0100c5c850050013441580410070104894065642c1c0c0e000c1d0720b0304041d081d0107113 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 406072751 1250 406071501 406071517
    0x11030d14090a17130f061e020106081f09060e0601170a05060a1112010b1207080402010903022211070b0714070609060605030307030e1207030209180109020a080109110402 75
    0x3400d01c602c5031040052400403c0c0081150401800003035179900e0803800c4048a4009802143d1030340040c00d00e244e4124200660700742984000c5c024103180c01344003a2a05c15401c2008500c64014410710a00c02c002d03002001140d5218800300130461071440755a4440c0346c00e001d610240c00c0c0590314010f0340b020002d80c507014660007101401131502c640f102400203041c1080c06034a00c3c24144035203a8204e95284c501030003010a418210350b13030403029031010903800008041d581400741c0c500a01c00982d034000c0ea0b4000f5298161541c1c410040194004541c003c90609414034060410504080300160740b0050041380c0d02c80d43c0511b200d61034005065410040318600d80b0111402071150170045034458000303244450040c840001c4040c6c0325404a030030750b40151425400f094008101c0c0a00d4101420380d54000781048015010050840d40000d5000c000035010900b944610b20106008450a500c040359180c0d00500c0b00c68165030703c03292240078009103c400e4503400c03107030888480182031900840d8140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 406074001 1250 406072751 406072763
    0x12071503060602070e060315091011030c030703090c0f1409181f020409020a08090d2f0c03060f01030b0a09020a031e0204020c0f1b031c11030d14090a 66
    0x1a1707060048103401103100410055061041a147c80c681c0444403103854001c50703511001d0a124818414100261000c080b6910024030003002086000b82510060f640c00034054580420401d146044c040801d0280f60420a0b03110b00e8200005400a15030b20000000c200680b9481c804d540d654030b060101c060803c1c3c2e8000300b9040600c18030080b6001d40850345010801010040c185a21200d42400302d0b089561403101060801d020322041300c20400440c03140360001d10300042c0c000e505220a0074001c41115000e8004000d145000800d0281031000c2d840b42d00c00070701141c00610741002541c42929083c442503442164540105101c0c0076240240d20306070b5005010559150700d1950b507480642103d6000441d1302c0502402c0f000142d136940014540059038000800086070782c404003a0038410301c61301241151a071500f85140e20b480100c2c0301100c14100100100501120740415038801485a02c2c0000a000004e060b12410708a9030100714010101411920302c1e070b6480d41c003561380e2402c405000d0b0203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 406075251 1250 406074001 406074013
    0x60d03211d06061c080d05160e0420090301140405011401060c08030402090405150c0c0d08100b09030709050717060306190203060f03070306090b3306070212071503060602 75
    0xb100c0580c030006807a01d0705c41e0720700502e00502420700d84110b50042d6034416080400807000d031042e0358840e5603040b2014040303030100120b00481418403a4100c112421152005000c40c003070500b580c003035100999120724200c1c0c0c012107190900c0c2190081222180c0011403030012000420381c10301c039000c5000b071141d120050a02d152100d4003003010f140c0303004000719014030586801e41c5801105840140c00b443c0c0c03a020bc02c8d1034158102d6118103103d480c00051017001b807910100a07034652410390a004032348000c50002e9480012300c01003401c00d02da03504a084503e06040a0004041c1c0c071060b65510350340040703840c040c580c84030303c10036884180c181c41c9068001070007140c85091100540c000c54003e0b200400c080c1d4141e0f64040440e0802e862a030059541a40e10040e46c8107200c41000c010340d20140304031521450440b04510f09280d070014002240e0f000c8040485800305840d003c0c00c40da02250000c1260b484144a554004e50b1002d01c4d0240e90f0204482c200c2c4014070300c2c00f0380200380a8980e40d8001d428 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 406076501 1250 406075251 406075279
    0x40f0f06090509060d1406060102063102010903020312091503192c071a040b071e0f0f0c05060906072a060810050d0209060d03211d0606 60
    0x1032400207000194020810b0040000146c4003596446101e000c5402404c154070b4044000790400034000c00c0046403d0746c40c21043c4600701400c50101c9a0081c0040d80d41c1e52079144c2c0012940c0c0c048941009416202d186000c9441d20401e03c00b801c800881210024003000820030045010f000540380440f90080131014010015025002140e10004100c1c080c0048000c00300c0c02070148030140c1c4121580d41101c0020f1000080f032480b40c1441da2500e440d006e10b000d01e07052100344588140c002c081d09440515050301c0c0e05808809a2110f5241c201c441c40071903c009003044000490880f1044500505c24040042c09003004000d90b01c1c07010b401020b190900201d52030300100301c0e00f1500700480041e024841700c03450440c0b010044000d00003c2e034900d8403528041d141210071001582005204a01c000350b107000503540e03100c203140d116900341d90328910b0000525042d47d01d1001e4440d101c2801c00008400d00001c992940151426100e410080603180040044075031170f00340c281c0e00b0320303081402601d00f58 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 406077751 1250 406076501 406076509
    0x90b0f06090d0204150b0c07050d0c030f031b060204050f032d01140c04170f030a051c0f02090f09060d02012102180a06030212010e0c090306010803040f0f060905 71
    0x990083c0081c101041482d0140c40742001100d00d50800c4d03c09100115010405120800c17820001c5d03d1b00342c0300544508456112603004c0b060600c8024080c03910284003400709482007540032040d07105d1401c54075100f85245013600c065001402050302845c0044402041443c0000c0c0d0076203200007159902c280b1401e0b8410310703415a84502d010211070764807500c95400483c140c0702d00a2041c40b42e1441591a00c3c10320480c000121a60000d80210340d00080201c1081c00d8088210741345000141011940c44028030103020313101203030404d000c1215243c812110000c0c04144c00030000c0a4040b0b4070080c0c4540340d03104210b41e0b1701d0305450142d00b0120040005005501803407040e414056110540d618245021400c031040c1d0b80444414103042c1318500c8035004500f0f00e0240c0700081c000070704056060411990761044075860510070310014036903e00100e02d51130906400c1320405180074056407155a16514400c1d56540701c0e00c203031013801c65410800034100c2c0481c800c80c000d689003a551440118a082c3c100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 406079001 1250 406077751 406077769
    0x1e0b040204030f0f120203070b06061b0a03091406280302040e0a06050306070c1e2109241403041104020c0c011d031207060f020a09090b0f0609 63
    0x558116500300700c00b00110700900c05948100d0300c03900c0690300e08810b5250010892a940d90300f6420343d407003441030300009400d1180c500c0d40007406892260300d074600ca00000c10303482ca04007100882805050400c13400d141d4004080f10503035500460301550949140c06100162144000d00c04051035401002d1041c40011078002c04118418503000d030500d0303190020018403010984400e01c1c5556210000c010303030704003072202541c4000b4138182000c442e1015102c00403031604005115250b4801089203804121f4510315184510100285240720320080316009071003583c06010b642507448801440810500c8407002402054003681d1710400300c0440c2c9642401c1e2a0800fa00444c0c4400c100501c0513039640381c03480600408200580100700d41a040e0001400707040d085010010660000440703010359032000074914800015044002d81d694905061501c0105012040049410b0000a805880a80c4004000c00782c40c40024100200c00031041044652040f841342e45400a9092141c00c07031520700091a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 406080251 1250 406079001 406079021
    0x30f15030c152b0507090509060f120f240403050f1803030d020414010305370507170c030f0c070503130801020a120504050705061612211e 61
    0x1459003010300e03a030000c03400c08003001504401544074a1510581c4801c50142a4002121b0700701182d1443c2848085855160001d01103409035155041038180d0784c03221600400c89095075829140318005134a04261108004400b4410400017086c1480c003060307011243c41c0c0500d5040e140d5a1505190b046c5048664224000000c01d40300c810300c40460780d4500b440140344042c05000016512800c200320580803112103145541018a02410460445404a402c81e082404071082d80c01060101300b0420754040c900000c1410641440c0c140710105400c44e842070505111861000119a00d10b1000c042c0703400100c4040c0e0101d003012012500d42d0000350002e101d17090059065a00e04440c0a21484070041103512228180e0360001c0d901c540294803154860f5024070481040c440c0382000c0d210150f07102401d0040500c90880041c070b109041a0040303c1c0f40d4503d034801040790f40c950990700050800c00803204998030141d0401a40101e4940a01c82c00d07143c00341004020140402c42c0010800422520303007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 406081501 1250 406080251 406080289
    0x1080f1317121b0304030e01210f05040b01241b0b0405070618030305030109020f040e01030609060c050903210409060803091219030309050a0602040b030f15030c 71
    0x86050300141d6040108518106031450044a040001c001540e8480d08441c04030700810501c00d000020703074001006041e1950901c3c0914100f10303113a5003000705480c00082807040390310304284045420390a4102034032940c000d1314820001da90300c0144624224a0113000c00b0400c0d0307040004040035000310b1245014044100c400c803054005541c1d1640b10400c1690f094a003075002c10400c02005610403c0d61403081000c0c00e001046a00c2c1d940c0c050468001030181d44461600400c450345840c2601f41a0380003403895610352025940d40c0e0405030000c2c0700e0568245c41c92424880f0b07404110307000300c04a900301d0501800070b14051100310b4611024060030b4a407009101810440001c014000e40500d41c06486500302645c1e0356030f50082040303140100b05402d5210341d040fa948414031400b000c443e0042507038050501250200711850002d0030b1170748010b001400c4a20215000c100803404101070f501c40c164088040d060b548615000c614051100500c90394942e0006000b481e4a04107a06e441c0c4030132003528 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 406082751 1250 406081501 406081523
    0x60e060103240f0e0609010e0c1e04020702040207120246150c0215010f1509120309062c060a020c0301230f09030f090612070503010504060501080f13 66
    0x46810b0b0680d9010948100360b984540c0601003c1b1000f823050302000070380c46c1d000b0001000d141000c140c2c031610040250a9051440102c41c9042c1c456804a07000d560340104115916030b42480c0c20a10030010300407201c0140308001d00d40e5030222800148990345494461405030038922084d01c1001200e0f03160f540201c43d8907800642d80011100c03200c03c1d1010340a074902294910203030720000d00d0952550880c0c5541010200100104000e0641000c01c3d5188510812510204030340c080d03507802d000c1d5011014140181580d0014141d10400c03101c02e5501c00c2d0360703400103c84030a40b000c203414012040b884213050340911510030340c03a08134008c1446e07050700d005482e104051200064210380d000100b6407900550010100310000443c0802a80049d01c180141a18201504526500e00030300424120005002881c80d803141d0f104000e4420b00104541a1585440d001d20001c281da042031194501440c244100481d0560141c40710510801c182d03429120300e5a940d0b051200440c01e0b000042c1d0395036200d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 406084001 1250 406082751 406082771
    0x5040501021635030103110307181b020a03020607080a0f05010810151406070812130c0504020f0d110403080a050307120908090409151503060e06010324 67
    0x9006100075600503600e826140c0c540c00c5804043c0001d12503c034500107007450700f40145441210989055a0300003540151801c11180400e04d00801504800b40641c160641d0784c000d808140c000c01019002c48040c1130006044002c16071750b540440740006e003d81c00070310026607964400c102d40ba03480803442c24041184070300d03070b011082180c00070380012400381c200542e42c131604515401180a4098051006040180f501e0004184d07601c1c2c00120510480c80003c1150501104506942d103080c52000000407500b41100c0341c103450f003283c02c0d0855070346550300d00c0014149001e2003690f80c607080c0040c03020b00e031030106113400008040e66400540c0c14007040c0008030120b90410003070501c0c2d0381d41e601c400350350f814440f1000d801601510141138060341020801070000310341509451112405850106d070000c010720b40964400d40762604155041d10b062400341c07040c1ea05c030301d04004480c01703480304110416810369110744941c001d000c060910545140780d8503519854800010119907600c03c00614030440e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 406085251 1250 406084001 406084027
    0x3030f07030503060f09010e0106050703020a0605010e040c05041e020c030c0d0c0b0a1b030c0903060e070512070602031e040f030c0302030c0406050112020c011413031101060b0702040504050102 85
    0x4000300541c0090ba012013000a0350621050400407032804031900352140d0726000b40d1514546050184c501003010100c1d00c001014020480c9071003096102005200b150384840008040740012a425507000c18603400005a80c1030038031910f602c2c1340c250141d0000108480103001d002c2d501081981c80345200800407681c0c01031040c0208404502d0903655034110030118102160518400781810444901d402c5c0300b075842554041101d1298009803c3c0425464140001a10b1640965001610b51414440c98414103940410a5800e4845c200c2d1b45815080a01100b03c1d628411801000301503882002070441c1164112001030011840354095854a5154058510341030308503401104c280007014401d104501c0c09004280c1c5405007650200859442c000000b000c880e0441101da0721603030b00140c42a0903410a4000040d4200380810302c4145062481c140000741107007640680008240030f816000403034040c0a6101100d0000111504009440d0208002020007520807266998200000300c0003000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 406086501 1250 406085251 406085257
    0x1409012109050c0910050102070302010e040b030706020303011707050d0b0c0f0a08331207032405010e0106080a0213120309030507060c030c06021e13092a030b03030f 73
    0x840b42024081107906001840001e26019041720305103841d609090000c0e980c00543c0e641140d0f0240f80902e40c108540300490024103800f0b41e8550540980140485c079150004000d6040b01c1045007918014003070f010f48540c54010a006e1181e011038030f50010b201040325055401e41081d41d5100d850b24101850891903e190320212905000c47c5840c400c110440440311102410750304800e4000080c92038106556800f25020b80000f4460030355000080b04401040000c20041d40d032015100c0c90442041c0b10030504c0303585200b02c6486072400e06002260b0310010780600c2d03040701c00d1500e980086488100d107102c0690007150000494100c016400514540408402c0c00000d0003070311594661800c40c2011030602e0115009542406040d43d880380009501015046100d9006200162114100d4012544507a01c840750b00c01220b101040c00300240c0703020b2450000319006040104042c1d00200030307200b1f0310034000071500356148130055084c0c1818000e410520001d02c000b130581e440d041c0c40da004039000360 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 406087751 1250 406086501 406086503
    0x4031106190c230c090c0c0d0c020f040902090106050a03150b0a0809010e0703030e0301200309010b0a0501050f130e0112110402030912070c09020f09040b011409012109 74
    0x5030344110240280640c1140303002d000c103c03100c8001c004000b0111229a540143d214560268280400107140c00e88480c003691120050841903541e40c1181c140d004180500d03000b420f0784103008170314404025141a1082440907940500003451581c039194055a258011105820915498100c50381c45a1030041030310014022480030280c5030705d40c10800400101004000e0300d0369030301d410302042030007000044030000c03640c0c1442c183c0c0d200b20112000c00e0141c414810700d185007001007800c9000708281e1030040d40c8100b94840003085540b84000170800c04031481c4c850325000c14001c0289600300700801c4020207040380d040340c0118031560340d00d0b122001c0f98803d0340030a19991550a1002c20020000c0300800302503400c550540c214200384800c15100e0750414040000401d00160002c1003200301445140104444802191955079480048000d13070b1200075003c1c030075440c01b03d1629143d80070780d414580700e00c401c1e00c00d2802c000c5c080006580c1c0f0804000c3c14010b01d0f0303c101d00d504040e0800e0280c60405c0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 406089001 1250 406087751 406087757
    0x30804030c112d040501051f1107060c03110303070c0b04241e1509020304030207120c0f0b0a080a0b030312040f030e06040b0304060209040605040c020706080703020403080403110619 80
    0x1c0305001c41c60955450b00c044244c851410000108015942c005802088901520114240740320b001c5007035600e00e8100e802a4001e010740e03000050580e801181c155040c81c002d440301d10700041c0d1505170944a1004607082400301d4607031082c11000c50422450150f00c03503ca529240a103500c102c00c00464075000300c0007000c3c8a40c5482c03894642041000da904003602c0301c0c081c144042c5407400c1c09580104810300071345101c59804000078040c03510801000d401440040a03c4107558140c0c18050000850342c06080d11146450701e0004001041208940503022195a0174109440e0310044001401025041c00d90511003889220040162980c1d068000c0348a104042c16480c450714004d000d5403051180c081c030504050100300703c03010111003200e62041e0701200043e40c4040910000380280700725000281c1117071509185895043e00000c80d603007510b02c5034450140507520307990100c2c10b83c49607000042010500340000c2000511000115560120042055040043c121100c04c22454807503100000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 406090251 1250 406089001 406089049
    0x8090414012606060f012a0201090f212105070b010605040303120b03150f0406050c1602040506241b010c08011203090315060602070503010207030804030c11 69
    0x8000030401d6401505001d202d0703805180e0403481c00e02c64840318000d0040c0c0c0144908114122241e00c01d01c41d804648150790800c1000780e82d5104030710b0401d4000e00c03081780403950700c52000c10748000325041542240c03100f81844000d40341480311000c41a0f43c26204031080c0124014a898040114940d842201e07501c0c1da4080e1142c0190629000161040e4000414040108030620210b03500c6404000c1c0d60190b0640490441c05100100e4902102140c042050714140e4091005626071034400a0056011b102c0610a82e00d80c0c60690189119500128251010004c1d0b0a00141801d80206174040720042c030075000b002299502c05003252400c4242800131200103568050300c1c0700040305000143c0480000c1201e0503d400c00500180740c18005c6220240c1c0c6801c1c203c040511404030030002d50750003465801c0700c0101201c40400340107913014143c098028924046218141403090781c984a8160f80c1da05440d4940d51000d030b400f149031100940c0c401d00f403034142000e1502d4140300c1022500344940c103100307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 406091501 1250 406090251 406090259
    0x61c0c08010b04110901021e15012d141002010b060c01060305061003110603090a02130c09082a1c05100c0815090c0705070e0405240f040809041401 65
    0x30440b0441c52903051020380174001440320343d0380041d59641103042c0b06120390a01e03040c802c185160400761002d5200c194603120011851100e1141589269040c2010201c18800060005c08088400b400b556041040c03090700307038507546030501c0019030a1410f4000061040382002c080350080d8442e480c1841d043c1e446031350800401c0001c0086503030100c020b10004011604640e615403c07440d400aa0b00c3c4203c4001c808904140300620038440504d50042c81034070b00c0c0481500400180c14454141702c0407401c2900b00099840000c41d40c01d426600b400b00e034641036244512101c085444508080c0d400c00d492400c50726030303504204044400d40380500000d1000c640860058400c0d9007900e440401000900810310482e502a2a04000580002c403412076650396840242c4e0b22900074094064140e00c01c0f10f07000109c2c0000900c241340628000c07400e503040c08010508045071450010f2085000c4103c040005200b14103000506410500ca0780c29581750803c0c2031300103400d03210b4032065501c4400c09140104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 406092751 1250 406091501 406091509
    0x170901120b0126071707050702060a05040b0a0306030501050c040b16060b0306040501060f060e010f1413091509050f040303050c0409020c0c091f140a030c0305100e0c09061c0c08010b 80
    0xa4080071403840201c5d985032000f001080c41c010301000031301030b00c00885c001c2c0c4c505014000359006003c0705100c16480b80a141b80060160001d444242c1b095441e1402144088003d20b0031901950251802c00d0b10301343c0c022840600d5014041002c1d102103030345528240d40d6660922506006501072000400d5083c240940307250200c0c10399012400340720482500380b80701c2e40c001951403a889650300305009000c080c2004d90f0302502c21081504070401000c6d001007000442d641c40501c06180050140c40d4a0f6210f048400440e40c06686a0f50720880c10000100042d22981000394082c200961607400c00740c6e2420920241c0c0c00035143c102d61904410800f90740b90034000401a84400c001c0450408403050102c803d038040d4650054107103d0700b54244040107501e40700c802d140211b034414150942d003641e81c1032141d2a038022189a50105042c013000180003140012284680c1e00c1c018640c1c2c8854a8071000c005241e82c0e00b000015040b03044155150204904101110081804500100b140b10460b0204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 406094001 1250 406092751 406092767
    0x4090b0f24090105010c1104020f07110402121909080315100f2003040b041d0a06050906011209020316052412180109030c170901120b012607 62
    0x4414508540c020001c06503481c035100c24115030080c200031121600c00c0c14201e03001110011030b0b94000d0300004100508030940c5d4001c0141c10300a4840c130000348078030300401c001c0e40704a905207a40c01c030510300490000c0080020303081184415481c002444d6a441e40d510070395400031200d030f00c002d42c0c0d003004001c81414222031880017030110b03150890946085202c0501102c01048040c0c564001405441c1d0181a041084901504003050942d07261503a4240b0b0f032070002e401c503d034040c0340d50749080440c0d00a4024043c440907240d00501ca12000d0b41c030403004403482d0403503000122006444100c20000340c0c0b0248484101c510452031400d8849040a00380501c4001c40c88141441d020352101400c54002c0c8401070781c0c4802d605041c0249161907000d42c00c82c80072407418070101694a443c45007010103400255481031a4400c00c02288010405a120200350140e00351443c0421945c032042d00d8040503039444150070b030505051000f104902550349203100741d6402d84e0380c0d0344010302000740001550000c0f40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 406095251 1250 406094001 406094041
    0xc070617060d02090703020d09080f0a1b12030203060d0f0c06110a0507050d170a0e1e03031c0204090204031103060919030503060a090203070305070905060a0e0603040204090b0f 78
    0x182c0c0080d080030754045040410020820404c241c0e01262401c000c10341038221001403074111000b5500e0305000e00d950340030b0342d0040148402203403c4c00c82c2046031400c08814207c17850b40000403545ca003144a00164080e42c0000e100301da08c1115240c8401c0060703440031000e5078887c06155000f900d103040040141c1a0604818100040c5d0f114030403140004800141c0141038440c25034050601c4206071038420f9004d0341103107651000100215601e100076074004c0060300c0e0060102c403105881410404d012102c0d80425281c190560020040340850541900c420b5a104060103401403a055490545400b2604290400c890740d12070071502c2503943c03178104411604506c1d800e0152641400b45044800714031680c0c03c0003003e000c00130000034980e59a403030810004040c4002d049d956403410220060040c02c02300c42082c00301c3c11003540403071103003085c80a0701c0b072071000c035180d080d800741124003001400d40000b8001c99126885241080018207c40c842c18052090196180300b282004c015600700d904c12000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 406096501 1250 406095251 406095259
    0x50a1410080c1c0e030c0f0106060e01091707051512060618010c140a030905090906150d02030109020d0c03031b0803070807050705010603080d110c0303010312050c07061706 76
    0x900103035049200480715034a200c011100f02410b2150803640c06049a02d520030880e00001c100108008030100e80d40505c41071a2000b00022625280c0680c2c64075820361180340060041d0030180203030040c984903031002441000454080c0c913600e40029949031140184001500b0001c80c01502c420a1640f140e5003005040b102e10381031085c40c408501c0001080d03031140741080300849015003805002036010503180c6102043d5040100103050182c6810714171b21559005001d00317400100e07208030109a082c00b400540188039042110482080301c000c01c0c0cec103004daa16558490507180140d03200c91058690034801c50043e8210303442d505002e0110314182c0e11840c400c10480c002100080c1020046a900101070708200101e526401800c407842e00820600a04075841c10f4004000d00c049280501516128080b00b40021142c40c40c0b103440c68018545034060991081c001400014021502d05481d04070510f495401c01000c449202c3c5429415809800070031100303c1c00d106100d44642c0c1c1c02e64842820740f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 406097751 1250 406096501 406096517
    0x31209150c0a0215061c02010c0605010b0403020112090b0f090c0315010e010b190507060902040203100e09030721050f040e041709030613050c0301111209010b130504030504050a1410 80
    0xc0880d400d84a5422190540f46c51664010110780c041d0344258a240e0300030300104030560310344445581075486400140e022810000481440130300301d010f041d04540c1c0c00030b986071040e226001003914940029000d07020038018601da000d555102042031030345e0344d1a0307007940074229450442807074150581a004050075440401050007084e42d802c01c2011309014500d4a43e0b515107090030204014012510005d602c1400002401a0310032004030000688400d07210080041e10b6030b07c00c0325a60301c1103010040005240c03c0c44c00303050511003003031140c1d613620350304089241024a000c01c1400d5401f40d0040c8030b0302407900c007c0c80140501d4000c03641c4060140d08020f86001807403400681d403508000c2c410b41d104408550b05d40c0802006101c00650440041c000340441350400e680c55160b1741141070208100306402e800141c1e0700c001400340401117034015100b1180b00c1d40110078000079103001003098003032000030000054075880344512000201240030400c520044036404000c00c60b54403190007030800c4810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 406099001 1250 406097751 406097761
    0x20a0e09160206040803060a15080406051f170109062a05040b1207180602010b190f030b101505121005090a0e0703020d0c05030d03050702031209150c0a0215 69
    0xa080f0780c1040d0019000380d240c0d0384007800210420555008213210300341130300182c94000d0300240700318001d43c40f030b00d0300380581d65403800c1e0b45443d01c0304a01040c01d51030b9010000c000141058001482c400c03902400441c24a000d500c60809581d280b022008030006c010101e54423440e03003820130804c07880d2130b0314261b4941403411404c1900750003640580d0b103141e80c0702000303d18480c0c09052440c140d091440d820708440c1d655241c000e4002c145480e032150051300030f40c5080001c01c0700d490580b01510a0b550610110038203640f52046074000c0244003160708080b00802140c120100b20386000307161007030390302e0755940d0b00903204182d000fa00241201c014041c10050503c05a960700c0582c40e404100d1010000e02004190007861030300000c0d030700c043c1d0803121240b030700004c0c00345180c1c40400342c03081501117130482a54100110100e90040300d0344001078100b80600d021030301c0d25040d81c0e80c000c1152000c482c1c141500548220a504003a110f50703041110010765600c00a4040c00b0202102030390720b0f04200d007403600c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 406100251 1250 406099001 406099003
    0x2090901060305060111061602070501030b0d08030c070b04050703120203030906040b0c04091503061404050709050c092805030a03020c0907031b05040906091802090601050409020a0e091602 83
    0x81801010189911400010b065034480c21915400c01c86403421034140b03050a030600c0d51a2201c182000005002c3d0480103d11940079015030380701c04c440680450a50340807526a4000f60300050112451002c0030059280030640e00041c26003d0303401075018000081c034500e40010064101c00b00381c1c0a5400610800a40640120715640d003e50004010f0f5040c1d524a44071101e42e1023190000c01c030051410020320184100c42d5525020317607100792000c11000d480c288404d0789001085030001c056a105d800144090036082d000b40fa004071410700468101501c1d0b200044031100d11014081c051408800104207074a0701484002c000c0c90140c0140c913a032442070710001d44a40d414810203004880b12404103280c580709501c01c403040c0341203220880f00d502d8040d03802001035110344070750405a0300b09000030400084c02d204076030014500130180507d0300040e5007480021a0010a6a4140441804001200f10703080c00204520001d903650301c0501240101000601407010345940507100065a2560350250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 406101501 1250 406100251 406100269
    0xb0a02160e040837020f0c0d0506010b090105090d0f03120213120c0512070321050a1d130b150a02030f0d11040905190c020d1206091a0a090209 63
    0x100009610b4902d081440018500c513042000e521109484c55042d1242c455000c40d0903036040d4072840a44555040b040700f0031084018143c4090450782107000100f10076400c0e000140f80c1740c40181440d5090004d140002568000002c1040e00c00c10000c52440b000c25902c610101c417041e03400340c0110b00b03015041d550005100114024100135920181d069403e000148250070000c0c00010444003e032140b001c14180c8809240c40708a420940d01d4810001210314118a54080340055841342e04040c40b2010842d40e4106403c050b4400074800400c4003666200d1000c1d01c00c03a542e04101c0400c2d514040f8042c0110405100c1d4001c0d81e20b0b205201d00001d296020044071013002038500781a0326249e0040d0080000d1001d00651032a1920021740021261405d802c528414044441d912012035a01c4070381c00140d5402e10705020044c2c00c906041520380b8000c11900c0040e0300c0585d400104140c40c0d003450313011281c01410340440c0c07079401d07000c140183c68962040e9019041c1084150b00f00b08404000c039a0f600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 406102751 1250 406101501 406101517
    0x1011151e10150e0d0606030f1a150f0d0b0127050c04060507020303040b0a020a03090815070f140d02070c06141602040b0d0b150d02060708030a060b0a02160e0408 71
    0x1041200c44000d0f965070788218000c0c0a40c0165041000556910780561a0800054211a12000d4002c0c1c0f030306a20065070841c4c440d40020741c02007460581c0c001008090300c44003c00c070307601c0000ad0b00d107080444d040002c0e81e406400c0810f540940d8842d000200100000300c07601150580b4100010042c0e1011120f0a440032514a41031480e210700c0144006421030080f41c020b1840ca10307010035002c0048e940000c504c0038090007a129120342035119070f138003511613010f0002d5015070364820011078a03081c8110840011865281341501a0b014290038030030316a800440c0000d035054012814909002e019990354006003042c3c180a0440c20340380c444000c4174043c440c5c4462000017060044010354451381c024204035040103165041c41c4246281501010000fa55598201c000902d185d1003581040706c81504015001001c80f030038142c5c0d1380d40380041903100078030050210b1317228240098002c0e8408007900804c5002d070081c0c03500c000c00c0003609030010300c2c65024885004030769042c0000f00d00030b04104e441003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 406104001 1250 406102751 406102757
    0x6060604062106080a030e090105060702061b0304080d1710052d0907080f1b072312040602060603060112030e031204120c0509061011151e1015 63
    0x290107000742d41c100512141d03120780d0080c0038441e1088205644001c00588810b8102d95a0980c1d90301d0b8428040c031401455402900414200800b1142c003c1c001030040d500002e07030040b01c3c82c0684410003941401850414940416981c0c0505a0000d415142895028a0540045000601d004006950f44604580d0349440511091000d1ba104000010051081324050680303485814420390090148200f143c9014511000e9400f0500b90780603003004120380b240540c030307440c108802619280c581181c1c03080c03130700c00001d0110342d0a050480103004105035024152038668680d841c0c414040d003055802042517100785c00040060120b1140e0314521000c0c40d8044c5051a003003040c4502007441c00030b101c12620648000403500196080303200040c080139500c01d6196980465542c0c2c10701c1511134040e51040c0d804a40c0e644180d4810b07225601c0d19a10385000b0b400c03074607000c1058804010900003030710003a0b0303001446640d4220004911144a8109200406240c3e05c6031a01c42c0500b11405241008410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 406105251 1250 406104001 406104047
    0x6230304030f0807050706151d09030f09031903030b011701240e04050109021b060411151b0604022b110105090312030703050c0c0c0d020402071a0403020606060406 72
    0x5482c402e105640e02d01f0380c410420020381c9011000209106031030320480003074016010302d860b20940311500c038500610b401401107007800c2c090010307a4599008a201607070175103e80c07421252030110040c150421203010f51000554407039400c0004200820210b85e89901c028480c00410000000b0107001d03100b50740e042e00403001e4550120003180c511b00000c0d1510741c41170604001041ca40700d29801404422100644800007520344680700d61a11800c0b14054402142c03002c403000d19003841c200d15a80d120f8650354080c0b41c046040002038190758102c015540941c0400304000450400a0914115400c1e0b030710b02076007014254080074400e82e110140200740383d00050011449074000c1c8150b0b003001000900f50b403060640b80400c01141d40088800b030000030f04100105015285060480300204244005001d10160100911003042c10160003203030425070070842000403c1c04650040f000e404070342014260390416003030091030070b4800b40200303102d071004003c10860385800c9500a40c480100c4050844 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 406106501 1250 406105251 406105261
    0x40807061b060c200705010507020402070804120b0412110307020d020307050d05030c12091309170d0507030b100e04051e0412020609010606090306021305040606230304030f08 77
    0x601411520740101018140120740300c01c603402c0002c481c1400c1e907201d14002d04c99454004569079850074492079010440410400000d0b0500740c004100081c0030344041c501e019982d40c4080404105420142c85242504050000300007540c1d11900e100c2d011858a1040f00c110440042d13200d21424078028464410402d1004c2113480a0220800500c002403511100040b0380c2042a00c5e0f901103e0340580b00c0c01079510341240e040000c0140c650340000039042c00f113240302d9100791400619808909072425000c0301c80d0b841d025a00200100720390048c11002180501700544c003d0140c50014980c24071480c001011a21031030351046940d00311020841d80800c81d42c40303034030030254a46000c1152404d90f40d0310404000c01e1180e80414854404515070880d4101d0b40d6040f605400c13100e05014040000c0c0703070070300104089462a00607140e8209145505061039035103130001411542c1e80d030302c00c03c0841d1502e51621000d07070304010b000542c18910a141440c40c501079400814100035030005805019010340496 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 406107751 1250 406106501 406106537
    0x6060c0a05030d0213150504120302010b040507050904141902070f1205070308010e010803030f07021f1b08060d0b0c0d150e160f050a180f05041104080706 68
    0xc050036410105a95071600079540c003501943c0310300c0c0c21030350780100c000001034522014074490b151030006a98103030030982082e0030911404034002e030a40466407900b502203000d60b154400c4038082d0280e52502903440d02c881052005545200140e00c450003003141c20426031142c95030740700d190b44482c82070042e03450704540340c640b502051003c2c01902d040102943c2e00b107019005070080042c0d50280c0c90301d07810750303981d0248071500d070000740a03010981e00140f000c500440720444001e50403c0070ba0060750ba06081d080491150240302c2154a91090740f41d041c40103450207140406820745280d03140c501211f103400e0000c00e002c4158017400900c610b55440001d10284900740585800c1c95503120b086c001d0060340c03201c072188681c00d4011040810501c40102d4140014901d4200c16079020781ca5001000105510903078039604041030b44418089500903615540c01c004846001a29049034444a10360a00007400222204890b0035103082c0c600308402c1c01032082c002091400c41c1e4251034060050b101c04080a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 406109001 1250 406107751 406107763
    0x2090a0b1e12070e040b010e0103030509010c031707091502030901050712031d0d0807171609050301062306090303120406021303080703020c010201051302060714161d070806060c 78
    0x58042d400350340c4021810031086841103015a008201a01650b6250070800941110a11000b404501c00b003011081550145800d184004e007e8101410030450119104681160840701880050b02101040c010940260900681d0012034030095040443c0070001078400c1c031034401c1c05400680701d6819085080e103c6d420406d01d060303510a03090248007821a1031680c1d0003100400c040401c01000000d0500c0b0b11880000c40d640090364402444c0340c48100380a80103a051001b03850420800381e2001c2819102406464010040d0580c00041d0500409034800111080500c0a2141c0c074100080700259a0010948108001d801d090b00700503241c03894041c00a1291186280d00349603800700010521035a4400780ca16240030741c081e03402e110440c5004900701da0b011030700c7c009180d5090942e4005800c0540180008500c01c50040440400e503400462034421141c1182ea81e01011410900080c4c45001c8405035102c800210314009003800000640020741c0100043c0c0101000300c1d090b60103907410402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 406110251 1250 406109001 406109029
    0x1030e010615051312170c0c04180c0b03071e030b04090f0605060406030b07140c06040f21140309010b130f06081f0509030409110702090a0b1e 63
    0x1082c04556140d40b4098625000070300c052580280c1110f0010b001240701d4921384000e81c3c4401c60303007010b040001c0303031161307517000314008001e50f12906c0c1420f24541c84d580320310503880f86200e01000c104015443d000c034100807030341c10480c07040005000380108190001ca0b800389803000760100f0f219629490004400a01c00b0203403990740203050a070100c061011812891421a000720b40c02c1c000740d035404d82800306940540c0300c000d021501010001d20050322800c00d02d045031130500241481e20204440366072528170280d81c20340d110554030305402c04124900c0c60300d040c61801c99008440c1380d610980c01615008844022856404c1c00000040080300d081d4044240c075500109000c49142c00e400e0306400506075540c4184610703150000c0440d107100d001941c40034001c0c4108180c00750f24100080e820240101500a4003a40700510011403d001d0724003a4414a04590256030340300d00700c0380100403c070180038180c010011301e070946000180d29450901c0880f440924041e52260f02c08001180d054814544 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 406111501 1250 406110251 406110269
    0x40513051f0906030303271403130f06020706080c030402040c120f0c02060108070513090303020702091302210a030f02030c0d0c1401110a0e0f0604090504060518030901030e0106 78
    0x10041540c50640d4442c00c144c2c1e00a5400f041300704a685005164010319100d0450190800081d810001d400c7c98406e110780d02c442c1d001e40381042440c1d90118040708094101101014034540b0a0104941c1044020020503861420340a50309011084400344d210140019000f40c0c0c5400303001031002c0c00350f00c1d042181d1400140c108003041004d40745000500300654145c0040c0151000000d400380006005030a40724020020459080c5031400b020017008003040841c1072503000d100344001359440708481303845207101c5160245110f40d10b204200450b18118040b080303000c0b1526018081c1d060003c0c9406400368981000240208141001d920f03500800500040d540b0440071034440180d802040c58038500c0c4500c528484440d004e020705401d03111004c9800303400690a02c500d410661180c600f42e2607080c0040c10a909004050010510f1a84260030180e400d0b41c40d94140810480148540f9500c0f40c581c0d404a00d454081c0c4401948070f105205100c0d04143e180c60020800705001e40c0510014400d8172 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 406112751 1250 406111501 406111561
    0xf04140a3210090e19021c0609060311040c11011a03070815070813020d032c060f0a03060f0e04020a0f08030a030908070b07120e0304051305 62
    0x504984007840d0a41d9909540041c000d688401c50820b54410340c640902030b00c0e180142401c0a103610800b41c4010807400e00c03050078010b10f0b1050040d6200401d107002d446098002e040d6920b09180003aa4015800900c01c18034144081000c1f8000721401d541001c0d0454020807014400c280c22a150380400c0000c006a518001c2031043d1000088441c2c1084401a0181c800c5203030341d01c44040d01c034510f00500c4900013240380c0000b46218071a035655a030084010100da4000015a008903002c409031402c102c2c0483c0c80f80a03c04070078124a0700c0b1f2400549a00b400014181079035011401c5c46c016080036810700034000c01c14000f0b050094000d480580000d0501802080c1d0318405420051130580d0305034005c1529000c080303030100b02106c0c1c41c0140c889202c000c41c500001e140d4224010500c0400030f481c00e800a03c04100010303d407509241c010582036079210340e0601040440e8080700e4000b0601c2e4100d52041100708051f840c1c0001d030042e10080210f00161a0b5145e940e0000201502e184071085940b01c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 406114001 1250 406112751 406112789
    0xa0f0f180e01091d0a0209100e070503270d1b06020c0604030809070e0105090c07050d020c10030207030801030602070f0c0b0d051509040f210c050606060f04140a 71
    0x3070303450a41291070100c020b0081140300d111680f50354083c1e20351900c02e030700303e1000715004d070601d41340160300504014800000d00360b8803003000f5465078043d80c2900c00074070004140464410800b00c40c0c038505140c41e41500a440d5a05002503644000d0440c00d0244403000e41d66020a039000f484944901d60004000d541d99014890605c2c0c8403482150203d0100e151000032030307008803000a0450583e0b103844400b0216900707000400501c14001010b170715680008005100004409218522020203541c0080c032150310040304015030544218418010188103018034004681d00c00300702070460341c006100503902c141a081c00742254405080203441e102804100107040301d501c600a011a100c2d2540c200141d843d4811181141e003030307810b02c0c1c650004882000c10003017180070042c480c1c81031150340308040c0c4851000e040c000940d8014500001309091240a10500001b8000315500c2841240d42c1e925144008046d15480c0c0128016050072010791128a8260346660b0000c001806603011083d0300c104c84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 406115107 1106 406114001 406114019
    0x303040f020d0602040801090209060907050a0c060b0603010803041404060311010e0a051c0213050907060f030608072c091c14070b04030807050a0f0f18 67
    0xa0b02c1c0c407140025034903c0100005c21140c1d001080000150040121007007004000a004520901c104001c080d440011112540102e00b045c0300b06610906080c07000302181907940d80c10440000000c2010f500000240c000c441d101e088400d801c000c50020701c01540c9042c8401402c080350011000025802400c9081d40107002030801d081d41565407001450540b605440c0300201000c2c9031107e015400e014a0204000008400a000d01c2c100383c0c03030b140da03100c0e003a120b40420003d1107109640c11328441e070401402030565008032410142c07a0b0f04141c4080c03c49070704011442c088121341501d010a4a5421b5102c5e040c4a0050482c40394030501121440c0e4504100394104000124040c0c9002c1d00c80c40500b061074090811485e1518103898003800f00c04000d80000d0034080280001121a0350000e0370b003100402c83d2a0003c40c0140c0c41c48203039040400440601d00c4501098004030720380381 = true := by decide +kernel

theorem cover : BRFrame.Cov 405935251 406115107 := by
  have h0 := BRFrame.cov_init 405935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 405935251 ≤ n) (h2 : n < 406115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
