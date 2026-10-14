-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3206
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:58:49.78659+00:00
-- url     : https://prove2.me/submissions/e769a566-6b5e-4584-b018-2a76a4eeb424

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 576438848 ≤ n < 576618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 576440098 1250 576438848 576438851
    0x20906130e0d050c3d09020411090907091415090306010e0f0709030c0b0d020d140106110f0601060c2a03030807180303030b010c050313080c0913030516050a06150504 73
    0x65044a00b0182403910010a40030b44203040c000017034082c000241640c00e002034020b40b4040045a2070004800900321440d4100d0b000140ea903182042103428140500c82c0c00303011a2024030131021440c1c0072291021007015140114108503405000901e410000c0c0c0c0900d003101541c0e400e11001a0802c507445900400390f0a14010340d502d90380d16506008540e11601a007000701040c04e00142403030743c0464004101150342805184030034041149468000c1c810840031a00c00002c401183c0d10103c1c0910100340c50b400507000603803a02d8400d5850415a9004944107041340b4846421800c0b00717420141111070b560303020042a0304500d805001100702410403400c0c0f0692401d080351641c4141e0288082d0f0740e041c6804101c490052005030b41029400000034490301011503003551842c40003d140c4100c450000848546403001e205114002ea01178481c8100700044440c2c0001182c0210000c02a164456804081600c0c603511254201000140221030103900c81c42e8032003840340c50701102805031600b10340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 576441348 1250 576440098 576440143
    0xa0f061b030206070e0f1002061005041103041205070b0103060209101e0c02132f0a2016080618060903120a0b0603010b120f04020906130e0d050c 64
    0x6020b5900ca00084c01013080103c108443d03440e90315100180f01080c4405801803810240b803100294403150101c898529000c4240300c0010189402e01a800000c13801013401131840e04c07643c50b03041d400c0c94501d03418824000c00b0018880014000400c43e8000d40c00342307038010f031036400541c20080da4909440104041000000020940c07070406096905227141d50304110a4205083c408201800c0100240a1403145070a901d402e840300590201400040102c1140b10001003962001c60300c0c2c051000140c001442954040208150103142c10b40207404030011143e260003040301442032060207403c8410650171900900060b0001c0542d500344000e400000380c00e5a1030807078240ca940380100031020740685038440202c0c0c517110103588140c80d40312000e09180d0340c81da114042c8403074640c40501807580c1050794200041d0311405140c0994001d82d4010480e076440e4592404002880b40e00e0840d001d13a050340c964040c410b03000100404800800c81d5240c041d01c030352008a4941c2800a842104d0b0b4644e20781c0f81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 576442598 1250 576441348 576441353
    0x90c080c04140d08210105040921090909062406050a18050306010f03020118050a030311100507080a180f0210090f1e0b07050705060c0307020a0f061b 66
    0x80e039050301c1c0168021071040002a00140051a183e08040e000040016640c07079240302901410b11403050241502800b43d85c0c44c400d0104564284078090540c0200a568150302a00c01a00c42ea501d041490458045501d901c100380456a0b082c1c0100c89095482c0703101e03540000c68000e02d407121030f00c003040c800c04d01c1c1c902440501584266000ca000b00910080d440348580494044400a00000760468580d5a110700c00044c42504901060340404c6400c2c0c000c44aa5080804400584202512080107589965000d035525501c0c075681000600400c888540030450034481d6a101e10380e20307522a4164180b00480038200c0e8036003c844c002c0c041c1c0c0d0b09456004140010440c018059060b21118905a070204080300d82c10603d4000c41008402050000341c0c074030400c404020b0319101081d20b4286246e4901004800d403041210080054100003020407561a00c0c40292100c110341606072450107410307500003040e0700d41a421240380100420b00a01c05103074400c3d00c1070350749104002e00041041494 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 576443848 1250 576442598 576442621
    0xe16081317030612150615030912030a020c0d120b0402040305060c030a02070b091506011d0111100617011a01120902030106050d060c0e1c0809030f16090c08 69
    0x4900444400300d0001c0803d0181d22070107130460201c07441c0b074161107081c00c0090b482d1918100a8072920300c40d00100d500d00b4000040c100840b8029510300000313100c081c030f800c0c8102030399810050509421990034000e03012948410320606100d40155a80c1e01521900c04142030100d03881540207501541c4180024400240300083c0e00d9009080c08016640340d42c0d945050002920038423000401c560b8007402400310781c0340d000a00d241f0b40d0f0300500d030b60542c59a81d80011a0031003864094002c41200202c00b0b000b055020b4540f80c455a40d0100c1690801c0201d00c0141c01034440d44c0e8858808496540f9829164030350030301c00c9a190800e05241c0000341c2c45c4e00b0f40000c01503040000080c400d25030780c185440455400358407000c01441c014260401c0c4100c2c0342088001068549071641c04075541011928841c40c22468840031403440999160700301c03ca503215890b0b69041005025050720030713640418050f010802901001d000808120442d0324184410300c401c0c0c80d07038a16204140319a45c400d04c40300d074044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 576445098 1250 576443848 576443873
    0x1060804032c18100605030402030c10080f0f04030e010e0d061104050301061e051201090b010603061701050105150c010914060108070b16030302030406140c030711060618040203070e160813 83
    0x2181b070b10503265200d90001a041a03150040254080340161800b950180c20104141c0b2581a40608090302d55815005840c0103108980090024150b03901c00092903000d02d4040303030000030180441010740744942d00c101c119142d2407072480380c130000400d00304128a070900a1101900000c0c08801403c900340d45810b4410b10240a010302c01c00b20602c0f1100f0b48142503201c05062500440141c1403969102c070040c008049030700840d0003040e40540103001441050250604840c4042d0508000c02070081034011141c008800c894180c0d5201c0751200e000c02c02c0c00e00000c400c03c00d550082d102d25490a4800784c60710304240d005030050401485045031403010460510706458050501603941d41d164500b501c02807840080b40c0b61569103510901c1024000b1030003640c030407402900c1d101c1c1c0c041040d00345c80d1307510142144c01960001400041d000304440c01400180c01c140301070125550035072035540c080c0100004a410303200751881da42c101034540350b0044406420131200401244202102d440760007a54a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 576446348 1250 576445098 576445109
    0xf0a020d0b06061234080f06030f150f0105031b040f0b1f03050703020906070f0c120303050a050c09240c01091a15060301060804032c1810 61
    0x407900007070031601d404044401248200080c1020340c90a04c41c002051140d0000303c0c401500c11860b54242e01c0600803401103225a81d884511403030361407001000201600400d8550980a6402c24501011081040c68403850400d00895428a4545400700300a03205030b00051107580042d0131070070b43c2d030300c040389018910205460111307020540005840c0904005110a60070009042c4c1407600654103180b4942050015903092041d52142c603c01c030180e001c2c41c901c0b95409030040190317000241403000c101818034070580050149a5a544026206d0b028441058000c0303a229020004034070514460079a028143e45121800e15591101144440d20075200300301c080c1d00c2c441180012508004191003d120810009102403401490095030308005214030200000008020405104034403101010126024003024116880d22000311008003001d0025001e22040c410000d1001c0191400f0b0494100c0518015000c250301209100c1c40f0924000380d03011491350304050203648070407114200d04070391 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 576447598 1250 576446348 576446363
    0x303040201170a09021c03031a1302180406170f03030412031503080c070f080d1e030b090c03070f032703020f03040608010e090d0c152009030f0a020d 66
    0x640301010f0701d0003401d0941c0060f5202c00c0600e2801c6103c602c1010221006100340e40500000f11041c1e00155141003008442c0d038420782d10b220015a800321640600185842a800b416510301c0400108007103c0903a0401070905065418141e60740004012112348400300130021495490241c9a2400d41d90080c0c01d02001c040d141c81b80c4040b181400c0400c80c0143d0382224007541e85400c078042003070791642c1e2489511a081d40b031100001d00910302042c0c1c1e81416841c0e455451401c05000a03c0040448041c0c40c1000c0c165a100c001241c0d03180c0340710913886002c1078174200f5524140410090300c5100b40c0c000311000c0505002807503010885100305050390744c10422503001c141c00b00340b40503810a480103c941c0712901c0081800100140d021500030304940b03180500082c280c441352003140e1508040c40c0c241000c5107071043d401000490240100c03058940304c40000031018018111404400d009201d109403140d0081041d403420300d07051203080c8230600000b00602d8101110380c0842c1124184240181c1002e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 576448848 1250 576447598 576447601
    0xa120b0a020f0714011a0a1d092803030b0603060d0215070816060c0203040b0301151215030b070c0f020904050a0c06090f060311091306080d020601090e030304020117 73
    0x2a203a0740d003925441940540700654058401a404d4002c06000340142e0302c024850320380e81140e003085117035a070640d10415400050084224220710342380308081c1c04041d0922520651020b01d550b0740c402c8030304100c60202030041c0a081030034002d080e00c0d4002d10141c4509002c10902c2041d59444818814469040d034109146000007501210a40668100901800b2001400540c0303e00c2105001d954140700b407030304020ba0710503000300301d80d00d0041d801703155203a03942080140552516180030203c0c00380b1038541401c2e01d040b00b030701c1c0c02c041d10039440c40e0428400c00b21a00703104001e285001350394001110702d4a4200054981c07036004485078003142c040e000e411a0310104003400001e008101100e80c11103e00301e5004d540d900e0061402c1e00b28032410354150801d100205030303207210303014171941c021100b10003606200e0410108251081e1b0704060501c526070314400080c1111040c45003850020a580290070705600d40110002550a1079550040d1034000b0010440182c0c2c212510b00070042e02d0380c0300c11940d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 576450098 1250 576448848 576448867
    0x206070c0c08100f06080708030307030e1e0313050405100603090c051206090601060e061801090f290c0d0503071214070329060d091509020a120b0a02 66
    0x1101036000701c441802000c1554038843e03401c1c0c01104041a076150100038a1359107101041c0c580c030a600915556400420104076010700c0798008032a0800b4050a940c40120307000300d40ca100e46510b24244106400104510b1604008202010300510741947d05000d02e18106544d0300003801c9502411040c503a903115414144a01420050041c141c05000b41c240c21410b801c1e19030b90b4510446008450b8440c40002040c442c0c46007041d908294806400d443c240034002c50701340e41c14143c0e84806410459403240018131080c0100d0960000e240141c1c0d094900300c40300c42c030b115101c00130a82a0540410401c1103544c40e04002501c44c0e90900c0d6842d10680ba510396010881c1c0e520070b908580300096082c03600f4800e044c6e54005045e4001d14660b10204041030640c9814440d51404c1c00140039100062142c035192401d0000041100b400101c2000803011440d03a11022204201d98002002e5580c0d89584001c500300f00c481c040142241c01c4814168188031b548000c44210000e0800010700d8001c10b0f030046 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 576451348 1250 576450098 576450113
    0x61401030308270709150602030a140d09062919090510031403031009050402150d0e061815040b16260a0f020a02060c09180c070302010501090204060206070c 69
    0x104100240103490b4500c0d1745590a2029000c0b024405800200303113000042c10038000800c882190303499442e03908599840c03e06201254000f03010720024951207812030710000d40988501412000c3c2c94503190610f03503005901102850b105840580610403400a0640394444401860101e41c081d01c0d0100309542d90b03a42c1200d00b90b045910003040f0456014140c5040380c8040040d5210b0428044003840705546c41c0c0c0c0d0b000035940309a401035049148811500041c0403c8402022004051400410140c40f880c2440b85800d40c111008240c4003090807080c159100244458442008044440700b041e060548440b242c54501a1043c40c051600550703040045016241c100c0a1071282d207403060640b1000e080305081690704640303c0300410300c0c00c000340c41040581e209071034010800381c0c002c0410360303903030049078481e030340320b940c0403540004002c00c1c900c0ba210341d500781c440c8607110340441d450703d84c2e419180c0a07003500c0041c7c1200c50351600511051000b02d07400665254045003030702d00910b0303402ca20f042110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 576452598 1250 576451348 576451411
    0x408011e05010f0302090f071e03091a160305070302040f0305010b030705030115060c020a050a080d2c01050706060302040203010803041a1206130e07080309130507020d12060b16061401030308 84
    0x101d011102084104000d4043d44101000303330281c0c080d81c0c3d01c0c101010242010000413506000b8214200c1444103540340729038841c0741e010005003030040c80c01c0c3e11403400d136841d1002a44100c4042c0c1d1689510030190406000100c01048281c000b4080040000b04008007149a4000c0358104000c040a99040d540c4038106403008000c05007840311f5694a56000039156000e180504000c100b541d4140242040121000030551003105036601a00c03444400442d903992152600303035000f6840c1ea02c04000340c0e40318402076000b090b20100079555585080a0030806030054031910724480740902410070b0384200c010180c0d40c010030440310311000c240580b4242006003040009500c0511030714102107403503100000144072348002191701e461003a170366003445c6c426108115070002c01600107406907042940602c0d024485541d84460116025403110544002c0360800411410700203588014071082c0406032040c28507011202588040305d604588003c1e000600281800d0b030500c8070900f0920302c000ca103140c0130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 576453848 1250 576452598 576452627
    0x2d040206030c07330b220f0912050c0d03020f030703020a050d06030c05032512080412031713020f15070203071502060709060e13020408011e05010f0302090f07 70
    0x700c0800b001c2d9011111407108640141130700c945405881001c61800302c41d00142c903101c600d0036620b000c1c041000140503064901880c50751a4840440100141d0300000f444100b41d17565855070b031911000310b001e5180c0444400c0300410b2502c100071a6840604442c00c07260300034250300300940e40e0358000c0c00c2140d551003520310700c154107481c00c0000f204000d400080d240c101c4a04404440b84107090080a55004004506189946940c0641041060440c1e8140080c89004404c441d0915031b81d90244038150803000821000035941400320185443d0721284241c0003000d10f1058089211541e0100b00d0761618110b4080c810681a2400c100519076071040743d001682c05016142490394444002d2071080c0e4140a013401340c000c5100249a840c0306040280407680e06a65901810b001403003405980c40040700490300c415020000070502000c00d0050182c100d9503031200d2081880d0754880102240e1044c2c000c95624104600c2c00c10150350340640c4ca58110311100802880d5032100c13041030b2000000c140f00c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 576455098 1250 576453848 576453893
    0x9030f06021e0d1a100509040e070308031807090204060e010e240c01050c030420060403061d010609020c0d140904110d0b010306030206070615050402032d040206030c07 74
    0x2082801d0f60b4001d81d0584424440030b05400c0c00300300400c10211003500c81000003503018418084241740130f8001c8070640120344e007540c0c00c95490351a4800140d004031001304105100c000d8101400d202000040c00600c2540006c508107410480c008040c614940c2d44e5a04115085503190099a985d40d1940703031260150307000007400c581a4030703a4002900000c0120a96510317000024151100c8442180c0c8600d5000c0004902c0480c185020307241800c40c9100c442c0c02032818040803002038114030134074040c184a1410521826903025900c1d0035108507820007000d01c4e00610100124060000d072041440c580340c03c00311079a56145190040a000b8003032a181c0c00350a0101c6180f035000958024001008208810711400f4040c000640565219100085d0800001c01c00300d004502c20354403851460780b0441101000d0781d9a1800181684c00a43e00802440001d54904904134110b040105100d1510320f02c01c00d9a282c1a00058014000180240b40300703600000d07a0000c0140c404440d9140123010b588 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 576456348 1250 576455098 576455107
    0x3020117270706030522080a020f070e06030c03010606081b070206070b07120614060913050906010503100e03041703130e01051e0d120212070f030206010609030f06021e 74
    0x104107507549054450600400c0c175000c0485c0c5c094107900d015401040031440300d104004090354500c04280d0044254800314005ca01c62400b103051306109280c024421040b6004840c10704008140c00d20340c08103107003407290b072400e24100032468102100d203a201103402c034814404510b00c20388005038403460306c009602800010b40c550410800007a07442c0500c0b0b5580d5084000024001e03060b007120071500038510703c00070700b0805104a25100d4014000340d90060201c10001c103034010444240c1c3c20540d941c0c1c09940003000140500c0c10300704135446001d00550130138003250035030310886910307841a4011000843c11001c4440c80882082003100c140f00c0e50f0740014981181c0d290994801641d007030003414401e01e9181e038000c42740310003801500d99003040100703464880d141980d40d90013048a8440b03204207502554481c0f6801d600c0b5003010300410f0340079084041d0030040f82e00d002401c00c0d00c1600441d0505c14680e005201007030405083e441002c0d40614010703550251106550485400c070360503101d47c1d680001c3c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 576457598 1250 576456348 576456421
    0x90306060b040e0c04030b13030309051c08070216140409120c0203070e010b0d0b030c040c051b06090604080309010b0d1208061c0b040f02100801030b09030403020117 73
    0x7801441268000d00b052041078641c0e505000c00e40c8100e1002030442d0060101050711151582e08d01d0010f80d1203410f0010b14820160350300b070304081d240100c1032850100854104003142d013042c902c40d8884100c0c8050465500c04407881403580e201030003035a41c90300c9061515520343d01e841d40055007c5410241080882080c041d005001d890b150104a01030f01426000240d05103a95215a060b240071640c59420804c04282d0b180007402d08901d241ea0611580b4050400c0c3d0f01c50b445100072142896a03102e650310700a01036078190311920701a10007140d120034100083c01e400030888a4010703501001d816980d454200040d8058a0a002c80b5588104145400020071a1200904c1062036441d241c3c01c503a17a44810800001d0314190b0301481c005901c00e0210000119400b8086501c00e01c1900c041c0d81080b400d402144140c51910000e40109480c100188144152004080d5011052000840c138250941c0c0c0020710425050f0348245111055002080c80d103210340f41025000d1070703401144c6a0480144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 576458848 1250 576457598 576457619
    0x50408122a070623090103020a200a2001080c03040302100c0f17061c06150b030402090c0304080d230a051807030c0b1c060e0106090819060c09030606 66
    0xf40b0448010405a101e4003150b134180219000d4070520000181c2e05101c007140040d0040c3d403005240b0000c21101035000d00c0c1100c110b91118246400507001000403961300d240c20541d00108030301d0300c04103851451411300d0580c1d10240780c0d40c2c4000c85195103607e0742c49603e01a864030b91036004000106091040e92a5403a0740012212502c4481e607480035665010000c4d01c02c1c2900c8143c0302c264112055000e00c100c0071400b044083d141d0792040034005000a00e21051021005d15500003007500d40f4000700380800d40c40c1c003056250304040c50b42107540c41c600341a525908680f02e0300c59548400f0751101d40225980f80443c11181c0b456414416204440c5001c40d01c000083c4022100721042414044800600040010f540e0082d84d0741320076440d540c542410764248240e005403261410080c0e040304010540c915901540c0e000b8030942e24520b1065050020160003041c942c1c019000d030398000003103015500d00b8000300040d01c0ea000100019030406020040300c441e2005e401c007908040c1065400074107090f62 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 576460098 1250 576458848 576458863
    0x60c0106060c0b070804050d0f05120f0703060501090f03030c2f03010501080c0604090e1207051011070b1611010915150602070e09010209040c020307030f050408122a 73
    0xf410400354140d03100720050b075001c9400d0b10080c0039944503440030020940110300a00d0041e0a50030018140b0041c0c07520540c840c2c4d000c032041c00004d80c80200740808950140104000307400c0c03d080a450442c10607036200180e030307401d22003c0c08101c00008510188082c4840d100c190079002c8003604000210515081c0c130314442e000ca4607010358a044000a402e484c007044d032802c021f000411980c501860801d2000241840c0540220390b4003600307a400520408800040514038030031005840441b0452403450100c40c4034050782a12000c08002080004100c5694154080b0307180100d0610320420050864003074a0480d0809035540ca030091080a000480c03042e40c1c07038101900801d00c5070946462580d1400452440f03a80e0147e80141c40502030505840d41f00c507400301e080c01c001420034282e00c0014064906141d00c0034007503000003400e907003419488201c0c180c101085041041c6000e10300120503640c0e0300001f216800b01c082c04584a900080b000d82140001840003004441d1215107000151b282d800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 576461348 1250 576460098 576460103
    0x50303071211090409080904180b072a0f0605181216031d030a0303090302060a1a0f030a0c080c0909060606070b040311060106030518011118060c0106060c 68
    0x41041d4500c000a980340900070402c4075071090300c2d040440b100c040c04058031100344129a1220107001603516074581c0d00ca03c0c403c800c450354014900408034208201d003020040c01e030504101c1104540600c00c1c40b142c0e810b551210001c1c20355400b046c003d0a007804a69a0500000d00240c00d00341070105400c0380c2d99051000040c08010745842070843d509540c16131060303c1800074035989040300071012034000c0c42302115080b014006e09142c2880c41001030b00b0145190006c0300402e030380e440440113050b1b040000315072080701c0d20010460820a1340542d145c0502098072070b03105181002100b007898409100d032401c999400414100040e46a40e00d0b10344901e60b2000072401882e82900044501000040c8180289000f0700220310b401c015440310003548034010019000c0c800644c100078260340003046498020000c1d5640000e19052135407415043c135440c800e450489030b04050902d240519848103c0301100a00a00c11883c4542900031841e98020700e88031844951a214000540f540c011000030103491 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 576462598 1250 576461348 576461357
    0xd0e0c01030b0d0b010b0912010e0610080604030c06050702070503010f02090306060a0b0304061112040b090106080a051e0123040c12050307020d15020705070305160b03190f050405030307 82
    0x300240c1c02d2244512001d8005004d20300d501004104001000c0f000b00f2a0f110043c0c02e042161a109030310b0390a442c808070a580095000300c0c208402c1050364400302001e000c2000150072141002d0714020a8a8001c0c8409020259500041038980f402004100010440540207000d245403411560009401075001d9034004e0066130006811454041a074005841009114a007140c8858a0f100b00a052020400e22400300070429014040c0010665520607441070074041c40340e180c5907813440d007511815440542c156000000400000d040446c0a00b4801c8021081e0390b2885844032099005d4034119584921618004903208820960080c001d4881c03801041001e618590b02c2280100d4061131100141440e002844440014504404040307005402090807210280c080d0300448100d0740022400c444603480b240b410010000148480a00a01e041c0350a071101494155082a284801410b10246c600c0c1a10f000c1d0048030f07a640f2a2110350714601e42040070740b400c1d00d4400e03a43d03031044c1c0b014030224 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 576463848 1250 576462598 576462611
    0x31e041707080105010801200a0306090908190912020910050d05061503061308070203010902090c0d05010b120609090a120801241d0d051002120c12040b0c0d0e0c0103 73
    0x920b014060348007200380400d880c080c198848c0c020340500e0b4205020710400c25880306000a41d021090084102c81800b4200540c0d0f11a007440104031040d1988030000f0038040140c00030042650315401103040d880c6c06031101c8804d991800700181c1e00e5030180e000030f0341c01011a20070700c090010000c0c0d00342c892016695150030b00c0741c8a908040d59020102c0707040c0300018402403504002910b04000c1c00d006840600041080705040d03002500c003030400c44114004007008140d41200c00194000c8500402441901c149815030030401c800141200605041c003501800380450a4183c04018045a0507000407900500d0031074032000420b441020303c06c1000d441d000d41003201c051180000e114005620640b1410b495410444000b00145030301b55003287d20010815034003002c600c09004135031600c3c0d2701400040e03a641d046d00e502d140c0c181000e4004690850300340003220040000c80142900240c002286600b40d80d100c10070f00215116440650307140e541010440c0107440c200041c038842008098a091280 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 576465098 1250 576463848 576463859
    0x306060602030a121413080d060602031806032707030f051b012c0d0215040f0b0403050613080702060a1106060d0b0a020310030c1413060503031e04170708010501 71
    0x181c9500c2103980c05c504a00c034000c20010200041203501d010703c5040a60b0400c0046c20000c02156040d82c8060096000043d100c440403890300000c40000c0c804998241c1541868905214490200741d904541038400ca021040104010054603004651101500100701c030343d40340031900c07251b5507141040b001500720080c0c42c582d0701800781603400c607550022607260506540c40150416034520301c20340d08883c003180c0003005a25010300010074003400f070201582c0d60b883c10440d481c803540c2c1540444002d1100703200a000003100842d2040e0803120314840d2110070f52003030401d40704520800388000e612110000341b2100036a00704082510245080e000d6442c01c0c0d54141c1400703e07601483d000107040003d030000040d0480000e034061500507030a007000301c04554590351032200c0d2800580064070720140312160003c09150540500c0d02c5440040014000c0c3c6c0e14080110340d503401050500080d45804c0f0b005014800b0561055500a1040b1080c80d0b000350400c400280d140c00040c000c002c555400c0a0001c00d9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 576466348 1250 576465098 576465101
    0x7030608100b0a0b0a03150909120509031608060402010e0f03031e041e180b132d0f0515010c02010f03060b031510090f09090c0306060602030a12 64
    0x84415a40182040c40020203505004240c940c40d0182c1c006032083c00810b034110340340c014210f6420261000200c0f01380d4030f0880781e4205002d40c81075040c0c5086c01100000a0b48401c055a102621824810384a503607100000742055000741c5602c504804104001a01d1007000074410301441c002c1c7c03030b0340e401c00c280502401007120014601c40c0c1c1550040200007003c51340180c06400c2782e00c0c0c1d55140c90801d07417600035103c0001240b05545079071715144c20041c041a078030000c4900c0180c4000e00104010320f2104082401041d0101040e50510b50350b81981d407810010200c40021107907070b0030140140c20303078103500d0340c00424034030000c0d1001c00d1400c0300003108040802444440c10300c0c16142d00c0740110b060303801141c02c0300d1704032100410551070300d030005a032800c0704c0041c6015411007003a00c8444080030081c0040f90040c50590070800003004010016040e1308000c01050340c05c50000868031141ca400c11559400d000e03032005200502c1d043c1c002480540c0800036044c40c1c2010b5899040081c058034a200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 576467598 1250 576466348 576466361
    0x51009090c090b0f0f04030803070807080c130e0c0702210106050607020f060702060c100c0e01260601020f03161b0b030109050612010e0a050607020115091503290703 73
    0x20f02d0781820000b602c0524030701e40140c0450981030351094901500c0c0d5070340340915007041d294400450600305c01e20940a400112642d441459101040e06004c2031811180b481080c4d8403914400d4810b1501043c01040d1890480d0341964010b032611050038100103245402e071540d4004000785501e410000f10301840e00740120388803541c0042c0420b101310031000c1000025400044100c3e80072030308000c07902c084641030041140e042c1c00f041c0009881c01e90a000a07008611004440d810370890100a207600c28078100121a41c40100c107000209640312070042c5e180c2840074809030304500c404501090010440c9103041c00f0076200d8842000c2e2928805a1200441ca140c052100286820f1005000b5054964843c1ea480300d401080704030380c4a1024032076070031212070703800300301d400e0f040150301130300b8007038108071907038008070244000c0190141b00d006010200e14a40a02c042ca00d0310f501490300001010444200035540000f00294000c140c2440724a5101c1c032010001c0380e41c0d10302e80020702560301074130564 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 576468848 1250 576467598 576467609
    0x1c260901020c090c070f15140f0f0705090409050c1314040303150e09010c08060f0a0311030708030f0304050106080a0816020a0905070f0801080a080f0d06051009090c09 74
    0x3402d1000306082004070b4031500031300c0c1d003c000c9400e0281d030010880038506a28100d02840c401d0600304000074020b8207440c504400d0403001452075083c00240d6081125065001150b40c520580c5611840e0044846206420741d191303019050081c844140040030074000071484088600e400c00129045201060b6442c000762000c4c2c1d1814080080c01284c043d0700104031180c03003001941c11030b070f032620410b11110b00d00381c4107212644c6d9520310748024141c0010b40e603504114201c0300b40c43c0352240b59000680540c2c00340002054001e51044601c4130b0b0301c0812044003c0c00c1c07400241c0c0d0b00c0f5500c52202044580045405589660a0403070000c2ca40d41c0100303d140340d8a80103441940303045141007001d00c1000d00003504a8000c070480c440050203088900c640d42c00b4012964428401810b1020010f0072410182c11034003942e0021403603080011601c41c1206d00c0140011081a2141200c1c4007420051502c0e60000360042440040c1d40c00d01c941c072894660903502800010010b225003034200329a40202030149 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 576470098 1250 576468848 576468853
    0x1020f21010f030b0c0c0a08040302010314160e130f0903081803030f06220c1d0a03030f020307060501080c1f090506090d0203070905160c030e0904021c26090102 71
    0x3071000c120444d5450740e002014070b2804c1d1500350000300e01885c02141c07610680d410500410140110f40e414001d00070701002c05604c02e9224184051051856203c501c00ea0b4244000c01105001540712541d40c980d400240072820400e6041e17083c4054081c0c101c0398000c40c002174601000880150068020b440850700020040d81990756050b40b8801d19100548003590109407100801108130030000040c0340c48402e07040101d408880000007902c0082544860f4180c0705004000045a4950091410469415140804441c03034045030983c21807040580140846061800100e03244000044041920006540300c101c0c106102407406103a040d01040840000c2d140c0200700064070381300d00540782000c4018010203000c209907000916103a001d40c02035001c50b48a204001460550750080071181ca0141001c1c4010032090303074024041c25150303030001c2c8280011000f05040d521092140001c1481454252030784a50900300150318a41c00390a00b01100b840c0422007640b50060070a44a5200041c0c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 576471348 1250 576470098 576470129
    0x1090e190b0d0b0609070c2a06110a0609020d020307060309170a08070e030708010c030b030d0926030f030408030f01050a0513050408130b0c1009020d1203090501020f2101 75
    0x4000250801622410401400b400600e0205c1c0e0548ea4015264260030280d800208100b0881c105282c90b0b5070105e01408043c0c00814100500420380c24201d40c0c3c000340028003002d5034030001320120b0340c2c510040c2d003600c10761038003081841c0c041d4005515240180440c00c602c1c20602c03040c0340c29100302454000000e0361400462246400f0b4080701003582d0000342038800d200d0b2121202e900711804181420300098551040c0b422606050191446c1000145800c0740298184880d00f80340044284c2100c401c0c006600703100d00050001d200350303021240c017401c0ba07551340d05040c2080e0181d41c005598040b08115050300010322480d0100c0d008040720006400440c2c5010000c800400034540100159400c0c18200074025289801c0444000648001c0c0c60b6140c47d64080e0588501d0507139480c20400081d4542002d0740003603616800c550700b10766489aa43c14600c0d4440710220007038051402c0041c80343d070011403601c21120258001e00b241110307042c3c0880148800030910000c0c180e00b071182c0d02c840028180c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 576472598 1250 576471348 576471361
    0x1b0d020108044806090e10051003051e01050a26070806040b0106030c0c02131e050105040b03013308070602010f0c05180f01090e190b0d0b 61
    0x4441e900c070b40541041d81c90f000c007001e1040101c2d11000603100310719004144000c0d1a40c5281c220b11020402820b9100342141448009004500396020701c411503015000000c1c59040000c3c41d12010700000b40861610b217401e404080c0161900b40d8042524405050072010f121741801585812241c00034030380700c0c0e2680f07005095844149414001b458004003801401d0310003d04000420080809500401c81880c0504100e41400f03010f070080c2c0d040500700200c401c00f540c0c0c4030200203000c42e011076180030081a81c0720917200610b00444800f210a121614042c003569186d40142d048035419601444442d10303e80415088440d0190b8055401c40300c030000160100721081e0200244401c002900c1185841c0c285544c60402c040c1e026000603034641d001306100d1038640c0145140a612406d2080c00d01480749000700d00c208882e0812401030440c1518038030180c1c4290922801803040c41002c032014280f18403800303000c2083c42402c0181605009a100c06070a040100c00a015007107413014402d6190750 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 576473848 1250 576472598 576472607
    0x24090506090402090a0308090306251b0b090f010e010c09090e01060e010b03040309060e0f01121e0213060f0503010b090d120e100801122619021b0d0201 67
    0x1c80c201d07400035428000c040b01c0d0303200d11424501841c061b019840c0c98410f09010985005001000e96020740c08141c401d818011013483c0c407080d410168248407a0800280003044407120345600c2c0501072032411410720200c110701103080c800c84181d000007801401c0392105024241c400700b007041800250720480420680403a80d004103010408070001003030083c0d8a0800c0b1184030800c2e049000500d50000600081542001701d83e40200301c2030524004034203440d0001120359008440f01e03414405181040c2c828000301340e00020800711084a010030b08011140c01100940103440b03640300b98090321102150450280080d4141500c2035501e1714516805d0a0811949401c1440600e41240d200425980024448540005100419680c1c0710030020500104690f40c0410f400c40ca051041520051140742501a04441e100e9001096030812000c15060121192800354009030407010102e00f0020003041800d001c242d40071103a0031200741c1d040d014101d0b41064007215000d90302004110a040055014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 576475098 1250 576473848 576473857
    0x30f0a030506030a0f0516050a0b092211040f090501050d2307062a0302060c16050a081b0102030108070303030c02010f090c0911120406090203100c02060124090506 72
    0x2070165001030255036076091700805010300c01c0350700d50843c03aa11204c40901d40c001d000200b074111501c82e10103240c000c69007641c0c030032204400d0140310303800c22010b54490327901c0c107035170320703128800c004000038410381c80748241a4019008454070040382440c0091498800d00885041c0d40d0024468001012665980c0183d00e203c10040304a00150b4500e4112042d0f050003a0b00041c1495110203443d0224454614075003099403200c8420f8402880b0310402090340052801e90124180082c283d892800150300c0b80317940f00c2000b00600038440c0034800b10070800340d50040d00c2c20b48040d04d400b4125040760100d07a400d0f80400d014410455014003420804244245c0110020100c83e0000051407400802c1d45d030261180b8960a80c1d520580041c00c000f240c4042c841c0c40f030701c3c1124484060134688200d0603694480e03c06840542090740b20304901056660600411a642030426410015100c2202c40a51030301c07424451411002010018140c690359244204150b1003030300e0303031100380040c00d01c820800b0b903412 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 576476348 1250 576475098 576475111
    0x14060310120309031a06010909090b0f060f0a090e0606010804051207080d090f0c1a030c0309120c0c0f09010803070311010f0204080105010315090807030302090103150e070f02030f0a0305 82
    0xf050390000c0415006112000c2003008080303180b00f14035001c0c00142c0114040d0748101151442c0030740d14000315020b20705070703600401c1304000145561220b500203003000d940403041c141d0002c5031120003e03060bc415400100300c0000c61041c2c4100e40d030b804005540511003140c014005070070648022500b0030b11400101149480b540001c0d041410050a0900712980d40000f141d45001c0e2901042c03d220340b075042ca20081c86140341c100000c480725030300c110b10f03404060300c184443d000110108201e610300344042c0d0400c4040082c15038036070b81e01c00305950f070f12403952034028081e04401d03142101c40d060181407181a5000c4200541c0780c00d02c140d07411202070800d03108503c0035550714040d0b130901c0b080c0c074002030000705169000400d241d411810001e004100310448142d031549008900310006074110300765290035406060042c1c50f1841180183d001e4007250305c0d4440e00e034160b018081074521110030110300450315549d07800b4404420000c01d80e600d104601030b071145803200344440078905100381c110507800700c3e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 576477598 1250 576476348 576476357
    0x20c010921020718180503030601110c0d03030e10020f0304060b0409120804050a05060c070303051f06050d0b060d0e060601030e0c15040801060f2102060d0c03090b01030b01140603101203 82
    0x5c003426078011145000b4900301c601e0740000007400381640c4e1060106481d1000c5502400c2049400c000203206513041490080c14951a800c1000d245a0300b809400300c40140c0f01420f5545000e00c222070801c5038412a8125039803850450250150b040510800108507404192014010790300f000a0b030320542d000b4000c56140c400c1c2541200003400500684d07024098081d102034a41003540b4016040e2900101101c4070100039490486100b40150054800c40704581402d2b9035031580d081e407a2015000462210750010070003d040752070002c0030340c850000703039a4480035101c00e41c44050045003a12500d00f40d9000c640e21a000c0d000c924901000c00c0580c191040c06e215203000d81e40d9498500391046a4841c0d0084c4070b2030901040003000013144009140200c1031402030405580e800100240203040200703100c40c0c0d0301c9400200c814002d41c81178003000e030050781450f00c540c0e403840c00200001d002d000b010201c0080400c545400d06107041603a00420400362036880030303801c1544030741d0301540d040029000c20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 576478848 1250 576477598 576477611
    0xf0403022e1e030b060702040c090803070f03030f1e1e0e010b0a060f0801030b0c070f1101030b010c021302030c070b010608060312030103050d140409020c010921020718 74
    0x30300a08200e070101d0000c980315044420400000d4429a0700c82545074014142800c00c400741d203644050480c0e00d030030360440f000101c0707541d10071013110041d1498004e0811403100186110611034403200c00b1000e24404c1da01401100c58a00901043e210010a2090301000a1124400c01d001c0e94011400b14503510150f140c07403c00c000d441105560002807010800d0350b4642030100035003029113001010382400c1c1800da00c1078410301c000401b8840c05200140c2110302d14004101d40c9020b030300441c4c2d8801d07082012805030280c1c50515810403903440184901203450007443c403003654081c0e040a10700d40c1d001841c80183e0b4105810500195100a100c1c500000041101c00c00090016042c2c2d40039010301c0d0369140b89842e00c0c0d01410701d4001900216a283c0c04188010000900300040c0c2140216092034640d1510003241059a00360249801210085001203410320007100c05610640090b07001d1241200401c003080100f0081c2d04004a081380140c00031001880840483c40e404a52010040b400150704c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 576480098 1250 576478848 576478909
    0x50d030e031812030406030905070e07050f07020315040308070f1412040507030803090f07050316090c0c05061812040b041509050d0b04060b030601140d240c140f040302 74
    0x40d17501640061020075583c884070814800100a42c8019001040503441c00d8113145101510a0240c0d020001011300c000503c41e04544080c410016218920905e0094500341071038080c103a01e004445140021f0304d40c2e1880c0c9109031058131031445442c5074074921454201a140d441450b000c00800650300c600c55808004001490000114481c1d420341002d440e00c4a0301c010628141b28095000c1482a4400300ca85900d03408060900301c01c540f1a00300025110b64035a50907031b510204008060b040340200000c1103143d8420230055040c118008054801d01c2150400e14400c901440c021010701480c1404103114026402c54801e8550115017014100d480ea600f00161240a1004044400701c1d815030a02c01000401d0141c04c1000c00110040c02456041070020340c05c0c0e604220640d84143c030750000040a110401041011180c0058691005c44510710440809051070403c0000084c1040c0416a401000d210541c0d098500404850345058556001c024040181440480c1e4044071030450a41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 576481348 1250 576480098 576480103
    0x1506040306090506090a11060705031c02130b1c020913050c1b030f0403080c030c011a0906061c3308150f010603110f070c0e01120804030b0a1b0507050d030e031812 72
    0x5059820210140e6140041080c040c0b0280c9140c1c40200016024430440100c801121008640e03078122000c016250460032001a06242030000c40701911481d22040c007070446060b40040545c100c50300d4401c6610340070015010342d00d10400c804a03202c0c49080c4424000030389180c0091490b1480300044070f00388422180724034211030544000201410260549580905207a02529800781044414904003c00c2141010701c002c56003543d0046a030f0b4400c205c10700c05540880c0d404000302179441d0180040d1030782103415948034190241c000e9a120302d0704070713803445030980c42540e214009042c100c409a07407070101c0a40c003a280d45001d10589000c28828420444100300c00741132160b00420b0120400c0e45800130044452006030003503025400c1c848103d10100d81d07208122000c0b250300440341042e41d80e4052402c0000d1100440034105003c9104602030003d601402400700341d030144050300c80516440030250210703404600c50350b4582c0c00611804040140d9890074000d04036003d800103084c660074408290 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 576482598 1250 576481348 576481387
    0x10203160623040c0b0a0c060902031e030301080709090c03060e1011091003290a05060c03180f28170d030b060c0a0b1506040306090506090a1106070503 67
    0x6698440d42c03007080103000e00100104010031250444c18508180c041008003a4800c1c0000940141d4030340c4110030840d142008111101000300d1101c5c44001e0190024945aa00a00c03900e40584502c95010403000f20328030a000810b03a201001400d22491a614034000c1c2151841c0340001d4010300307a0040001c1400e02440018800400100399108641010000220112090141018942058110644000d100c054401c1c05507804810308002110f0001d85c5a581981045800c1107005c42e4924041500001034400340011041d030345801c3d10032800b80b02d00d550340608600e44c4160018001c1304c103160312411011402c005140c40010349078840c022490f110704054003210050f484030203400a01641417003500340b580740440701e20340b410800c05085640c0c1c51004e00d010b080031001a011034400602c0390b2010500701c502402e00342c1c9840d66401c0060003032103045000c5e146405084005140038201250301c1034855030001e80c150140d03030b1250a02000d030308069030484e40e03840200400c1c0c890035200c90105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 576483848 1250 576482598 576482651
    0x2040902030411031e2503080f040f060305040215180a170d08010e070503190f020a030518060a05180703080405040c09060806060d06031e061a0102031606 68
    0x32100443c014241407401804060310f11284201074010b4111800125a401600714038051090250018040710b0a03540551391008200c13000c0065207840c81511540a0001c581030542c0030303c411642da0005405641c1d003210000e40c001014507001034103a00702806407060711010f98200304100102c00c08a0f0400060341c00564a00303201001c44e010040c42002006030140091400502a5140c01c0b0001081400640103106200b808000601d03803c005944071403130508401c0050041e050112422402903019200c0c550000f0300f8840000c0510302455924443c0c402c030800204001c0e910388144034000d24016020040c024449405818103600030001c800141d80240c4c0e01c03c0ea07462510081200711400140890240412101c0800125800441d0319521080503140c2e9940e0f10751a4020600410352380e00000c0c140d859620030b210800000101d4114958483e0320100800281b905032030780b0f043d8505000700d00580c801c0003000e00101c00303403903c3e0011901c0303420040303448a2015400c1014200c09282c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 576485098 1250 576483848 576483863
    0x212091504030204140f06010216050d03020f03041d06060c0a030305251106161704030c080a1809050c0d151d0403030f15030201030e1612031206141003020409020304 73
    0x20702c5810206030000321f41001c0240001c1125156259410741013000da4440c40740710b04a12400e14081c140207000c0010318062038000d4960b42c54668040402d0314110001e00340c0b5202008001907520f040103070803580f0241081c4001d04160920307540c114040c1400828002d2500c0c90321803401c2409165140011140480381c503000c12902402884c07616000c401001060095804040c0340a09034200000c0082d0341020a1180084c0d40c0d1418103942001c02c4010042c100040041c3c9440c03a154005042d044403040700500c1c080803681c405144054072415107541d51a0f5034208601103020320306600c0410340d81c201d1400500007030b41e00c0c0042028202d90b42c0004241d00000d070100020541e252240305d03910b0a42601c2040030b0102c0020419a02a150200030305141e640c0000711a0000d00304041e40c003954482040320919511031030380303030135442402e4000c40105403504240181d23840c444c0500b405449800c44580c010100c1d05040041d288516101b0105142c0e080001040b01c0c8990f0000354451800f6040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 576486348 1250 576485098 576485101
    0x3110901140307020a020619030b040603020904151103011214010507080127110406140f030615220906080303090a0305070f080a0c0c090b030d0e03070b0705070f06021209150403020414 81
    0x8020b8150b510100ae103e10840c80c05d2000e00050342c5a5200076003042c0c0280d038000e041100f03207100c0ea0080403891800c4000aa001c0000078403c2c9000180070640c40c410000c00310403054501d216401e0350380940d240404512010018441000e055400c400c80c08030800f072282000c4582c2c40340307078100c03003005003850310030038001030305001083e00142c040c00c80842c2541c881d0b141c88100e40d1113212502003e028a0302c039403106a0b0320796440135102c0944006c01088070603a01d906003040e04900c0740140354800d00c02800d003401070019540c2000f10941307201d4802d01028140703151040d43c04461036401032070100d030000d04250300d61780420141e10143c21a1141901e542c10301408a0034050400c50307069000360b481604141c48000c0c075803400b2403400c000d5912800d1145a48a144000030308083c429000301103a40070100300d10713003030003c0001c0d10400c03108016850b204103502c0d071034103d849140544180301050010440c2003028102880f0071101c88900d00d4007541004d441c0c0d400507059400700584150075012400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 576487598 1250 576486348 576486397
    0x72918090907080307110d0506070201090210031a090c0c0f0109060b0603090307030305040503040504110d060e01060c080a1b030e043804090501020307050a03110901140307020a0206 80
    0xc00041d000200c04009001a03490803c0b41c540d01e100d0b2000003041203060941d000143e403100c00794001440e605c90143c495520301030f80024001d0070007080c103034800c2000755121b0320070310700a214a0310b01d034250040e080404044142404840c0c040a0516403d83c00300700702d015410001404010350040d442800483e1641e0103040110544191210703480c4285030820070302206440010444a85a80c58100402d8139902c6007000b50440c00350740e220366002400c02030788018901e0004020311289403041d40c101b011a44480f100e5040c00024015100891400d503500d00c085070700c43d4013402c2e8003000e80c0340100a10860018440d08100605012404190400300c0c07120b103071402d8010603100c0c01d40981c03408642c0346001d2408403000d00c04801400e501e1020380750035190b0784460304402482030301b0100a560300c1c14a1034000303090b948040d4180300044d1800794100741414a0504442f6551816520a80003140342e0180500d568006003280c0158862030205c40c005843d2903001d400c0c04920340238a00c03d8556001e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 576488848 1250 576487598 576487609
    0x5030c0f061030050705060f0a11011b08041b030c06032a0f0e09010605120c04140f0d020a0b0a02010e010509030f07052404170705072918 61
    0x141c00c40c41e20700002200f920032684005283c4424000c444007208000c0031541000350078480582c1069410a000103035651601c52407500034140440c0d03607a2103802d403842c040350780d5013221600d003200700b4448050084184401d00c1030174100e40050040402d2038880280b00000488041d0640c0210740c0503e46a20400c5001e8042c4150a0880300c010014000751781c0441d1f2410440074180494014410003120301c1d8500c07441001381d44506c4034007902e00da1403035855040203005074102d0f0b0401401c400c1100c00040140b1205010f4900301c034800d095a40d8020402c00412000c0c80c46015800e4000e2644002000941d9485c814100105087e50700b60b9511211907100a0a480f100d0402c0101c0d681488207101c00791500100f00d030382e403500b02c1d0784058032621b062a100c1c3c1400c41160705030301048907054540b060040c14880c00c1c1d0140e841080300b50612860140f0040b2140220303203014203560088182004120300000803200b1050340480044851100d4400710000fa4100076060001c4182d1541c2e2900d881c00c14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 576490098 1250 576488848 576488881
    0x230406060314010c0801061b1a011a0c03090f061204060b01031b09180204050a1d130308160306080a0605090f030f0409020d021e091003110f0705030c0f06 68
    0x550002c4c819110408030252070100c062143c00200003050300c031a103111000040d150300180c1e000c407403a1884620318103940e966000038001e00e9411340e02420020b1407815918125040c90400101860401c4402d00401c81442081e4013080d0708800200315405c1d88600c00c480661149100e04c20001c0c007205580300040c00c031055103008410740c07941b2610000001d60401c85040c01c4580c814030120318503000e404000c000c2d019a9000035006416071801090076a0304114141182010302280040ca80d107442600140840c0c0c000701401040f18400800c2100e040c1101602d51a001810040741c41962140107514200c45028155102c0d50f84206010841409100c81aa031482070401075092a0910100d00a188214072030002c03284c1e030014111803207200f40d4040d0383d44460742150b03070340c0c55550f40181c0000b103600c41c2811907c00c0096031144281d084c001d105400600351f030b1840290402c898881c41005607401100281c0e0705103c103206480348241b040261a02c04030503140503001509000e144031182062 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 576491348 1250 576490098 576490133
    0xa0f020307020307081c06031401050c0f040b0d09120917060f27120403060f091509021903080c06070305042f0d0b070f09030b0a2304060603 62
    0x10024005220782c000107540f04642c01543c599134900c0c00142807a1071030a0360020411544c182003002003440142500a181000400020302442da01c03600e0094141c07255400d8446c0510301400184007440f0f28001401240060000018800a458840346003900b180580c001c002598030000740100c40c48100302225500e2250020300c040d040280010846040c0127200d0b400400c000c00d09144124019103003007118002c20f8050301e4000c01001c101e0211540b05000944245042c00401c0440051900c40c0400d40c0c0d81242920003180c000d480e0000c0681070a100c140d80c809030540711400c04282100c200300c0118840c09546640d001c61f030700200c4c10000004d040c91b040c1850041000040756464170721300071080c12101032a56160741200c4d810040d12544424682184a007030130482040400da05981c01001907480b044014110178404840c90041401f0040c43c074615540031a0f581603403500512203022919200440c904295085c140c10342008640a42d000e43e181c841c100240700c000d1101103600d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 576492598 1250 576491348 576491351
    0xf0f030d0b030609030d1838060a060305090106080304090b040605030a2004290405010f12121e0207050108011a070b07140403060b090709150315050d0b0a0f 69
    0x190113560f194690107400003100c585900d82c180307000d500e0180000034030301503400b0140707801c5294154030b89902d000105681e020300b02c0c44864180070510010090310702c140801021340c40c039036080c60400c401a040180584441d07640f42e0388041070b641170601c0600068000000c000410410380c40810003929456840a4001d8001107003600100b42c084443c043c0504074070300418a842c03c3c4401041c0188488507ca62440114420a98180d0340c050260407180408560a00c200c2e621410071141c0c0c4103c42c420395503d4003100202c0d800084802c5101c9480c8109810002c0340c2c030401c1705054503d03106018807440181c20203c014801c968000030014094078007405c06006241c81c1410402407803003080e10141400307100500180840d440740c000600d070650f81040729500d450b924900740010708100c00c4494892014000082c603854881c480e030341c2c1250441c00748842c003580c1081c010303130052400d90342c040d10b42c5039070304804140c94030f910615200303d5104501102980ca00450120121500b00701500c0308103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 576493848 1250 576492598 576492601
    0xf01050f0c040306020703140a05070c0506030c1c091a010614030402011b05010b04020f09130207020916050d050115030b0f0112110903010c03050613050103020a1202030f0f030d0b0306 81
    0x1003001005a40a582d4013600045e40c0e58007604041c0c8460124607203424120741c000441c01d502c241d0100c081c010003031241d22140c840c951034208005003400304030b52800364802c05011248110381000b902c24802c040041e070009480f41170f6210440c0540c182c202405420344600010046a5403203008900d80020080086041d41040c0c0d00081203407000000d84840701442103000c1051010030b5001060b2500d00800443d941c41c46007075031410a130088120b4610401500302c1703884206c04180216003815500406181d883e949002c100d8004d525207440260410a040c00008503207003880c400c0502800fa00c240c078030f443c1d4841607402400c3e10818068503005818490405280f1790704190145540d0300c180760b0108203580b142031240c00a00030080d00c6540f5600f003041203440765800d41d0006002d02c00c1982e40942c0c9100a009131001d075103080c4002500a04220001c03c540090701801d600918401000d554061502e44a41ea10300b0108081003441c1c0e80001841d002e06007a58804c0404041042c1c0140c9880e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 576495098 1250 576493848 576493861
    0xd090e070215151908010e0c09061903061404020f181503030f04030807020315100902030705091002060603060a0c200f030a0305010e01090605031e1c020f01050f 71
    0x2103003685070440340c84802290100748000d4440080b06001940038040034216043c0401c1c001c1001e80385d12500c079083d403030070800114500c0040390001e504c03100a44409603540381e00b02400114a00880012500b40e000980440002c0c0e0500442754102d10380c140355000340c1800d004102255448001d520302c41d0b1b00b2611424410400c1c4901c1075407040c480c8800309440e40701c10001c00e08521a20a000d101c2080c0020b010003000a2a005412a00e000780c0440701c2d40b80700e03070700743c0c031540321050ba00c400391070540c0f071810040121660015540302c1c03403614040d0700301005030000c40c4e00d0040c40801d490240e08080200055030408002d00c2d980298039401c280a07078150068041c0800050a8504004000040091010040c101300d401c0048038a0303070031a43ea80c1e004040003030080a0038007a81c07125088210000502c0105170151206a500007005841d00e85000c00c59500c4079401c80f1150b03030541c0203201c030110142c0912850584682d0041e00600402c13420079810a0866000a10002d010100e43c3c082c0180c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 576496348 1250 576495098 576495103
    0x50301030b06040e120a090f050f03031603021e0c0310180201180b0f0d0506060711010518040c0908010b0d120516050d030f1415010e06070c03050d090e0702 69
    0x420031016540054403100213003403d070030500840712040078032000040120305e40da8881100000c88000700030404129440b5407c004a1040d40c41005505500501251074240b80c2014651031740da1190044032030035020300d80c2900845403003c001800c147c22010840c06282001c3c0911180001d03a007000b00034030404c15448041039004084080d040002d0044104030b02603900e25800c4c050072207009019180c141c5a00c0322880f5900c03081c90b40c01e11030f090002050003800c06806540d40107900c10a90501052040011190b580004a0000d9805022500103902d034031103124000c0300112644c0d8bc0b088607814600c10074207503580004024010041c281074040445c03400c0e542411082a185045944c800c083c010002c01c003aa15100905903005214084140c030b0b416070302c910142d00d100c6d44103002c04000450340c040c01da0000c84034041c03803500c035881203a5650300c01c901550f00300500a00040c00c00300203450b84030024400b030708121503585c005612004480d800c0350510008290b1901c11030024038000c18000d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 576497598 1250 576496348 576496351
    0x7031512020406030605150102070602070339090507020c0607080301090509030c061e010501030c1202090d05030f07020f0607110423190e01060b1b150a1b050301030b 73
    0x440d031036055540c034119074494000300000e6401240c00d000604090f005406a0710654000c40c3c0544203500303001860034004035660080f00c1c2c01265800e81010780d62002441c04034000000510b03d440c00301b00038020307502850110301400740c0302000580c504e04400c001c1e187c90204491148100d0040c400c2500003a490001c890642c1e54001c40440d89444801d03c161440c010110030000d5030048100308088120307002c0300510780802c604045074140e44d0351300042d02113a420081c00000108449645803080c0240c4c0c0080448440144c41d01002c0c503101c0e1174a9055401400241b21a01d400040900075460030305c07084984060115141464401296580d65000016610b041d01407500e03110000303240c46e60609030400c00b5401a11004107840d1940c0103030017100300300400340c901600d04030508484200511038041a80d60030000720b498654401c03511060089001d20800e404d104110b500303560b0600e61180ca9014000002c408034040c000b1b2500b0011a020342e440c2d86080240910041001c186507030540c0c4d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 576498848 1250 576497598 576497609
    0x20070303021227301002071e051e1f15180902040606020d030e0102180f0607060c050711010e0d0f0f0203010507020f01060f0b0306011107050a090212070315 69
    0x645614103e0124558211081030f4861000d41d0070283c0003420030401101c250520079406035905040300c003c2460480c0101e80016040f07180d11090076000300f9a42035109125801034003141d1400b040f40140c07424640104482800c0e68002040398024104076556565880b8603412080c0000d070160030318014100403520903031402074400205025800c40c603601904a994000d4401d012180d20ba0f880039603a00c1241140c1c9000a20f86074020f05c03408018030a403885000b802c1044071031031001104111101c44d032004025481441046440001100c40c45100c00840c040c4c0c40d190340f5403003035080c61205243c907040741c14188180301010040b250380322210141d00c198080310540c0041c800741401c42e581a01c2110081d0550b28140c1800502038001806250068618009019890f03c8544940b5550310038440e0403010031041c400b01c1e0866018002d084a01ca450304104c8240580d03901c00076080c114244c8c40303800769a41c000780c1345070b91801d02e02c1c40607481460703400c0511621115580281140c4024400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 576500098 1250 576498848 576498907
    0x9060e070e0f1b1305030c010914131506020703020a060f0813050f060106031d0307020307030305090315070c060528020a0909090c0806010512060703020a200703030212 74
    0x14680d0b141c071103c200c20300f10325441900e03100d10181c1000d061000d503a0080b5440707480307850322010480d845020003000392102c14101000c01d0036a6414070103003c00c07042010880b552a4883d02c040c950700b0307504090040c6007560003000894614018095001d50903001001040520004c1c054603503004000203400c0241e045107040d451800d030231f1842c10030510040d081014018030000280f0f9580c03507008101c1810001002c4000b070715078200764aa503445600002900758000390000c101090080d009001800d0014099402c1c40c11102e1890300820401c90b444800716400007088000d0102a1184660020310095040e18808000246801d130b12100c0006491558000521155540c0319400f0180104183d64090201c100329240c80140400300340141d8010348680800002d481c41c00780c1c0304102000c10314015280c90f481d4400e00b2000b81d07000000c070200388900e10007141c2c4000104224500540d01c054080e140a90951038000c0c10800040100200c0403403c0c00300403400303012000e10140e840300c2c0060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 576501348 1250 576500098 576500101
    0x110a0509010e1512010603112506090b0108010504030e06091c030302040b0c01020c0f03030c0319111c1d0c010309110910090609020a0e062b09060e070e0f 68
    0x1600d070b4603003280b041c43c1000000c00c5003036482c215004118162031450710240808555010202d0751401200c01c151041c612020b04851080100c01e0f01c0007006003d80404a280f4034152641ea40b000700a13440030209a40d150104414142d0250440000c0c1e181100c030649400b140f030740001c0468000000000c0c0801a80a10800b0075000c0c5c0e0440d07004049a603404c985840b40713403032283d0003500400810074640c0200103d020500001000301c0784107590700701449095032940c01106480d07064158600070303074590f2466041e40380a07140d00901003206d003881810040c440f0341e14007030090b00e0f803060044115140d4103c0c03202d60380f40041156900e01c1c03028600040d05401d40e0820780c0c101c19034000c00c00d4120768800305000003030300c0714807401e010f4032f00c0000c040c07000e503980b170805000f24807035424005e000510769982655030f40f6002c0c000340038803209110341c3d10396280d4401e1580c6404c1103103c0f00d5440e0030742e103100c4201000400e000d444407400c2580c01500d901e910f032984452481c0340c014201417403103c0000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 576502598 1250 576501348 576501377
    0x509011401060207030b0901020a270308070809181009020c0703060c05031803030c070809030c0a060e032e200430020a0306050712020705060a110a050901 68
    0x50201404000c060a51501969144006500c0c1c1c3d10501040d29401000000038411080c14001c40e661101e20707a4400180071158075040c0000c0d1101a890900795207903400c00000320710240003405170207000d540c100395241c003034404116400d801c0c103c0f1000040340c4101001640789041100740210385180901696030040c0030001030a1803c181c2009102a10b0107021018150f4414003071403050002d5511100c50814001c03120f90359001c110394080c2607038404c02c10540040c134180b016003034000340030b401c45480035201800100703106041e8000000280440c41412554035040001c1015040c40ca403008140034401d40c5600340e2024401010b101d6a51283c1c00e54400c0303115900c0c08041040348201143c1c44070707241c1c1c8803080340c1c019400f0041d15024072000c008640724403e6240c41d83e495402440741c4c0815103143d45020141c40010855414080000b00884c2003102c03d000500303480e84940c024251502d4010040d80c00c4490424484c200c17240248030350b4440320f030000100c6518103400d081ca21740500c984c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 576503848 1250 576502598 576502601
    0xe0304140f030a080f0927060a0f060c06020403080d050603101802060f040803040303120506040b03190302031306180602121602061c09050114060a0603020331060b010c021003050901 80
    0xa08151f81c00c0252140c030f10000d01401d4915040d4102c25205103200d9072a42d800700401800c0502500714030170701d0010204440b40c041c14920701c1292141c1c0001d414247c3d40c0d2a407000c2038000110f011511a280c5080000c141313000e00c51508000c0b1415000c1010100503408019203022544000f4001c140005650100703080300c505840080500390f0440343d441da10384c0703002040ca400180006039071606050108909242c24000c54000d50b00281c01000080c0c000d103000f41003410b10310300541c2980004c001e04414200d4900403180035022546031900544200301c03400e4080d00196020100b15007210403040030112240c2d044500d0644541030040d060364450000440c41d10401c0c150700141c10302c50710f240002c000b49400007801580244000c010702d02c101801c038150700030111025544584c41340d4040c042540290701454000e83d02a900003a0003103009048004006030820819040e0b14003000c0004000132402a00c002c3d607000e181840700050541d0220b0817950600440f10103141d1240005a42882c09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 576505098 1250 576503848 576503857
    0xe12070812010803121b07060b0d120e0909031206060d140403030f0b0306090309040c1107030c0f0f08191e2904052508010e0304140f030a080f 63
    0x81000d0505541e545001030f5903540410804008101840000746410b6002100c007185040b03540c50a900d02207540c0c0c8e800f40248001c044195004010480741c1000c00e400403c0040401c81e25159105800b03002c0e02001090400186021000d501c02c203c62407980054003032050b0400e6041c0c60311602d629004000c0390145c401c0c801628001c8500304100006d240e0305410203410514035000c108091120501455140e401c111041030b01ea9104100251140c107042d03000c0b003211452464682c080c01d101d8585542000610b52055030604000f86007441425604500000204401300d0b42440b074606c0c00c07480036200e4024030b900c5020300f0b26075010401401000486115680c1c3d02a85041d12110580b402c030229001c5c0d85200000c54007900c440c0000f51a80745500d900039034102c1c00412210f07441503221102c03182c1c02105d050f4101c1c1000000289030000340201200c080d511405561101c4c10003a101c034042114040c010b01c01c55407550440740e1500d0104411403e181c0001455039103d00c001c4059085106 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 576506348 1250 576505098 576505117
    0x30402061902010219080402090c0c010e19141501060f090b07050f0c0414040204091415060306070f0f080c09060703021c0512070806031504110f03010e120708 70
    0x11111680c1c01c6a0381d040d4020885408040240182c00556500845030b6240485000b50000c62800210340200d241d0030152026110b0180003241401001e0100360400780800b01c02a1582980121181005240c44c10104844c1060300280070100c1107040501d10702a044c840e0b0400c0c0150a154422000c0c4595440d07c06072010105544d900c1190785099503072112180351120840c014402000703840c1c5850b014820407020781c110822070b203445030b8080200401c2d454400300e8000f60100c1c0c18072448641400000c0d1141e0200381844082e21b481d40a050600c0700007018101000202490000800d03040f4110a90250441c90551070310ba5480000c0303401440b852052940c4200007240d071104240d0b0016010801060221400410086000058800b4000c10348824016a0741c00001800148a0103100d6801000201118540703180860441c007040403c0e507040d44d050000080791030701d5040208541305a201c05070000c000050390098a00c1d203ca1400c0c21300090010005540c41c180040380081d46c2c040e03007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 576507598 1250 576506348 576506377
    0x50a03022110090203010b040902210f010e070915030903020705030f101a030c010f0c020d0c150806100f11060a0c1b080a080c0c060f01091505031203040206 69
    0x66021590003040903045580104078965408003050f054854000c0d00d040343c0e0010309076410241440030720000f0b50040f1540040f0384c3e070f1040d2210440800880d8a50042c0c20b05104941d0070750415281c0c8030803050081814050003407000d000c1204500b6480c40c0004525145400a01c230102840c040f42407600f9a80010703494455280002c030300d5080460300b65030307213120604100220805005030b4907100000d03804195150f0042c80d0f401302d05501404030703034860308001e15021140c42c802d640040c1c500d0f282d004c0280d0310b2001a480034428101c08445034940056a41410702031460404001140301e08034605007010400700307204d48264070307028444e9481601104c601345c505a181c00c0103140c00420000103203c000460310f95440c001226001c440c00f109581021b52646800c0c1c0c1c00805444000001d881150440d5080004ca60035100a10610b401034141013124140d40d403410202005684070318400c043c1c01c0000000400a03554000f5000860140118216440b9a50780c00003030014010b031144416940d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 576508848 1250 576507598 576507637
    0x215130602031309060312050f040e070201150504020313110f030f0c270f070e100216050f0906100309020a060c0203150f0718050d0807020f09070f050a0302 69
    0x40c0c0c011024014a0900c00c90326043c0c50350752100c4070f06450706444041e240c00d21861442812512030001000008900041d15142c940e5901c11000c0c6404100d41d01401030b590303200c086458915054040340144800c580960443c01e1084c0122030031002d0f0b0900915020440382c2c00551903c03511210305864030002d05072034041d200328144ea0785032110210514442d0281901601000d1111801c41103404c10f4800108030301d03600c6072141c3c042c0d24070140c6042c0501012a070341c404946e484051012000c14540e0182c141c0b01e000d00104420741440f500450702c1100300018001b80c688403480c0c001d5008134100d489803001c0d492080f05500501031030001a4220803480301c04034216400a04245490340309408845d0116581c0300014034105042c4c5030031820a0003030021500b55840b801080a401074580800380f0110b54800006041c10b0108100311032001c004200c9a00754507012800d41100c11060351103d03035514018000a00320501412100113001021440164052003641a6031400c0c400c1c94100303004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 576510098 1250 576508848 576508859
    0xb1e1806090a090c05130902040e010606141e03040609050f0d320c06040c050f06190908010c12061703031303090909110f01021c11030d0f0209031006060c021513 71
    0xd4005101f0a0b0300a070300303108071010700240500c02c41040700c0713265640045504004c400c2462550016003949030000a18000ea40154003200c01140a144521800115009145401801c00c00382d800c1900d42e60308113001894480780c0201c0b411283d1411040b00100a078030140030405c0324030600804009130345010031141c034244c40c0040c0c0c45000f80e02400c000000c1030380c0c0d8000c020400301c0380d185a94000c403083c4400e082c3d9179009174142d03441295900340b60f864291036005141c02c4402c2d4103054400034500b5081010030311180e200788000b034800d1402015076809140e503015503174030024221800304600d0318004010300d4881d4200b4809442688014841d00d500f80c2403048001c07034600c1c0034078440e401a65441031258000201071030030308555051100020ba020600f550070f040000d5444000e800f04001010000d03459101d1894010580d42c0d006848010090505140c42c610b90501940a8034100c1c06214042d0002c03100398006030b0407581d02c40b003420100507101e403a0084182c100c00c4056035040c04100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 576511348 1250 576510098 576510101
    0x1140d05070c140712020d03030b040906270203033901050a1d0a03030f09150c200709020a030204090504050c010809030906030c07060b1e1806090a090c0513 69
    0x1d05000b48032500340c5920030070fa500d0f2525001e2040310020802c2180304401030600d5103440c0d071441d01a080024070300d03840c80c002c90142d8002c0750307084031a20b50360300d22018100b42c204d0080c404115484154100001c00b0750101e940d034030415000c0f18034001500000000c0751828220004000410401e070720940d004d0b43c8010703028003401d039091030500c4c0c10451440768001c0e401300c601c411010320b41c0003010641050348095000780b00c06a0034601c0140c0720641003001c182d152001a80b9418140d80004e180603582d00c00404480c4a400e9501800483c00c5580070700703400028a14040e1600c1c50b0006a449940b0b00d002d400911440d806607925034140002c0105000700419104568a03081e01d945941e503032481242c984030b120300c440c10350b48400c00780046001032043c0c40142500034400c010001e00c507408040040c00403111407840070700316071090001700c0580c00c00b9410405000c4070030b503800200342000320000e10071200003883c070301401c1e99400e0240b0030f01481d103983c5402064050200265041942c40000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 576512598 1250 576511348 576511367
    0x1c140703051005270d03060909150e010f02130509060f1011070f080303090c0a080703030c0804080111030108010c03060303080708040204110a05090307080303070905060d02120106030e0c0405060f01140d0507 91
    0x5c08245001c00016444403140111002d9503402104801301103280d007113140041c00980b034400115035071004110444030b050f100074492008e0180100c62000c1c901000c100400c50300070543d0313000d0396512500e202c06071184001e126072481c07141000003105c00d5011140740b0b0009075600c000b440c02c07041d18002640b854080700650095009205035807214403602c060002c00700c981d100d102da00b40d1002c503040003c00c0c032070740d101520244103070122440c0580d01e0b000c140c2940c07024281240324810000c0104042402403040360301401c400d04043c488076181d620003174080d60008001d041449002e10010b001c540d241da000b0007560150b98140ca851302c4040000509680107121414081d1159810100380c2c00d2000003030300d21811082d51540781c91400c0c035003400110341091070401d90280d005d02104101303510b0054042c0c040c10b4159000617071080e0b840310142c0741c00c00c1040058000d62a00041c400c0c41d8842d48003a0342c0e559402e003001d1420b91140c036015070341c2e0b03c980d0141410b1503140c00140100b455100c514407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 576513848 1250 576512598 576512623
    0xf120103110904051c0905150301061b150b040b040905011506170705210f060103060b210606091509100912110604051c14070305100527 60
    0x980c841d1441c0c01c00d12180b11401d941c05046540103402c0701410341c500700f1982d180101d05180100d0701980d0f8802240007450f804c01e444010940c00b01c0103100e0700da8005414036a03408200f000c005810301a4036000c004d034500e51990100c0380d45986118035991101d810803842448080c00421440032030f0306206d4000d181019200f1200000c400c40010400d105080660b000d0203050b1000020380c80b400c50603034065004c00011030707110810644a0185480c0c1903075262044400400300324680c9002030005048844681103110000000e00c15554903500065001d501c15124030340502851b01e038400004c0550048460321540903207a40e08001c20703011028054544081c06842070010003400000aa40890482c041c094500c1092044140420070b5402e031000e40d6400901403510b010b8940c404100c5080c120030000d4107505100c040302041115221800040c8509100a44038036415513441644456030f04114040c040d4907030012842d2440703c040350f44826190795034014501c0340801d000640360550003140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 576515098 1250 576513848 576513863
    0x20702090910110c250b03010308180a181d1609050a0c020d18150f0207060302040803091e030a0b070906180b0a0e04021b06011d0f0c0f120103 63
    0x1800c08006440c41078441041400780600440d410176150300c0c51440440309000483c00c5503080010355401050000c44c082d5005a441540e1840a40012190340f0700e40e011603030049000c4101040640780e8101c0c818640d0082e450086110a83d03030100d010034824880c451542d07409000c6142c0c155403d0419180102e40000d03000707200b1682c132480d111044540000e05a00960403039688040c80b28401c507032030070071141c0000c0c0c910b040071b407150070b0301c8074103a60031860001043c2c1804145900940400c061001410b8900e02585014200348a1680781e01401c981c4a0180420714220405046000300b0700d002100f010301110020030706400c280e03120120a460002c0410304201002c00c00a201c0c5d41c00d880e50082043e5030241c1c1614102e0121070562040d0100020400340800d03c2e02e80d96214002001403503490080e0f6020f4060342c040305030038007006070300822900c414926155003081110104a40c00090f040c2102c4032581c0c0c1e003901160314400d24058054a0034009004c450310084100f0700c2d8103a0380039500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 576516348 1250 576515098 576515111
    0x10030609050a020910110a0804091d011b0e1206070503240915010302070f0b091e060601110a0b0c04180903140a0c0b040b0405010e1605090a020702090910 68
    0x1a040101d00c00c4c0c0030600e0700810100c440709119800391a50b0208150703050100c1e071403032005498840041d0026001030000f10f4951602d0354014440803c407840941094000700998041401c40300e400707030044408042882034250030b00740c0580c0d540d840001107084400946209280032709000f4040d920494180c24107030061840c003240450300508040081c0300142c01da03222515822289410005075000c83c0b0704141c0c080050800251010505401c454882c443e06081070820303180305030420101c5104c02055000c0e6185001c00c2c00400180316400407000e00740251001d6803c0303455801c0924450700500035441d6a410700200603ca240108215940174241c19100741e90301041405550307070703260003a00150303ca150401280c944000107010606240c1003141281c062a80c0e1180710013401c0b2001da07010f04d42c1508210900c00c0c203024440030314507500042c1088600c10680800080494020a405201e81c40001000300030b09904a42c0075640041202e52130b460240030195440e150600e08107000c904059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 576517598 1250 576516348 576516361
    0x30601141f090b0d0603140f1e060103020f15181c0201022505120c04151206091a04050109030e040b010507110f0d0f0605011d180a021003060905 64
    0x409181c240203030340c0e00050a86003102494103504440b140580540da43c0c10b002001564407203d86510450036009016803020302e030f50030f50800c585184c0d2800e030084a4490705103041c4000c9280d906407903045400c01e88540040010803141c0f581115280c08024001508840c49030104800c0000325038225840c200a000f4107607a00c1703c0140f200350017400350340000c45516480101584a41c03801d0005940460003545c0c03600042c070700040d48503114a4641040c4059101402d080c007400c1a11100081c14240540c030780f40004d107000e51000006445659214508400c2040c50700b40c00140c0d04440240c0401401c150910a000740340c1e07603400b10049000000403e604d030900e8018070320303441c1c4161129410501c1c3c680311821120380e400c000591110201102418a41d51031810080441c001e40041081d03440518028084a0042e04043c0c045480e25210311a021801204561700c04a4001707c03003101030001e84841c2c5000e40905000703621000100c0d440035001d078594030000c00c846841e6020710068480302f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 576518848 1250 576517598 576517639
    0x60902030307140f0d0e090714030a061d0421034106010503061009350c100509010e2809020c030a0f0903140303040314090d021e03060114 61
    0x1009240204003016045121840c0c2487c8840c1e008601e4241003000c090f8040010380554000ca50500941d5904d15051003c1c039450003580ca0f40c0076a1154140c90b40c10140c5422424035000f412500d4900c02e404080140e49100c0e8120070400d1080c182c1d01a540c00b09207510b64200f842406001e4411030740001c04102d24540140424022601038445910f0b503224102400494280c003030943c02440107401000490b1440c0f00310720700c5990000035a02c0c03162481d912003400c4009000045400641c412504401c4a41c1c4600b40ca640007040c0e420130550740ca03414001038500070702d10604558003201088440401001440c040c1821540f40179030304001030f880315154012401041d11120161344288048840c060251520306202c0c207072070404d0144583d980e0b0742c190680f10001c0c031200701c80d0170100030711007003540009000d6820011010500d04006128021400f500c1c1c4149020380f10300900b0003000760740c00c944619038152190103000d5900542c0c40c0c208411108a075840310701d014840000130300509951a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 576520098 1250 576518848 576518863
    0x204030b090a0b0c09010c0506190b011706040906180303050f07020a03090302090901060f03050304050a05010e0d150219090e060603040203070303030f11211b090d060902030307140f 80
    0xc0c2d49602a4031511580001508049401d906006082110f200800c40401027503100c2c1061a80301f8085004c3c0066113010b0b592815000c40c144402c6004054070b10701040421507014a05580c001411070144c105900500301c050303404803603021051044400d255042d004107218104181c8601c0e1240c8a04804981d92010b001c80500014003c41c81070005242128a550b04040070a001291840c2c031041001ca07901000e43c0111159817001504001a00705031010310020f04c0c0c2400d1904041c650341e004a5281e02007808024644400c0c40903440c050207803581511195105a40e8209030200248005080c1c0c03070303890043c03503101e10301e10300020040e1501d1001c4030310555020700071384800b034a0340d034090f400b40080450342c0404a80350ba883d0540d0480b0013016181c01d44e010b8140055207002c1c144180c4400303101510b130107192008103080b4850358910b4001c0b00c0d00b020041d1400000045c417414104020000414000e600d4040000c05006100d0303c600041da100402c4016034a51659084030140d0b039105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 576521348 1250 576520098 576520103
    0xe0408251a0c090906060405040518010e070b0a03090f05070611010e120f070303090213021801030507021207061104081608150105011116060807121a0402070f080d0204030b090a 78
    0x40800034401d0f01d05095441c103401c0403000e042c1741d007402d80342c00006064940c00c4600c050b50034080c14000c51411003d008003c80348943c82d0203040d000e401d0002e040c1c105d01c243c1c0480410b140d1650107140030029400c50243d4481d403c90292500e090b1201c20040c01400600c108800641c00d141418203890400700d140b12184101280c1d49141c12040c2030100115046410190b050560380c4080d240962140180c8036400f12903070000580d6580101415922550701c1c807441c1d0304040ca030204005155800003108840030003c25242611000246419000341c0030302000003103420804540002c3c03060700011080508542d5100001c2102e4584590340d64540354128410001e0460100401880d4042c95000c00c003c0b421000340e95441c46410031031a2405e909612003000564100200102554400f80c1e81c524007058417002e214030861519494411691515070501c22540069072000300145c5980007090b0a41c001344980e100e501c20540440250098030041d02c440140c3c0c80012650080440d000d03000f60b0b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 576522598 1250 576521348 576521371
    0x1c050d0e0a061d0f030a0602120a1d0703080d11040902043204021c090b0403020c010c020102030304111c0b0402040b0a0302030303130201020c04060e010f0b0c06010e0408251a 77
    0xc3d11010405000c0060115030381600640d002400850000d0005140642a20302c50a0700c60500e500c01c8811100030002600710448482d101c0c0d00354940100d488000c03a50000c40c100e0320341d884101e200000f481c10001504030341e0000140010440c1d595006041260006880004c01c071800c005105213460000c10818519030b184c6900c84460b2400c1d5000d031a4172209042c1404412104c01c4c1041304403100020280c4d100f040700c1040008041e4108442c025605080c030740f4910070449540040c1d41c3e400090302c000d005a0813401c0031000703030300c4140040070305811381088045145a107003021781c40340b1029582a8011800c241c0c0080d41c1c1e00b048244201100c0e80a002036140d9511a04000c1a240350307102e040b4114002c100824046543e1401854003612202c4000d0001e545086007000036140c0e90792100022070170511109074070041c0800c0b6581141c810b0702e1000c180f55243d2a02e402c040c440c1d00030310480e0104403d466543c0384004c051210005102e1142180c0402c04103d48051411741240c21050f40c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 576523848 1250 576522598 576522647
    0x10506090a0c02031314040b03011a010e0d1208160305070504270204090b030f0a0201050712051608030106020c010e130b12010507050702101106061c050d0e0a06 71
    0x141154400500b2200780e1059a0501c1107240c545100b011042e44034408404692003680d10f0b5190a101d00081c000088001700070514101420030590055042c240313040c880130382801c024030f44400c0300f80f02c680c0341c1c0502c100301c032242d01e00c4e4041d018840640e4500001c940e26544900041d0081c0b180c03a02840761038130350900b080d01d45000070550340c900c01d600c0395a01880d0540c16100d070301c250018101910b5044004030b0018202c0b0241840d100700c082000b11564072000329040540d80080840710342c00d4100381d4074044007510030030991f404c2c0304032400103440001c9194034405225410000d54142d8403e5400c0e0b6000c03011002c01199080024005079034409512a088201720b4155030000102c1c500191140da00d5200c1c041c0e1240c2142d50032601c80001c10000621403045240c440700720107015826003804810401e04040c1c55a480c00d00a01b0b150091030300d0184d202c0108600c1c0307805601554050102e48070704481c0140201038031005c0c0c540714050142c01d0707000b0501c0c9028804001d15101400b20355402e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 576525098 1250 576523848 576523861
    0x9031d03103603122c0c0118030b01260d0504150509011706040b03161401050c070302040f090b04060603031b080f130b0d05040215040e0a050403020313062001050609 73
    0x10003e03080c5604a142006109841e4840c401740b00501c896800c1d40a441e000c580d0b03100140184004018000100750001401c1c00011800d558030340c10348070b6013041d41000707001005603043c0e40ca11032540c0c040c0610509041d101030940c098001d0082d0741020320101d0b02101105002d0702d40d4011001c1c030901140c41340040945c00c080303515507a07a02240080010810074240e4002c00d042c0000449058205011690103001c00e6808040b201d800000170320740245000040f5411030740f60720450200174801c6850b500540311814407600494400d03900301c0b200341c4403401d2074a405401031500c1e00c01100402c0c2030b0051102500d00007010081495080302d803031443c02c41d1800503007540ba401480c00540ca00026030340800c40d101281c01401100c416030000103001d05250040101d00d800d0034030718850b8903c0420013400700000080e40c2507001909503102050365140c6180036801c500600100508a0103e590001400c95100400c0140192410312695521074940712060a17901c00709e84c00d58011030100080383c071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 576526348 1250 576525098 576525101
    0x1008060d0609030e18010e100f060e0a05090c070201080105012606060c0105040506010f05040902010e060a0908120711060322032a02040f09031d0310360312 69
    0x2500d4842e24100304c00440803000542d120781052280601518580300512120245001d100d42101642c2403468110f40340600090071031105020309810010301980300d0040e6194410942d0190400404124942c03502804c0a007054200d090306900103108100001911b500441e400a040d082000301088400020b04101003d0040949030540280c03080148101ca41001e101d40c1c0d0003540701d0390150490394074109030741c5c4044401d078000a11403840c0c070303410b000180c2e00b00324071400c01001500c1040d1a40e403038560568000504d9400f000c0c850162042411001c02460010065144601c0300c00300781418000034407025010885030309001b9803501e00c0c58070301540d0408140750428801d180c02d04171a00a00c03410100c03526500000341080c41c1000182c411490240195a03e00c102400208030390703402c540300100340b110b0380782e006111003c54202c0c886030341d101445081c00b1020582000d1080b8010041080c4100c44002a04031500a8490f070400c6c0c00b803140582c42d4881c43d00743d42c0340030350340c160515080c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 576527598 1250 576526348 576526361
    0xb060a050a0e1c110a060e1c060c0e120304060f030b03100e0105011a0c0d08040212010609140618010603270506011e060804081606090f03090f050a090207080403170403021008060d06 80
    0x90b417a1504200800040c0032750003080c0c841541903131111440030801c818003002892105500740c65401c180801d0040581c003030fa000b0074541d580c0c60f0100380080401d02007400c14401822000f030103820301205080f2050305402150480c1c5a4076030039100d0590101040c070050045a04481140d0000c4461803289071184180329041130004050440000078100c000b13007103810030f50042242e251a40012192100b86112007030b07225206403801206803541442030002110140907000901d50b50b0007035150170001441c541900101d10140d030060340034080c117080c3d0340d40d0340911400e88a4403003c108910351214541d8003c08079080d585030020769807100d590f10804ca401940c0f9151402c1d00100041c00445c1c203901178104894044d4100c0c0003445010304000784070803c55000014000d08000e410011070310384c0c003600310841b82000c40c0140c80e510350b440d1503506e0384980e90010f00346203d03080e184c500c4010b10300300a00880e8401c80e0201070324210326905840c5088210b8a00340d01c040c002540901240e541d4124a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 576528848 1250 576527598 576527629
    0x13030f0503120f1b07080306090405030d0c0315051c0b07350709050307060503130b0702060709120b0a051e07030209010806040b060a050a0e1c110a060e 67
    0x9030b0515001e407540034800030040390703024800c54180041c003076844001180524100003022210b80f60910715221031400d444042c2c0b12500407442600041c1c2448028815640d4114194405000744000c1c204003c01a284450403141500526000010589000550312803000e08031b07101640601c0f656100c10415400040c044024091602408140e1480404211203c4000b03404c500890124034980e1141d140e03002040c100c2406a4150244066640003442a0840b102807603c66525550340405100900e1000070040c1014500310600072100c2e00420007912070980c5548130603000e5038070b4000500241c90400e000d400c00c0d840501080c0b1031001c2e50405a403084116603c54841c0c002b914000c0360313124084944034001380d8040390303000d420369101c00d10303903008881110280605050354000522610406140390140704000800810b0301e402905c0107402c0280c000c0c41240e06550808124a0f80c4406034400c48200880e00030100c500e147c20316002e000e40360250f550141140c1c00a040c003c000c0c0300c00d0a036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 576530098 1250 576528848 576528853
    0x412120f0b09160915090b0a03021903050103020303041502030f0c07060809062401020f070303020619020c070b070309120c06031d061b0f070c050a1d0c0a11250b13030f05 75
    0x10075240c1c14035008008c802a190b50050307440340000300c082481d11086c103130201014200701c010005a6000010740701640e01e824a0440c0b0050b80800c143d00e580b147d0722040f40c5400010aa0032101080451500100c68041d190a241c0d40d0361381c042c103034843c0412a00c1c0b44900d101092801d80e0580d40350601303044141c041c0120340c941c0010304002450302e40d01d6401100140d2000c0e08004101d00030541c43d00c000301480070294201000c42c3e001c80d40b80c8145015283c1740200c007040a000741886007005000422a504403180e03801c45500701450112518003425000c02c0c01d1001c3c2c01c60300c040c20030500f01d041405e000989042d4035112000350b65640c0c0a08504080c000a00c01c0d4600c407070f540401007460310310031409816103030710342014010070032201d910107180500c24103007425440076110030b000c0d8440c00c1070103aaa680d403920102038400701d6102c100f00d42c2901c01c1806541c0403079501c1c051081084030420044802d69980c400c000d40610500c41400c201c0b0451110800000301c54004d11200d03544a00c09 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 576531348 1250 576530098 576530117
    0x3030e01050c1c1407030c0f110909010e12070b0601111204080303011d010807090e0a0f030210150506070b1e090d0e01090e0412120f0b09160915 64
    0x4281d103000380f40350040c80d0b2103a0602411140903044400d07628110311030f00680307080c40f00d945c0b00a042030481c0e01c1d0103400301048000b90420420b25054004884900418504003810700811903402486101100d0807a84030380d440407040e0002c2e0f0740079280040e6000580c0c449543c0c0308030046840c017440c3c0e002200c45100f00f40003c1c60804161000e000a4195040110340340d62402c1024003507070070b90b05030203400308054034014440d5000110b014400d48040c4200450b0200b40d0290062410200c2e4002a05000103510700a003010381c04104052039181405c4240440400484c0166030a402c40c8112540b0401c1007000c6e00002e101d01c500c080c0d0000f0035011501c058801c20002c034401101c01c5503203802c1900509030646c10303540c020b004124020000c1ca4012402c3d03040040d92180081c010b40301400500989506002142c441c90764500c850f82c81080511220094020000c040e1840381e0b4200d11a111410008402d12204560107103100b1103a524600540e00d082a00d000516072290000c040064180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 576532598 1250 576531348 576531367
    0x702030c0901080a031412071d1801060e10210e0f0a1502090303041a09132306090a15031b0306110304110105030c2502090f0702030403030e0105 64
    0x100058001c0203200701a103511a114035005105540d4684446c44000040c1b12014180144d8460590304c08400d0410020070784000d01a40329142c0034a0000b0b5201b01c0c41190030b42c40c00b2101210070b049a2607501c27a20b009403444c1c820403d40150050401d4009041d0540710716000110081e40c02d51119500070029044019900343d5003004c500902da606581d010703040d40030400c986260700d1914280c400708110309080544e03001a03120b2240b44500c0d407040030303a014500c12400d0800e08680409000070400500c2c0c1940c840380101130103100003d54a000c0f148000e10141d1002612050b20a080040c58001a03541d03141e0030800800d102024010f41081203000400001c500b0700602445a060315126412140780d0301d0001c00b690240d1202e5000f9240034018003000a0020010240c480003d00b000e40c3c0f2a542e0021002c0c0a00418220018020b0b10000c240c21103c440e1502101a40c000d84240c122a620721040708a0070400b0360340c900060b4820803041001c43d00c240e91800403d101403519034a41105a03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 576533848 1250 576532598 576532609
    0x703020a0c1505090f0f12070c09020c012f120c070c090e1b0d20031009020406090c05030a0b04090f03050d0e0d090b030a1d0a0b0109140c0702030c 65
    0x500030700b55601e96035410300a86041c1084410010082c442c000c20b03600514503044c907218072034544062107101012608104104200003294003a25000804548400c01c02206030f0103001d20f071081002c4403081c031010221405400c10046200c55142d00d44901d402a80784101c44901341c01020011985428840f03000020741a030449401031001c1c00000c51048583d0702c0e170b00d0030811001e40100c90059902071a8040352108400c0d110340c183c1015966110004041124038200d0b08104610b6140c064040030300f00412042d84500b85140c000d560030007a864640070070004441000c5c0751403010641c2440051007458058010399a0240c000d80003040c00102c1e030342c500c080301c201e0410450120b1804101c4004802181c4144001e0102860003842c104c407a21001601d42c40641c01210544200040080c41000342d0350042240d121183c00001c24040c82c1d50f13003003511161082c0048491072007280000400c4d4000b030080c0c00e0f8800600514102545562050141907408182d040b030f014000c1ca20801c4a55540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 576535098 1250 576533848 576533873
    0xc0309060d06030b040b10080303060d020f040b040e0a03140a020a140a0210030b0f0d02060d090302010e0703030804050f01050c090d0302101a13090f020103150e011e1d0703020a0c 79
    0x8004543c418186120b46c051044055085070b40b40780d1045c02009136640d01d401a12070b01d142c06883b1259041c1585002c280600350f04d10203d60000e00f0000038400e100e00009102880b2402a03681101c00100d05400c07112511a40401f000161710102000020600c42c4031140c014107a2003049038544072203a80441d1140803004d4070307400840d554070011843c0b0300340003082c80c1204c0c4048802d07010b0600c05900280880c0158100106003c0d40c82000c801054000d40c0081c034001d0a2104480402d941c80c40c0003840c1c640201c1d4111202d014400b0700d00d840e22814000c007801407140100c06818000c11505109118400034815030441c442e030340e0003112240b840d10079058103907201c40c0700200c02c44090082c80480081c2d040090394891608907548081403c03582030541a0394240380205e20103e0241044420010a40250140d003c055000250840c001c0030f102d42841030701114440744941c3d0b21f41c080c100700d03504050449070400120014107079500c61340c002c0c200c14800d402c3c0f4100d40300301500c4031980d0014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 576536348 1250 576535098 576535103
    0x20f0c1002160e0a062c0c13080a060608150406020a031103090d030b0d110405060a030b09030a02150906150402040801090807050c04020301050a06080901090803040605060f01050c0309060d06030b04 87
    0x20f010f010f2a81e02034020440601030248910b00194108403040319240c1c4002e050140d8030703107040302080d000701811080303c2840c002c0c103061840c40b40d110b61006403035002d0031100301c48040c42c110001940c800b0126900344090302d981228903a9036180e0702c0e000c019510240030310302050b44d034000d01c3d0b031290800ca01541c0107400d581c00411200e01d1914000d411100740209440c81070001044550018100003841040244103a40c0443c043e2508004144c4051715500b0041c9a50201001c1004542c0000b0103841600300756070031500d00e40c4900c030044c40d55650988012140343c020200045009110346008507400c4ca000c2e20040c540783e80d07007580c41d0846409103130449540d0030001e42c034014040104504022001d0855046185514041c0000c000b1056445090b0030f000e00c0c2c0380000c880344800e40c0502150760b00b08018560381e00e041d00c0c00000902e021141c240c802e00148516000d5544504103440190044d139008600e807520b0309081107035a411494054008079141d42c0040005034030385000a020b5032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 576537598 1250 576536348 576536369
    0x40504031205010b090604032301230106080601050d0c0e060c100609060f23040515090f040b01050f130903110f190209130c08030a02010c020f0c100216 67
    0x1100805400300742d8406070b0103204807840500865075183e940504840459610070060301d83c100d1280c0390000d099003000740c400455460000f40c0742c0101d19020302c134090321007280fa41e10f03042d07a00d540b0b081d501c4003025502280001e605119054500c001c55015590100e00390900030240717031011700010039980c003000007210142c02c40010040713007016501946c4041c1040d00030510080c2d0408a59603540d100b103110fa02d50741ca040c0c00d041c0b0182900700d00d0703000410300054000d00482ca060001030391800d00e01d12600d070042e442c0c1c0c1d0000d208116000e80480c005c560241e165091a403034601040b1101c4284501d5a0b44409481155030446081b48541c000c0c0360f210752110344403030303224070821410700c48158084105504920300756142d00620040c1000a01d50403503144a407615086444807610181d404020540c4030f040e0790215007020000064140000240c0c001d1014440c284070480c0c40340c0c0c486001040640c4039110720912441d0541101c50100e00340d02c1199410140001005116041130340204d0011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 576538848 1250 576537598 576537617
    0x80d240e07120b2206080111030c0a1133060a09110d141008061b0a03020c0a0b092503060504141c090509040b070f0216060909140610051804050403 65
    0x4005170241c00003c0102d00000c121030b1801d03085024007440b00500f8101c2c0030500068035005203026003403502420100f03008440070400c3c0d040e440b011010602201c1200c102004040c07400154a425005201d5a4090406001e4618020102c2c0292107451402c8418820074442e86151110501c60425030303150000c0700c04581c1c14010050740340c47c2000e03044480342d90040010000500500020355410404052810340e80b0802c02a003140280075154401080b8001c1084003001d1012203041c3ca03001e03c11120641c1c551210a0309032005464400386c010b081942000401c00105407507030703ca0b44e405801142940c0f20b41c05010b04003420700450040c0d5400d50000c220078a40d0860b408101c0c0070103040f055076280d406081a848200c040c0000074482010068540d036180340d41c920038887d4041400230445075240083d100e102c042c10060860003440c0c1e0042c5000c507812a000c0070324800900070600542556024031021070210f8099108000884d014008003100c00c40940303031481114481d901994448040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 576540098 1250 576538848 576538909
    0xf180803100504020903030f0c0c10110601050306070c11042304030e1507110a03020301050702010f1107080909070e0d0c0603050a150506090a03080d240e07120b 71
    0x8072a1604a2400781d4810b000c018800c1e10000b048814519659640c981c45640c1d04000380e1a00300d501c045070f6046444058089849a00207a40707040165800342a56002e030f0b211414036640c0e80c02101c640d00040d0840c0d070008080382580e150700c40005000f91010600d5103505800402464002d405801e00602c070404001c24140d01000c0c651070914111450560b0010041007402d5a0050920140100c1d00070f400015290f03980240c0d21005550240003442685440a0081c0c001d09049441c680301c1801d04e40c2c02000c190520b03003290381c0c0540c0141c5040c1055000303070600005240c01030041d024070110600c2d81140c0e0740c41e042d0705d007032452241c0010194503003010b10041c10346801409504403241006601d6400d011800e40042c01e680c010745016803544503a000094401000350300c06004040001821800c1e12401e8002c40c003040761812411088000d52036040081415520845c4900310082c1d0125480600c600044118121022000311300d00a0400000b00c00d01781d24403081c1c84e00000d82d03001540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 576541348 1250 576540098 576540121
    0x2f0a1709031e04030f0602090d0b0a0204080c060405031005070c0c09050412031802010809031605010b0307170c150705102403020d02120a0f03020607030f06060c060f180803 76
    0x85031814480c40e0b0381480c0c030b1507462003400c00080700000c0c085034012034641c109884a080c001900f6400c42e829116604103580208000d5006001d200668060780401d001903041200845049600180c003d01300c2c1d417000380618006210140401d17041054000710030001c107803a068800003502086100092138140382c03400c08490344100040f80f00b4035040c00181e4143c05400300f944800b264080c01d090314140d940b8261b0700d04501c0380c641d80c2c89000140d5611402440310560006c0c10850041d0300311481e00f5195500c055080c070441c2c51042c5103500004580c40e4609010200c04045008160a181800c1c09035031100c1c1820300405c00707842c12a60761030650011400b603078a444010841000240652411a001b2a02004003400c005e030192004843c441c040e0f4104100350b54001e9042250911408000c0ca0001d44074101a40d02000190901803405e2a169041c440d1f002103c1d100e85030900085d2095984201501c103a2030500c00140d070751040e581a0004030402c5885041c8070b10306940d60f034075103041d0001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 576542598 1250 576541348 576541387
    0x1507030216060f0215060402161406070c0b01150c0c0b0901030b0609132418050601022406120105130204060e01060806010c060b0a03030c03032f0a170903 68
    0xc0100718146001c1c000d8000c22844509040355a501710320395070b120081000380c402c405040c1e900e107105803101c01c140030304a020008a40403900a4036503039291030301c040f035042c0b1110a0140000d1460310040080390ba98038541d06444400341080c942001641d1513046012102e913002616503d40040c82c65102d40e8144a148111841101c37058105411000411600c0086180f10404a952509880b0041344841da022281c0c5015988540c940b85d00d5203a40b0214082000c9810002410b100206200b50b00101d940d01c20740c01031954540d400705441c80004a2400003a003421740200307040c0c003d406201428041c1c14420304141200b241c403da010320500c4104c9407558050308044a448006102c0355a00030300f955048030007440c1c04461b803041418540f0092003415000795200800b00f01c00801c041d0400d41c5840c12354041c0d10100701c2e0490301120402000c5010712080b210000010381105105a00c2c00070b171149602034a00048076000c0303405116450b03001503400c1744059102150b00c00e8010030060042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 576543848 1250 576542598 576542609
    0xc04140402011707140a030605120a0317010b0a08130605070e0f1e150d0e010b011106060109030303240e0a0615080610110307140f121204021507030216 67
    0x10b806180c4600005e00091900c0704014450a0008070703981e00500c13a4001e81301801005000112400ba04d000e5140c1d1010100403c4020403c1c2d0041d1558a4403414921030403240c0c0011414030b46a16160100c4100788000d04001c81010040c00d43c9010644501c00d80c2e100d980e00c0c2d1102c0501c0140081042042d43c0c0b1408510321500081c44505049000298076440b03415045e40c07100403400d45803c40e10341c0307401202c503c01520b510303041c0300c1c042505054101004031282a2942c841d204040409240c032132000f1504203010400d904004c00000340303c0d0307002a449507c440854500c0300300c1c10900d80349981550740002c0d052400c10040c00030b124100c1c85800c00800f42220494070360005c2d0340000d0500c5ca4028025803043c1e24201d11420300a01039085c8103540c0d000001501da0b42e165918160780c480c1c68a54500e641c5e80b240b20a0180c0c81c1d0f000003850070307420300110b480c0c0d0700b054110100741020500c014400c0fa080740760262910115041c080160214521030340141200d0310024078013078204440360307202c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 576545098 1250 576543848 576543887
    0xe0103210c1b0302120a050c1c020d08091005070206031504020409020a1e0507020108010b13170a0507060e0307030605090109050307050619050c0909090f100606020708061b0c0c0414040201 83
    0x2070001850000303003508c50309010b480036001c00d0825035885030094524a00690441010030b00300c010001803000400c2008800c41ea8080340c00380c0c11608550b03500441300025007011080012881010070f40010640c2108010409440d06071030303005030b1090b604401017142c003080555844801c00420703031701c080c1c2c0041e0513841c08904001c410b800003414848184290042c510000038424101854400a01c01900034801d06003054088203c0c0d15030794403800743c0192101c0c010b55030003103100d43c460701c0f007041080300c02002000b041d429511010024440900006030566031040e000d00011414005018414000c101401d080d00c1c114403900c02121402981c2c590841c603003020442031201792010780d01030348400c0c0e4003000740b40c0c1e401d602a80703420146500d81415203d84600c0068084964100710113580859095801c0d03c0d60754544a0380e6104140c9200204202141600381d400b4500c0003d0201040d01108443c1c505100714007040498030700074a151110001c240800c002d658000121002010060a8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 576546348 1250 576545098 576545113
    0x3071703070c120c0e0403182403060e01090e1906090215030c07060b01051e04050112021804110d0c090306050609130209060103110309060906010e0103210c1b030212 73
    0x180c10b0a00c0801740030f058030781031400c808501810b20920441a0f49420f992003a0b0105486c0e1800e1400c2155099030300910900e1405110240c510a000300340450701d841d070890701d0503403c120840300074008000b050f941d14428420401700900e540301007060b525004490002c0c030f8034010300510080641c04284007402c19420003e005265001390100c071507580e000000020000c60300b0340100d07031521038126801003030740300b0743d980098411101c0d00400071601c0980f0f916140f40c40301018041a402800000c40450b14103113242c40d81401c05404c150140030303008400e18a001c210081000450311410218030004a8203213040c070801205125807500601c00701c07440080c0f803412194540710901082e00c007e01450b603a20108500780d00a400c0314a4035006000100d03101d01d00010f065075180780488214282d8410000001103840901c50114160703908a0070314042c0b800702c00224107800c0300d1035110008100d041c1d42010046441c407005042412800c0a0340c0d04440d06c1d5004006800c3c3c00412a11215002000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 576547598 1250 576546348 576546353
    0x30109021b160b07110301050406050f07020c0d120504180902010f08090309280611070e041a0705040e040f02040b0303090d062f04080615010c0b0603071703070c12 72
    0xa1240d030403582c3c4036001a070f40b04111314140109180c02110b140d019070030203060104004007500b0a134400d044030009010180d47d0644107e945030641c90700e85810103141d20042020400c0d0b01c1c04003603011103c2c10890302d400d039600035006807550840c4801c80d007035a0340c403445801c5682c8801114201c51042c603100c8010705101c01c007140c988c400d480030684102480e2409500c0003c5992060080300d01060340060350030f58500c4003411001c0b00c83c60018a901405e140400d00d1010584c2e0180625003040c0c1d905143c1c200c450742240c1400e4050003000600c10103000c0080c148181380c0c070840c4030303510402c0c41c440c4210f0180b050205850070f141c0071900c00d400c02c2c4a425180d844441449098541004011039010f0800da00000308101144034048960601760203503e103080803c1c014011103c10703030120784503580e4900c5007020281c0f8056059002981103c80ca4010960340c50f030040e0000001001d4030002a0740d0030851074180c840008a0303001e60000b060400900c1200b84104008206d9180c00f41a2420b159 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 576548848 1250 576547598 576547633
    0xf1510151209030201061a0406080c0f030c130806010b0714071401121103011e0807030206032d0a15060201060b04030305070f2a15020a110d0602030109021b 69
    0x7031219095155541c1031401454402d4202c00011702d00f0300010046070941c421919169881400b80401051000000c0350010762640115000223000c2c6842c241980c8036021a03808661141021001c41c107101d1001043d030620500100e8020507250a8045c0d4130000c602c1c2c2060030340c244800b4169650080f0008010181c404003501110110910341011030701060303400c0b80020b18842c060710400003004400030425644c84c44034604d0481c00d5651800c0702c02e40c2c0d0544980d0f2082c850200039040041070002c6091480c0c1840c4500760700342c0000c0410b001d02c00180070100b00180848034030b181251035641c0d039144804180c042c00c0280429100038840f06003003080704c2041d446140700080400c080040c0801c24042c4010348420700710b5004d19030120321500000d24400c04050001040c0300c1003242100010a0803904011302c03250381d45500030740070016158a03000029444502c1064102095909803400a803e62004601800c3c45800040e11b45e480d61f40341401008000300d0b66005513000d4017260300c201456 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 576550098 1250 576548848 576548867
    0x1603020901020a170d15080106080303160c140d02011416020a0f0503040e1612142a1c0509030408070306050601020c060f031f050f0d050f151015 64
    0x702000314180200410500e8442c0314410792460860b1800041b03100581c81e03c00c0030001c403030303500780203101d01501d80c0916601c0f0300c0140e90564009001440d41161280a51006100140500501c90400400100d880d00f48501000e200d00141d44d80c00c1d1404181d10800500c64200400581d00c68801d41d103054080e42e83c448020001d0f20410721a510181004400c01c1210f020b056060a00042d608000c11613070f00c072900ca03404400100d01c07401d1421044141502c1905e101030440a21201d81e62a44c220303c402c02803626100e254108001190044841300000052031001d10b440310130b04148564000c454100c03030000c1c2c5000103542040004002c090000281c0500707884c1c002e0400543d585844005034986203107118030300d0704258003241110005a4010165126241040b50300c1a0800c02890034000050140911688010103000111040c00c0071007062000520810440350101300012146d07140117210401180c24448102c10003000740204000c4200a021900c40b40648442e00540034190028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 576551348 1250 576550098 576550103
    0xb0405060310120b160f080105060d0603052a091e0a061809030e01020d02280602121b09031005130c0e061504080307020f060403120302031603020901020a 68
    0x3020000c282d80d11615002a002049414040240c03040c0740d10748003d0740c1104481909602401444074500310b40a082c03c40c0010610740e6038140143c2c2402d0401c40c0d15007080c058511442c0c2d6998010002030401c00400c04401c0c02a43c804141c00d03d5541d00c00404030b25804000c0c0030303803464418041c1070160101041002d040300000b0110f00d9440c1000e43c0000c20656001810700402012030300d1400069500508100703010b56144801d0b01004001139030341d448040400320042c0e00c903400c620081c5a01c0c41200f506203100f0740c41400c040c405a11114117a800964600da0103010301d40c140b00410400030350700072452200e541c2e41800c10780c010340025164500c0f5108001c2d100d0315100003c0c40c0c40f0384404820019544021495203144d207507804071911200460b0360a006010800801944a141200341c508450400c401945820300c5079007849503240c6a0203401c2e030416424000400040c2c0c8800c41c192208490303a60058491030050007840d0781d40001d8514000f0b2600c100003040d2a0f9030302195500380e003034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 576552598 1250 576551348 576551359
    0x70609030b01060528030207110d0308280f150f030308040f0807050d03060608060607050703081e04060201020c07091406010e01120213030210032307050f310b0405 72
    0x1c0b130032140718517100c45145250000c000c405e0340c2c481c00140c06901800800340624500050381144900340310b4070080101c005400b280601000030038a000e01e106182d4141e0340c3c41c1508000c501b02c00c0e4000c0030380704c1e5050a0748155480da0448540d2141c01c404800051000c6090f496100c0d00e540c90151260b040500050001200d00c42d0b00f03401d00802004460035640c1c010112119101d01741c400400030840c5005050006c0c0510010410514002082c4c0728010f4018001c2c050682c80c658502007250301400e202c0300400382400c141030b03038003807404050320042c01184c00240c0e0741d004803c0050b0130403c254001c0d605c1c10740307095a84011b02d030145442c540e01c10400e00f41070400d504070500681d80002242204c0070b0b03c90000481c400080c8860f50705c501145c0c402c1e50030304000f201d10f81094082d501d50500342d40c2c0340c1103200751030ba18580e5090320b425082401c505155180c440402d450101580c002c0c0342c61440c0d03001e110b640922802500d0740d032201e08074100705482805414507032003000034403541c41143d120380f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 576553848 1250 576552598 576552607
    0x60604120c050616060b3c180a0b0405130f03030617010c0207090b0d0b04080f07240c0504050d1109010905160815061b010c080108070609030b010605 66
    0x808040e0021002e080000d15064490a40c40580141062890b4007180e0300c41c10f107050004a4200404e804440103902d0106840302c4001591412503140e400c0c803240401000c1d240c002e1101d440da1a18401148041a1141b4140c0780c8021901c064855041302c0700c0c000e4ac0750a042000103100ca4020343c0103940d2040c1c0b1041004200d090440140c980758000c80544642d042240f007491005501c40c1444222a4094030f4529580e420800708490301059156004100c1003550000a814505a1170b48144030340318207424116039000a1100c0e821104c4c04a0b2a440844a100e84040901a144d501803407901c0303090104001c007145c010031038001c07445194010092204800108903148107030220722040900302e21220b683d1541040302411055441040142c2d0050811014600c0340c942e103803013010101144050407141e0300501c10f00f03034050490014444120495450081402c0c019402154580d030b440040950400c420f003410003070345511035828804490300401c0001d4801c000355044901c07070306020791507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 576555098 1250 576553848 576553853
    0x1081e0a091b0b0409110306090402040507020a08070b0105041109010207060e0f0409050615060c0604020f01030207050d11071512020a031d070e0604050609150a3b06060412 76
    0xc0c0440741c08600002c00a04012030548040701c050421504101d1050020640007038000e801484113460a0b82c0102901d00001d000d03042c2608a5a008641d41c8116840103646c2d84038503a080c1c001c036078111001c1200800404c01d914003801014101c11949600c5442c0a1020001039030b075a80c3d51086030b084c0070301c1a000802c075a0303641415006100018100748881ca0640c82c005451303080844800100b0f1540d4400841c05003010310964840030b50980007860552155020040000200c0a08034101502040b0310303030001310300f44100302e240c80054442382c03404450011903c0c10700c005a00203802d0034009200d842425036200030007210390411b1450040e030b10110507104a000e42039aa0801c000034402c464150a501e00002d6443d08554041c0000807050301c40d0410007050320b40591b25180d00107058808642042451428020a214003c00c0c0c003040d17540c0c4100000c00c080903035040c40c01d2880035442000d019001c640c9840d0304040007401d046160f207001400174025008034050f040101c6d940c9040340d800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 576556348 1250 576555098 576555113
    0x4140909011b0203210402010c0311031c0c120b1c050705031203090105060d030e270108010c080c070f080c0a15020301090e010e030d0b06040905040f0201081e0a09 72
    0x84204600d00741c81a68401c116010b0341e294000402403908845c00c0c1c0c02e450740f01c041100214050360b8165191345504681d6107040f00e0000700464042c040d03010420000d02c06610f90350030440c50003070312035001c0781a040144003d0007200c0b8448041c00c859007401050300003076483c0701c0a00c1c0400d8030740c02022285415820f00600e00310244d002250140f1542000072311802d400d802851281ca9075034020310030780c3d66050520030782d050700e0800140800c03400c0f400b00304c161034074008688210303900f101354400310003107a4080380011000703a00c60301290359981d4a60000d50b42c8a03a025620070510145e19140000075a60462001c0600c540942122000304c0c8240708210709201c081807154000d5089a004040c2c4c400c0f41d0008d601c01e200f8815401d207058080714000006000f0300340000f100e40702460900700406040d2015140750075140e5030113841004003149098107885a64300981c002d40404241040d54030000d4200315026091400038000c450070100c0710098004119030150982da0081036a0340240b42081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 576557598 1250 576556348 576556361
    0x30e0415050f1e0d0b2203021b0d050718060608060604060e030a0501020c0c09130510020307171611060f130602071416060509130b0a050d030e090c0414090901 70
    0x81d0700c40c4d4603500400600c20001307401070103501689020754910005070f156144042c040b2130010003580000440c0240321025480c41842020090002d0400000b00d54a46080c900e01d50000d0324815000a60b25400505510a0201412050a0601c55800c104000600d1401244600010008030850100303a640f018070104450582c0980255210b006000200b9141c17035245008500400d1054005a0f5600c102c2900a0f038050b0404050082240610400c6010354030061194040c00500b0005007180c04011480c64855460007e03440c143e0075030501c00806039203c4040008582c0d009105104042c00100400342c0c0000000602c10250300252411070003a0003415405070041001d0f4168880812010410b203060300c403184c6150b8041600d81c0025600d034042c04c6002600004441c1c0c000d80018503d40c0300070700070300340184803000c0540d072100081c540d01c0b0b8401c412800a806040403d00030b040c07241d041d035004003d59603071609050410321000f41da1103086059507c50311185020460f2000294005c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 576558848 1250 576557598 576557659
    0x903040302033003013305030703200a050c0d030b0a0b030406061502060928020d05160b0c0706030c0c0213090b01140102100b01052212030e0415050f 66
    0x440c0c4a40e91440c1211b544480b0310700c4525800c040524032050610010394034220b88505c0e0b01c4040c21901c607100c00b00c004043e04100c190703103020641c10743d004101a100180c1a0100c139a5501907941040d11100c80c14680204041000c0c18200402411950790b8407100005444803460643e03166075850030b1103809070259500451074109084881c0c0c498642c0401c0880c4290310020448003d06003080c0021040c038070b144400b5240c0303444101c45000602e48000c1c0310310524054011203568280301c80b5521710404c0c06500c0800aa00001190400100705002410042245040c00c1042940142c07024051508101d0001d12403941103540300200056035000e103031401d4011005060720340c1c5131484c502546464640240c00b41c03003020700c25005c098040c010380401c0141079640707d00f855050710b02e0b09040f0550210140e42550140070102e02c0c0401c5504400d0514041d9894800c010703600c1d401e1004440b882c042c03502c100c41180d1000d000d540c90391180c010002005450307100135141c5a40c0e80b481c241c4640c2008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 576560098 1250 576558848 576558943
    0x40312030213060c05010b010903080f0d020c060a0b01021608120a120f0209010311031e09071a0301030210020f0c011116090605041d12070614040b010e090304030203 73
    0x200d0fa0b01c2e030007001c15112504c56002000080055001034030810700038800103018042c1008410100b841c50b50145c0b0018510301409424581701c0c095071420f0620482c1c22600c8203030386500c1d09415690400c55078100c480c54858104519041c01e4003ea214203182200c00c00d21140094580c000703a11070804682040328483c0c0401060406005501c069404241c803940003e080910080540724034808aa00450380800c41061329005800d180320b220b00020b11080b240e024124001074880d03045421030b2085000604569620341c1148100134540003d403071500110b500c107041145240c0c4001982d504000002d08118100d03a40940e9400d24100310241b260380b24402d101000647c100c141d0300302d403044e00c03c121801d2102424600040200d00b02e13400c10012507901540401d481120321100a040c0d45004660100b41c282d0b40700d4642e2104642542e084a55668038001080b02000300303d100f80d001890714002d140740a01d10b40020341d031030f00402521040d101c2c070000b004d9450314041c078503201003495a90b80c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 576561348 1250 576560098 576560137
    0xc080412030f091401170a021b1005250c023007060206041a040807140303060a0f0b1b0c0316030c0801140f07020c060d09021e060403120302 62
    0x203005002103481c004400c04140711080c041074018100d500b41281044c180d40e00600040e508018006000f8050000301c5610750800c00d520240f10701840f9030203060345071740003401c0e6450848400001c89100800c1e010032100b500038112601d00d0000c00a00504985181c02c0c0300141e0140001480741c100f058030030b8440b19031200d451041c46078070180710074001050070940d104c040d0303121021b9843d01400c9800400020782141070b04d10340c68009035400e4006011300182410510581d8402d00360070841200c42c641da0f0b1010080054a00d04900500058600070303000e41c00c41454000c01c0c0195018040c1c0407200201c0303240c50b409003503404001d4100482402002c454046900810016001c04140010707600b0f03403101d02c400305900d00705018617485924115070350b09841d600c0307100750b07002c2c0340006d4030f9402140103a0340740c401c4030f40c1d603032000d40107a2644400001b50340c4070910402c4042c0130030005a049507036100d52035181540d900703801d9070116130b082044d0080a140e5841c04074001c2c0700c1c0b4180448090200b40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 576562598 1250 576561348 576561353
    0x18010f05070f1b050d050a03090b1e090d080c22060905100e090615120a1517060403080702152a0711040218090a0504121706010c080412 60
    0x60041842540c8a0728440d00003035100c240da420080c3c0c8090f000340c4c0590040201c1500c240f00070b1815445600d0300240c0e8011590354041001c1c02a1805e9907070021411918090290410f0184d40080b0943c000308604088020050300a140040c51740190700800310390791a00340c0c03881c8114071a000761816001d040c3c0d81c403040301a003926400c2c024140180c84480c84222003d00038607201e9401c0c1c034010700d06545641e461007048640c0300c03c0c0702d00c2c100404080c0b00ca090f1400788088000d0203000c03c00d001040002109002d491422001ea008101c0d8002c54a94009003404c0801c030fa0740c1094052a000ca80f81d902c0c0c0000b40d1038401c03622243c01080100104021025400c0003003c01e03824084607008943c3d918800c07c103d550b0045000140003084c04400e524410f00d01070340180140c10440740550208101200065252070044402c030716020b84132030401081203561040f81010a00f907044c0301c0c50011525440d1015035400400302414000b03103001140600c00b844065600070401d411170040d0600052 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 576563848 1250 576562598 576562607
    0xc0801050a0b03061e0c0d0c081f030804141206131a192a030603020405060901030b010e0c19020a0b06100c030e060d06060507050d0302030f18010f0507 67
    0x71181c10034014585150300049190109480f8020f9a070200c003049402c030700740b403c110382100c040c024900300403080111100e044070070301500b9492034140e114004a440c005010944501d02c40380c1140040361259010b200184084041c1c8003641c44480c0580503600c0904041060240709030794500e258400c0904004c564541c00c640080024030030416072180b40c84496009260356400c0c3c0300503045121072000424846a1355014a111080c8251407118030b040c44403662544200560407180002e4443d5028425400c01c0d0107002c2d005041a03400c01095855511562a1050b040c00340d40000382d5003c021584074541d450542d80414480c41e03010307030045a82d640181d60346200d500c040343c04200410000b41e2504d80051488020070003911140841c2c034090394212003031119100d0081d4002400e2013200e08400c118460070300541440e032203150381d402d1641040d51804d14a0310900007014010804c109004005031040e03500400306001d140170006032144410f015228100c2014040b518000420400c4d40c1d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 576565098 1250 576563848 576563851
    0x70f020a030c140a050919090b07020a0501110306010807050a0201090b01140f04110f0912121308060106090905040f0b0c0418050c07120923090105031504060b010302070c080105 78
    0x300f0507028000e28100c090000c48021403051607401052a0002042c0402840c04008110050390b0001407a002c0d5641d5030051440c144e8800c401030384900344410411400344181260302031404040307030651400c90002009020f008048004000c0d0210b0305604c858000d40050800c0c0d5440651000705c1c0d0b858808040941c03401c1900d00744945c040c1ea015440e81e003090f00c11800461031341c485552a100c24902c8281c1c0c0c550100074260f41040e08001c4032601c2803020701c060019140c90003101a5110140c0505650032080d40d0800d9003a034000100411409800c868000202c030102d81010600d51b03524180116020324031000604030380248400c02000140c650020403d548540044400034017803e00584112441290040c25a40041108074080740c0354002040b1a80d07040d15100b503e440d141e0031800d461500240c11103800e028520035070411490140c003d01e000d050284d004241c1a08142540501d140c40604007a11980e5180d020341c199074404d804940032076170041e8413011001d0703603807590354004e050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 576566348 1250 576565098 576565109
    0xc0a21050f33060d0b09100e0d020105011e030b0c0f1305031015090207051c080f0c030609180304150819020f071121010504050607080912070f020a030c 67
    0x102d10b203a501c444051002002d0003400c1c040e05108203d4420f030740e640b01108010301041824440d046407401e4108250040205003a85c0c074000d450006070401c3c0103425180e040c0c11080c0811034414031484020741300c104030821290004030320715054841740c490a059110300c1360400b50052000602c1500d5507910300c044000c03100180c003113494110034412800215a5500c80c2d10005440d035160030803000710182c0182c00c4050045040d1402c0c41190010400105100001e1002103040a400c20075203000014806034404101c400a501c0c42c9421030000c0c5150074010103114248041c50086241c02c142081601c0240c03c51004900c0d6200e00e10602500c072201c01c84030709130162a2a80c1405d5440014029210441d081e140d21604100e0b1340d5490403c0e0f440d13018166900010124660006003c035075001b500c0c1010b010300009580c3c2040d080090412400525803014407030075105010340d140d00082c80c1d00c604d03440d00301100d4440e0f4132460100502140000081c0d880700c40c40d0008814451281ca28004545 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 576567598 1250 576566348 576566413
    0x50c090102120a0207030314040527010909110103050a0b0604120512040321030b0a0b1b0c1e0d14011d01060609140409060e010203090c0a21050f 64
    0x44900c1e10043c4280344a040040e0042c081c10000039014100c1403451580040d19541825140c03008500342240c4844c040c0d03140030028071b0000614540400c168003401cad0514061061181d10746032082c140301000701d03060405555030000784640b00940c2c05034054a0005011983c1c0d1a47c907014407201c100e030301c4002d60741402071000960958066404480031242c0c4034010313120214107070401080d41c0e0301201d816020700d511915071220982e04c00d808100030b4a103d101d03140d1107003030041c00120f140381c071048200c103a94805902034036165100d60802032b02c1407594401d40740307103008440403441483c0003110081c561000345a52070300d03000041d004200d48400c0c500c14180c00607001202982070303c01c103108110100f11450720620855041c0454000c4041e005880450070307000c0c44d5662402c0b61300914000b00543d6010080c40f0040c10140071800150b40101d603028004c0c4c4c1400c400c10183d156400d2504d00d64000034000c80d00b0440d09104009842055009503500c41810042009016020281400720721 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 576568848 1250 576567598 576567613
    0x60f0e070e010e0403090803071b0e040c090509071707090b0607080a030c030e0f0c0405060402070503031303030e06311a0604110a030b120c090a09060f050c090102 72
    0x1200000c0c00408441242161150503440c1c1021454104806001641000340c2843d0109040000300003e01005209007500d00265107580242c6c440c00c40c5503044528071545410910012882a18150b41541c0200e80c0002e00341e226840c000e442c02c002903000e102074a0340920302000d40d410201e400411250f200c5014402080c8860800485100750500204250302c1440022480d0340300380e1004407a10b00d02d007000151613440221942c40c09942d84803070451980141d00403642c0c0c1c01c15000301c0703401c1541500c0950070980b040d990251207010003000c900c4540b100407800d00074580b00303411001240011034142c40090522640354120b04290888405107000340894000c0884220f402805442e0340207042d502c004146041c0d050001c10001c1c0c9082e40c41511441f1b02100848140020815103443d40c500141e007041201c00c0c003840100603804d15445810803052075490b03445020006611030070f01000080c048070f40d4a0024010300c055130440021500d803104006401c94410003c0c00061400d03006c48070403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 576570098 1250 576568848 576568871
    0x60b0310060f1d0307030c030b190c1202070c21110f01083607060e0d03020a02190812030901140103020a06051e031005101404050105070609050109060f 67
    0x9030300c0b107060010000f02c00c4070000c400d00a40a0f04401c041c8002029612000d60f42d8807003c103000701c150400d40721401190705010b899110120303160407500049505001c030707146804014010b01d422406030603125800081c20410041d098115501412802030005007242407106101d41d031490100d01240d0a211400c503d01080c50402d0b4541d442c0d040580d10425682d40381c581d40c40d000341005002d000d003209400c00c02010302c584040b440000c2100c40b0004d00609142880050403500c8100340c403800355801041c001c1c00f181e030200b801c0c10041e40545000014800c04c07104506070100640c0860258000d00516545c150568402035005c2c0c0700c20402400503800c100d058400713170b0341c00303210095002045220801403a80148003a01480c000c1a895050110110303040f0300e4503501c00c4408104810f180300c0b06116a01c4c0c4240c180c0804180303072030445560880d002903d6002d200e14001c1d58103001020800b44208120ba40050308000d07446402442000e035180b5007140600081444c0040b80ca0911340d03083c20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 576571348 1250 576570098 576570107
    0x3060305100603021e040f0f0f0b0111150c1605060703060605090306072102070b04050f0d051210090216060b0f0d0b0601050c07141305070c12050d060b031006 70
    0x10f9a40041512030440d0100302005c0e060a404503041c3e8100d610b4050001545111340710307004506903580400700341c160034000110304603480c0b00a9203050103440d070103034140c85000040035000141c119500c22041d840707110800020703006500f00c48003001c1d4840b40602c108000814070310700800075502e061101546a0fa02600c0740c1c0030748440e603500369018800085209115901414003130115490703100c000c01198a401042c0d070b001650940e410000501840704100c410005410300200b08006855840e108035001441c910951070020300c01c500e010007051860702d0002414008094080c0219900c00d10b04800f060b143d60025000c0e079a661828510703031041d00300708004c0c81152400034008040c4182941d02c1056022018003102c0c1088000d116030940d40c841040362030301070807000c603000d100a580e400c02c000d10550103258040c1c400b4281010b000010741c2010382c002c103040e80000188200700c1c41e010101c0381030050b40c58444185007007008c0000d0340f029038401540a00c0707442c401483d42c02d17183c01055a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 576572598 1250 576571348 576571361
    0x406020d120b030c010c1b030614010506070308040b1e01090c0f02011104050402160b040308090615100509031006090609140702120f040302131e060b031305070e04030306030510 78
    0x68060b08100c40407826584206c400c01c9449100b060a0005900c18a05a0782504019081190b50995801444a0980b41064401e0040c01c0c05c40325180742c140f4070b64005101c80c0c00548003c00240d48807003c561881c45103107100382c102450000900705581d440d0b42c204060000e001c090800b1803107485421080c20301c10b00900031003242280b41c0519107403a2405010080d807040a14070300074501c2e00c0d45030000030800c1880e43d0182c0d001e582d030048142810f2500d82d04040b0060304400303e418809079000115207420300e4401c60f107080c0d070500c81c2d161000030340030a00b00426040c4420f8158a441c0010600e20101d501c0502a42e0441c5400c004111001c1c3c6281b155000954004001d640190307994070602c0303848002030144001010800381850354039800305156500b240d442c1107485444070031200524401c2e100c00c0d4280156402c040c1b00061600c1c0e1b942c03020384409424450a000d80790302c0e80f400d0180821444005240d044a26206807130203040081c018000c60004a07045d000b0550801d0031519140202d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 576573848 1250 576572598 576572621
    0x210082a0f0f0d020c03031b0304050a03050a26071403040b0a02070f20010816090e101205030403051e0d03020d0b180a110f18010903080406020d12 65
    0x1440c040c1074116080440d0030660404840e900300300804040e840640c009401ea034448800116280c0c10160f00d241c00c020b40c1c107a146036240500340304002c081000014403841d565058244a40c0da01450b08007210124402400000020414041c40c201d018409103228440c8541c0d581d42a420b4450180c80d60540c1300030b0740c024040c007841c0780105400c601c1581c02026400c0c45480b00d0000415541d4442c078140c0300c03a840200c510769400c480303481d042d600684004d50002560244211400e0305a001030840200740c01000182041040061103110a030744220010746601e60414600041901c1c4c0641c2d241d000e4007045601d40951407984d103804002c1e0b01d0a080c02400c0a0213417507145200700d8114004d4000480c00d0702940d442c0e2403a60b8043c0c440d61450705840c042d2a484c4146032519441a0050740c001a00c00350200d07c1c10403140c2c807036074100015140021000d02c1c00031507014540b03004032102c00700c03500090600c0000080004485800241d00e400c5079800b901d0360318904890300c460303100f166400301c0c41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 576575098 1250 576573848 576573931
    0xb0c060f090a0c15110d050406030b0f031b0613080a051b100c24050702012f090409050102121503060402011704030306090c030c0207080601240309021008 68
    0x707200a545140700320920f13410324941400c0070210301020a15040b8a420b0b54004514005014460300754140100031146c170027030f106088041111008030f940c2c0d001482c0c00c00600e50115010510aa80c0d1a0450b0f0700e00c2c05c84050000310070703150740d100350b112507113660115210700c00c640d1030700705906911140c0b4420040c0240086092081a007080d01d1030160314030229a520710b0982c034a0300310841e0600030112010707001000100c03460115406421105650080c07445440c01030f420000c00000c05010001d24505020019101c00214000c42c0103440139200042540d4001f1030f10399440003440240c0b912961140e01c144024062000900d41c0303604041d64082e00242e0440300b000c42010640602540007031103490006541541c3c1c0c0e220034221681d600744c4900094a510264202e01d50400141003d810450050102c0b54900005c00f611072004c0201014400e10a0f050040d46a00035402160800d8025104001828006800429510b021070311951081100c1c210404013881c0e048100e2110002c0411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 576576348 1250 576575098 576575123
    0x2040f0e100807180f0203070e01110106080c011d0306040614130503040b0304080702041b170c090d1e0305041802070327030c081615120b06040b0c060f090a 69
    0x1809050b451550b8401d0042605c81600110b10f0704184001c6200340c01c4c0d540c42c0614a02e6000005201d01440320554849a0406c0350a002c2d80101040041e001b00090900626a58001c2103c4014a02c00200543c0c540550010002441603a80000e00c003100c07012000b2045607030f81100684003000803c0b000c2c0080e4014401480400544401503400034000c0503810704207d103da0000d4261003060f40c2c442142c54000d481c00008035045a4821021414510701125600e064518003070b0342d00074000010301c40e00d401ca1046041c07080c5003151002c5914844510800d0b04241d08010b851644148602503086000640c0414841c0c054030a9800156240c0d44160380968428045d070703182084d07000d030b0f00c0c0344203982e4070300000040741e02841d03100800105018100074905c1010744002210f81c1d0340061552122050307849105c660228080301040d4801d0b42c0040e41c0840749011400500840d041542c442e0340010701a400c8020004000f88a0705058041c0b2240c1e69075907032400e45403400c0c60300c0105070100002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 576577598 1250 576576348 576576359
    0xa1101051c0203040c08390604170601030203070b04080604171303050c040e0f19080405040518060916030206030a091205070b011a040b03061302040f0e100807 70
    0x18000d04895072850a404107012004864000701d80c01510100c40ca002252410865120b00707000e00b14120a034500b95500c00c2961071a01e21929808602c012201c81051182859995646090b1005490000707501da880c00841480399a031f4901c00e0001fa44a40301c3d13047d0000721b9917000c00803503003525003e1004d800c6988075079503210089204040300724590a8180141d030b200d12810061040150300410003094030307080d1ba80500040f01c04100c0f00c01415000a04d0388041010009003407100c01046032003803c0b01c01542c0c03e2450031030003560001ca0348181000e003480403010242c030307c1400c84800740080c1d4481c0d03251a0304c0d0580d01c6080d1031584000d0500008100050314204000d5a4080714140b0003094071041c940c0c410000380d6404c0441408601c0100c4c5e007500303115004414901403c0c022039010940c80841241c10000c0c01103110b543c990030382c00000590161685aa00d06100c0804501075440c0c41e19081d1304002c031981070141d80c5100f560080010420700c0d51041c103004841c00500549a84c1d410315 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 576578848 1250 576577598 576577607
    0xf060c03020a080313060e030406050301120312050c04030213060806130302070e0c04030b0c041206020d090c06080a2a080c12010e0a05010501080601171009090606080f0a1101 77
    0x440035800e5010b4800c6080c0810391440043d40301315607040144030740080603c0e1510890b040400460303001c0c4c0c000e00c000e2112941001c1124151040d044501c21020701724034084680f51b42c030208038880c3c2420310b0280480151040b01030400d80c0e100303c40f5071005001000c41803048600600c50b54019600002c003084d01c00c0307015a11015428068030580720725035203440c810101c8004c161000005008000b1301001400b900241d000d4211589140441c501441c0071424049800754000242419a000810100d22045507008048280d809100212006c2e600ca801900b840801c136801041740342003a81e001710604004100c04966032140c1c400300b41c00c4404000848a462009252100005013005800100c0c59080c00040c0200303c1c81d810032005249c43d0009009071041a070242e8103000d55801031042e51703a0441103003d43c000c00201c08480750390300d0341d8000211202a50101c0e40552400340c2820074844036230070010507501070000301d400350010020300b1903661a034001c2c0982a2143c4000d207003141d600c44d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 576580098 1250 576578848 576578867
    0xe01110a17130b130605030c0d1e0f0b10091a1e0301090207050c0a0e160e0409080c1e120c240601020c0f06070213020d021614070f06 59
    0x300006040c0b14420018000d140e0315508261810400070800f1a20114102110405000645041825800e0188000782070340a03140d40c0500f034070b8485c2d1030301c4050300400203106c061412aa806022040c1105805030007460203484090207200d4120030a22210301440d01c0360304450100500d05490041080704480542208d0401c5440c213940040040c2c0b103891b002c0141d03020307001a0070300603039596261030310a150000324443d2500400d030b04582080703030005501c00141d1012248001e2000c11280927001c8a50f4400404c419a01030300e0440c006c000d1124241c081d01c0016011011141d8880a0b0000704000c21070040038a4865031041000c02da0790f40000000d80040301c2c41c441215040030a403a051851f0242c2c41440c12050f00d0b050301006070569041150390490b100c2a610f130740d5100c0003200400e0061280401c0a401110101d401f0204904a039040fa01d102c21134002c11921000b044a141802c1c080740c2100396000241d080b9440614040031030f1660407a4242c040d0491040d1914205032900c007107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 576581348 1250 576580098 576580133
    0x8060909030906040504150e0405071d100501030b0d0203100608100b0f12010e120c0d0c210903020d06090302060f0705030403031a090411010906090311010305060d08040b0304030e01110a 82
    0x10141c00008c5d1100c81f804042e0056114101a001007030400245454100d5074800d030001c01405142404405d5072100a08003d441083c030b000300d56401c445020500b00000408000e4251041c201d2000c20400d4690200f42030302d0a11040e03c0d4401c590481038002d50f04041075040d1b01c400c00c59800a014588080d070a55006e10000010030002c120800c0d213400c22080001d200c20f10300c0c00056484c0b00d0700d4103206d4290076000d54140187c2c2c10020361500c0245101d10751035591079500c90000c00e4802c500072007988004560050400d03203c9003446c5403000151465020490141c403491003c00c010303058554030b107841041103969007401e40e5a0350720308401505140080c0701c41c0c002192070710b8010391940f54030315200c2c0340528014824101ea220005000c02500d80c400410499038540600000e10118034800340c070002440c021070075031640000940c000d200400020300498002900094100c4400041e502c518000e0316084003000d41500191075103d4258150605a00090000c000095000112984440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 576582598 1250 576581348 576581381
    0xf280308070b060a1d040210020f160e07050f0313060b0303070501051501091206020f131805010609261c080f130506070507020312070308060909030906040504 70
    0x26600e403110401a480000c098502c9110b4004012050405004040042125051809696681c0701e601c48185a01600083c4200912403881036010f20030043c540c20a4070840603280d01d00510048490342081c2c6202ea0728110f1030b4400002d50503070041d41558200701920031807521b16a42ca050308a01c508035400205c42c0c40381c0d00c11081034562000c1000d4240284a1400042d40c7e05020003184c004483c100c5965041144260003444030440c41c00c80714281640c410030258407400c0c00b54040c28280150404003004980d038034030000710002c4540c00000c42f1500e9100410050340ca81c03200703e5850000e130142040311103002640401c4d17045201c11000c189140f80c42a68064640701d5080d01010741c0d070068543c0020466010300101d20140051290048046110850a80820f17903e0b9074440b0001041041407000100f540d80075524244084652002003101d40f941d226140c1c52301825800083e5481401003406a00082504400104558040d88005e0016040c107281600700005031640303407203654150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 576583848 1250 576582598 576582679
    0x2011e0f090b0c03060307050307060203250b0708010f061805091e0108100e0102090a0501110f06070807020105060406080c100e091303020d050405090c0f1e090406050f 74
    0x91054000c5501456103c612a039503070801008152600071203422041c420740019808206481d00082210071844490110301c5100c0e000303e141c0e4650f94580034028003d15403040401850030b50040032076042e11602044401c4403521000120f9000388120400d03a40d000ba208010312442c904419034035842018109020000c03003042e408501d42031020383c0140071a40c002d503410501c880b41ca02a03100481c0900e0001c42c109031a58001400c00d078081e03c81c1905011041901c04180304081c003410703246410400480b1603d0400c848000c142c00c0d070854044005500c0c00c3d01203000c0d031801d4003507101140c3c00038005040e034a141008104009007540440e005018217280340e05d5040d150490550b2040c5003202e4260a8144a400e000e0708140580360310300b0070054204000e00c85036941c6400150040c2d00000d21a4a400b055407107005544280e41018a508000310580040c0109150040031303100803e54040c44515540e00510101c2e185801e00c503030740598003241022080d00c001c02c441c008103104811010340c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 576585098 1250 576583848 576583853
    0x402010207090e0309151e0f180310050705030402040e06040308010314030903100e0721150b040e0c030c04110306040506060909010303020a1a04030c0b0c090a06080a0c02011e0f09 79
    0x181886401500d0304694003145801d108034201d0a03948a00e00409078592408c1c1c94545c0010003403059106802c00c4800070345c0c2c1500703c0c2e1420000700600049000d81007007181032011028190b90001c6404038800e50800c50050f040e0400868503501440d40358466890036400d568481c160440171104218062106000d024070a54080100340c0303031101104000100720807698403441c24400c4070303000fa0800002c245c1183d022046000c900b000c84030381240e5072100c1f021118124402400e035a000c0300d540701f805e100240c00c1d80b002c081035000c82800d00f24100c45080ca0900180026112011003802146006000060603420250042d40e0b004000801d07491401c00c000300014031049080e08290300513440800365000b0440c62040071140401d49140c0c94a443c0740540c0c0003441c0c40b055042c000c0ca00b082000224403018110826242c81141c000d00b210b1130640ca41600030040101164074405031414071440c442a140184038000c45850000c0c095500160b0b01550341c0040c2134008000c217291703552541d56401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 576586348 1250 576585098 576585109
    0xa030c11030f0d0b01020604150b010e060c160e1303030b030f070b13060327030e060315090604020304020d0311031e18010201050c34060e070e0402010207090e0309 72
    0x14590321400e540750322000203c0000c4103c801c2d11035042d041d58882014400812500050729003402c458400118204640e0001200c1c0d01040d80c440701e40010021a40068215021580000300c10300441041c403542d40d110150307480d180055070280f0001c95000110404284240c11200000344058216542806140006441c2440e568402491601e02086004101d0702d90415000100110b181c14060045d025039504079000302c1e100d403802079400c2c00300c02804050040a048003480d0f0002c000d03e403130345852106882506900d4080f02e10450804001607d10301d041d20903240120740183c50314031034016680d0140e590b04d0840348a5411403005010040391019030140042071950b2703407100c682c3c4135006001c0c0038445200241030a81964100410170004034164019038204039644c11101101b009910304030382c60034007191400103040c620454410b080c00403503001020408180707012602e54035551101071420101c182d40090050708071100c204408955074200c0c0541211400a480c9403030389960005d003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 576587598 1250 576586348 576586357
    0x919020f0c0a0c080313140102010e1002131e03081b0105040f0b0609071202031b0331030c110112180c15020a23160f050a03080a030c1103 61
    0x129070340641d0007201000890400d850042410600170b50a1100e4905102900b02250080720518019907420b40c00310fa01c01d400c100d00d00034010041d81c05060b020350090029510245a0100005a050f00080c406542c01c411017006000032016844071420769a807810981d1040b035051903258041141900c01c81c10a00c236050040303100c1c4510610060041c94114484000101040c2c81020000300304800150020a411201103101030016070742c2e0340d4000f580e4104180003840c10039040e4088104030f011603030400e150080954450102160540c04824050a03e40200c3e005001501c104200701c000344105141d580e001b04d050401e08115025001490110303904081483c5002280144840c2030142c0d01c100c540142070039050080c44101051006035031a011190020300c140c490380015401401024510b04d041d07004001540c840e02c0052000c0e8001000c1d6004001c00700c45c065000140310b2510b03124003022250f01401040c100707c04880254001d09107240080d0511140c01c1d00d6110b0b1000070700081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 576588848 1250 576587598 576587617
    0x12020402210601120207080901030509030d0606030e10060503190c090519050c0307091703120709060e06070201090504020c0c10170604090b0f0705040510030603061a0919020f 77
    0x1401d0740c540803000401800284c011000d8061040019002055850b0110350b00404203003008501600c2e003451b050301e144030328002c05c2d400740c3c40c0c10000b00744290b040d04200c0140c5c91420448035405641102c540407030f01c071886502d03450b5221031028074070052107440300040b580c010340b00549680ea4503024079081d603000300c038280d4a450018104890360070052240c0ba030004032403035030b990075807400200207000e600b8240110350b900c03001070b841f83c4109402042161075190b0380412420072800c2403c00501658403070f0085c0030100d00c01086000382c5040c64025a943c0580580d5150b9040d858841400000d5000303c0701e40440d030050350b40c400704d152515054001452a81c2d640c08503408002910071a0601c0041d151610882c100701a001c0428080881c03260083c1003059165819140c65805892510890f4081500a016080802083c035059801401101e01840c4144542100000c1200d00300b10b8880c2c0113540200000046035522205aa10001c07203071070030000501d48103015840d4481c540044541 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 576590098 1250 576588848 576588907
    0x81b0708070803070f0306051c0f08071b0909080a1b021206060103270206090a0906060f08010b030f19060302030111030610020303010b03070e0f060d24080712020402 73
    0x1481381c44c642c4648000d80b40c03501d9250070081141400c0c001802c84580d030350907102020340100048148650403494452040d440552555501040e140c102c100d603902d084202c40b00301c103984000a49011034050581c0480d800071b0303110b14010320401d06403050a0f4403c1e42034554200c880c4110016110080d40100008440c80200014a481c01c00101074881401c0410003900e1440043d48454100000c080d40031581261754607122505040460f141d118140d02940c0b40e01c3c00c0540008501d038100e10800041c0380369a9504419a0301c80720303030598034402a036050750300300c032114000f034501c0310403040d04410f0400200c00452420360b240c0009003911584602407021200000a00003a49029840141003074024000f441c2150702d001c084518a010007002401402140200015565601e004007071400030300924481e1113040070080384005200c46100d5255081c01c5245070301001760710111440440d01c83c080240120ba09060f50740203540c2c2c07213000890b040354080c446003907850b0500103142544151302a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 576591348 1250 576590098 576590101
    0x311100605040b0a0f090b0d020a030b01140103141521010204080c09040503030403120b090c13060305060307030807050f010c0512070509060909060a0b0c100608060106081b0708070803 81
    0x2c12007101c01042d94584103d490754810407070380712128070103022941c101c00300290107042c95020546414114138000d60015000d0004000c0000f5500380c0d40c144c4201c030b85000700c035a0801c0e0055080b41d143c03020100d007000c604000a0b004070808110244485c0001c7c0642001e0901c00140c6030540502e100140182d0b500490188440e480410020b24100d00865404406c1e0800d0f0320344a40b60f01c000b400280410095004144032148560081c41c600080a4402401c0d03140132500190035402200702140e0045d080308002425500c01d02480c1c1c02090000c0140a4940ca140d4401c0039503880703041c003201c0c0ea0150840e94010034000784950900321080362a0103558600340d4860040041d4010503079406d02609226038006501d51400340c4440207016110050f01e61101c0300081d001031099070015100d1100007507030700700c08140841e000400e003c0080d001e010403500c40d0707220b544441003400340720005146800002d0890080b00081e50000c9045001305280a98a44800c6102d902011055840c26000030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 576592598 1250 576591348 576591359
    0x60302030c06040e0c030405120313020f03010b06030a0c02010906061e0f12081809040c080f0c03151f0f18090213020a020c060715060b03040c1203111006 68
    0x19419a0344002c6030740515042c18850031560300580038007085171036072000c0005410440204020588500312501d01d03038403403030310303024a010700c130366460049000b1000800700546600301400703880c50300c0c1c400510f090300b56502c01002c03100600421001d0001c540d2078030a004085101d91140b00c8c090300d10421032081642c001c00c1d6030200c803007040d4424180040502c104020910740e0303001e100034042c1d001150036aa840441243e104440780400d103640c0c40054101440100050716015804a41c10700064424130703401862000e80361a50002515055000b0480c00b90103034503803206060f0b1100e1020710643c2054824020f0380780320946500810410000c10307809020f44000740f40303a01c210320802c00080c410340ca02c0354049000409000c10741d02c441c64020842c100c500f03001348036007420190090100b980701d008030306102c049100e00c074410044031450705102095804162080701d00c983e4001c00100c2c1041c0c0740554010341e506032070700190104020349014680c001070a012900401c1400b0314003140c0541482c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 576593848 1250 576592598 576592603
    0xd05070806060403030212030c040305011404020111030405011202070819050904050f0702251e03020a0e06011409010314091b0604060f0818010c0f0320091c0b0a06030203 75
    0x1d491a4481c100c18441000001c0e4001880034040f46116070359612030f10340000140031801250002099942040c50f40703040900550301045c03059000f40c3e5004101d482c4000c00544a10a03409102c1c0000c40000d180400d03442160000c1074414032506049203407100d24950484803810040000780041c00000d03491074280317030038001d5a030007204891100e056030810180103503451129081d1000600c1d021011507810b100743e0a00c1c3d400410b05a403c01c080c0301c2000742d4440d0181c403207010880c4542e90420f0003180d410b1150380d00720b03c00c0c00181c603001c0000016500d103030202d80040385218105505e0742c2c502c40980d04a16041806610b90500030000c1b05100303290581940301c0b0b041154020101800200300c1250702640141d001c103c941000d030801e44901105c44003000301824266001e600f009404410240d05c030300f81d2000100c017907508000e616030a481003d003001c00d12010713000e20413060255002c0391902c11810180340c204040c800a407032105a45e500700341202160a46a50380d035981d802c10560505 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 576595098 1250 576593848 576593851
    0x1060602102a0305100305011d011d070302010c0f080703090302040b01020c010e10020f0604050607020d03110d020309011401030809041103101403160315181101080601140d050708 79
    0x10100244000d06101c010002d018044080d00c010182c0b41c20108042c4094440c0c40000b840e0054006d00030369480000b00d03a21060510044425580780c010410000c0d10040c00b00c03246042101c0240c84500d2960b00115035800d20078009a81d458454203501002483d0352005085071032007900c400f0815403031401004200d40c8001081410342d080030800d06810783c0d00c91080600d100007107801c10080c60000b1000c910708035245440d500980300b033400b848207004001035090301c03d0806501315107000c100e00104a041d13442e0114082021320060010540c50a0300d03401840c2c0c001004c2000145240f141132506000000a80c010303540f8810003d0542040d0502c5d01501c00d501c2031000f049451403c2c14204a500049948280885240c03031041e0702106950038041c0c2003014442030004500039840303041c2034468000501e55042607500c1d111600d91182c030840c0045402c25009081106403100307c100664002c0c6004090904022046401400d400348034806403a0400188500150500d010f1601400d000c50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 576596348 1250 576595098 576595121
    0x1502190e060c0706080a0209030105041127010306051b1305030106120206030406020304030203070b07031401060c0302150703020405040f0e010b0a300f0b19020a0e010e120106060210 80
    0x1420030041508880020301c2c43d04403480c03454551000d80d038544071003001340121424154554205002e03c001d0000e00e10607408a01c1d003c0b108140f18a683c805d041803840c412003000c07006c400d4031706c0040000c241c0c542e01243d0b00c01c1064448200100d41510400175a0b888070150038200b640083e005d000b01d0a00b403103148040c2c064240d801c90a8902900021170901008100030440e40c1c0010000b810140300707000f0b9030a055440407103111103060a00000d0301400701500f40c4001c60001c030000044251103046080c58650b09a0080e10110304040c103a007121500080801c0241a02040001040e4a4900c20000c036035000150014045418842290940d0b0030005070318031440310b100302440030702034040c0035440781080b03021580b1b052072810128036840e0503498030180c00305102551480901c6550508284107110400309607940440b4686600b080b0b009544034900081c41d41d035561011540107032841000164000d04485091154002c036900b907460b5904000010b80102c40c00c841446030a010390010f440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 576597598 1250 576596348 576596359
    0x7090b04050a12060e0118050d050f03160314090f1207050d082a030f18060a0c0c0f2103060302090412030b040606051809010503070302010c1502190e 66
    0x5181c040014800b084900801a1a00e0080c10000c100710440e441107036203131030b0340b402844085010300c2038101552140701c09841074000c2c41c4010003610321a8003141c0c0e02290410445003543c880038003039400704138854060b80c1810341d1070402c07007948034040a106101e4a4042c0041441741e080c00c400304d06002020015070b82114082c020007000520104207103005090a1030101c1165541c111003807800f0602c81207031605654141a00341d102c0302418011803007420780f0642803d85845050f240d4454413110303807007000d00c5d0f0880d0022441c0c40000b90024450748846191901d15414036454040140c04800821100c00c01264201c02028540044411100178070f401d0401001e0718580119054020040000b004040f090a00a009078041d030700480d40e40401800c1003102c2034589201412a900c450038160300802801280106032408a220f141622405000b0385403261541d4019030300100c40b01011600c2d400a480d425888184620150030085d400022100103038201c540003404540080410741e0040c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 576598848 1250 576597598 576597607
    0x1201020309240403030e031b010b011106071d010c1b30060506131a01120b0f1201090f0b10230f0f0d0b01050405010b04060f0c050a06060e07090b 64
    0x924400b55041e40c443c0d010b003000700c0d0644507410028218803520026070a0750040d1409030322245d50550000301003100a03201c01200c07210108c003d42d99140c04840541c00111844465039100c5c50140e00c1c0c07000003106040190348078109035103040d0440c15124a072141c03155244d00c00c20000c1c9a6840a01110321110180075203034004040000720041070b0200905202c2c0c540300418110340b0340032250f00114840900400c821749440700e454282442c41e0706854001007402c220174507244c503188110400940300502410745944c0c01018401c6401040525004c955a12100760006c20f4a8240c01030041d88503c0e00c003281c82c5006643c9150900c600c1c0c00004481d02c091034020343d14049511410017500c400c845900403000418001100c41c5007501180d82c00111040c142c40400c00c1c1c03000080d058030011a401e00c404d0380c0f00d500d461554001c82c41108001440d40c03003003030031f00740c080c031090320752180900c05980c8410500d40f203100545109521800322070b40c4140402840303984c45411a0042c003444004140b50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 576600098 1250 576598848 576598903
    0x110d0c11150403020a12050a0e15070201180e0c0406090911030f2e0501020705030d30020a11010510270608010c09031709030a0803040206091201020309 67
    0x30355040d200038601002072040482c050600812000040e00d500c0001e20074410380c10007004009402000303c1c14081102e68441c40298645114240340c20030781e44030f465081200f00c3d0011140e1010121174960001c100c00c001107495040d44404074822804038858a903128038001009110a00350f40c882c11425190030260b4200b10f241e0002c03030303400c1800300d41451215220003c42603054000f680400d110203c1c88806d040c0405103c080c184210340c030907000c0d510300599500c103054071003100702e84c42000034120311b0040d41c096446003a561010725427200a00c1d01c128030030b07074880700b240e004030800004100090002c101902c3c00740940756000b8840294000400e01d082c2101c07100c680c1b4000100441690300a02a22855095200b1002401d40c40b00a21012241d0f0030b01801072801d500095030468006059405a113045400311124500c02400038000740c92207403140c13250354002501c00c84e031200e002c024044007560b90041c4010351a440100060b40e0381042000c0b2880c0c0700761840c90021130483c40151010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 576601348 1250 576600098 576600103
    0x91c020108010510111f06061704080c12040305031905090a090c0513150e06070b0115120912080a1404150209031209010810050f0d02040b04110d0c11 66
    0x1190b0341038518580f481c0c441388054850a005210040f41d501c82d9004482030b2004141e40200704221150b001c110013502c51204403036803104250420014030111000c80d000500342401032a240846806172803940307080e441200354945c81a40709807070991000c0341c0155040420004d101a411103401e14624000c458000f040030481c0314480d2489060f80e038101c02d090307640281c0484d51915020b1034103c10080e1210300c550700c044040d000c1200010403507251890a410404112041c01da004506071185a1130800d041c003920290070320b500100002c5809034040114035010f180840d510481e088800600310301c00081000304000c01c9000618241101d18801021101103190040d810060340030400c404229183c019207e5001a19014400c11188046400301100074100c0644240d8039104070f5195110442c00200350340c000c00d42d01c80201d4180c03064074905101c94005c0785102130008505107601c80d0001e400c4444071684410380e9034001030940031104940c030440c15201454104400400550f8805130f6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 576602598 1250 576601348 576601351
    0x7030b060c1c0e06070506010e1501170702100603050c010e01050f04030f02120d020d14070b01120230010e120703080907090606030e060f161d04050903091c020108 72
    0x100b2100c1c002140052442c0701e5811101c01d0340c1c01400e03480c1e03140141d1505940e40c100910502c0320031400e07a004519a010361040c01407982c10140c3d11040d000b043d40c100c070072161300c000d0891800d600c0f424010484ac07020034000c5100960249001c0c003c5c00320fa80300050f02e800f201682003030400108103c080104840d41d4192010f481d005a003040842420b880400d150540f515040244c510565160312062513000692215201c0030355200030b6074449c090801100c034004c03003c000303107008441f034018007112804014056149000a01d00446005900030301c910b05421012201e480205031035816505040900410301c80145040c010802c3c2010490001d02c0c0d80034088006042202040200f140c0f190108940f801918083c00100921540c40b1409802002e4850003030845004500001e003148a01e091200d1049035100d120518241204070b0469a44050040521281c000b210345101c241d101d922980f4803c80c001801142d56401d450104841541c0ba0642c90b003022042c21003010050f6484801079 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 576603848 1250 576602598 576602623
    0x51503030315030a020a0803071e020607020f041803030605100206150607080d0c0201020d060b0a09091d070f050102012007110d02040203040f0b1308070206090f0a0602030307030b060c 81
    0x10b2402d2020000090400a101102a60241c000390300841c6110000c002800340601c10300b0f4161005074000b1402800001d0b28502a41c0000180a000090b0800c207066030b908000040c00062841c2160407961001192803c003030740082c0c1e84450038450b0341007400031001451010b00007001e5502d00740c800d82c0740d40054964964091000412110104082041075415440b02480d0034030030303588001c500a000350401e0740c8901c0028103140780040d00d52491812a4440d988a907180c4c40b42a0600030200e000d403038503050b07075100303c1e10300107d600a15100b400034401420303100b040107240910b000002800e5403d005000d50441009450030000ca000400407503481990110909083c082214002000c0145945020b500701c0c2c0000100400c10a4244401418610030501200140c0b0b48001c43c4402582202006200020410914001d0300e0f040c03000d046000310081006442440800104111042907400100980e1001c001d114455425000d01a10f8060540340c280c00c00c41c01c04d03601550b035944030424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 576605098 1250 576603848 576603871
    0x50319080904150506030127060501050909180a24060608220803090a0203161d0c0d0204061107080a032f06090307020a090b010806191d0106030515030303 68
    0xe602d151107180981d10000c050062141ba169a500d1a81900c9403000841a8041c01402010b00d40c1c0e000240c4034120684006954031030500850310184038002e00c0c041d140e80d5015941840c4003c201404000c00351107180300b003025a89001c80360301d0181c0706c203580fa507015066901703001043c03159a03444001d09070b008a25022410040e0b0160364407000402d55400c0207004400000308005076a50001861079006209400711070107030303000c84444091004a03000307824501103c00a0300762075440c00c5015582240080c4000c2c2d1500c142c82403043c080380d0055002070040782011341c1107280080240f0030500200118006000315041c2694024000400d1405011001d141500c00721510036211603401c100c8840700b030071101203080110020b65250403c500c12880340c1007440d0f001c01c09400b5030182103510001a11080e10316100c8104110b50130000e980f48002404059030002075501c5901d103160020240a0341052142d4140b840003002d642000f0040781d65100340045801140d1400000c80340d00c407007010030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 576606348 1250 576605098 576605111
    0xa05030c0d0c0905030f1f020901030b1f0801080304140103020304110d14010c1e0c03050d0c050d0b0d02032a0909011407180603020307031113050319080904 69
    0x180c0d4049015007482051600d1070401490b0b03441d07801c1011641039600c118125007081c3e9803400e8030b44c2d981c8100341d4802c0d0a450042052240c0c0c0301650050031902e54141804160501d00c070002ca5561000c0d4445030b4002040441d07075041071078001e2036145c007600040c1c0141d450309040281a5040344242841035040560020019041c084208a05075410100070300604c2024041c0c24102c4400d0039601004540307520700011541010301450002d00071490441c01c200f003401220b40c058400f94030034401607060180420010b1b51a94852243c000e001a09807103081d241d0030303200200401c803844805018002c91050f01044c0240e6400994009030040041d603006070b03803040080d00b05003003449088031904030070300c4c000344040b550040d04a02913044085551318026510004100d50303441040481d11180f0080350340c01d0145600c03070b0700115440745031403d0214005203140d0310044140d000e22851640b44d41c044605000519042c4071031a64103040c0d014004101659444a403c184101c0034921300c0741e5a10031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 576607598 1250 576606348 576606361
    0x403030b0402070c03120f09030f020324090106170c040f380d021815090106030c082a0d0603050d09030606060215010306020c0a02060d0903030b0603010b0a0503 71
    0x10410886064007030402e5490b407032203103885140009540001c456403107401c00345419030f80c07040c02a8808084030f55100c8111519584075a410410300c1c00c03040e070700f50003103010b00360000322400b10011610700b21002d2403034030345045107400d4211041c54200300c0e603600e9040c080c90351648001907800c9002c50100e800007442101c007001000284a801050091603141250f070591811561600203c07080e20649000d01900b004420003040310703035604000354094902c20110618010301241250b009182c007906901c101d000340c2c0040e06a040903441400040e0b124100b4800c07055010380b200ea0040007151120701600c03044004406a1180700030f06c0140c03030102085115080881b500f04600454100050751110540520018005203007400305455050500e000018003a20000d80b415003811183c0900c01a41d0a656510f40a0b600c5600b69420742d10543d07100001585c0c4400084c000c03000038000020715041c1d0780c60301506860000346080c0c8100d001341300411003000701108a8004a40700e182041c0d607a038510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 576608848 1250 576607598 576607601
    0xa030f14030f0702070f06020312010801090c1203030f14042006031306020403020a0321020703110d030c0b0a052703070206131d0601030e16061b140706090815060108040303 76
    0x180d01407074000c6d80301100011541e4010009092102100b4400c01c071503030303d410002d401e80741205001000f02c1040c103810071811400318000031702d481c803d19001c100b5202440e00041542e161121940c9100405010302c0200481c2d40c50818030510b0b58000d5400308802e00b0300049440c040140300e041c040145103d0a000c004040d811038020359030003010361030700075203a080c2124007448051808007456428561044001d000141500450f035200b0910240002c17450b090101d640c501e01e0007103040c000307000c0001c400101c005004c2ca100f0191132800103041d107041ca00404041c05c1441280ca074154865080094800d00071045440c01a0103072001c03680d820000d0201402502d059009004903282411009014482d00100a00400c0c007642c061000b0700c65001610303101d600354459085040700801e401c204142c0035840307801007a040000c614074403c8864542480444940300f0301c06458100e20010700c00f040c0c000710b100307001e0503e080003011000c006140c80055401e001c1c0c419030601030503900050815109 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 576610098 1250 576608848 576608863
    0x8030c0c18073f020301090c0927060b0a030b0a0f0609030f170a09030b06150304060c020102040b0c0a060c11121612020609010c050c0c0603150a080a030f14030f0702 73
    0xa070410703c0c43d008401400c0094000780902d201d110b0400f10181c000c18865000002542c1d100c0700d1b60112000d01000b2020b401c02c4122195060a4691600240710b4807500c01801003d4402e80b0041b440f0034025040008541254011002c5860000e909100145d4086103a03000c1c0c9501480d0f99040101c1030825401c0107a100b4280c031415000051307a654946e50124004049038800c020004098607854100219080c40848110f0018400c0c00014003050b019088102401c0c4280001850580c83d4002040340da03005a0b0103502c103603c410121070800c02288120803148003c1e01d0a02c02c042d65280009840c2c030416a082c1c0d00054002c107000d00040752100106c80400c0d030003005030b03c0000e0112006501c3d44801c503000f0b4603039440d1060484080c2c0c0a01c3c00c0381d4444003400c001d03026098852081001c1c640029000c0d04c4a0248510210380644442e40c0501c0604841d030010320302c2c60003502d0003c109050071001d00042140241007001c0b0102c6a4081d0b03a0082c6080d000c001450750754080c12440c0070007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 576611348 1250 576610098 576610187
    0xa050106030c0905010b16081803010527010204080606210d08010915030302031e070f0b04050709140f070215070908070b0405060a030b0a08030c0c1807 67
    0x1030a0380020410682c1c100580864503141e0060001c0e0b81d98481e9009680a41008500107521b18220140000c540d00000d00d00c1f404030f04800c03804c04002c0d801090131124222003800c0c00b40c200c00060401c008480e050305d400d00c070440c2c009520b020b040644881d02c5140c05000b06005070300c091005082e00a40307114803040c502c00c420440d0229070b070000c00100302000a2144400380c4e80b80c203a0b959581b0480c80d40e00300071b07030307030035800840c42c0118000034420074408101454000b1841070000200158000325a0361496003c1c01040d2003906240c02d2090408059071300001001c1e01e0140f4007800c0301d1040d100b49521801000d440481e83d03403010b509038108112650360b184c00e000b910040000036a00031085100b61241001140e104544405800000303201d180915030f07103c5024030135a0241031003600107580e91140945001e0f25550380380c44140c40c40e0003a8030300304842d0b040141000c406003401c58000a80d50345801c5524860701740f03940090040c15a804c007456540f041041c5038144c039216403015513010705 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 576612598 1250 576611348 576611351
    0x403080f04030803040501090201350903040923060109030f1e082d07080d0515100201020a02100209091501032304050606040507081306090204060602010213090e0c0d050a0501 77
    0x18080c031b8024024066a40128042881d00e08200c1c200c170b44a1000c0d0500c8c9000b40d8914032000c03040c0144100e001c0000784150580e02c000c22001c510403c0364029246880074001001a1248501c104006c0c0e9450007801641003141c400800c0010410f41240079040ea078220400780e890104600660f5202c141c4480085d10000c80000c11000d0750f05001d11240403031a00050061071214085146d4001d441202e0b00548280d90500084040c26441e43c0010340101d10211030780300012100e40455401e00c1c9860250000d40d40c0400c140c071841d43c052003200f05400401400310326000000d000076a40d20005003d440c3c25035861018210b9990080d8000f03500d103026600c9182070540c0b03c403429891008102c80c02c0303a10b8050000800d00c01d0402c0d0090758000c100548840c8001d540d2180c01020008154100740e40c41926a445900981c80b10f100b01c01c05028154009030795600310382a8644039140034ae0001c8991843c1500590044001099121501070200c0d8001c07880d1034070703091541ca09148618081c0c00395 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 576613848 1250 576612598 576612601
    0x30e060712060b03041118093a08100f0b0712020106090f021b0f06011a120a0f05090d050405061605070b030f0c0c060f0612010e06190b060403080f04030803 69
    0xc10703e100b00300440c0c0002c40d040301d50041c0c0200c10b5104842d043c2c80303000345980b050b27903c11031080480d4500e40409154020700c89141009403181080702e4103d10303000001c12211000d01420008110044002c1c1c10344141505206107080f14848891041410180580038001c9443c09007038400c0d044880240300d007280c00d00c2410120840d040c020741c0310b0600c031401c44045826400e2034040100f1000250122500600660780c0381202840620720300005507030411004220500d142c000c05189030703014043c4454000ba01034140205a001c880c4040c2a420f00c0b54484038500b0700c490350000032942554001d95401d600d603600f100701280701c1241101c0040c000c0c040d01d400460017408050103148103007038101e020b20704d94580b10f41d110340b90700c80c3d0b2600440c150085000100490040e900140d00800c014100316900e00300c0c04885800c4904400c0c5504043d04800309001010004035640d0040000d214010418809044002483e81c411448028510000070844c000728a10140940340110741081e155a6039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 576615098 1250 576613848 576613853
    0x605072d02010b09040206090402071518170705120a051308032a0604120c020909250602100f0908030702280506040204050a02040f0f080706030e060712060b0304 71
    0x201030300035405000643c68104030980038a00392102d14001c90700600781754544009182804003030351100034143c4801c900002c0909424460303214103040910864007242d40c0a066241042c404000c0b0885103000f50302c284410030100340b000c01c0018403040181e0510303a840000301170546590003040300c608800080d204d0005032048002c001406181410401c0440b1214102e10991501c524003580d0802d03a0300103400113000801d00110b02e214544142450500d404059001802c600700c226081c0038903402940c0440c10008404e40d01d41445003201a01e02c20081c100b040c02561519541c898146031500c0701c10403680741e0074a41c030448100c0e81040d11280d0b6403602141c040d64440c0c1b502d99010001400740d11440088440704014001d085d4000d0107491980c49030f400f0003002d48000741003012019400c00001401c03d0072124050300614410300c00581c01c92a01ca0002d041000d50ba1001080c1401c00c0c045141d81100810060750004032424400d021246103106580100752580000c1c1c10f011000003800b09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 576616348 1250 576615098 576615167
    0x801021207050301080307030309230309040f0c051e0c03070c0602071a040e040312050117010b1e13020403060f020d15030809062b02131e03060507 65
    0x2a4912000403010198503981d00854a610091140b42c0490f0014001c0b90000303842900004056406410610304c1014504242041c5107060300f104071056100044031406420b003402094000c481250301048904501080070b010340c8a01350030f44e00720318031011003a40c40c030030035100741c5c0c0301e00308401e049946504a074034002c0300c60603072130090002500c0b070b0880010300407500030714040d10300321720109441c00c0520b011000c0032075843c0504220188800c0146103000800c0b6845154000c040b0700015aa1528031183c2c1c00b401c413031303008240720b02079100030202551011a440f203020186000b80c803650308454190740c0400007401580c10040001e030510214804149640d005003041c4a0800c1c0c040010740d01d034440842200c0e80d2072100614603003041c4251000c03480c010014001a00b841502030568100311341c982200030f485180c0e000000d030341c00b140e10848041107280210107400304c0e2040003503200c22001113082c030b0041b612005100d25183c1001404107803185c480c419010450020900764002040403010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 576617598 1250 576616348 576616357
    0xf17040501090e130312290f0105070c121401051f0909170c03040e0405060a05060a14041107020405090d030f1a0f010c0c030303090b060405160e0a0807080102 70
    0x50005044400100d07a503d24200514003032410002041e00300400e81d90180c5028400a089440c442c1d951000d541c0c8410092601c14042244d01461020000032101042181d00c689891241000414004078001510300c40140f4103a03000c81403007a480c00c1035481c01a0760300380001002c5040b0b500745024454400382d441d0803094103070000c0340c514496a403150f000904840c5001070282074a140c10040b4060108194000d18190401c2402d40e4903041d101c41401008100a48045545520407000c002d20034100d0702c60140c000c0002c0ba003052000345010503102142c042c07542c0d818440c5a444940100301c1840004540c0181d034042c00a01c01032829860254071075405102c0c0c0404617040541d81d5003014614810300702000c101c21900d0866507054006d0100d510408140325051140900a00001c28545892880214401d98011901c15030350315003909082c00107880c2a0113242004280072007202d101110001c034004518004040c44e4101c400115114400c0c1e0100d030075401742d81d101080445c3d0640040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 576618705 1107 576617598 576617609
    0x1a091303090b04080723030d080a0605041a01030f051b090409140304030c1217090d15020a110c0a0501080414060c0406080624070f1704 60
    0x2d500c0754810380004215510102040203000b48041c1c2a0341e1a41d121503e1202d400301480c0865a00c062005441040c4145600040c2e10885164841f0000302001082032041e480005400b0b41031800340c0a0303081c0080d09116030000101200c0c021140680306112640007903c1c0d400c03440552a412025840303600544681c09100441d0444100c04a11070515000d5641e03245135260040603042d40e03038080b40c0507802c06000c0c0b0000c207502d149400500c0c80c048500c03035603681c05000043d084041102d001010b0394014800100c0b44101d9601818040402e070b221074400ca250701d02d4180da00c00c0e07640307120303540000c403002d0511403548501c0da45904103101e86c0300c15111002504031641080c8044410207103401004c5030400c200c0343d001241130303000f46080c0c070401c2c906920000d414040c00f03003031500d0340c02c500400034464041040840641007010b4100000390500390f0368107181311040c4d0051084 = true := by decide +kernel

theorem cover : BRFrame.Cov 576438848 576618705 := by
  have h0 := BRFrame.cov_init 576438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 576438848 ≤ n) (h2 : n < 576618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
