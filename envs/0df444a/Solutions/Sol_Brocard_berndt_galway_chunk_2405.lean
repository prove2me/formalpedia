-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2405
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:37:11.655523+00:00
-- url     : https://prove2.me/submissions/138be4ee-16e7-4146-96ac-effe5f702481

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 432374100 ≤ n < 432553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 432375350 1250 432374100 432374113
    0x601050910030605040e06070507140a0206070506070306300203160608160c03140702010e030102130f140102070b030c130e04060e01110a03090606080d051c020a0e0d0f05 75
    0x441c041c00900c034500403d40918140b0016800d40030000071994040e010310750b2400e117440c01381c1c1c0340ea49400b9090340341d13030900e0b0181e11a418056030b2403001038548940101c000e0111030800c0701d0080c08580d41503202d40c5002c24414181188132000e8040ea00d540c00040615024451892002a041155101d00c0750040240c41300d01203141907000485501c186500d40103981014400c140c2583c22060003040100010315503d0402d4201c042000030782030851040c18000306944e40b16001038207a03040420701d640032008003201000342404d0a1410402000c172151601d4282500d000005e40713036411030180e0810078400001207224100d144084500c000ca10200c0c3d40060390300c0f401c0e40403400d002a0740c19252542010711801d0b4000701846030030b1510b018442e4451034a450880c0540140809403400c1e13440035603420303001480000c148102940d00a86503207041c0e41c1d06200a60404515085400e030900b81c1c0f042c010641c0c01504048035081c000720032100356600201c1441c10500a140003000200b0703600414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 432376600 1250 432375350 432375379
    0x161d06090a21020114030609240301050a0f060b0c07061815050405130e0c120106090f0902010f05032e03121101051b0313140d02100501090203041a06010509 69
    0xb80c2a440009200b641c42c00c00c14445a411032803540010b0364001d502000d86408102d84c0e4584a910004c1c4122607130a06401000120010f42101c20031101c50844135118082c20303a84e04094403400000d82407106005040900401b110390380c0e208180110410300c109150241030f5004000b92050052031041300103140c251101030000c0c11504288a52409140c003a5108140990b5a0040c03002212524006210034030304c51040028500c940c01d08800d0555880b6004149002180140c1c41d404000c4c0c2e501007800c000a10004000018030816017040160031b00c24022000003e0441c046122071220a40c101d905c40c00c03654111005c1503500c000c0c80344804030392640b5041d03007103e0305148808108008000d15520702c0103441003403070b404120700320010b01000092030b03d01c140c12520706030301c0c020b1030b84000800307030541d916107007141c126109005070344140c10000c200030303403070050601400c2c0307400d4190308500385681d5505d0030020b6000d144900a1030b08001a180c0d9114409450001d1380040080c3c0341640030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 432377850 1250 432376600 432376649
    0x70f031b0b0a180f11010e0a1409061306090501051c0302030a030203091603060906060503010b03031b0a0b010608090d1407200a06110c0d03050a08150315161d06090a 73
    0x1035045c040d001c5070900070102014034000c500c1c01c045030164544440511400010045030b85c40042800d0f500c1084a004540700940e5407203658094807580c40c1c00681075040004000c111a00103241446100c20014036400080e808001d603481d482c81820050b85035242c120540381801442c08001e0100f0816a800005024454100204203400341400700046602c0d2000e0500b44d6214140050f0035074010401d0070720340c1f50700010203804448403100740d4603e1003456907a241d101000380d100000082c285c41c14448503541c140100502603225040800b65041500d0240f40f06000303445025080902c04021100814a0b000d00c050080f40c000385842c1829480f00005411000e91451580380e5100d401d0f00d100030f9040c40110150025050b07215035040c8404080d0840303040c0402001c8803c01c13166481000740c1502c1c20030001c070320107124000410305860400d0301c007442c003221984460704222003a107510034011400d450307200c000d401c01d0350b0b030300d03030b1403000c03801040c03841c0c81c180c1c00111450016203403580c80050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 432379100 1250 432377850 432377873
    0x50d0309060e0307150507060e01090c0602060703053c0a06080d05090d06020313080313060e0c01090608070e0a170c0102071d180102070f031b0b0a180f 67
    0x4650b107a085004001c501419661410b5000e00c00f54018259001031003030b4050405400c81c01c2c4111004140581d24211071402c6d6a44680c0441e00c1d820051014030103590140309031a0301184600d002c200c3ca00d0500500308100310114000c9107820310040d001c5060300e1031411502101c90744c01c820206103090035280e4400410040c4520350301030103940003902d90a88100300b00c80c1e000c1002014040359100c40e440e0400258005001010800381e02100500040e4569015601c07032010310089000160560800e5001e80307103210b03600c290071b4119610704021680c12104c0030043d94124944520340d5541c0031001d40e800340803e0030381d540c030210040740040e41c0c84003200c08140c21510a400d0319101c1c0341420069a49280781d004a0076100f5242034105007400c4003440850340000c40d604084441010036445c80e08a80c0040340641d41c3c1000c544c8000c05158021200000c050300380a42410b2407502034035000a551000f90040d0483ca803288000a1540ea04907480d80d0420b82000c0f8031210001c840c5482030444e00b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 432380350 1250 432379100 432379109
    0x3030b041d060108210903010e060a150b0a052a0f0a17121807030b0106050318071d0405010b0604081c0207060c021210060b071e0203070608040309050d0309 69
    0x300d00b000100c2c0e1590049104443c1042000d0110380031809010300301d41903000103007013640541d600d06034181c01c000208500c0d03000d22601080012294500702c611151803216800525020f281000711a60b00c0b544442125060410683c0200d00036000310070f0b280d0702c580c2c1c801c3e0000c0c00c0c0c45a501502070400c1c0200d84880114400d0405007048044509901c00c64064190b404030f4002984001074003503000b42107505410401e00e03064440300750300c90746c0f004040c1c4000c0e04400c0002d4408010020020307120110071250001d160000c0088502e05144440008411840c44250080c0d84d40843d042203400d410071401040028121511741c0c0d11a5100c2e9903c1e01c1a90080180360020b44642094500100b040c0051f6820b50f5a0b82d241012142c0a11600700000c1da040140d61103107400d1b010140e605031265401412a2602d801d40e0b915560420140001c22042103c010b0000c0b0101d490060b0380008009080b20450700b454803065940d41025140300d405640b10907001005140780c4400c02d54000c501c3d40944 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 432381600 1250 432380350 432380353
    0x1d0112020f1009140907090e090f0d0302030103060b01080c1e0d050a0b0315040201020c012a08040612060b0304140307050604060204030c12030c0b0a0e0109050705040507050304050d0c03030b041d 86
    0x6994644c10090906426968540801c1802030306002002c0c014a40c643c0c846031941c101c4440300c1c5400c2c0c030140b614407060705c08800280c0c0070005108009003400f40c000800e07024a80401581008203078a695840382145225507140c0c40d402e00311115905205032480c410682d42c0c100030f40e00c2d00c2e41710140601200c0d51803900c0b074080d80a00100e407489480d40c0724000e0340c044c1e00074003040f0b072030384015629003c6100010031401c1288400c0c0c0000c24402401d4200144200c05c200d44580c904040908000d0100c0c00e0074040b2414144288040c91401c003d43e58001d030031019812884c0c013201c0010381580300d440e0b4040c2a0707004240820007031080503002081124401d003c201d00c8276650301b640c803c0140000c880180018070b8003600f040030a2118036440e800c50b580c0040050b8540840c40c0c1c5c142140c0c007062040301d954011050420030752404d84101c0790f0010243c204545146050359440b500c0e00b81e080b10311b50500140c03a4024007858866032016220300c0c0046c01c104002d081003c1c443d88800342c00440b603107a6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 432382850 1250 432381600 432381629
    0x9030a09150503040f030527090a0209030a150b0d110f060f16060e0d030f0501090504020a230603040b040c1e060c02061303031101061d0112020f1009 66
    0x401c1403800510071050780c00d56495055032141e5558001141c9900c20960030400c2c10f02101a0940c0b440110513000c042444c210711030264000c0611807803c00007030030140818418485070019440c041143d00e01c00f64046103e0000d951280c4402c00208550b03104640c21840c1e0004803410003d405002e0300d49841d0848400d80e0025400e420046a407060b12540c2808105c1400b4801541005151100c030040c807601000c100520850031032031601403c251000000703a05c0728072002c071041e5244546409400540ea0610481c6060f401161180d55288a9500b640341d158000048649613031f5455510040c00420742a90f80c14181400910180e060380e0540b082c55601c08005085021600ba240242403415030800b443c40c54888240c4d03c403081c1c0481030b0780000003080844510940030280314082d42c880e44a03101c8030b1301c0400e0b009017102c2098104030f071150124031400324544200762426044072215482a201210144003107001c20000c4821203070080807420140b0805600000ba41e8113440c0341c200c4c0d0046 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 432384100 1250 432382850 432382859
    0x6090f0e10030311011d01022802070608071202030c07060c0e010909021303020301020f0417061b0c100911100e130203060d050601030b15040c020d0e030708030309030a09 75
    0x400c209841c00a00700342140020800240503484640c1030881240c0005201d10058404c1c2d0101c030103001400d40e20740d50004040803c904404144074001034044030418444040a001035501c80c500c0c0070300018040184002a0718034419070a00000048203403096440e13041c1049481c034940c000c60303011110181800c10703007003541d84104884200c541c1d05a440c55001c6243c06081e100a5019404200903100281408800350324240001d1036101301140c0c000c0d0380c681c0b41580480c505c421810b030304003040c0c0122040c80510103002c1f03903921032200584a52540c51000070002d40ca004006000e50000c58140f000000c180b0501034141c0c54542c8050360000040184890221814011000078039800841da2681c07030401480d66000e140e202202034044041d490305911000d181c420240c0c801ca41c641408010040d04441004580c9582c200c2628203100344d003071303846000c0d40360070603902e201080081c13004242500b9541044044010901c5d002625941d0a00c80078aa0b02e9500140112001c103480400014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 432385350 1250 432384100 432384119
    0x70f080303042f010509240909330a180507020c0102121b07051905031009150506030304050d030206010e060d080f030604060f09020c0d020f0c22050106090f 69
    0x4040c42100c2440c42d100c3e4102c0040d44c842e007140b602c81c0d402200340060031082d02d210301203030810080d101c105c0c0c0742c90314101d030b0402400c0e6600a0100d864480302c0001c2202e80b003a16550001c4c0e00b84c000c180900c14101c2000865941c180303036805422100754480b800c59201c45503501107400787c0c98550079100240c004800590b030700c40004101040200041003209440c40020304118006030b400303001e682003070341c2d6000056801550724250a032280d04405040145103010800c041c140c43d400e2605018011042d142c94001048010f1000ca10548807030001c1c0b5555420700c21280a0000203102d5404c00410381402540c40320b09006188003408900b01040851802c0710170102c41c00da00c203290500d0034403d0381035018990805041c554026446107408101a0302003200f4101624082c040141c0f90442540c1951901041c07020650554000d14a0649001e80100300c0e4109404141e0340016140000ea000b100030400103d03c56507407500e840004101c5030307802000c0d5021103c03501c254200064a0b6001c80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 432386600 1250 432385350 432385403
    0x7020706020309130e03040f09050901090317040f020909100b03070506042303030a030b030c09090607230406021c02160501080705071212110708040611070f08030304 73
    0x30000342c0d00500110f07689182201d503104820316041d9000c20855500c0384c40600d07603005504141c0a074180402d0034801110f40d48103169110580070000d002811103a24050801041d90514002e0108a940080d06100081d202014001d43c058005401c03840c01b45241600c2c1d200309522240f2690419040101614002070300c80c090321b0000b4002c0d8645032510307402546100c1710000e03020440031203609480850750184058490480c0a46000c189107005400309402c4c00310101045100310007a03c188070300e02400184840e8440700500b032180c0030b900d0b941e44100280803410304080342040000740c0840ca81368003060000e501452541d00507150b11040384280d81300d032141c0c40e04540d5144c408d94104003640c4583c081c1238000c59203040c0140f8100543d122030340c54080629404000c0b4160b1031441424941c40d03c188050742c0d030229030640c1000d411307603075150b885e200b241f255800300301c0c1403050050000d9040c403100d4003c0400c9814074031a290340d0050142c0700e41085406503108040400391800595590b8000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 432387850 1250 432386600 432386609
    0xe06180d09031505040515070c0b280e0c060705070f08030a0f0c0c120b1005030106061b0305042313091112072612090102030d020304020411071a070207 67
    0x1000451403480f4000e00340204103440030712402c10100d9007140d0404016000d03417119555901c046c030303450800c001c90034805040e42440700281514490040086d03035a004d11603102c400085113901c002c10096141a64891420794015000500c0c0004c1100010b0715204032401080803d2850f65908062034490098800000101343c4a4410520403842480d280d643d00d44540004001644c6520301802010b04003481120040c05040601824084d015400d10082000720003e0001030300700b0f28018190b002e4002c0340b48023485900130035030416000b40260b8015120b4403081060380100650f0300e1904003501c2c0035203400b5070002c2c11013806110a070f0203540d00e2030750881d41904440e01c45200f44803640c2440e00620000e07018030907021407085041c3c00c1400f41420240709601a050031b62086a0406001c0741c086d01ca60142000400141e0b41c01009588050b0761251006889641c2c4d80085005400200010303614100002428000c0002c4034161040103d070038560066155243d69050740c1c0c0d29841d004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 432389100 1250 432387850 432387863
    0xc010b0901120b0402010210020a0507021807023c07090501051e130b03010f090b09030406020c010809150a05040b161b02040207020a0b0301080d0926010e06180d0903 73
    0x9030b180814507100040e5003203407061040f1a1140900c182c004100d07000f5420110004100181038400c2d481c0030149041c01c04013150801c5020f0030300d141c02035a2801f0356004005a925004400200e0f04140c480721501e0040100040603102610a040ca44504260186000c124502000031a1905081e0094040c2c9104d05031904955000407040000c03000752000d468104035204e41c44115142c030203000f4081006a40d00c40490441c9182c035140f50441401004400260301c03e010400c140d503400074801d8091070080c2486600f81d1945609542071101c1a0102c401065408081c000b954903d41d01c014480da002e45440d24254aa96039a0104d005044001c0c0c00041d8142040602c00151403120214a41c401880146007054590120312644040d07841400440404401003240c14070501c0304000140c840e2401413002803d0074a81000c410f0002c090f200324048024a007007000009502503c0400011001c50348035103080d6588100c40400d4159840322070040c0102480350754083c225680a490344105d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 432390350 1250 432389100 432389129
    0x112170403080a050c0109020a2405120703092102030a0912020a091a03011a030610080d0e01141317010b0d150624080f0f04060903140a050c010b0901 66
    0x5004480c00e4002100c500c034155610b00707c241c0183d540c2d400c444000e000007012000a24030080c00342c031155402c00b0010341440810803072400c20415405091b907122115080000e50f8480c00e0804040e00111102e085c24800030340510303040b4454000010380b0b20640b00b6030318040440d4507a03c3e80d40720a000c0000003508841450014400b002540c4c1001c804041400503616224034103400103801d42d090010381d001d02048a00e03603076580381400c2c037250350301054046290b601c061408044a54400300509402c00300203a601586129070b1280c1141c2d05c0602070b04105a44429202148451080580c8250201d8100c2c0702514900d001040c0901c41c8245001028640401d00541710503140428a84140310140d56402000c515080485900a04005200e8075100003840c4440003410030f10024000c44001340500040004003000da164560340150310410200740d51440d45016903c0540008c007203000050041030801c01071798002c0280c8800c0f000c00d0024012071513001d050140e512028050080445044d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 432391600 1250 432390350 432390367
    0x6140d1101021009030504050a1e120314030f0f0f190e0c0405010b120f0105100c021311070c0b0f160305070203150405010c02010606050307111203011217040308 71
    0x180500c000010060058603034008145018004030703000d25030120042880480c00f442142006e01302c003c003070048049404d1307001a00b00c40100300d484042c882c0000b40810320118600305445886c9050011685c03200c00341e221b0400c2a4081000c84045a18a410348403410004269071041a0014055940394250784428607008500c1d0014089001c1e0040c09403190180d2045607840304e200d4580204210200f00752074404102c008414440007038811081c01000000508c5203a0780e0303004500c0b8002c0c5900700b6030303d8184148049158012a80b46100715245800000c48500300c071800244546407181401d8240c5036240c0b448440c03030740101181110125424405160040040002e940c1024001e061940c00d0002d1a40043e00d032904065800103816006024003040180c24064400140d455000070b00810317040c407900808600005011408100110702c16200c0d0003814040740e245070b010f58505c42d03920745e11078001016012007200c0488039403800850144a08007124203032400c0e40e9214000d1031400e03000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 432392850 1250 432391600 432391613
    0x13081c0e0d020a08060109060509090102090a0e060f031b041415010e150406120b100e060f07051002031512070b07030905120106051c020d0605130803100906140d 71
    0x545100701d0b0890f40000c0c0125505070100309041c000c084081021554038103080c10701c080550003608000301c0341c6c014059215943d403002c1d1008191400344c04034110302e40e00c100004000d0140210f00340d8041c000c24481032111940c030440001081d00965090000c200e6921000e440a201241c25600000c80013100c065290b100e4100700881c0003000b8000603225031240840203041d8401c2c2c1c41070020680540020385602194001c2910280c0d04551452400c03805034406040c2d0800700c1c2599102e50030018089044c45940c00139101115008011181da40ca01018548029071041d128044001d20302d003500354081c035201c2c80740f0280c08045000b80c1502494107400400740c2c0c2080008406002110714045161380341d02002c1500c00c043c0c5000403a03490724000602102e00c10086666001401e1485080d0244e10303807586910240f43d000d440018260341d420864805611041c0d801080080e00009101c1c02d044200842400d40c0c0e0407803410850103075500021200507965820035504552500b980c0b4000c2860f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 432394100 1250 432392850 432392869
    0x1006061701090e010e0d0e0312040e07180b0f041a090102030a030f0f0e0a1506140d060b061215030106050d03030914120403030e0f1f020106030813081c0e 68
    0x183d00010a00c20760f8419614240201400380100007002c0c506003044030f01c0d0030007861151050002100b13280c9814944002e8069070002c0204050141c138203807941e4000c000941c20310082c04802105900d0b42d207040d031020310302d500c14841d44403209000701c1c1a01455805000329900b10405030002c52401034000c40030350103025090214420300b6621081d401c0020314502400741100c000c040a03000801a41c41c0c40d0400c034105241c031560702454100d080c040087c3c62014a88805811140c0408503041454800003a00310108000d40002002c60418003420680d150b290040c410080080701d80941e0030241402c880c003a1240541c410503007480c40010034040c0d40902e10031800b80140c01d03e05c1c1041c02c03405d40b401c1c2803081d0f1003801580010b000c00506501103590515031078212070b140c040901e8a40000e1a030320039040e002c1040414420500d400381e001758010070003541d10580c50340d00c030a003404180c000101c071f03440b51050b6801280007504004003181c0c07003600200c2454603051845d000e00300a0000004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 432395350 1250 432394100 432394121
    0x6090d0b0a0f06030f02280b090607060f060810090201080402120f1b18040c05060f0c0601030c0501030501120317060310020c03030709051206191d100606170109 71
    0x80ea922412070107103a00d40034140207140210b0005c1d50b039001a20500103072003040c2952000c0d50b42c503803400900c0b8802840c05101142d4214080f2a201e029600004403a480b0b050030050401d85003110b8206014441d400110484105001f40c510055200c909103094412300c0350000d00040e0b900001400515001d42c904250480203000c50301003454600029160240024510805409284940d00705243c483d80c0311400d050700c005031883c4c42c109552203d200703464030b0203030700c0c814140842d00c0182c6000740d100b543c80d200c0e503c104076030035941d4030b041212005629000300e500003402d06002090f0280011181e100d200e5241d07407003091a00074040c800c542d456019010951601884900c07880c4110302d800030b000540482000340d139503818500800b42c01400e96078403d034041c010034420518070400104900364401030b000700e100b04400700c0031408030050031988506040340c10981a140034051300081c0000b590884020b041298607201c480640e20604c40d43c81038060070455400500500e800e40d0000311180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 432396600 1250 432395350 432395371
    0x6010f1e140307090302041a0f120c1f03140601050a0c020a090c0e0f0a06020d0509040b09070c0c05040b06040302330a0206010911030402040c091e08060606090d0b 72
    0x10309000c070803144594420b8403180c0000d40181d00038010340c0f40900c00c8540d2800240b170300105e80c20360b80340070074407003034811000034411840b800b02c86846d0101441140d142d05001031070206c400c8868000c002150a9603102d0b040041d1400361401d00c541c2c1d1050045020b104140c40e100e0600035145422030b801001c41c042260051124040000c880c078060080403290022625031200f41c00100c010305ca0801d0007405014890220080100100e64010864020400051621542d50a45440803402500c040081d0540181c03109042140941c0d1040441c2902441201c400f03490366510400c22050700c4692500d0759000e00c04220400041c9080303000400d0116080c60000c00300c0706001004210a80f2213600341383c0054000a0b0118025811310550b809400ca455040203840c14181c5508817500008000030301450359100d100b0b070841c1c0205213030030041c0f0b1a240e031500d09000c01c5101502800451050020610501001c20305502e0000f040d5a803e59010305040c61243c5191540309204034045c0c02502c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 432397850 1250 432396600 432396617
    0x150c03040f1202100b1504120602250b0901050c0307030c1b1109100f140103020c010c02010c032003071b150203042a050f040f2306010f1e 61
    0x24042d0381d003015a07001a030041c00d04461120160410b4a5410303800d10b2003180b20401d00342601405c40d058906440034440301d004a45603924002009110312841c0c1554100400710a4100b10b0b4525854281c461081c603861085845410100e403e80e041a903110914080600014920500c41d6000e0300c603402c06864261825a50a0114102d4441141080e603091a00790b00c1644a41440c507205500142000484103406207403440100c190340d030034003418904840450140030f6a81c420f80641d007000025030000c1240101380032002e030081590b49015070100c2d041410055501710010482d00015801110080c515a503a002c01c8902c14426030a11010390318a07103a400224000e048031030005071002d940160350b07084c50b0502d003100000c0c1c10141410b40c0da00b0040a0002111450110221601524251032504a000018001d04003908012181c0d528050005010303d544000018034180145094089525140c00440380002d003404c000011507480301078a0b24800c0507910b826000003c1c0e01c1c100c0381e07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 432399100 1250 432397850 432397853
    0xa0e09040323090d0b040b1006050d1e020a0305060907020d050f0901090b0c0105010807122a05040212060a05010e0102031204080403020901080f0106081908070204090605010e090f150c03040f 84
    0x1010541e2510599421760300d5410401000700f0a0402e6411280340407680044a02d409002070042c85400c820440d284c1d00c845084c50909502e1452400300c48486c0e106545078a113210004004101c1210101d10949100000c544000d001207021055131070581d0780c0c2ca14041d18031842403144c0e0311184045040202d80c0600044035034105001d4160701e0f11100012806516001c0301c0e602d4031843c0c4d04160103d81d5484007210000d80703030320144400703040c150174042400f98a1001c00d40e00a0080e07403103690044e0000908c10300001d895504e162142e441100c0322104030391110700440d000b20719449000d001d0fa10421264a40c09100044240c0c02480b41c07128501d4035440c1e0780419002a821b920a21a9601900c07881c00040e00c28000c0001520101000b410f007070b40449001004400c0b62070340a1301551001402206549a80c0c01030720b803480d04880240320f0307943d65103005403103580111070340d14660041055131005003d001c24075055a03145001c0c05031a5454400740480103a01c050310496044107085008030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 432400350 1250 432399100 432399109
    0x50a060504050a060b01020606011b11120a020a09110702090910090b09011410090e031306020c090f0112060e1c0305070207080601180b0303041a0a0e0904032309 71
    0x348150301c5140a410142511302d03040d015265140e42c0c590554001e14100501d6076032010408603010580d0310644a0710500d403c20314042c480c01c41070036030080ca40101d00c07044100300050481d0002c0c030a42e000c2c80c0c440d40d5015914120b80041d07508d00b08400041040d01c000d0b00d0142c1d509500a40f2800c2541c262401342180d16049a091300f50031144e02c01400204a200d034000e20826000d503108d04400708051030192100e0000110307500501d01401da41e0200e2060805080050703031051100030030714465641d11000003942c0c0e5080380700c045110b04240c1000031000b562002c0c200d4121114520000c44000040c0d0303c2602401000c0c4079000744c0d00c9120501c2000b40c61419076803848a0786903c0008030b0742000e060090070402d650300b00401c40d034402c10040040100e0151a40c0b000d00c403040c000600e000f02200001d080d071095030300206c0011f40d422860b07803041c03601c40010850282d0355200c0ca004214640240500c030907040300d01030301050005201d2018400404090303045101446215460003203a0400074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 432401600 1250 432400350 432400361
    0xf021e1921030f06060203090d060515030709020c0d021204090513061508011802010c02090907030c0f050108220201120b0a2907020307140102100212061008090a0f050a06 75
    0x10303000070b44840f03201c0050801ca10071100604118805140b8100200020515403030f034182004000c40d41d031300c0015100c4028446c02c41c51a81000b810b80b400b0b107943e10340b503402940004240800d031703000e00e424030403005000080b00300040410b00c81490800c0e19081c8043c00503c001007841822402c040e0044c1c0c0090700303910032504a030491100900c1c40904205010342144c0c0c100564014842c007401000f00542c3e00402c481c1c00482c2d04444030402036031995400ca040c00c0881e400244010040400031991803140c401141c1030b10380a0740e0341c2c2c50554403070303100342000e11454100c0942c200c10310b4440700155205001c0e0f03540f240c41c05d40d40403460542e20000305041034130b10b51000c48039400314501e50101007031240812440708905003115051418503000a521880c4900c0341c0290005010004201640280032007015044074440444d12072601040ca061225402c540d000d01c00c00202c2d5252014500603403155010b840010020500700c8001c0c0c2d9606948801110203603682d12440000d00d00007111130150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 432402850 1250 432401600 432401663
    0x1060f0b1c0c0c03090e07140304150c02060a0e070506030406020c070b040f03020102061b03010521010c080402030f01061a070203030403140102070b0a0207020303071e0b04030f021e19 81
    0x80c03c00907019401c00910508190700030300e84068080c02800f4480d0703440b0080400200f60f10300c070182d50791910301d0040c1507010720400142a01d0b0034a0340c0440c0300c940200700248900030078081400b00d442d007441c40caa200c4005000d0700d90f004205101090102c4c01560242c4210244002240d201a45480456665401c964440c03064408561014400c40d41d041c84400d80104100843d15080c038440002e044d00c07400b0500485001d80201100319001c640c03a0101020183e0114008201c4400300c000c004040c2c10040b0f40c01c2e4040d00c5001315604014105208900c11110240c0e9101000c000001c2d50308050380c403e0034142d80c180f0040c48044082005400260b02c103150039800142d803480d041c54074070f010b290008d2450b12180e105008030009600d001c0100c8007081e034450020040d10310514154012101d86400c0500201e80c000100810541c12001011401130386400311000c40c40058941e0b00104241000010140c106812001031211014510300b01c05100c2c0310170814455041c0c00100806c00d11501c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 432404100 1250 432402850 432402857
    0x280e03120301140906030304150c06110406030605010503071e0908060f010806010611030f0901050d0c031e0603031d03150c09040c09050913080c01020d0905070801060f0b1c0c 77
    0x400052000c114190107500f011359101880e4a403410010352240120710403602102e4800780c0075044148601a200445507008800b00700038016408080c1160b0031500511000c03910b0404042038940c001c8041d24418902d41d51012a41074000094106c0060b5840491082c4034000b41d02080c124024007006214425815011a40d07600d40030b4028500f20040c0d0148040c0310800e000400035000c040111500c81d2004400310b41d80c0d6040900484062241240702d02c42e807481c01c651042d0860b4980c0048030550480ca0480074ac5510551007241140e01d28800100800c501e01c1007480603046059045240000080503590031211490058115641c1140c640390710480000380105203107803a1107941d600341082c1c03621030001420302d408100b50910240880300707068030003a04403007000444c404440c10343c1c1d1880000e644403101000b05002074071400d801203d8034000d14801090001d0144191401c03200b84642101042d880c140b9440455800100d01c0190802c2c01d00c40022038268034026608031520301e42c2d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 432405350 1250 432404100 432404107
    0x1e03050c0a0602120c04031208100906080d02011a030a0b0c1201030b1008060403090e0907051c020406120f03080702010f140601031a491205280e0312 66
    0x1850b48081000200300b800b4481701888180045855400e55141640c00c900b840005600c812000c00e23040811540509507840c200480459444808034100030f500050707400030b02c444200d454406082004000340700790036500004080000c211140d019940000c03840e0310301403401d10750201c040c0c0503010236041a80c4250221003403042c18120b00c0d41800c0105041c0d13020300751500705076078000c2640c0c50b180f1544c4074188400b80171840d0300c902407181d040100030003008140740b40044402241103042c084070681c481c034903047e400202d84000d50044465168004807001180e20349a5054a59900140450046650305d154030886120244910a0010a540c4440c1440e00e480c1c4001805c2d5070039401a41b42c40d1507008900c0e103560319015504820030012812980700340314030851501c01c0c0030024203c1c0b10442c148043c01c04040e5000384088090f9401603130904255002c0020a5903039110381540c60030444000c035100154291943c154011240c080d2403c582803080c0e0700d000034904000710b46200503940000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 432406600 1250 432405350 432405367
    0x2803050c0310050c0910021e0d030e010e072c040b0411060a080721060f0602160b090f13020a0e010f09030f02090414030309010b0a050d1e03050c0a0602 67
    0x200b000090122200c40c040c80300749000c80709424240690210f0901640d668400c01e2495402404055140b607000413400c03000c00d41010300300d6a140310840b00d141c0460320380800f0310f2186106000c0e10b22003440c4a0010645c081c40d1160042d6540700000c6e4546603e1900000e4001e0240919482801240201100050750030305080605084c1c080d40701c4c907885041c1c200545002103400508495101401d410007850002c01150112a85e88120003501c010b24605440841c401d5400d0905c0410fa80a650813500c1d4007490750750751600c140321405400360070f250501c02c0b0942854424092150311070003412201111402502181c00c3c1d030449200f5002103221900348140950344400102c0c618041c3c1c1c0b5100690314507640390381d00c049e101814040e001304036590000e4240444c030781e02210303084801d004490740c924091030054001c000c200007042c8214408900003c9901d841da05656480e2340091200454512201800364100c8942408601b844828088140c4580c2c1c10300c005080b041c001c400c0542d464a00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 432407850 1250 432406600 432406603
    0xc0e060403083001182706020c0a05060103050c040e1209131a01080a0b100c1a04030f080108120a030e16061d03061501050c0f03030408070b06100e2803050c03 70
    0x1420b00c0d03040400e241640f042ca0800e100700c50100e1044407281d40c1000d0800c41c2c00c20502a1044c0427131944030307200c3c03800e0050802000183d0b240c100d03801101030310545601f100420007681c1403040005a90ba0000d0200d490031703401800284003900c001411000c0c0490088189030a0342e030b0b80c0564104803d050801c059082d6088a0202c7e8026080310042002c5031282001a607502c183c4c100382e200300300b0b80048080030004422903441d07140700d42c034400100300d00c5c2c41d00d0010840343c4106094800201f44400014104200043c0207810304900e0150505280b1102c00803030040c40041541000743c452414586400017201001002800d21a520b22001494040d40d5460303452106c0035042c040d030312502c10010049054142546400c9003443d0142e62040551500d0b441c2400c40b00051030640000028801000010b41c000e05040348107808190850b6240310820002d0b4841c0e0502c03002103601e4042801461400342d407600c106c2c05902d00720b51104803144e8018201c8140641007101c1a910440314480d15160 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 432409100 1250 432407850 432407879
    0x30b10090302060a03090201050702060c011e0510030b090a0c060e031203010f09020f1201150e01030b090a052212090f30051f0c0e060403083001 64
    0x2080c1440002285954086551441610680020155203040c4102168071600c12248031540003000541c6882086c10101d00170885e01c110081e1440707013007100364640040d80c0980d078460303041084440420b5181d030729076116251008010000d40c0c010040020002000055040040c040aa5600081a041e4000e051401c0c0c1031000e552030403d01800104036000b0a0300404050f2422030402584400c0750000501c8180640808001d5041301c40c8004190020a003842d121086216560001c2000180c001501101c5480303035101d8000740b5410000b01d21401c1ca4122641100b491283e401003d10348229a10790800e401504451400445400303164141e44090039001170042e14070708442c03562134a080310840b10010201141d560b41c00028800440c00d00c0c00303a46032150b41010076650100e0880d81084103516101714003109051a02d0b00160750a840707801d03c003d0511010301342501c0c050540d140c05006030885159843c1d90b900c0a40303849021240f10200d40200c004104100c0815410018100018107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 432410350 1250 432409100 432409129
    0x510030c080a0b01090218090c07020112060302010806010e1c050a020310050f01060c1b17060901020a0c06050a0908040806010608060301020a05220f15120b0607120519030b 76
    0x30710403900c00d80481c020fa0710340c5044441c1c290380140c2e20f1180032402105201982200c5911081e03181c2080154020000104405407007680c0da09040b42e24a0740d0380c41201c200b404040d00103005200060a55401100b85080c006001068041180101c00044040d5440c0c2c0c0b10489154010007038220460030200030a0389101100b00090060386020001d0741c5044c6414481c0300c04002d0130144800070f000007560030880740806900115416912818011002c440d99500c00b101071089800060201e40107100351401c1a842c1c0e540d44050949545400c5c000e403002400c0440026078616030302000803040d400400060800c50040e01ea10b61401101800c078640c01440240a40d00410080c621144d004044a101280031640c4480c0040f03940c1c103090001c03540d500b10540080c091080800c44840c543c41014070300900342d0f03d0001c0c080180024001b41c0b2071842d016900103c0600452000640c1051041d014858900d03107941842c1604400d8107135216014020004240d41e55204401820b04901c412001c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 432411600 1250 432410350 432410353
    0x9040f020c2d06160302040b0f0c0f16121403120708070305010302030d031a0310020903010e03090a09020c190c051c120e040e100c03060e090c220510030c08 69
    0xc1a00c00b205501c50200500c0440b000e6480d0b02c0d4601414045d9040c4c0d00500b0a0703561035503c1e00038954090002e68080c5620002a200d4401004010400050740607141c5407080e0000101910f1b000320095540044641204d03100b8480c60415241d86040018089403140d41c40f40171154205140041c101000150040e0101820540148056100040c0090780c10100d8940001c42a52008000343c944120a880541c98003603181c5228603200d007600640170a403001c800801c200004400315940d01e104400c1c40b142c0003030303403508100401e900c540d000c0c2a000c02c405080c0c0e460304100c10803000f202c00c031550302142d0508a0351130902082c2022841003102d400f007500000f000c0140742c2c0321300b4803801a42649104014070b0b440001000d03203c0b50800c1900650f110104c1e0f0b40c0071f04518120010700341c128800000640340c00030009620495102c40780c040c2c1c5806000d081034040c144140540c8221054007101e00e0390241c45031000741100f61043e24406e0f840200541e040321b0a41c503106d2440c0646a1005949 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 432412850 1250 432411600 432411673
    0x1110607021f0b030a050c091f0b0a031113090c0c030c0b041106070308040b06011b120507231219030525050408060a09080304060209040f020c 63
    0x2607600040c1112100c0740104460030700704a02d0701c00388041c010030b004441d00b500414442104115000038450407880c400c50b200307032035940c60132520380c000207035107030100701d14400f1181c104591103480004118620540c600032500a200301c4011080358001103143c9a031218011040244810501c200655940b592401c0040c1041a42700249036503032044d00500810131040124003000140d840300011240c0c040d280580300c0e0700c1c9007800f8155002c2207070306075144058076000072907943c4201c088402402e02c401119850f0f5503103071203000340341640c01840014405e0810079440400e0303882c030300350200d803280920f080f0a50180080e058100200c81402e039070214001e0146003552904100d903c0c1c0003c0c003030b00e0300086658544010314040040081410030a02100d102c10000543c004010420780d40600103c0e080e613183c0c400c00b4130880700b8911001c0c20300c00b8140080750000302c030340c0c00801030b8150060000c15152080c075845422640940c0081c09140c1c01328070b41e02801100340c05d00d40c1c100b00100300d07c0d041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 432414100 1250 432412850 432412861
    0xc05071506060f26070c110d021c0602130b0c011b080604110702120304030212030a170c071a060414150405041b0f03020f040912030e01140a0902011106 67
    0x118001002d40581881450124000e518401c0c890251034511020800442414003a50141482e010006c050b28030781c20f4000c05080c2410141d007107080d0142d000e844410800e090034101f20401800d0281101c071683c0820100481c40d40f5034030040080c00320840c5da03607541d0301c205020508441c0480280b407480100c0c071100d2000250048100d607030002041d1404291703003007005844a16403007842d5001354031582c08603000d00303a00c0000001e04142c0b03200f43c5441c1d1645004810540d6603001c1d00b100d0400003004048a00c400101ca2940d99401400040c040d03414003d1079a0360010700303468050110b0a0034601000c100c2c0c0c0349000d0140801140340c0c080e16150a0078407000d0314100352640c6150354000c1c0d0f12480441c0401c805080e80b6582019118000307640c5c951607000c1805a4450307440b06a1013907183d60014031845c64240302da13017405580100b8160005070404002d81c09010035001d0b12409542c4d0ba103c81a079034582100c854031071010924000b40d0810b035403001501c0d40300c0500038040d2642c020300030007d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 432415350 1250 432414100 432414107
    0x60c0216090e0a02130603021306090612150207030c0b0f090610060e0f0f060f04090b0f030606010f0509120c15090d080d11160506071d01080a0207060c0507150606 72
    0x20030340c580585030b0205c20ba900d0300302040600740c903903c0250032510101020b9020706059200700185c0c0c000c00424003040d0f0342d44825488002e40340401800070441c000e20750403100903d50013414114400c0c200700a86446d20b4540700c1d10740c60115090000c0ca0300810800c200880107002e034a9004e1220b500d0744040f14104800100f0200c1d503a07428602030b1000808041c4240d84050060a003200010020741d5600d58280d81c440c0c00b03401c1392180202c240c0c2031039000c000d80d2600c0d00343c020b0109000ba00400340c964071040111401c84d1000c040d24280101000036484c00e481e25070b08103041e102c250008043da514000184a04140b14038201d4030a100d0502180301c3e5641d808008140c43c9070000030340d40d00d030002010900010100c0c0c0d540c0c8204803000203510420480d00c0b8a0048440e030065058458958940c030054806400070000c034004060800901e0445600842140ba00010a14001403d000c0b055451310100c40001c03411401140021885108215100c080016010300c024018420207142c00c4000c3d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 432416600 1250 432415350 432415363
    0x12021b120a030809070902071a090d0c02100e0405181203130b0705090402040303120f0b060301050607140f06040c0f0e0604020a0314010f060908070b0d05090307060c0216090e 77
    0x201009072001c0131509140341004410003030107440608650340c0c18185000707201c210064500c80000440c18001031003400012a4448800d509a03c5e603c0c013a00e010741c02c01020300c210300d110405100244042006a03180e41c40340d079104079940003001a001410800881c600125151c0c05086101d00b08100f010407190031036061222903100c150050f0780e80b68111309644501400142d59013051003c5000030030b2540c4001d01c81000e12640b40200401ca0b0895000015990291321103a0024002c100400060420b8001001e41340c2c0100b5111801c03100d040e070b0960501e480d0140007041581300c0c0c0184000d004601680d80010003030401c080b82940d141c24000e209044000706818421940418140c07152800394001610030703110740450115560b114081100d107800c250080a00140b103001003c11010030005d13131101656200d00116007481401c46041e0090403009002c104140414800007001401c580520000040550081c002c99900d5080c0b65518480e6644840020350410601c91040d40b000702d1003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 432417850 1250 432416600 432416603
    0x90206090904020312070804031203050601020a02270109050f010b070b01030b041a040c0f0b120105090703110f0309240f040813090504120f0206012112021b120a 71
    0x401d5070381d16400041e00700402400c0300700c41c42c500014520300708000c5400400c180d80c821141414085103c041c1101228030480e001805030707000007607547c00361404d2265852803d100a0302481a01440780403146840000c0e4040e42d4465221400c0c4000c280d0200d40d05405441d0b08549242019519261103c41500622002d841f040c2c1540100d030a0014415186a10000200a01c0141d04151500b106400d80910501005400809010804100b004115000f1088001414035103900700010003d5103640641140d0505a80f808800e02000c00c05c400f802040a061100c2074680c980030801900744900d03140c2d4440d0307071043c0c4c005c4180242c4203080901d41090700c400291844d13a4a61034140394074030640c04c1d00c41c5c0031a840780300014a02c00c4c940001e40701303620440301980c02804a090540f075050f0140f04403005a00100010f03c211068040b0080d0780c3d5900400e03040c135034010b58071008094184e1941e0400180c1144840b110120f0411130040140700d400e9400020403940c0b0314601d0340355085200c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 432419100 1250 432417850 432417859
    0x30307141e070f0b010f081011041a040e010605070f11040905030409061e032102070308120103030e0d050601050d0501060f1d07020105062103120f150409020609 71
    0x51055186007036410075260803a05140440e40d850141c01c14070300700824844201c0d064000c0381d00104841841820760021940500024040020358010280160224001010303c130402030100040c1c44c01d011740701c1c2440f00a2680126034460030306102d80e000007c140c0100c0300f0700508110aa0000d0951600f51000680280c00c4050151011001801400481801400c0b074030010601081d101450b90000c030444100d00005410650040b0f01145040c50600c0050035006504240108450302c2c03688140b0000030380d01c16540d0540d1070346d035040300d01e0b00300c929424641c10010006204260300b2181c000d5075141c003103405d4031054909940b007550300d5005010352030007010082800e00c2001002d400c514003a02d00c1a50420030103441d003801580f00002407205241c2e071103552002c5111180184105070041d50040e0642d82c15103010302903031a031403c1d520a0242d40b84010450f0102000585e00c00a001c1c5282d203c20802600780307079003064850006003ca69224900d01000b990040c0d584508a421419040e513 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 432420350 1250 432419100 432419107
    0x105071416080f0d1103040306150b0301140a090e06063001020903060c1e0f0d0c0f02010c0e0a14030a0807030f0206070e030c0d110a06031b0203030714 67
    0x12041e04168081c2924410021004800326540c80082841040040200201c1d82c90b0400b00c8411980c00c1080c09000c011a00100018004108150010345003010f40e04140701d040da60326008a802c40d40242d100001c040090b03200b805a6191140030320004041c1c2100511034040e55020711500da0001070301652142c14030030303c0001c41d580c514805031a00300000a01c0c52400746034036050b0b400303540011a1315100e40030790800600c56035580416540700e942a000e4035041d034510802e1100d4190b000701c2034440c02c1c40302800320030340140040c018000010703c290380d03400d000c1044000207429101d51168917010300c174200da02214907450f08200f9070215440c04545c4001d5894038400710342006080900500300003400200f080c02d05412800d8500800491381c2201c240b5940d401044541c6004100c1c0c2030b52503040b2490340c00703452902a1140ca040c50107114022a01c2c0300490009200c3e2641c1e078003010101c4e4070760750070307c0c441e011100708099190284d0014614510741101c00034002e2003034804c801000c48010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 432421600 1250 432420350 432420383
    0x14030318041113050a09111603030b091312090b0a0c020f06030f1e0609040f031224090203010b03040f0501060801060b040e10231f170a0605010507 65
    0x2d40240c28203401061141c1d80d070308064107903100d0030360b0f9501890303000d40b641c1c88002030364598034460050400b03080700a660800c4c0919802a05616100e202601096122013040486603a800c1c0940e0140c180e6140564103003a0600d0400c5e0010110340500c001d1140e1041c080103100c50b100100c41540c00e0720b00d483e504000c00c9100142c0185070700807900703030070102c08401c0002c04020040c26502595558402c60701a05d007240e5800d042c3c5004644154024801b20701080018400e102c08042d50707440780c00d002102c41140c0b40448100c44030724a5a0140d00d01011030240007005000311304000d00617415040d460741d0704125002e030300c0780b00c0540300070194400c0740c0440c404d00a082d4803246c05801010024400c256680000e445640c21a02402d075a01c01008040f0b00c00e4050070000104441c3c5404001684840390a044c60261070303403000054008900390040c6000313007038108221414890b01d8031040131003400c620b0750030520580280a08120b5290a030184002d030b8029042ea0b10f00740d841340400c16600080d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 432422850 1250 432421600 432421609
    0x1104150908010f0e0f0a1208070c020415052d0d0503120112110f10030b0f04050c0d060806010b2208010c0c02030606031917090907030606020714030318 67
    0x40c1d030104155510300300b000362202d02c4980200d200c0200303c800319400450b00e030402c00e0700c0e108480d100038000c1e00700340d6078202214026031f05198000c842d8203110010700134070f4001c9010350341c60a6900c22003090420b01440b00345404038005010882850004c1c5008036240c0034265400c6002c5a0540300306242505c1404010042040f560801c100c2c0010122550b034407280d400c50030350302000403510001000751407005030500380c448840c2c0e1708004000142c1c0c1c4207010701c10740042c01c21305009a00450440e0134110f190301c8900070320740034a094100c00b03035558403c440c001003111103d40140f501070704007500402506201d042501c0c5120102204035450480c5440d856982c10815440098507509144402c16501c1d008412180501e00a0301a1001170b6541400c00da22040701c07543c904000f4100c00440008504280e02d4020021000b0501d5454000040d0020322114002c0b03c0000c002505c60b8000d000700f59040c81054010f00110003c141c8a00d1054002a03c9000d1420391076000d0440b041c808805544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 432424100 1250 432422850 432422867
    0xb0f1018170a0803150d03350619050d200a080d0305060a09060b03090709150b1605150a06060e010c080903010b09011502011d03072402040e06040f110415 68
    0xf4001c2140e00039042134900923169109120701114011081c0145121080d4250303414a2040c0c40003064201940d07402081081c501d000780c84009107a40c1c110000300e80764851241482e813082c0910074076001c17003001400d0a81e1040302125a41e00922550008004130311b0300041038030450b00c00381004921943c80602040403048568090028a030030b1510004141110728000c50180300790f40159410729171a90341d90b10030303509041040e200008058404100032080a40903241c007a100000b0307199041400d4852620380811015401c45010306003007030102880d114400c030340050502d8108442c001b07040c4d000190a40c80c110001038050070340020010007030341d001c0d440400c0c0601d00418420941d40c640b040c100e044555007003803c015611b0445d01820309120b02c000e8040000b0100025031420344e0b00c1d40e44d03840c04c0001c60185d544215450b083d4120040142c00580090503018a46280314507010b801c0001303444803040610031980c42e14024001814100d02103d0656580c141c070201042c0040e542104c8904 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 432425350 1250 432424100 432424141
    0xc0904080f0702310615050d06080d1e020d02030a05030405011517101802060a0212030903180919050c070209130302150c030a0b0f1018170a0803 64
    0x50220001c02003541e14100034245072541d0400e0f2440b110134040c2803100315200c0d0700807541403120560107001250700c02d00c0101805511040041681517580040324900101c000c0b5510216250710382c1600b82040f02210600002407610003403a01420050380607460380320301207a082c20018004005020700c842500901980300d40e144074030300d41640e0341280c5e00c1c9144012900d031189000703240c00c56050400d076004400c9165504004110000307455420071106038810440c4100354058030402c80392640f410300c0075512400825014581d030300c0c1c8004483c1d2001d08440e030614420040b41060110382410605440d1176410030000014560b2182c407041c1079103000700c00d4000d520903ca001006540301c1000c001c030300c4007807007a0201d854136404091500100501202d0700b00c90140b0510014440782100e40040d0500342c0054082c40c0546031b440045182c00000024000110380c004041c8000c10f49019a1000185011410b9a00c1c0b046081c0095441b80c040640c040c00303001020010031543c031250007501035001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 432426600 1250 432425350 432425359
    0x11427010b0d110a030b0a09090308060d0c1205100c1103030601030c1e12060e07080411150309012301050105070623190b0603040218071e0512090c0904080f0702 71
    0xc4c11007600040141103031a0000b4001d00300c204000a042615008401c1100e5160701c46100c2603075802c003070000c408210781c0f082d142416a0103000804d01c001078908901c282c05031014003200741c50100d00c607090b1140210718104201800d0f4091a248034084240c2e90840d00034070300840c1344409168129072101c6030414980703000e01190307804518a07400640125111603071500500103590f5454680214136400c490704c00c042190721002030300081c0400c0d1044001750f0010030396400034031360042903e6240c2049600404680d0341d41560401c1c00e01c1d0031403400b440d01030443e0080c81c0b9810407000a0441c06514030060105490751462a00b00320a0768210708014406038240b40f851401c01c104180000300101c1504400e0710381096001e560400000300d1384210b4000d48112010381c4102040042d00700000c100008101914460b00015030540440003661075450361510340700d076240a04c251020304041d000000640c0300841160098691581341c65000360052002c6403a16203818201102d4030a046c4000d502 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 432427850 1250 432426600 432426607
    0x50906060a0908030a0f030b180103030507080712050a02012405130b0d1b06020102040e010b03180a120216051005030606070606060201020715092402090603011427010b0d11 76
    0x1a2540402d441e071404d4487d940038040040f400080c0701400d200102130700120320000e4018000b2900030001170044c184540ea40c64503102a640b2203000c20103040c41c00710001000011168115035090103103490440b0741c203180a01e2004d400e040000480050300c07915015990303000021085104580c8032035240280030701990113400403031901816081081d02031911440b246000861801d07c148251401c2d60408008001c00380d0800c00c504495400040c1006102802c00301c0c60300f01020213026200d1401e12880c030305070a000060320701a00740380b507003103221801b0034400704108020f83d40c1c00391460902a07d401e040d50b40740c8039400410440d10480c4c10152500c1c3c18020700240702c41d8154001c0c030302940150030001c120103500550b241603a4956401502d001503207016910003810168610011907481d5a0040c44c0035007407000b050785034101340e0245010b0030110007080028282003403000c089412000041d00c91181c01600d0805d8600e060103034a09195020503541ca0140c1e42e5408080e040100340300d800d44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 432429100 1250 432427850 432427867
    0x61008090109050f0a03091d0606181e0306181905011103040b0103060b0618040b0303130f05040b03030313060c02100501080f0c030f0705010302030a15030327050906060a090803 78
    0x658002d0350030220005404075030700140030f4500c801d40d4281c0f8403240c100d40da4507441d50010411190840300600e10bd4100141040d2619030741e06110b04805116041c0016900350300004050800703400401a1400c00b8156040c3c0fa00d801001c96003414040140e08541c01c0c801030760030800c1c010a0303018109403402500005100c24400113403035550490784194000e0040c3d43c98501400418010305030030b0051500d52020040b000c1c80c09801c0101d01d000068212401c1060800001c104130287d0382c05100c1c2c040d03140c1000c0c041d9003490f004030010010160000c5145082443e40b041c2d24860f9403e014003001e5840c1d10b104401e5109001d4100c00e500307443c50074001943c40d10b503440d840d82d14281c5a8022813051804024090501055140c0d2840b084400b0301200307440c0000540c080d41c0020303c400300055503031603509038003d05400344102940c020366420307060103060016000d001d12242d48503038060403004003c1040755580030042d64010300c1a10031b05c0e1105040b1900b6100d2452540004425000110f042030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 432430350 1250 432429100 432429103
    0x30d050408030a0c0f050406050a120f02070b0a0203040b061003020706051005030c09041212090501060312080c030105062a0a0506191e1515020d120203061008090109050f 75
    0x50048070362000c100059500560182c4181ca05c1c00214804640c040c001000310a0081c00940705030a400d0814005020781100168210350b90200081615540400c880040c0200749606030b03849001900118910f00340794443c0740c2c003020000c0149100e0000c003008120000d2003034041d2040c8a600c050140694200245110a83d1025010300390003842006c40580442c80d28003182ea00070340c4c0000220300200310500d400c84507041804821001540c8401c0780d000092000d02c1130341c00840c045c007421080c064030035000400490000c0c041085214007440140318507510142202c5001c1c803480c003001101c0700010f0001c030f060950301012200034000c240c4204c09100d400f2400910412408054000f4810304c03608060486800800e40c11070701da644010050f503420168888001158440304043c0b905564003008540480c2482d402d4005030482c02d0510004d076001110303d0066503c02c0310135401c40c5001004201580c8148504030100714010000c10b4503848290f0002041d01d402005890103003614080c0705 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 432431600 1250 432430350 432430357
    0xe0f030a0c020906040b1806010c0807080d0507050a1205150904150e03070305031f03020603010803131a190513140909010902011e26270d030e030d050408 68
    0x2a400f815007880091900d1400c1d214020340507400510075845007400f0054600d80c400010714141c14825a00940400300d4000805044158441c1d448513554501c065802d00a03104003420306014098180002c01e8142d0b08081c90084503c4000000242580ca018820700d00091071001ca07a0411142c3c010b200c2401100080e040201000e22402d0203840d4000d10b04560702e00c03c5c101d01400256003440400d0128500b03460b04103640b86501413030400180ca80e000510250310aa000c1e45543d4000207036020b80d24503205101c801410a07002501409225103604001c600c610303180034420303152996858202034013502c00c0d0783c8a6a841190401c0c00354440c11001503907480501c4007031040851500003482401e0500441d44825410394421000b80041c10b070b20412303c0315040d00c040c14081c0c0030140d01d0306c0810244004800c01c0c058400745050707090250901c04802150610100103800403401c0d80d41d1044006901240d07416035140000b10502440310850660003030000307241800f42010148428400008083c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 432432850 1250 432431600 432431603
    0x1305030409111803030414090a0615051e070f060509011d0a0201080a020f040e0421171602030315010903080d051008030406090311010224070f0e0a090e0f030a0c 71
    0x307a045a0300f80c4101a50ba00851260f90300c00607108003426980d0800d01549a00f00e6288103012500d00c2d02d4503441400c103c086202c400c00610040303a001d104800c0d881c0d0706801030202000580c40c09586032691892002d50050240082d030701e0b60003081d11420250b215003104544040d94508044030001c10980700d10b4004420707800141e0003004101815198401ca56820000803e8146010f182c4103510f01a0040104103545109070707240c0314a00d410b14003d20164004281c2c0e6120a60f11440740c20386008a80945a9239104942c41110740701e082d0000103c941000c20001c0c0208040c410300012107000c0d0b010703080100046e401107100c0703812215030380209003d08641c50050f9a6103031100714079681c0707000e9403040f0f0000030742502040010480d5140b40e86e9100e0700600c142c07440c0d107400e1401d00e6803070341c4230342c05100c40d0404c040c0c00c10040c6039200d24400580d400900c2c2001c07030b82103008002000c000c40c90040c111a41c0e958464104034031030030880035914041260542c0e885500300000603088895483c0c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 432434100 1250 432432850 432432877
    0xf15020c0c041a010c03051c051801091208100b0705011a0105070302070509040311030a08070318050705060a050c1903031802061b012d0b0d02030303130503040911 72
    0x20050a00d16280c010030355012501061883e00705004001107401c03c000e60000c3e424040104080070390750001c545604c40240d680400030506080410210340800d80020400810b40d242404000004865092801504940e071a002c2d0594450080b0a08404025072001d04a0807000801500f01709045d080700c4542c5a4007116805d14210050055031f241c810074a004005070403201d0700b80000d2a11101050b00316000380380041040505000711403842e03000b1083d200100e2280d10410524543c18001d2135850140214404207000707803a5549a43c07019540640c6204140200310000403901c160705980385110940c088030074541c203001c080d03032141200e08020782c002402d1080346507805100da21a19510f0754043c160038682800b00104541d1545408101e4184c0d5481e00490034014180705003041d8080f0b00308054410040030788072003030116494002058004c0c6540041000542c0d808001d40c0c3d800b0045c0c030f880b95600849440c2c064210706c200e40001c00315904c6c020b1007000e40003140b006440009000c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 432435350 1250 432434100 432434113
    0x403110f0705040c02060603120c1609020705070f1206091502160b06030601141009051302040914280f051302030d090b030a0b0312030a02070510060509130f15020c 72
    0x410891b29a401154603940650280300c41d040c80780d80000081c48110002415a0400585604042c502e4555a801540c0c400e070040f07404c4051060a201c50740c010026480456001c0d07140c82d0014a005500401c0501080d07607034000300d404e0101c100e20080c04800f00380000c565404003030540204203010071a0503201d20380c5440014006090005200c0c0c16100c000b02840d22124242040200c1200701001d01000c0180181002601c3d03190700c6240390305180c0310000035071901d04042c40201280c6560b4000c603a040c1070b040510040d5030f0a100380202c6980915145285d1580c0c0d030740703100d004d02000040420030174948820003805480b00507103441c01c0d920803001d40d14603000c25082160481d00d18003450300122800c0020800400540d40002c1d80d1035005425285c00c0c40083c3c000110540040b603503001403c0e00020030702c0800800703112042400c3c40c0058104201414013010441c4441c1c010321018080d501295890148000350031118440c90344502c0481540e190354034150003942002628824510495 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 432436600 1250 432435350 432435371
    0x1b0303060b04120c090b0609100203090a06090911070b012c160f02030309150a29030f0d0c03080a091e020f0f13090611040f0810051e0403110f070504 66
    0x103010fa21086c04004100034180050201000b0b00308500782c00384406e61004122005140e1110302c1c646000780001c0d1241c503812490a42100c090300c003010300c884401441001035000013079181c142e5606641e540501101c121086803042d005d451848082080a0038811003044504c1c0700705990f07200030035016543c80b00380384450320042e079603030009980045080c2c00501d008064a0340ca403050304c0d070050910b5400300b848141407840c0102d03034540a000c0400c0c00401c0c200ba0006040810803031100300402001000a80350510300249101504100101007088000106e0301c1b40360150481010141c000c9120102c0c020398500b88001c85052000403030180990f004034010328504102c1080c45100003400198141c04868442c01c0100703484001150640e40c1c80038019041d00c0091701400140200c4600360a0302e0b42403210303451410502ca00c1101080c0e040400f0446464020000c2c1d2106081b42c01419000780c41e1842c00f551031100c1d86001150320b21490701090442c0400007110310890318150b900304508900c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 432437850 1250 432436600 432436619
    0xc22031109060d0b0903190e0306060a031a04030203090901150305090601120803090f0601170610180c030615030204030213090302031902120703080106030506030109031b0303060b04120c 82
    0x21152030398451003d0b0342100200b0b11000c8556404040f0100752450300e0100c600b200520b050700d040032000256002100051410108101e68100d0401c95403008141d145580344041c0c1c1aa2554103034410000e2030120f404c040c000c00a0b200c0c2190001d00b504070700d6844070a45901d14940640b030a00180c00c001c0822640b02020507524146d513000300d054244204280c41e080c800d50300c050400c0301c00b03105031501d04c007002500b481800d000c0c1000e040d031214400d010f49c600a00e85140904284c010680301c410030405c03080d4100001002c0811214003044030720313020000750010f2816520204a40c00b06401200007550315034010810b491003120445000100800d10804407290f510b0010050f0f170041090380000001e8928a2040c02414070449080032010110203045030488041100450312240045c0200c5815000b41544290306400030000d4095640740280150550340c4011080f04070320380c034881450302c641c03c8440036018101d1020340d260303030710384591480d00f500c20001d884a4403142d03000b0400051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 432439100 1250 432437850 432437869
    0x1030b061309020303160c0504060b030103020118120f080c1b0321030c090d05100207020109120c0e0c04080105040c03060c02070303210f0e0609010e12030f0c220311 73
    0x2000703001503040000501d078211b000d6103908020780b083d080d02403000030250355078000c2c00090014110b4807504c0c0e5246100140200b28000b0b82401d51140c0a142440801c2481c8048994550407010614801c40329092020311442801504200360141400f04120f1660030407641d03004250580c201e40300022850042c180c9071100c202e00035500d00003000429690242c0e030010f0841d50b40024510105004150b41c8c45113000307500c10001035855000315400082d0741e0000e002c0f1000f442c42d084845005011680c5d01c0201d91514010642e1800c00e202c0441d442c1c0301d501042e9070103000c0d0080200031500742410520864100c912040f0751003410202c0f1800030600c00300320f07603044961684651206919a200654000c0d1403100c00081441c9d54241c6075401100741d0050040140510015207028249003030f8940c20344102c1e46080206500c103044148000c0e5580c03044950099007410302c2c4a981c1c6034000490494803802407100303001c803140079240c1080e884d00180f250450b44203250f03151800810505001c00c009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 432440350 1250 432439100 432439103
    0xf0c021e0f03030c1809010f0f0f082a100504170c01020607030e10020703030f110c03160c080a031107050307120f0201031104080c090a0203090604170706020301030b061309 76
    0xc10501c00f0a5600c04d10a000d040d10243e110701c030300300071040c0342c02040e00c420b4240d020703d024061001081001c1c9203556a584054607400109640300d50034060300541d10341041300884202c141c8484840311048003481607585ca072034003d0200d4404801a80c00400750380180c0290000078000003401c40310714200250003003030328074180c010b000f0300c2d61000c8007500103008003962460140940c0d422040e400c4131030b10007008040d120344c500081001b09030a6150495507001030001d900d040c01c002d6618002d40010039503401d01030105504142c3c100c0d52500c40d5240d1219404403215100b00c10406042503084803c10703490010740012105043d42c4c8000301565000c843c820b03010303072000449881c004640030b501c1e8621418010f040c0411b40d00c219280c40b041c0380e0f10981c0f0100080d0452000124149019400c468200000180540c20750600080441c0c0355400034200030138075910358a45e811500c03912029560501d0f0041c004541365a503d043c410403245040326420b100e95024082c403a840c440707611035100e465 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 432441600 1250 432440350 432440353
    0xf01060311100201230114040b0a35011e0501030804030303020703032a09080a11060c10020f03060a0e13080d0f1a100c080d020d0f0c021e0f 62
    0x1912840c18000082e1280790107404654a503034079000f280100e58862800d0100e02d0100600c0307585042040007921540791401c500c80c5080c18064011a6158072a040a0350034950b1041000054040c840c4880815141d070607020819400d007103e01080194400301c50030010080c1454aa02d075164038100707c070405d00009205220510040c0f0100b07200764050083c15102e0304001801e00303000e8059400f01d010304111840d072012030310000c110040e40812544002c1072401d0003000c030b800303a0390307289416542900302060082c103000c2303400300005034100079400010000c503104550b2a8216042520150b00860f05d140c00f420001d100043c482d4507000d000b6103d40415910000c009100b50780305e0b0440c1d441885034240007034a0301754690044285201d10300d00b1801509070048800945000c2c40452014540384130284048030b6401c00100f03040d1411901c5007014484010303600e02490407c04010309001655900c1c4a140414000e41da640010380c003900c010500346141d07110490024030950314900a0001010b6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 432442850 1250 432441600 432441623
    0x403080112110d2105130b071e0f060507110c21100e07050604150c0503130b120603031c0e0304030b16120c05090d020d08030c0c0f010603 61
    0x8010180801100c14441d1120301221042d10b8001000450948001c1d1150898070b804181c88881d140c0d0325000200340d6080490508041e440c4001005010741304604c3c20100c0000c070345007000301450b08200005215a12401c69401d28102403004405141040300c840340380c007000c01c42407401200b0b43d40002c0398403002007901c880303183e042c055600d100160f095640c0315001048083d114090044043e10800e0b060f0000303110707005030209481d1a1407540624012700c02000280580103040c01e03203960813155821b004010405500d000c92445c491544a140c0ea038064000120302c1c440cac403500a00401c080e0f40e00241c1d954a84800b0188ca920420030344100090aa100051510303099400a0f401000d801c6e0a5a007041d50720348500e0401103003100c1050b1b903054000c401403280382d08850a48484404103004021a1290010140940c441c0f0b6078807911401d41d100d4244110743c0c48000700481682e00c18200750b00ca0610380451861038000061204540c010100514959001486006d0480c0d07002091000c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 432444100 1250 432442850 432442859
    0x14010525050120091305011202191a04060314060a050f030f060c0307110d0203040e061f0906020106050f0a0603050402031c090f0603140a020906040f030b0a0e0604030801 75
    0xc41000d4084100c07029500c5109507090000c0054030f0315118001800000d41d1140c95400b0440001000d0003080304d4540f901c8010311001c3c58800740040041c0c2d05480c6442e00110745040900ca40109a100e8804450312509011701c001c0e000c80544100d07802c0d0349007440f0052100344015900e1400b00e44103070300140e4000b810401490702c0614006190005029103074400115002d89040c01c00454450701100400014070650b2503100c2c8a090300d0a0020005d071150040c540b00094a07840b45106010607506242c0100e2095503402d401009002040c0f00c42c281c2c030128621000e03188034000d00c9204059440e0a05c002000c4c10b0006400740d2075440104000e0545042002c2038004010250052341c15115502e889a80050040302018490400740c03200c0c40040d14001b000700c580d290300d4001d201014206a410920094280030054006c0300c5031101588030542603000c00c3e84d6020360760081c2d0303541022400010034410305805007802266030220610204801003129692424203a03070007400503c03140700401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 432445350 1250 432444100 432444157
    0x105060d1e0f0807110d0b0703020a11030a02010501150c030c020409060209180a110c0618120a08060405070201110403080a0e130b040e010507171003060e0601140105 73
    0x941401d859854611922192a00c1020096024040b5995000041d0710005e01004448241e2031391000c4035640101240c503510300b41070300000341081c42415000300301442403078040c151503003c0002040407030b9111070702803100a0181c003080c8100c83c90031441e02071620403207128140c28a040c0d90151142180d8425580c2480014001a14280e51456092004d038403d507981c2c1c1c540040c01c0d00d68145104090400e000c64400702c60303450f02401c900200c10452032614244c0440d8240e0703c156640700d881c40c141e490350030482c100128407400380030b42d8000085628400d5000303503d090003000162010400b541e56250140d00301c80c1c0039883e2140c0e40700140802c00c000741c00303c001000100c00b12b00d42a50700d59800004501c03d80281c0c071030042c0c15074492080c41c2d0141003030b00c42e160841c0c8880c2d00a01c5503062410001e04009105141103091070b8801000500c607007500301e540f03c01998020f108000c0e0462031841c20392151030070b0080a8143c550391134403030a150301c10302c244c45440c0c0c0035003010395000c0b403040c4050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 432446600 1250 432445350 432445373
    0x604091113063e060711070602190b2a0406021221070e130902040b1f03330513050f01050103051909051b040504080306010806011e02070509090105060d 67
    0x280603103140c041405141c01c201340300d100e00484140d122503e08040020406081210301d4018008540c03020340301c1c07950154001c40300104c0a4000d00500741c2c1d5244c8162540710165100382038400a62407042d0046044200e0f002401215440d07400c0e104056880d4807107041505c1040070f1091000d00400b0380004107820001099040100750030441c0b844200707400440d840070130511f68a06c2e415030302c2e100d02d0158100350060480810084901d00d5900280d6800d003c0341c00b8011010804260343ca4050b20b5400c4000035000d42c514040c1d000c852001d400b0046d1a2007a40c0c03d900a00c0d00490350480c3d1807061025070b0154a0007003001c1c018282d4a68208001180200001440c01e407034030030316003040c4800e41c04901c6041003007800340029100050b81101c1041c083c49000c540603014519140801c80802c18660035a50031600901c0c0410309510381600403035003c004c0510341b203030302d169450000c13041c2900000c07208111034055440d00125645d4050300c07401c07180c0841d04550400088182440002c4205100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 432447850 1250 432446600 432446687
    0x1801050c030a23040b0103150905100f1112010f080a110d0c050d110405130201020703120309021305010305060f01050306041101050c030d050402040b03010e0a11060409111306 77
    0x20441c2d50f103180c4444180d2560140c0d803d440802c0c2400c01402032050003079412074082601203050013020002d54501d980d0f803410000c490101d0755545008bc100103000d8200f0810b030701541444a490304000c4c285840303002000e208540154054440005440402040804c0304d1900010b400300c2c44440181441940800d00c001102c0d2410004800308080e518440c2500e550303802180c0c410704c00e003030050501044400192841e007a0f94611015040181c0c1d0008416040d6680171104120681d0a6501503014000460000303501c006140e0710310348003500c5a070081c2d04032406034085540c651590003a9080444d0300303000c0d26425030002c100007404204848090300f2001c006141c85850502c25032001411600020061040b040d101d02c140411b6191500031081c0c07840c1c0480003008030805064031280d4951881a004103400342d42c01128405603901000c3c4c8004000c121028400c1c45000c500c0a49a5030005144e502e038001c2569010034201e100b01c14a4401d9411078113185900400306116080e50b0500303152 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 432449100 1250 432447850 432447881
    0x4092409090f0b07020c03060609270a0215070501050601050403321009110306100501080c0d050f060915030d0c0c0518180606010507021e04050f1801050c030a 70
    0x85480010f4801c40c00c607100f4000ea0b400b811800c2881030400d818060090304a0b803040491005000604400c2c0300d40000e003400c92002c0030100251521040e0809034011000b81d801a070f83c0303040c0091104882d008214071840381008111070381d91701005440a000d14000542400d21200860143c0d215460056180310f4481c6606140350750319018580c507002c0c034101d05589050b1500103407400c01111441107180e10400710041d02c024540320750741700d140c0310183c868541003003080d202080c0300a035503000300c44105a81003414001440c0003100c0701d076400c1041d0740341400707114483d00096110325429480302401000801800d1180c030329007c102d981524002c4203550500c26034100007401e40d59140b48030301c055603850744900300c0d141c112040da141c0820704024200b40d0b003162003040400da07800803c66903120380c101d940b0001000010b207940301c0e089030844065003080ca00400c0c000100d0601c00301501c980c80b103800700c8540040c0e483c0e955082c0ca40a84041204403010701c0410042c40701364215220000000d034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 432450350 1250 432449100 432449123
    0x9060702042a030e010b1c1b0602010507080703021c020d020f030109060819050706050d060e0702100b01020304080a060506031212060405011203080609041e06020409240909 76
    0x1044003403024600501405480251030011040b583c150140010301c84a4030700811000140c1408504c074149003109225a42c07410750001000c0040900a600311803c4a00400c0b018648420000e8024602a1003c01c040b510107400074410500c240200e601048081603840c055403180d0a510020b90480e050700d4854940038005250242c00700f03030245000b40b00b03103034001c2541c0b0b01e8407083c6d504205141d400390350720000d140101c1005c44d0001410108a4416240003aaa403c81c0c56121006007560b4200c100d610080100303000c5080d034000744000d582140d044040210f2503208005980d00d10917403140c0d0380c080d00f041c040c540100d400c40c1c0c4000d500ca040602600d858140d019510142d0f0f9205020520314219440140400d50500344075041c090031a400001c0e0b0b10100c1da803000741c10140c00400203842100120000b07000c0100343c0d400b1543c102d030303c0101c08246959500d04800690041d0003006d5941b0710300780c004200c0b00e119101c1c070b40d80804030b00440c0320503d09184811010b03110400c8103492104846 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 432451600 1250 432450350 432450371
    0xa030e1c0b06190305070b0a050d090539040e01060905100303030609050c0f070f051c110c0f1212030c0301090b010e0927100204170f030906070204 65
    0x841116103030340700d58010070042c07404608004800c5900d20110038410021901800001c80000e24030b001d451001e800c0315100c81a182085030f181c0b00c0c4100704443c407800e245044007001400919644c003a000224485003c0c0c2c80342004041c0c0c4d6140d141100b6001e80041c5800d042070400d544100310310740e0741000100c0c440e41c880900b107060b0303041540c3c403100c2408203820402c203243c0d2521034800035102c04034040c1320b142424002c40d9071a01408042c04a2101c0c00150070080180444200c4100760307014054516200d908a03070450441c1c490b580a10110310240c18183e504207001c01c001e07058820080418850842000611160000a40303c19030320b40f04070f0328101102401000514840e10411460781d90729810200c0c800d007070b40e00610100707061054110300d00d07290f03984501813142e01c840c1030f1041811401101c0800c0342d40480b40d4100740c00601540008480d0ba0b0b4039034000300306560650600c1500300c005082401c0c1e0754025440c9003555500709000f43d844601e0444024410300340018000308440d25030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 432452850 1250 432451600 432451639
    0x5160503070c032304050907050c0303070e0d0b09031b070f06110a140c10110c041e02030c0a110607020712080c0f1c03180b040201020a050d050a18080a030e 69
    0x181c011325000c500000c44c0400951400e00d0802d540840c00b031030704506120314543d07001c4e034a00003c0e1008051005001c800c0c9000d88807403080c96a00c94011030154102d0600d14810794036940081640c9469914092a025030000000703040d0040395612848410464501007046810a1182806504a00505450001189541b03d00c2c41c0c0e000740001c00341c500910800301b00000310281c20303810700030f1000e15a650310415402041c00103c000081d5800300d100740d0011245039202070540d5007200d080e80701001340306018110001800c60001d40da2100b40c1190a1103180a41d01c4c141101c00c140181d006034000e2207200384240d0720803041d40c4521006810b116400741c01c03505001402c42255419400040325910016800c03691040e4a20306040420002058a512507200120101c000c0c14815505005c181164400c000f05884160040b0540d10044100d200050560b4482801d003000078000c803d0a09011001d403030000f0495070a0401080d540003203613416a03c1c01c20862039580d010703078010320503545e4903070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 432454100 1250 432452850 432452897
    0x1e04050105070f03050c030f040309090204121a060a06030f181101090902031003030e030f030403082101120b090f060108030409050c0405030a0f1104150905160503070c03 75
    0x21480010a1600c0c0c076810090000007038803042c0f4201820032040c81040f122540489412001c001002c04650b0f032103003001d0b14125066408045428800140081d124031260340d0050342b030f0320528681032802081d2004a007014400d548944c0e019828441c10080540a50f0024180d180071500c04586030781070f420100000040207500f40e48020845060542d19a40f1043e00e1000d8558544218118209145040703504110303404000c050224855250340165000c0100c0481080c00d202141d0b07031a5220700d0310014640003d42016034600c1501030326403040600034001e9050390220031702c4042c0f1035015110500c030144003500b01c06d65070003150500302000c0010300030f950282c06610021a44d89140c94a81c000300d0340d0060040c100d403d0700b40418851075402140d898281500080003148844482c24000d80e01308080201c20b505c10301c1c095090031003580c42000d48045919900c0100301c59903c00301180d10170b10118860344006403017040054240390182024405a500a01d051324100314480c2c04140c0407203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 432455350 1250 432454100 432454103
    0x506040f0603180506071206080d0f09080706080f15030f0f070f08071a0f0406020d0905030d081611010203040c030204060b0408060c0a050d1503060b0f03030409051e04 74
    0x10010241800410b425002c0e0103d164000fa42c0746503900441c0c0c880076190400541117004001900c07101d815111b034240c200c0e41c00b600c0803000b621010909448064200304030001a4030215032032410004081002240c488125903040c0c542c440c081c2e0301e0203a078a80346803000b44006043c0c2c0c407599880c500f6450070040003c0000c4128002c024000010340e24500e40f800079442400307601442d06062000ba400403444500301d4141d02070009048110901c0d00074a0b0040300d8030549a81400b003400103820b03900080c040c440c0e00c210784540035025100e00a05440d40c000381e074101c0105486a0128040b001e03c8800f0419044440c64000c1c503422034001e1050a9034030a40c1c083c0c841342034000f824410b40c40d00c4c5c45044004d14644145928082c40d2808664450740018000188403201140b805240c5000b04c08039050003002000c100080080c0200c0c0c2e508283c5c050005450151420a80c40c40c03509050b80e070100d110400034015801c10f440c100520010700f00003024220762071081e0181c4d1210000544650303002e10b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 432456600 1250 432455350 432455369
    0x7050306060f07061508011e2711010f05030106020d140c120301080c0d050d080406180b07020705031f05091504082d0301090b0d14030d15030206090d0309050604 71
    0x1034001c80c0382028000f85c550081d5940d07926010303410404419540b80d40030540200040170401e0606201c505100000800009030115514188542044007980c82401408403d0701c804091174100803003220140000d0291002691001a030101000e004040c0d40400100d000c0340c0d1868603900c0e000c4c1c10b05160305100c1041a922000c001480344400030700903614a0101a5252041c240031078542075910601450020103000a00c0c0105080c0510390700702045a280000c0040445602490070341d200060480d81000140201c0b01c02040c5481e02040b1003144412100c1c2d8556449141c101103c010032002e4a40700440c850100c2d41160450360405039807107180140c1d58035071250348007452441c00c00d0232980e18000e05000e481540c04d25401a07000c0e01d0650b030318614006040110000031803809400c19801600b60301040901c0b801050000008050000032207006012602804004d203030010147d00000358454818050030690b1b051485040c40d00034064540381e000c095075240400c403680c1c05504200f142 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 432457850 1250 432456600 432456611
    0x608030f0406120e03040e180105040f05010c0201060e01051e120705010f1b0f060905150105031203040f12140d0f05241201110d0b09010e040b07050306060f0706 71
    0x54000050b50340780b0801010a005444c80301c48840c0e1244114098000034103405804100d00c0b07011440424401ca90000c0200000d003418100341c61aa803030300d18211140e6092a03070045140f803042c0142e1017100d0b14222040516401e06c010089030700351482d00c0e00b41800740200360145d039a440c40c00700340c55509020041d014050900000402c1d00b05001c2007a018422400345400003a0142e203130069495410425030b001010700d600d03002c0d02416080b10f01810a1064002e030800042c3c020702d03600d040b160100c00f101c0544010f00842030703543c0802c80b805007081c0c441e140030707401061201410b0000c8402e5450009070f5929400f42044050b04858000102540da81d1900c1803c00428801d454001149039101507008820400b06040140d440c00054001d00240100c408001000d40004003101458807a90361280207101040005044403c1c40907c2280c02c0000050701c0e0540d41081c44c0101d4020f40300e04020b50701d10b582907402d03600103001c058018070200148001100980b0251040500c952404100b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 432459100 1250 432457850 432457859
    0x50d0501030b0a050c030c0f0906040b130503212d0406020d0201050c0705030706090201050405130e100209010512130611030a0615050a0315080609150a02070b04020607060608030f04 80
    0x100c1d40c004107460031700301040060010031403007a000e0790100500c005017144c4e00e2400342c010034020700840d40030740040031001c10003100d0300c14103450150666000390100c501519079000c40c10360b9104002d62054110703a0800201c411041da030130140c03002d0500003003d10192500b0044070402c541c8654030046c010b8214101c0c480c1340359428000c6941010841e0b01d880d040c24003a0315110f40300d04c280c41004040a0340d0742c11050869006506071402420002d0082905a00780c01014024207108420544503004000e0410420b52640c400e40e0807510781a07441d2030900704802544116144041c080743d9160030031102890014442d40500c0b4000044503000580b02c0c20400c034120b00340c450903041a208003da00321020122a403220603155041e050b840e0206030320035042c08560801107507070030000c9103004490820404000024000c81d0314002d043c402c101d80d907903038a2900c08a0180f04002070102140f40c000c9805445d02c40b0203072401501174040094070a90b150300291465002208492104074003050400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 432460350 1250 432459100 432459121
    0x70e04030219020108011749090509042609031c0807030b1309080910110c010c05100614120321101517090a020f10050d0501030b 57
    0x102c10020b07540b8515203080143d00181c03801d10140122a6104401c001410b85001c042240c0b0b2404041c120390b0583c25075030390a80000e0704443c04e078170141e034055402600411282081020310340c0c0140daa5241c0c0500d00300820071042d8080074109860030a00308050f42a88554407110010840c010320a1958500c0008141400c0c0030900140e0f24400740842e01075104141c20203401c560040640c80d000aa02c80340381c000807098072407400d40e40302c0246404401e00030008070310028010a807044640d4800b600c0c56400841d424100d961303110b025900240c0c0850380b50350260314400712035031058040d160307a4007a19030f410302114116407280240e40e540d4445645581005828142025001005146400e4503020825403039402c000c45c01c24000c004c40d00144040303107454100800303030820103407049a800301e250009005081400700ba10034804c1e500046283e02c0c500240b031140e5158040d080c410034084404c10003032120405020b1006100c001c00c2052400380f941e11605019603c034003c408110308082e000d68 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 432461600 1250 432460350 432460363
    0x804090b0907020604030e30030d05061c06090309030f0b070306060302091f05070813060201053409051008011701090308040b06060712030203090d0f0c1104060503070e040302 77
    0x2d00942d0440010b02021a070703c0400141b61200c107844e5010b40c500000740304611004159a44002801c113a12000021540030000342980c0711364040600150f11041c2c00c00c04420700701c4c510a0203c0005441400015813207400280e40e05c2d0181c1401034031280c3d29100d981100d1851001100e82d52424400c21560b65014440c2d500a800c0d00d03c1c085003480411008654a01d00c828020103070030080e402c4411149210b6000c0341c2600b680410380d540c41c2c04110301031500300e2815000e038501550034080010384c10303401d070b0000c0707400e0040307883c0d11a00300985140c00c1c68130600031141c024108142c80c0c6020440da01e6504000104861a0707685070010740c5042856001c0c3c4405a8401c0c815904024100010a5000002680140c0c0114852041d62038000002d500361258406c001d00c00c107695540ba10946405a01440c455040203003a180c814080000485610603400d00c0400440c581030702c083d011035901c049081c2d448001800c0041e040c4e40700c00c0001d20342440740e4042c80956005c24100000c065060104c07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 432462850 1250 432461600 432461611
    0x8100504060623040906080a26090f151b01271e060606050409050c09030d08090109060f09021f12090602091203070213060506030f040f0b0c0306010914030a06020702030a0804090b09 80
    0x181000101401c064000303d1040802032441200341d00b2a900c0349a80e40c1c0c864101084104c8019555003001110b00310704284c0443c18400d19528000c442c0303651500140c1d00c040078034608407504100c41b0b210380d154840501d0300c031480307643011007408903031400510380e0702c40c20006d400ca070f49a007074850780350240350800c0c0d80004120440c402c000348810800341d200001c8404100000d07040c120820741c0c982c400b03039005043c80e0f5400390586081010065001c0200d0f402000c540e402901c02040010740304c200f80545031010100d2000080f04040c14a02c210700030303030080c4180392140d44003503d0058200300062071050204c0010f561904000340390300451425611101c4c007207505076014040985041c00140617400002c101e51100e0030003500107420440721070a00c02550303034022110402401e089521303c040c1d4008030350b10340c0841c0065502203401110000000c203502c4008004200484280e41c1d0200a508000702c201d0300f62280140b0000045d120201400203003866500018200c00701504002c0744c1c03080a0031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 432464100 1250 432462850 432462893
    0xa0605010c0c030201030c050d0207061a0108160e01020f151f0605070b0c0409020711090702150103021513090c021605030a0212030f040608100504060623040906080a 73
    0x340300e030002e808400040d0450b13409090008544007201c2003a2281d03c03a018042700803610001d01c203420460264809000043c00c2d20803814089102c00056038052000e84440d00d17448051100d010030244210400510700c0810310580310b0803170400c3c95040c40d144160128103021f05601d0f080052480e008806681000c1c24504441105490300b10007401d58420394201601e420414400205103803040402c841c0100aa80011035565140d41800001c41c442d10328064818540b00021450745440001d12440100c02001603203283d0340707503600b040b0030072107040066110090280101d11461700b0f218840da008050b903080c04541c440c28040020b04049080c00d6001c0102c604a8040c000c61714000340b400040c40c0c1c10358040440900c0240c8447c80d40c06410300d07041e0b0100c0c00250100315140d024124074050440030425444903611401000140c0d0307850b000d404005903a1800c0150036607111400c000440f0600041140340a40300d50031801035a40d00d0700046c0311648180710b0072040160648180b2500107402c0b9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 432465350 1250 432464100 432464117
    0x2030714030a050a080a020403080c06040c050103062102030a02030f0a05370501110d09060e010509030304021003060305121b060c270306070314130f0305070302010b180a060501 78
    0x80c00500f0a0091400c03140c1041000703400141040ca030b545c1154042c61300260011303120350303010302c1c1c445c2c1d5010704407011034001c10100d800141d194020300501003a03410a12002168100c8014101e40c1c0d41c2084a00741c0c0e0501c05d2052900150f207007070200007444652030002d0201030019040c0280ba000c42c0c1444c04611105920814400760701540048a002d014030104110054650500d10f02421100d00b44401c81000004d01c586411040c0d480f01c24810710659007404803010301130499003201d0f000c80d0307070b00e20744c0c1c05c1080050300510b002d4000700207880c114140018915241d483e680c2c5003103081c0307034044d060900c0005ea100404025000520360740e010385004014a1908180003075141c000e54101010f0001030310001039080c20241c50080a00308082d0840707465151854000f00645600551004102500ca01040000034000380100209804c0f001d202d18091443c1da0423074841c0c3c0412416011556100765180040d91038403921107030854810488040c5040240ba0101182c02991069048c40703043c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 432466600 1250 432465350 432465367
    0x21b0a080702040b060c070b09030d021f2003100e1303090501050c010207060509060703150e07050304060e010e0a051b011b060605060a0f0f0c0803060405091c0203071403 75
    0x30111000c00d503060702c01081c5140c042d400f080c058000d540d1071341418001e6100c041114403d0001030140100700b10200e401e5032a044c00280e8403504102a90030104100084110030020123410400101c01001d415200440742441e2400c1a50001d441c02c40e502000c4000c100b140c08030200d10a0340141d0700100c60303409103407030f55400341046100e88112410b114020a41e81c40760030007036043d40c400d1a0005418032203850003980040e103c2d88105e5070b080100c1d01e0000d051940e50a0030382110191191400917001c01c1d16800030994064000400880701e10f5254000c00350030f190b00380984141070303a190b4000c004c0b80001e03190031800c201c09d02540b00c01501c40350346a0705440c1e07848100c4056040e15180c08041304003081c204100a00f541d6004207800040000b03e6000c801c0e03001c0200c0c0e049161541c0c1718401107420640403503c0441000020b401d00d01c040c070102d806460654000c0ea0004841d404603809092a061a10780030b03034400c4510400742e080441c002c01440200d4041034032082d10a0040d503c1c02500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 432467850 1250 432466600 432466613
    0x31b160b040309141e0f04020703030915020403030f110304150203180f0102070b09040207051204080106140109030311160b040503060604091a090c0d0803150a030302210f0d021b0a 79
    0x2002d00d4145c910703a40248842c0315201c200640030b013001702804c195503032111424054060300010380708564a141800c5080b06880b154400c0e18196581907640d4840f401c982d0f442142c0c0f4003183c90341c92203140820040001c0001c6203e0b07651102074100d8001d507403034081c101048042c04151644040c05288071014100701aa030100c2c000044d50114429542c6500022002c00c000b4098060018024031410208444c0988014050022150090000c1c0002c0da11112040f05110074115107a010804942041c40000d000e07103c48811119044112452141080d06603001c03c8040da00600141d5800601801103081c00e2122640c04030050304c043c8000706895840ea4008401240000c00b481001000300340004018409002e21a800130452641600c1c0d03401d01d038070280c4c000d64070120613507803c080c0c03040740382045000b070400c0b2900b580244ca192240008581340900092840c24102001001072210a1120030094120010390040c01031f102d82c2e20124107014140c03100405074480c0c5c807041c1d411000410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 432469100 1250 432467850 432467869
    0x103150603110904020a0e03160501080c0a050d050a02130e040507050d020d05060109020d060e090a122001060303080c041809020109090f0f0b0114031b160b04030914 73
    0x3801d107800a04200686440003841c0901e00c00d60342e00030300004030b006500754818070a010003601241642c1000c194152644415a158802c10f40884e5102c0e000810000074140034144440365400c4c83c5203404c030140e40307082c1115401c4441c4070010b540803c0c0d102c0c0c07652104e04042c0140c01c11000105007400c10343c85440e03442c0c40038411103108084000d81d040440d1143c1e0600c04000398170408030340c02561580d0007840603400c88101d040c2414074110000508007800c01081d8081c2000d02c0c090461a0307003544400301000d91068121060207080340301502007210408407000001808000094141d0039441d0007041c91101500d6800c440343c0a11092150304000041c450790f4480414002580d40303945d20060351004d85550011200601d40b074800c84603401d00e40c0000303607501c09411f810060446044015503203681c0303c811b0340d0b84040d003e0000a04101c0e03405c5179001d699013928549410004800702d035084200d01c159045420407048800e2004264005d2030320006050158040030102c4d0503080420680d0a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 432470350 1250 432469100 432469109
    0x60f0d3008010e0a02040302060301030503041e0b120c210613270501090c030311070501030204141207030b07020f07091a09072a2105270612090c010315 67
    0x1280f04001c1444494180d04645c01954007401860b10381d80d69007081501c4c0e422034803660041410045c820081c0d800455400700507541c81410203424184c40030a802c1900b8030003003c402600004010324003d500c0b03c01d1050000c0c901c441138074403ca2134003e050109010a1103c3c200e5200d090000180c41d0018080000c42c00c0d42100c00c80b00c000c4580c0e810b1030303400340c212410080c07d0303c080c0c1c04000c810305500510144082c5581c1d4100c0e202c17180d45400440c12481240304440000090758509101883d000c042d048011514070104c580d61603ca8403240c411100079190400542d0001038045480602803026100030004c80c4400c0000315441c58403500700603080403a041c405c02c00f081c00139100502820088038251415001040b0219040d0401e9032018508102036a8500c00c1d040a10640c402804005e000c201aa903030780d60510002c01e19100604110740d039010507540c07601800e0112520b40002401912229140c0642c40b800c1c13006010741400b840800c040d040506040f1007055800180c10341c0402c0742e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 432471600 1250 432470350 432470369
    0xc0a21020a030807170709050117040c090b0f0604060806090f04120503092b021207260706020703020106031403090927010e010c0e0d0c030803060f0d300801 69
    0xc4c1d48500c0125603c2d0303441c03003100404011a20502034141d40c42400c40060700d4081e2210700e041c8200080302c40030000e04a900400b1851682d40600c84d40c1c00c550031031b030113140c405414060081c0d00b400016449400036000000000c1510040009514000541603007010804011a82500b89500c40702c441901240440d400d200700040854812101000743c5283e8034035440700c081401003240c079a0340107014844441d000520400e00054284203a201c101e82c401580b0000701c0003540380340c41e40002491010a4212144e51042c0900404035600c1d00040000901c0307039000040c82400c6182c500303500d50ba020620f034070750ba0080c4109041a00c807447c0d0150020301c0300c80003240f003d0720501060703505494081c0140d11542048c0010b0b81001054200b450a030105440d49240950b002060101030b15603080d029050325100c103401c2011415000046030070400140c048007600324690003150904040c00703402c0b00d44480105080c5460300000304071000c0702c00498066040c0011028006018000600807000f80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 432472850 1250 432471600 432471617
    0x10021303060e0d0201110a0e0d0303061505030a0f0b030309041505120703170304080403080901020a0209090a060c050c0706030b0a120506090106050105040e0c0d09080c0a21020a03 79
    0x10200648950801035611010601078440b0307640c842c40d166624070000d00c025600b08400f041c103c824002c1541c000040c1d6588002e42c0104000070844810040301040c0c0515943d490041514449404944410009511402da4038200001e070748003180c034900c15070984c0e1031410050141030340c1c022003202d0032180100d80204014580480d03c00c140e00c01603001c6a801002101401d14244011034158110303401443c5e2540e6641308a032602c1864442154020a002010001031000039601005041d40034010b00c12620b40c1c3d1810703404610244025a0315191690003150074104000c114015449018032525000d4240162010143d907209141c2c05250107040d11118030502684440e80c240008048105180c8403070580c42c1014ae80717642c0181d550b02c03d154241000442d00794061021182210f50840700020f0b41d60f5044030003035a9401001c05010000d84410022012580d9a80608891807540e000b51240840520b000011200c05c00240441e0710010410248000e4000c5024400f240d01420720b03508 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 432474100 1250 432472850 432472867
    0x30b07050c1501060201091406010e06061312060902030c031f020c1002070c060915020304060e010e0307030b010f0504090c030311030c150106090605070b0123033703021002 76
    0x10480070551120480c0752520000604030b50540013542c7c610f0054000c1840c00c07541d81c0c2c51584480003401003410403000c00010510500300300c1c008044804000076000c10540d124000c1e0440d00540e00030030386000791100d80c56019071030148000902c4010840082c000c00103186a0050302d0300c4040040980950b0110b0b17200302c903a07070034480142d5111011504641e500100d281800341c0031030310300030761000807404200410580d0003100c2100524030141c0041d805e043ca000002c541841900c217200b4100503107440c0c41022910100045e50280d0311410705101b4541c100600c038610160a0381c000c5200c2e40c1480040340c0410f00000601040d0380d054504040070710280c040c110310b0340c8a0b2900c074044912800c00380c0c00440c0380020b081c82c141d407a03540d03900281a170f0311901120940220741e00a480d0b00c80c21001001040300154412141c0070030218200c100c201091300103402c07d1240705c1021104500c45040010038030316410740840d20b40c620782140c400100141c07402566103000c0c06004101c0c0c0e40c0024900c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 432475350 1250 432474100 432474103
    0x90c060a030e101a0303040608040b04020a120b0702060c0a09030f030215010902070501061202060d151a04090630030e06040603020c1b0d0b1003060e0d0e0a030b07050c 74
    0x4192084021151000110b0f109280200403280b4180f15802c00c00600904078034022044900310341866444070340503240d0f5119400d501601074400c9a220200d80000181c01c0001000c41c01001e00520b882d1210f850002406810064001d1520700018003c04c03600c0a4503070014100310a40c1e4101c001c42e4604401460141e203085003c0305641d00c4035031564000030b02100ea98005004581c401d50080c401c031651844c20170400718003140d00030f41c00310f410f024408664540c2d500a001c00ca04824403603085543d030b1041040b48034041c5141501c502c1e00040e0501268006000d00f2000b07003140054103181441102e0040380101910020000d079641c60000041894400c80001c03024110081c00d05135141e03501c181c0540254440100301e1903a0145088110741c00341c5014500040c150058516041034a465880114044004102c803c95100101001c00404c1191041c1180014804000c4c2101c142900700a04404541d6515900c203801c002010300c0040c50f4455540c3d048500350078019210200c100425 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 432476600 1250 432475350 432475361
    0x41a100305012106202203020604030809150c070915030218070504030210090819080a0c06020f041514040f121a0f1e040c0e1905250503090c060a03 65
    0x80e811520303400617406489080402001178548180d080181c18110003020034600050344000ba42c804810300c01000071402c120004c2c80ca00c44001c1c604401f40d4410740d28850300e41c00c1299500c280354090f0b101440712004908c41c0c082d054002071801c906892039680010a409d102c0b1907020070107400c000c00700b051103019a0585004e540e0040881d607115000402c0100307009250f00c1030070494400c0558442041c052044001170164005d040640340041200381650441c1c00010102e80044d4200b02000b000001034024101a0460009000c40800c038180001d1020a000021700382980082004100b44044610040c2c100c61044005186403566030411140101089038164552098401044540d00000c190b151003403e5004400d80c0c03501442e010302041003000c03180104160001402407003044480c0f0007180e800728086610349034010601070b03000240c0358181c1e10070108076072066030600c6500300d120030034040715203c1c54920f04500e0415000e070348e40c26180604c203000d400c0010700038412a00c244c001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 432477850 1250 432476600 432476621
    0xb090a020c010f18020607020d0f06021c0c020a033c030c050307020c15070f0b06090a090b0408130b04060207030302100b091519080a02040c140a1805041a100305012106 74
    0x411180780f441e40bc194000c0e6000e2038a02812101c012400720360b9076007a20800364000e40c568018000b144140e9016110001c00c1c3c12400710360541c0b070318a4004803203d20a105120000b501403401d1007001c030f041c094152068144401d040c41400c2c000c00285540c0080c2e860380710f0508840c04100c070713070280b05008001c0c407071004060215a020701108041c002d104120602842041c1c8030f070521951081d490908507001420024a0380648801003400f195011000c4c1c1441000384906605541c0d4541c2d40c458250b0180d44a080560811070003001410740600a050091201c01c01c24848400204001505140b008010204801c40019001c840d9110507a064a072255043c558901d260745504c00c26035503980f644e8040784624140b44440d10403c0c0300304000d20100c0340400105080881003001620070841c554081c03440c0d412440d400203aaa9200e0081000b0011200f00401a12840c071085c4a200310349104c041d01410305020041044101c04158168541c800a01981c0c100d221071801c0d401070110f2865 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 432479100 1250 432477850 432477863
    0x11704060603021f14030c0a03020c190323120412140d0b031011040e07051c02071a011401050706060503070e070f020c21010b090a020c010f18020607020d 68
    0x20b11134640560b0402d80e144c1e40c525901c1d10061241c4000c10703040385200442e1201c0002d1400d020384d005c564000c0d0090442440d010064a4240000700e000ea003146c1281e820580000308080c0141101c4400010b52880c0c410006d8203513407820410b40140e4604800140c0000d11142d0707900175101d040c0c0e128842c05181c040d10030701e50300d50781d603e0b400408002c1c10014454a11074091001c41c041550314510502e840c0840e40401c02d0b0030140b40081801c1d12060007040703c8e09124041040d24042d5070403460f1098056003c600068a400450810210306d0100c0700c0c4036009031823104010300c442d02e16484140c00010342440e1182d5500400e15048020344201c0e4086601823207520000301c0c00b203e01c002994411060b0350307034140d01815014012070740c560b0541202c917000b981d4562414000d184440000f046040e454001040084412021840f1100100c0712070300a0342e4041000c07100600c080c01610380e0301044c1c85040c400c074910560541c08011030030710005d100d01000900c2a0454039111681802d2980120f0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 432480350 1250 432479100 432479119
    0xc0d050601051804050a030c1a0412110d080c030a18080301150f0e211507090b1804150b04120204050109061214010b060406091401030b01170406060302 67
    0x50100e40e941428041e080c440c2c0071030b400902030003d00f89445803040760401c0040040072800e8400350384404413a101502c641c4284110150072001c0381d4440b50243e03100f11140e400c80804284020302d2210140b0848000d03400100c90a802c13240e010400c250000d8a00c1001c40d03484d2504001346000b040c0305011002c00404642c3d6520a00c100f0802641c102c60f1043c1500041824a000c1199010140c01da03240200310410503001c0242400e0b201c001c001a2030307900020401c41d60003611890191481b903400b4605980004201e415a4400c481000610442d1202400e102160b4400e001001d10481d06601556071682c20004040c030b070110110080030703c1440320713903120784403080c4101c0c00700c46200990085080400000b0000d5080c1b28034811501d8610014081d018030365281c051060b80850108100c2d903d81c81003500c01d40c0c440d0700410007405a41c8999003441d1408400411028806004074141440c0420340707143d50340c010b18241084100100000110703038440c9013403c020062074001075084044003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 432481600 1250 432480350 432480353
    0xe0d061d0109030201021201050901030c140312040e0402010e01143007170c030c0a08060d020a060507020301150e1902070f03050403050f0607022a060a020a120f0e0f01020c0d 77
    0x640c01070541054031f6190680580c0c031a41405035061003840010722a03955040204101041c000c0c0e44504640300409030791034030740e6100301c889482e0416004000c1c240a603805110440d070f000007416a44600a003070104000c4818441ca2101e401120039001000580d4607028120101d03981d10303984a0f10780324420403454108644006c14045e0081d418071055840c0d54046640c24140606a034814040042858509040841c04840c0f905c40503151640000b0a001040300603910b850a140c064200e941d1003585864442c0101800d4810130340b5603040080820700e040c0001d54240c003042d58050300410200442c400a506030714001d2040084c040c01c400310390081001010307030280c005c0048a00a10890701401074000d80360340c441c941542e801002d64000024903101c50400807400f00c8140744a0401c81c2072405100110388103070b101040880c010707040b240e00c48081166140704440e6525207480d040f0072103c0400800f9100e12001220184106e05407400b076a45d5a100300b2420501001c060808403d03141107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 432482850 1250 432481600 432481603
    0x1091406120c1314092d090303090c0f0a15090b0a200c130506030a080d15120510020d020c0109110102010c05090a18021605061005010e0d061d01090302 67
    0x101c0c42c140c010201c2000013588402c0d079003120a440001400030034103482d40d805000207114060507a013400344101c241550350800304841c03184120b4001e40619505d00d03004100a0415000445c3c3e148184c002e070380000340980302c8107010340079514510746900ba4103d8101c0150b508100d96808151030420010314040c1641c0c0c0010352002146080c41c41a24003580000c0e19902d401409c0c24403608031400e0510072015001c0f64205a40001c1c01070705588540c1681d44bd04060355000818001259440d46c603c0f0844628003500382c4000c007240e10740003900b01441d584107911303070f001c45400e01c48494012a4800607010664110b0700803401ca100200406030040c54803001040520725100c1c0994680401c064010340141c6c100c92901400602c0321800c541011388601d681104c4541d0307214550340c244101d24841c60384c5034074140c2543c0648000c0400f480c201201031403400301500583d0403c8101e1940382f030030fa120042d00d02007050380007001007004a440c48043ea10384e10280080001d642c241505903062540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 432484100 1250 432482850 432482857
    0x515130807060203061f180b0708030a0c0302040b0c0c12010c02031603030b040516020114100521030403150c05040315180210050a0801150e09070e0a031a090c01091406120c 76
    0xc48501036000d10343c0c80c10f023541d590150101c0504141c04c1000081c1c1c035036446074071540c800d111604006080c42c0c0c503101c01d0000750308050760b03134952075214802110305890500c20301c03055031004000034482103200b14402901da000d0b400741601645141c0e603d010406001c0e801035001500050030403c11071418032103990000c12000c0911000d546071000c004a0945c03032400261040242006110242c1e142c10144070640741e03505e014118118034880000c0d0005030030b000600086005007039402098042c031254900300c41e121558035062060810080001035001c40340c46448076800c0c8800903035100608a03c08a600e01904025403002032400381c840c100782c1220140c100002c0c0e640e21050a80c0e26400c2d44a104400b1603e6500490307100380c1d07a02541d2802403542c07640308500d0314140f12a160f2075400f1404030702c0150011259050106c0c000411052445600b03030b4088202e00050011921002c00078240483d90302071074030f459581c001e856100362202c01c101c900090000003071000c42d203051900305480c0e13007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 432485350 1250 432484100 432484127
    0x11202190905041b021c020a0b070206010617040b07080a0f0606020102130608010305060402060a120504030e0f0924150c070503070501090b0a050d0e0102070515130807060203061f 79
    0x1840c3c0135003030b03000803103189410140d102e03a50001c1c000c50019410200c0c0c2d2240b031901840440c03242c0c00000c40010440091103000d032886800070310745e81d414010060080300300d40c0c0b01030301e10815900821000c1030743d039151950041c003642480b0312551680000d810251007043d00401015081100000708a0b82c1540280104060030303003501e5002e62030303a1003120345401c06c2c0f2000d490740c2d00c51004030f4058034201d4010001040203003000e0b10050385404001081c0e4104a030150046000c50212000b0b81c105403042c0c580c166422101c025192402804c110142e4078951310b010400d5003904160078080d2140604d6020b030005040103180c81d040110341c110713504d02c12070203424082c0c004c800002425500a040c01700640e400c4070401ca050800340358086469802c641e0f0060000754903001030a030710740000e00c01010241d01a0014007030303c00d41c140c480c04400c40050000001400d071100d14030081210a0140d60060f40d025002590300d85415000070b030707040502142c9201000303588560140c1d0355008100b641820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 432486600 1250 432485350 432485359
    0x30f020c07051507080f0a0c0507060503011805010b0a0c0203030408030706060f050406081009060b12010906050106081006050c0307020a0f030c052b140601060e0406050a050f011202190905 83
    0x702e806a0f01d485a90044900080000301c050200c3c21100c403041018282c41c00503881e201b603ca407481d071202450b244030f07644250f0208000100601081c0307560401401c040040030820b000c80c0d450f00d0030040d0944508800041005400c0342d09d28119071b02030003100c0007081044200e80c1c8400150030900c0091042d031080400815000e0310009081c10a401031a0071204000f02401106036502d4bc0c4038007921b1852003c441039641d44c1205c44640e9260350051511601c91000019800014607020003100d41c103811841c10f2110768010080070b0307500d44408205443c2a071070b1941d03c5020500340c0305d01e10300900d603000354003203214400441e10444031102c030300440b40640307810304806603600244078035a03540c4d0807803400000301c1d2000140020000d0f001415041d104486c40d002c40d08880358080e00b0301400380c01000003c1e050700b10098462401c0c0c00b8500162004590303004001e0300e01000200502001004c0340d041c010303003d00041c1e0500f00b95040e034004116451313002c490102142401401d06200780182d5124 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 432487850 1250 432486600 432486619
    0x1503011e0906050a0303080406060302180a050709180e03040905150307060906050405060304030c0210030c021e1522060f0c170117030c1c14030906130201030f020c0705 74
    0x22590980107510403203e02a2044d4011405c1d5103080321010301c010030a44540740c03540c000100507100e000801403a0039080001806908042c2c1c045400c2e22409030400c0200711002d0001c0c00390f19644100314022020390140002c010680c035841c0f07400e5001e140c1c40000828980301c10802c20f640162002d800444040701518622512003509446a01c2075014800c0040d40c284014131150602c0c00003550031030700034104000140410750006c0e004008150a58000070b4a030103055280c940c040040034242d40f0981035030b110203455901103507a250880f00e1500c803080d100ca0301180c00216a580e5010f0f002e40740318640900b400079030401402030f00408181c240218a0030b8850301015105090005210362811040c08043c0d10f40030180416100c400785091950008208800440600700060180400924544980d4024401c0701501c02495682c501040903010810840303004000300c0c0140c1d03c0803019030107940b408402c0c00120700400180c4407042481c0e00c00129000d1203c00007940804860044509610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 432489100 1250 432487850 432487859
    0x110306071107060507020f2205060a180b2103070309210b0405010f060f080f0d05040905090c0904230102090f04050604020d02210606070308060108061503011e 70
    0x19410700380c8601e0700050300207035810310250303102c0c0d40242042030000302003050313110702940020280f410b00d100000ca09007136504041500650f07401025440413007104c90b6018103140c8480c0c01d0284105901080b001980c1d1080d0000540c0d98001940c50b4201c012050401e40301a20036403543c2c1c0d44249410f0300400d4400070000740c96480800c0307040b4400d040720721361400042550b6a0358440a07014104030358554072610505603200759482400024405129040300c501e14007000c5904201032a01050000d8101d44002c0c00c40f01e4100048400b00c0310103600024545d55aa180142081505240964001c01c1d5105010500a010280909410b4480c501c103c084540c41c0041c2e00300d102e05042c003a00441c42021013141c91500d0f61045034400d0000d0000f52904060030a19022030b4084039060560301018804460003142403071a032980410141e503407520307007200c030b440191134810002d08450400115500003600c689a001c03000d000d002d070a0701d1981c2c81c2c5d6100e1070b41c2844426845001007103c12003000009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 432490350 1250 432489100 432489107
    0x80303040c09050c0a050309011d070e0c07031e021018060b010f09180e1606090e09120c0102090405090106080f070f06030b060c0d1d040b0906040e0a0f11030607 71
    0x80c0544c030341041030340c640000307620161460b800091509480355a6001f0310b01401c030040403d9a400250440038164444c1094480a00a0009046001d41120500041c000603402114904444200400200c4c400d035041c0b000f01c1c680185850b5503409103080501c82030020315100c2d1807501c13181c0300b02d40501242030584011039204036000b4030340d80040e0946104110344241000064180030081c103005c10302000708000305113000c80c0d81d200c07154290030441c004c1180d00e6200d0003030b80251610020041c1d45040071241544d54031a80b9082c03110205002540d4800c45a0950440d0300a20000d00140414901200c1003070090a192044410703c2c065440c224500000c003040c2981942e018203504400701e414040221f000300300420710710790440f004004404140034108023680301c1c0c030000d80d64a10110b03035000090303d5002125103860b010b81d08000d40407140303aa480601c10303413040e025036000602808030180d191404400080c080c3c002281408020240324215103a03a585100c2070301118010b4a41e18001c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 432491600 1250 432490350 432490361
    0x304060b010e03060619030b0108160509130230151524040315020d15030f0f0312090302010b0301050c030f0103170d02040b033309040f0c080303040c09 67
    0xe0f5260300800700090703c5140036141c0b600210408000b601405480c0e545c0e51072484000e170000d401d01d0707000d1001103007000035840081d00504016105d50102c0e05100f21035180d40390342044002c1c0b1415407110302089030b4080e42040500407400550485111084007803880d1680b042200b001d03c86840480040c105140c4581e03900e420100c064aa00324000d41d11034103030110f8555120100c90f2050810001010918460115150f103401e09030042c1c3c0e403d03016000e0f00440d600410400c000001501d002c0010411070346075816515002080f40c0d1120321f0f1403604072000381503254201c148510b00b0202d8810b0560544c4540f4034004103070000c02c4951610ac0781000c144c0003c40304071540c2a600001070000410001d44c003505070f550044a076041104c51036042d4180d8005c0e0300240322003d0007004100034000d02e1142c6032400540104010b20030f15400304450707000040303040158015140c9a020074200000d80d8010901d40d038000007541139003501c49030b1664480e40241c4e002d0311150311500f8081080718051045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 432492850 1250 432491600 432491627
    0x9050601120209030102040905040b0f090d0906080601141308010b090405071a0708180f0901030308060d05030705010c03060e091b091302040510060f020c03072106020f0304060b01 79
    0x20600440c4000c10761a01962294040d0b54242d5001e000c0003c405600d809000d00403403040303c03d0181498400800495040c00a00558496002200c0345a869410441c0781040e41c02c00e02c2d04846c02c2d5200001078a04c8203008202000b080700000780340d002041c18034034600c10394401070002d03c2881035500c1000754130541a200508903400c48a42080f001032541150141201103004e5581800d00c40d4803080201e81061f035840004460190742c142680c80d081c9039044134030320200c9001c0c0703140d411074800030088000100000d0103003c8106400090040c100f081c0c4d095568010b00038442d4030308c02030004018080300e10900040071041800308154110100726004c4900700008041030002c0742c0b200300b00c440440a0441012111400c402e540541c480c2e008062190041c9a24854030b0340c5005402028099900d200e1411034002ca003160400741c1e404525030003200c040c2c0041e004006020061800056100032005100c03500c0002c00d032505c454800c000d544582d009031820043c1066080043d951404141c01c1d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 432494100 1250 432492850 432492857
    0x51e03070c150c1a0703060e130209070e040f1d030f0906090a0e0901090b1e01030f021503070206041104050108060601080408040f060534260406030f050109050601 72
    0x4080c000003520a0b881480309842d854540d18003403090b03c90a03030110148602900071000c040411034000d0f01805004001d00c80001e0301e8a49241440e80c0780f000310300700b5000910958010300400c1c0e210f8840c07441c4c2410032400a0007041145804d109110040c00d080000301340d4020081c0e0741300d10181021040e115114400003a051411950780300308140c0f54060222664040240c150104075015501c8019105d140c1d940300000c1c06038034a00b00f002007580003c00d480344c6001d607540f61303051002000c44c40c241100c0c1d01c001c42581c903031100e00c006400390021101c030046038240841080021030340002d20030702450040305410402c04400c03082c0000e84070300b4000d150707180d4440f4000c200301c0d5120b94001540907010f0039007541060303261000030b444000c056100000059010441c132210394410071107c44c400d85200c10071290802d003141c090361803070490a0302034044003003548011030704250340340e2541000300c1251300d96a0359500d40c90040c00a2000c0c0304521a2240741000200c0d90300807a00c641c50203078078142c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 432495350 1250 432494100 432494123
    0x70609090b03100e0f0c19090203130b070c0b0f010b040b1605100b0901050603130f0809090403050a02100507021f0b0603070503160c170d0b0d051e0307 67
    0x40c101030007002035841c1d00751181c041c0c81e10b084a00c0c1e210780b010180d544c101130184d15089005161910b008680424410003240c2071900c4d088110988100461320b601d031016032a55038540c851010f419946201030140b1002c03804104116a01c1003a108076130740f040d00c402c40c03603444110005403040024003a00680b40c9c01004244121920500541200005a040004045c1e52640c80d681011803011103050040d861f15010030240c07605d6242c0f1405002c1c00e8802c80c3c11840e00302c6104d1040c001d070210161401c00d61840c0380082c000d1501c1256612075011b440040c1c141031500d001031150744000540001406840c00c1d11040c0e1302c1901401740a140c1550003800c21a6448521115140c400e16049641b59aa034105081079100c2d44065441420389882d034030744901d0301c14940e83e4090321100350001000010010f40c400140d0f056400600e98641c40c402d26100c42513504a50014440707000c9041c0c0c0103080b042220204603001400940780011482c256094030b080c045c24a40c1c0303002d2018010090708885c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 432496600 1250 432495350 432495359
    0xc07030c0206070507080105181207080f0f03010e07080c070c06050a0504090e0106061b0b01030605180f0609010b270a0b19090501060f27080118020909070609 70
    0x56082503a01800100039500d0420565200d81c42c0801a034401502d59440394100300c0c0c0e00e04144604815800100003070542420300c1481c09805101d002e200400010380440c1d800038990305102a07a49030048400119601d585840030000501d01c00c45000d40011803c0000942003282031045d1242c803a8001e05101c5118100101910b180d003100d05801d007006000d02c80041c0e52a00c0717004a0000010480001030a9400c00100602c400c03c62104a809408910340c1500001c27540f044441c1102c0d0480c60025083c0c460f0340d50040e252460840b2070281c1d203e08130005071351000104205001d42c2000c1c000300710407031607001401504008080c043c8180d401c500c0c503903082c0305d12141300994459400c0700000741c2c080c4044006140d41013041e48070002c1d04800c2c801405100d0741c6100e20f5003d0311503400c04666060700d20746c00404005000d200c840f20856950858a16000411004030161015000a004003482e8903600d400384c3c88680c806a1117401d540001c5800e0080100d40c00054408650b5882c2c6034a090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 432497850 1250 432496600 432496607
    0xe010b1816111501050a060816111e030901080a1109040b0319050706030e2b03060302030601120611030c160c0302090a0f0507020105160e040603080c0a0213050c0703 73
    0x407020009004000e000519000c009101114690f590411403908550411040c440e0310b01d5250850380600c428901480790200704040c1d134141641051a080392020688021a801c00080ea040090354180c1808400122040400078008100d800c2e03890741c0d081ea40360343c00482a01c1c40b034000212890070800c81c80e0700608054000b0044508007400710740c41d0448009505018403a980c509030762603041010140500d40c0d041c010692001501801441459012407002d80190217422100028000c0c0c08071103840940640c00c030000440d0002e06543c06581e50301900d00322509210300880e10a40b501000c03079070140e002003d0707070300400721103132583d042449100c6014281c98010100341c0300d69581c00000001681c43c000004d200d054464000f240e095254204c50058030b6014040c4800d69041c4020000030b98074010075032520f00314030700d41424609002e4000c00c000706400c1d04007500168000483c500c03003200024066000c10b1080d245507103085d4186402c0d0007203410580d01c45215080400081011910 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 432499100 1250 432497850 432497881
    0x2714041a0d020a0e040b040b07090608010b0304020d3306030c03170f04060314180c090a020f03040501020403170703050304060908040914070206070e01140a1e02010e010b18 76
    0x40a40350f0103d4030b4461403031001040c000c41e03049131045c0389041040104144001c01343d41081c2d0074145400d0150900002924a003c14018a4a034070404000103040d5aa1604140f0b051600070211a403080c01807903903107030511003c0c08441c1e041c8550340c0b200307050b4800720f01c01e01c4116900700840c40c0500e81140d4415050000b420322202d41504180b103111540242040104010895038900140154403000c1c07202100e44010f007000c61b1071001d0a03025004140110300350001c1d070303002c03101e0502c1030f601c81145e40006c1c0900d1461348002d84011040008000056000b0000d490080701c4802c01401016000c0b01144640c400c010005102800806d002902517000781440078441c2e030a9900340b80c0c840d03000c1d0f011200e0020745080b6032824481809440f076014072030300b900702071246010034070010f1040000c1c080c401300c0c01c3d00c0d00d018800011071a460307a108044030313a80c2224014004111a0b082d40c4000c0c081c02c0302c00900302c2c1c3c951a0812181c2c040c0f0b42011a2541202141c100010542d01c015980e0b98400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 432500350 1250 432499100 432499103
    0x11060c0703051006050411040605070308070941101202160609020a1a0a050904061505190903150b01032d060504020a0912032714041a0d 60
    0x4103610011000640610144075181088440080e607980703040100800d54802c00d51a40301083c0402081c0071040d0301c00308903a0f000340c01d401c00070000d40f0f07103000880f8a9000342d071003c0726200e844031031104103400c104600c1b0f842c0e5501c12a141c1c1c8415041d140042003286500d2507543c0801300480030350300c0030300030030004001941e013100c0142403070018202030540f003241c0c03030781200c515030b480d0b00742030443c80e100d220305001d020383e0080104082c54000c1019074611441c0c0c0c0300014054042201d220580e6503400c01d502812036000c04d4250780041c2a00500150072060110503030b600009041c4140700d00c6034400130100c942291f9046120246014000000c180c0309001904050301c50072408180c00d11100720022075200b00708202e43c584250720000c011035140d504890701c180c0c0100700c51040158461b5616068640c4111180074681007441c0540e030800170045200d07505144c035080e400d100354900c0d074140c0403241c411840ba00c2c0804d00d0020001241c240c000c8003540400360410070110360418191590b00603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 432501600 1250 432500350 432500353
    0x907080a0b1306021c200327010f0209100c0b010b07030516080d0e010203130602030705070605151c0b04110d020a0801050901060605130e07050702040507030b0a0f0311060c 76
    0x4018540f509001e9912000726500c41d4984000300c0c42e170b130703401621440340c03044040c61000b00c50042e80f81caa00c1991001800144590a500e104502c60351015091003e840708440c000300b080c00442d07000500039402821040d44601d42c0f034030701d103d00706010790030200d4281e03400350400c04560300300820034107240c0118000b5000c1020502045500d003424441d0440c3d01405000d4950319002d11180d5072040d58403021941d1540c0c3d0050040c000398100360080e6102c000e6200b17a0250701c95440e04422121030141d010041c0c086410a8240140001c0c810b00b40c2c004008165201c0c15085d59040712420b070480220b2000b4202074511002801007111802181502000188103c5403c0c5068000565600c203603005860181d542c0e90510003ca0b6007403041c08001c10032030814a080c010003491140188a2910518184180020000782098400c100310340c84560300078420002c074207200c40018020505500e07024054032144102094000c02101064107c1364081451301904444c04203002c07061700315800071643c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 432502850 1250 432501600 432501631
    0x3020123071b15090807080712020d1103070b03160309050a020d170a0503010f0602010b03120a03090f06020a0e041a01030b31051003031407020f060406170907080a0b 73
    0x1c050445201c2071450f20b0994076844070030b0a224800d401c00c46154082061a40100010081a00d4466140d0140c030340444031118407100c1030618072910b04514090702e40c103009144001c05c003021010051401040076408984090030703030700400d5084880043e405841a4420381e081c00040c601a401c0c6403032144581c404015880740f4807070300c61464205440e00e4011880110051102c0c100c8882e41ea0b0090601344001e00607030707500d140400c1d214000503404180484001441590b040d010790420303c1d030658020140e80d100c0006080000082d040b0340b1042e0005601c6c115110075910b01405208218650391545501d021001d60041d0001c00d00d154924cc0c020403010703200d00310300e0f01018008000100d0203415503001c61060140d4011500000c0c0421112a20040180007280d407141c03c003420444d01a140079551078450002038074403032072240d05580c4a20009000301e0074641c41450005042c0c000014030500c4c1d00c4818071543c07a81064051118650712140a41c00421412103699400c00c0d80300344074442 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 432504100 1250 432502850 432502859
    0x503060f12011112130807081e1b160530250608071202030705070c0b130902070f02060a140d0b0a0b0c120903010e0a060603020123071b 60
    0x2d4a240000411a07071401007011444255814144c43e80005001c912801c1400290783d11135150003654005030103074402050b03040e80007801d0243c5da0350345484001520303107450600f8002401420443c022040d94028400303080c1c400d02036107410b241039070070003403110f00c084203512840908107541010b120115003d0b550b1104a003842448080c0b1090701e24400d81005c0c100000100110007040e5002e8010040e0b00b82c00c00000381c0d8001ca281c030392028450005640e0fa11618001c0703420b4041c160000c1c0903500d404000240d1000c030500100081c46000c08040200783d074488480c7c0c100e01440c80c1c05000404512084401071402d0801410505900d00300102d5a83c0350040c00b12554000000c1004503d0359041512030703e1504074192001800c070606c40310314114030030740303040c0d11005100c0c5c401e10b0f0703a83c010490303089540d000c1d082003022403c3d01c800c03180c007400542010b101a1509100c141d021540680d403070190b00f50441403005805813114101458514907646900480190055031105008118400314 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 432505350 1250 432504100 432504103
    0x1201140d02190e0c0421060908030a0c0216050a0902070f0c080109051005070e0108070e0402070b0f06030109120804030302070b01081b0f0109060e0d0803010e07030c09060503060f12 80
    0x220025503150410249810071005200000c0e016256140013074042c0410015a011100001500401c01060794400003080c5001d50103400c0e251001452070314003004005501c45554860741da4805281e00f1980318010884601c01e00055600540c0d8110014160034070948811360001c210b55882a200c51885004685802d12480e03511b4001c1c2001d40d4540c2016418030401b04400502c203807200074100314509100401502c0e60126450a0b4140101e41d4000344400380240300842541c04050b00079981e400d0245820782d15607504a51f8400130986810103d181da0405215210140b40c1c02604103162583d168002d58039503400400480415800b04004070000781c88030441c1b80244194002462620742d402c200d0420102981d940070702401104603c00c0160380c1c05100c1d002240c0356030070303c0841042880013081401c621144003400b03518001000007000038840c016203102c1d8070780f50340030007000ca10700e2000c540010007803040c180017880501c0422660f1a00500c1803031340c200b00074503a07807990400000d106d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 432506600 1250 432505350 432505369
    0x2101a03030304121103090f04150504020a030b0a0e0103030206010e09100914061b0a0c06140708090708030435060903270603010e09101a0a0b1201140d02 68
    0x495021802500100c01d244c1c100f54030305c050079065006941000105000f0031003204007884c040d44961b40340d501e801004115211000003401002d03000390741ea40c08092010b4080c10381c044403a0b0181411040000310201030310907403816240c3c990701030300e0140d18040c81016070420150299071140142010090320b0000b5215040742c09100d47c5142418081903d03006051190003040e4101014001c281010040b40010450344c0c2c8002c0c6082c03c2c8048074841c00c102c001001d2000c1c2c0c0086003101c003070a02007029049010705103d50040011103c51a40b0b80c1a00c90302d078001c40c4107441e400c21400d800600711204e44200442a00ca010002c0800701c0100410f044c5050025101d8040030f800005003122113150071b400043c1291200c21030550502c10740d401240709480144509c07250f4018110110354101d4041c82079072514070101d003007401899002d80c0032201079051a4040780c4124441c0000154800c5501e0645240f040d006100c9509680307013803000000540006800c96000200d0413820300142d0b150b0446 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 432507850 1250 432506600 432506603
    0x1e05181611070801050a270201030c020a060e010b1018060806060c0105071706040b03060408070602041502070914071710090f0b030f01090206070609020315070e18060102101a03030304 81
    0xc503a0381401c03420786c000c6800014002c0203041d0031800d54003044040c003d03241c10299082c80c0c006240340d142c550880c00d100c008617008006074205a44620350003015000010100340c11a88400c10001d850000d880124080110004008494130b080002c24016016168410b10142c9000d1520b901560800c1c2120b00884421000c02d440100c0da0380600300101007258843c034140c0c0e040150004241c0000c0d07988400600060104c0f00004800d010400243c0596000344011000b24a11404080000c0c1d2140f145014680f0700c03500c0c0100d00da0451400b03c1103140204240d440b6005039520b01c005511010f070380107002d03e404512000300016030b025980300d85007400020a000140030020f0104140c2083c070403140781c0495a0500400802594904007107580d02c0303502c40d030001580e0203030384003003800c0003820209004520100f00810103050380080c3c1200c2092421074942c00f940070300801110405405648050043e40b05800c42d102661203075101c42c84164500078500c13001d03c0d0010000307146901c101c90 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 432509100 1250 432507850 432507853
    0x2070b0a0f0b0604050a0315091202150a051e0601030b1e01200303061306090c0903021f020304150509041503030f030e1b0f09011e051816110708 64
    0x207a9501001c0d442c81032185000048819a1403e8030303050021350070305030b9400b0240c81c1184000602c2085107030b9501c614000da9108040d444201d8510002a48030b514000c112038840c3c0c0000700244000140348143d41c4910081d2651280d000c0007000c41015074a001458607050556035039161005641c1d1811203244034012070680341c10a0342c55000100600c0c0260840c181c0c4000c52030310030101c100003100703481c0e2041054400c0042c815405a41c000986040c0d40441c0c8070760f280c810140040343e40221120305590082d1462a2a444044407660a5000d0a4900d0b03005810500080c000403240840d00801d640551a2990900b869100000d0031211504003068295655103810002c060300020304441b0040325043c10002109441007403070711000081c000b2241031034804240c1c102d41c0d568800e400c021240242a034803040d07840701c180c00000341d078124030131802c0085030380c00059a1901c5903400c1d89440880c1c0d1000d500d070b100d0819807415628240c11820600c010900e03070307501e10300c410040c20700140018070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 432510350 1250 432509100 432509111
    0x41a100b030a14100602010c08060a06081b070606051e010905040b0406090609050a0e070e01030b04020d052a0409030903020d05010b0d0f0b06010c03020a0b071806170603060105090c03070302070b0a 87
    0x5e01030f084070600c10340642400b00c15010000c05075100780d001811105c0354104510250350700c00c11103908031015100d40800c00008100c1c44207005107a0301c614203030740080d10100d40d118040146050031252a510060003d449207000b0302043c201500714201d0048041e00101c0c000e0b07141c124031019105c440d00040b00c1c8683e540c080010700c0580740507030300140004102a0403c40e0502c001d0000c04001404050040c51800000c20119160341c1c020b0b131086600b08059540e07000d49059070a500700701b14480030b81152031000700e020f00d5107014414018116415103c1c01407662840e402e008650a003580255101d543e20000e91140d0348444426001030b80c07240c42e4481c294046450503940560014020604025074802c0240000703400194612500d60455142c0302e241d52005d404460142e180352a110400a1031000080c1d0380d0340040391744040310300c07940e20b4406580e5207806048e80c0d0a400d2003008d42c00844030001c11542c2500000464110480f454003506c0c00c112512520411002901c901d00c1c115a1107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 432511600 1250 432510350 432510359
    0x60801090b0a0c0c05100b0102161e08061e040501021b0d03050a180209250903050f030a05071e0b190b03010506130c2303041a100b030a1410 62
    0x344075510700c10f015410410f080364070340e4a40c1641ca040e4070105503603c0380c1e5035030000c1c44c680c02004440004000c60b040e501c011074a5202000c00c0c3c42c049601a0170209040e0780101d04070070041401441030305c40c40000400c00003000d0340103905040150055402d5542040b9050840d00c1c00f1305140c140c030144200070b01491414031801411a840107000000c190701e00302c0001005d852481000301815011100c400c26501e4100c0444210b200c40c911442500008144150066800030000412240603105403400c00c00d0704007902d505c911590340b50800040e8204600c4001034604200f2002c0f5103222040c03003200c10a15a01c88a088509482e084580c0d18028041401c1042c1c034056600e6881041c1d0082c0b011317050920111304a8950004101e00e406d03102c4e0002e0200da44201e0450b002d180c250403103050314802c3c250440f0043e50090301c0640e0300d0782819044803a105000c822441c0101d0ba21024010b050b45002c00c60b000a40018002d03070302464842d80003500325221603801d44d000e054250008805980b50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 432512850 1250 432511600 432511621
    0x501050a0518011802010807120c091d0912070c08030315040e0c10231908061203030103021504090207122309060f0c0f03090118081c0201060801090b 66
    0x1991060140380e061110300c04490f04501106010281c5c28200903456032955007040d501207400b80c0c0d18410103441c0002011001c0c2c0c0c014221000c440207040008244141c080703011a140c042150070030190307400115085603001c0b41c00000c1c203c1c24059682c4900712131f102c815607815644240c0e4000c0d030780c0b0f0301c5500c400194a81840b912896081120042407a0203142000c921000c4082500e001802002d51001c5005403416200075428190b07201003583d00c659440010031600c034801c0c5d0030400501440001095810000340b50740000a0360002541144e20b154200440c1101c071900f95085a0804c0c0400101c1c51158006403143d2849107581801c40300e10701c04000e108074410850f411072251003100c00c0c0f03008030702c50b0700302d5121010030f981113940c9030314607a001c07103240c8125400c05a0728840c99480f00c40d1090080050002590240d80380c1e41d001280845681095469000c0c9544942041015a41c405560800d003131455001d8000825501e6445d102c060031654103807410b48081c1210f60800294420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 432514100 1250 432512850 432512881
    0x11e05040b06220e07090c0203030f060901030c0306091a0906040311010c05160f0210050403051630021906110d14030c07020607080a080a0e21070501050a05 69
    0x419991152064254107904812a0a408603603001ea41e0b160080303104440b0178001710014200440d82030003a2240f0f50802035480c0d000311090214840c00703d000c1112480c06060b254122900071054086582c11900d407803000742a01c1004035400c0d548112242c2e4100700071080f00d031055003000050021031409007400b1700803c1280460482d1a403500740004911074020041e1111000c2070900c4803880465032401100c08000810082d40c085900040360851591020081c01524403400c19204c2c080c08a5580540315500da0148841320320b00d07110380203031012004a2113500034480f420034010145c0d503600802d100150218001c3c1445036030300b100b4401607401649040d198012100100f03101380060600421203504048036510f075801c00404501d6110041c003d4981c035640080c8900d5407000da80c607041c0310300e61150038030f280811031103400500820f005125402488203008040c11124030b0f4520300c00c200b0640c5001d4815503c00038020000414000d00c00d8034828104040c0c0003405061003030203444d5011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 432515350 1250 432514100 432514111
    0x80103031107061e05040b041518050a060c0809150c0d020625090b0c030a03060b0324131107050705090c0d05130f12090614040512011e05040b 63
    0xb407028204100c5642d000c00340d9090101c4052184055802c0c00d002142c00384070300c1d4821141c0350004580814040b4402c0d194260b1a00e05807200b2020b803642d011107003800c5560b441200e41c0300340d000c442041030720302030000ea50703c1d07522401c46145041850030009844c8649030100807240b04003c10405a9014100102c900454031400203000d03500e040f25176000f213034016a00c031031050200e4841054409003d4560403001d485007028407611808091540c6903030742c201a5000700068140000000c9140c402d400310303802054540841200882000d82c40d03a41803070183d02c2a90090b02c0c03452010b1003144940710381d240418400c64899550b862600f0050710344519500201e00ca10741c08028000c1500c00c1508480c680280c54602040a60302c5e0300346008000610500580841a070400740820058801e081c9a02c100141d180c0c1070000e0f4482c0e8040351907910540d461700c4201020002841a454000c03100ca6030816091700106400800d0004500030840702216640d095480300140070406c0607080010b40d218 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 432516600 1250 432515350 432515353
    0x708180118080a020f210a230c040b1203120a14090604060e01180605091c090303080901090206190e0105160b04030c02030322330c0f030801030311 65
    0xd03414005080d44501103144003c0c440d11010409180c2a100c0c00c6c610f000303500ca101c58182c146e5a02d464101d0711080c00c54030880d50105a45000c80c01c8212503a64403540c40c010704002e126440a04062000502a241c01150311801c0d113001c0d180d4010302000200018070103040120305c030303003003042d4000b0503a01004000f07004080d001c401c111070560300041542d03019130040800b080341ca036200031031401000f201c0c00710391543c001420048180314031a0095400b5895510807111003050001c9001c50703101046607400d0018065603c1007000c00d00c42c101c45a049034580d800010303010390039070018006a22004840f4008a00403102c60700c629004140400068000c2c284245000c107074000442c0c2c001c140c908001d198455078404201072602c40c02802080d9035010f01125502c2c840c482c0c1052a121154810070041c00a04c0d002250008030840034140c601003988040c40031103403400c42006104d0342610600200700300c00d181000440c5461101c404003900903110300c412075055040081071070403c0956115103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 432517850 1250 432516600 432516647
    0xc08160b0a080c03041104020a030b0f0a1406221202151c0504031704031211044a010302040b0103021c0203190f0e0c010c030f0e040207081801 63
    0x12500702103010f611510800b01c55650b0703600c51a2201e440c80070040103c4d0054404104203000d250954004031501504850806154401c441003003034911090198604030b0341d90701880c150324284440030f171103008440b1040002403c1c1c052a00103a500140d813101c0011a000201d4a055060a540015540d0640c070915403a00e544002940c8101c5200328260220381e41d2400001c052602c10b84440c44040529541d101c180e08141c00e00504002001185140480c40c2010804241c183d040885040f0b81c0009810701d030030018480d580403102100704540018410510380c015206050380e0807414001e44c0d258400c403a40d411401404200c2d0050000a0f0500d0710400c030100e81c20785155a0313a481d0400c00d2030056a60b40c0e030703aa04081b400343c101d905458514148071800307051401d10341120509804000455401e8010400111080e801c0c00c4409030114041c0760318040340e01d2103245511649d14002d8405440d00e0745941c0c1c1d9017195404282c043c2003088803452001c2c03c1d5a88034140e030750300311071b401e42c00c544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 432519100 1250 432517850 432517867
    0x601052205190f060c03030b03151f03020d0f050c030a050a03030b040608190303020d020c0a11010315060c1e05250f0b220b040602160e010608070201090c08160b 71
    0x244140c0e1401341505114120141c0020144070303421155100e0760142c1510f09a0807003004990345041c0c281e40c1c1640d40c3c0c00899000d40009800e0110300120303500100001002c3c0155142c000302802d030035005456070b01a40310507540c25141007194020b040e10400c01041c5c802014100203089801140f8421321540c1082405c200045000400390340c00144401d074982d01c001240340a400a11640699401ca20700204031b50102032030110350029800d001e03d0444540500a10044003200c01e030f14011200e50280101c180300041c030580050103001d11030503544207030550074801032a060f04000070072180303944880d000010703400440000710303002d071060f400035054030f0b0070000307001c2c1710f0041401845940c40c400328046200203050502007500d01c600d0340440c048640ca41805003410f600c103020b5000540300c0e10b460030a003164081c4d60041161074a400100003070f400e00764200c41c218000381483c0119074a805d00d0700d02240d400b00030000201041c0000b498014030810145032074611680c00b0b8010640b0602c044407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 432520350 1250 432519100 432519119
    0x105070306030c0e1009051302090c070201091e080102031003110a080607030e071e0f0f0e150d0203010509010618050c04140a0e070518030a03090905060105220519 72
    0x40e55005940d0900c656151211a405e941c49640301c182d045081c10184030302805030b100c00c103c045009550b03461040e91080200802c82c031801c44024005120350030104032400c5c00303842c0a6095a0154010301090b641c90480c1d50a80e0070036070704070802d82d002e80c0041042103010591a0034442098a22244032454842c006484080003010141070503108d28004c10803241c2031010380c001e04031003138680c40700c2141d00c11b80f0050f0702030074094280b8640d0030321030104150249260f20003c45401c240025000d07921800320107040891004981e8000c07442d61001c20042c1e90a00556104410b0b00c00002510351428180d10300c1d01c205040c2000b0402e1130300301440a042440021581a034606200e02d060f550803279404112550101d507c4002008514030600011640c80070040604041003907a100c29050741000305034460513118402000720b4120301c02004031250941003e5400201410310500700400d84560300d05c4002c11020034510691106001d000525003240e400449015219202c070f2a2414a003070030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 432521600 1250 432520350 432520373
    0x90d0f03050a0905070906080c011e0c02060f03040605070306060509030c0907021609140c12040f03180906300f080d0c050c070506030c04051e030d020a05010507030603 74
    0x1101015192400100980c070b10b0f4110b2510f16a100c4c0440d41c0a50303507500104010b14141c0210300060144440041c21507102d006038560041081201c5100d030002504140c503020132044040340c2100090003a607161030041c2c40035500c110b0207100c02003002d2a240c0e10040403180e0f150004410b203c028001c41819450004464100000c2035400c0c00e0f842d1a0040300760700c0c1c92900c850101d03907411182404501c2c59440c1c1c208182d1079040640d20202a02d40101000c01070048400540040704108000b070081507030000c50404c024000c6c100400846040e00031001c0880d510b802180031140c95100420a6905961003076118071141c0c0c03900f242043d1041c1080d082003c940902600c07980c00c0f58010003d000c0441d0403203010015840d020001014050000307401c13a0054042c006060140200c00600ca042500807030f44180c40101c40c903490181030404000c1602c0060a640680c00c54075003a120043c0c40410030143c541415400904280b0302616080f400d40764020085020141001400c00021f400700008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 432522850 1250 432521600 432521627
    0x1e0f080601180306090c050d05070306110403150f06050402270d0519080c0102070c0e070f020c011206080316140a0209160c0203150603011512030e06040b0f040e090d 73
    0x440d003510b40e1b042c00880001d2a402c0181d00c846008421410400002181402c60384a0b00080c0149604280007030b009005a1001a00c1c03c0300d1004111003003200e5900007032810b8462240010090b4450010408a82000754048080e151100c41010b28194000c41d00001043c01c07180d5000398202c50707640e15254070039000d07402990b070403003c15841000315100668084449820007151034840034140451200100d02c110783c020726460380825041441251401040c5034643c000b040301d1485040110b4220034848425200641e54180210384520240020072910701890302400f480d0545003021040c001610500c41101e078000c00449005888812030554043c6060003400318400d20034005480c403610a00d0000e615000c2c100312030042d68843c01300580580c0c07064008100e16143c034580054280014003540b400003020f1215130002a21480c4035a1010b68050301c8181059540d411449154200c400140c40440d0081424001c8084400406a01820351030041901c000840d0024004000e045c01c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 432524100 1250 432522850 432522863
    0x14090103170c150901020d05070c0b0106230f090316080601050103051806131b1a0a0212030c0d0b011d0909010b030a060219230a1e0f0806011803 64
    0xb16038050410500003c0d0301003980e80c01e910744a250809440e4001c4d03202c454642e80403490320010030409031003000b07449040d5a01046405299082103408d888855407a100c56075525203c1824120321000d010182040b80200103219494a041504040c104001d0301e00c440a0b12035660380030840b607400001c40324119002828001401d8440381080307a01c0c040003031214075040c4140020b202c4110003e070100c2c00c20600400b09580200481003590000c100c1b5886640304492840c4642c03e00c00503402c006250703000385401200e005101101c164511a0000c0b102c4010f0b01601203245440b43c041405076110030319003441c0041c030b40241c0680d4100311000c0010350314080c2000000240c0080800d511680d60304000034121007498025184c5a0301130742c4107460020703001c4160745040c01d00f2400380d00d03122a248002841d01c1d220a19426054810360440107461040081100c07203d59481400916000c070011207076254848071001c000050304500c3c002e45854100050b5108440c455000d1160000640327601c441c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 432525350 1250 432524100 432524107
    0x3010b12070621090f020112050606340b1501030203041518050313060e041b050c070e01030c08063102010509091f080307080a030f0e0f01061409010317 67
    0x36050340810f040800c03c500040c42d1807600350a0090907152042424802d03603030001e42ca51210003507402d403001554000e4101d4024040781000880c60f8102500c0407068000000b0103541410800e00c0c1070101c8241943c11800d80d07410f0005660b5001c140b0f603008803082c2015031075410070350b941d80d208412401101c2201d03562665851001c0801499001c04641c008027100d4481c10440720b080c0c081101d030b100e10004180c01040c060450b092a0082e0544c2006e111007607801445c403c401900c1691003071003d40801d001d01080802d0b04649104424041c40c090321400c1403650a040e000c42c50300380c01521808885d1041403c0d844161040903060310645c040c552061b604103034a20050301e00f401802001c1c1e03403044410042002c1e100c0c0c040c00035130b80d0308031407a545a80e143d550307040e1603107030720898074040d103051810041c81401034020f40210403c0c0e1403030103001854440b20a4504e003006803c0210039088d035128a01004800c1841c0100300201c0021200c21100b03501d103660308010748110b210107400d80380002c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 432526600 1250 432525350 432525377
    0x30602120c0a050304141c050c010e0f0a020d0f0b0a1b020a121202040806010e061f020c040b0a0306140601030510050109050d030201020f040801020a081617060f1005040503010b120706 81
    0x42c012408166641f000c08590003c00031030142040e000320386112640d42ca0311005260496001405001520040014004008841c2c0070b000d40701c4c1450000b510600d964002840001d079a95008601c2407100c1d8400017540303003c00040c10410000c011620013158803c01a900c017203003404200b20307980711403070030821094a0200c05510280c0035980c0050744601904000041e02c40640c03050740e100e03003011112003401031054801e85c2c1f515407c5140c0c1500503031081d040340c1c8540c01c00398022404074100030980a100d81e41c03642d6403015100c0184507059501050381c20b1003400d507050301416420505090b10424002d0030200024105111841003601c40c10440c8a85001d00d4000c0d41100d0b00460044035255407283c0720b0025502035489856650005043c21000603541c00c1c0d002000c014425041d500d0b0781910100780640100b4400203001284d0040c51400003107410307960700400001c0381c100c80e26040c0d246e81c40c0004141c00c64485007500750140b140c02800d1881c0b841c0110307005040c2c174940c1c1401d20028800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 432527850 1250 432526600 432526603
    0x80f0105100e031f0603050d0915030507171501030b120d030f0204170303040302120a080a0e010f022205030706083c04150e0706050c120301030602120c0a05030414 72
    0x942805000d80c0381c0380b00707810844000640100b006d981c003450031660004c094070011110086288103440d40003498905008041d8031035084590000098980b0004140a40720881a4003000b5a10a00c2000c1d0320582c031505560940580c596144041701c038030002008507414640c641203169511010996a01c00c088001010f55064030301600e00c25418140a0001480a030342d241c0c8180d07030940140c4602100c00f19062070030004c68416402c10303a140c0301c0315111025500094403008405900b15500c0340c1c1c00c00c500200a20140c80e1204203000030318017945030305505c0300d0041416005240a0b0704100400d1000640001442d41c01c50169102d2064030f0400e0300345117002007a01c52100300c00c0d0040551201001000135130302c1b40924082c00c402c92228460b04040740481320700c41d500c0b40064000c548100030082c0510094000100900e003074908541350100f00f42032a42c0242c104a9449a0128042c840039824081c030765403201500320b0075403502c0d20079003010f0103902004000800c800c1c541c0003000301c8080b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 432529100 1250 432527850 432527863
    0x305100906020715051e040f020913240c030b150c12030103051e0f06010e100b040f03050607180b0901051903090b10030314090d020a0f06080f0105100e03 68
    0x810914150044800b80c840d0806090281e680c00c1e101ca1b415131000d0a5640c80400c19030190346d0101c03410140d29800d03800e01a940d180284480340c110030fa0240c2201042c4000c00315820040c7c3e81c00041d14040044044100f1110a82414004c0600e42a01405951208848026a450541c80031030311030030300716100ba25045646d084d0000410700800000204100022820746600700e941400074492907400300907543e8480f48000710303160707803081c0010008a142000e144d500041402c0d9015941a10383c0030319500f992090b84220b108130305000302007003401000c1c050590000b0303492500c07101c1941d000da0b0300209000c1c0d500502e858200c2c0064450301e1a80144221a8a03111324401190307030b40e5090401900419a01c1403d40300000400c1c005000c10b21003c121170103803903150300c44c1c194542e10300323107040465041405603a4201c840c0854500c0581d460b165114014041c1e04851142c6500f807404c01010301c82c01900411550119030018040c92740c0b2044805603000c0140340c006291311200000030324188 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 432530350 1250 432529100 432529103
    0x70b1306060812030a11030c091909061e0b04051e13090602091005040b1b07050303131d040816050a15020d0501050f0102031e070606090606120603051009060207 71
    0x8a8102c50b0a0100c8005010310311642c9040000c208200d0206c0394018030b032004442910740500f04201c22040380c50428400d484905e01040d080d480c55480b280c102d411034016400c94004880100760440ca100c10b10020200603240350b10395142468030700720225801c00c0c4c804030780d003081582e101002401d9803a2102003d0300700b403241d0424046403035641002e2009600403810b02d800751281045001d0a1400748044034100d85d24a03400b545002016800750340c0300340e10f03422004202c0c0540c400015260b0340c204050000020110a943c04d0349280000c55041c222500d00038000741c0c6401c03c1080041150042501da150707a000d40d000c03035103200a01e0030a0030242d284c4002045100070704140121181107501601021075100340070401c591300c890800030018500899507005138410080c00e00c1d0406c00c070040400c44a880b1800d81d040145c8d507076406050310f5680d006002c01c0ba07500d543c1082803039400307095414552060001003044c40e080d5100d02e170700c07224002101c441e810f880380d00000811556504540010303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 432531600 1250 432530350 432530353
    0x905010503181209040b041103010918080705161703041511120a02010f06050f0609030307200109060c050a0b091906050106090f0b03130215070303051b070b13060608 73
    0x10049882c8501d03013a00440221405a40f034405450300c02d0815108049022401c0703541c8030f081d80e1034500710101405428000c42d44415103020190300107500384010380a0340d8811000361440e00101101c1202001c519405040d40c00300008952944640105c101c5054401e0208602450500d501e000d660015514051415910450484082e10322109019043c2c0d000681e00a00040142400180540303019000385d9901c91032201800d01c26284c110020028210060140c034140702c40d0f911006c03103d500800600d1120800700c00b0145c825a40160528040c0807141840c9103d00142e84540b075403181c0c3c13103000411405940020502101003048074000c0d07480035080c03418011189180c42c3c00503100a00c42c107004030b402400085894441c1114400a592001e0b2620b8203655807151203d54990310310500781d800060b10803100c082482560700410303001d0300a46002c205424403009407100144480d400c0081072900340050800140100c800342e8001c2c81f4031450580054080c00c004000340415406154203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 432532850 1250 432531600 432531613
    0x50a05040e070206070216050f04330e1b120603070f17060127050c0708030112121e030e070503071502010b030316060207170d0b12030406090501050318 67
    0x6881e8005113162044130305c0d40c203680d501007081072040070840c024000c80c1c0d80040a400403194904159104d0440084071640503220305407203443d007186103072558150058840d180441441000d030f40000040e00200041e43d41c8030351010409070b0340f441f40108500d2310380b4403042001051a43d641080914041c00d00840340c850919a10703200149283c80005004003680600400000c112144555a42c402000d00c09410f041407401d5180400400740100500b01c0c03582c0a120480200302034402071070103002c00117258821580d842c1442c4041501e0300100c042000040704401c040b0b0440e10118400c0764120781004a2120349000030641082c0c06c1d03401c1250103101d4090009803200d020300307403005c401100d60000c225402d900d405144e202d120f20080284030152080144000901c15802408500c4c0110304800caa5550400c00c403c507a0b0050380d84c60007141d140e01c000411490b1080d0740b4503a811807840110325003403410384040d03e110054881c032818400040001040d0800b5103c54004e2080d191003075508 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 432534100 1250 432532850 432532861
    0x203010b04051305190302060708040606091b080a05010f1403010b030f030310060203040518150a09060609050108040507090504030203070c0608041103010207150e0a170d140f07050a05040e 83
    0x820f020700030030380300341c4141202c038409031070f1003075400a9050300f550140071150b84864041e40c0d001c40140041b5881a650f100c0041d010119210788c07145420309044101c80741d07003605001440c1d1074025101407212860b000c010040c06070120b007400308882d040104030541d1000307000043d00408030000c00e513400d170148001300300b40b12030040011b600c0746000c02c010203041601d9001c100d80d20300490240d40d80040003400303800b000c0741502801301d510108014000c41891405008210303c00340703640c04400c4690300d409080c0001c50300210072801821080c07030a61007510703090b00c8095840c0b02c1803280040ca81e0341d610108050502c03c0c000c03600c909802aa400032040c0d9241c80c010491002103e05480340c00c2e09900302ca07007616040c003c90b690290031400d02810400b41c103184100429254a54203800c0c882c2a603001c0005032100c00c1c040300d080300045400e4a94910801c2d40042d503200303014044204030f00404011800d8074410045402039010b00e001074882843e00b406950b544100d030820050000d02c0f904000c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 432535350 1250 432534100 432534121
    0x3120c0f2f0a080306040c0f0c0209220b01060206060418110307030813030201090504020a021b060c0109150515060a03090c0b030405010902031b01140d020f0a0503010303020d02060609130203010b0405 88
    0x41c0202c174155820002c2e00e255080c2251120542070f02580060354048034100586005d4004503003015942c49540c0780d604814214840c0b011111038215050354010004102c078070b405200a650110068030248070230011180a40915000170100500f451408100c9102030b440c200040c00145911400e00e80c2d0326040b02807000804103851004900107a4000700109180c2008c0c001d13100d2013a425001403c2000144018296526189008a80100007402107101b035440900a444e80c01707004455400c902c45002141d101a114011700440c040f410142c2c130143d894460008648101e2211f00d000285240240342c0319002e00c0300795024680140c000700030b200034401c06500800c8101e00c00c43c12225a01300d0000107000002c842542a030102c4c900e50461070b181c6008000038910102071000040c80c6c50140c40d8094110b41040300070700d00040e070110051042580410140e001316009000800191900c80005034408200802c000301c41c207032509200302152001d412052800c54010f20520491070004003d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 432536600 1250 432535350 432535357
    0x180910060f0e0109021336020726040e07030f020706051611100207050c060406020a0b1f260706080a0605060903060103240903120c0f2f0a08 62
    0x44000b14420000003950415910859072184501a4592101e51400c900b50722541c0a1100e0740040c40e540094000e0440301031248102c07078107508003005840702c010b420541508500c00c0710141c000c811008414001034070a0007554105c0c0e0641a43c81055503550000701c011740403c88442d160503001044107170411807142c2069200d03040c48034040554819003507084440c0c8040d02802c01032034000d00c44032008892160010300085000340110303003651441c0d101140441d803081d07100a0050f0411030100d0100906040282d40104d160b00d640c5407403184400c580001400c9603c0750094440e050144100c50003070039061a203560464409441304991345440c0544407440c1103625001051405d000440e5901d4481300b612203036000507008004580c2196107040880c510141c030143c141c00100549100030702c6030302800304a28802c0daa80c0305c003503a0130b40f03032a81540c0132029103a003030214190300c018440d640b10070801158a00005804031102c010180741c03580e80c075800c0216006001e001c0d00c034424082240000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 432537850 1250 432536600 432536609
    0x60604021b1c1205060109230a030b040209060d030206280e0f011d0a0f140607031a010e09060d0303061a04081e030301060c08040b03090a030905090105180910060f 72
    0x840050340001d4070681c00325a0202d41076408120180401e0000c0001d0a400204550301880041d02c041204030005040203827a50007107941e0762200d000c1000314117100010070782101d4290b403100324201440d500030352520f4004010000c5060076503c000b189132924040c800e15034500b24810445c41c80c08180140d01d8551500c1c1c20002d0b0360078002000c2c10100109400d686500307648018001d02285650303460ba100000c58010b0b04c801c80400000c6107221414017003030b80a64816100002d0080d8444008403200300c4e03440105040c07001c14446401d84d512041601175000b18101c0344400111030f207140540013405150402480c1ea4150242e00341031000420082095520f004203c07400050546094030b800756100b00c5036955500103100401000e80141d50030348803544240c4030182441e03100c1a0016050b0021281c00e1250303803001c10030320103054000c2404000b03800c00744c50b44501c544c1048045055130841001800c8000181000a03c01704410b002200c07080c07070a68000c3c0141c40e1383d0641c81c0c031001032a005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 432539100 1250 432537850 432537857
    0xb0f0c090d080a02120306010903080f09031212060a0f14011215030506010803040b0a0f02010605030102120f0f0f1b0702041a090903030f01060c08120109020c0f070305060604021b1c 80
    0x1605c240c43c20400c801e4903c01c4005942e0b140a071800d545c2c58003d40d0b0018000000a01c2051204245981e014000e1080ba220b0011009442e1814082d0140140360094185401405c4c4020144940311300413074000196207145840210181c00c05004941081c00c048a00001340d1500180b040714000404414013100e002c0d208640840c0d881c2c070132140e10b03441140b251907540c031000c20140c2e1304640198a4080300c070381140000a08241d0312408a401c3ea400381081052407a00c540c104626030b401302200540203422103c0c0741301589050760000384110006040014100750b041d203100028650380c800c41308810350280051001074868101a540582d20b500800c1c45105444000340214038000152441403400014400300d603403070711400740c2d0300c030500320000d45108008000000c0c030003c07280704580c000d0088034001651200b845240906140405080c007005410040080010400000725580c01ca1400c840c01030743c60940510786040d2484440a80c07005009070550387d182a119503841203246181c985 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 432540350 1250 432539100 432539113
    0x7020d0b06130218040506031002031612090b06040f1d03041a0c150604091209090b03011a09061804140d1403070c0303020c0703050f07080105040b0f0c090d080a02 72
    0x74800b0007a070007100120080310704140880d01c4a881c10b50400d54100e580681a512207000c2c070a440d1003a42c0c070840300d902101d1580c59018404a0340804000001501400100710003022552000c49a1274041e080a00c01c0380c070344500500c00c8a0660141c2c00401c0a9503500c04d58224803008192240c0051140c0344e1041c3c4c20a4611131180c100d54102c85c0b80d01c01c45409072074607002015140449407006006203402135a05d04e126000514124201d444902003511051501d03450032114405030b0700d06a403441d0099041041e170000007500c10621220300d110407600b07001c0d00d0b40d4680110303010851824075001d0140080c400d110074414442001c840e44450f01d8241c4400c1300c1840401c1d1a049449005610310020400016012a2080b07204045070b510a18001d46001e0310070710340c940381070400e41013900c42c0e401a6019181d890700410201c0001d0000000901c114501a100c044c0c8002000380351800d0001c146002a80c011080300c216420580c00401c4c108000d18a4106040b0343c1d0040c0d110030004d80b0822 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 432541600 1250 432540350 432540379
    0x60504050306010603053c0a06080d0e0d060603030503041506031104020a0201090212150f090303060613030c0902071e021507020a0b0f031b0c030901110307020d0b06 73
    0x140119000e488014004003003a0b460960220014400244a806258100f800081c40300071007006921400c1c00039a509902014141d400c0703809220042d001c070140c680780110030007111030302240c0750407901000d0516482c64031604011407840c0c660000000c0525160040c04010183c000d8042d41c06540181c604d050010f6510721401c0440c0c156020140100030040d51500c041c0c03806d07030010585d1221a01c00458006403950103e51000c501000b100900d41244a40907268800d9280407030344450161030190b00390500951079030b00da01c400b900880c0210800035008000f018100e8802009503403000e1004421036944100800941220008449200f1006279280128100000b0502c8054004040c02c404000381c809030b13007403a4020a404c0760400d400748030005039080440d019248191010944a96034a0007040c4104d401d800b030600484040001c1c00750031106400003050f04d420310400e0070008030701403050030442d186018800001350f004100c0c410000c100301000207600d000c4d2500351200403046154 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 432542850 1250 432541600 432541607
    0x8070603180b0622021b06011202063402012006070518030303010806220f2301021801080601020a0308060f0a0317030f0615070b0916080a0c06 63
    0x1c81d410596501d07054400c01c000301c0e0305407480c0c81e00000000c242c40807803c103400700384410805040d5800e0766a980440c200d051040d0380102c840743d00443e10040c00e0150304004076950581d0341590003078001c260226941d90380464144144907910403540b50b4000f04035803282da100c440400100200d001404d1302c440d43c0d17000018140010302810b00940a40707070390794038542c0480726500280850303c0280c840f1001ca42454400740000d5000e0010311001e005035240402160445d5600c0300138944401e00010600e0b00800c0328034480c50705981c1e01c00a1222140f03000e180d035105e064820008052a5480000c0b05a1107948032a4408a1000280c0350031209a450f04010390f102d1030b003541e010300400d030610000340c1245003a41e403a1104410042072050401e03121313156841d6188403e218001c1044000040c084900c01402d101640407002700e5540004080700c0c01c03a54031a00520b80700410700e44005000c10300420082c00a800d4440440302c04804035540d603403401d940d035911094140d800100340b20001c10194031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 432544100 1250 432542850 432542861
    0x51c020c0402031603090615060512060f03030d020306030102070209130311030a2f0610080115030f0b130b0727030f0f060605150a020f0c03101a0303030a0608070603 73
    0x2010301c2c510400151388081900601320020088172000c0c1e9070200303500703134030700b04554400548810358807a44c40b81c821344400384050714040c140700d118a100345600402c0b582c0000c115020440e00b58801768994a4040209002e40956074009610003401000c01903548009212105800d0095a0303413564480b0b20128a0340306e1103581e40748800a000d241c1c03044e02c0803c1c00410082c1c0e040e00324550408105411041c80d092540c00d4070355a00c40010018200308940090250108528444228400e4a840d660300c8448ca1a030110001b02580e02540000e0200001c03150843e81ca44d07006403032126240380c500e5000349007030b4501da103090343c8114200340c0e51a070020701600c480039030758010161096150952940400c0c429984003c40b0328640b00d02011034641c030b070140c240d00c0e211015120161101c00c00700f0f004c0d08000c0c020002c176149a1000d680c4030724940e400108072210020004000030038030710310b00e8401085403030308030304580500c40002031081200703640c2d0010342140c820006a50866443d004d08805964 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 432545350 1250 432544100 432544111
    0x3020c061e010522020f190306050906041d100213060206010308030601050c071e0f091a04050a110705101404080a1b051e070902070825051c020c040203 67
    0x1d07000001485641070041d010100b507206442040f1020a00c107008206a900050b0384140103040814102060782c0e403140d80f103030400e5550400344130030303814030005c0b400c880c00c0140450321603034030f46021181241142c41e40240e03859003030080d221600503003c200c1c4040e43c803000200e448000510400141d043c408a5654180c84e0300c441c03441c0c60354650000454140d0040841781d626030050f031100007941d407282c0c035644807415001c01030342e04010b01d05510000e41c46083e0784800701031400c08111096074591030207080a014412a00054035480b0044041c00a0401d2804e0380781c50031000901d107051000005203900303280d200d01707400d0201d01510780f61070313001c500d050381c0040520506201d2310440501541d4452142031100c2d0b1491440500342d102c144c0f8201789480240c1c08260288032502070510148010400ba10648809618202c52a074890381c0a21441606240e42842000180784a04c07906c110710000b00e070800104d03014a54401407182440f4850b401d004003600c00c4100b4034210741032038000e6038402d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 432546600 1250 432545350 432545401
    0x501090b0115081303031d0703020102121606151214060a090f030807180b0304050f0f07170102120c0a030b090c03040f03020708070605041703160318031203020c06 72
    0x60325140850384403400c04c403d08030140343d101d003035018000240c3c1c1140802c1540003402840c500346580006400d0828000c00a2800d00c0200400c40c82c21414000d903041080d4000c40028041c481b820001740d4940803600f180400a0785141d2141c10311001075070000e0400504010b4806030b480e0004c10000b01e0b800c02c0c000600c4540b145000601007030194070503e5010020341403582c845041c50501e00c0680c01c0d640c22030488400d002c4240014084100301e81154203072080c000300b020020340c40d007995460086d4420303a002d0f04d2110b8103800e00300d00c1c29015a50b15030281035505015090202440502c1d800035089580003a28155111902d86011900d407400350030400c20240c55900ca0362610864480604000d40035440380d0b0000083e1100b04010f0440288515074800303450741d0502d840d100404078202961101c3d40e000340041c016050b45102e0201045605041c496451030314200c40080c003250a61010b4440c01d10603101445490b00f50b001040500f000d030040e41c070725544600c1d104010380300c4204402c110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 432547850 1250 432546600 432546617
    0x612060e040c180f060303050304030e030c061605010612080901140304200103140903040611060105060d0e210307030507170402090618041a0117061308090405040501090b0115 77
    0x2c443e4201d2591404100700b40201d0842035000050082c0d40c401e5100700c001820000810040c1a481303480300c840395100320040c004824150001034801d000d00d461210311855100414004c00c042540090005c1c00100780080070003c40381060b00341074001250207808552054000949003803010212031040c2e82c00f1014000315206030031803030311609581e40d0301818190b482d001e4520206a007000307540308051401c0295543c9040400c01000c20045007803041b9244d0049005005036554501500c190070368050000418501510001b841e0000071400c4585070181401d504600c0402900110f1203502d00e40c506100540b01d00c0c0c07048418809581c6a0744054048a01103001480c103a10002e40200780102090001d94400e82602009102500c0032a000c96208040c2801e580c100400c140c01841400c0c04030a502803099a0f07a40c540500030426039007086800b0303842d03007003003010f02c1a9007003560060420800341c5000e1030018002c00303500c14142c981c502c011000042c1d24104130303103503100d2008554a01c2e40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 432549100 1250 432547850 432547859
    0x60e0106080408180d260903190204151203030b120d1211040b030411090f0f040503040b040311030c1e04020d0b042309010b0109030b090f0303010612060e040c 70
    0x190b00a99030283c00300c0180941c40c20241c0c0e035a405140c09a015040d40c3d9610558049011207004001d07940c5e5144c4042404482d031f0595010031201d50700c0281e202140e09445041c4002801450141b190403e018840d68003c158044003450072041584603440c01c200503000d9100700b00403030340c10b0705003182d10303921460345500c8491150015941d909251140490508050600c0207880d401542001d54403140100400c01480b41000039440b40c450241c0341c90810382000b41c0c0442c803c030701c020803c40c80015075002007400c0040c1041154028090b400f0120340300c50b120f00d040400c5840ca0309003248240b158070f0781c1000724505400e09454040846a080034008041001c0c4806900004d0071606400d42e9408080e4460301d450040118030b070300114404140c80b070400c8141848440140c102c403510303072400075a845075980180340b44007525001000505259540d000c0c040c5401c00140d00307005075010100000840c9034100403103d1442400c0c88007403140c10749444218491900480780a00804400c680c20070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 432550350 1250 432549100 432549113
    0x507080a0c1511010501082b05070f030c051f0b15221a07021014040306110c0703060b030f0303041a09100204030507050405010503010c080103060515040905060a060e01060804 77
    0x1030740c0849428402030340000c3c4180e450840e90240d0000402c1c0d000454901c480800300d0000600700d402800d401400b0900c1098000d0041c0141c82c00280101500c0d41d14206040c0141a05014282c2c0b05048070b034490034140030a0300078000603c5130510387e420694164818900b0340400d072010003403454418200782648401d004071031a00d000542c66400000d00101d0b040402c54101284040e036010f84540e81d40c0c6038414030082e40c80c00038105040041094120159180010031501200d8120340c2c0400d95100cac1c0d0086e03070505c0c81003101d04401c91140300000010880b070354002e0350301594101d0030f890310140c481c44101e4803488101c07401044180c05801030406010080b6400e07401008140c200c400d1215441c08a5007280c1c0305800030745e6523501c88582000189803900455001d800b017580248450592890003405042c0103000c000e0005403079a0024404580c849048510007400034030502845144c2d040c03c40c1c82d00f40644643c03420760b0910401064440b0b1a15550b4100d80050f6200842540c6a80311032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 432551600 1250 432550350 432550379
    0xb07062c0d080a0b12030705120711041e051603060b28090b07030e0306010b160f0204110d2004050904030e0a090501080102030a0b0a0605040317040503030a020a0507080a0c 76
    0x3946a9038580301049030781c5a800410102c541480e0055a1f250f41d1401d200345400108445074523240005c202e5030740000e000314198280044180c070007180900c5183d01d400300384080003000844452411042080010458130304d048904a0b90318100700d800d1b01c0300c180b072130f8a01c5460420701002e40803c010341d800c0102c9100e4003400300c0240c9004a031880d1110030880144d4002101a400515845032100d00d45c502801054010009942c010b40307007400c2d10038005214241d090001d0083c40582c0040300c195100d0b608084c14034140f20150707982d12617110b0b107480000d0a0300441a5041d02c459628070b1001c0329400221401d0300d8009141c0032103580d6a507421116407103110003181e0440507488000540303031024050a8064400d5000168480c68504020000ca48244005a12410503113404100140e00801280c003136035041074110080d60010040b80b1081d20a50b80107a415200000d00740c603900d070340891482a00b40c8030300281d40c1055921001c40380e455601d000003500510700c884c000c1204003804811f1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 432552850 1250 432551600 432551611
    0xc0604140301020f0c030a03060503060f150a031e0501230c180a03111009060f0f05041517090c0a05040b0f03120c2e02070305040b07062c0d08 63
    0x1501e4050302005050854008060a05e1158008103002c5c02032074141c0250000b51609400904c45481c0044048042080c090700b4000300314200981d04145444641800b8042e40e00280510709180f00c0dc040760480000071401aa80d552070304008000c04034140640c01481d54a04220fa265920f0345440600a0361140700003d0035180100b500d5406911412942c40c011401411034100d003110a60600240208046203078007080312041c3d0070300401d0380218060760014803078984607098a00809060f51184202d03000009110850550107403182d500011400c42a0060b94600e170703007600e41d000415920510340344515130100c00e030402448075090640c841503030501e0081107075060140380310100c0d003401d00341000c810a54100080c4019a44010010142c07021202c40d910817030a0133942c40008150201031205425036000500c12080c91300c12025280034103104200280c3d03803100da240140051800d00700d0444400d07880c034100300104c070400c1e20000b10002d904000d81100c88a01100b1121a00024038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 432553956 1106 432552850 432552853
    0x2070204050c09092d0a0c11160e0a14070305182a0424051903020d111f0e040605030606031005250e0f030c06041403 52
    0x203051741e001101d2a4550b03980f1003000310410140c000b5101c1a0310000d8103d0520514500c5a8401d4080c1243c03900c4a40c114540402440e454413100413452000d212034040030403102d4181e40c0d80300c0c4d001c200f9040c002032015030550300e103003044419108800002d07580e0741004191010241414803c0399440e00510900c1002c1d2800003000c552515010102d080c0e11a440d0710030b813125008000c00c412802050209010030190124542e1124825030303105c3d0032114881e04010b04001c0340c0344103032600500040c1030581c1c1a215444100010381c1480d400041c1c1102485142d00031140204122840e5650404903006c14010081692551740140e0300c80e8001d00c0c1404595600050b21288002d010200440c00e69110740852044003c498070051240c4080b05003003220713651080c00c40c3c0c82c200702211044400190f40051551300c0096150207030f00088200b209108140350420030f030310401380080 = true := by decide +kernel

theorem cover : BRFrame.Cov 432374100 432553956 := by
  have h0 := BRFrame.cov_init 432374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 432374100 ≤ n) (h2 : n < 432553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
