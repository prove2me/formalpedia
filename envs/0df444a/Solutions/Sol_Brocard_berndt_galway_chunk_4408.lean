-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4408
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:31:22.778044+00:00
-- url     : https://prove2.me/submissions/12b7580f-44db-4b02-9f6f-cd96d353b367

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 792625899 ≤ n < 792805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 792627149 1250 792625899 792625903
    0x11010806040905100902061303050d0e1c1211030f030613060f0303031503120201020901022a04230709060f0c0b061201110f121b0a0f02010615050408 66
    0x10380548126030600000c0c0b496100d160f15610f1961401c01c01540b60581e0b802035480b0340045a10080d0702d003040d1414241d0b40c0c1410740e290f40905140000142120041c50401e10380300c000c1c0b614060300355505982004042d5248010081000e400c1003c2c080b4048005801500a202506106200c40141a81d82c90250704010b034810303440000782280703450035205100e603c21f40080803081d82c0d4181000150b403a4402c85c030085015003a07100809840241c10906102a41034010f401040303c2038084651800d080544540c1003103644400007250b00011080407600d2605402c40b0300e1008444627005c10101610420150003200ac0312240d0124901070340c00c008a80c0d00c81c8040e403140c00c840c504140030b0240c903500c5c0d03101d03404090660b9114001c030301c0407034003403540a5024000040030041c0f1656940d83d40051626180c02c210088124140c0600001d42c102000d07409500e41e03031070b082107203610b0302a10038400d5500103034622690045668a08020902030729007110042c01004680f5500e88076440d18030114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 792628399 1250 792627149 792627151
    0xf01150614071a04030c0f08090909070b0a1809060b041a0f0403030309080d09060b030f0a05060402060331200a0905060f0d0609030206070804080a140d09110108 71
    0x4001c0e031010407090000c9402220fa4074030040307941a1841d501d0b200c6081c01c4035010a14000a4042030714040c0395420044500c1c0106060201070b075908256070750761400d09448807401c0c0700d0710f04045c00410031180300c01e100d9440c0d42030b0104120f0101d12050f45071100070007110b0701c540120070301c108009014412000c01201004a00102d10308413850302000d00b81007401c900a62000505060f2a00710301c40c1040301003000d491942c28011340421404055052042c064402c07400443c2c024010389040c040340b05800314000355030980041c014403036134840f07600340201e0344d100400140703240d0b5001900721010079104400e07500c4285001c1401240c42c2d03035400c000030704501d0380d01c54141803c2d02c480d030303402c282d2555442281103c1c5520800289982d84601060b5003c0249200543c01070448403a03404000c100e9200100c0140241c0c03c64030035954112041d500108261009000c40c64240602c038141489440d0088000c43c4869040f1300307100b40443c000c01a40d02090301103c007945403400b01005964000402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 792629649 1250 792628399 792628427
    0x105011b030c03080709030602031f150203121008030315030c041806090303110f0d060603092406030602030c03040212120d0b0f180709060e150a020f011506 69
    0x9500c0410903590150405941c6a402010320944400066595003e040700d40020b503081700c0c055640e8603081c400e4035200da0507448040340000b10b0400120f4a10b0703848100c401038000790740041d4908202480503c014030300c0240b410400c0000c40e4008100e660003807000d1801204001e070550720903000b442c205801c1900e4452424007480c900340c01001d03503078032050000c244581c002000240007425801d04801401d107440803461810000503803034418020502c024187c003a50b00c02d007003001c203403540300840a88490f00340c007030005410022003445001d02001400b2070500740e00b20000300c0c1aa02c2c3d0300c200c2660411160590300c0140031003000309509050404039100040c050107410110f01c20202c025440c0a0303020300c030305002d56649690034541ca07180364540410b6001811200400e100c080e82c52056031040b1120400507101143c00580b1728010f002e031089121004010f00d581c81001c4040551503000f403100b0b00c0c118402c000c0031182e000028807600001022003411b4176911420702002400e1060000c0130 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 792630899 1250 792629649 792629687
    0xc26030708040302010806040b03061f0e010b0405130b030a03080a0506014e051906140409020301021b030901090806040804061115010806010e060d030905040f020f12010501 76
    0x5003400050403902200e06030303513090800050b00d49079440803a0040050005c40e80e0140305071002d215428421030348980c080498800244850b0f5103551802d502e4510a100d44400c100040c007090109180c440c8204450114000c80018400ca00d40c0010385090301080e401c0c1c010400160038451b0328540742c010160301c0002802c101400aa41c03000540d90b0150302042080c0c9102c0500d02c541c221001e1050000150810354142c02d0340c200014240402480141e40182200304110952089990f880c007840040b1020307150821400115003040c4402b8080708041282c5c555400c101031442e413201e1103c64000310074050000c1d81c44440c04000074000012641110f96560311150410001a07002011607041d03c6051400d144048511b902c0c107460086e10036142c2581d642c00030000f0464000c0040c800341202d21481e010781081d10740b0010300640d062181d2000d400150018014082030805030040b030090311034840c0051800d1403900c0d0303001041e0804441d50b4003d40100004000a6900130a8224110070f41381c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 792632149 1250 792630899 792630907
    0xe0105180412210e06100e0f0c031504020d0f0c0c0c030809030f0f0f06061f0305060a120602180108010b12060d0821070203030702150606070c2603 65
    0x50b1980080740c81040081040303180760603e220484115800030348a40c54140c14441c0031a55030b9125118003080b0b0740e804401c044100002031720064640854080c090040300201d0717544920048170b07210b52006081c1d445074070b40302e03281d404c45031140d20040c003807a20321f604006008400d001c1d45000b03480003c445141000710304007642000c13407071003000d1000f209e41c07240e042c9a40380382c40404070b401c1c40c5003080400034a00441d24601c100c0c07023010807042840b10050341030381d445a13503c3e01006002c155503c5403030201124052a068070034041e81c0a0354225600400c0d0013096a80c030740c0c1d100c200c0c0c58400800c840759900842c10079445120360540011038442403d050a85604200c100003031801140300ca065021511400304410384c40b40c00500b44010b42260030715a442e41e1050101004201652122200b901200002580d051000c070689000e28841d0340035089014070540c0b600d544881c003030105a80034404010000000d0000046400101030b4680e101d40081000d000040e52903c1c01c1d080b80b10bc54000304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 792633399 1250 792632149 792632153
    0x6040227150d02150703180810020706090c06080a0c03140a020d09080a030603050610050114030c13030b060f010c031227030e1309051903030b030d080a0e011401030f031403010e01051804 82
    0xc0340d90807034278018840c0140c5482550034030002400008402414000b410500860456030200b08240b0400d44501e01b4000c80e020000f045040300c84003d58000416114408610305203a80e800811116003014004524606140c07200e0300241d100522020110b5034071041041005001c0c810030341e02038070515010690354a008006003000b84d07002440c020070680000040c41e080d000b07100342d66803020141e401441807078a0780741000c2c60b210180c0700603106060015001d256076104200e20070002d5815607503c02c0c1c02a4141c400c8000c1c00f040d50346683d190954500745c0c4141509044004d00e89400780d6208183c00031a035041c8001e03021090102c1e0070b020308012000c00480c0780000d04814900d5a8117030154290581e0604800401c400000503615002d41c18111070066404486940101041c0d03d042200c1c041585405003280c0400070780142c6208034800410210350459030805000340642040200107005848002c2c00f54002d8008103540c060180060080381000703602c01c004d0034426024101c0c80d081c29 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 792634649 1250 792633399 792633403
    0x5010c0839073f0303140a1e0b040905010f0b010306060c0302030f031005100206040b070504080a0f0812010e01030516060e102006040227150d021507031808 69
    0x40c5089000c80940f02940802d00301400201c01164000341000030071038900c0d803030020060240c07808840258070107040840c150120900c6240070200d0f016041e03540180030f0132024805003201045036680320341d0700c604003c0414001e0040d404034500c42d03800012084411000034044500a81000040002c4030310001d00094001040303d0806100c21505030322030740c0b02103500c0003844940d0080c1381c0001294402140c540d80004510340502c0c800c10008035155255041107505000b1440380c12070a500c0365440802082c400342488580c64010b4142518040281e44601c00d920700070b910403140022031100400500609100c4041c88550b29806094107a151910003080401c100100b644204050b5581307001042c028129003e40e03d41c0f6485582a21004d4a083c64441d4803c8905078060100201c000c1d00002c03d2943e012101a0a60700c0c2d26140d403105410a50201804016190014241541000540d0380d5018031406007200c0c50516035503c440b450b0042648101081841e00c12081c40300910441e000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 792635899 1250 792634649 792634679
    0x110f030403030e12030c19060605060c030c01060b0a02070e040609020a030b010f2304150503120a093003050f0f0712020601140d170c011b08040c05010c083907 70
    0x6a8801c0941d07e00b60b60506000070700d815803140f644100002a880c3d214030012006d0300c0707818a03182c02008071917030f10489207509201c1c0f81e25940060308980300500c00d001c5040d140c070350080d000b0b00c0d0010390000c0303d9003c155407410320b8106840d4102e045004100c1c16001c241094060407103903941d4207801000410140c1007a0030000014403494031b41e501c002880c0c0205403c03c006160080844d0320582014185050580c80301914200152a04d140803e40700c0000c0811450b03510900c03a4029480710a4008032002c400d9000210304010b4100300c0e40b21085180d00241110781481f50a00d5a24200b502d061110891007004a00644d000f907001007040c680c024012000c40389003610107003024021803500e40c0d5580f6052401080100001c81c202400110541c42050310b000d48807a120a11012001d068400d0f42003140d008044d0040038209009551088031114000c910603542c1c18105180c201040c10410364142e4807000740d03c03115164800700090442c1009040c640e10000e01811810600c1001c20290 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 792637149 1250 792635899 792635923
    0x1b020405091005070e030c01050c0304210f0c0612140c03091204080601050108090f06010b09040e011e05161403040c120b09100c020607110f030403030e12030c 70
    0x9655000a15628010301101940702c0b01c2c00c90810592501180140400b0651015280a803080d418401040d5003d407080f03441c01c03c4460003c41c101494400b0407214107980c078524400c1d600030780039608005400d041d81104c08901c2214036600306410a0002000441a401410405420042202d4102c0460003c00c1d801403540c0703128079034030742d0344001d490f14040c9104c0850120213800180000c40034400b0541c103040e40c0090340c880f685c50704d8040c90700da6200342e04803085c04141c014900401c1001c4000c4003c0c013017000050b10110341502c8101c856400c4603404095614443c7c050039800e088001c0394440e03540c0c01058003a8a4042301d885400050058220328402054600300001003070502910305c0e4440c008040b0446c0001d44120589001c0c07030015401c1d0b035408103502c5180d120780c018240500500d06401001c0d4014200703503962000803a11040710030362602c2c6a0250160401a4110603c020300c0950300035128074a80c030825000744005002c03c42421202900f080c803c00c0610200072442c016003c2d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 792638399 1250 792637149 792637151
    0xc031803080615041214010b181b07060e060601030c0504060507140307030c1502040515031e0703060812090307030b15030307030c03020f0601050f12071806151b0204 73
    0x80c0da00008030308840703c20080b81d0000b400104002810451400340c41580c284a071076480100300c8104011402d07180d07180d5016501404585c00102c02c98003580c1e20640c070849042d80e11070306d4112425500c0c0a40c0c0308000560b0207684031101c2c00c0c180901042000d4002070f0138601080350303407503591000b0510f0145028070020003400052035014051030b158011070b84807620b001d81e0b1307603090781c1d14000d882d4090891040340d01280d003480c0300f05001c1241c4251801c555001d405071300510b0041112841e40d50000340307109800c440d154040d480c2014140203240c031400702502c1c001600340c2803919a03031405140290781ca60f480f1003001400c03010348011814a0032294040c2003061580c40d402e600c40c1c0c0410f034199140341c042c44007181900c10706900140b010542802502581e00890380c2c1c0328116202c05090250355009401180b026425042603400c10404042c44010741d0700854a410104030120003602143d5060303522190b0034000c2c191458000040c0303d00504107a11010750b85134814213040c0e20010082e00c52 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 792639649 1250 792638399 792638401
    0x2802070506250c12020306132402120a1a09160503040c03050a08031503033105030616080c030f0406091a0a0f0b04020406021005100b1c0c03180308 65
    0x40c104003000c12080c0390f44050903402c12038072480d840b1451001404160320a12400012174000b0204900317400c95250403003511003840107028110055070010745103818a255082040280c9150004880b600034603d02030040784410062070103a00c040750031841244145070320020302c0b948904201d0716002c1551340313003420364480d6110b00785400031281950018065000340c100d400100400440254410941c0200800c480641e2000345650b03070040340700d18003e8a00f05680031500b0704010b8100409560483c11110041c3d4440c404030b4245071040c4d40700104421000302d12000160001e4003a42d20203041d020090851034041c1090525440103040604010345d00d02c80708052001d101c1c0c0c180c201d4640c035492142c40741090f00a40700209008100c0c0040c4c54a010030f02314651505000b200e0480b403c56008140300c8054601b003000400c8041c0c08601209195000010440f4440002c0c040400301ca5403282c680c0e40c040c400100c1603a860100010400d480c20340200c00c500129040c2c0ca2000760946400202d0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 792640899 1250 792639649 792639697
    0xb0a03020907200303100b0432040c120b0603060d080c0106150c020f060f2b060e040c0f0501080115020f0106140a1a09091306022802070506 62
    0xa1004000e5100610031043c0a80810000c002000350301411041001c084004e0380c414801c43d80b40100e02910245030660001101c040e42c420801003080001880407c40c903100d40b5000500b00c4d40741c1c1240703001103040050414507440880c824030361411004e9a40625516194000400184000c10000d20a8802003502d12505800354814805880d203c0b01035100351507a2080941460031042e000c0740301d14117205817035010b803c1c0007080e1200700c0100360f4a01e081000c04010003582e24485224009812500c0401c00e8601e100340c0500390080c14a03040114107410a0305201c40310210300c0d0805c00e912580902c0412183e44e2048206044540c0400640f94408141d1812070900c111404216190740c28180c0c081510040300030031604224003140c00769030481d82e50b0742042d035041041c6003000181005200b4000c56040442645a0206c0f80c05c001d804209100e540d007404070381107c5074070703801404917281d10503050001d500f0400300980c007400101101c510713100014929120f4121140503d0141c0071182da0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 792642149 1250 792640899 792640907
    0x130501090b0a0608060709140d06090804030c0e011406040902180d0c08010e010b3a0b0a0b030c030a02010e0103060503030f03100e011229041a01090b0a03020907 71
    0x802250700c0208201c95041110315074000d01400e0080400e00c0c00f0f80000725084600500410302100c2a03101e2004100400348100045c4103950803058030180d480c0c0340e01e900020007141c001c00103944144102d51442c0c2c105481e200ca16041600901c1c000c00d20b00350104040e5036440262400c40361949000f40e915000020100d07280001c0b07030f41c2c103a0440760020151003003101c00c2010209444101000708a5040740410031801d9603083d8002e241c000440039060055107844024200c1c801840100141c04030341d5240700c164945c0c0b02031500b540e0303000c024400e000c1c9203a898000e4a0142d00110014201e00d0b20ba500001c2c0c407083c03a810000c0c188030005e0301c3d64002d41d0090b0420303c02824010142d94a0f1254040058503990089605008181409401090f8070340304040090603a1440c100d8042c5907059982ca4601d404000c48551582080f038800303403420194845681482988a46001c4280345801141c180e952001a007200c500302d03003441d6401180b5161900c04100f00e030b170111514600ca881e8014151303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 792643399 1250 792642149 792642161
    0x60f0601110a05100507032c0f03030108010b13050103030203090f0418030e100206010305060a092d11150d1505030f250b0301150207090617071d130501 67
    0x100c1a40a0801e040d024020040384c014103442e07852109109541d541d050440c03c0700d0b5007100d00c0000202196041d00d8022400b400a08881c544000300e50001d03602050092464000740d01801041c3c1d110700038401e02d824a80174413100d46031010700901c001c5d419035402a44034065228094002c003450b14101900743d03142d42050200b1a0b100840119a042c80d0034000e00100210959900620000401014440c40007404904aa420030041d08440c0c80301240707840500740740c410035516403032100c1018051240a03200106411249a1858403c901d82e2824120010014200c50b02c035806101a803003030729401104031845946c14580018054020913240c9500b8180c0e80c22040d010700c04c01c00c20500d402800160000b42840c00c81e11098000c5079500c201d84008401e0248000400061004100090340800c400d003500320f81d40162940701e03444910b0740044503110b61284d40d403915040500d440c040c40a02140e409010742030745001076004031944103042c03040c02070107440940c002c40b81a101409803c3d8864 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 792644649 1250 792643399 792643427
    0x10020310060906261b2205030c1804060f0606050309011d03030c0f0705070e04170301060c020f0f100810170d0e190905070807021c140708030109050a0b12060f0601 72
    0x50741d100c1c8000031b074030708400845c003021403000980a41c0c080303218034000802c0881e401c402040007117004d603e035558041c0c98501600441d4010744a01400d807080600c1d004e158003034620f40d40d966445e481d0204503182580c2822840241450a144c2a4a121000881142d03480303110050f40664034001448206550b1144001c05803071806448000310341c14404402442c0034500540c50220505081da12588a52000380b140e440891003440c00c04005080c508410030042c940108425000780c4a1030101d5552800500302a0000301a00c0070415014084100c0f03e01600c02000180405541c081e11150344102e0a241d0308203010199041c3d00c00e90b640c4603601010b802410401114490b91105100040e2105840c0b5102060143c0000b030402071002810f80300c007807d01150218842902101031300c40342010302c80d41c0700480702044100040303180100158020f02c281c040002d61071810620000803a0700340703084c3e1885041a035a08190311500040d80341d030132000118440d4103980350040182c85c127203054282 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 792645899 1250 792644649 792644701
    0x120e0607060509010203090705030d090509060d08070501320402060706061511070b0a050d050705090613050301060e13111c0312050703050915091002031006090626 72
    0x800c034203c6819005103014080d05070803104011344171000c0646030b06451010b400001c2140504100a19124600302c2d0032880c0038090b003500034030710344454126030f200d050b080e2400ea454495442c0c3c500610084102501103181100d41e0000b8905020441c3d0f40010300040d1050350301090303840601072650b0003013005040d10080d5004d00c045400000c0d2592201e14080c0c000c500461000080103400c4208440785c0c0042c55449a1910264203d5071004003005800d04082000031b1004407c240c881b10002d2410060600f030030307040c20745010308260a43d00c4542000010a031160280300625803d440061745003a80301788404500308090001c03612120407005402c81c5e440c14404800c0038107402981a41803025071032406c2c4803950302c0c0070040d01510010b5881e91101d0f072090340c8400310040340d007054940142d0b01105030340c2d1030310921004070107a801c2a5a041d010489840040103515000756880d801002c003824405520620700f94441d503d41403034400046070a5400000440d40c00c443c0703401c5410140748480e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 792647149 1250 792645899 792645901
    0xa05040b12070815010f21060b0603010b091f1b030e0d06270c090c05040308040b03100e0405030a0f120c090801152313060305031213120e06070605 65
    0x7080e9980c510b00013880c2c6400560060003c01c0c180c0551107914160307007a8840d101d90f0007e5400240380e0a40100b02c0c10344a0581d10064510f1503640e81c402103000b805403000e000d80700d000310741c01c0000c1e60700b00c008441c42116100a06d8500642c00149580701002e480340b0b04007201540e41402d0360385624441406030300c81d082003905004c2124a5214402409448984500c07040c0c40d80200c28800880d1000503240c001c01040c100242c030900e8100d1140824185012404d080d45ca9a40400d240c120390810f92405c00040300308019850210200c000a0460708402e416504140d29659103d2040441032070030400c41c0d0301c210010900892a2051040d0004e600304054100400010022242401401d200d54245060142c41d644920580b0064801c04070201e03807580000410074121a00b104803094000030b40700c2036080d04121a00c42c840041d402903014580d01d032550f80900054480c02070030020a100805e000202080300112074031003410403820110020020300001400501800d18010300141c04e0070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 792648399 1250 792647149 792647159
    0x70c06080613061e0501020f2a06040f050102120a1d0a0b070506091e1005060d050a03030c0315030b040201110c0d06090215120c0906071202010212010e060a05040b1207 74
    0x98200b145013403880c1d84503603200f625207004980390f001c078099500320340d84100260020b40c1405544550440480e11940c1c5003a0669008103425401c154805e45049000f44400c0000307507018032914241e038810642c030314900208044042c02080f07001c01c81807140c0108102002503900d90b082041c0282c0f040400854030f8840501d021503449404550000341c43c0113003441d129141e41c0903426598032140c040041c2072600b1a131003200008003030007000507038440a40b42004c40810014402c3c5c610080c0a40c0e030100d01040a40c401509407401c100042000602101040011441c5014056009a4246810072a4449110580d0b1601d046420f400d0380c07205a841140c0c08024160344404400b500c00d644801005608404203100781c044c01801044108114000402d01c002000013884e0043c0010902410132059440c5c0e420034803956414880941e50010300101403c24002590f4010841c0600c0507e56240c6500821086542ea10580340030b142c85907011755055580c0080c040513200d10b0400c840d410782d41c074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 792649649 1250 792648399 792648419
    0xd110f090a0902101b11030a0c080714150405010305090c061b1509030a0f11060c0a030b120d03150b03040c06080711150a020715020a1103070c0608061306 68
    0x400d0080b48145842e89180e0300150207102c981a261981d05d00710802c1014a4840c1c01c4180130b00e04002e0350600a820840c0f0004032280c0030703a03002e04030b03010080079040c0c202111200b00d10710701001544100050a0300c0c08a004c108003c4070180c802c00c0c40c000c202a128490154034060740c81440b150f00c42804183e00003c058840d9040e01d014900f0001c8a0012112208010311500300341d1301038160350400c0005218850049405510150052814010a00c48802114248030041d102480350885c002050b9403c80d5050080000c00c0340229500b40a107003881000941d00c03a041e00501e011b047c0c50342047c005800707810031410001d10890100503500d281038500320b1002d10450003484c0c041a504404100c4140c03043d000e414600c80740310010841c601a18254106580c002094800303c0c42d020451f401c0018a00942d2040e9004d03100000b503118149010050000d00c030901e03000d04154001d02071a00441c8500c01003000b20f5459040c5040c003a10b030f0030080750501451f080e030880802c0c24003100203003806003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 792650899 1250 792649649 792649661
    0xe010903050c1005060d11120f010b0f0910231905030d09080a0f0f080c01140a0e0309150f07030507030905100f080921091503060d110f090a 62
    0x500001d448442000d4100f1030100e03242a40e0340d64001074004032a00006400d24401411210010102c039002c07030340c4003c90762520b800c0c62800101d0381d440c0d0400600d5401c1c4141c00c03800028048039001201d1404149608211180d0301c11088000c841d01d4494482e601041e07036100010401502c10504009020031191442d8054031985000380308254060314228840d00e000c1c000c0d2295080074040c085d031181c40d110b40c03c5180802c241d680c0450094544000b80d5101c0040c82910501c40000c103103602004914004404024038244a060402c60003800c0100d010007110300000c400c0b40c280b07940c81c0c00c801c03030601ca50017410a000310103003001402c3c0c814980c0013000381400603c00c0c0d0b0703008071040d191801e1020741082d4400c04070120700031800064000c0d01441a40b035000c0815011641806103a94221201d140348040d1003040700000501c010303180c1840203404400ba440031140e2803a6040100c041840460500d5000d04440c80343e51028a841d91207854019102d10020811945070602c81d4000d0001d104d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 792652149 1250 792650899 792650917
    0x30305010311040504030219030525020306010b0307020c01080c0d0507090810020406090e061311120a0c080609040c0806010e0711010c05030c0708070c080309010801060e090a0f0e01090305 83
    0x140400a01c802d4038041c040c0c5072045906a000e001d0000d0070805680d06a07294a06c02c40034070000780f100f01e11078071010001015500150303030f121401c040746005160400c00c040c4c0004c03034000c004004000446800040c003030241002841c242e4915a02c0040d0615240141880c404500c0e007800240400b290b8480300c1070040e2880002901c0080689041035001c03840356204403404550051810044091092205540000d0282040f0108503010360b401041315809104094101130100d8559890078440d801c4540c045035014040000301080131f005400c819004050912a0000c040020100014141403400a01841003150b8903541c550b6510661848111480c50014855818203004040140190050f03502e0170303242c80389035846201e011100e0754005042a01c0f60310042100400241600c0ca1001c028110b0310055030325580140001001140c069201c80d0400030365150b40c00f000d07034484107044c2d0482e44030600040ca040e1100c01e540e000d03284552101035a94030b001d0a503824150440c0c01444011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 792653399 1250 792652149 792652163
    0xc0703050c0102071a01270507020a020d080301060f030b0a420f0f0e0909030f070c030c1d010e04030306121a01090e0601090f110d20070206070b1b070303050103 71
    0xa81c0b580b0050f60910542c040b01f01140c0e030b008104005d1f041807030740100c1c0c000d8040d2043c3d500390040ca40100304000807065040f604860000300411039507600065000060055103814020094068005800700e030b018015034140700307645981101c81c9070318544107915421045075000c00c402d440c1c031344900c0070300724200328080422031180100d0360b82032240b240700c548441c03103072110409040d0410a024010700c0081c05d1170020f2100704414690661804040c10b0708a114100000e403850852400500024043e48892000d07001c1c50000806c010015038064195451142004225519800d0442c040c14140d0f0158980034004c096640c14801c840141441c0b0040d4050101500e99035112800d08680c0c0301c030012907440d00800010300070100c0503000b04220203502a030100300c8240541807100c26901684401403103540c5e0b0004012500d4900001c01c0000c00c41c0c2894505084030303034010405512400e04010701004c8100b0024072400061003090108210210b005500c0d52064907003d0003c0c1801e002c1900c2c02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 792654649 1250 792653399 792653401
    0x21b0105040b0a0b01080714040807030602032205030717130b0d1401051804080d05070f02010c080f07120609050705120906011a0a030f020a1e0f05030c0703050c0102071a 75
    0x8207105002d07203104c00806944442680d036031032008545007a20f10340083c030030720020400040c074240d041000c4000380d8000c100c011703502d090018544491420380c40720f040c182d00c803644030301cac0110f080030003034400054002c3c40d40c03068107110380300030703001171051b102c4d80c06011818200200c0e80d80d00442c05450100006c0710100003a241e10020b141c00b08400f4030400d680021600d42d081141ca902d80039080d04140700b00c404500f88030320703824010103444088940c880003882c0140001219542405003016052a500340301c00d26062031043c510f40d2490051a00e000e00c4110621880011f00c00c0e8404c200130051000e0400181c18000401400d81e03001001085100c61028080344550b800460360b14103e848201282d4041d03401c0040082d4907801544080062581d02d41a41030000718a000400318543d49a498000382484090012f4200103098025800c000090001001140c0c0200840ea00f01022820280c4ca0b0301e0a458200d840307100c0c0d070850f04503e5002003642c0c001c0010f030070a54403610807815810382c06 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 792655899 1250 792654649 792654661
    0x9010b0d020303090409020105070501061409070309030203040504090302030d0e010605040b030f1c020f06041104140714090307050316030b07080412031a031606030c020a0309050f04021b0105040b 86
    0xc000a0310101035030640040181205901d080da00000e85944181405818000c40d51a12400c43d070007607000c02000159503000d40c0e40c5180c10494298800050301b01045545020381340291b4900031030082c0340c011a036600c15030091600070000c0e240501302142c402c4c0300078810000400d020702528407600307020b079040504500706844c0100304420004250001041d01101071040004904400ca9540c825030142050810300385505002c5d4502c070b00c1c011109000740101600a0208503084024504001040c0c4014072000a80c031a117107a02d004854030186494040c032000081c1464016803140d82e0501c01c012611805541041e02c1208580c05440440701c980d64500307040d2803090045030010100d41d981e043d5040303028001ea00031440a0505d4100600c1d2501c1400424581407444800c0701036107040342000c1203450380c14007551f40140030a101601c6c5000307159401810503038040c0151407103400000c8005496440341d03030545443e2440d8206d40709044c04090100c600801c005c2e2410340d00c0907890000200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 792657149 1250 792655899 792655909
    0x40f06091103160501050322050d1d0d200316181a012309040e01050a1512030809011119171312090b0d0c0815030307033509010b 57
    0x403c803001070f12003501d950350303113110308c43c00c540700c10400400400e48141040100d00104900040c048083d00c03600c0c861000d60020203000124814900d11400c45005840c000130722400302040356001444040008851082c0003d08001125030451107000c0c070f100000880341c41c0d00000021020340120104164964400891480760b02d01b5040e07808101000d10308121000c4107841514034a04d4814140d0501c2000e034000350075640e090301700107070583d102e03414883c1c103000501c1901c9102098140300c040c0c441c600b0340ba4008444400d000981440003500c0020380c1034100f07412507101c180060044a0342d4040d1040a101f100d503141da0140009558007002a8996521a81c0180541c038190389a0034820305c0d50b030b507801c40782c8150070022003044145100050040005c0b00580405984240d02042c001c4003d14003c14844004100c952500300158002c800c64030040200c60341540c040c90400d201d0758410100a0701b400f4001c05904511604410700c0e84100e0501c809039015a41040091144940301c004101c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 792658399 1250 792657149 792657193
    0x30309030306060d140c0702040b040615030e0304031403121b1b010902030703032303010b0d180b09010f0e030703090501050913090605041e0803010905040f06091103 73
    0x82640c0e0310810108406180003c040e060a0440f03810110350b0360801c4002d14000d50b0161401a81d810307021681500314035242c000ea2600d994142e6040100c68500350f861030300301e18610024000e2580d00d5019010240c4181b044801850b04441c2100040b0340340814940d0b80e40c070081e5101c003c44e45c0030010880d00300d040c00701e0303086031104102a181400005501f0040d461070303071040812903640c0c610300d43c40180c609000758401580a82c03501011006442403018042c8001401c5041110003000140a00380425050301c0100b040c0407000a0045500d0420054105142360003500c0c07004410100100c01e00150440c03808044803c2042c0603080300450300607034a011300e40e8020042010a4000e201d554814000340440401c01008402207540b400b00345001c5440703072002604e1140d00c6801b0401408042036400c00740c040840010007441100c0d488441c840e01040c0a4400d90741d48070742c080fa0510080c8030001842c241c10407020000414145402e0801500040c9103601a0081804a80c1c0501c403000d100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 792659649 1250 792658399 792658411
    0x31005090708070f201b0a05040c080a050604180b040507090b0f01140f040846060b100507051204050d03082d011404150501050c0a0210020d110303 65
    0x18103808421310402c0d66040c1201640319191001083c403034010f0441000520344510015045030640d1400c0c0c800d01c4803002c1141c1146000c0d50401c101c000040c2ea110312401d0380702c40d40e00d000081503281c8030700050203020484200485e032034034683c046003885021121107008910520858810641d00c0b0204000c2e5202040143c4d401103422464103000d50061000c03c099059001d0071600d05a004c400d2201e550708550400c8606900c81100c0c081c1001e00180080c504013490307030307007216608852220302007264070804040741c0c0b0b81200b410302e01c104030040d0050742c06800028840c1d840700400c40c00007020b0b03410035035040d41c2c0c51142c0005006c0304415481110199070307005d04010030000d40c545041c1c0d140c150181c541e0105c00010806003c48001d07288880d1a030812880071a6215403400040400140b0300c0c40409218034600524202000303049805a0f089401c2030070240c0d212209041c1c03513400d00040c2c880c0079400c5a20090300c50b0341c0c140e020074100d07035503941c94581040200a80c40c2cae550356404200e0321 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 792660899 1250 792659649 792659657
    0x10e100b07060920031b0901120c081f0b0925110303011d01170a06090f140d031a0607140f030c01020307030507230315030303100509070807 62
    0x41403000c04403000080c000315001d000c1c00b0500e10780a0703441c00b00c2040c3e903200c0b40000b4401c515003040c440c9014845484601c2c3c8480c1500404020040001d901030b90600c507402c0007811680303005080010b2a103845006241740c5c8240c40000c408402090360a15118055034170080c54a9110801860128981401f440c1821080b14100300602c07410160b88075040396000c24042c0780300c5401c4140c0c4080000350301900e081c000781c41401041d44000c1c104180103070445d0207000b0401e40f0150018400055120005410140c003141d0340c0a2070402c14018010b0400150846c4070f07803509070315030307135000141c0b910380340302e984e4003045640400701289082608000641d50300950402205c40131032010420202041180700903200c41f15401e0500d00e00d0b503440b125003d04165008030810840e25014400e5990155080c104040c441014582020340b00ca003004440805070000310101d00305100b9481c041407055805030031680e99041145040281000034403805100310310f28000100700501c542c2005020305041d442d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 792662149 1250 792660899 792660931
    0xb100c020906030a20100c1218050616021201061d2d06030d0905091b0903010e010f150305100c360e07020c06031314030a08010e 57
    0x308002500d1009040e45500d8403811920001040c01c01d00e50152050740d00328110710a5010006000038004003502030740c207000007600182e0124101c0f9256031540c00c0a480c1c00c680400141101d1084140150030046d00322202113800c01e5850b190031840340907940225405444081d107543c01c0c80c241c6802d0700516000d00e40003800706041c006072a108641203460915040f00c100d004d41c0c044205421150300d03504407100420207000050030300380040600e094051030802020303800c11000c02c1882c00043c04500d1141c034910b02401030040884140c0b000c0410090090204000c1d1440c1140a4010310220f491100c0c44c0102c1c5081c072005011019080361f40c804040d10304003680c24005802007000c94036450903c15610412910800809420009520a00146442a4203680301e159902601e904090007401305481440b900f2500019143c81d0080110380361956641c1d08074014046036419030000300260310710b01c900c0c00c041002002400760314090359541c1e54a40c0e038070035042d48840c4040d11103490781d800c0c1403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 792663399 1250 792662149 792662153
    0x1110903100f06050d030513050a0b07120c150e070801090201090b0c070f0906060305090d09051e04020a0305011a1303060203130b070905040b0607170705070b0d0f0b100c 75
    0x9048220700710084540050100e44d9800807400b80700034404210000342000403a034451400030f28680010b800f0694100341294148200911a0304c030300304c000b13000e40c40345019100328541309854070f0441c0341d8444411201d61401030780800143c01e25003107a00203070141000105c0c3c500014401d410302c00b50140d48840501e03281c400701081c0c90780100c2003030a00340a40c84001c94450b204603c0c140052603a00800210145045401000c50300054820f40b01c0d50440300229003256030054004040e0b640841d643c100b00c2e020b11a0624155082506040d000303400811a00c0d00640c165124078104e6416480880710410782d981c0d400101d10441c0d284441904100d202800460201c2d80034540c0b00481c1c2d608264803140d00d880300e183c070401c11140c501c00148880d009101c42d0505008a688114050b00d5082c100741d41ca64881b00c1c641880381c0c0c8188542408a00003080c001d08110403c0140300a410031544c0d009110422400b03090b0041304208090704154448000342024143d070b42b440d001c4e9513102e1b0a40c0a5035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 792664649 1250 792663399 792663401
    0x30e21070302090916081c08061e0d02030109060b10050f0a080709090218030106091811011b12080c120703092306040c08010501030209010306180b0f090111090310 72
    0x24244e12241d11038482c60081e104145e045c01c901070701d4404002c091315085103d4840e03403010362401e20800c00908005200103030f25500c403072401104d405119886100100404a60855414940a9855804d1601010501603982d00146900005660300d841c000a090003e680303034810a059480c03040c41c100f0200554611481c1d030150400120700d41024980e80c3c0d00242d00c180d800c04d500b6482d50440900328451540303070034814203000f054040c1044c003038491900507604c0100103a10b000390049580003128890303a0700c90036822001c3e41c0314010000318001c203401e201507204409450040030130301c0345000c10300405804060b5070051041d0041103605a8401c50102e014007000c02c811501c9280d86401c010003003e4610000d4032941c00403000f000c141c0703441c1c10194079660b610b40c04400d031039151400610168495000b03090540b0780280c0003140d001c8440301403103c4440b50380c501401c00d0201c0350034040c220a140b04e45034052101800207102503000c0303230201c80c03161203101000b9a040d84800440d805012071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 792665899 1250 792664649 792664651
    0x4060e0703200d0c03060e0d08091203130b01080a03080a15090b0f15130b09010c080a0c06050103080714060f01150323160e03210c0703030e2107030209 67
    0x50921009610b40b50f40f051644d1810307030021206030b41c44083c01e2038034610800000350500002d141c0071103a400c20740d0045480710341161090300020b400100040c00d000d042124180529032000c0b4841156030341c0d0404680300c80c244c11f0210001a107030b0700030410100c20f0f4060100000e08000070234440d81e1030400c003040101030500103680c00414040701040a07a0301c0b440200b03100c0c404070680755900c1c43e42070111140c142c0c0d690410030142009005c0400310780d900c024038070f400a60202c0c141c0d0340c644010790295941c403218600144100e041c000040108030001001e080900d105a5903150340401450341c4a0301c4480854a95001941207401001a101d00382c8241407032848034100002d59141e4100c0a00d00b85482d11301d240b05d514540f800344841030307860548170003e01041c1c1c03504401c0c4282c954002074031000341c45221100540b85440e0741c00c0443c034010403114144080011661b1082e500d140150002d80a041010700c140d841c03104030590b443d40e003420140100300303440261001c6802c5508110850f00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 792667149 1250 792665899 792665963
    0xe06090403020c1002031b03070b07050c030c0307080d06270f02120f0709080d0f1d130b04060b070c0504020c070e09060a1a0319030201020d09060504060e0703 70
    0x407030b010f21800d1a440e01c800711044481130394051366580f00315005443c0080781e40343c9109443e500410201d00840c589101e035913084a881d02d44a030303650704032140451650049400038a0580130000c0c00c4000c00480b4002059054107400c000c1c45070766030311190f00d01e480f01003201c550400c2e10070076030807514614507030b0016072009560100141441c01c50321020310841d1084410380c01580342c40040c4442c060b0440d2403134000f008400d004107400140e91100030710440c164045803091069204030020403c0910b5a51031030698041c6c5015011002500400301030007018080c4c9002e14a001c0001c04c18490355011900b9441d0060f80c214082843c0c83c060000035801351b0080d6096000d100b801003440c4110040d418080c100000040203241800c0d02903a0031100c00100501c81e80086007e81e00d1551800b09000c02d14090807940780035429002d0400b81e01911400640e248407903c2c3c15204d00c200046544100d0046005200c00c00003007503040072096448a040c0030103024a0b240001400d8503001c0c0b131354200c6d80c0c20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 792668399 1250 792667149 792667153
    0x81501150e1c0501321b070f020f130b09090c1c020a080303040f061107020f060a1403010b1e040b0306060705030c07150806041a01050c03040f061115010e0609040302 73
    0xc44002e41380c14103006005c2401c0c400b84029502c03603048000000d00350022150b0070304050701010300700868201e10400e10b006141d500c050440d4015503484010b0b00300e10000103401e84e92001c0c06004018002e01240c0c46070b0f403040c549440071403800c1400140d420402c200152103075211201d5000d903d9099054000100d03070194603000e0105d1544800d00156001d5071041c15039248803040da1602c40c081d15980002040c0c00c0000340300510160b941c0d00c140c11030503801510296514500308204032580072400d0b54040700c14000000004011042e90010403464100c0c1d0304200c0c8110340501000074902c030314030803101ca2103004d1000c150359140800040140e50701c44c0c4210f03483c2403200d0f00317164207001d070940c1302641c540c0180e10703280035064101820301e5000c803080b42c040200301d0610b035152496084412460b0b042200c0410869401c2d181081281d01400f2032016100c0075650380e0200a144030b00707060954003a8041c0e0f8060f814010a581481c50580c1d100405154140d590382050110000340100164218 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 792669649 1250 792668399 792668411
    0x60906040201022e060f032d03080c070c061124060405070207030b101a030f0f0603010f0905071a120615070f03170919020402070507081501150e1c0501 67
    0x9030782c0c0b4460000100307020741ca00340c0a00d10b1414604d192303030b07a4507500c0310000903814106a105c0340102000c2c1030b04c2c1c2c2d050900c100c0c0c6448500001ca540c1c0903140d07008054201071000407848640050b11a20300f0251101220703c10110340c90500c5030b0700c001e0021400c082c0c41007004a40c0c185400c1d013103d64022600d02c120b911550b03880e1035000324000c0546c3c168500010342c460600c1480c1c24000030010203448411154a141002d0311121a1a00c1c0200110030540440c03021946596081d000003411911071042480f00404d1405c06c2620382450b441809100c0460082c00d0510b40250001d84544d00e0140346040c14a41c1c0328010f0082c41d4480c030f01881c0d003c00d810840c0300000307070703010907030105250082c2c0c0c505480c000d050b113900c1025980a884810305510403590104083c50b000000f0103e80e5042e40c015071108000c1c9481c41c500031040d0840c1189002d12007002142c603c45070050350403204501c1c41003d1140f600d03070095407540017070b402e8150810144007001c1c41c0e01521002e401d40030707413084000041d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 792670899 1250 792669649 792669733
    0x60d031d190603020a0f0509090a3c0b09040c030311011512020415080d030207050102040305030406022406060f0304110406150305060a0b07020d05010209090f0906090604020102 78
    0x90200190000b0011a40c0400d080b08120340c045581d41c88044241449841c0014040000ba05180001e000340b2a80303413180d12000880c1c602c0100c8800119822207804440324101410000792040800014541c81c5000c0c0004118034000c003085008a411181d811512801c0d030301c04452458140e041400319640316610044115842014003000b09010100318840749114410041950003002c034124800c560004184400a401320300e24a221209060040c0d03590710314501076000e40640d51000d40f26010100340003d56a03000300e10120b00660260030319a10b540c00204904107040266107080c0c01500a00540310b0030300000780156001070081c950411006407040004c2c0584616421030403a0300103012450007201c2d0540240b81e08200121940c120b01420064485010301405802a110f08000310350300043c0502075040304d8010700d014109280c0e6187c01c40000ca803070700050342c901c5a035105a8000840449000c00c003a4050b0782d059010f0210b09005002c030b0090701910005842600d000e4a0401c54 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 792672149 1250 792670899 792670939
    0x16050a0c020d030c11100212090f04020a050306120a03020a02010c031704110a1d04020f130f060312020a0213050a140f0702012007021302250209060d031d 68
    0x49400c2c800d64030207134842ca03280f81c03090648010400d8980540008803c0252540d008500350030344048560440d519030040d1000a0f003440034800e210794000d4800504030540c3c0780c3c450025441a10182c49805008280013501c070b68840c0301e000040d0041c2c004584400043d031285160321003003406403a00108024480d110145041810340d0200d81074032140707000896500b04500c0d11802007400d01e19200200c60902420715a40701c005000910903a64010300500c280daa92005140c2d46814000070085250908420001444507001c01d80e684070a41d0440003056100240440c440c69000e082c207065042007000d00009444080d1000c000140c4a0300f0141c0200e010110303246c4036140c00c0851030700c50300745154087e08503140d80b0051a1802c200b00074448400c00c030788044a800943c195045e001c1b128402034104000c3c01100343c60030303010200514000b8880d004207130151020b0b00072203075030380a5180c10741002420015030344000c02090032424114001d0f018017426002c9254041c151101035101d2400c821 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 792673399 1250 792672149 792672169
    0xe031504060b01020a0308010512120406050301090b0a05010c1b12060b090a060f12081911010e010c1407080409090b100506120f06010903050318090f16050a0c02 71
    0x10001184110401091040c18020301a042000b0b001422160000742c03001800b000050064500410210482e40c4c4800010405c00307a6452a02e0310705621240c881400420130b51007031040e82202800c0c58110308043c40c1c100201ca04445058680c140b451070703030b42d0b036a40d0b8180c3e11150081002c0d420460000d10001400150300c02c8511603980090440001410000d4144018000089440ca0203000307110008000c0c050300d00340c451603044504400110310700ba2440e881081890020030350180c034501a10394101100e4100d107060100281311009608c3c20b107500700d82802e420780002403400000f206113105c20f100105250323400741301a01e140540340d12401e029240d1144080b10b4248401007044a903501e01c001400251100300d48052070541c1071310b07960a20300d20240006105034580b40200780c0d41c1e030141903007400565111003941c4e2075140400c1e00c000e03100d25a0043c01d001d41c0d01880007034100241c0c400d5042c8692154040c0008280603c42c08841c0c0f6040041084180134881d4010400749e510000c0e40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 792674649 1250 792673399 792673423
    0x3190e06010803070311070303080106111c17150a050d051014160215070815090a1a0a08031801021510050406060e03070501031509090605070e0a03031b030e03 70
    0x555941e1340b249802801005468414040f42d01f0104003030000913440f034541411101c1500c1c00030f10008100b0381d030300d04140a450320440510010768049141c50303005030341d02c01184060302e10380a00303640740000b000840311517400d0140d0040c10004240400d01d00000b0a0014500503000c441c0c4c01e440301d001d00e8003266000d402e40400ea03a403e00400c41c1943c0c0d1000c43c20001c2d10303107101820000109500c00c24103403402601100621425030300040303101c200700070301c012040e400920381005401c251203644014007000320789840d81004d4414441860500c114010121402c28004501c0c1600900e02c030520b00350285851070450045e41c2800080e604141003181c0100070f080000c40b59039241100704004c580c1b2982c000c0040c45035000715811150790108070b01048420a00300400c1c4501c0d420000c81030b41000e0340100306040c0c41c0001450510005500c00351140100703032503521004040208009c00d01e64288001000605505059103500d01c0031242d08000c03e20034101031140484440010341024010004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 792675899 1250 792674649 792674653
    0xc0114130f12140a050c0d080c06040b1009090201170a0b0d0c0609150522080a05030c010b0102031e1303080a0f0215060a0605070807060e210f03190e060108 69
    0x400003840401c44400c42681640c034020010b07101070741c4d00c854403400a148082c7c0b0500440d440b000602100400304c0f4081c00c085419101d01d4902403078201c0c12600103803107002598014440c013007002c0215204400000b9016110502800000000096403550003041c118070151546c070382c2c44890b211892411486441841d5503010241030090060648516070301154011182d40c0a003440b06400c0390846070b200281d038a8070b9a2507400304902d49100b03400c9a108056911070003910400388000403020307106400c0c00b04024090712070007400480e0350780211600412048440040c01d0307031007545900141050306020315100301180d0b882e2038003049600480400f0001c1a2100e842000f200d40c14003248010302d9903c00d0b03280660402001050005034280126402d000340095010107000451050703880095200c001031000340a203110707091321800f01181208110743c0c14003042384100c80034001d40784400e0032038441508640c0c403500f01c16448804541120b9946540d521200040d00003440790303e020381041c1d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 792677149 1250 792675899 792675929
    0x3060612160f08061f0306051026060f10170c1206090417070201051b03090307090c0e0d0f0203100c0e01090f06050708270405090c0114130f 62
    0x2000d0b001d004910854403c0081003c10804144d0302c03c0c00b40f034003410f040c600e42c1503040c592590076801032011703407c05940075410700c00300000c00b0b41c040392418081e03906000031000c40e40c4002004d5103100e002d03142954400c0da400c005040c01c1c00d100154036649503d41c038210004040c4078058450344103080e1859a0003a01c00914080348580700044c4a070010030940b1040ca036480d168848030303900701502c58020345001c8000307021020340e841030302a075400c06100d85d40701c1c0c4045422102c5e01d551740d03c078500c001d02a005100002402103414820007a02c40c249455100b510700c0e901c0201f260b1065840021615007000c0c6108001580b001c1000e040c038044400070000792207205030790145c140c000740340109041040803e000c1c845c401c504d9540d102201c40d1418916250941450071072032a019010030b4402420a2501c0704c1d503001d070561000c3d480f844c0e003038500f0400d41e03e4028105031211007100009000c28949801c0e0290048600018a4440c07080c64895507402d44400600036081c7da00da0000d10000d414107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 792678399 1250 792677149 792677191
    0x20705031b0a1e23010f05090102120622150306050a0515060c0307170408100207020f04060b09011103091306080d0513120318030515010812040302040203060612 71
    0x10642068201c0c0160f40403014101c56683c96040d01c4241c412450814001c10703007100c1418094019072606284104148002c0c5040c02c0902c3c000d4002d400a031010f01d20003008101c4600b0080203000703080c014a0760062800101003009406031000c140c1c6401200902000017020404912900340174901c890404203403030900c6102c8600b1890f006d5000c0344030384410003202d1000c1d0400412210702541c440c07155030401000c000c58200d1801150300c00f5100b0700450450718030300134031b560083c43c0440c4200c4044207000492030034001290013074080d904040070b0402c42c0280c1136009140007840e95158404603840c2c41c001e0808a01e00343c0d1804074464200f03850300000e0000420a100d888034007030003031806c5400c04032403a0700c2c020b860009100e1a801a500c0354000001d140c4168060b8021010780030150b0080d0b6500e1429983e030f1007400c0b078142260b20402001107114900420785500a01542c5446410141140c00f04002580b0250a6541c0007908105030016075840c0c880051144401c0c0c035201c04102d17105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 792679649 1250 792678399 792678413
    0x803071101050c040803120a060b04030803070908070b0901050306210102091c0c052101020f1c29041d011d0606091b1e1b0718020705031b0a 62
    0x1420700414a1421300007440300380c2d000800d840441e0752424501400c0d1702d609000c10010700541d04402003001c40000c0103c00d01c00c8038001035014030980d6440032060346d51000c82d07645a40b95801210f00e020010800e400d02584a480999082200103010b80980445150100d240c1406551000c149940118100c26540b502902800a0031754100c000840c10301c15a0303a129065219000ea24450032031840c0000c810341c204d8200e640382c141408001c66640c029484400d8460b0030002d42d010f2542d1b003080b000450003459003e2050264010612031070062100081c080740903d40c00e120940165850501055100c114846240c08070300700e4000007000102c00e0341c04844003040001d20025507212009002e100d44810320725035070103542c2007550f1241c50000b050100043c400c41510b0050000e04100003005011000014040c04042e064a018503004440c14181c98000d9031140004448406241c00e2900c1c0c0b540d0000d2001a111f903041d00d2601d4030103034070380382101d51500e00d0049a41c8510120070801000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 792680899 1250 792679649 792679651
    0xa2f0a060f171612020708030a020a120c0914060901120203060f1f0e01090e0f0406020c0114091c0518030a0f03030609050c03010e042d11270121080307110105 70
    0x284d450150b25000c0d03240c030f50341a02e01c000f6241c8444954005584002588100c03406000000c0145062201d4070111030020000c1105000f521441c203809100041103140031000c40341c0d60b00040c0c40b4000d001c111032440d400290001000680c2040705420014001d5036850283c491038210908030104003c0b003040700600c01c1400b613542c607040c0b010015062110074149459291f000000b020f10003150341c1ca41c50400068003840c1c03142c012560030028032250704182e5103019481740844070221220301c041200d08041c00705000c2041404500e081240382405940c9c003198200000c400f5040320031800c059950421120340e90a4280c00003035840b08184003040f10f500440d40c0122440d6841070640d4100038060a4a0401800c0200000780b4015004080b4880d003c1090106421011848001440d402d0150400400001071441100240002c000c54642c0c03204043c0d500c610401142070aa0030147d0b0007024104030060443c005050003504000115404011031042110750b503108040e6a10400403825100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 792682149 1250 792680899 792680927
    0xa0b130225150f0b040e0d0e1c03081506120f0901090c060f0e0306070f08060406080d0c05030408060a1b02072907050a2f0a060f1716 59
    0x1c44240708008104440684070b48100c0c1c1940020325032250940000090116541603030b042070078401601d0a10001240d9103d41c140b5503110317960042440420064406044003261070f803030030035550f83c601080c4240c000d5039020707410140f00950043e10800254280d001101c00e20089612501000f44080c00101d019812080e030400078011380c0e49603501c2135036051175406450100301c040f00302d010302144250508802408094251071190030515001410b002e0b40161610129410746d0101e421828544a25421941c059025004080d0070000480d0383c010329110640c0c151106210115502e0018040c050003000700800001c1e02404803452420502c070306070076400c00d54000890400410740000c59824800c2903ca2076034000c40d0b240314240aa6000d001006403140c4620001c00f02000000480b800001044050301c90020013241090701d00c0d140e07003408407600402c0c890003c00199002d4002404540300324205a04009840d40302030064142c01c4441c01c0c0c0001107500007440c0e072a00080084c840c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 792683399 1250 792682149 792682207
    0x417040503030a21090605060a0b07080f36091f0530100501150c030806120d0206060909010204060e060c12041d01090e060f0a0b1302 59
    0x62030100000d45a000310078240707084c030094000f0f041550420740444403969080403403c00c030107011400e104000302030442d50f150280003541c0e0b01142062681d01617841255111004ca0f1030809401e0800c2c1c502e0304003d5420a51a1068000d80c0741410b43c030740d440d03114801c0704018405800c076017002c000415402800c01041103200103000b003040c0118000540c26524159206019105581d4500c540112095160505c4456402e02ca260319080030849510a1517031040c103212503601c0c0c0c111090220240c04c11900464584025100028051f4451540c0450010030380c03c0d103800110035607403c2004003852240160001c2e4100031403442c0c0003044582280c0142c00131821715080c1503000d0134034a05440304d01d1045001050840540c9000c000719400f08103100c0d819911213030307030709840c4000100b41c1108503146c4011b42c0c004190b2840030710071030b16485c0311000200f20a0b21a650003012043d00034060382c0b219500d4008900898a80100303c04011076a02c200590750103041f4807200c081000410004003507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 792684649 1250 792683399 792683407
    0x70b04120210030b09041211030a08011a160b0402222003100e0c0c0f060702150f0601120e010515032104032a0306091a040c0b0901020a0b0405060417 66
    0x540740d170030030355600c2035103e5400c50700708145250680d00c02c465038140d45021703c400608011460f0780004001d0403122081454032491044100070541402250310b041c0307408240150071000711311410030898100c1d0020704811281d228540c0825245d5a040d0800d03482651150324400341c029012280d251055440704c107242c02c50070680403070303900d2800780c2c86100d4a41c2040303004140c032000c0090480c0c402c0c184030070032115441281510a0384652080300c0c00c2c40136005882c010ae0804100081c10341c07003480c1542802c61242d5441d00103550076042d641038400c02c0c0c0d60f203180034950f442092040c43d0042c61100001007802442100f050b16000b2110305213582140449080b80490313408805030740070b495020024803100b220850b280c0c20051882400c440002601c00400400d000302d03584501c000901a80100e520465100711945410320140c4000b000d04400c0c0004210044200b40a06030020701403040d109808080d4903a5482c4100c160303810f40d4950480028041001045800030300b010301001007180c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 792685899 1250 792684649 792684671
    0x140106320f0c101134050601080d02060c0d050903090d0507180902030d030b0613120b0c09030a02150403241d0d0e010e09070305040c060c110d0302070b0412021003 72
    0x10700030703405d00c03c5044400040100d680248820140300340d01303060341031407400f01860038521769801c42032007076030030751b000e540b0b400d15a0074804220140304030a00301d002c0389007084000e40304006200080005840d4042440040000c3e95007401c9520300500440c020840c0380e0034041e08512840b0001001c50b05e192401400030b005031008600148140d6150400042e080c14030350100701c1c14810307584040354510b9a0b200201d40d011103022862102402901040819910b80d21011004d02c01c08422650561259048000610b0106034000c009100310514908180d90717581d540aa41544000d50b01d641b41070000c1d900814a814800c0840c844003003622410035001c81c040f100c1d02c82000020340d01c10403020024000d40c0e64012142020301c410040d02c01143c51031301c52130045c0102000e803001c4500243c3d422001413054810803c81c084160400790301e02c200b01010040000c07007011440c0031403d41c0504900052890b0000300984000d00034030744020054081441041624081103070134200b89440c09058182c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 792687149 1250 792685899 792685931
    0x1050a08130c05180702100501030203060f040c09021b0f0c01090e060402070b09010203070f09050609120c1c05070501090e01031103210409140106320f0c10 69
    0x241002019040241900303180c14003042030b04032030304000d8001c01c2c06500034060076071403010207210744415400d890a004105072800c1c2520f00a10020b036041d8400e8021640c404840c881d515005441001b12099581c0e540c10781000ba41c218401844148499011030440c0c10001e0110303850085145018014030204140064607816040c00750750305800c0310800054442d200d65044038032072a000b814100b41c520300040030502030761040f901d200020700c0c540b08190525005003802403c0d200010034150038110808240044030300c0c00009240c0d14440d11441150b10f480d101e140c1e10030f000d0303401041800c00c0c280f0304104d440c204603030f44018100900c5150400040b0500c040c1c25054a80c0114a50369481d64800080c1c90020f00072810740d2840101982081c8030303001c01c40203208494040109000b0219000341d403910000b002d100310300100b18031a822101d080c0314044880085150b610350a082d59280900f42016071b0004030b4104555280001c1d101c120100c2040b9210b04c441400c2014480e00c50420301400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 792688399 1250 792687149 792687151
    0x70807051917010908040f09140907090209010504050a0e0f0903030c0304081828051c06091e030f080c030907050405060607080d06050f062118011a01090501050a08 72
    0x4400950140082562140c082d0400c242c45600a054079460f1a124428422501f200740704400c4080e14082c03105804240002c00140300710300100c00b8101361031038003200d20301a40c00400018100201000701140e0b50f0f0303c641e0404041d1802000c50b2025203003c0e80906003000028098a000354800e0041214a0310000c00320786d4402c1c0c0c441d0010707840b061620380841c150002c1240e402e51100140321400c43c080f20f0343c03520110b0a00c4451400d036407255180c050041410704100010422034080d407201002c209250040d29001340b240c040c866107844111030418000d01c0c016022400116901c001c0e86049070702800054210f006040b1441c614140301c002c1c0c1daa07540761440340d240155200c2c000a4515030b1079006440c1c0f03041d00064120b503141140c1c04500001d0015015481c400c07010800000c5050400509981400540302c460108082120911500c00e00c2c00620010b9810000541c64020312002e02510303051441d0400e1740c08000c591800090b144400d2a002141004070603c0308070300e40f5620070402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 792689649 1250 792688399 792688409
    0xc060c13051908032b090503040e100803030a0e010c0801060519030209030a0809030106150c1e141c08070522030602041e05090c0301030210020109140708070519 71
    0x15060740408016034501c50100c3c1d1100c41c15000104014103140742d50340142000c0c081443c207a4100d03076400b4040c94102c0b420500c01030000d80c4240000d001c00c21441c01825081006440000c0d241541d400901c0e24544c0700322039200752551687c01401c20003100b4020580c03880d01c1e80c1892071066051500080140c09108144240071450500500788517000341e04480c4101c2c1c02600382ea406694034200100154484030300d1501a61900000003019104450402405c8249946042881c521038a0710740340318016103c042c0342c49110700c181d400040c900d208010110314004000e0000304418401c0c5500341104030103002c1c180a004020407840c1c5501004942c8a015011030860004980302903100c0c040880da0001030500f4400203001c200491540d140d190140200700100980720703216014001440c4c41610790030312409007400107100624024000b0510000c0a20000800226a031150410b41c8a0442c4100254010785018450700106012050241000b42c1d0307042d2213190810404240d050300740c490 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 792690899 1250 792689649 792689659
    0xa12030218040c0504030c08030c0c1509031b09070305010305061306060b0c15091902010e220c090504090510110d0c05090406050d0507030201120f110c060c1305 71
    0x700000c80d078085051090035840900b04008078841c0c400040d0a5034014042a02c034a106c0440000c0c01560010480700b800c0303081c00292074151031035414003d0b054a20030744540b07800700a000b07162081c1c078100311816400140c504501030542e00e0300c003884141c82000e02403004241c205801480031502c00117610f6003102401003544801c40007800c20074010718542d00240305540001990301d501103130002c0d50310b0100303c000400800c16120b034507410b40d40f0b100c64030009052281c102c1400000d507000d908000081c14000c0c146144098103000d140c1c000c001a04000c4444940d220844803680d90302c00c8085c80503040075101006103e070345848542e0b0740c1c5944090365200c10303100c0030b914032024051000c0d501041000441400742190344480500244c00c07a0b030300b450256180100009143c81c2c03c0074912020341d0890040c0500600316001111418009a5001c1c1c081c1d403181b5111a072191030b8458158004035010301d0765205c2c00600303070240c209000a0400345000c881803001d042c1000b2040a404200da50482d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 792692149 1250 792690899 792690907
    0x50109060801090309210f0f111e0103020a0912030f022e0b06091c290412050f130509010b1e0c1608011d070f0b0c3c0a120302 56
    0xf01c046c0040c10703a42c40c024040a0042d540c4001c00c001ca0300c1c0d040f145413103402c0c062480301100d4244851f5044840510b2222608861402881d500a030f0040501f01043d24118941685480c06940501c10080c4105c0c009012450307007810303496050050041c0081c1d1840e00c1c0901c00b20141084c8009000000d10b0a02c1a0b0b03290301d21b10075550b441c000c5841049019115040c0d040408221240000f100307201500c04211000d0410090b50000130300c0b90b459101c903501c04050f41c4407074036002c951300464542c00003401400c0081d408079001140180800030110b0b4005032009090500307100f400c8606900901c7c80180c11f01101c0d0040207060b203051584410140820340340c54101c00d01e00c0c035081c03001300980110103503504040365101040d00107411014815608010301e07291880c2031903850459201e001b6206218000174407050040b4001491200814005c49511240f206580c0c4041510020248800c078400c0d4203c84500c88600041085000d02002502200c03541d5210380f48139081c0c035190b040415034001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 792693399 1250 792692149 792692189
    0x60a030e030c060f0a14010b031503150c0a030f0b030309090411041a01030b010f08070315031202030901020706020708030f0a0c05010608010203150409260705010f050109060801090309 81
    0x800d03128404200003c4803020305209100001201c02a2281c2c000682010200c2c69410104002d841c103e4035203500c101d2540d03442c2d851140032104002c008580c18000c03580c01004034100b0718400e0b40030b0100c181d4201d42e200c1c2c4040c005401c03604070078244102c2c00d0404400008558011059640801c020381e0100c001d60f0f1603140804100059622aa500c2442c00c1940c149a8201d00034a210511013a24208440746402005542a11100ba0360300c0000b4040d10000e40c0041c400d42010751500025046411a1904c1c2d95500c0b404907803c055060050388040381c0881304e0341c8e041000d40300400c51070010708070190501420703d480c0e01c14001c8084075070300000342c82c1c40d00501c5503540040c002d402074020004940c8480d100c5d8080d60043e180c049042c641181124201c0c0341510a00c506507510011640b041d4800c2c90080c9043d0740290040ca145603028009500070450a010702d804885440000003031941c1040c11075012280786410000142c0c1c13604450000003038004c8803820540e445c0c0b0204400040c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 792694649 1250 792693399 792693403
    0xf060c050c01060603020405011b0c30050d020607110601060305070903120305010302032e050c090604060305040b0a29030f0d080117010b15090409060e100f050105060a030e 76
    0x11180c0141250b1070400f0001c0d40603031683c090310944000342c2e10300c0b24803240c000000c803540000542c00b501c44c0101650802c064120605109000040c09042210003043c581180342c94810750441503030150003001d8482e0030310b5414046590301c95100e08004030708030311500595a4504050180b0350605540380e01080d1f54500840c0f00340b0080d5400240e110054410702e1004000d01001c0c8012400303403044c403583e01d5442c3e143c0c24803c000c2d800c540e81000c9050b02c2d05803081c800340c08042e0825481c01c0c4104441c401d1619400014409800c1c903071004660f0341402e00d04100c0401c40200100c01061801240e412454082d84020800050700c0c50150035a00c22000045c0c24034114000b164070307500c91101c5200e0b00a4208079418102c448800300c40e400759400d88851800e9a0001c0d043c107500c010440100c0841002001c0a00050040034000140030807199581d0800c85544803a41d030b43d1540500080580c480540c02460280f420703d142c103000d15490040403610340c0c00380a0040341495100c0e41c508480f0303481 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 792695899 1250 792694649 792694657
    0x30c031101060b041d0105040b010c032f0607020625030b0f0405100501320708070507060305180d080115030905010606030902100207061d120f1b0307030f060c05 71
    0x14031803000303903215517480e0206a0a0348950510084c4801d002c00066030f480c0a10500c1006541a1110b0314a40116a42100c070307a80c0b990981c80d1880c0340c496041d03d600480811034028003100c00010007440c00e144002900d4510000c0c5040299a02d480382101e94401259034200d54945906012904003500e00002e003044d1000700403030350440c0c034103410070409000508140701125400e8031641c40c41c40800700501d40075043c00d402e450300c014030006120341c4d11300200c00900b030795170040703400341d04204c3c0316941e960400b1416444230000075241c60078080031481d0515003840c0d52071404001c102c400316182001d04002d60510440c072201490a0b41c2c1229a030007904102901a030110007008816111354001c0e0003400e05d0a41030b8025641c49001208060001985500b5070700140c96406580020040e40b4400a0030076180641080c0e2086c6840b2458000700010340800d009500900044007090305281c80600000c81510b1003540b0540081001ca21070030000c0b5044c40e0090408038104425440640749886 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 792697149 1250 792695899 792695909
    0x204090f060b040606080c04060f022109010305010b161e06022d070305120a090609060c260a05130c030807021908061f0504021815030103030c03110106 67
    0x5500d40d008041164542c004154030030200d400f0014107885180072100f14a0446808000c900100003d1000750701581201c0520581303481110000c40a4104052007900080908041084045180402c56805015540c050860201100d04226180907414903080402c10b0241185803950340004005c01004108180c15811070401e41d0784078500c8a00c040040c2d502d00c82245948c00c03103180e002508224404940704d4a400d83d8a660810b80007a00d1b4810b40400640600b02d001e507140744040000d600740c019200503d020303900c0090340d0b8050041c0a812026040c22048140c00700c61481903403140415801c80d080804c41c54001002d03501c00b031028010586101d000b0340321134081c0364000304100800d4003e2103024030960390700031042d103002a0f032110781000b40074a1510f0781004000410030311842c481000070107820b100228030cc0e40c1d80c001082c120f0f800b2880d01c000c00803002058642e0350410440300c000301181c2800d0285590f15584008000b04100c040040c204a042400b01900c000250401e0f40585 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 792698399 1250 792697149 792697163
    0x203040b070b04050105011409010911070b15010e030c180c13030b16020102071a1f062006280615030506040c14040504020f0c030706061e0605090409020409 69
    0x1030300c2810650940c00b81160110348540c02c0c040082109075030ba105146940c0805081d9811a908040003e00544000d0034506000ca50070702c910404903210181c104d021b06c0140c0300700366880300240c0004000c0c00c4491403085c041e5000d040c049805071142113070305103000c060034528002a29042d0002d01d8074428101c8802c0396080308117000c0300380040d1000c10f500a44445041c020084558017003039080c3c2c021714001408403901000c1000070320140c450141d03800381001c1010f40120070b0b110307803928801c1300c0c540004000801c00c54a41c0c0c145d04812683c3d03000d48001c00010302c4039181c8200c1c9041014100d0790810b0b680842c1d01022503484205030060b8000d0803043c105c401c2130030500c0a0040007014100c030b956100d50706204050131038a0040740d5a030740000c61400c000f494241440c0c00c2c4806944007011002540a00700903080031000c06002400401748907402c04900c4901c0c1c0f1240001a40c000c4c17010801041c5106000c21421390003004070340700c1881c2654040b4543c412400001c005041c5120003910342 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 792699649 1250 792698399 792698407
    0x5190903021e1e03030304020103021b07090e070501021c0f0207090513030306270203070e0a0b07030206010608010b031302060c2407020a0b0a0b03120a1d0411190203040b 75
    0x8410346090b44040c0141c508001d0346540700f4448003109850201d079605508104041400b40d4420740040c0340710a520403503080c4000300244400e20780a402c4e03001f200059030351054090414070a114020050100344000c219210a00d4404240750400d22215414006411919040c040c000d0020000034080318000300b05528124450a50380d01c107414088000034078214000c01c10801143d44014280854909201660341c2c00032040000e51010b070801042c0b00300201a40c80e00d5075410f08074000380c622a1482a01c1301e445140c040e15054042e00310307105101c003050040c044c0c00c10110070360703a1001c900310007c46100080d001150051240204444143c09020300842c005085680203d41d40c9200180c00015581c03078160890b101c0505c00d000a010202d5600450800c0da4650001c0746020001400d44078401e40042c0c4890703003a8841e1200310003041d60300680c15002c1d0054000c07001e01c600306403010300410991881604080c46003500d5096810a4903688807202442041540d01501d5a08102561 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 792700899 1250 792699649 792699679
    0xe031c090b0f1309180201080601110d0504080c0402070308040b13080f1b0d1b02040f0603140c09060109091d0303070c05010b061219230702010e0d0519090302 70
    0x2150b0105800702040000c002e000a03030102a0300c590f06445c40e0203095a40d200e0150781c01140c16410260201d410400d9070605070030030ba403040c0039040602c0c056449240e551407922002c2c504100c00082864420b034418006c41000c270341c0069110f41d200303501121141041c3d0b50303005200c91a02450340c000d85003580c0810303400c1c103940c030701401441510340d241080030025100c009220b40d2009040c152a00003110343c212405404607081c40c40d100144002e00c0031030000c5007030001c1c0044500c1c60f030007074074805031600c0f80d642800003c0c4038450440c6820b4030141c0c86450540006000c2740d03003d12561007107550f0782c881d211503101200311103a10b50b448107050f41d0342c034105000e0040890380c1498041d2100d52030102c5080340c034600b01e412a80711212110009400303981f812b003041c01d488a4150343e6400c3e03d0716107007050b050880c0030b03100840014100f68903010034101900c0007401c44610390800846944410500401590090103482e00240c02510b00014000c03100021a0b1541c2d49910080d040102c2c0c01c01910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 792702149 1250 792700899 792700927
    0x7050a0c09050f09013c020307030507080c210402030a050a0b06040e0102090d02060c1c0c14030711091518010311030703030c0803060a0b0c1605010e031c090b 70
    0x20140007106183c100340d44031603111508803201c0880c2481140000d001d4070302030018107000ea1108440c4443c0714042c58590401d01410385e802164040000b9907100100501d880d04122100c0e048440c40d05800c0c10000105a40c450391002d20020b401031549800025086680811540d04000e81c0601501d82d902e0417403929041c03070341c07055400c0361080d4186101c046081c2414820394040880090000546a1041d02802a19800b0f43d03845056070090500090142c000c0f0396034071440c0042c590303400042144a0420844c4207621225881c0203400802c51100440c2c014801c1c90300a00d01200c2480c4d207178480c0006a0700080c00f031021150405a5004d42c0030341c003400000d00390f04a038003030944992104a04410591038402900005005c03540481911010400c668060f5502910107046101415200c0340350720320300d8022003007030300f1949c2c01001c410b08807022809040004080070308040c414981e00b00000303034460314004046d031850b288508051081e2841504601d0090080152560341c50412081041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 792703399 1250 792702149 792702151
    0x2031b040e1b0708120402040507030c08060f0a081906060b0f09011413060c11010206190e01020f07150f020906160812160e0a06080109050a0605030730021507050a0c0905 75
    0x10323205500e80400107580e03500074000c14104600c02d0355000b02503034401040208882c40ca40301d05400103500000410000c00800890451000032410411803580f545407a07001d5844c19002800704450901031f6003024211501940c040d5102401d0104100040311098801400b070f6071912036100320070788400120150007486031400d042c050b4604169002d1804010f91303880d00155a40310101383c208a481502c840c82d50711440e0309075500b800162801a2112035290036412401d400d9030603169000210b030801c107992003407005001c100041036042182e440d0004085010341154144142d58082c03140080052500444021030115620b0600782c1c104294110032810b10201100c02040304031520040e2441c040001008880c525030b034001c1e40da0309040c044405064046c10901c2d00b1600c644006c1515501400014080c020000b00b1075800d0740313022010340a4001a40701c040101310443c2007500903072180c1c1c0504243c43c2d400c6199903640d000310f190203443c12060b41c0e0040d0211840c100c0c08902007026030080b03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 792704649 1250 792703399 792703403
    0x121e05070203330c04030201020705091003061d0d02060702071401030608060a0b030d05091c1410020a170408160c0f12110117220c080102031b040e1b07081204 70
    0x41d95031a00300c4c940c801e03c250300020f400360303000d041c2c02c200f0340c43c207440080c0e8000c402014010700c0c1552039540d4019100010320b10040b602000390b84e405407080070410480c40c10a1032000341b151313040013040607480d0301013401507088001291400c13503501c0e4002d411a0000380301013011604145480b588400040c80e4201009102e4080c0c1c5400c0c0c40c030b6511030410b4850000d4002c294503010004c030000c550448403007481c00c0714000100b0007600c10082003844440c181c800c0c04000541c0c0c4030820704005000d0a100c40510b643e6501000911010510b41c4003541e49450b0086615001c8107483d090900325050203910070a10214800b03800300c2c889140b505034410b00f030305c02d2980003401050b0000561310410f045042110040e076010000e0080c07030340c2004900782420300100070500d00c55141c0303584031505d5507a003021906a4001090200484e0030035210100d03000744000c101d0615003880e807000e4641c2400740a1814000c0754141c00c14000c00454212517000f0f910056035940e40c5103c2e2800b80b0300720070440d81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 792705899 1250 792704649 792704743
    0xa200d110d0f0804020d05060708090f07030302070b0309070f140301570302070b01080c0916020c060a08040c09180602180409030c121e05070203 64
    0x60603066900041c0e2480d940d1003500c48a03504041030100320b504840062003643e0020071b010950300420000c1c405035020f010f940d40c1e08009864a45122454800407900c402487d0b03100401c00c00109a0118418080e18441e640241c0d4030303180c0c202d549240c08000d41020180c2e20480384002000e250000441c4400c0c6001c0e00248050141d11081641294581002c1c003c2d2200c02c01c403408481001020300e0f81c1c0f0601c4c6c3d8910121100c0c400100345460840550301801003a40056060144103002441c14010000c500050400c1d00610000c16040b074005081254640d40c0c02c24140100c1c0c0c003c0c1304000c45418003900d52520360072220310041800c68180c406071220170f903040740841d044c4482c5c051042c1c003c21001c0d0444c4440e21036541c00000350720001012044141a501c00307280d81c0e45500800c050306000b07590b000e50607099030800d40c40f0020200001010f0052414150000000b80600300900581c1030030019202c0003180046800c00d030301e070402c9102c407400031108186260750000c0070384248510110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 792707149 1250 792705899 792705917
    0xd05031b0a090506070501090506011706060406080d08150910140d02010917010207140307120201090c09090f020910151b110a090c0207090b040b10050a200d 69
    0x44031000d4800d2040c6980024580c801c28019814207a0092581500c6800009181c03107640e104c07241006001e8115440c5041445a282d0017104102f0010703401a90490701000030900d0200c6181d40c0d211815003040c140510040090070b40d0748180d07030300311764040060310012440c54a0010051240d885000341d4006082c985d43c2c40703181d402c00740085a01507606840e110b05003800d0079845004442c40100148056400b0408203001442c26040214072000d000b00541e100d402e949440281d101d006194501168035100c0c0840c0850503901d082d80440702d40401c00201c09040c2d0820392041c21107244041d41160800c41440052400f5081843c101c401e0407610b420725948044084680180655981c1c0468044151100105160085c00d10b0b01078801007001d003241e580c1d6103020b01134600203a20035002d6000790341d003044000003038010005040c000316000c104540ca003000040c04507826041d40d604101021807015400d40c025884120746000e00c40c01440e40640d2805a140d4480740440e0750000614820 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 792708399 1250 792707149 792707191
    0x2030a0305090d170c252a26030307020601080601050316092705030301051003020f07031d04090b100b030f0705070f020604031a0105060c0c0906120d0503 68
    0x80303201c400303c0c0050365852000058071040d400c540c03031016140d0a507000c01005120011800c01c4411000300c0040004c4040556a6041c5401c1c1c7d200510500140b0420303241940485c614102c100d00e0554030710550300050006030500e50715040d01e03400030800382440000705000040740c00059841c101c034001000c807841e50fa00ca00605485141d6000c1c400900c0702e44c00c41c28040c142c0c5540040070240c10351313584d00480714406140300080d071004100594841d040080140070b075082c034503458034003100b0f5803c0940c034042000c080882030b449112009010004036102420394840c4020342e07040b080350000c01c184a0304d8130509204100b484185c81e040e0845172600e20000745a03d64505980c40340607800c0d4a05240c2c0d44460044d190355000341300480f0324401c051000401a030b01c980242018502410441207580c030f00c460300e6224410103030030a40c82441e00340700c4086107200000b20000101d00035244030080d501d0341d00128032141030180c0211041e01801c40e8180d003d03640300010714803035481e600f14105074130181 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 792709649 1250 792708399 792708403
    0xb01050a05070818031f0e0105041106070510020d02040819031e091d090d2c0d08030f091005100312180f060e010201020c100e030403060c02030a030509 67
    0x2001000820018001c140104814102901ca104941244039869044c1180000d0030111001e10315002a052461003030200c0456200f11285411040c000700414240f03034a4411017018a5200b20740300d61780c00255402044018000d58404c0640d90b4001d40d21390052403500340294000303004030b080da4480c2c0c1c47c24070250210010b448400a4054503030101184800d00c1540001844541d0302c0d0603c104070b4400140a2400784da0148014280d11034024241042080c6905280318540440108000c034002000c1e00e540007240d4800703003120303044c40d40b5100d107540b130200c3c5c3c19100407040504800301c0441005001c0c81000d841c0d6200b00f500c0815605070303503540243e81d011200c050b28081c10250800c481803000030780090310b1640003c0f040c20214911384180c241c1c484603079940d4000c0d00303030380c00c520104011241d045410301c0140c2000340029400c141c00e06141c02d658039440c0301c0480a95450314000b20004a06004880103960080814042112001e002070350300e511040f00c40e0006443d00c40011034840300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 792710899 1250 792709649 792709657
    0x60f0906240b03011e0e0403020d0f020a02030607030c02250303080c07260c030c0c010906030e120f0f03010f031505090d120b180a051e0c0f1c0f0b0105 67
    0x4002d9034116400c020800c0079403503461241c01d460101c401c1c2c01061840780307a884d80c5d1169209a00800b03406030f4a280007401c48400c44080700944d440009900010380d004502c1691102040c540000c4c06266205e00320720340b8000c500030399050180140b03542d0641403680e10100c1942d001b91681801740e201c1c1007014415100d090b07405040044e0903c0c01034070020807103001c40c11030394004659504040480315132604581c49812240c0c4281d01850700a0283e50b0401c401a000f031000e428104030000202d1451919007090030340035140c40030b00241d440441032580b0156640301041c00b4425071a90f840c0c610303080708031103140030a40d94442000710181c141c07840780c0240e0348100f25440140c02030a0202409440014248105201181c1c0303464100c0050344072080c00602407245c0601005032410a00514821110050820020410507155400500d4000c421990300050031118060347e03000002600c110030b0051803044c40b510412881c8448560311143c0004544c80c01d00b540c208041002c12005407841d1007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 792712149 1250 792710899 792710909
    0xd11030106090902030403090e0a05190213090905100203100f1a0d05060a090e1e150f0a111204230705040905010e060a14150d0b04060f090624 63
    0xa00c0c0c84040c000c110443d00951b400c50701c00c0c00c2450380d09465203004150120208d540310403040d0748008010346909201c1c1c01500390012144214613140300f000305201c001c0b000703000c0e01407080d07103d94803c3d0400204101442e40420300010131916070810a0802c0394200d95445044144410710102003218100410101900c01d1800c02091174a004003001c140540801442c1c241e00000b040c4000070019441e015200308800a0006001c008098400304006482d0500b0f40d10015070019100c1000501d12500194000302106400ba44030b0b035072032061030060301c0704214104a402020400303262540c80400001c3c0a1440b0301361450b0065801c42c21030340c0301d903a0417413030305403e52010340c0801c40340c1400d601c03070034640c0e00850000c1942c42030a0070386032503d0020380303d00783e515507201818280c0715a4920202d421a14401914124103085800181c0c50740300044040c1003040b54902040030415a036000420401c600f11051050612906200004040d1040c0440b0004a03d0000301840ba42c1591075000340c031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 792713399 1250 792712149 792712157
    0xd0204140f07054003150c090e01090b03030f0d0501030c0902120c13050312041d1005060a03021209070807140916020c0d0809030c04050f13060b1003020d11030106 72
    0x1002d0b1150311141411400c2002c900c042138014490240050310070600c0910b00030001240e40180c074441000890300032020080411070085030a0104a21a030800740c1103030b03244103011541e541401c000904503c580c00f0080b26554000400e003a5810980e003207641224051080c81d800103682e803c4200030b0b8810759100300100e010b10000615480c02e60030281c0052201c032007201c0540703511640464900f031901c0055901c042c90209003000202002c1109141c81b82ca2980c1407211820110065410343c4500d0046520801d07021995a8a2501c603034180c4240e0461b81585a18030308103c04043c0c4c40d180540644c0c5014044d483c40420516010141c1c0b50030040d02502404881d40d405980c50545540c410240c0304500071003204039011b556030410450082d000c1d140d8a5a41c0791440304151a00c5886158540a14141020861450380611400743d101c54003042400d0709000d40e1801500400e00c0003003156101c00007480444030242e242d400b51200605440040140703000600460005010900c5110001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 792714649 1250 792713399 792713437
    0x10315062312120c100e0307050303040825031d0402030603150912040f060219030f050c01060b03150109120b1b0415030f0b010e0f0f0d0204140f0705 66
    0x1030411103500940445420b082d14400764600040c040180e0299a41580c00d41c44502c000355424554450074904418042c010340c5031082a070380c0e2580721f0000500240c1003000210304d14040d0401d1180301d00b400c404a40d4180800d9035946030152400c42441c40c10b4035005244900d40c1a1418244212401220300400400300d920304404402801000100050468028840365505c004800c5010304007910110303c0803023000b403d01e03400a1070445e100100808580c0005071000c04241c1010b40d240b00951140ba01550310144114268050903990380300f40f10b8803800000f0000a4960034186801460099940c001c455544524400a07403a51100140c0717107a180e4400300b07910180c8070707c4540102752802149410241c0d02c0c100c04400488901c00100441d031600440c680000c0030340710b49d070520701003401c10884095207080490b180c025440c0302d450080b1050741d000e0186030784440c900d4001a50050052041844280511800803400c1c2c0e0108000055140810031070350041c0c1c1a03810070b040500f80040303a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 792715899 1250 792714649 792714719
    0x30b0403021009263a02131202121f14040206161a09031b0d21140109020c0d08071706010c0209040c150e06090d0c0e01031506 56
    0x41c0c40d05645810f80510081215140031321400e42c120f08501d00481066000c0756180300f010000c05d00c0c210388685d10b94810005084000002095182a40e600d8247c071180d001c5039201041e850703910101409600d00c60944241000d508160410400d0781004100f40004840c165840b49150f009440080d4400810b210480c54010740d041c0c1c0a10647c000c0300462007468804488464540003903500c448180c00010f60381c003031982c0049aa906480300d81c1c8c002c03d4041c101c03103c0204a90440003800c06040c2085410114204803a00031106405620340e164450356514031100f0300941c41044022014001c2951005210b4010f5035241e2181c5801e4030f0700070000740b6500804a0700b050007041141405605086040035860b030400c01071286100e90b902588040c02c084510081d20034580940f020407141c088024000c1e02c5920540344185000d86142844040600e420186d030b032203e40140152000c0c40c0b0002007481414031000c1050b0710490002c00c0b059440d02c00c641d010040f64450419952018160300d14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 792717149 1250 792715899 792715943
    0x1f0503030f0712210902030c1f08041401020a020703020310050903070f02031c08070e090c070b1801022208010510140f1504050405181c0513030b0403021009 69
    0x221050b14105003c0e4004a40c4c04180841d034007019020301d6030b0303481c0a5085040401c00d81c0002c070f40483d03192012118075248401c1f20702aa4200c442082845000b14040020040a00640900701002035448429031031000307507143c90300e01c016486849024007420051080d441200d0103440b024019500c1d040d81500e41b00090088254220303010300c5044250f1041440c001801031000003641e94107000c07810300c1c1200610b02c4600c110303454400c01540301402440104403080b21489907000c1031103038159451140007105c20b0684c0035401c040354000a13103560004e10301240c051b00d2110001181d050140c58003011800c81d081114000384407403c100c800c1c000300e8801d241740079080d24002c00046071030950034049200b200507a00c640b5000840810207020b28541809950761188010384e030980f003909206011980c0d8022901e00c20809003604244400661040c0708541e50210800d81030f088055030b07450250028541140d00790014020b0310080074642c5503502a40f01201d8101c0041124441b20200d002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 792718399 1250 792717149 792717173
    0x90c0901082805011701110a0c060f0e0303071d010e1e2110020315061b030a09090e010902031f090b040f03170f011203171f0503030f07 60
    0x1591070b61a0085015400000048555409810340000c80c1651620003c02c280b54900c407a65207669040c650780700d103108803140540303104000300c0c078245901c5485070801d01c0041c2084120410600d007406041d1044140000c001d5024140304e0382c601014040c1c2caa000c41e10700404802550004200208c801d0280c54140700702c11082140c3e0b4a190b003510620340018190664489021441151210014040344001d0007290311460618600390300d103251410030012203220007207036648150300c04907030b88640c401a8514940418200800c82e1394500d000c49001e4801e43c1544159690f83c0d01b044000d180c244818007840d4080395002e40201014414200c00700f00ea10341c42c45004100356991209640401c0c220f00e445805140a2850441c036010a07080007400410821206403c1140c04000d004540040c600a94112242c8030411003074030070306160031030f804038a041c022550b500503001402101610340342e501d450107038844040ba011b259180d0034181c6038090a40d031480401420b20038240410748218160f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 792719649 1250 792718399 792718411
    0x705060601050d1d0a0c0b040b0405060c2d0c12030a140c0a0602071104112b050a0b010905030c1005031803040f030b0105090f1302040e010f1505090c090108 69
    0x4203010600070304c507129084c40004121400da200444884c240700440c0c243c8000b4088600c80781c0d281c5070a01c150044e0034070451007001e01507500003034880d00b011030a106000100740f0803c02c0d00e0311a0b5441c81841903641201100301c13054003d20b40044920300d48040d070007490003800300203542450300400094904403103425000300915400c01140503822800d0101100c81c2e88a00c50044c1c071100d05040407401c103d080b0800c103004625103c4803071052490310013500d0803106807042208155182d80c1c400c40e0b0860680310a0101c031401c02062104000c516048000c2c130900a0f61040d9032a03039580d08141c1d03200002040240c20203403084c007500085102c1d1004603400080ba010704c1d404805400d020740d1940c1c2c4250f2112a1004200c50180b040103e500c6910b1300401040b214143e1908050101305071040c40500040d180301c02d90780c0c3c080b0464403a6044050098401e10003085810300b03448602c400b8011042d480700711640c1d07421020840e80340180d0350078000e00418446074241080c483c019101d10b0310207003407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 792720899 1250 792719649 792719651
    0x9240f0901150905120f060c090109031b031208090105130b06062a150a15120f0f21080f040b07091e09053706050310020307140705060601050d 63
    0xf010515886122804c03030210b0481000f42000c00700212010b081c0400a844107c5202c01089413030070581e8440b0000d0140c0e03800821a221041000c9100303500c0448a0388000e0291030300510741480c941d00115114481e032500f0b00240030542c0c8e2400c1000c04080001c4000704001044c0d00414291305000c405000100204401c40004100842300c01004811108411940e03910814850114249090020f03030803580d80142848004900e55201c00c643c00c0078094610b0b00e4060702007140c14000301c1d0021090040e004020311b00360f500107041180d10320b24101404c246100c01e22164400e140d01c9954010710500d00c0f4500300880352915618500002006003c240030094449404152850354821030103540e000c0d00307003103c2034038500120001641c4004000800710b00101c4440c40012914030143d0340031201150030b602c018140225104001c2c0b03402d401c81901403242c1041031016a036281e00442c000e440c0d640346c00c4c160481c03180c020317026446010b170014895000100480c08650145010b400310800c5048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 792722149 1250 792720899 792720917
    0x61605090a050a180b0901060e010804030917070603050c0414130e0d0e03010506010503010308191407060b04180804171c0c0b010509011a030c0909240f090115 70
    0x20028207503030f4160b08554820406821802502e42c014880d00322142000c3e124030b83ea03585004805442e6555164085040c4002000080c040522400c1003c01503e81512a005000c0f0b83d001c0450341d910850150b480401e142c0303408622216071403400e0310102c5140140e504c6d640503510702840000a00b000305414190b0701d0703442040700c100c81407188200404480c1e41d450201800c90040509541020341b80b241480310420050021441c1c90084440300844004c2c5901e140071102d0301244c0d0344032012040300070f01c503000c0740c52001c00c80c15070003001d40d64500f200d09001480f084800e071310f07001840a0004218100411003044514600e02e0034164861094081c0e94503035030300d0680c441160701400c0c000c130002130402000c842000710302508030380540420380e05c000bc07540c1409040d0a0080440d000d50a01e4900800051072807038603003084800c0c4802c094500c01c0d040c1482c031111280b0141c4404d090190400341000d006c40c6061180b100304140e00001d03c0b80b90b840c2d28080c0c80000b43c0e03943d103c40208100c101e030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 792723399 1250 792722149 792722159
    0x2010b1003091e140129010302030921070606050609010c0b0a02220503190809040e03070f03170c0703050d051e04230c0d0308091608010617061605090a 67
    0x20b442d042c0d03004980c1a261306003203000d603d0071502c0940d44070800b41c20340108402e01900c0d008101410810030b0800503031320b40f074008103a46840c060ba9445030000b00021492401c40030340300c01a004003031080006128894807802040308600900d038ac16800100d100443c40e0114490004494000004800040c6040216006002e0311910000c50440e500d800175010011400c04000050403070702003598101540328541e40340c0f040ba104012a031481580c842c8181e440780c03034080c008c90702c041c0d902c96072a0a00c4d02d05403a001d0140d020306001006000100400624034070f054000b00c03245c031a41030390340b1032400300e034424000000c0c00c0160540c50108900d0100e5004241c0200300503006500441c400c5285d038045440103550302d03101d140a0710a03502300c400e20846988410107940034055060a02c00d0040ea5400102c0b840d10400d105c0003002c810b110040082ca1610643c400c006a450100072081d80d081c20021303c82d41d4200035182c0f000000c0d121841c4100b0184504040d181c012402411445020359035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 792724649 1250 792723399 792723443
    0x60306120b1816170109151d151806100e0a060504020d1401090603050601090504021539030d0c091203020c090f070915030f09140d02010b100309 64
    0x340c0d0f0146600080c4039003c1c0b2000344441e1301c0044000a02c0000c0c000440da980d211508182c1c0d01c20510003090710382c10081001c030a00c10000b14101442c508440318450038513120000c60600385e036188000c0084103c40c440c2070401140c414410300c140a04002c01c0d92410a00741e1403490010700301000c250391034501040b00d83d03c0380000d00c0aa440d2041c08207400c02d42030340346a031000e8133030f00a11071285051001c0000070740c04035800c0e04603080f07010005801e50760390011a8031140414034840c00403030000b41c45c21040c540d00f0175200c0e0300c4114102c0d001c514841c401d942031500903041040401c0303500a004400b0303040510380040d240c581c814038150302c809584000c1c007501c6000503d001c03000b5820035000c0c007025042200459500802c540416607aa040140e4058002c081c0e031b0151190311042144c20203000707070290304480faa001c0d031071104010703110007030804105610610040c84e06a00030041059426841400f4280c95128000d0141c0107600c1710f20b6045c1d00421304100c086646194041c1031010940007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 792725899 1250 792724649 792724663
    0x603120304060c17010807030f0204060f120c1202061207020a020301020414093403060b040902031602070f0b160b010905040507090606050d0203090c0d050f0106060306120b18 77
    0x100c0c010100b41041e8198000c0d000c0101304e03214103400d81104004110343c050004510f4100d0307400c841c4502c05101680040b030068840e54015075030000c1c0500c4000380d083d5510701090b003518054a41030244c2c030780701c0142d000d500501c01c0d4040e5004e40f040c001500741c0c1400c83c2140e5002162401143e4240505501083c00c1e60065801419844191010340015044c4400c0321603001614001505010035451812a8000255006a180c09401d514480a058000e61020b8007030089001555244e80d0784145420195004585425410100f0205c0740f40d22070000403580305950110880315001c07424103094043e50340240d030a080450003480383d02c50200c2c1104008174040c00300b01c2008a01880c150400500e044880d900c001301046c9040303003c20031b265100c81501c1c85140e140401603640d40704c040496143c080034081e075940c401c56018901040100001d891060703001054001c0c044941c4e2010150100c0c0d040380b1800740e00f03480b05001c0b800000c142d0451107510082c500900700f01c1c2402c000229180c041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 792727149 1250 792725899 792725903
    0x1a09040504031d1c120203161b210b0a021605010b01020601080615010305070507050312010302090109110702040504140601171506100315051503010906080705030a0b0603120304 78
    0x101c001c0100d010741c5150301c120543d00b2000c1d108991200a00085060a8403514074060701c901d00d65504a22002d00c24803c4440c92000c100740e201300d042c418140300b400000246007440031400b00340e000103440d01d8403224828101442d202403640c141256201e408801c00000e010040702c03603080161003403c0d0400c071003ca1034280228000174220356504006840e0100680040003030b54000c104201055100340f5060021004c01e01e80418103444080d415103160040c400001c010b4000030408012020304000342904a900891311107100d642d0350f01d0804211640403616450480c0108211130260034150000381c1c12910410700744601d41e80500496050031401e07005100f078104030007030401540341c4c200000200507552062013405810710030002001e041420030072500740354031600004000c108a03038240c801040d0192a9449028001c02e03892400c0e4424055514918a0706401040d64100001c610040c0d17000a402050003c403a51104040020000c0c20207a040c400e8071550082a024007002e0f5008034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 792728399 1250 792727149 792727157
    0x9140904112101050906090a1212091a16090b0f0708040f0314162c07020106090e060606090d0606030819021e030f07060e031318151a0904050403 64
    0x1540c1c0b01480e5082d107901030000340d0650b1000092280d44000031558401c8036900c80503d800500b90f5003001d031601d0808004c118005403a00742c03110180844403070710b0603400384d07001031220440d0b40303d070f01c4081108040c00303404001500c0104140000000394004140c419120103660b420041144e56503031441d44503410564a060303400c4030070001c120072052902c20550503140039019188843c1c240d14440c016504c96040a05110001e1101e0641c0405050341c1021080385881c032240313841000039010742a648103411005c0e19095207003903800000318141d8001e01c002040c076454458400d080183c40220705009a840740c1c2c4c2c44070000001002c0800030041c0d80c103000d10040380040800c1c1c029042012400c51041600031a882481d0304001c0481120044060202071986801850810314000c00294152002e64840002e0f04022254007003000b20403501d02c4600c00440325540c80032a41a200c4000c03e0101020909205000e2035807900941d150b0901c040c1c0d100c5081074502d10002d0291803058405402117 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 792729649 1250 792728399 792728449
    0x60f060203070b180a020907030207060608070510170a0507140403031d0f010207090510080f06060a0f0608010b07140102030414160501120506012304080c010914090411 74
    0x180d41c482207034451480d134401d0340250320a2403040d8640889404c0280315592010014442502a41c107a5603802d411840c104407035900c0744442a41c80e2401c0c010035210320098004440c40c1441407141d02e48282155002070102e8580c924441d01401d40070300b00f4400e0107003840390110821003c802602c0118020342d1120224004036610124001c02280c82e0750003003281c600b00c460703582d0700050803000300e0300300d0b0400113460754480803206006002a0800d1516000c0e0000c141c411040000781140a900d0132517000141036031703544298180380303001d20401e80410490702c0100039815100d8040c20085000d050141804250b1018150072030f841201c0444194031519a50700304072070100402224841c03c030500b070340c1c2c041c145030000c0c0030204061100c50201307849400051803070344030300001400800c0010b00c1c05400d0b400384a0300f004540241c050700740d85201c3e08149000301d61203404d1001c121484165030313606240d81d140c10301450b144001c10940f240c114039801100035881e070910710901c0c102044012041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 792730899 1250 792729649 792729653
    0x1b03020c030a050d09061706280909050f06070207060807050f12041403090a090905210a02010b0a030f0201050a2106030606080601060e1e10200d08070e04060f06020307 74
    0x304a0321780d0452020880b10405445d80301086002c5240c01400407180981c004048070809005240d40345c80440082c0c410301c0d00003031010000d0300b114101030301c10702c1590405001c20003016629482156441d0059000c540c0c1000640e0094100d140c20640500d003080c070b000311424031124a5032241070125188402c0404100a10120046180305503416101540c41d1011200008403031484d54003810010f181c0da10f40b40d0003002000c000011213003065104810300c1c01d4841000a2061708242c40c61405542058030200561030110307044403d0380da0203481701035111036503001155550808003401c410701580d080644514044010b1340703d42e01c003503004081046821071900d441a60701c542d000781c0040e84280018802142c010809540900c02510864800e420b00c0f403040301034800100010b80c01280c00016858800c0c2c1c400068821303008240d000b03c80440c00420710654804443c4043d02c00a50420041560180b140212000780c183c010f10110390390351140c0c1540c80880c00d6a0121300540d1002031800c0c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 792732149 1250 792730899 792730907
    0x2220b160f0816141501030302100e03090a120308090303010308030a0b03010b0301111c0b06030a1518151202010c03110f120309160807060302090a26010b04020a1b03020c030a050d 79
    0x2017241d60300f0f503030b019075451030740c1c06503649485200c442045500c8160f400900c030300c20030030b40300309207001004410516981c90246110807001031003600010740710700000c1c40c0e14900104880c122039110201c6440c5559242c001d40c020040043e5090303042d500c1e68102c03a400e07602402151402d0440d100300c00e07030709c00c20030710b401a01510140c0707219070f02403c000c01005181c1c0c0302c8060326804900910045018002080d005a0321a402d800a08011113500300542225006500044600b840c3d11030030040d464841c468018165400e00000340064801c8002e00e0000344225500f08001e884442101c3e0306010020409003803180642019402407004810482c1e040c201304402c5010700c80d90407004480d60306101c000394072500a4040d80d0b0a15400145815640d202c0c01c1c0c0c108020060410543d00c22100c2c040d9070f030b010021540e0400b02c0b9600b82440c0340218a030a20894444409540340c070304908101d60320015482d1094038050301580a001d1003d080ca031000d100c0c091426106a015002011400e08054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 792733399 1250 792732149 792732163
    0x90a050711010606020a1401061d100609121103032104110406050102060115170c0c070603063005060711070608042a03020402220b160f081614 63
    0x58260381400c50070042150041841d900c6c107900000c250300c2c0240b00202c410701400595100703440050341c40b031805560080c00c2c0d140500421076985031041d00c1e5a1510f040b00c01c01598002e20709400d0344c05503408009000c1200b41e0040342c1002c0d09803070030013028915512196a02407802e151881700c500c208001c00c40011860700340c8001c100c80801805081c440001c1d600c0f5414000c0c014030f14031410030102c07482d014020400034988c00d0f420b449a07924011461211302d410041c11881940305090b400305141c0d001c2d000c0c030780c01d9420a250782c0e0500781c0e10b60261a8a1560a48030810310302c00070710048045042440503a12490041d1100314102c032101021a14003440ea5000508109821091100088119503104045041000080800081c401d1001040443c0e540700950142c4005249142040a0101166401191803c0b0f4954583d83c81c01d210240c41060100010107443c40010070005041d40380050307245005150450401000601203c403843c1408800d46e406801d6856906441e4001c2000c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 792734649 1250 792733399 792733427
    0x60501090501080604140a120903150c0203190e0a06090e0106110d030c02010e1501090606020c0f0409080f0409020409051e07110a02040f0e120c0a12050702090a0507 73
    0x801880d890f0008442d29500d025000034040d007588141c0f80b0407000200500c850260f080344100c0c03900c0380412400740c2500039a120449105141502903104803105106507558602e030790b005186009035803102d000e000c0010540b10014404840714005040e240c282d810009800c0544424842d241845042a02c00f40160701c0142041150400c90754203200104111038442035604002c1800240318105a01412003002440e050740314030380400d05d0011050355814103c9014007070800c8042d403a58000c03a1945401078a03203801001107120b920072401c240d802010020b009006060806d508102c00620355409580144d42d03568010400340328045451158a0300b22030007034a40510038440124a20142d01c004003c00184450791103d4558402d0501c0602c880d40e5004108001c0398140300c18000c0189407801d0b501a440c42411000c0000401000c111400c1c09514402404409265a107074480f03090040c1e440400c101e014044c3c040180c40c0c503540306006400400e4081014a0002c4005040900700240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 792735899 1250 792734649 792734651
    0x6070e0303030c0708090f120115230907110706021014071718030c030d050112080d0c05041706041106090a060c1e0311060a051014040f021606050109 66
    0x5110851034a0004c031070720350f80d125a1540d1965901c10015a24140d1001c007140c0000c044150900111019802004003411110a240807203840340b0340d0940b0320303090007030715030a52190804c0d00050b0301c1d014403c42c0d406030035460030900c0321044855460405d0003a502c054050791015803030010725804d5014042000401c410022068901554000c2a144100300d50f904040c0c0c51101003214480b04084c4401c0c15848041240d50311a40d149602d030750303544901c41c104540d40c42e00c4008103002d04a641003a80f00ca8100351145e04000f480c50100f402070120840b0350041c04002c000025440d43c0c50304084da040c1d2400b4014000c1c1d0302c3c1504000180120300c90401c2c0c811501004000740580c0c40c0d42024050f1515880d1000c000c0503141781000803d0103102501d80c0c28001d25030307120308040c1c0c807042c4c00d6403401801064400e03640310b40c12100c054031400ea60b00e01c2c0e900d00c4004140001c00c03102d003008200c904000c20110760290700141c1242241d01c8041019181040c0e0501c800610409026030380c010f21030044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 792737149 1250 792735899 792735901
    0x109050f0705090607050a060c051c020c0a02120106150512061918061a0417060f04171903050603010b0105180105070f170319020a021c021e06070e030303 68
    0xa401040c2d8850403160b40d10455002c5416028040c04010b000501648070800b000440100303180505aa0810000c0c02c4031060441c20004e508030840c0281c845007141d80c0010b0007010007a500f040a181d00094440b0455965200009808010b20784249010302032501c4a950b90340501c10341d2000e0150040c10540249012101c20380d006c010740064404440240b2007400e00c4940c00b0700040040c01c40c1d6880650700281920b892041400200014070440c0e01c0c4940c005000300100c5002a1541800c9500d007210038481c03c00500400e40030b03c404008000511002403600204840d010300040001c003441c4c001a58460070010780303003000d00c44d070094030b0400d0908606200540c850701c104c02155030251410890081400c8040203075909150244690100700150952003010381110315030030440e480340842003000300b1901200d1240c4229064255143c0c0500340800880406040c5a240c03c042c1c4411846020260302940900260101c24101d4810140255040c04038004002c45081d0700d0b0103200b07410401c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 792738399 1250 792737149 792737161
    0x6050f04020127180608060a0c0f1403040b060411031e1e0c0a0207050607030804052811010e04020d090c0e091b1318060e060c0a0804020f030d080109050f 68
    0xa0784080864035402103e810488862440e040070741741603807040020744194024000503000c1c90300b2101100314241e503011118602d4240844905140720905503040200f000400d012400802116900c500043c0000c100c0301580034500ca0300798011070705e0300c0c0c045400b44502c083c22801c0380502e90708000005107400ca10034007240c0c0741500d040c01a2035414580000520080201e0007030005800178400104801d440302c84501303000d45241d0044608442c6030203010031010040324110305015000b01024010440c03202d440c4e885000000c00b584210b810f004995402c0b085681c0ca50000b0324488403c5040459544410301c0c04003903040c0300303401400c40d8a00384410042030190003d0a03030345280c108403d85078071681c02d10120b031031104c0103003400d45514207011201c04400040260420114423404007000224241040c086d180d0740251103840903203031300304460302039a441400c002c1c0e040350009200f0803003607120300000b0b4038180c1c0300c17514003020800050040000e96078611449921110740312494038645480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 792739649 1250 792738399 792738467
    0x100519020303220204060e010602060f010b070f02060327030a020106140603070f0e0411120a0917090406080102070c0501080915040816051e0709020403020607031b06050f040201 78
    0x51401c0c41080c038a080b843d05542d250b4000900404101c1c00705500d55031901002511424100d07139075018805004000514980c1000858014a410030b880c4030490b42c003076003084555440601041c040c4490705d103a40c0d019008290b882500c4100240007540e82c1d42046902a094440035880380741c3d00c038076900303039030380b460712070000705c907400f103c9441c1080c103d5030201c00944025640c03c4d8915001031402c00455020300c48080104980e07501d440806285507190882d42050303441040c1c006100003400d802c1c0007580c1446001402c600300c0010000b0401c6526405940c1c02c907008004161403084081c0f01c00c001558004a005030402c03900d201400c05070403494040400c9400c00740c8001d0268000003921b28005000316501c0c54859032160545103c6c0b40324000c03418a4401413503654200e405160000684840c81d842150212030f03016140a05140c00350b107042da001c00010090744150003d101c200c0c8001040e51061520500466456110604250000400074150103d401d41000c400404203030f010488 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 792740899 1250 792739649 792739681
    0x6040302091009090501020901200d0e01200a121d1302090d050f1015090c050c030d0510050a030213090c0801060f05040f020a0504060c0809100519020303 68
    0x640307034080161034280e500d0801070700503440002000d141241d210304101c0c3c10b400a14035030200340e89459030a512901c0c200031100f078882c90134049600c1404003041440c0100c403402045101414038034017020000300071110100d105404803400d81c001042d90f40801004d00c80380d0900600d0b51a22000c0f0b059945000b031140c0100e908030318401d650060210fa0180c4c51034046034140309002d041d044a41c034080ca00700b980c035022050258070900030390b507048080c1c403a03d12603d01034003c10b091445c000c92902d14801c00418000141c0e4041241c10090110001410001070401c1344016400086038070380702c0c1c0000740007035080d0441c6100c1c481d40e00c810400342e82e581c0c1c01f4814074680c50000041004540c43c0610540c40d944e40802d801e03508042000440c41d1585860b07504540f8143c80074002130320b181c0032080c00c0b485020060408160705000074410944100d40200d0400d1081001510b4075490400140c81400c441d012000003d10000324100c903480801c5074100c09a040d80011811810240449851610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 792742149 1250 792740899 792740903
    0x11506030b0d03111e010e070e1501080907030f14060a11030c130e090a11060309210c0615030d0c050c0607061407080f07090315020c0c0405010603060501020f0c060403 74
    0x5013600404450080a2101c5580c0c0b1084c8910310071035500c081080e901a01c8140c04089581c00f88103c009284400980d03503070311507401096003403040d1031050010b68100c1c1000d801805207204803d004000500c688580c0b0166074050300b407051146031448140c030300e40100100f0b603003034803420110300d20140003d66042d0303500102203d42c01b0f80c84161140354040110000da0142501d0710000052080300750000c2114500c10f401500d80101e00700f082400c1c01400d21050b90350000c0340c0e10030355544680c07030b10031109514110041490b0619200380c4190503807500805a4640641c144a4081c038101803a08000401185078981082018102c40341c0741c458803980800f203a5401b440000440d40200a00c41d401070800d05422003402005080000d0014101981150500040d00c03019001c40c40643c000c400c10022254011485540001e00141800182d009440c80b80340920940d5090501961140078040c040c0c8000d58001a140d480d00f0002454107124000e50324040e04010700c50200c0782c6070740301118103481d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 792743399 1250 792742149 792742157
    0x403050703030f020c043b0613030c0b09010c080105030a1106030c040e0a02031012050c0112022a011d03031b070c030b0f0f06030c0409060b12011506030b0d03 70
    0x660741c0300581c284002c101d452580989040045281f0491194000c0d8003200e00c18a64418885c00092880700c0d80381d032800c0380e4082e51203400022520102c481000e40e45610030301d4013070900030703440c0d40d000c41c0d8150580701c96440d1f035103901100340c5051b4441d500742e00401e000c9004041a0080b911026022207008120501410000000072102000303030084070020201c5400e10103803071505048000080d00244c0d0201c40880070440c0004030304240580c6545c0050304070b0080c0107200700503001522804045c05c500100d8a800f80204246000f0151000860148032089000c1c8081024041d9007194806440012500a014281d1804503400030550703030301c070764a6035000e0342c240d9a40212440d07074091613000800e0020010408030400070ba21052a000d00c4925440c04156150440d44c490700782c40c1100c5903901503020b801c1c080d0291400b50841c506950080e480000c40040000204000c40a0355503042c2d1169180e1b24407064004c0f000d01140300920fa81d1a041100f41d0196001402034a0307a448090208 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 792744649 1250 792743399 792743417
    0xf0103020103111c0b060c0d0203041410050d0504020109050411190908071e0801060f0602010b0102010204050d11190801020a090801060503030307110106152006040c05220e0601050312040305070303 87
    0xa91201d804646007c2c00c0c101c102c8410031880d41c0003d42e03961150240c0000510344e42d0982520703060403582400000d210b600e440b814101d07a00815002840003c0060b030420005020000c1c80351910f22a9100341c1d907036100100c2e501c20740141c52402c600e1885101000704031441e0410003210002190300400c2d2012041e6058034111000040101c45060f034000a48552812000203604244407215a0407034525400910001000d000164202c0c001c41c4901604178080301c09600010b140c8604016035800c0080c180704542c604010842c4100355a90440301c4241e50000304a242d050b08441854004c140c03032802401058100404281c0300e000c044e25200601042c0740c15440030050030340218003d4905c02c0d03d907ca6001d601e820040014054140300c049607a000e1404400e41040465014802d40d0800d110078803140c03910f4184000390f403a9010704821a203001c14100c8450720180030701d840c3c42880308001c2c00a07504101c101805c1030700e0a8102544103e040004000103100441c3c8003044030380504004040e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 792745899 1250 792744649 792744671
    0xc0206090d0503090a08150c120105150d050420031605060319051003030314090d050a0504080601031b0b03040b041e0b0a2009060912150f0103020103111c 68
    0xf03140160481241d014000b05e401042855000030407a00804440c0c8805109440d086a00f402500c03c07105c1005800c0004401407044d8184160549038000061710105c1c0b0b410600e400c2d04040311000c0d1002c80319603441d100c030000c22301060000d100701a041200685011195044001d000540701e00c100c50080902000203003400e41000d10350b001030816080e09100d546002c01c0c0000a5011a02088010a24050f07601c40d0000c654108103104601c0701c00200000521610161800d400a5901d2020090100004204c4600c1442000c0c021803056110744904c2102880b580d01005203a002000c032080240100300c040b80310386e5006604680c200700381c486201d2014284d41c0b41c03a07040c0840600036400003403d000d480e8a29078001585005030021043d1505200d161040300c1d40700702c038a081c0e403024081c0b01c1043e030713403400303580d03811502c0ae42e401100d41101c0054181400307036804848806c7cac004030303a038010802e41d40c0501400c6140400c03070404600d003100d10810040401b603100c081000056940014841c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 792747149 1250 792745899 792745903
    0x41202060712080a15060c11121002210c070b1009050403020c0112150905191104060f0c021f0e1203090418050d08090a0611030411010c0206090d05 65
    0x1112582011242e25121402c0340060210b950907503108259a00d40820107441d055075551950541e8000d5441348140c40d40d40d02d4500c0741c0c040c403680190740000c203042d80b00c13401c140c208106001d80d050300f14096102c1e0050161600d09000018194910385040000c021a0300801e5007110816544002c484e4047d80306d1102560382000c154015140da20b141c0350030f200074550001208825050247e80c3d0300c843c41c0102d4201004d4030509021010b9140402c0410b0100206030f420081e8400c004901c1e50743c0800c041c800c09426100b00c150b0b8244075520000e01482855408111035400c100d03e400c1250702c0282c503034007003106640462251350280540e0820199194412800340b02218802030101844180c500c0c00d141d180c1d80700c44400d43c4250310b081440741e03071880861801640241c008020b0000040c100006468002c0018420b000501810080c100000d00620a420011544140050b02c0c1c2c0303014500301c81d40c1620104000c0c140523244808000590b90313030049421405003030741c1c1a15040300c5450502c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 792748399 1250 792747149 792747157
    0x1e0604091e03021f06140a0501080c1b0106032943051b0109080f07140d02060703111305043209120f0301092304050c0111010c0504120206 61
    0x128983c401c10418013500319094202d18180c031200c00b92004a180040100807064900741300386030208420900082000034110081d22a000054030304080300c00ca07030080c1500310b6145402c101d60303c2d803c0050014000c172a8188259002009501130b11103420141d0782ca640c90301051902aa4100d007000c4078440ca24194440c0c1d0184801c211210340740315018a0300a03000d030300001c4076281d20203010000040020300500a41c4401034000070654034100c40d00e007481d036465100c580c050300c40185190040104420420480000b0740355030380904000c0c10314510040c1a50f0120641c1700110200b4044100124410141e10040b6101241c00003290310000f003140403103846200c075079048183d60301c4903c21400d202405143c400d820301c03400d8481c0c4c1c030b802100c0c45545029080185460441c28001072250104640c4141810300da0140114030f804e0085000400311070301142c0c111210f420940c00c90031103580045110000d5003101000b0300a05890010090250186203d83c40700c103c145100081075450340422a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 792749649 1250 792748399 792748423
    0x806150d0b101a0403030905130b03150a1407022a3303130b0717130c0f0b070605060d0203030a0c05071e03080901171e0604091e0302 59
    0x5000351900440b01c440380003492080b0032002e02c074011000d401c2c6510500b00c405595050300e40545050a00041c460030044100407194000e030345100308040780d40d00b04203691158100303405ca100a0b00c0c048002d003095031102c02e0010000642170040c08041900130412088900d050550f045c11102000071507905031459100036500b1101000813415410002042c0c0b400d041001c510500d01400d0001800761184000c0350b6041840e040c05402d240080c0030070250580101140c50310b03084078bc403030100307002c1c001e101940d4440004405001140410584081c150000d040c1e4800d02c00f0f406141840880444c428514028641c580d580b0004c2c1d00c940c0d808080385403d0340c010b012039444011032000500503406008060794140300c1d40c0030005d1b16480c0b9850710490112106041d0210382e2442ea120841070300001c1c910b50501c840d21010405941c40e41c140244204c1034009912155100611902110030b809440c16010f41c3c105400e100114280041d54058040524906004101d240c00c0c12400c0440000c44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 792750899 1250 792749649 792749663
    0x4050718060203121602070513060b0307030204031a06100f021204260304060c02132003105307171b0103021608070b010602060f010806150d 62
    0x12890300c0c2d00102038901402c4000c0d0041e415203a01c900c40c49000c0204a80c100140d0122409114509042d08000c09041d80340340003003502030f100c02d011170301604110b440b130001940c003003010014041000314112041561082d03145442c02c240020608a00d00940c0300e00c1848100f02d0030a0105200b0011110f00101e1003040780e40344c0f5260030310040000146107200010581990450484050200c1264122807072911070070780d03e0000f5424428039240340c610300050142d481c040c8071140340100d482c1c4181156640a401d03035a107041d401c04400f5403225007010081d00107214041380020200c05011441280c8004525045c0f00e109114400c4450703041c050b81d0001116412004c0401c1e0300103032080651b2841c00e07442094a01503540d06a40b071503074034007103039141c000c0388981c07d0b0030b5000758018290128a5040204001d5441d110000c00e41d10641c804c032411400e040c010441c003641440611381009002e00003a00a51410710029030316000a419502045202c4a0314007c0e80d03100202c00d46080d80c0891 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 792752149 1250 792750899 792750947
    0x60e03031309021902060108071a09060714240a0e0c150a03050c0304020108160e03030a0503040605100b03011a0d05010905040b0603010606050a270305100e0a0b0402040507 76
    0x60008040d400c6284d0b0080d59108954040c030120f800414024140c451150090260500c1d1043c031074500e508528041b00030040810040c10300e41c48900040c01d0440c040d080c07080040034039219680c131f05a002e460000d0501e201c480718003600d059040e08540c020480c800089081042001071a0404055a04050307000031414411069440d4007030190000d00c080740c40c00c120726a40c26a122042d440200c80090029844000203002045400c98284a41c80145031644602030014086440c1d03134084101d1102103000402000104916030140c00d610291718004806458502840011a40418025501031260354091001d21194050688000d0200000c0c180425651806540300800050300e043c1c1d1102c1c9500b00184060134140580800c80b281030381d450380fa003107500b0320031698492003200242c2c0384030005026003642c1d0304d940c88100140d800307900176100e100b1180c10440201c40c42c8100407502c0d5084550100c01149a0b0403001c0c1e88203405031004546503440410858207116418051503203442545 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 792753399 1250 792752149 792752159
    0x513050a0e010e100e1f0305030d021312021f2604030e120706110c06130e13021309020d05120406021e060c0c120406081605070309060e030313 63
    0x1c08030604036245203415030440d4681c046070b83c8400c0da13603009825070700d110800801d030f81c2d1540302001c80e03002d01243e0b08040782c50b41b40d50f2802d0644d4040c4600c0300d055900483d20b40c1702815100860002050341c601030a8980c2126800b0521100d501640c1d00c803400000c60312801600c0c01030314041d951814088444400c00c000071070700c144101090301d0540c00580349081d0a40c2c603080040c04a0600d4903410b008200321490030804903820550007088a01601812030032448580321840170b041c1e910109607084440c107040c001e1001c041440100003200280d0080350420258440d0801540d11030107251010071003981c00d0000c00c0e403e1588050041240c860550300190850b440c0028201380c2e40345a098072804003072039440c081c0314010800346942c1500f02d003002c500c01d8640c0400400c01003406206a03084207451b040803214582280d480b020110b01c990741000200b03210242c2c02a080352480c02d10504080c003a490040406a140c0503500c28005400c5040b009035504200b90f510098003699920f0722140c4030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 792754649 1250 792753399 792753419
    0xd02011e0510030f150903050d0c02160e09030d090506010311010c0c03080f07050f010911010c020916020c0a060806011b051c030f020d1a090f130c050d1b090e030a0513050a 76
    0x5c40820500e030b1911907000c5032b1a1003c0381d55130b07100c2800c001c01c82c41c2d0750a00415003160140a4950b5000d484100f000c1d02d5100c0d540d0180c00c03003960240d0003601480d0b00d907003441c245020040c88803e04000c1c0101c041c0000401c6440401c0c203030790700310700d500d5141d503044191201103200e4604050198440e203080188410700c1500281c048610907030724400030f030001400540d03005848040003980031203084002040a520860000c0e488003061045480181540000c1240780009402842c0020305500c200101560052460402441c01e5008404410010380b030340b94a603d207043c82070104840c54036041156a110790000d20035880e540342d0840d600c0c03000e030680c080108030342c1c5a0580c0003c040c84490141d454040300d85413081d13030b11801140c020b640b0f611502d2103030620310804480c0029240720229990700c03040202000b02c0d02c11460190700050310740030700c1c4c031804080e4009400c8909081040d030304102c006c02550034071000c2c0d01f002502c0c2c04142519808030003050304402d400410103080042c01e0245 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 792755899 1250 792754649 792754657
    0xc060c14070605180f1b0f0d0b01030c0608041208100e011401020f070e0403080a0f02040b093307060f0e0303250503011a0c0d02011e0510030f15090305 67
    0x1031844040e00c140080c00c411a00c0e4000c406048006400c44014a0722010f0b0002850f040c8600082441d42e1f240440320010b02d118165440684543e54500010702c100088003900740c02402175410156610710f00741c1d44040690418400c82410000002c021070ba042205040b00d60290080744454101da43e1255088080041d104078800d005100b60340440700041404107940064503241d030300e100c41541e1191001d81e072180300a0000c41d020ba82e201003113001c04210748042c0c0b020741801207941d981c948464003040054200142004000074080021040c1203440007944c08803101101103668641d1100d0900ca40103291403c1d1000041d81065114149010088001c0d80302c3c0c072448220307244a4551000442c400d5040030b003940e0200780e0420050250303d82d011050403001515a20180c50409030590302400c0002404030000540c1d1035106c1c106000c40c0140c80c28040d00340c0510104141e1520507502c90540215101c0500784501c10381e0b21005020503001003101c46034800c0401e006c0e00d10315140050482d0b02c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 792757149 1250 792755899 792755911
    0x605040318050105120f0c0c03040303020d030f0b031506030a060504060b01080f0c0a0c0f1a0106080a0c020c040c031b020c090711060601030e03190306080606010e010c060c14070605 80
    0x412000b05496000308260f4500180041c0421295500c462030f594049602a100f607003680c03014004e180b28804100020700107948640d014000215420358080d082e140980c242102490404a00030555100000d2102c82ca1100c000720318034036121000400e00f051007281c40500110300700f004201c1130121b10340000785158402c1e604d5040e41d0350b9010302124101780c2076400d814a0081041100c84292259021b180306038007d40d203641c0c4401441e80c44000340c2e040e11159010f5220401b00400441d6001800075912030070f140014072400b46800c0c3c0082d1944042c00c00b40d48100d41e940c9009000074840d901c6a081251490b01c0c0c0d072081e5080c040040d60b690009d0100e00d2040b840300b80040c00d4107101e1100c03241c002032540000c00154031000019400b078402800c55000f00d1005200c04c06001ca41000d2403105030714542c07800100f0900340260300e824404002d1101d41030007002080e01c00703980da00400b420040b81d0001000501d40d609120102d862480d01c050701d501e50000442e00740188601a440140901e03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 792758399 1250 792757149 792757187
    0x33051c062708091008060604060c081306080601032a030f0204170f0f010902100e032805100504050a03050309010f020a11060a05060a15090906080d1b110f0d06050403 73
    0x4130340140494560808507401a003028040c4003c0220500070030403030191324070449042d418200062140c540854541d400000007070701e02018070441e541c26200d05c2102580e4000340c0d25070544540301000d010242c00154104266684154400c4445c40e0740c1130702c01030210b5400340c54402c1d14860501c0d0b1f4074240d0303554001c114003501d405100b400005111b03a09003154080e022590050380020291000314000c0002c9806000301c03c1500c0c2061400c0440c40712071180c4c000c07510460350b010b0601c280703040a480c880150040c9890240000310350005140a04a41d2610700b259481e603234450064090300054003050b80d124004684403150a40045400300451b40f50000c0341c110f50b0b501c140d52400d40c1d2007500c00d26003013000c840f01032213a80042c0720012840da1660030075844c981d503654090411070b440c6900c04125500402450050150b0040188458442d03481500300940d240740ca481005112204e000c41c813640d8609180c00d8281c51301c030809485a9000b140410461a250070081c0c4150703802079030f40c0401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 792759649 1250 792758399 792758419
    0x100212071b0605150a0305070807120c090507090e1303120207030e2b0f030207060203120109020a0e030a0b010311150d020306030133051c06270809 65
    0x554400d201e80030071403420744044855a060340e00c50700c00030507015040d86185030681c40c8062954680c014400002d511800080c81054030b00103629080a12175000809104020640d09012070361043d8010151183e0000000741500e0700f680a40d12050705130f00000065221004100007010401140608035010741c07101101003008801c060101d11035004014089030310340307060050509040c0e01c0205a0315850b518083c01544100000d004164011340c11500d00688007041310815906128200040409d030000307505010605500080a0303c050140040490b400314441001358441c030001c1d000c600001d42542e074032000741d090041d05143c1c2404181c8080075100540c604508000d00780c00480803020010710704090040f0400c801070750000c5c100f0f6034150348a01c4042260f12504650703070709000302115070240d90300350705030045141381e02640158031076840d8607050340141003a02e06040f803040d801940069601a003281c80c1c1e181c0e0100d000d004120079940043c40d0100721600c001000c150740d0440d82c0c4c88807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 792760899 1250 792759649 792759661
    0x14010609020408030d0f0e1005190608060c0c12030c03062b170f0c0615010e010818280c0506070c0e040302100c050d0b0a03021e0111100212 62
    0x5901c12445100e0f155482002040c0c0f84a81590102900140039080400e03d00c0c200404640303007d00d04140400314a81c1ea0080c0140100c01c0d400d034080302e840c168018413005103404000342d1942c0e0014116400d0400004031084141c60030b0004200840c800080c50381c03682041d068440b166001203079442d0181d850340d4141c2403914170704001400290030200c401040343c540c0b50303030781c0703d0700540400050b00e02c00b024801220b80425010292400103a010010007140c500b207a0018404128241c20a050015102e628005030743e000072510b82c400080350007048008030181d04645070000e04100f80d03455001010b00300c484c65940c000d0307803290a07000d2a5514601a11041040598404e0340002048408401c4080049004200c1d406500c14001e00580d44540150341000c804c0d00d018400110000b84c00240d40309003144140300e030350499002910700d82c0d00c150559010500000c4100201105040d0301c909103240c40e80b2035041c2c2502000d024007550580b44202c030703803503000e9009508421000003e000c00248 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 792762149 1250 792760899 792760901
    0xf0a0804030f08040803010605070c05040f0203071803030804020607020f090c0904061a07110109030b0a05010302180402010c08031810062d050402070f240e0c06040519050a0314010609 81
    0x70240381c1103803d1902c1c50740381c20320517101d561060000b1039034603404100016880d560b80c40ec5021b07403900e00c00c01590301e24018400511000c00c5030b98518414680c800e050000c030b940024040d80c0980e041e5022903482c3c82c40d00028800d50010040c0303550004007101006004801c10b400340c50980c1060710203000c0151500440540200c4100c4860300e090010b111038004680ca440358501074000c18109003100c00d0303c90701d600c0c0401204032050701250742c17105c2c010402c6003400815a0761750031089000c1d20b00c41c00d04c0d6000a1074402c3c4100003414020000c001b05441e956001034510340c0904050440e0b1105203000802e0f0047d1505104000708a100b001a0b805010a00300f00a90709100c95030b100740120f420002000002e41021300107071802c1e104501c0305000212008520484010b0030501307042d2007440040701d003080e00c85011218245810906030502280c544009403000c0d168116134486d041c5071106840800101ea07039015030743c004084a000030078410603c00b8000c200902c60000c0c410140c0301c4901c0301c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 792763399 1250 792762149 792762151
    0x3090706080c16080f040321020c040b01050a030e01062c1501120f061a071506140607060e0105040f030305070807201c1701090908040303050f0f0a0804030f08 70
    0x507202040f58842d400108800b0003081e0a16003621124101038403511809110820042502808681c4040c1158196010081e154000d1421102448040d9940380001c10038001c04174123905168442c04c01658001007904100d01030705c0c4082c0291a40f4014880f0711049540c000c40c1008540704d0700740412203c041c01c101c00850201c0c1a100c0748034121404240d480207222404807030a44599030304001c03408200603031520311145158142e1903140c1100c0e0904000c002044500f0384001440c14004106d00700c0c81541501101c03c2c221020340d01e400c1d00c0c2c141440a4040c4030f1100b04c55500c2c05041104000c50045140b40d198040d50341000203a5407040d0959075946d09407444c0022907828941a984010504107280030004118140c400d50201d003051200119180030303517240420039622480c1c10794646e8000d054010030364001c0500c0740c0c0307203a80c944821350700c59400094100403000414001f0445031000316031070000001203580e075a20000500402d03078001600c04400180e142002c004083c0d21030b54540b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 792764649 1250 792763399 792763417
    0x409060e0105030a0f050a0b04080901030c02061012060207060f0203090706211802030a0b15011407030e0a120501060f240f02160b0a200309090a020c010203090706080c 74
    0x703115115080c0c035080905d81400b40c0850307051050070b08a0000030044648540507601c2a02061740b900c0e104d4001505403694046014210341c402c004010aa08200315000308135110f0284005041034981082d0010b0302c15904e014241a00b45036440030307440c1440e070043d80301d94aa0015500e20030b44030381c02222806800502602c81e1101c000c00c9004460907035000341c2d010201c220405102085a60210b03040046841c0251108543d04081103a0750101d403034600400e81091a2045481c01011000f0106002d102c1014042180c991a46500c90b151302c001c04d40034000310142034180195901d030007030192029026203800c004818000045070401e8075045c41c00d56039082000342060180010845400702508850350031842030300c0007102c40b208000440c0c0c01510070903000d03580d43d900b8101d02801d402c40402d8143d5043c556018a03460714040030094a100d20700c101c4440140e612903055060190149680071040340d48000b0901022800010b414030440d00107840e050f1241da910074451001c0e0003503280e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 792765899 1250 792764649 792764653
    0x2f06010303180303080a1104120f050601051c121803061b03020702240d1e0b011701140a0b0d09030f08190513050a0c1d011d06030a12050409060e010503 67
    0x861320340010b80d000140021f0008200c18140341d1381d40010106801a0f41e1b003501c40e08046d1807200c052050901509003d0002a20211300b084080e203260000e40c824400043c001da0311304482c181180d44035241580a021440d0340000b003d50701c1e0304100000304100d4200000000c0c161030702d1080c15001c0d0090f900b40b980c0042111440002d09002040f008c3c0c0303940c108d009205001c02580c0c2215501d88680b090341e5031044d51003441d1040c40701c070317090032211900c1509062210010809402c4405070340700c141583d1036015039003014140d85010034421007481d00134403600070740812509140364859100409090003a65030040a0503480429502c0b000180c0301e082c821103103c01070701c01ca1002e0f07170092034012030304200c54034039034200340ca0351401c2413040f0350300300d03090782d1242d004100a1184402e090511120410583c4c03d40d49010021070b1404819003e070442c0d0903aa1300080c0d40b654050003004549504045081c100581203c0300070540d50050103502c040d985490408202018005c2c4094107039400540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 792767149 1250 792765899 792765901
    0xa12140a0c0e1c17070f081b0703060212100b0a05160209040f140102090609041805010606080105010311091014040b040902120f090601062f0601030318030308 70
    0xd06000a400041c018100344046803481e005241c40c1c0e43d28180014482c0700112000c840c5501c0c4c420b951300c0549200502c2030740c05000c440007241001100d403102d59400b0711708a5503120351000703000c003a42d02a035001945002d00040081403107015002443c1c41c0c80e803528407601941c2d540507e51a28400c03800b40a000c1142400005000c0d80a40004d0400000e0440315030100b084590001d11320a0b82243c044842c50142d0841000b04141103d501e4440301449000f50304104a500110b2a14012119010300c91038607080c1a049402494941c4511541c000d8000d0041d0340d1150030140c20081c00f80310b036500080c9059088604884000d05642c2004802400301040007800d03501201c01d03a81e00c55007050b511004000004100d2003c5004100800003a40f0158441b000311b442d0401030880204400c4445500e10301b0440050008190603064500600f402c00100c1641d2079024580541007228010995600c2840c1035401000144181228030039580c0002b26010441c202030200a284401030109036110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 792768399 1250 792767149 792767161
    0x70801030b09010b03010e0106050301060608040b06090a0e030313140a0f060b060f07030905031002040b0d0f0e150108070611060a0b04021201152a02060d09170a1214 73
    0x30090903040001c00b800440c1821410000a003195101c000c81e1754a44c0d5510030804c2a42000e0080400414250410382294507190f01d0b18201039500404039840784030f100d0001a000401c0380d000c0d081c5810840300b160f80302d01c0c041c0c3e070300c0b84126054142940d01802440000c1450a400650007141d02e91040104070900030603501c030005012500c0c0c016512940902404901c41c1c440009070240b2802075a425a18601d820306042c24a0088100300b14041c0c0100028000e0840307001c00c441e10440300b88400a40c5024245811b00180018140c1250301e01071044034104000e400610107050310b5090b016038000e80d07981c81043c0e0f40d0400003098400240c004100144040c0a04c4d4000f01c840d24024001528100d0510301404406100f60084901d107060040c141004940c0940c1078013002d5010701c400d1021806042d8070241703000b01e48a00070b1048030000f036145074403030300e0303401c01811241d201e03103140b040c24500e094204032900004804000503a5591405240040700c0c0205048820345a903090b20319290741e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 792769649 1250 792768399 792768413
    0x6081506041203051828050303030106090e0702070b040f0512030a020613110301050a02041e03081804020906030702033402270907080d0908070608180118060507030507080103 77
    0x1051400170b0a09601180c07242c2e0307441d000d10880410181061144a0741d80b190005100c0040360f0b00114081d500070b100510074250400300180544455060b400050781d11160200e24005403a04001c01410000c02c0026025100c1c01001080e41c4040b5800030000c510450450380c0d80c0904800c40d40141c0c084004a074085116420040442e4011441c0c10740943d20741000c01c0c03d590083d2114100c0039030009042040e07140c2100102c8140a05400c0c1c503414905d5074851100a000c0c180072001101200f02c03810096544640c100d50041801418181e1240b6000c08080d489801038403000454412455203038100c031551441003140300c1000d46200c0f41001642e000c0c88103040410f0f50121519201c00003e00c80500030100d11303442000780d4070040070500c1c2403030701460402420100010038407042d040180051341c400700c3c1c840143c524900c2e008043c1d60b02d0352054081d00c1c840e048460303c0c070f5207401c001002c07802c070300091822210701440c810702454880c10400c03011608100c40180000d000440140002140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 792770899 1250 792769649 792769657
    0x110c0607060b0a080607080103030e011106070e040b1c11010513120f0b090c0a08071a0304080403140105060f0d05030913020d0c050c060702210f040f0608150604120305 74
    0x406000143c3c2c090710b9281c501e16103601616000d021034008001001003550000f101020a035082ca84198901035003a58103580e000c015001030140300b5046150121b1ba200c030792140c07500b04401000741c0b10070100c2c4803c603488140c0105041d03841413154419071100f54051006c591100a40d4001300544c0751400c03001f581d0750398110004a60810001400d24013040c01ea070b1f64079000b0052340001d007144400d180104115400c15034032501098003e510304200c4240200078088400d54003a414695035a5607152081c014440c6d9040241068196100d89030700540541c09940708010507140d03045100709800821a0300d0488240040c02984100403e8607542011140c40080c00700e0114054108042c43c144001510f0411a411002913004030f03000080c3d4200700032640e0801c0c41d038001390110f03410920420424600711072211480d8100002d00e00300c1200078104490040900d1500d039484141c40c0c0100401400003030b03520007196250142d000c4402e2810000303c4040380e09002c0d448883d0710b001d07a000e1301d40f500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 792772149 1250 792770899 792770921
    0xa090c0203040306050406020c06181b060f03010303170c071124040810050a050f01030206031911091e030721170a090609080613060e120a110c060706 66
    0x5100003c0003c0703103401058001c80c031a19000d03031211070340d42e80d03d03191a1005003c0c11140c4c0101d61103116501e404159021080b00300900c00b00100b407200c0101e4a41d1144144d400d03044031001000100781030303001181500c2e4901100c510502611580d4a143c602e0003032240c0134010120000c0110480d1070550f40301e0001103000300e00c9100c1c56104620038140c07500280c1c0580c04076006001e505520400521540f40c0c0002d4100080120b4104081e9501030481e05001c000c0c0182d01c0000810902d2440350103603808001100c0090110003e42c5230380c1c5072036030403034094207025a2004044055042a010918a2548000d0001c1100a00d00038060400e07540010b1a641e103803140584240109002240d11460312000300111640c0300418540203008001940c002410800031100c14402e00d4800701d200f5400c00c1600a00190580b45401e0800c020310f042c0c0c40c60201ca00c1749820410700d00d201f00300075010b240060349030000c10301c400001850b207070b0b40c5107144d0590020b000c000000000d03000e544248c10b410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 792773399 1250 792772149 792772153
    0x1211071a0d051f03050106050414041104050408070503160b0c030708070f030209040906200313021e030a110112021c0f11120405070501030209030c120118061b020109020a090c02 78
    0x2044039807107040803c6840e0800d4a041c0d4580000b44030b981032a000d038022942010b2202c125520b0031b41c6414400c5403004010f030b441191200049010b1103285003d50388456001400d6a580300e604c0114250481000b00040741c0104006000601000e24101981c2c0720354515102c55669940388841150a036a8441d81e035400d0640c24011780c4075580705d6100c1d4000c801d00c1190005503021012820940314506d0014085d1000c40400030800103505440f20752403400d5040c0c4902d00001011500710300c00711003140c4502d826116030083e1006000c2100354004000400f03032950300142c18880600000e074441d15400c58903130a540b07040760b04080810743c800d800c40100d00740001120207440a040302c041d0701010360160714801c2c0c0c01c01e10060050500044004100908003145040c20300d101081c3c503a4006011284a12404c1c50080c20030407003034001801d60034140791400007010b00c2c1d2800d0030083c0480402c80708004c01289550007100d00500c200b03800640c00402d04052245005003000c0540a980b039458214 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 792774649 1250 792773399 792773431
    0x90201020607030b13060f091104030203070306181a150105040f0338010602010c05090a0e0603010e030c0f070e091e1606030605010305090604030e1003091211071a0d05 74
    0x5c0c1d0301d21555000e8808010032075040c0c2d18118820096404145c0300c03a001c5481000104016a0f00284450449602c0003000c01c81d10005441c18400c641400e40182c400c030300c2182020102c2a07030500182c4078041c40215101440c5038007004503050b014a00a030100c040081c03100340046940106d207410758006071000f03030310f2201483c038020502c030f105202010550b058402c014040f00c4c0d020701685400348050303d4110b060040000c0000c0ca4195944501000141c108000c2081a1000e40010700b0034000750040740d692b502000d40c010740e00c070f89902c50416103024501c1c0c0030a69a5080d2074003400f03601c1d070030001d102136241c00e688044a0000c03a03c003002c1da8450030200300c140f5048240101c005100944002400a103040000f409681c40240041e1a0b6040756040100194004001e031560460544030a02110005036050f0002c00c1d181002814090031140c21071041580504042c2c500d0220109664081c0d40d42c00c0040080900e445654074030040a00c0513880484070f960040c0e5212105004001d10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 792775899 1250 792774649 792774679
    0x504031d152a151f05010509040b0904080310090203040503030f10120302150106081b0915071407150e101e1d030a02011416081b060a090201020607030b 67
    0x110140c12031410b20030790000810301504100300003e256200c9009100301841c10380c00c03500140110110301a45041c08070100700014107440ea0350042d9800007014244030014181401c1030706054104840c00c03105600030031400700d1000540e00a43c2e01442e40070f402581540c803042c01d003488500700100502c0b194039280100241c1095070243c1900228041c0c0c01a0442010040d400407000005030854804e000c901000c0c06807192440c84075100052410f03201945856144000803000711084d141c45005000100b21403051021102108101445000444000943e0307402117112540380d4640320000f0907040180e803119420b1200880c102046507207040c1d50209080913150603c44040400b60700002e030081c0c0c910002001d0811b00b000c50700c00c00c030002c192441d060f0340024010880c54000110015001c1408550309051164001d5143e6000e071045880b100c2c003041c1c04c0320040c0e070304000304881c0c4103a4012402d481c2e02d81c81103440b11501a80600313100c3c0e55425007a805000b2030010340390421a1403c400007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 792777149 1250 792775899 792775957
    0x409020a0303030e060c180906011e030b0307060801080a030c050a02090c211306150b04061205010b0f18010e1f02011b090303120204180504031d15 65
    0x1c0c502c00e44000804151030410b640c03800800400c80310400d0001c0144031500321512014220b009003c82e807092190f42c6d00b500407541200d581a1450384841003000d0122401d80541119080520a4003240c007c59518902250070444c28403a1f1509a0021000080440c0c881e0221202c590300540440300540c00d0383e80401e811613812079000c60f202c100442e928842d4403048100c401d800400c12003100003410140c0d44500110f0064000500302541c4808406814038543c032064004e0207088480d82d2107a584000180019541000352100a8a00000800c3c1000110287c402030070410624074100303608207a030700c41000710303280280307050240601218001e591019811801071046401e020a006203140002e400e682044000400030b07886540b00c07140c0664400c1414080300d8141c9030500007098107180202c0203102d0354000d905100003a901c441400c00440e041540214860f6894000030020881045880d0410385841c42d030080d411a0702c1164660304001501e4210036020f0484620b0f596007038070a07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 792778399 1250 792777149 792777169
    0x15132c0a0c06090603150302100302070f0507081c0504150c06090606240e1c1a0426183f0705120703060507090806090705040c0f080a0b040902 63
    0x80c2c0080e89400050041035454041c00d41d01402c4600c0100b412410350340091070507503600c8044010140c0c081004014001030f0300d01030840036040400d45850940380c08001d91901244080d210400303400303115074201d0900c00c1c0200d44c1103641d140c41030401540b48a60803540c52551001c203035891a2103008900100e0600e20640e002004840b807100403900004808076a050180200c40303091040b82c0da4600721b0b949131a450368003920941910745c1b81e451034515042e00ea84524042101d541221502040300300035041e010041224000c1c07a82c511500a000800d0034103124140c6140d10503002d4420034540350418440180b00300c40001c030441029110400c0384450403450034890041e040c80340100c002c01d42c1040c4507420240c0001e540b981c000d10965180c5a545400d248402000160380f00c00290350288511803030300141c100c0030207840c6a0305000700040d80e01c0301e450280500c12890405400c040302c0c05840c0b200d03450141a10740c82c001d555000c400000078035440e8441d40c2c000e80c41d07401101c0140d071128140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 792779649 1250 792778399 792778409
    0xf190201060f05041103010306050606071203020304020316150f1b11040b0402070812090102041d060a0605130b03090a02030f030c0d090e040b041a15132c0a0c 70
    0x5089103030540c0b241c00c079405a40928044c0d4138003400600305810a01c122810f40e03400841c0400d454450001040c0386100f8504041c1070394400310381104c0d00d19403580055003d24021012251403c400c80c1c48200404482d200d461580030240b2b001142c2c10740036a514404c1000d43c2d0504228000549071101c02d164024082280c25450f18803000390f09241511416190241c241c0f400c60601c002c4d99107041e40d41c429600520381c4030000d040003680200094049501801c0360940011001c220100c8000100e10143e40c05032042c5159440411200d104405461405900040e11540c0038503100d00300810743d001820103112402003080301d00c00f41e101003003c0c81c2d2020f0260000e5a5a4400c1140706080c101100204810010864010030440745900300a039003140d04514921440d8540c1d2903d64201880348031022424820307401000030119050503424000700d0700303681107400c42c181c850000d401c49040481c00340d00184810b08104000d4042401c5085000d0140e049a4984405480b1031030401c14580c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 792780899 1250 792779649 792779651
    0xa0506030114180f0303060306130c080d090302090a0b0120071509170c22090204060806091510030b0601090b28110a1e060f060303030e070e0103080f190201 69
    0xc0c0002400800004413410500405141581001800286c840c44080d100030000c140a481940c1400007000c1c0300b600400c1c030202103c519501187c0d0207070500d5003621050388a8160240000d4191180740100702d10010141d460301a2004c2961020418602035010b401c810304c07901401040b0b2082010750440c2c6000c3c680c803240541c51420030040030741ca250a202c90752a4005a0b0083d4041c2c540369510312201e08440d038000d0310560b07031090000090060740d0002c0d610030700f0020005043c150214040740034405078030541d0b0003212042c48030441583c003510781590b4207203044030801c0444c50450030181c00580515050344000e81c2c5481c00c00e000d070001c964010500b03805620148041209006c43d01044945080c103001d64044d10031070075280c0c07103290005040e05000c10044400000444014178050764030600c204a003000c42d045c04402081140011404a0710303080d465442007400007550070458100d00c66244a9a00310f59500245810003400090540c42c02e2203d0303e5010006140706480d4285980 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 792782149 1250 792780899 792780931
    0x40b01181107051612050c01031d03190201060603060b16170309031306140a0e0301020415030234030e0d020d03020f101e110403020d2f090a0506030114 67
    0x1404c2014080b81e4031080e100c103035080c0d02c82e0010b8000305041d1f13415202400c000070032000d10103034200381c00034542d555100c50000280d400482401c00c01e0720b03031407094640c0c020807515446403002e030100c44040c012942d044e1028815400004242c10b09204018031400300c401142800b19010b3344103401c217843c0046550000f18140100080200e200001003501d0704c1c02c03500d69a11b03c40d43c403000e8481d00331298200001c070540f18242e5202501140c0042c014101a0b60400e004004028004c0d0000f25075074502203003088403800f05440e5030600c6405e90002038075010801c10190340a0304c0132251040601c0d00700d241492028050b076510480001e00b68001d402601420300b01000c0d850404189010b007803180c600d0518070303012048000821809101e5019000602c0509884010400380210781c0020b6100407030488040c10409065404a07101021180d4502c0c442c0e40c03162200e0003151041242c64010326010006a08018542c01094001c8000340002a81d514658031100018500b01c4250200b100014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 792783399 1250 792782149 792782173
    0x7020d09031113060f150f0c0b040203010b06030a060303030e030703020c01120f1d0f01140a0b0105160c0e010b0c0c06180409140d03020705060114150d150509040b0118110705 77
    0x6000b140c0580500e260030043c3c1c03001007d0140110350081d202801d8660b0390707400901151001d602403072071403000501c99078a078580940c000340035000601044001904203000844202c0e40001610152541900030300094400e00340112050050414074001064440040610b002641e2050741150f900c9414800310b4041500c2001380b4000e0150704522482c1e24058510308500929214542c00c910340602c0800d10640110040340e490048186410003441d04450100c02c01c80c80342c0c21101290100511840546e99030b82542c0b24030b0190a90840346604200700b514407520b060401412162107004802c0e03210340760b60000c10102d0354402c004503554100c00c421030044003020005031941048a00d001e52600e09103960383c03500c48006126900c94101a0b02154000b0b0341d0712200c90f90000d000c0250540c5034031840203840d0280c008600440e41c080703202c0e1008a21400c0140324248619008040c8000c580d1038085540c84900c503000c100007089a40d040d006078520024002031140d140520002d011160a80c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 792784649 1250 792783399 792783419
    0xb03040c12061a0105161e0b0f1008060408040306050a020c1501061404030c151407060504031419140915030105091320010e0a0b0a030507020d09031113060f 69
    0x34041c4c14450b05100081c030000c581c080001e01d20ba441402d8003071030110320108003002510840c00a2080200e0810850074415030788030540b1802c8403100b505240c03aa07400100d0b85404040d10080c0030603000300010310201d400c03904880d403c680540001031901e40c03034581190030520403094290298411000410407180d0281456501c000c0c44a4114a45481e5548148003000144585041181d103044100c000078020000c4035038003d21658520758684084c90000c0c010702d0110303800c501080e400d88a960102e03001c04241c403508031420504840c10324107100d09554100c2e19100030658504100502c0c04581c4a41102801d001c1c50103580703d44a50400c010414050801041e41d900b802d0070b01040d0700032482001c00b83c0a99030304040341940d401b620f0f20049403890101c160b0550020003003800013824048907002014206095a81084551581c260403a1903511440000340000c0b1380d1041031020422110101d0700400c00280312014080b071101e1884140d90941c0d00032080700c2c80c00c3d04104016502c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 792785899 1250 792784649 792784691
    0x180b19180605070f110909031e0a09120c0f080c0906060c03120709120b011701090b150303120a050106090b04050108010608090102090d140705040506030303010b03040c1206 76
    0x100ca4a088800d0a011008119000e40500903000310358442003901444181020058240c0010f058032425262980000d0b0340e0b0b030b120030408403800244d002c168010790741840a9529101841c1d030741c41c180d03d103454501c50320000c00010513111011200000101490b0701c010200090013006d0180290701c00c80020055035010080859000390410401c41c100c403070300842180c0103807462410381d68180e02c1c0e400045400c520b154102780c03849014440301c2001e2241035404c5604994818855440b5000c10082c4a820f0300d0420200030f00d52004e2001240c03013110303c9409024180c0d0040d080f6818101301c0340742010f001400f546d0380200305981e480140003c5034802d251101404500345220b16180c23402c00001c0141605100780000c00111501140000070b003901180c0002900030f00808030b881c210b052601c0310728210381d64008a4130a0700c40009483c180707802500c0c400c00e0000c0140d81180e00c0c11041100c1c561000b03204440289aa000c08180c0d504d0001024a201f8000c1c000001e10910b1840e000380c01e440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 792787149 1250 792785899 792785927
    0x3120a2a261503031306211e0f0b0d020103200403060b09060102030a020709151203030b0108130203070302102304030c0b0405032113030b06091e0403180b19 69
    0xc10401c0301100c017215001c503402c5404c0b903d040701142c035041c000340f810076200c00c1a000c1600d08048544118010110703d0714001a41c6010400000c100d400c8000111905c0c86107040d000190b4090000143d80203603c04200d4202a41c04004884601140c0c11000e0388a40c0045542c255207900b00c0c001030030310012481d0300c41d80070300045d45000c0403a24042d40d14000c81c030801030400c2c0c07117a2001891000c00503564004100403102690500130601c0e029000c0c00c107080d81d00d4002040c000002c2c0014072450422568241c014025180c2d00c0d095400b40205440b4041d14601400888420f00c03202c003046451446000005071203517500c80c2d00714504803940312181c0d444207921540c144424017a503a00414500d010b403203030842e41c0c807d050803480307840c1c0c0ca40115100555202b0894000000340000c1e51452842800308581c0c030b034026601c2d43c50b078009079294000c0c142031412000001400003030040c030040200c101038611820034542c0d14580d998956001801c040d4030002e0603211091200c0d00112142e071214 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 792788399 1250 792787149 792787153
    0x10605030a05060a09020a030c030302010f05060a05150717040e0108010f0c090e040309030501021603020715020a200303030103030c1e320303040503120a2a261503 72
    0x403031507240c2c181c2e5140701800c210b240550301c0b20050119901c44450390011030780710364074919090b600d00b4082d0080c40e520210021941c01c0400049161030030341c2d01c05007a101c0007846803c0703012601a55070b171180c10040c01207400b5a11700350340010821500c0c020f000100072180300440d9a604003c0c2050a540000000051142c103021210000541101d00b1100ba1411902480125661400c1c00c407034410700c6910180140d4400210340240d010107102e1900c41c035008e41c08950703071556580d58070801842c8245550340140c00103801c540000d01c9095900480c0711004102c40d4204d180d0341c00190075588283c0c4200c000ca42000119010407050000d03112601043ea00350003280000c40d107034405000c140000d810004140044244543c03010002540706524504003101d840e072401d45049030341d90317009079051030705d12000800250b0088060300540d1102e04803403891000c03414284102403250510b05603003105102034101c00c603c030540d000b65101064680c2d18919401d5040644490300058003a0042601903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 792789649 1250 792788399 792788413
    0x6010c0b15030a0231110f0307170123031f181a04030e040e0c01080907120507030c150c0204090c0503030d15050a08120d060803031603050c09010e01030903140c030c01060503 77
    0x52006e49040e03d0072030701e18201040c0d070307991007490484003441c031441340d0480c0c51080b5002059080c0c0d04540d1342c0710724000e1228000c014423843e04040d551b4240e00001c20311030140042150300c801032504a800700c0840281c0c820241b100541d07c5e505041d404030068903040403404104070078164040c0c0180b400d0714042d64208600b10034151100d8407030403041e0f04030b810302280c0d5010421141b002c11405000740f0a2107184424200d117440c10a840c0c1403684000d41d000a100700c000300d410703200c886040500400070740380c002d5540500d030309000141c1045202540c0f443c1c0d10b140d0000360303502e040c0000c011900460400044007041412001220700340b54101600566281e4000e0203440b00005411501451103490107440d09606030011010701565006201180804401d0154203480d00d000e000504219450501c40c0369514160100c1a0142090150002c0c00d5400803c40035400b036405074094900030b1030003414080e10556410855404002440c41a60001400d040081801c1c42082d0140400320064014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 792790899 1250 792789649 792789671
    0x21008150a030b060f120a0b0405100e0d141903020901140f0a1b02120d081b0d020c011103130201120b060301051e0415030203010506010c0b15030a0231 67
    0x1d0f41600400041c041c1842c4145129035a0700d00103003194049195003100e107046003519100021074420384003191140315000c08590805a1801006030350307070340200140f8812180708012640c0b4005a00d0782400c10344c00300504866480000c0d03070291711190688015a454140c4070005040f1742d240c5081e02138510301813010b0724040ca2101c040314240c00c1140380845140440b01d009142e00c1103840320007540501c2040c0b50032485500481d0b0485140191389418801e695400760b2581000b24281c510308c010103003040021011031030b47d070241c1204c0000e28000a13030400300480130070b45a44241c3e12640340f8072001c0b14141c00c42d0307401840f070b03050840c40101c10310044448401050040c0010f0141ca407058048071001d9110b607007012140d90f01c40c500108107100c16110003540e802070b0305a40c0826030180d401c140c00281554000d640541006074400840d040556a22440304a21882c4100da150f00d0700450100f880940e4032220001014010003484c03021992070351070400c9408942c5422118144d050000c2419 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 792792149 1250 792790899 792790913
    0x1c120e03073b010504150504050a06030b0c030108120f090306010f080f0f07121a0f040c0902160303020a0c0203070905090f120a0c110402030414060705071110020a021008150a03 78
    0x104440c0141c4000c5031b4540380d100b102d030200001c0d820458009107010204910060203400860840340680d14006e0962580140303001648024040e142c4103510084c0c80d81d01059403140141500805042c0c11030424402200180c1820300c00e034442581011618407c0c090082c05001b07040d03c130a03540c4000c0440320b01000d02503498150900c6020401e0708105107220500050420307900d51070b0048803402401b840c0071030b95140140020b070b030103540c0404c29a00c017007880d07503007031084601c6036141c4801a0007110080e6002c030040c0d0700c604245801c0141901c161801030310104070f003034050104200041100d180920b406898485514031491031513201c003086002160342c80c41183c0041031a407034892007034403190604007080916005c100d42c00c07900c00410013060148501107000700d80d0400040e00c005841e4508201c0d142d0055000c00b410300f8510703040110711441c054000400b524070b2030040d01da4417605900003503507222428500c440419804410001c2c0542440c107440fa02c0724040390304211007800c54403808 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 792793399 1250 792792149 792792151
    0x30a0b0103050d0504051f02030c1032060f03010b0d1a100308160c0e01090903090602162108071214030c0d1e020f0702010e1c120e03073b 61
    0xa002d40c1d0003d180e420780c2c824030460300440c42b0706040302c20850014428000501d058100c407120401503000c03c2c1814404c03a0907500c011500c00400706500e803074690421148030300040009505650320f0030015400c3d20743e600e201d456180122182440c203510403a100c850800d0040a00c841c506201c0c0c02031000031024404d40c0c8454800d2600401c0114140c685002c8942c6590800304900a04500000303949000350800d40074280303e0b65502c52060f43d07039081a41d0380d011040700b0044a240707407135051088114009442c1c02501146140c0c0000110981302d10540c0c0d03005510139104182060944440a5008605443d208a101005901d1440c180e1002405030007400c01d00c034002500d42140900401c26054a544070403040d1004560314118a1500d100a0f40600000c030b0100307440040e10541454010301501c00b0a803d44148481d0310f50550302c085024000400d04802d00c042ca00d2000202e842c2001102c029140841219075034554268200641070f0030800036600322b001c40c0760f0b1203180c030440002035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 792794649 1250 792793399 792793429
    0x1020d080406090221011a0907110118030e151206010f0e091812043008040b030411030a1a13081809060d110d0204020702030a0b0103050d050405 64
    0x3481540c859281c0040a0b080842000e58814440c20100010108020358800300c030b00d404d0000c00403456284050400e085800007101d50000e484400100c030b150046c000d5174040c42c920400012820303100080d203040281e00c0a42a4000707498100050501d08000d50400c22852005001c1801d1041c41c004000c1808002005107040151072420400c0107030290865100e07180008016248919190282c0d81001e081c900501100e48135032000300700ca24a85200b1602900e0200c0003400707443c8910303010000d030403491a40d40d103043c8144042107404a040030002c0c1000c0c0c0740c210705140d50b134281400d104110307410545a840c40b84e00040d1020000450030076010160095905d01d4032002d5481807039101942e880958040c0140c08005410503c4442503205820030000803980f468198550344140640c0d02c007940b100801d2150700a01c409143c0c0751807940703c40d41d6840200054a012070560104e414030310542411110820048018001c004042c050310b02520007a190981c242890039001079249042100c034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 792795899 1250 792794649 792794657
    0xb03040807080c15100f050109050411040b0309070f0b251412090405150102030d02160816021e0307090506030c18160207060e01031d060106050a1b0201020d 69
    0x903000030080b00d0002e0307414510f18001580c0c0e40c802c20030684e0026440850394403980c0d0b0b1075108040780100001c1c02c2c2c4004c2c2d95040e501d0600407810030382800001c101100c0030a80103038003030000041c50008079005611510021020b030031507618004c05141006000d80000f0840a01403241048075801d0b06020000500c83c070401e0304444095082100c90402070003c59107150040c8802042e444611400400c00c080d800d81c0d04000b640e494141600d00703d03010300230b07550042c1c0080024004d000140c2d0041d04001141d00446400b014079642c80325010ba010340101e2228080d0344c4440d41c250b191200300e460280c80c8496003d044120f0140c0002d40701c1c40030303000b944801a074850101d00d0a07281004010440c49000d094014555076401c0e12080640f000c0700c556803101a01c00c1e00f9080300744041403040844042d92240a003e912090055003d820100101d07640d52a5100f500d1504031020000e242c000e02154589036610622654018055144410025654402100a240141d070f0000d25841c000c07415240c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 792797149 1250 792795899 792795907
    0xf0f1e0c01210603060c23090d02060a021c09061d0307060f12050c0702100314011a190801050f0406180c0c050f030a030f2c0a061103060a0806010b030408 68
    0x20030b1000b060a90009030007946010300e40c00e243c6400045004c80c4d000000e0b00103030580c2c032000703d6501038420300060703039001132804030705d08018200788015000e288280e0050315003560103207294202c1210303460410000200d04144c20042c59411a1841c4040c01d0712072800c02e204207042c0c0109680d1005071050f5001c0205040d1001415489000c1c1540100e03003041c4284400d0500503900d40c400e411580c001d82c40340441e07410b035039a024060301c00c00403104100081400f10741c0c81d01d0803d07d144200c540200e144503a04116105c0c00c8038130f40d15520f00c9900d0684070642c4a5061005008440c0c2c2c00f00c5075540030b686480c03000d10002c9036810b020280c0510b40072000c582044008011119a00340b04001403661081540e02c0c7d8002c80c012001c2c04c3d61000c182d4040080d02d80117940c070400e441c06558000c462520b0400624041848221050011b1035108203c609102044d41c403001181d6203100c044c02041c0000c07013440924540110048001c2004a00078001941040c03030381c060610026100409100c4002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 792798399 1250 792797149 792797207
    0xa0302070608090c090a140709060801030803070309150603110604050d06020f0702060d06050102211e090d0b041502040308042d031a2a0306030f0f1e0c01 68
    0x404a803407003102500c0394041c0d080014010340031f880d241741902c034803400f440c00081d1264401c08800b02100e0165079400b466929549500c92582d102505100405489242c22008141122201586442001000a499861400c1641c00003e149400511400b010041005181d40300b0120448142c3c002100681d0b5407034aa0250240380300d0024020340100021030801c2c06245158400411558284c003900c1c0d050464011480e04400c5840008080030014045c00c80001c1400320681441d100106803d40f6110508000039021440010104c070400c0700101040200031900c0954210303c0c10403003065003814156520400180503030b000ea100005103205024050f900c02c564882144c6104c281819120307512030400030b0b41c081007028204218003000c00031902040294552010030345030211079009040700c60040000710b52002c0e120a90500c01c0c1650a554402c0c02d0040c0324150f554070005283c0d0080e815810110404461110700d4950410000340545036000f9000c0e031100c41002c1c803030415900c1c500c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 792799649 1250 792798399 792798403
    0xa080607050d0209180c040914060604150c0212011e02090105071b090504060606020f07030203060c1315050a110d0c0b040516080706090801051009021b010513030e030a030207060809 80
    0x212040034180340c242c05006d4500c8441c07005106450103040240701c0c800c025440c0a03640542078808540141c000c00040001120302001811503501514003000c14a55680006400d000d1000117062507035510a104940c1155640c03450480c0d10030f06109506098107900064000c0c01201009040c1c40341c031364000c0040c107011b4964440549681d25003000f00c1d04041c00e154009002174050075016104002038034202810019649044a9000380100a00d07500d000405e403243c3c10480e07103030f07881c1171805002042005845410b4201100280d40b61500c0314901c1c44001c0130904401509410345d04400c10207440242d22010089031690042e4000d009502c0c0d500d01342d450101858203040500486400218019074042103501c00c44032180d4400388290b854625081c200e0350203860068840e840001c08011103183c58010f8100929051003c080c0e85008a84a40c00d440701200c1d292017220100158400301608404120701c50075050b0010040d444103030358080d41c0c540ca540501c0040c0081240007403924101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 792800899 1250 792799649 792799669
    0xa031a090c0c070801181101302c070608041502090126060a06050a1718070602030904050f040b040209040606080a080409060812040b0f0706050f04020a080607050d0209 74
    0x842c000c1003034001034103c0004485600e0401c543c47c6000e040303148a02c0d8491121011702080b0a03100300c0950149003010603004001c050384428041d04d0f201e00c9070542a04802c0e8030b040d04070609034404945801d54040f82000c2c15500040e06001c1c80b40c0a010106002180c050003042c03158000581c0c0c0d40c0101d0060710300043d1003840f00000e00c201800da44c0307050305d99a1194042d000603651090907a4644205139032500031520322100082e048501e10224000c0703069035641090050b0803c028414070b8107030301810446603801c1000503034400207441c0c0403801c0510032640e102005500c442e0302e50805984400344442d01a002030f00c255a03040c0820148038040d030081008054000444030300d12040d107000f002542084c807a4809062602c00c001030b00041c0130130348074017910894401a203064100114000160030031380340002121805c1c0804400074071a48074050241c004418480f14519091041205803006500211017503000780c4140110540c0201c1176030000d402c51341d000750321180040c020442e4146 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 792802149 1250 792800899 792800909
    0x30f030c02070506032511030702010804020f060a050406020c01020c0d0f15020313020f09070e0904060f02041412011b271d1014060d140702030a031a090c0c07 70
    0x30002041c003013201030b010490004800700c12605c0c000301d00c4120341513412087e0a00ca03008543c204000e03c0006611030120381e940544000c0803604031180c00b402007042d070f80182400d42d0104000080c24084950104400c08070400c00344000c040101000000c900444141d5900611406000401d80c0030042d0641c854402000e40250031901c070701e40500790300042c0c01451410f0740100e44071840800c0b1802e046071128441c0342c01d92108404403600b00c090000c071400040041e113517183d480d81c510154180500080009214507100200c008460104204001c1c00c00f03810702c03c05a15041649c5014130303050031008009459402d05000307007031034800f8102064041481e081840f20810b9070100b2001685020500401100300c0341140c0340c0d84150f410b01d80e1180b6030080c00b00d100b060000140240c509000106414001004003103201100680c45a81100c0103a4070039001d07030004a00c15618030741c148a1302416219410108051480c0d82000c07902d641805400134500d0240058842d40c400002c010f204011b00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 792803399 1250 792802149 792802159
    0x31c11010c020c1008131113020c070f06020a1722080a060e12031501050403060c021e15040f050307050709020706051b18040b0d0302060a0513030f030c020705 70
    0x101c1d4414009444160409603140705060008402e0101441000524070551990725400ea508105488148000e140301d040306600c242c2d440d1040c1144401800600050351404000703000e15420403500820a180075000507003154400c100300e5001c07520346440d080300242e60000456a4205506800104121100f091914a1001c11002031059070020300402924010003040012030451040e00c0d48841c14050000c0480805001084180310307803ca81c40c204082c14102149810307521356645098030728195100b000b50700103c0000c50900201c000843c0d1001140020f401743c002c1d0002441c070700c40c01c00742010340b280090f1910141007100800444e043c0c00c3c0c0100440d900c40e9641d00859010354004042180c02608000220750340102044910301c9501900304024100929040745450300040c070361546510540750788182030140c880804c0c4079a4540603502411182ca480d54004003913580141c041c480d00d103042e01c00040400c1c0c4c0242d0403e20f0600500c0e021071200060ba008071300d400c240f80c001507448 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 792804649 1250 792803399 792803411
    0x4170a0206040b091c0e1f02070b0904021e0c150108070e09010e0f1014130201030513060516090e04050607051b0d0507140705060306040b011713021e031c1101 70
    0x664200d6a844206c0c441180c2c0111855020900d035060410f240d002600036910980060220805c0d11003d00b210303c502070001030800c102e44210052010813408034414030000044c001d50302090610083c1401c0d01d10405414541d4504a00d4503a103c04500c101600d40c1c10810220340074076802e400101410340d6000443c3c0d442d05c3c4440b0003e8035100d054919001c00d80c5010b012403640031800d841d03079114540c008500e43e03001c81590015800b0741001450508805030045c01140043d140744100c81c00307007882d854002c10801c00100064150200c07a0001900140740400f048001a0001082c03a40b0603194540705440741300c4044403101d08240720341140711030b0081d1659240360030340c020080c105160140072001c0201061000315612420326004464000204100095080c10300b5040724a00358410b2400d062015240010108004400e03101c000354842c600400c20f007907140a83c044180d03800c0705440000e030604100c1c0029030343c40038100c00040c00c1c0000c16045400c0c900425241ea00c03070b0f940324028809 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 792805755 1106 792804649 792804703
    0x920100824030115090b0f03010501121704080d020a1a1029181801061b0606120f0c0803041a0304020613030b04170a0206040b09 57
    0x990348440106a0500315000369000030179403440009441c0b0f04031420040c1501c0001c2d24244241e0401d00144213205548030054405540048510804900c0031a00d241c0e500440d4000d5560b4000c0e16102500582c0204580d0301d13a034450f66141c4100909030b80d811919500a44113115044039154080c00b0306c0c4034020400707103035101000351009425131182e0481060341c009915602d4070741ea0311880c6400c0e814501c0741c1001c102c0404d0105000d0758180b100080100c002941050801c1c60800081414403d19500c08409001070a00d01c5084c00b903241443d501a80021200f190000f03001c00b0000342c0a0004810b840139140301070a2100259480001c05000d07420280059038001410041040d00007615000c0310000c5222310311044c41031506003801c5204040500e410344444074204103c161071580401d4190b40a41d00c00715130307112a00c0d2407500c0791514503132604451451740c580101e18a = true := by decide +kernel

theorem cover : BRFrame.Cov 792625899 792805755 := by
  have h0 := BRFrame.cov_init 792625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 792625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 792625899 ≤ n) (h2 : n < 792805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
