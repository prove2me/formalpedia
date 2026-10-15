-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5382
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:41:14.51578+00:00
-- url     : https://prove2.me/submissions/5f7b121d-40ff-4fe9-8604-56cf86fd7b45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 967805755 ≤ n < 967985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 967807005 1250 967805755 967805803
    0x18160c050727050a090b13030c020105090402071a06040f1e09020312280f0e0906120708011b11030a030216020909150622051308040b0c 60
    0x50005020070031a0000300450700d480100d000030b03034a074003034400c0c0849015080c8001d04c81105050303007011660900842000380c142c0c82e0a01940290121034200034040ba4a40e801100550701030000340c243d4210242016260172010341ea50f141c400d0782490300c0550041c018040c08400d05280c4107001d52003100007020041d0340d1425113000395505d0146080300b8a11384030b540c034004649091000c00304859420744120b071105102e003e014541b6480d61142e403001d001c00d0b0108805140314600400a440d501d0701d07001d1000840304103005c08075100601e9540c200b009615070303c00042c0c1c100080c80080c860b00f00000341040204101c0050b256111820204000104400e00e048070f07004000c88001c081c15080040e50340311031008040301d8914240e4069400f403500000c02098081c041202d413035420685880d5039859843d08200884501148011500c0d8030210585001c200010703070010390071072603450880f18090310507641c042c02c0e6481a0004810104003107104421400104910416035485d0302c0311044103d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 967808255 1250 967807005 967807013
    0x2030a0f03112a030102070503180f010903080703030b0a050a1206050709050102150a1805030909060102070f1a090d1211120f0a11030c010b010e0405040b040f03050918160c 76
    0xc81074110110b0307143c1c850001e543c038551342541242d50f101d9100095a85400a9045810300c400c11914902c0c0280364042c442030443d0321a0b06c2010030303203034884002401c000301c0d520124010a284d800241e0010101840400c150352285003140091510290b4040700001c20718101050360b0024148506015950310240f141e070381c001c0303641c03810718a031034107490300c16550040110b0140102040103051500c0c0c4081078420310001000070103c65030142c03441c078440d03108c0d10012662044c052049464442200809102c860310001040b11a070351110f002c01d041004010000305d0520385c09a088500c02ca000c01a2981603821036052040c00f0881000b4003801540c20081e040c40340b0440c0407095603034100084611605000d440d540c5011846003044130f403502448905940284000603025020800740705502d603841c9424041d0b00d101e0b0740e100b0f50820042e00c413950350b020b505101c410304405001084c00020200c1d101d210707400c128003265080602c42824440447c0400180884011781089000d01609001c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 967809505 1250 967808255 967808293
    0x406090f0311100c17042412111317060f0f1602160305061b09060f07170d1b08130215040905010b0408010b191203090302030a0f0311 59
    0x40403080d0760b1141c102030380c0c500450f015a035103100200443e1025000030032420170300d00600191042802e6000380c0d80c84440f40b07a5044140300b81c0810000c0d1488080c0c2480c1090784e00f01644610b0440709031800d1035031207001004039240035003200201d06025000207038000304c10855660845c1c0b03007540542c000c1c2030080140308101001486802e01c080c0070003008500c0e40c401c1240c9426192052a0010306940307914001d034071000165000c05120000c940541400b6080a044900c0e40300004e1009140c4800c201003030f00c40d60032076801640d20f120030030548011060034030014202d00c1d44154000400c152107003000400b6681c00c0e407240d010800c0300d41c10400b040044291588009030112142407101403c81c51189181c815500181610360034000005107644144000d08142d4500d8070092112115030305c00c1c002d0002d1400d96196182c54582e02c10000001340702c040c01764a034042d14202c601c0c0380d20ba40110703151040388030381100c1e04403c641003d4241540075002d150b026140d08040c000800c0100d01c60486 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 967810755 1250 967809505 967809533
    0xc010f05040501081003120809010b040b0f15040b030408070c060521190f090501060b030f160311120615040f090b06160506010e0f010614090406030204110406090f03 73
    0x144a401d034089408003104004135170065500810f0540000b1b06584020459242640d040d01d1035806c052125500d880c0901459403a410301520740c440d14030441040050300390344010100944a07007000003041b085842c900540c819030084030103075034464180c0342c51003003492164015810040c0602c42d421203048070010703002d086000f0710342040007501c40101d40c920100c0001c1c50078054902d0840f1000b0100f11907005016058040c600130041baa035284607581c0b03c1e10003282c09420159640002445440c1c14001484500c00c40b07180004e144460350001c0c4400d0f6010a204020200c40902004410315210105010140d4400703c42401c00b4504a11020341c4620703401440c04580d180e00c546540c075215681a10034402d074050b450790441849080c0107441d400203024807104103000030b00049409403420f01150481d005030341c07030480381d400340400003459810981e80300e94007030786902000001d680d8074018030004500be40c008540d11491b01001412090032a845200b1740380103000104007040c004c0e440c81d54 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 967812005 1250 967810755 967810757
    0x5010509060715050127090201080727090f0b01140a11030f030c0307020709090f0314090424060e15090105040f0303030603030e06161b08030c0f0c010f05040501 71
    0xb444036164604011044040078004010601d0706000258400d0060204d40140e0002d001507030140f001c0c1120f090641da10340300080c5c04a0f02035004903400034425003102002c1880d540c0042640d469009160094004030350108410301d440300f00c3d8003804002c502c035094441109080c0b5004c407401800e181c0600b030140515081c240948002c8420401c0c0052040321000b2864083c655928900f550001c181c68101307480ea030006100d89880450150118801c40c0c000c1500b100441d4641d00c00707036408403010400c0440c00c80d103040e01880716030b142c2e403154043e084407060307a07002c0400010f0401441c0c003003030f107243d5200c58204129009201e1054640f10140092040121101550f4452520040c1c48a104940c02000780b245200000418541d156104806581c401c3d996804ca507c84402040401d0052a100404004200c1410400591744043e101ca81c88003130380c0883d01407980c9500d00d03070554110380350380901904102c02c40e0b0f004480a21106400f41c000342025036a02804480c001c2c1a0300031030107058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 967813255 1250 967812005 967812007
    0x306040302100510050607050307030207080d080a0c120504030c050c010f090306020a030204032301050705070b0621100e0d020114010605070528030314010b09040f0204050d051e070501050906 84
    0x520113103c50203003d40507107409031009544420b6441c2540c1e0300d50122006800501400340003281c031850204081410003d1036662400c60780b2a111240b0040040344000802e0068035405641c13050501d0160b01d2245000b512018103081040c06e1042c24004084c150a040001d450141040c843d0802c41071425241c100c040144c030385400007400c6d8000d201e03070381003e1f1405039007940c4011200002c01c82d0b07400920300c40c0700a01940d102c01c00c0aa580340185c01e4000e0014801d0030000e003581c00c0860000d034446408008104100c82010b038800e042220300208514059118820f190000e01c0400c40c009055000b480200044040d075040c0811088060044d141040800504c5105200c4208000f101ca02403040300c0303005900000600004130091000c045000c241840949030450502100300760480c0c078010000d43c03502c60f0000411004041e141540320b038083e400c1c4004180e649400080780107240c407800007050032140e103c404100d1056101c801098a501a000501c46640d0200990b048450291000313 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 967814505 1250 967813255 967813261
    0x18010602030f180315040c14010903080a18140a050312120711030a080a1506021c1107060c1505060d0807020d060e010501090f060f0509040507081002120603060403021005 75
    0x1040f0007074050444581c90300c200307071000045a810301c4250f4010352050740705a0200ea500c15816141c138100480c018081284400c1c1000031841c0b800c01802a01854582150782403d00c9041d03103127030360171900411140ea446044030a03c13400d203e4400c1c00500021001413030b80345000c001c015403030f2044000c8000c031582c81c400400c4841c0c1c0100040b09801c190b0303000b40c1c0d846980e060710092465004a4042c01801d060480b18030341036646600810584059902924800c141842100000d03003040603083c1c1001154801c44030300440900c54031000c7c000c5030f650056144501c3c100740c0003088501d031034146013038500410310041d0790302d1000c000d0126030301040b01e039210320840c0006010b440d0140c002a20345800d00342120189a4190305c401d060b160800001c014080700200400100c03007450080f00340340400301000307001d07900e0500340305903210344034000b00c402440e100c0c082c19041021800c49052411f802145d02c40742ea148103900d203603009900317034010021450a40c500a40e104000300c02c1031900350f655408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 967815755 1250 967814505 967814527
    0xd02060411150708030405101407120c0e0a030b010603050c03010b030403080c0c030c0c10300914071406030f181c0203030105030d0810031e0b070c0218010602030f 72
    0x2543c6103c3d40001205850303240905101d915044103040555219142c4915800e10a030050409801540f1940e202444022401440c10040a4091204007131101c0e981074210581c2d0342c6007010020b9486000000d140b5490005c000d8151074024114051380b160620052125000103410b69078850b400d0300c2d18104d503890304503c1900c40c1c4104013000c1c219020002d13140b9030310701002405042000c0184d4440644041850040703030702080e00c0038000b01d17100c0e0701d045800c40642e071106018507039900414001180680e65407a514001d090092240070760b00521020450074104071440e02014905450f1135155243c103107802103403420018664000c50140380c0703008450210400103105140c0c02d0400d20300d6107070340d0a030000c0d54a030400d115a034480d2140e80724805a00d486601c0490103690405100c086090039a83c403000c1081900c0d903100207447c135880501c4013141c9009080e6020b69000e8a400019802034014026070382c1040e402c48104084400040091503400011100c106c514002e030517890b07810702c0385 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 967817005 1250 967815755 967815757
    0xa060c0905090103050319050c0a030c2907080108030405060306130920030c0d0201020d0c240504020f0a061d0a080d17100b04050d0516090b030d0206041115 69
    0x88550020a04000030042000000040c840b041f00d19000314038092100808503103511408040c034032035401070703081c00000030300a18411130300510404c081c05010b0b00b00c0c6418800d65640c602d889513201840c03c10f1150310783d0041001c0f80540201c0021354a0241460049841440050b140c5406120130a84178010012560300c070340346203640f14014a09001c4800e4042840b410f0b040080341c82400f0f603444880c0c0514041e082c20000d6541038024042401000c60159002200a5001e88100f4800e00002e041741e001c01e205840800b0012800140504050050141c0003811401c118010a030b010001d04c4005e4004821038400c14040041c0c0e9060342d0307030801041005015501491581c4141d8840d0000c0f25000445498119059100c40b032413a035881144458a170703000d00c1403c2c1140400c00c13060100e810a100381da07200601800131038840c280fa00d250041610069031091090a980b290407842d20b00c0c0c01e100100a004151008011608103034584c5141b200f00c0101245c441d4220505c00516a42c00300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 967818255 1250 967817005 967817009
    0xc0b211f06030204090c11060109051b0a090614131403151603051303050f090109080a0c06021204081b040e1501090b090c03130507170709060909050a060c09 69
    0x348204400c1556404060040e4200b409102140c0341010b0811800342e2050500356010b40034034004006d181d1814081d44e0050402030846c14030303845902d4000280442c9180240044480c1d40d95561646142940003405090400070741d0a96140030020380c03140c121740a4510040c0c1c2c00b109150824010300c2000a89889aa9090aa00101c0e66020810170000812103100a80d0003034030140541d84d20b0204441d28007502030303401030104800303110900d503003180940075001803041070400c04415900c4480483c500902c88004448512241009108440d03040c0180c07440c19140c81c4a0504240c20030182e103494811003981c174030031401076405020341030b031741d94002c0c00030403580380d058600044035144607141102003402051095810034007650034509160409500c528640c002c102e080d621581c49540e010028080e00355868412400040b03139503440c03605880742410802d0010b1030b0b01c500d48807203075066605a07880b82104510f888207641c0030030000b20b010203101ba403021000801d1704010710f080d21b00100503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 967819505 1250 967818255 967818301
    0xd0807110d0e0406060203090d110d06140916212d050c012307020d05010609021b06040302120c150a2a091206090213090c0b21 56
    0x80820380600d15002910585800802d031002d2000646505c000d80c0c0e85e1007011112600304010f00d06d030b1f074040303030002c1510300604c40300801005203079686403240300958150056120300783c001c800500072090010000ba03500b40c00b00ca961060450f16240c0d007000a408222072501104150764880020080c114404054000c038000b441005215400482c0210b240059402c9507144284040c0c40050360080940340b070020442032044140620754003d200d00c9400c00d01007242c1102c40d40d401c410000b44280119005005403181c0140c803507400806e9174228032007002c50304226410641c2403201007607001c65540044403e142c1c00343d87d80c2c20421130181c5824044407903103c2c101569401c2c44018000d13500320001e0814070041011f0a900b0200c040741c03e07031848012a5002c641144410403c0a5840c1003040405000307200c00943c8040c1a004669201410705007220100c1e95030003510304000d60301d503034040600900c50881d401c03e0b5200068403240b10300100390030790f826a210300080207550043c0d008810f8802c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 967820755 1250 967819505 967819513
    0x190c1a07080c1c031b0c02030f060406050a230c13090614010305070f1d0135090601080a02011d0d0c0f050f06070f0204140c040501030f020703020d080711 68
    0x40b0702601500c1c3c030308815880b10030303046895400348214424000d0b0701403010821481420209a00815185445010b41c12070b014014107041c120f0b440710611460344280d0003080301040341d18024180100301c070001c94110302c00c40c1080603902ca5851081d030445600450a14050380d07960b000c408840c018064a5000c0c80031030b03080c807002003824051704444100014082c0c80a200303c0d00c5200d019101640443e00e04d00c005000743c00940100b20201c030b0010b0003130f5018144242400007603014183c0f1750250f041403d005c045403418000c0e01c0107071482c00030b620aa0702c070040c04855050a110b40e0302d40311690400b904002000758a03003020b102c00c403105c54400e403004241d5082181c0910780001050554890510003088203000001e6a0805116101d10030030000c058a2402105a071011303204c04100074140d8220b6a00c2d6510814541e10504c094003400c0403541c4180c58501d0030b0001410380e0f100202305241d450040c0600c2e0300180c1c0008086200c0c120904042c6504d5803220303022604206d0401c80c0c43d00c5481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 967822005 1250 967820755 967820767
    0x30100b04020c07092c0123152211041409071d041104030b060a09150905040507261239190b0609070c030f02010f0c08010602190c1a0708 60
    0x81d0540c404904140620321040b41d02c00780c40006071f074594040742c170003608650158103015070b454220751008640d000074591809406443c258403007103484e1038903c1035104a001605003d402d8180b00c4c29904440101d591050600c0c15a0000b130020b54900d064461300b03203100720303208015a03aa0b04051039541c0c0d900c0c1a00c0d1256602d0620403c00380c000c0d00e110f0300549007040040303031421580c01618095059188644049490082d084000382401032050360310340600c01e0080741400300300c2d44c1002010040c0541c2514035210460300c504003030b2212021106008200540c04480102c00360f03200c4000340036a0345c410407403840c44030342c50342c0c1000451040241c0a0241500f8a0601031080810b19a008040c0704582e03a40301c80501c10101025a04500032482140420001900c500d6a240742c1488510000c6004914506080152050304039900b003c182240010300c0703810b80c100105c00080060480224002c4160b441e8812040c1c444d00401c0072044008649050350101802119403555100800e42d690391 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 967823255 1250 967822005 967822091
    0x1110a03050718050f13140403180b0a0816050904050a0e07060201200c1509061b0a0f14120103060203011403060f0630100b04020c0709 60
    0x4aa0700004650180d10520f0343c141c2815025007612000303031010407014200410400700115912003050001c0e19007164010703054030074030303050b014030b10a407071340c1014020f46403558a900321990072201d4003220500428030029480801c0a401042120342940d0309100e00f00c00315550320416800035085400c0c1024081241d8140d0701c0384421960003401d840302d40b5182c030b600b242038800c26112071380340303080741d8805d554041c5240c0014605240b05108480d0f110f454240ca90796400b20031988009241c1100042001003d20000042c070b80446c000300403883c00e9055000503000e00d00c3d41d000302c4204014008180c00c001c4188049030072410340c048108840b5a540c0c500b0402039130007405209601d0000402d03c84040c00c2c00101c59000e1605200707a04044d566180a000e00c2d5004c00281425000780740d0000350030021554400021003581202030044040c100c3c07188401d40d40c0c10a221f80c095841004502e050340030204200c025200400b00100b102020800c84803a0700c0e980003110403400700100c00c000703005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 967824505 1250 967823255 967823261
    0x4030e0d05010510050301060902070b01050402030603031603080708070305040308130312090602091503010501082404020c010c02210414130e0a0c0f0b04120303111b0c04061a030901110a03 83
    0x5c420403002403140e0b07074840039079206901465800920600b203290040c40750340b4040d00a035501100c003804582c1440d1040b810004000d840350410380114400c041800b10b0300c0d500c242000d9220006080502182c1465500204982402007032007103807405000c078010070140f0600500c40120300382c40701070100030f03241e091800080d40080140d41c03088403c04006903d00000c0010740e4100d40c4140c40726040c0303554180a02c10f000042941e103405000086903610900e94a03403005c0e2000d03d07010320000596035489900a032a01c1580000c0221613403202000c10b1034185610102c4044d200005009140ba0010b4404203261400c0003420500e0175041080200c408c010011301d48404d039020b003048200d80d5680b01c1e810481040c0303d00501401c1d4200b00420301c1090240004070310140d210340360020b203824a01c441080140c02041580c2c0c8442202101c170035000c07004011490001c001290104a00307407400b58040724070660341400403078141c808070004203010004e500070741200603800e2907182d803018002001401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 967825755 1250 967824505 967824509
    0x50708070b04080f07080c13110a0306080d0c021c050c10030e07210f110909100e0f03070204151a13080307030903030302030c0f04080f0d020604030804030e0d05010510 74
    0x83d511a60102000304400002d408040f140a24050b046400d112400d1105010080d50150140c3d600ea50901000c1d145000040940c80c61607540014a18180400d460401a0b22040c15040111b4036a4050159449040c100500503000c2c01c81c180743c5115241290904100d40c00f4203a0210311907140d4207286030141c2108915907403610035624000c1c0c4811550b004202801c1080680310300f00a06040090032130010240e030a409030328014007100000e4005114204100c071051201d03000648558a00d141c5400382e00a40f40300c10019106010341403601c156a8001c980000e4455525408400060f80440c0c0da60805002d01c9500b42c56004440100c514280d0302c52480c881400c110b42c080043d10400100944106a0341030b56a0060a4595141200607400c0a0109880c4050410802251040400c000c100802004000d0004011180304003420b20361104124810f64016004210000b45d20080c1d507644164541841266506068085035403101001d40c01080e540c039100511825032180800c1d134007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 967827005 1250 967825755 967825769
    0x15090906050f180604080f09331806031503030d050714070503071203060f030c1409040b0a020705011103070e120d02150a0e03030f071b0b01090207050708070b04 71
    0x3482e500c1d40b5500210325100032800e201c1e01d81121000c68009181c0b00024644003007030601c1e1300d0034020080000381d408490701842100c038040515800c13440145100701c803103000d1211079046090881d8048400807102c05540c4883c826a0000000780d922401d00070040111800079003125243d01103030f464140200341c140c6000011a0300c46801c04c0d030301c040c0c02080300c0d5032a80c4940594141022a610304401000e022001c40516441e058040f80d508003000c020b87c011070040714180c1c172983ca0018602c180d0020380e03003540e02900d283c00800c400300320020001ea4001c030242c1001aa100c80606002d4010480c40e0f0188013003080000900c80e5440e40206032542d6100211100814076000281107650f40b81311504860160304175045042e880718600b000a503201064200108070b505102c542c0d142140d0040300c070b06815920720018042c01940c0491440f403d24080c800d521001e91032a12948002d182c1403140b404010b07000249802041070a110884c010b008036000c4840c0d441e2111070f5807500b50098041c4ca4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 967828255 1250 967827005 967827031
    0x6120c030f0906070e1311032a0f070f0c180c0206070315150e0a032d0b0c0d15030b070f030920060c0f030403230c01031509090605 58
    0x1d0b03010310001c01e4880c06061140c90b4048805100310600104900200b00b40c0300130b030394400303001e013456142500440c0f0400045c072000e0314008626011088081218100410720031b420700202c103040781058221a01c1c00c1d0400c0c0440310340e1155182120b020b01403600702c05218540c0300f41926185006400c216040c003242e0b0244c3c1c0041e03803805030440445002c04511820f1a5240301c04000400340c0080b01540d13500c0d10b181044c440d4980c032010030400007155008072039025001d10702c1400c004000d20400038240c0c80404100000130382c4d4a411040c2400075040c00318901c4001100d04c007134050355201c980354a1f1205c1034801c08030b9407810b0082c0c140c001200c4030000300c0c0e4001e1a0304603030b9100b4840c0c1906147c0c0b0910049160300d092001044c0f0024405c00755030000c40800114105e120100808411101034600940d1345600750b241211610a03100d014200da00c0160004502008012802c60080f107801e103000130360322120b028021140282c43d4001d00303055142c0344207001401440c2d0480c1c0c1c89461018124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 967829505 1250 967828255 967828261
    0xa0e3f13061d0a15030209040203160e1c0b101e0806010b04050604140415270e061f12050a0c080c03060408160b1602010f0c0e0d0206120c030f 63
    0x314103404410100c10380d010030109011300600ea80e6108440d00d00501d8a0014101288080450201c0e802920107021700341c100c1882d64a46540603c00d404011420340e8103450603e00f001400403481c0300000010819924040003034114840080030300c00030040c80c080d000e5842050b200302100c0d031075a40281000c501890002040001c500b500712400c0b2940904101e00d030074680340c00c07014103c0100400c0c59101e80c95501c015100380307000031040054588140e46982040c480e4452528020140807400f038814109404000c040401041039a40580e02101c20885c4c001e02c240b000000d10a00d42102042c10010000d034410710400040c0d000c862031107031524a21f42c1d034480761240d03514240d2403291945640014000380010746018090124001da001030950040c3c80c0d6540e05515041c02c980039070b18400144400d04425509004070310150100880801925032901ea00400c210608100315000c2c1603032117045011520b50408440005102c5138800643d42000c0c0030100180e07005496a240300015a004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 967830755 1250 967829505 967829537
    0x9190909141b09060402130f080d0e0d02040b0307091e061707120c050405330108010b0a09090509030a1409090106030e10050f0a0e3f1306 61
    0xc840000600c80c07000440c2035070b81c18108001800010540c9400c40c0c1c007840740303d405907140203d0310060f102c55481601841d04000d261440d228025407003408200c011390000c0000d894003400f8041c100d8045e45e0101e140680c2e080400c0c034000b0035512000f090361078a207604048880980b1070f17003045400c2030000d00045c0d5844060751295251005061119080407000300a00b030761009a281d8458071070f0034015611a80e0368000340c04c0711800c603919641001c41d81a01048401001d01c0784a4409030340404168086040300001d00e030f05414041c024454200050b1840b1160081c4600802413400140c14020b92415414442d10381d0860014100441c0c40b141c08000b20303e074410309807415100045e29900460f80f900300700324003902004919020728040e510b2008181043ca00400d40b080000d01d41180250410516207c210380701c002e092403031a000310301607260802d8028200b24400c1401c10310104251402d1505030354001e440c80700c000c0005400600407440c003280100c2e4004a520300c0d220080b044440d945 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 967832005 1250 967830755 967830763
    0xf0d1209080f0304051e28031712040605062b0219060f08070c080c0105100801152310080402310e070504060905060406050114030403050919090914 65
    0x80e1a51006e0300d2000c041003100114144000000010f010003819480d01d034243d000f0401070a0784142c41200c60b041402400b80c88c0a5500991402d84002440c290702d801c0641d03002c00780035000922094548020a00c290740c0c46e000450010803000d000c490f680700c460301d203081110002d6070490140f02c0040e85c881d1040301c46501d080c1102c1c180d8580d28101000e084c400c41d0303036041c014034800621090284810118812401412007122a1000028031381403161400703807103141a80c0852190f0381003046512180d40120000811654125078201c03070540001c1d165521240c40a44194101c2c900480803142c05a0095a0501460080c0c0310004d0403040d040013003404820740168070030000300020500e28041e000381d11514906203440c0035134840301e45502c0018242d44042e44010303421900c0e03005016085c58503118441c000c18003400c2c104845405580403540368040200094140000400c1c0908140c8825400c0c3e51800d0802c05284c008030740b0345510200510b021502940c410350f400b100700442050010f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 967833255 1250 967832005 967832009
    0x120804050604060e070e1f050a050f1320120705070b0103030e0d1b030314070b010e0a0e010f020703080702120d020a031d0d1106060a050f0d1209080f0304 68
    0x200140440790b9682d140c040103030884030600300c0c440c03152840000d40040d0a00c002400740c01b100042c00745110000c070b9421181107a5400a83c414480b45208122079980c2c06418100347c601a00c60100740c01c03100c4008001000000341c0706142d0b086006a4042040000d0000c2120143d0007a01b480b05071940981114640120007006141e80300003001400468000c10030310079040c2000300608109906952145044030f0022000b21003104501c105200b01074200c9000b04c1d0142100403400d00304000d03619078245429043c4541061180460081103101c007280d000400000e03140c100034406544011030120096120324007ea002035010f0011800d00b6102050384029016a1034003141070204c1c3c013000b94000d602c21b4072800141a03840394481030410081c5040307030101c85048040c140c1d80da003140000d0b00e102c0c140903907081d0681010080040551f10303c1c1607202900c0b0141d560300d10060050300400c032611440040a010130390709002050049600c0440c5105980701b020903520800c403440600c0c1e0b0307280038038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 967834505 1250 967833255 967833263
    0x603020315060d0606091a0306090c01050304050a05010c02071406030709150306030f0c05010206100806132d230a0204182f061c050901060b040b07120804 68
    0x21a9106000344803451070782c00841c020800071102e450390384c03203004556040d442010900d4a500408418140d0300c0f42141c0c002c48280c001d84032071310f00148030581720303011750804c9810b011021001c00c007400f00410003c0155541304000300300d0780c1c22184019680d16224800d0255101031650180105e06001c01030b64003c0c04141c40b61400d15003031035292000b10010f07a400504050391004004003084e901d40c00ea81c0b00a004940c03502030349041c10b00082c00c0480080c05201c508060b51000c002c42d4400141180d841030511b00e00c902035086910304009070080588030040d0310b00c01c1d412034031110710525194061f4503200b44505803105680d06a9603922954000c1c00d40c005401c4402c640001d820960019992503800e607580c200e400d01195070707401c0310344054499425440301c01b44a407144104614801400400121100ca050007000c0d4500c828441110700d92603203c035110740104400c9102508200701808010003402e44851311200c1201c1140c000c0c4109413040410000d45da0119030003070005038060703030304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 967835755 1250 967834505 967834513
    0x70f210e040609140703050a020c0d0e0f10020d080c04180506040b03061504020f2506050a09020603190605060a02010213051c020603070c1514070e011224240306030203 74
    0xd00d52046d0000c00c00103110100d8584c0820000003102c1082c0a1036100f40310310b880d9103070b880c940c100600c06407074001101d141c020078081600d901034640015941d0741001c180c2c500110350381c0c0e41c00d0503001e0398001c1c1c5e40b0501003003c000310140e82080613608003901c40c20703003564100140e5090204142d80c4901c103448103100d42d0902c030683c02540c04d042c0c00908429000e00c158070300d0800c0d94111465540039035140c004005098180703940c02c012850050301e030030898005c414040301031160001078684c80f0140041c0d040b507484104a1810000319081072005200091030962600341c81e26010b0302030f40c0f00410002c42d00c40b80030004280361620780ca0b1810074149880079000c07600100e600740100c5c4e50019002c00107018441182400040d03180c050310340c1c0721200210100700b40909207070303512480e9800303084030f02800703200e5507000d940b0b980c1f14200d209141420400800d250142c0c1040004041e0001e45c1c2c0d1198400400d0701191b03d4018100f0b521280301d024100b41405001e1820450460300240002549600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 967837005 1250 967835755 967835761
    0x40b090f010c051e040f0f17010b0102060f15150a170c0703180f1d01081f0b0d15020a08090a12050a1b061d030f070f210e04060914 58
    0x40402840c8034400791366540c90f14254840030440f500e009203601902901c00c1c0e01c2d00c18807800ca21046510300c2c483c401c0009000051400c0f0010703440c0c1c24014841c0340d52885031400240210b8461340703032001002c8081c0071103030655000140c1041507809080f080700400d91958076010b54480e4442c03e144100049803016040c0031242e901210303080c000c0e0407007001d004a4000080b0305054650301e0640240100e0310b0000084000c0c05c2032040d03080701640011201d82001444100c40403040100c01c00200100c90000b0f00001d06000146003105040b9016100c10400540000d509003d5401085080501d0300d80003465920710702c100b0341d648810b00c40101070f00b41e4003084000460144004e05054a15801d00041011491840c160035800c5200f040d90415103410308040e80d05581454902d80c4013070840030f03514015480c40351020354460504020440c0640f51000018409203050511062945082c4601491041d4200420030f0144003100c42c4150720381800081c07040d030a44542c0ea0780c4280351900e04042c0ea = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 967838255 1250 967837005 967837027
    0x103030e0604060e0f04021e0924120604060b220f05060f030a0f023606040b0705030c010c18080601030b040b131e050c090408040e0414010203040b090f010c05 70
    0x600f4420705e6001a0248143c0109a540d540d105074100c02c5203140988444180080081000c09075541400d0290710000e0038107002018402c0358254001e011405186850741000704009140b0b5500c43c20301030f040425400c901c40e00350f400203440c03070409015490b02e00307481d40d0038640301e110303030b8840c4961040c5c0c10001c1c2c003811409180174581c4135024400c0040d05d4980103201c0e6059a1203184100041003100c3d44a90102c060000e02d40c8038215190240b203a120350799004546544a940504400000003062100c1088005c104441308410610003e211f5004c2e203c401406c0c9101c840700b41c458482d40302501042074000040c00c141225003009581180740c94603141c1016003c3c020307115403008141b004000e00480d0102140e000a80352000c10050521140c0c18500d06102c5480e206070720918000c014880820398480540d0169100054010010b403a10f00c0c1010418400a0010a040d40040104014005004e000c2842810f54a090311003004c9022400c5080701c85860180300812428000c40c1680 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 967839505 1250 967838255 967838269
    0x10b0603011701230603212703030412050d030c0e060703180e0115090f060e061b010f050a020310060e0d020d050607030e1c0302032d0103030e0604060e 67
    0x204400341c000149808014221500c41d040d60245044210414003170020904080140301410550f462080207a0100c50004080c1403051094902d0100d0000d48640302c480001c103515000b255004080320390f03d99454000c80d14250040030700341c50901400b5442c40081c0c0c060701841140b00340319911240e01c2d01c040d60401034a50482e5200b5400c006d030090440d045105803403100e002801d0141121559507141040502e00d510310156881b0420100340004c210244502e0703c420b060702c115003010030301e002e44400414190b0081c2051141007100c202410b9041c1801984054112845103500303002541e100728408003a80b0058070b4241a00e1528041001114850503441500c824000c10441f03140e500c90700010948030704c4034400c0d11907800c01e400f44500700341c01d44101201c90380c000303020b40b05201ca103051104855520220010505800000041788001c2201c804c1001030050001c14204140780342c203a04140d402404201c1c04181864091030441c41d0500030b40701114840c0d540c0c002006070381c0e401d010344 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 967840755 1250 967839505 967839539
    0x406081204121103031b210d2301270204051309030504081b0405070c0f03050a0905101806185103090803060f031509030901030e010b060301 62
    0x550f08011121503607564140000e0002094809400344840c001200c180c0c2810b0b6410f090644615031800200c551401500650704c031502101000036082c044280c810302107800031248103a80380a044004152800300360f07150300c8080d0f200d045024506541e0200c200481c450b501819500c100100c1c014841c801d403503004640094440d1400c0d07801c00c2e50340c15030386140c0100d1040003900c0403e0502c003074545003012300c512580496180342c40c2e00c41c5922601c03581a22110b681e0701034100400014002c10180c02501040010080548048c40090003c100104a500d0030182d040004204031000241c00f845a0000c0030124100d00082001501c0e0105070f020382e00014100401003640b080c40320440c07608850b03200740c001c1120400707004800d400302005184412180c1351201454900a86000403801420a5903441002030320305955000c0c0b4000068581a907441c0201a030000b500700308038403044088042c000d40c030300a1720300b4003801040407011402d03200d6221110382c021405200400c200c609084a941d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 967842005 1250 967840755 967840763
    0x3021903020310020405031614131103011701050a0c050f0c010908070b06011205090a021c050604081306030902030a03030c09080105010303021e1c11010e06090c040608120412 77
    0x2051503496002c42e05105000403001016540440c0c10442c07424180480300802034241c03a00c0071030504100d801e1914182840095000f00d60140e406100500349a002c03d02c0b00114203100b035240c2d83e5800f120035110301000344d0002c2650818000c2150780c80d0038024005244820703180e250902007140c0392084190005a600c0c00c3c1503485403049800700e4050344c014515107014604803c1c0354601100007511041d14480118502071401c820000d4040011a09851650f4115100701091405a11502c900342c00d82034003912500841081c0000c1040c803000400281e80d00c40d8444161958034001541118210140039405401a001080010b40700350302c170310603105840c20840410350325689601d086480980007140941e11502c2c400602c6200d0801c00011100d0700c8004003203401da010071900c0e05441c0700340d001b8180181d00c441520680400e402050701e0100450441e001898040c0095507603501e850041c50003286028400700c0c03c1c100100303001c20403440c0270003058502480c03d20480106d1a204400761 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 967843255 1250 967842005 967842049
    0x702030405060d0f060515030c0d090213050709082b180b040806060405250e03010e06011a0a080115050f070605040314041a03090705040603050d0906080f010302 71
    0x8034941d0390342c0d8003070302c3c29440c100000284880303049820030413103005422243c402c40454000111058004003129800320100c0006034a07540d070124500c1c06401139010003580100c2299031885415a954409031059019030748241c001a03a98030a0f40d101c40300301400090076088003802e511081c2c040c8a0009c04c2085a1508190080da110f80e01076140e42603803c5400c0302200080e0422102d2810000f4942181d0200c030204404e00b4501c0c0d1b104003940c4490701d808440b0440a4043c183d9600030304003e4011440a4020f102c202c120450f90b41e2221800d0007203840e04d91403289100c11103200503065403109641c907101c3c4103540e420501030100a034000c5078030b901040700401c5941d0b8107940d280c01500907680301d960003107400e003400e2401a090900d981130240900c0d100b480101300d02e80c0c070007034480c0c64003089401c0e1030364030341321004080e0074640e694006c0d80d006810071400104000c030001d5004501003d585d502482c1e01d49803802241c81032020350310072a04090000050000d0300e080c5a0001713020b00544034107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 967844505 1250 967843255 967843259
    0x150c100b3003160512091c03030902120f1b06031f09090b060319020108071d0a03050c090f010f03030f1e03020301170303010302130513050a05010c030b01020606090f07020304 77
    0x41d030314550003003004080d1060807207006004c101041041d840700040512035542404041c801242155015251a4403281405200d820a050081c0d00c2603111035009440200307502214001c03103a580f4102080c40c60350f0300c00c40c10009944030748003100010128000303001a1440d20f4084451000e0039200d0707a401c0c204c00030140c0000d01000980b2500a5062191500d9881ca15209007014103144032a0351040f54401440720550041c1ea201000550000980c00e010302868822402c100e000034800741d4140d040b0f000300c4004024841c00250050170050119102d581070360341d5840c47d1840340c00a1182040020b81a2014400a03000303000789412800d9600e00400542c0660ba0400000c0e168601d4180200350b0000051068900045001454480d41001107140d9451680483d100c00352541c144039170f41c0ea540010550b5106820740000366560040c00710f0785138486030300349540240501c28052000c2460502040d50b95400440d24078480c3c10000c0600f1502d903104039442c84d1542000b4080c0085000030400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 967845755 1250 967844505 967844599
    0x2e0506060d0e030f070302060a1b020709050702100f06260a03030902130c090501122f0705070b0a09090b10030c0e10121d030409020d0209150c100b 65
    0xc0c158082c003070780c0203000900740004140304072b8501c04c8010000069107038000c00481e40000754881140c0469800190036a54114120b0400410042800109007010880e035010507040c0c02610070b0f106040944800c034030383c43c00d14101b04c0070703013002050131900513a00d41c1001c28041d90000094500240c25014040301400b81d4004540d900707140d20300442d40745c6000380041e50307012000c1d02059650356020055443c451445001c0c0c0c0c1c0946040780c00b4a02780400d038010303401210090b0303140541c1c40b20454140d1910740d0302041164104024500001e0905000098845c404c3e004080c000c600c05070411b132950b15020401c1f4042c042004071103040c800c1c000c01c140d02c02e40301c0480400c0b00405603501d580380313540c0700c2407400c003601c9503619640c00e081881c4004550006003c000c41d41110044070700140d0303855001415030068040c00103200d40c000e48502c043c20381c114040c80146501a686c0c8107032613404108840a104031210300580303d40080401150400448071080a0485000d034103060300406800511 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 967847005 1250 967845755 967845757
    0xd0806040b041805071703091c060926160b0a0912090501021b15030a1b0519081605070c0803040602160806010602120d0e2e0506060d0e030f 62
    0x500a01c043d0300e50310804013030060078041c00000c1c00c1420000c41007101c05d00314156803409541c1040d84210b06042003c40800c50001405032626030100060181c0413550030143c03000f003801409290b5080591000241c090000001c450700c1514000f104084d040194894800c0c22034020106007072140c0d200e525101103040402110390782407859a500b080342d400d1034002414405c110014811111204401d45a0b0b42c3e14200d1132081c8c1c0750b45814584d180c0e55500c0c1000c01502c1000d215440403050005100e03003040e40400202203c03502115843c1c01080e560380103c84080088845a521459409084400600c2003000b0300d140381c055507103800410345400015055a0059000102590140251a644110700e0170548010309801001c0d061540c9408006926a00e407804550407a50000070071300d071040c2c6a40e0040e00b8454101d400c03a46a03405e10b010310101510019110001c0c1030480200c10b940c1441401355a219081c090041801e00c25103000000c05801c440c0844689408140450b218100c4010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 967848255 1250 967847005 967847021
    0x30501020903070e100b0309100f09110306150402030a11031014060f03221e1401020f09041a0d0b041a010308070f051f05040506010f0303020d0806040b04 68
    0x1100060361003666204061500e90640d0080d0850b40e4000c0410110b00d600c102e0f26000c844103404210750340e550303404855080401d190b60f108041ea20705600880d010b0443d40c005510359101d1001c0b801c4005010082694920044034a501102c8840014000d1410660055500500c40840110300344c02da0034030060081c3c10403a00402c0c504404041000821400901c2014160b401e407070091030514440d803500c0d0b0b03a1200605010a012154901c61030b0b5002e003000011605401c151040500f051052119404c80040f038020b4421076034030a07142c0d524800c18801c6542c0e41028244161a01c40044180000761140030a044001c54862444070201d0325844050303035995206501e6181c0710f180c1842d028224805001c48110360046030401800080d002a080b0b692054005a90303207044403440c0307880c80c078006541014440c1550540d140316689403554000d0750240d4418019144680e8844416401e0b0074500d00c00680141d10200d500402a805030b1003c540060700a4408204078606402003400c2c3c0740f1030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 967849505 1250 967848255 967848263
    0x1e1112120c03130506090907030b0a09060b1210060f0e03210705191101030b031204060f080a0e070e0a14040c1503090b1b1e03061f02030301091a030703 67
    0x60401d4002d90007410074400307088104e49175806c00702c03180702160b00400014404c1051540c1c3c0c0c00d1038001a510b11052800a0002d4641405515214039050b0559009400e80b151110901070105203a0400307440c0d80301c196495691440413010210f6001c42e484052000030a400d03008054884a01802e50480d00c000c0b2000300b08200c2d80e4004a203482c42c50203105961091092044411010010754400d401500b41c01013468041800c9100c103000a09242603204801720603407000400242c0c00307412460340d140300461600c510030240c0e90b0324a0b10041c2d03000b807520315000307410081e002c2c008510307010102074124030703003074000a03c41455802c00c901000f0f0603241516403034130300c400411420380c0144840740d1003080352070280004c41c03540d5036843c0131a5000d00ba20585c81101090111205403c406541082460104205130108070820141c490340c019503150b4000c012064140307009249074003060522540c154020b625682c40c11840340020030702500c000301a001c1003240c0310341c10f40d801c101d0213001c0c41c06 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 967850755 1250 967849505 967849507
    0x1309060c170f0c19200c04181a090703060606020a12020c0a06140f04170d02060c090613120318140d021216030f1e1112120c03 56
    0x1207110034541c1400020401e01c4512181c404008a09084100342e500040081502084918140a0982d079070034800e0007112803840c904203641150780000072051001c1d40151010004665000b840c5249070106100240013049491041400d04108840e13256000d8140e0081c3d40140382c4a656000581e1980e034490343c01030744000010320038808008030707480880380c1c58002400c24041e20008101c501420344540018862214004c0711011040d50884103000d50b410042a60742e92105c82071000c541e0041c4001d036880c800c510202c0181e038000502c0500510100c0609820030b00020100074003540503070b82c2085207203100540028903051800802d04c125119855100905600c0c080610041704903a0045035090040368403a0802c1d01c2c0d42d040b00d1a502c1c3c054450700a4500c1300101c46243c6800000140e5001a20440c00024442c4501072000075a101e00c0c00c1c04500148030141c245d002c0c0810b80080c0c84a0000e8200442d5403401004204010340004e081d200000008034030808603400400c03c850203500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 967852005 1250 967850755 967850777
    0xb090105041d0105150a0819020c01020a180602010903080f0a0906020f12150f280b0c1504021503040501060302091302180c070305131814180c1309060c 67
    0x45c0090442510048092106081c008060001800381401070080301801b001080c10121110b8103070100c480f000440c40080d9559005c5040040c042c000c2907903181c1d000407100c000465021310600450781c0003a0950758180c517640726030120a824010142602020a0703035a42041c00007155400940307005541007002580319054011100300d2000010b00d81004101c10034901d00c2240e135003120f00c4504680907241d95401e1945c0006920741c801221201314958118100d000444168a5008004031105c01040c0da1200707280030500003214bd403d940080d80300883c607550050070001d40029680c0240250b0011442030341d40e40102d0b284002c146e940181c4409840c403464203509054070b48810402c61000c0e042c00d14508000307240b9207406200390081c100030740002c4c8055540c100c4000d01c4041d0031a02c49988002c0c0c0500900d000904100b1490000301d201003001032410f035607007400304415903c00c5020b0305560342c1007010000ca200c202014400c281c0e64480780d100110f00284921804015503441c0c10380104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 967853255 1250 967852005 967852009
    0x321020f011a0405100f0b070203030c0f06060109151b08090a060909110c0a1e1a0a0c020f072106110a0806030307030e01030506210c0907030903090b090105041d0105 73
    0x244001e200e5085c006035401c041056240a1400e0f2003115800c0c41c10603128101071001a0440c4500c40c01c620203486440c000c00304400020030800d0007004240c8801d910150b8450100c031894010a0004011440007030f03480300c908000d400113110107881401c840e41b400000000080303155560760401c01c00180b4094003400301d80346c83d20508070f40c0c2c45071080c01410605684040c075641c07603e481009040442419456880544040b9070800c0b103070b88584207202800d541082d4118201048507080c020a04240c070300321084e030001c0340c24010468136002620f0981d06011405d40d669080761030504035210709403800b9000c20f24901c144041d100840c4100d554680c403985000744200000742035548203402c100702801c00250001c09164503100b083c200850140e4800e0002001180e08007448c0082c02c08912000d0300c2c1d2540424080c28114003103c80382d0a5032903102045080307500c05035004000c52200f5805201d102101e10103028028014507141f454507440300c01030600c038a010350b0358155401a4100500080c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 967854505 1250 967853255 967853261
    0x190e010914072108040e07050d060e2203051902103605010b040509010c14040506181f0c0c0b1c02031302030318190321020f011a04 58
    0xa03010000051200906140d031001c41c24203050a03010aa2400c03c0d1401d04000b40541510000d0902092103001490140390181040d0700c503030204a1105c1c540b010200b40c0403221a01c06020380c080000031540078400003005008410041020380500c4418480284001c18210b056029005158050111240d41481010036100342030310711641034502c42200c01a8001080c203101007a8200b03c02065800901d0605a0040072001c00340c0344c0082c180020002c2c908015003242100c0b403070325a918181c004081300045614002c07070140381e40c000360403c8042e004040700a203c1c41040401406248408112450302030740c840c1000006010559031503400d024898600c080000030240884510318056a814400c4103c03a0340840300d034a2141c0c0800890104220310484061040e4060304803959811300700000244090881c2000d8814880080f080c10941421000902140d5205d20000d0411100084c080000d010201c26502107104101010100403824025840c01c40ca07020407030000c84080030180415 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 967855755 1250 967854505 967854533
    0x7080d052a07020901170c0d030309080a0305010e0f06030d1d0a08060f0f09072c0901020d0b040905060610050d020703050a090b1206090c0904090c300209190e0109 72
    0x1400780d1041400b080c2180209107c006110100c402d4071551030a0325081c0c1c020591031a014050b0100802c20b06880741c3c155100038183c94001e09164069501c9544c4805480c1d01281c5039505500700159118009001e5071040c4100b01c0039013091b480d04e000034404542c14003110b510000039503201c1000c1c000c2c004010000580c004035401c0c854581481d03c1b070100b40e55013a0b6445140080111841c0c1040d0500c400308046124103550112010700b410700304e441d98041c1d0841074260f00403a182c03125541041c6010320982140340e60000141130150707100e20030408182c2d1008030f0102442030070804400c90903001d10040c092030340b280e160603840307000e1a18001c0141c80a07800c09189100c08122442e113054024161640c0080d08441c1c61646940b504000145402001030194110381011104420001024215803e4900080406e85415020402654030540400c0c0d140280401c8010a001505108949035802000e00907a8940000642c6200044a803145580350699540c0c400e01d4040200c1308840000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 967857005 1250 967855755 967855769
    0xc0418050708091c1412070e04060501020d0e06030604110c0307030311030415050c0f13031101030615140912250f06050d1104080a1707080d052a07020901 68
    0x74018040c4044408201d800e00104c2803200280b0600030740003007401102d241c0b02c1080d0303007449141415480540603810080d00c640c465424481c1c040307125480041d0f000056070306ca96503000c40305030750002e01c103640c2d00161005401c29110b075070031000b03450440014502d0490b05001556685c029007802000c0301d025203a41c11070303103a040080c0000310307050790944c0300381e80c10403800001e483c2c54040283d0700b98070500e0b18085601c800440c41e00e5896070882003130b0048070301545c45030910030080380044003266a50302410280350745d95030741c200280c0c0c864480040001d513030b50986890712858030002a24038040440c52461030b488030849151310300034001c0d070282d14007103071041030055410700c59220310807036147c0504010000041860703028a40036030001040c070707101201a0ba03690741d25079200613200c0180500070b95400403d103010141c07030703c0488201d410664101d03203450b00300b0312a0040d68000e004080e10044100240245601035480d02c55000c0750007003503401d29940d40e00101d1040c021744000503849a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 967858255 1250 967857005 967857013
    0x70605060f0f0907030b090c0a170105152b06090b09070801050103090c0e04080316020a0b060607030c050d0201021c0513030c03020f03130320010f05030c041805070809 74
    0x81d10780381c44442e07450907403003201c400e000e0b5070303903004114002d2020b8205c0c030394040404410300c01040c141070700902c180c0313a040c0c0d59960204000d04075004814428819a604a10313600b01c504000403040c00645890281d6400361044811003a0040a1416085414a000e980e484108228603180d52017905000e51042d105189203260011020300584014031889041c90385400c0c1d440c081200540d90030024000186800b020750500342003a003c0c9400403564a4480c2002541e000f01d03050000078515111940811030300403d036181401c3c81400d030031407042101440b06c2414084d0014030203003c0c060804e82d0550005031940790182112011400304107060441512b0142800000b480902603034801c16010f040c0580071f442d003490128a01404c0040a00441c0070103d017504c03c0a207580003942c1100d02071040c0300840400c1e0083d04507000e44d14450913010441815040c110140a01c000e15440414045441c0c10942e0700c10fa100c2203c005401d44405e62583d40040000071038121513a1b64208205030014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 967859505 1250 967858255 967858279
    0xc020d14010617010b120a0f030f140a03140612060a0c0c0b01090b0123090d0201090b210f0717061903030e01031d0c190302090c07060506 61
    0x42a0411484440a0854200390319089100002500400300505858107415031411065241900030140c01000a2003088880da4403824101b00245c00007865030400c801c1003465003071381e60030346103a140d00312910248040c0015070b000c407002c8071015207509403407510302140040464020119140700101118070903010034072040d0008030700103040d6503c5124680c00040180039824244d550140500008141c00c2011001060072030080d00440000902030700c0d820414000e0003070a0321104054500c20240c0740301448a00e1103441c4c10901c8443ca9401030610164407a00c0311801d050503803280500000140e118050008443d0078006a80d034000038411440f049418101c2004041c0c45180d403044440581301c1c400b140c3d0940d9070100d5281c1c00442d442a40c0c1403c0d90781d00d07024100071407418985004c07034a8030404047c0b00b4a01804a1204c40c000c0740940b0301d000c8000c1c100113801c0006424401e002905560100058880e900b600740074804403c00c007621801c0910344401074500080206000f130f4500c00b90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 967860755 1250 967859505 967859509
    0x180f06070f0c06090b1e01080604080a0f120204090606020c030c0a0b0a03140411040e06250306091508101401030b040503070f11043e1c1401060c02 65
    0x40c04500015074030309415000d2150814001414041c14081d01741002d1205028010310300c900c0b5144502c0312485031101c580e03030350141203445007011a006480d1440030000e020105200300d103402c03004282410a0004a10401301c00e4040385c000c0c0e085000d0155450070140320383e035010051000304840031401040e802080300003081c4880074a12401042c4a0040b134440c07501806034212600100100c83d8107402481c060030104600c48007010902e0144c0e14180000342091000300300c00d8410213503019034804564100d19401502c04443c0c030050105540c0c3c100c0412949074a02441c0342c18030409407825090782c10b10040c141814940341d11242c0641c42c00c00003144200e5a42d02c2941103a4029030362004a99440c2040c43c190310030294020101c5c87d0740b00e450380c10002da402e14400c1085043c0d404000c0d50517150317410443c108203406082c1e10320011910a850b205c1c00a10548170740000e0900342d5003000408c0b000420605001200030324650344400001c194410080b5005004140e2071500307610140c1e413900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 967862005 1250 967860755 967860767
    0x40b030705150c191101030b04090b0c0c100203010e0619140f061b060a24030b0402180c040e0f06130c0e0607030504050a0801020903100c17180f0607 66
    0x1000c0004080b0108410b918503600380324080d1541d41071380342c14285112a00d0000d400070740e030556850200c0e10b800e0600e060781c209442240101a84001ca000340ba46030301600b5151600880340002003441082814600000e50340003640c020100c102e000d0354282000020040007039040032003000305221102c0d080241401a4a03089811041500c41d0040803042c0030204404d449841d07000941b8007000d0304020040759002130b84038410050380608009004002c07a40020250300301c04d1010303280c0f00c0c80350f052020891b54108643c12610052107400a40c46031005182c5004040303404102805002c01c00300042002440702d175601045080110703c403490200300084510701c03400b0100301e600b5a0756001c0c40d0824007030304012103118030080505072100c8261030010881d0380107002e01d5000b22600305000410400c14000e076085510300601030b05a03180c203100072400800c0075184c40d604011425103104a2401c45a800c240a038000301e1030040c8000321058154680400490046010ba00c4001081012075004c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 967863255 1250 967862005 967862029
    0x3010e150a0e1905160e040c02030a03050c040f060207060806010219030522080a02030111161b0e0106031d060105220f0e010c0216050a0909150911040b030705 70
    0x60312141c3c49000070514001940c0801143c02443c00c02031060140c41d60120034128030056452001c2140e2420900c401d0307a8200c540d03a40135030710602c81c2812580c045d402c1145d00c00c1181d60014102036480024040c1d484190f4065000750304514000d1181d59480003134103034807150a00050030a2b04d420340035018440c0d44c0010290400101288a00d00c90180011501801d000e10020014007a1681021031700c400601d50202d21a40c82c00c0d4040f1015584001611084541d604050302c15500c01c3c0c4408024400001354002602486c0c00d011034000e0b04002002e020b0309103950005218114241e6612001903429580e2050fa801748004100c0c5994014010390084003000340069454020750102000c1c025018800c0d00359400c25614000c0031105600402400c2d8050b421500c1642c216282c5c0b0b000454103024080d00030038219803c0c0041c3c90140c00001c0d07003602c60752800c248801210349540c121810381c4811035821901c0703003440303c40d032030a070107106900c54003107002c0d24481d840c040001d09402045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 967864505 1250 967863255 967863269
    0x180e0a080706020c07031101260601110718020d0f0504020a030809030102090d0f020901060914010e0d1b031401024602030403031704030e010305041b03050303010e150a 74
    0x1071507070800180e034042d039800503030100c01c480d04952a0301c0c1400c0c01c1d000c000d944a000505e00c4030b0519041c0b0407184411034103541c5004e00001e07034861200450315254003001c0c424981c032071290300044007580c00039030309441d40084030700580b5681c41d41c200c1c400b91010444410405803d1009000c0036a031034004105c200d85c0e01004640e521008480824068000c541007658440082c490000a200c042820712080ea0700c21101c0074110781c1c84a400b0b0381c000003140a010100b04501c2e02420244d40a4055902e44410040c000b02e0b64540a40d0782c4007480b029001ca000d80b04141020410401004042c000d85905031400251700306080020086071100c0052036003807000980c0380007088030180702c2e5007040304a0800c400c0c0081200009202941e6544680710031000104180056031303841d000c40400d9800f5030386c10741c4c0d001b00c0f0f1403080f0011405440080c20940f021141149205803003408084403200840c49503002d1500da614200300d909100500400704000703205515060031503607407101c40e00c07000e40d600703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 967865755 1250 967864505 967864507
    0x9030809131b0207050324010e070c21020d0f0c031803050a08070b06010e090a1d010606030e010b0d0308010515040902030f270616030e01020406030204180e0a08 71
    0x281c41c0c6401c0140c041e88191a060b010028210440746902180c42804c0e00d400354201e51405040c1118070301c9055205c1040c1145c1c0d0203000052003524550034445402c90040d00d0a0b040048541d11000c6000d40011015204051107126200c0010780602c030902c8503540c54206030708c2c10a07800342c01601024564038000d0402c461401b41c803544407100c40e00080615004421503003018260300d17080120780d22104040d2582c0b40020700240c019031160404c500c00130000380182600392500316200003c0e0100600400d0144c004580400000c1000d00c1480c001306407540d808101008000d5000f800c61f040800c10500500c030400703450b00030907041441e140c111038060742c003144483c1d400016084980507981004111302d000109020880c0c0403901094003401d002c11456440b40c0c008010002200e05440c580d0008d608035800198000d003403104644400c0740d4034200460205001741005007246e000742c02080c040707a030205060080c0340030a01905401c0f0000b110801040c103400c08299a604100c0c2001404800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 967867005 1250 967865755 967865779
    0x3171b16030537020a03060924020304120c020f1005040504060902040503030a0f050c07060806120d020a02130902090a020403110904050a060506011b060629040314070b0d0c0f09030809 81
    0x21480c005c4402103401c4441040400c40b203260072044a5401c145070300040c1000d400003c1944014422240201d51056170005030b9690a00f050315080c00151040e80e0146214202c0359132900d51900c0c50a0300c441503641e00d95190b00749020001200c40359008074103030600c18001801940c500004803207050045003000d00015002500032503840c85035402442440c003c80000080b010f40081c1d089020b010200e495581e000f016601c1c0c5a0b8807101e080700742e00142d00001414026080c4a400c060300398900e500003042d20b030100e8012598100301607824180e641c0d40004d041041c005031030215060204102c98410303490034117403070b240c0d50f030806204060441d660343c4d00850790503809080509411919005030303100d1000300b0b042501c000c08062061000703440a201c0d08800c44c000311b56215600c0b180e03006003181040e0441d203816070030401c440d2081ca1688110800850200e40c0724002d003e040160344004199500080c2c4020b1140c0d034103007040802d200310240c017400020001000e461050009540d9080d20227 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 967868255 1250 967867005 967867009
    0x5070b090415091505060906030403080901150305240906071d1c0b01080610090914010908042c0403230a020a05010b0a03171b1603053702 61
    0x100d550ba0081941941a81e030008207a0016040082c00c207642c1130051503002da6880c00d0080b00d110355050340e58403400410010300007902503000da03030b0480ca40702c00009032400b2140c40c420171015290025100c1d644030068994900b00c00604036818101000245420b034144404d00c01d07aa02400b40c007417418800845014411060450a6061400d400038000c03108040395050080074419203080c2a40c00d84031201c00407034000c80015940d8001c007204900c0d0f034009840c0400a80080c909000111401c030000744200c21400001d000f4254041e029038481c5a4071450304210120043c524080740c004521524007910000c003551800d82e6000c0d405041c01c030040d0980c5107044208803500400e0401280300810003040c00e82d03000400000062156008000600f160010070264820300d10004003a60651401041182c102c0070180041034049508082d280c0540e20882d03080c0102048020020f00324a441082401020440d413012000303040d0f00c0301040d5240100500d4005007054150041c40641c0000400319 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 967869505 1250 967868255 967868261
    0x20c0909101a040c1d04090204020409050727030b072f0f07051f03020915030a020901140c0a031d030f010629070b0703182303040305070b0904 63
    0x580701c1e00741e040040c00741811104035026402d08049008034a0315086071203a84c041c4450110b80b60001c0c9032500800100307030030417025007002101203070040e03024080000d112000f8007500d070040e01180c40c8c0400c90b4506850102000710421003603200d600c0301103800c00c00706e5500707030007150010350501d8403200d01c2403508000124807402400c0b661980c2e078403200d803040e072140102d1030f481c03049001425146110381c0c42c0c00b0490350406030100100a100300c000f403040418020342c020102e417103000c0d0955240013503800101505d0340084a5101301d082d00010048841d6a102c481011603544008050381400c0e0034a400c2550303103004960080a1046c43c0618541c05a4010512034040c0802401c80f5250707500313900e00f18080d0070603115018800c802910b80a904c1c0700012494003501c180c0000981c284090350b200c1c1a604c2e8405010f0030103042d595042a0780c0200581500e58910f40524892107040d05400040710f80000c40c5ca403c62200d4100f4001400000c0f4042000c40460361096031954503440010005030003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 967870755 1250 967869505 967869523
    0xd0e090c042309090a0305040b180d120e150d050406062705070906051c06170c13062102030f0a030c0c050108070503070c150519060b0406020c0909 65
    0x300031503003080450120403601207048440025030b059006501c8003d04c00c2c0da034460310000100807440a100078041050280054034540c05690b6450407086040400700d00e65207aa02419079111903002001000d00b900181d070540a05002d03240c5001c170800f00040d044950240708200750135140c0300d40c00300e01804140e42120016204184000c05c09c980c00006114500e07100000000416040c00000f40007140645001c6044a0b003d0311040d2034010302d00154511600e01403c0c11211a9035080c01050700c000e686050760007413212000904121030000100000d0125000354440701c80e060000c280041d249211010320b850484c2c1244850b09030f0103200007400c1110b040084800341c45a407200000385a844a1106001d034003805003007040700d07103441c011076194400301d45020100c2e00800c041002140f140c00403c00702030103055004810f031481c1c00a10190f0b070341a14140e0078003000059090f64485a80720700b00051140441c04c41c83c103071038600c0103503e40100b604000d105154a8001610801c3c0c18003e1010f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 967872005 1250 967870755 967870769
    0xa080103030c0501141e0901050105150c01140c0403110916030f47060712020a0f031206080102040503100209011202040608010e0601111b0301091a0402120d0e090c04 73
    0x11854000c13520311603084910f043c0307154101b84101086d040c0c01c061140c0ba06a034400351080340384900751503c2c2e00e00c65102d0441e803070007503581e802520005802014000d0040001032032659540c0d195061981d0081094074000340318580403c1030080e0101d11000429541c4024100401d0b4602040780c003000400060411600d101440705180800803903800c00d4181c004440700381099502c400192201d890104068069007000040044c4804900100c40d00c030b02060003441102c80000251340c0d9050303103600805085003c60b101142d4099203e403d80560f8010340300520085041c1860980020758a500041c000c0380920360001e0308281c10392051115220384004008d06668039960380c0001024900240700c3c0c2604002c044c4041f034180d42c0f0890818111400c40030050071040101d40c000181c01004c07100c050307411740d030b52289540015500d0094101d0344e400a90101118506401030140568a1031401c4146030440349454098641219501555079019101280309990301201c4030014451070700185 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 967873255 1250 967872005 967872041
    0xa064106030406020d15030804210203010c181707181d07090f091511090316080706090b0f03090c04020708030403180501020d0e0a0f0611120a080103030c0501 70
    0xb00a0007003035002002416501d442c20003610394050b5a80101d00d181c6d000c002c244401c10002007081d03064005195403400c50842516141e1105640040d0071905e241111078045003080e0001083c0c00740ea40e288000911850140480203c114040070f82c8400307007070081e11008142c1c1c4442d82040242a41314119103807000500d411203a00994410307554685074422601c441d4102007800050032514011203c8956104d176004074071a45840d40540a0a0552346590401509000300140350303808102030a5001c40344540022000e003001c1c16a03092181c690002d0041c0903441c1c00070042403410500300c900250025140907103e45441d03074401c0c100680c480d8065807050012400d0300620640c40011400b81d4820345404c01500305842c007180e0000020710a05016030000c8a49880c500d00501405c0004000248800d850700d07220100c0b1703c013605494004000007403808000ca007040e08108009603030400400795080c02e1005500d4004d01e4548140130003020080d03030403000e03000c1010941003440b41c040070000765 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 967874505 1250 967873255 967873261
    0x901061e081302030609060405010e0a11010f02160f080f0607050306010c080c070603061410020304060e182a1201140409060c051317060103020d0804080f0102030a06410603 76
    0x11547da100aa4064601e5480c0c1a080000e103107000415440c444e0f03102c2c1001e0030f40110040103481d6030741c0d401c0007281940200a0325807404c0e03000a004101800c100c4900141407402c00c2c03409490500b0500041460380d11150034880f00e540c01006403a400300d02403800710b0714140145407141d03260084d080d20110303900c40c52402141c41c1341c041c1c20010564195640c00110b0101d01c2040107221080118000b0258008020038801c039445821200f04481010f8241d0b9440f004002c200015150219035003590350300c13114060710042d00c00f680400c02441d02d001c81242444035840300c074007407a0018441d403406203075001603c0b07880d41c0399034100c124950b810030410448810103c80240080e404100342181d5000b031a0b00204540228000036169080070200030041a0b00750fa00b07000c0d060360607280c241c0710240c0c103000006402001b0461170052450030000980c90381009580a030503120036400c420f4203407003034810741d02011a0a01031104100d00f1020b204e440c80c061074a01c841c0d02e800c0d0b01ba074141c21500001c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 967875755 1250 967874505 967874521
    0x40801050a0204031709010f081b0f040e0601080f01120303090b100f0609080715031e09060f1802040b06090a03030c0c080303091e01140f04020901061e0813020306 72
    0x2810499010302122030308070b4003065655945200c6c68001328042520841d03288600b0f8414031070942e000203030f800e102c140c800c01000c92030840d42024541451041c0001303420b001c0d0107902032105802c0042801c19400c0c0381000350b50034402e0b0308140030307990744101e2408100c0c6c103141c131a4001c0420107400c000d1110f010304000c0b06c989680d496a0043d985c0c9442c90395000510948a40c0880d401c5900f013038003604141d0f040c03500b805035004031003600704100350f01c80050030108520300b8982c0d580c0f1000038000207080019460800103030348807050900700d294501009107038014666005103000b240c0c101d50004103801040001059030040c4022641c10091a9002004050b000301c0c1c28840c01e400f500e0041482c6030359000003903581c4801c0324041e0702a0850306642c200040d030319a0301c403002e8003464004100046030403d08810302c5811900040400000e805000641c249440c2031340c09807440c0e140c1a081120b00c4002d0f0240100200410400c105500d000900d80c805540d01e2100303081e5000b030644855090902d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 967877005 1250 967875755 967875757
    0x12042d090207050114060a03110f0a0e071d0d1104090b0702030a080f06010c290a0f0c020703020a12060b0301060311031501032f0411180102012708040801050a02 71
    0x2c21556507203081c0700c0d4107a08032212119886084010004c40300f00f401d6940311260702c0b04210003503400465650969995076507a101c000060310505003014810318244400425650002203462a544400401c00c00c1c5074603144d00440460390400341040d0380c0c120a501080c010100c170400505106018414000c0341a40030000f00103168082e81d404801e030321001c401c0c14005000b610320383d000c81c81a140802c00543c1202007840040b424030864984001003084100d12020100e9816959030f5464450403181001846124094466880181042d07415030740440c0440000c2e014014014541081490800129030080b910b40b24000e00203014a503a6854021400b400003c215442409040342044040c0751481c003181c103c17a08002082e0781410141090382d41c1d0010810444412502e66800d02181c0e15540640b03902c2d01030400003c0da07541940201d0071100f00c104405941103905002c036580003151101c01507080b6004100d42040ca02d001c0c0e01d004201485507901180b06542000c040240d1002164 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 967878255 1250 967877005 967877017
    0x90f031403130f0603142a0706060602160b18011b3f020303060f0a091d0111040803030109020d090213060e011d070e0102070f0b0301031412042d0902 66
    0x10b1000e11012441c10701d4066402c904840c10030040140041c44d1f295504044460383c01c032a141482e507403405255407141d0044d9645a00403c000d41d200c40300d4410098080316013039008045514445003040c4c2c0c0710a00c40c0401c0400010b403810840e00e510040c07902c1410f0300d00368600a41c030640c41e10103c805210401e54403049180d103401c052500c41c2d0145175504405491420300001079001d58038641d43c5004000c090702c3c000d460f59170011106a03000c110703e103461240b0b9958401940c20101917481f08a00da60079140300c04d814103240d10090100304005980082900e056401c52040503071101483c51030328000b00007410b030180d1702041c0700d4192070310180994441810b0701c8040e42c0114280c4e0b25812507154440e41c0321a030030070701c0d4803020008044c288200501e0124100510558a00300e99a240d80401403016070450546030ba00000100304100030f882e200c6807145041405420001c15640b640c03a124000c5105c0c1e4030240031542307000100854240c0101810141811340045840e48448150b00250005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 967879505 1250 967878255 967878257
    0x50601023a050a02060112060b060f1e04050307030b04080d0c08070f0207181806021809100f030326151e061c1821090f031403130f06 59
    0x2030102205402e00c10303400c90702c60700d02c9900140b4590346002c403040d0a0542c010425107a896a80781400d501d580c6000c000c0c03111041514540e911550246103814a8243d4045407560030001040100300340d44020800004881d00305042d214260354600784008184280fa00309549540b801044406a9400031031960007002d03140d981d07004c2414494000c0ea0780b101a4041e21a505a00900000c400c0340550405110f4a5451300301c01c4860456545e00d00c207a8101c0602c90b54240000d001c01100b0b418202d42c9903504c0500d180d480e8011a01d403900c2145926a140800342c108003440301c1c603241e81280c0040082c0300d2012000381c43d000e072815180d103a0f81188502000d0340f1424081031004d10842c1d1603070708446009001001c03280741541101a0601510402c0400f4601c90344964205000c0458400e5000e01503018944c0c81c4160070380b41d000002a0203018421f03409006502c2c3c800c1c41006200480c2e0810740364442040e49412404d10742c01451030185081142181416500102e070b480300c1d24201d5800c40d155 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 967880755 1250 967879505 967879603
    0x30207060c0b06100e09010326090d140f0a0b060a06021516030f060308090901050901140405040303060810150506040b0d110f04031b050108040506040605060102 71
    0x16648100c0710701d018007030007500c000700703000219a0510340750300e02c01c4900d0b44504040c0700414650001c0381556400b60300580e83c07107010007a544407070b2040b068225850704130050a07500c0c00b600300e000252003130030012020b0000e01c8407258210b002c0000b04503148071070441030b08445201c60036103040c02400c20b08884281c0164800380000601d90b00000e030100401d02240040e10451365420801a546440348594400305525100c4036002c80601c0d01c106000396000c7d12500f5900c1800d0030501200e00302c1070303000b9400b0710403040040021801c0b00226040d90f410031200850140c941c0d0074228040c1141d038015003954024201e01c0b0500d0003079030f40880c03408100d095001702840d50700c4c420803a16000d240300e03407070100200304141e080c0d1003716407042244040114285003002c446102101668026400850b0380180c4614034500142000300410014042460102e005103080e681e41500c4410141c00101640d86035404224507a009011965040584819a4559480200c10300203400c0f840080b1581e6540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 967882005 1250 967880755 967880759
    0x60507021209011b0c0b130815040b01060e0312180406050a050d0204020c01020408030f0d0b0306040309031113050703020d11070206030f09030708120901050604090c15110706030603030207 83
    0xc180c058a1100c6016182c900307642c0020144101800e20304c600032200c5d00e04c04600412448400c1000d0101c8100c1296055950350400c0a10381c81c0a4036144101c20001c104810800020301d1001068150354070307890b01c0b203211045200481e181a6022070421214000415040800447c03d601842c411404840c1804810b94031014008888541e00035a500200502000c1c000341c00c01d90028905c9188143c00145000e6803043d0050170740d0022850348550000011320203440165901400b00860011006014170b4202640c000d400c3e0005071000500910822200039119514154205280c4406c80400d00061803c9500140203620a0310450259890442440c4040308088162004154090951031450f12440ca002c0445403009100080e40e02c81000751900113203400001d01041c46283d0300146240c104150380a0940b1070003400c1500441c0351030540408224100c0c200c108032161112903004080221a00b2600c1c100440f80c13088580c0f181000001c2d5140c0d05034400c2c01164001e90a03208055 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 967883255 1250 967882005 967882033
    0xc0e0c091c021c02120f0a0b09060c2b0606051b0f15040c080312010f05042309010213030f02010809030a080a052d0106020601050d0302101109090406050702 69
    0x5054144083d400c1403055401c100110004080c1e86000ca0000b0510064180400c04042c9046442c01d007626003034101c44021410804440c900981041940010304500d1074800e04041c014010f903030410210410340c0c0703848003440d02c4612405501501e0000140800c80d110b54002c0d020b1b500c03030b04400044004c0075003c44a0614040b605400d0a1640c1020b028404454482480300f450060b100b620a410800b10005e001d040800040840d581e039901800f5081d80f5141d05494400e506e035200d140124101141d88104100c0e031140b10300013110456145c04203844079038220340240074000401201c42ca085401105000124400d405024800d0360350116a0303850343c045c2d986034011801054081005580481d10344c0c00181c003c2640a0a140c00d003154903007410144514580f80f290003407125086082c01803007804da0601034175001d0701003990074402d811215a0000d65a40c85030b4003506005035600500d000c60b146480441e5071301040100000b43c2c0d4102030508400904040c4d503100054412181141c0e810 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 967884505 1250 967883255 967883299
    0xf1f0803120a02040b040806040201020d14160c1206020d0f0b0604030803040312050406050f0709051008090c0409050d12060b030a050a0b040c030c0e1509010c0c0e0c09 74
    0x149002102840c1801c08081c0e601a002102400d1500c103543c09210206545041201400050915200420b01030a040c00064144409403042c50100503c001011038a0803204080701e5441c0620b252500f00e4a9890401c2c051555543c0c00103044003581080345402d00610b50083c00c40380307503500c0301000620f1841c5100350807103840c3c0207001d4002c002880100049500b0710044c540c00750180c10840b41e1040d144071490103c640c12036049810550b83e50501c040ca000e40e440480e031051042c00c101200320305180015100010801016040058410006800380007e115040b26a41c002d0002c0c4807404d0f0520309203466101c0b03203c162001035041c4801d080340c1100d5005041c1100c5110964030328644404903100050f00000305184102c42e10740704030614035103844c884d08008020381d540000304410110f03801026001c418104c92f10421f000306400700544201000c841c0861401d00344205891031a00e01071506003141c1d071042d100e4070002c0b805c010340c1c0402d1078020410b9800807914007041c00a80c0110000d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 967885755 1250 967884505 967884509
    0x316031716140f0102030f16030c0509130b100f02060c0304030e0103181a22080d05100305010912030b03010c0207140a0810020a0206070f140f040308030f1f 69
    0x20410390741010000306240b201d08000d41c081d1002074a91010056407450b09a902c2901c2490306a0140b0f41005010b92884814010010991905001079264001d0042071030103282405841541519100350398565035601c0700c00d130006d0207009402c80e4140c04501404804440401c0405800780c04d000600889820003100c1c4100ea2540358908091819001103004040d20020340019265410f5030f60080341016501ca22001400c102014051402d03010240819100d020300c1180c0140b045420301c00901540d007a120048680100064513a44014801c04a480746034405400395280403140018440c80703003800c01d0035007002c0e10700703021902c80c0d0018103003201c1030030788041c00503000520144605200c00c84d84140003a0001c0c1a4201940c440d0110b0341080d50000c9041c81082d8000380d001c0390aa010700c00b0540c01846400e1034800107081c0c80d00a071443c103071350f1214002d4003400142e581902c01084251400796800500a03600e80c45c1001c05052514416075208806044416007804441480008001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 967887005 1250 967885755 967885777
    0xd140907171f0216111203280e0d0c1e0602100e0c030114041b0503030a21020a020105090f0601080309010e0d05030712090f060c08090f03160317 64
    0x8070926001c101d010190b001050a40600c1c0c00300300c1c80c45403c40311100000c0260140f40041c0210748010100060001b4250b019511604107004080b020360016109500d41298640702c42c0c00c1c0901e44d04110390310a8004403c2c1e50021460034080140040c140e0300340e054071203503c10b5440004450880c003d171143c182c0b0804c4c00580c8007054281c1824140c0e0030007a03140700c601045401c00382d101400207085d1a030300c1da00c0030401360420381000203000224201304111903003081e200f28594181000301c0e440384900c520206c10300c06400007120395030350741180320020850b030310740110f4454510890003806003409841014181c03280d040320002d25100450114100e030300440c0114540041c181c01583c248a440d41d0596100340110040000704805000600c0c1071417166500c940a8400104c0103001480c01307400002541809450504c48640c21038845072850f504460015154030142001504034490060090340600400a05045002d00e090201c020750b0700c9000380c806403c8654102803118002d00100003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 967888255 1250 967887005 967887013
    0x1031e0906061a0706050a1a10180b040501020609010c0207140609060309250b070f06020c0d05030a0c11070b0a020a080f0d0f05040b1b0d14090717 65
    0x1400160859004160161080c9004141140e03985100100c05000c08580002c0500004070301d41006014400c0941c0701d030f9910420041892000040380866420a0313a0900500648100d10f180a001e440d600b500e080b44084941c440d5519011640400d421520030300d070152062201080a120060151031407140c03c0703a000785446403a0a2914249c95000b5a0f11a04146e0400ca01d00c1291602c0707000f1031054071140000d0108082c8020041903903203a07103920104a4000c92824480b540c1041c04460030540c00c20710002230790f0400d0920700c009120b00784600d050b500c6100f520740072158001010314446c4400183c20800813402a0f0144c80c0042a040352041981010006111584461002e005011030610445400b518265952080e9034003801c0200078104000c250316a6901007401580031007100c4d00c4061109041590b10f0444202016122841e00511a011150302d400050700392401125079003000d001e0810103204144000c1c60070b40b41503505001d0407901203141980c103120901c1001d0544010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 967889505 1250 967888255 967888301
    0x31103010b15032806050a0501081b0a3c2303090f0a06051f36060303120614100804020607020a080c0a0e0c04050d020f0d0c140103 58
    0x80009640010000c003040040b001c0042c245a011821501c40505902130001e441810f040070000c0d4507825500090401411030304021103041000303002e404507020100300c44c0d11181500001e90300744544001010900030306402202c80001a10800e0603024500340c540d10360751401c0c03501140c0720f80e0010240f030300be0402003816050041201000b10717070014809003529000010b088009003844400181601e80585aa0901540303100307812040c0c6a240d080080000c045240c0900d01b001d41c0d20340c02c2d91411450b003104030141e08001031021056480c2501c0710030044a506e81c43c002e00704202980c21102854982940400c6010402d091040360f02c0004044d442c40800148044600b54001401260440c40c04d0240c50010f896000c16800a003024401400f0101d512030180002c00c00c1641c48404806c45000070710001b80c8000044a09075801690a0303107803002c071400481c41040c10800c0035900400032205800900408000381c4087d074180580c47c0710b82c04107040044054800f4440f8401a4014001038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 967890755 1250 967889505 967889539
    0x20907051206060a0212450915120a0b07171501080c070c2c06012a0614010803070c080303090304050d02031c020f210d0c05040b040f031103010b 64
    0xc0c1004900070300141040c0302c03800700e0303040411484400c004408902c007100d4149810b0261012407000314140da180240f4a0243c601c110720700e044490704c50040a030ac40702d070b201e0903109100444e140da810075084801070500180040c02c64031411068000706118601160312032141c180d10700901c02050f52450050740b11042060107641c024441100c0355a002c03000005d10b6429140114886c0002100d018803452290846d000074000082050f4108a41110038501b415081808115064114107041905944518003800104009003034050a0794441c1d000007641200000281200d030310070282c1454103a034a80c0255540e010030f03501c42903950402d000038000c0b130030071403801131103507000404a9480342031000c0000480c8030010541c40050b00079400700b0701501001c00001c0c030707071810610001810009250058500303000f040c18a484054a40c10b104a09a200b207060f00c3c0606608130000e03513200d56400080c030031242907100480303012059226000c0c0c01e203410712400050071405080e040000701c040b20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 967892005 1250 967890755 967890757
    0xb030f01060807021c09030b0705031b0d090b090c03070b041512020d0e07030b1f0e040302010204050a060909110c0606010f03020409140a0e07050105120402030a020907051206060a0212 81
    0x800f503000c501c81c41400ca00d840e90390200c140c011095039100d030250142142071120680c00014101028230004005210780100c40c480001040d08030624066241d000900008000d008003000192048000ea014018140004540810b149801314222241075685980346081d60280348a000c4420901c0102090614000d04040d540308a90000052a1044038074a0800312441c2482d00310343e41d0307c0f0407400c1c010090900005500901400600c4c0c04c1d07808010400c3c0c07510038250050410300d4512002040400d8004d4050320081c20b4018510782d515a00c40c1c00c010111078662050301c03020340c209000c50b00c0d503150740000c4807101304510014103071039a540c100540b200c42c140f8402004169003000b0001c0d000c8014850400544289481c404060030071030020401d5409501c0750141a07001008100100c2e0f030860304640d01c5c181e22a40160b0703a0364890000074142118200007035002903450080140007a40480180300c2141d0440d844a030079144c040a20450f401804182805a4002181c44d03064a610760 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 967893255 1250 967892005 967892011
    0x90a03081306060605090906040e0a1707050f0622021011101506020111030c0423060a030902100f0905150c012c12121302030f0609070b030f010608 65
    0x1078440c401001180d039108126001c0c0e9000e00001000410710403e1450100d16003604a482104e060182c0013207410680e0301e4107032a4034002c1c4521107442c40450300c1c1e00a1401e5640c0260000207450840c1038a5404035203a43c411214050306e00c0d00354100d41c0c41c1e418034200204a09401501c030100e00c6020887c00d950f42241000800c242d0b114100f104a1070a200c1e000d94010641c642c941e4078021883c00d04040e080d15a0300b003083d45110820720030010040080300580741200c20302407069591180488001e1b0384000000142034200d04001440e05646030903400120b01244240d400c20811140c0041c1100c0c003003014504040010000c2108010522b0041c1080259000300041c2c01d250140d00003070036003103602001403011a5200340c50fa50460b04400c0d0006034044010002810300d0b03040250308048240f150562201d115205000031a01d005408250b1076159680901124500702c8090200c030b0307a0716004c54040c40726103e01c030f00204004461405981c0280300c1010740e0f01c200d9080c1a0280c2d0103840013 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 967894505 1250 967893255 967893271
    0xe011a09031911190305030d15030f060c1e020c063001031202031e131e03110f03300a090303020606120309040e070b07110306070305090a0308 63
    0xb41032003002c600142c15465070311034440c08800410310102e4041c00348a43c0061807000c03840220340f4042001c1103000c41240c1030f4080d02c020019003840e41000c80c600740c8030385400c080d00c160743d401d00080400980713a102417000700a54466486840d450400031460300c59101d13000740140c00608100b0120705014015103051000b002d0b04400c8510740d400601181e0034110303411100740058000401c103101c0c0c1c00c4418240b8024501c00b541c548030545081805110410440c04100100010112000340349811000c0151800000e0140d2036801c0640c0400314003258041501c403140004140c1c0b41916090844614801c0c4c0170b4060203884000380409426407900d400b200040000d60303403104003911098801084860620340301c0c0b03200f8500314103009107040c800811150140b01c01032002c280b04030300042602d0818800f200e0100f494480c20444070304010245c2c2c010650001c000c00c080d420081c0441c070140814100360104d802c0382d5034941c0104c054a40c2921400700030b40001a40c480440d21032404907a00c0441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 967895755 1250 967894505 967894513
    0x30f081513021908010602341214010c09121b030312151409100b0c0d022802190506070809190303051b07080a0b100e011a0903 56
    0x40030340410303a03004010344540242a400510071251000d6071210f044040524542200b8960410502039075542c512550185900b800d403451046621680218003020010549002100f5586a0b00c00d8410583c810040b01c3c030080d001c840c24807458052050b101c0328829030351601100e500c0c0c918120b131b212501040c26102e20000c4d200c5450b80703840f01d003c000010352090307584140000c400c81e800006c85008002445080c02040d0040003546182c40c10030a01078003c80e41b41e5a01e40700d0100c5084401c1855004081a010100d03412401d20400304024a0b8421540c00740c9041e42c040056041aa00009050064490b040310440c03000d410301c405141449018190103228094607400054a40d40001000b01d8010300700260701c0701203081060b1540000c0d1100f00e01d1004050455402814502886808c4d0018604201c1c0b200001c1e0001c20502004003250020748103058000e04150303000f1541100e190212410181300011221034403038415040b00c1034400080d0541c48800d1002c25980d001c94400e680c035200d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 967897005 1250 967895755 967895791
    0x13050309030d230c030405040e0f01110d1112011e0e0103110a092c0a0c0f060906230a030209120c01030506010c02130e0f07030503120a0603030f08 65
    0x90800c4162000c10b801d8483c8000268080090010640c820340b00f00070b05001804608a0a0000426a8152541250089034151102c01c01c0307440c02006101d80d110560800d8029075104480300021b160100340c240041c040310803500c1c1c500c101485001c440c00036020b02000100b21203800141c1301014003004030b19040c0300c0360fa40e1704840a590000c4e023040d07854045006224015281981c001402070050160502800b100c2d100201e004861181c42c50b000209030b51f03100c1e8420301c000d0281c51340459002c202c111001c0d4640036103186114050007010042170440d20080b0324140149510110881009004003150110350f0100450b03401c02d0b0744000c1810740070300c05520705070f45000744c10505003100e500402800304040001420b50b80041c00c01410b00441c0303090040581c8584003e0484d00c010981d01082d0240f09a418a00e41402c50018002d10301a9903408000c0010100c000c21064030b6404050341641c03514641c050480e81140f1005010800c00700c0084c203a58068052035034042c1e4255105080c001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 967898255 1250 967897005 967897009
    0x607020123030115080405150405011107050a0c05030f060c070309051003020901030c031a0616050a0c080c01140d05090705041a181b07080f040f080c150313050309 72
    0x70442000822a00e2070100051118001e4110255894100d81c680040c49007001c2c1c40d4280c031010400100400c030322041002400748602504980110080d404609a40c0c0c05241441a01c82c1c11000d0b0886040081d400001020f103000035824854910342006804692554060b541c1260300c1a00b0403014010a070100041c0c035682e0000d00c50001c40c041d100983e48001c1e06000404680042000b84245450a13207940840242d803004c4c44206502a01c200d941c074615103203010001403080714010010300c6010082c208004800c0000c80c00c80d00344000312404030785048010348240782e0081c4006940c8106204a01e001c01603a005503400107080380542f501240c485000c58199124a5400a40c8800700b80c1501e4142c241040e034034002004120411a0720305042422034400040450b8010b040d2001044183c00d01c40700d9411195403d041103885079803035a481d4418402d912461050281c1ca02a4412081881c00d241101d8040e8414400e4418510b0780c943e080341841d1818075405850900c01803062002c55 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 967899505 1250 967898255 967898297
    0x5010501060903060e0607050a1b0c03030306080601060311070b1f0e071823031002030f0a05070c0b0103021512010e010509090703080901030b040b030312040624030206070201 77
    0x41d000e1075031960600350460410b9020703110450310009655200c441080720f2240e00000b039406030041c2e454120112540c80005000034000603001a1209183d6903001080542507840751086034885020344030070760780c2c7c0e02c029403c446032118204240e080c02c120640000c0c24990005034000c0343d00700c1c00d074010020010b5692010000d030b003007820004885c00c240116690061100d1044411103900e85821905003429a0009842c440030075042c00d800d401041170300d54040c0080b01c0000c1c0000300454581c030705240300c030100b00400e4071103a1400703240002299425126145003101248c000089507604d902c2c41c1d091005c000c042d42405801c490052003548103420030302c500700d8001c00380082020744079410841088086600906200d402c0c0d401500c04000048081045e640d80030700c242000125508210003180c081c10514650a03458080040e907195141c151079030305070103640980c9003001904000003000c003003400054140341c04140c001a081006181420045c4071403881850300440d0340240075025414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 967900755 1250 967899505 967899509
    0x14160519082a040c0e2b0602092706090a1811030106150f1107030212010c03050a180b09190b011a030106050f031509100311031b1002010905010501 65
    0x11110003001021100940d109403415a80b80844080141e00e020340806084942600420b80c083d004282d0841801110305103a58000b03101580b000c0401386292410034000d61124569038071444804120301c41102601c040182c0781e00c19004c02442c540c45440800c00d40d0760000300b1200c030054840d1160302408182c0425212401c0c8070703915400c44100440304147c251110754101c4001c92032800140c4403920303807118458400300c8080c01c000c06031000140701542080040e13000a9000402c2d089481c1084005601c0510f005440e55403c1145480d40b007075107011743c0d0320691840d0081450005480c0031820010350b85400001381c0c01100c514000d42d0340302002c2011300031010341c2e100c1811401000756003280c5400ba6010381080a04514540c1002c0f0054406c2c050580e04000841d004030024a0030713626480304000420004008104900d010f05503c1000010360101710b81000540c0d00340900390030b000580650351080040048100400c07141401700d0844843d0b544001c541d00e03117140001040c03080c4034640c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 967902005 1250 967900755 967900783
    0x10204090b030c040b031513081c1b020706110a061406090c1c09140106080309010e1e0607150c0903060b030606150306030f07080a1416051908 63
    0x200e100401c0304150038142d080c031072180244e003400803c20300c5540c0812441034410b00010b00c622a40c603160070010141c0c02041c00240340410004444080ca440400076001030359502c142071118071241074a1480401400091102590106105110490064115100320394008044a0000c541174481c0e901b13464002010707030f10021640c01030061a0400c241690f07401006101013600c0c00c08090001d00c80b0b0a0000b410f001c04a5864101c0c500f0070004000b00e29024403090000d00003282c84e54080c1c1d4595124002c1da601181d058841c500f40e5041003064001c84060741c02203154541da1200511100b54071081044a402d6182140f085502d01c8a10407840e140049075100180d007401c0d0b24003442111645a112440703644507204002ca156101d00b1141e1f15100d070341070700701c0d120340f00c1e140030914040c01e800e40c00c089405a0600425246000190540081c0c010402d0034140b81181c0c46164450750b800403811818600d0500c20b000f035042c11004043d40071142e040c24540d00da692009182052003000d4a10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 967903255 1250 967902005 967902011
    0x90b03280603050105010f0e04080703050f03070f1d010525080c06060112091e02060c0f1f02072604030606090c0e120c220608071e0614070204090501020409 69
    0x1000f44002446141e000d001030420110b02d441c03c0007003125a04200034001003c020000483c3c90406200701d00b602c400301290031440742c4074100444094115100340080380001034200c40444c0310411000e241d03000410068580c2d61030401c0c21308070f0008400b03c074601152142c030400c01c860001038900c001410600780f2103001c4e00c182e0074a071000511504401c01310030400c4d03081031440000700b00202c04008441041c3d806a4004607400c0c40031a909002e03602c1c1c0d8210700c1c094030305102400100410741807228280c0916100300039008494007422409244400b0303103007070b01d4149409444030016241c080c08021001000d030420380c0c0c0e40e482c00242c61140c1c0101c54a2520b40d00904030154005552011410341120a181003a80c078410301e40c1c0d9607150281e080d00c6445903419403800781c80c51a4192104292042061004a8032205071580c1e0316002d126149418100d484450940c502070402001552444c5e51100c0c4041c612a2940e0441d41003000c0c01c0e40d10990b0340c801500046d800348000d200411880c503000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 967904505 1250 967903255 967903259
    0x3070c0f080606060405040903021501090c031b0e0108090712030e030c0a0b0901030b0a2117040e010e04060e160602010c050304050307032106060e041b090b032806 72
    0x55006544103500c05030700c6078050070a00010b580c0d400182c80aa6609071000503a05089046c105c1c58004043c04130700d0305108940010135104a181c12002803084152800e10010f01000050503081120b41881800100030180c2c483c129072040c1105900442d000c400c83c1d59890321000c141148440a0b202100824500d0000c08a603040034001d00d100541e045a60603440340c0b03850b10700750b6030f84030361503226040551b0384031070402e81d581e840d0000f8007074042c0301403c80c1c19014140c03600506140100c0b082e22800c00601d1529612241da204a805449030075803602030a07440c2004070345080201820490b00702c0d84890090402220400001840d08801214980d0840c50500b0190841d40f0751a400320030018100200008a440041111003195162920140140450150f10a80881d00803089040b07401c140700040d18a0303001c40300a03000b80c000c0700c00700091810803081e140f8428044815101090f000d4604010b481e40707040296500010302102c1c10200d4010b1980c8204043e8040c9541108603a03034541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 967905755 1250 967904505 967904519
    0x5011107031b05060106030b030115030b01050924040b04020d0c02070e1e01170c03030307080402131e09261b01110f0c010615120b01021f1d03070c 65
    0x10811180898920b504024001510307426281c0c0414080c050505442d03032105001502d003544403203116608a541003005075282e1801181125080c81114861440f1402040031b0064020303440c0800004403a001c1c602e0706e900024080500002031031558041e90034001d010b100591409546a1130206034041c0401c0d80c10148000e85403100900150780003016800a458034a2010001078156429810280071489600c8651807401e41082d00701c6d0381502010080c440e00542001c030590060b4821180f0305110180d0380c1000b011500c00c004080b05500c60302c40344241e1400c0311380c49900c2d4180150b070b01003810182d003480c0200c40081c030002000d100c04001110b40511004d0503d4205000c103410091020204210b1134003021f02503510505600d40e400203100d02808403d43c4041c1c0103001c1d0800c0f0700f144c0c02c1c0e50a005000f01a603400000c010300d05129540241d503102080b89942c00003038a903c550100887e4880c007005142d51400341d8488118400403882e250b104002404080c1d2049205002d03c909000c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 967907005 1250 967905755 967905767
    0x50105010608060303120c0f07030f0e010c0c180e010608030405040e010b100807020a0c1412010509071a04030605090618070e04060519060b0c16240c0501110703 71
    0x70001e8208020b0406100c51070754007008540d8480a00d180000d110703140c89040f2852446030514451b43c100c0001918000c00d40c00240600c4040040d84402d0ba9200590005695041241e84002c0403100800e800b03001e03c0070101c00b004040355250b10000f44907003880140e9821284582c02100583d032002c0350800162400b40600b20748446400d000344000540d0348040750314021604000d4051103101c4000545261003040070304d0105400c4003000714415980c1900c1da510403403880a0030300a2100204050382840d050103440d0151100500070501140b9203004d01c0046010803001c1d08505000b0000040420280d0241c140920806806403200e4248591070782068103604203001d1443d002104100041c00d07482030407036480303038114201050b0743c1d66001ca0082c912604601c044581e501d016808a06824490060411420f0345421903006c1101000151a840e40074400c1c0d040c50b56140d5400c070403d00500c5c0090203248034908089582480c19921a401d590004500880601e008a420028140e00107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 967908255 1250 967907005 967907009
    0x111130506070803150d0623091f0b0a03080408030a1106010e070e0a0e041401050c0c030d0b01020f0a1a0703021603030e0c030d081b161401140c0705010501 69
    0xc075940e242040701d544800d01c80c040244035042d00c0c1e5800d101c88445807035071124850b92950024040281040c5021500c00b4180543c050707101c5d014103940010385014001490b10034103241282002503100046800402418445105540281c2140c200200280c00400508080c3c2000c4020356120010107000800c4080c1d09500044550300c10801007007840050620180c11a4442c03902ca00010901342c0840c20142d103d500104514036180204000c3c003448400c1142d130080755000030b00c0562105d8040e2816809000108065500100522058400d5039880340418500c180103484030310382c8201229003030114640b8160341002981502c041c2075140c04011550101c2c040c14118282114080602d20003520064018203150b40c450048081e004100041c0000c81e00042c00c50b86041e081a10052120310f050b1817403100700b01b500d5140640120100252500001004a540e0034082951074078694400c0755908807015550301d10500024200b20b1190034400c800341c1111556508042c900035085510503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 967909505 1250 967908255 967908259
    0xd05060402120109020d1508031206241608030c0c070e010b0412020a05131d0c0927010504241119030b12010b0109060905030312090c0301111305 64
    0x100601e903071014124100030f041d00c0200e81e00503226003866940e1401401c1c40703682d4003124050400d0000e040764001004089201c948031043e44251a02000d10803a03085502c0700915003003005c0c81800d82030309098060412034075075840654510149440701000340d40142d80700003200f100029210780e03100301000b0003401040c646001400b00c3d8580044254039000714040e4080b245941510b41c015541c5020707101c005058010851008051500241002403034101001c682220b010308460486101c0411080c1400d4000340108031145d0305c034138086205524000c416140c101c100c002d040d04140007481944d100311722444d45c0040c00c020320030300d8050100040340003c40c041c1c2447c02c848082c6070f040080d034001181400384603843c0c01e9064403d4002d4941c07901829007207a4411035030300c001541500501100d410a0301c0d0b1268103a22100d00320f0300d042c010300506416505c1000341854002c55002501d9202c8039420a541082e59401300090031b44020f84112010700e240480e0400342501000e070250f00134401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 967910755 1250 967909505 967909507
    0x3053d0906060f02150610030f1a040b0a03050703080c0f0106080c122b0c050111030406050105090112020918101b02190204180f05010915020901170603100606050d05060402 76
    0x30700c1c4800c0005c8000700014003405000c281d4410300b900a40110b0b070501d0020400380328184c06207800c500e02c188514102c5106600f000741c100e0740d5085c40d0307414400383c94110300500201802e544900306613921140320000c06120b40714a64050100a100b0680608444000780119000420421025809031801e44507140c00c040c80030741401901844205011003940580b210203c182501520381628910000d0120350900501500e1202c044000790f01c22441560100000e03600da409001209209004051034001c41002600140c90162132032030b40404e441024601c02c6102601d40c0d4200244034002d640a01e07110795084003100300d03420101454108038402020f52515080c9408904c02c01010064003959a4482521581542000004200b50030009214803009249442802070190110a0314076402101d441074580c5124000c41d03001a0b0160b44031544468132a45c10710300e46034050300050303141c07040b0060300315018610300955008002c16100d403511038407417500c5201030b11402030007a0f00c6688 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 967912005 1250 967910755 967910773
    0x1e1306141e0405010e07120c0b04180b040204090e0d0806010e010c2a0b0706140403120f09051209181b0f0c071203020d03053d0906060f02 61
    0x6400e40d520020140d1129806070544a81c2050382c01000d2410b0900900c0c05003a00c080f40359642000c3c0491485d206807214070b2426954016003a4500490103090403141d04408200c02191a54101c1442017000500062426640340754000454131011005c001a070070015401005980011503164016020300700024800d4000c8002010b12503488001030444c0344450f001405002c84981021320035612015044200e92200e0320001d003900860800c894960602d0300f0442c41d0304c011303441c00d4011640350700ca0b43c2d0039160300f0881c000a80301900060441c0c903a0303603c1c0440807450420042100701441595144d43c0d0400d00240000c0402e4000c4008aa420b504240160301d0726906d25600c0c0e41052a40030740d29100403d808007410700c41d0325101d04440c8900a80440c54281d166100c42c41140310b42c08843d82006024026070548000303c40043c0d613144c9400090103062402c11800103420100916400d000950f1840c0c40d61345a1260010301c0140d0b0390785000c0c006250010b42d44400a01c0c2c83c001080081 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 967913255 1250 967912005 967912021
    0x316060e0f01090611150403050712170103110d051002090a05090c030c13150914091e0604140c0a02010c020604050703031b060f0c020115031a1e130614 67
    0xc609100d51000c11004c0f8403059400e900030b000e03081d0030790420703d0210840c4c201070032300420390b80240b081a14a0840c41c000c20801c140694084c01141b01c41d9542400560300e5926205010f8561001d40c68001440c141603100061702071100c0721030108004001a10307400c0c0c11080c04031606031030704024010110300042c042280300b40c0040e25409400404100c0d682d284800c1c2d800030310701c0c0d15880b94103144640c4403803180058009a25000b0303100c1a8107407407010400c0e90100140070380280d400800070184505040082800382000d264040805000454005129103102608110454054031502408144c04490950a014043c400da0162004000500b00303034a4142d1030340018840102032103c1c4091110407240c0310310104541c0741e0810030400100ba1080c08d400090b07c850400d810065103462960340c500c008804a03c400d42c0c1c1c02c0040d00621440200c848000004003070704030600c200c40e008207115158110f40d0010310408a200100f8050f00ca00c0c0740040c140d07000060310011120407142008008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 967914505 1250 967913255 967913267
    0x1403030f040e0907030506011215050601050316032d0606090302220609110c0c0307060f030209030a051f060902070b04020603252106060e09070504050316060e0f01 72
    0x38644641e8080302d1503c40001c400d00e003079916031001b041400356000004444102d9100b00b0741e035a00840304154070102c5551014100c44084070090702040d01070012070003929190482c26002d03481d900700060014924a0860000701c226140710340300c0b02448040c1c0072030300010702444c002040c0034200b0341c03032680c110b6000490380110186044903019502c043d0022070b4146822580040c0048501001044080140d40c161540600703201280d81c8501c8848100c9804e0000d900b10403255199110a08240c2c2c1250032000303035108004569152207488400030101e002840101f00c0f800d0b01065502003e000070b2000703420744109034480d0003600e01c18041c0c2400704e2080303180198010780c1294116926542c1c0c840200114081c02400c0c0200d480161007101f005420001c846c541102b880d18080344070320000701f900c0c1030b0341d0316000e030500250501400e00d0660401c001c00d1360700207403d400c00b1800c0c1510b0b100840d09d00100401c550301000082c82c82085183e4101e0b901206d008011b98005900710b05041c0043c2c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 967915755 1250 967914505 967914509
    0x180602030f16060f02041e051f1103040609180605150c2b11010207020f12030c0f06070905120d081e042a0812030615030a061403030f04 60
    0x285020025814445611078080014403070751043c803c00180d01041000002034019010700a11000010051034105810144034000c48000a20745655003080d0329219441c00310101d1564144506040c00005d2504140042c1c009003074640da58211241c50405604103182840306400c4003145410307030038001c54031002281c2154582802e1920ba44d80c5446120500d4611030300c02c1d0f00820030f41141c41046e103555904003003801204540c0c9100d4404040c5070f03428202c1c41042c8009510141c0701884058504103007140c210078505040549003448500d40c442d82c10452403440f01020741c0c1100d030070050882e07080a07081000d0b0409a80b00c0c50403000100b00c0d1683c50510354000300a00c142040094990340f090722010038800098515501036080a01d8080c038010f0040e03181d03401c02c1c131001030a4092121f144211600f100e00d40c0b0020300304049a003510030304a0348081c0100e600303c04a0500903c40d151064000c501400c1d800c400010828a4495a600340f00000400079209800030004c0e031840f04944015141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 967917005 1250 967915755 967915777
    0x309011d070618050916030e010c08241306080601140d061e0606030207260301030305070f140c0a05041a1e090108160b03070804080a020109200118060203 68
    0x3103032100f407112071150310903280c0c05294030400d40c1c030801020002a1003150304001283d00c00340080c1c01c0144c038040c280d0b80b54050250010f0800e40008000103206002d650304040c0074a501c1e459112a140822544815000780741e02003a00c2d0101048501d0042015500408030a02c680300b00401c40030004096201c1c2c848081d001903161285800d600d425507440d031501880f060000c0040590b6100003034065002042d065820a01c5148015940d03e5415100e00f1401c00e030311000c2d40f642e0b085603020758481d00158002d40e00c0590a903064400076060a0181c2085894040200902502c0d2810050390a035580c000c035004500300b8000c640070f440c51300c641d034811040490b2100e1a0b070b44494200b80c50a6500605240e01c90240000060005808208185007401003981e401c20203403a00456409480107961a500050322040044c011480d000701604000e003180c8004244dd008688170308602c1d4a00200701102c90100100c04121580c000c4540d5a2408240e4204a800761400c00040c1d264056010303040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 967918255 1250 967917005 967917017
    0x60906040e070f1211060405060a051303020a090e0f0d08014202070f051507030512010308091008250c171b06040b040618020402040b0309011d0706 65
    0x4944801d05202600103001d60041c0000c065580d103501c0450461000e000ba0f9640c40b01035206100c1342002c60032201030f610050700c440d00c0c10706120009c451a078021503607503506402003000440107a41c0c000d24480180034013000882c500b111602c29030b08050612212422660001406183d559007201c641411109520b0f44211121341e803681c003122490841c2401040480c003040c05e0441200402c4800c50302e00345aa08840d48245c6030081041400c18a0080d03942c030106101a544290300e00400a010aa01c2807904e40d00388940044003c040c08000c0e041150054000b096440480c01e12134024520342d1a185081101800e140e590401781c003103031050104d010f81000c44005251406201c07181103055101d804042c00d080c420306043c1c5c80b500510703018000400c084c505503519410004400c2d010b142c110042d9440e17a1034030750b60180203000109541d00840c401486400c05030349c461010788010183d55142e03c0c0d4074035001c01d41c1c600f15800b42070013140f40240c900c0040c40b03240c000a2110151031544c04e00e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 967919505 1250 967918255 967918271
    0x151403331009060e1e07211a0a080703060213080a0b0103110109030c12080712020a02010905010f021b03010b04181a0705031902070b090f06010819060b0a051009180506090604 77
    0x1c8800614400780701807000d0070303840078000846441c6e00c230b048488400c02508100080003420844802d0452054200303d03841003000b44040b0381650300604198005200f1301a01544d0317120445e040c501c580740250b03124840a00100140f010a1a400030244000d29060160340e04603515440040464055000c1429458400e80204400c0c0c000312030050ba000202030032200c88065009554010500c2c00300e0000e41c4840e000a101d502424840d0764510007a006030071031442c0d01280f4010100000c100c00c0e03066490303030840102512144221103000c071070729024101d8201141040b031801c00c40d20164007000030a0300104030085501c0780a907500140c0380d102e40c0b80b0250f82e5010390f07400790140c40030151540089034140501d044002442c801800c005a040e02c8083e070fa104182a10b8070b604034184c42911085041d90790025046501c8941c5184000f401c00c082c55459001080360284401581404904040c13400c4c8130243c801e1048100901401c04140501d20b498000701300300d500050200340c0540d454280c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 967920755 1250 967919505 967919507
    0x10050f0d020409020f0403110303030c041211041d0f03130303080c0906040b030405100b100e1f030e100903090e15030a06151403331009060e1e07 64
    0x1120020850203c05648622031922494103a50091204a60580c1003059410b00d900b008404c0c1e0303124035001c2100b03e0600f40b400c49504d600300c049400c1120001211031200b10903580b03070320402010900010350b031000034001002c903d103070020004650145030301c00d00038080395014001e00352081e61f6042c600001291109940400140030700900554044000714004c0f0f03140c048400074522840c0190100c442456082c6606421104c010902d41e4001c4024002d00028901540d52803c0c0c510000d04003010003064036582c846d10b44a01c0000e140001d4075690515041d13481000f400d4514510000100504541580c01600001ca1885901c1840c248800014000003140300202c054a10107802d81d01c1480d41031501600030607174655a40a8521200c03004200030002d071441111a02c0301070001c01d4410548a03541c170f810304132010081c0b060040801002540b00301c80d0403050048030220141c0604504084510040e2001038020341201c581c0502080303140c1804030104192050510b00602d01070300d540c50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 967922005 1250 967920755 967920757
    0x31202030c0d050711011d100e1c020f1210050703090f1b0b0f04090e0708120301060305010e060d11040609090b160503060907031a090103030c0501060510050f0d02 72
    0xe103800c41809040b2030071910503002401040707824442d01c0c807100c07141c103010019507440301c1d901546003107524031130b805c072002d030501c2c0c20f4030b06809031281008020050345000060b07002c90b00f03464107000e822006807010114140302c40c0c0101c6d40b071b2080b54004d10400c60225520f035191040710345251056120008540c10900a52042c40200e070000c600e460060f116003800c80d0445104081501181d60005000405280010542d01d43d4505000d2251505141c50b249a0151881d009400201c0c05104800078900b075080142c040d45403141c8000a8607585003403000fa01301d5005030b10112410581804108850795400c02d806203407548051884190035510010900408894019682c807034940340e40e030002d020011803031a20412031140c1d09085844c10610860315808161000c40d00503c0107000b0a45032400394102039210040b10011991762503000c40043c212038400e078415004200303900714500600100b030007001c014220a403820451001d01100045c06031152410545500700089540a8800070a030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 967923255 1250 967922005 967922017
    0x3070c120209071404170d02060114102618190b04080703030f11070c1208041206090b0103080306100e030d18051e091e0a0902060d0c05031509010b0403120203 70
    0x1241b01240c83c001c0c5000a40c3d40c0713240400c403202520880c800040d101c95907066401800320003500720617640f06600c034280c1d601c401c034186202041000403030014403a954251540d11a00604e94818260711012141500f07100c44d03030a0025a0301c061621b00c07400f0800000c00c4a0f0041d40c4298501d03690280c40c01c08400510310001d11088043c14108003e200e00303116805807034100d004681c030240d2680d076407824030201001c050005001d420140001c000e030100040148400034056071003c54030406681da4040450001d0300100e4071100c0101c2808414180004901d00e02c80d01d40c14142401020480000d55802b480e611134010044c030700070403403040d40d050b82c0d40380010300000e004050503200c1408291866005003810780d00803a010000505101c039030ba011080d01e101c0282503181103440e5070704840080c1c41d1950b41660001c2e010883c102140c165845441c091601603a141900c03030414400e0f6401c0040b02428031803040d118140140700d10481305d0202e0703040700d0780300e89240c0702c000740c00c1740036402c41c001c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 967924505 1250 967923255 967923269
    0x70206090d05060601270902091c05150604021810110109080d0e06070f0e0d0803130c050109081222060504031b06021509030f0c03070c120209071404 66
    0x109070450400000082c003500400c026201c008000078207070300004449541e00030b04030001c1092041001206590342c014100d003040035101031980302c904007440384011a140cac0b08a50036801031040c0c0606103282130001d07410600071078043d8504800000e4490050254885281c8a0104280d8a11405000302405040040d54000901c8100080d003004030903508a110300d108114140201d8001a00d40451841c0c45000310740c030791114880121030f0407150780240c0400e10390003600c0902a0030100d41301d02c020b144502c50b0703880c4514a445503840c2400800e421075101c01c2c180442102c0500401a000c580040000340c4481c80c0c5440d01808030b40902210030704c83c0c0c20000c0c0e03910b0007400300781c8541c098000c0c000c6d2801032580d03400c2003526061000380c1e00890310500005801114890310f902c028a800d0319004500e500450341000304624100440f0790003401da50915034000100340c1c0030000380b160450b000700b0510403000403618075900814955980100440d01f00508018412901c004c0003003500c0180140c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 967925755 1250 967924505 967924519
    0x10308031f0501020c190801230a0213030f0507030602181003020f04030b0c07120f09080d080a0e1f061701021e0c030f0a03141006090623071a130c030807020609 71
    0x200d500181100030400303882ca02706050700c0001242c480c06402154651031500031800c01003803550321000209850101c0c01c81e0140901c1000101050b4240090440a10381245a5003402c3d500f20800040800740b031049020701d030043c02294842e15054054400b102d0304600c54180340c0d0f5640c082c2d0701c07451240c0c3c1c10051641c0c400c03054810000b075004012201070342442e20303072803010f640300d01c00903540e0380342401d41a0000c1e141c600010b0466540e900b1048104504408440d00c005800d840ca0780d00b0a80c8090940303031036a4504007045440009964140100031281c000c518014201d41d503840420042000c505c2c0c0c002000884001d40c14080044801d01e60b200402c09440f0304801710010081e180051361420100c1103000860001503078914420200e50007911a250014640182618600000194a104000c0c1359070842d44031041d22006005031403240480050140100c003034038040600c080d00f902443c0d000e5481c6a40059400c044c00c0042d00c0d084803010b5154281c500c00217a107449415041038001003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 967927005 1250 967925755 967925771
    0x192406090c03061805040809060d0f060803030610031b18090903030209040b0909100518030c101808040e0a06091404050c1806040c02030c0303010308031f0501020c190801 75
    0xc0d06038816825138a44140da0f200c022844414041a180d00795005000520b08000001d042d01d412802070034a50414400494182c0d07030b0524410845410742d0003410542c03c00000c01504d49050705c00304d00080d042e820200300c03030203c28510303009083c1040c442d64140031034282800720b03605500103e98001c107141c06040c00f07400300502e0300401940040d46010701136818014002c0e541e1404c04501842140550010051270310301c07000c550b01400c0040c0c08221030f02010000550700b0781084c0018142001080c0c02080301781c00810403002111040050040440c0c808444800060890030454089403448500080b454403a040203000a04465101206051030540c1c441c860507150035101c1c0c8564098401c3e680c0c050a080700740b0400000000381c40c120b85581c0380c00103c003031800f0303403090010113240e20460b4103101c0c0c142d441c10f25591007078105403800c11010081000c039188191188100d6424880d45c16020780c42e090020f5a1020700c2100c0e24412921700942440c1d0110400e15100180807280090040c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 967928255 1250 967927005 967927007
    0x7150c02010e1908040f080715091404050a0f06030303090c0510090e100909030215100605160c0509100e1303050a1d2706040603051216080706050603192406090c 71
    0x880a200783c0c0d496002c1c0e6500800c0440c003c0700ac0c07000325000b8800e824203810071002044020100144000060b40d0f841c003d42100105900c1020302030751080c0c400003407000303840c10200c4400e41180d004e503105c0c8a1121040e1129070707010130010304542010080840e1030711100809242d0541513001087c03900c1c0341040c01800d2540c006504400005803000f0202300e40c4540110b401c03452498040e4030003003441003088481051980d0340c2c46104600802d061032550362514000b80c0300030410703211284055900392040c0116140c200f40701d07802110b0b1541191460046a4000c0d00c14000c2c0c05096041c0035039031a4035007001d1070009201000750f1000702110700c0e010040c40ea100020001041ca4800540d00c0390000d803003410315100c2e12003600d420900800e203406401500141035400014443d2450031002c138800700142140d005000114030910001c00c40389030034401d26150269400c2080b4081c00d0a040c160045642442c00b070044031100301c41090182d4885040d0390151207030f64008010035240c1080f000c00f0b2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 967929505 1250 967928255 967928263
    0xc09090b07080709060527300309010804030c0302150f0901061415072301060303120510031101020f0f060703050123010309030c020607150c02010e1908040f08 70
    0x1074070458540c0d40700e6455109003190201c1c1107019174800f103401000007054088840c0004c484e12031401403241c2c840e0310103201241203002d0020949490303074884952000c9900c02e0b4800f00940702100700003103081c8401400001d00028000c2d2019003482225203890050610a100540b9100c054100201c0c0600f00030406150624040720000425460920045040d1032401d0048401304402083e10281091450800c50140e000b01c02c12507482410b00d04190614965043c40003031201480000034841d03186040180421140100398207000d880d00c401c21102d44050344401040e2600000d90308104d0100d140141c3c6046600c40708101140b090030404031025000113a1181b207003425580074469a40e0720661048a09000e440103a0316400014442215510039800700b0f441c00d0007031030b05c01198042a00481c8159002c08030036550300e5614991805032100d140244141c410051000b040f01c60390001c0280d4545440850b40c15003e80c80f0004501031102007802d03140a4441c0030030b541011503445c0c04071a56 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 967930755 1250 967929505 967929511
    0xb100f1b0803041a0703090b0c0d200c0d0906120c09081b0415030203071413020a1205010b0913050a0f0203070815060a0f1b12020703110603011d040c09090b 69
    0x803400141300050300248240100030503107078000d8611045807280c2c0e0001d81c0c0e9401042d01e1150040c5ea542c8150400b102c0302c11411b0305070300301e1120b0303541d11403103101510b0030300c4001e61b42c0c1c2040c491510000c101c1306074490350900c080400241e00007103550080d2400c0325070000a50090300c04ac41000c5c65211340202d004001c2d04480f00441d810841a035586092045068062001a50503001444100400401e90074680d1350303614001c1100404403c6810040226080302c2008400a04101e0805aa152052184074013405030481c4450034940b0b144002013801c04244501d4406540b204081950f105190300700d40044441c0300380564480c0b80807800180504000c45440103200c210030300300c11440c2425411250701003860756910440b188200816241c5c2041d01c000d000c3c0c0342a2170169a00131546d003e40d035054000039980076110061841c103241310300c403c420b5550340c4100010401045072520302e428083c45508825000201a40c86003041a440c1805a000d9441641031150b520101304002c04109d00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 967932005 1250 967930755 967930793
    0x6150a09060b09062805040e070801080c010e030c310b010905040e0307050d0203031603060b0306011407050a050105061314060603062407060b100f1b080304 69
    0x4249a58036408025a030142c801c00c1200d01003080900a281800e800030b00c00c904d65070500240c0703c01058628041605d24120950024401280503c000d07000e030454650444500d190030780103035040221513a11901c9035603040c2d0600112200102086d1000d00c10006000300044c2100701100060308844100c0806c8001c2078000c501c07822520010000380e11650390713060810303580e01d00b009081000340700050846c1211013000d44010302c44640054001c0201c0c0801e0b640941c05542c40f41020300040e00d1840f0b981030740d441450b0814a00f44605406041603030b5202000f4a040520000140700d03060a51050002c0603085c1d00401c0f030850148801500403901444c829250008020101d0102c4802c813000400200c440c50384801c0410041e18011000e540c00c100000c094441c5168041801555408200b0040c4c0703406801150400510405104811740c1020550f04500344480030200200241449000352080c020140171903441c03a2203001414030356592000f00316640e800e15040c0240d98011000c0a84 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 967933255 1250 967932005 967932019
    0x5062205010801062309090a0902010f0f050304110a051009030b06151605120a0305040c0b030c0f07030c08041412011e1802091306050a290307080615 66
    0x1840d5200c0e01090f0b040300c8a590b618601103144030401c86900c403440e103100c00e11078410302c50291159190b0b13058901901d9421400141b401442c400585020b2005180740244284900388407600c54111003220342c0701e40c0c4080b510903081c48a00000d060880703d5080340d6008001c140720946078507004091081904d009050a16540c4c1e00c00080021000703d10b240c5d00c0d01c00c80b06014541014a0380741310610301a10440c00c1d07403640345052007a04078603005501c0e0000007a2b121804d11007800b01c0c014030103000d0400203904515524001c404400c1e580b0800d4140308078250005090010300d8030600a100e28a540303c08880d070748031f41e600400321940814110440c4140301222511254440510840e0000041521294004e1410203240c1c0000c0020782000341d1690191100100140d03201040c0500c180d00b6003d640c096412141892011200d0041003842402e144c041d56045032201c1003020320a85404100c641c0f0880d90400220342402c1c8a940444003c1c4036060501c114603052428811244009031402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 967934505 1250 967933255 967933259
    0xb04140c0a060c03031e02030a1a03160e09150109020c06160206060d110301140108150601080c1c0e100b0a030206041a1b0c01030605040c120e07050622 67
    0x3021419510030b10020074110704070036000038000d401c0341d02d02c0da020b840100c101d40380007100e18059034004c80d0449000e0b55160050ba517005011015211111000e400810584800c8038009803481002d0203034100304490f080009844800812000c081c410440420035080e5a4a40d41c0704040d4116682c103130054007541000990f0110a044400c064440c682c2c003c000c00c0d1107841c144601e218800d13a06441182246054100540707007405040762415410201941540c5401c04907410001c980596001000c030100512000340e03406000300b034110440d074034910f507510201500c41c880314048000f0f1800ba1814504030303990b4080d0200e61552440310140b4144291070040040111510560200030b501a10500c414010201c480808102a41a00d1162881e0070209062120604150118260140d00c10000b041c070710350703150003620001c10b829201032059152092028241c55080d4130b08441c141e6541601040d511000c102e0b00380189000b904880e0380d0f220b000f40034803900c0b00034071710030501040c42c03840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 967935755 1250 967934505 967934509
    0xa030801170f062202030a080c0c090114010f11100504020108070f022a030708060709120f060902010207170a0516181505040c0c05010e070b0715090b04140c 69
    0x40b030b16005200030160003e90380300d049400000b9607800140b0400112803282c40010b8800700f20000700780e80584445901c03016505140c40c9064129049103010301584401080a451380c00c41e071000d40003003402c0811184842403412510b103090808010058400c00f42c01c21484181a402180594002e0741c905140d90395050701034905040b0b8025001c01603000c1403030303600b555141c071340c020403a11340001c0382c0c0940d600600c0000b8603001c01c03900411030300d40081062100264109104000500010440c080380e805641c60b41198408404400b900c201d0301c6030b65000c01c42e0710900501018044207403440d1034207941200b05d20756483c02201c04413036912800000c56070020a0034010800c0700d030311041c2d244824000007510406004000d8040042895036030002c22142e9642c0505007544d10780e0360750000c0701c0042e410600c2c2034a060585504e6150030490003809810440d00494a461b50440e207209810460300054800400f03400d20050585c11014040c070040201600c00745d403480c541007040701c3c5650380c00f0302 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 967937005 1250 967935755 967935763
    0xb03191406150901050a03180f230109020904020f0a0504110405010e0301090b0103020d031115041b0b030604090510021b101505040e0312011401021605090f060a080a03080117 77
    0x160a005ca041809071010952180c1c0001001c102e100301d8141c0708090030369a890410030254400c540b07601c0b8089011021903915066580303406240c030004c0c0400262500468060320000c2c00190140f202c1c1c928030340c0300d074072203035620b50007084054410072182c001c0f0000000150024003642d070014118164030b00d094501400351141c6c10b9008141da015a03440c40d03080092280e0310304021030030710581142440c2800c0092100595541c101549030b0075030719144c64510300c1e00d000c000030341040480c641014000120b0b84e800b560b070300810a0b5000500d42e50541860b604d00804221100e1555000052000119515150100704040c0180481d504442000c000d001903480c03c0e100d18410b0780d440c2c00100058a840d400401d082c080d03400c00d99241c00d0002850354110a8240c1001c401c0002c85511440d0039607040045162007089800814100c40c1802c002a66142c0050400500d00780b044020ad4650b980700c24420000705800d0048481c0c110007813801501a01d000d1085900b000701c1e1510020b601e20b0042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 967938255 1250 967937005 967937017
    0x1605061e0108070501030b1c0303140c0a0206010e0a020c03070807210f030b010c060509061f080a1502271c030813060608100f1a01090b0319140615 65
    0x1401d0742c0b13814400114018003032041d420380e111084040a208070f000598144264074040e036404a64188914a00c42c040d68010b0b01c03e5114100400c01c0c998035a6001c585030b4103444802d001c01102d911003151100181c002c41c0b01107501800009200410020f5283c01800202e1080000c1034203542981d8111810000e040080f201040303003c0c0741940c00ea88207038442441107505060259111036552200304c1100d0084820810a80c00901848054081c1003101c803c0380c50304516011110313061002c4131381c807080032001c011312480c0e5811008006614540603548500c0462511400784101444168409441c1d415640c2c091034104110041420641c42510100c642540707618010b074450a440b562440201c0c1400e60700c0301e540c0c0c4008250f1200038000c0e449183c43d04807002c1204241c2400340002c5960f099040b10460041c0c0281501698012000b98200c503400045140c41c3d039216160700c807040390388200c51500540307029110318130350b020380a8140c01004143c032220300343c00301415001c1f003600c660 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 967939505 1250 967938255 967938269
    0xd030b0a050f2202070f03020109171305060c0106030503030708100f0b0f03061f03020d05060a12170f030412020c09150d03050c030c0c090c1e0903031605061e01 71
    0xf104080250080c1c00f45a503100b5800c01500520300f00c0244c8580031518008a42100140d44891801c01801a0f0101c074040e100c0001003442d2038003132554600c16020380d1502c00c09001c0c0f0030108603645400e03400c0d84090010754004050b00d0f070300d2801210041a5800403180c04602c680608804103c2da481d200e58003060b111242012440c004501081c0d0300e1540000300741c6580325103000414035901c00c20007424400c041e42c54801584030110050321505031b0350010805070244603100c0381001405030075064045a1034000c4c07200c940c1a4001d5009a50901c02d0700100348020800000b48020044000414503000300d096080e5200c040d00081007042c20941a16580304503041003c2090244c9080603803280e14030710a0800520388440954194150303040105a4041d036007000c004440d240c10103116a64ac404407500540703140c0a51545034004a020700c0080c07040c3d0f00004243d4241a03101001112007000315501415400c498a1078207980d558000c6600703049000c0c0d00168035460b8482d62503a0743c162010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 967940755 1250 967939505 967939519
    0x70e091317071e08031e09030f2d120c0c0a15021204081317101d0f100c021218270601020705151e0405030d030b0a050f 53
    0x5154004803641d000084203070f030010a83e403407800c115460500e81c0525144204a6240c9a18082e8440e4a024444907001040350001c1c00401102401c080111a1000d02e4068129116103c989082017155600c0f030100c92b010410302c80c80743d040c1e98a84060108061215600455a60b40581c0c1c3e02c01402415542e11866201c0c4000000040760030480110720000903400600b01000c08030031a0b82c511007034130300761071030784d4002100a03a024120715010080d000181c615904103d001d455680c1c2c0c1d0b0741c04541c40380c015640d140b20841c080107005081c00a851304c10207e039110f407401120b0b5034540804980e800e00c0c50340743c461016020703400410b242d4410490401d0540c100b9000503035a506090400305540d501c03804000e00c0d8800d1264000e010018184201c44805140c42c015001910740030081e0009842030050354140da2041c915902182e400b0700b42ca0580d9030406225206410071405540c100c80c0d8940151420030300c4a56040e80030056450041312190700c0f40b60344609011049609104841d0021381c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 967942005 1250 967940755 967940783
    0xb061c05130f03200d0518042904060e04060b010e010e010504170f030705030a02070e0f0a0c0e030d111204030203060718030213050601021b1e0315070e0913 69
    0x1000d03407882e4030039800341040c80a00c4e1004482e1310307003400b61034002480814800305020f000c1c51012440c1c1440c1700d80c01d07141001120180e4841c40000c000c00c0c40e1003404046404921201516940c10000052500c0c40c080a42410540303005000761004910241c0010141d031144807156208e008410106141a120b40349807508103040c0d41c80e41d80e42a840c4107000d108400520030240001c000502400e4000e5024584031491800c0090070880c9030380c02640311001c81401e00c240f9500d00d8054507002003891a00181d08072003064140c40e40402ca00c00c050b80340c05007010b2100c44540000900020304c02c1e00c000d0350300b9074211240d0403105010710301000c1d406510080020745240e000f54041007203014000640c29910340d485e400100c0c1f0b03d2006400210140d200c1e002d01c0381d103580400445400c40240001c1c28400080e50b0702140501d030390311140c000500c1c81e02c104001a07132414041030100c803005403a03042203480c01e0200503006040441d03641d801030300d0301e000141014403050403400c00b4503070000704204041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 967943255 1250 967942005 967942007
    0x6031b010c05011407050a020d02010b0303160f0506181005160c0f1205130b0c0a1104140f1b0313060b0f0d03020106140402070309090f0b061c05130f03 67
    0x14030341c03908440641da03619181201820320400319204401c0d030b030741d1a41d852003148030003820440d40d41074140035a8180031013000c0725980031040d03c8075a013102e104001c0c1742303400c0e06020f00c0b0544c0d0032030007810328003c52040c1320880e82c0084c03110010030400c00c111781202038135001074011224126403002e403c900300f0040c039007024030503c101c1780c020340541e07882c41c5882001d0700c415140810106584001c60701c00505640e0460007800250300402500b034002c1d00303201d015410700d511049c00c008003e054030390b1124003068170f80c2d490b03020b400201b9048141c924940750030300d064001c0ba0380a680107009064001c80300011144844102d904c1102d984070b40c40919604c542d00c0c00046c1c00c071600016403000c4141424450394446211100e1040c7c020f83c0040340340d0f80361401411600511020450149004106860109030410300603001c903090500006640c802c0e188090008140030b130100b5a100c0c07000540c070210685d070341960440184078881c0422071a151990081c0b11011103640c01040c42c5501103d400c082 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 967944505 1250 967943255 967943267
    0x106060c0f1b0806070203070b011505070b07180f0302120d05040b0703020102041d0f070203031e0a09051614010801030c050112110d0c090801060e010e04030e060a050a0806031b01 79
    0x1804105440d4200e840c0c983d00038506103401222100010b83c0085030b800103001491640a0040030120100039581200d401300400700e104550b0007030107100036000462038440c03084000703182010314845002c9403951102d10010301081c052200764415462080541a05000400c50748100c9003d85c4a991a00e450201c0c4000c090f0000c042c10740944d5420700000074029030241c50000002030141e41103005151040000000e0348c806404d00c400c5500c144108100c4806030300f842180700400d203000340c04d0341d9200358081b000f42c550080c0080540c000d154812030f0350080d0354048001c1c0e0700c4910094200c000c0741c00045034041001d01c805807100c241c00e030381000154040c0711500982c0b0310300b100205422400c2999581140d001d600c803510030541e55841302480c15400190300c0c000d0511031000b03000c03075450107000c52464201070042c10300d2505d03110f011808041c080e20b8070254024000c0c2000b034841054181c003a000c3d4000c000d8031001700303000400043ca54039000c00c642c41d01d001c6203c52503c424200b10300460310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 967945755 1250 967944505 967944533
    0x30201110c09270a06061e0803031f1e080f030f0d0b0d020a0f08010f140103030f090e0106050a110118030323100801110315060d1e0e0106060c0f 64
    0x415080c0c03c8600044209020030071045000c0e00011444c039103404504281407103800002c00c20a00106801d00c103115000c030450f50070031241171156802c0480000b2910404119601813212840c0d17041000001c0d455610103501100c8440c800d40315605c040c5c100c09622441143e061200021003001a03840c0008141d001c02134160024140d10060000c9a0100c0c5d031501c2250070029460243c4001001039400900990b5640c4860700400c2c8242c0c001714101c0704034860107000040034040101810548140714290310002003c929003420f2295a4900015150b507200501107000210000a01006c580050060f03010101007074003c0c84410303d07141c0341100101020014101e90640d0364021003444050842c0d01402420802c445680c06071611000f40d0840c5d04080031298601c1c02482040780711180009074008100e8281ca4007039680112404103401428040c040c52441420600342d40c040e5091030f8020f0040400050003004041d848910640310ba00c000b1400600501801403080c0004803035030b00c00700f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 967947005 1250 967945755 967945801
    0xa051903030f020d060e100e061203090d0c08070609080a110f1207050406121205031f0326030c090d0212070303020d090b07030909090318080304030201110c09 70
    0x10b0300031041d08040280d034803000300503204603104c000601030061070f2610b241d00050b03002d03208405140780c482034aa2822000740414410007410000c00040f00080c81141e80740d480090982403c1d51441c0350a40741000280500b9525200e12840490720b180182e2080e4151603090303000b09a100004c0d07030b40d1041504080d61050700030141c80c50303821560b1170b80c00f0031104403403045010b416614201070600c03040b11966480036041000315840d01021940301d101c5070b500420310b843c000d6969a541a00b800c01007150241350754010f25080d0b000001d2100c0001a007451107010b04122901c108264800d60307050009540900100108005500e254a00715075400300151000c1c202048242c214240e090922003141d10680140e044060016a11603021107944003800d50001c9150a0040c2600c00030700080c80d50150000d8103640b41034600900d0301846280041c010759802ca00c2c2200d44a407841c2d616500244412070200380805c0003404074200120f20980100c0c030280503c0026600c070001403c0020410348030342 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 967948255 1250 967947005 967947011
    0x80c0705060418050a091e030c0209010b070605070f05180a030c0e0603100606050a031e0527060105100c1502040b0702010e0303070b0703111b1c020a05190303 70
    0xc03641c4584010380000c051800010741c50001c2c1c2240c140941c0d03801892104040c0c81d040031007000507000706210008100f210b050742d078a0311462805891421104c0006980f0000003000010030a038080000d0601c2c5100752820710007602c4401c1c0c1591052071002e40d00d002320b9002d0204100518060418411025000b080107440c10f54079100d43c05600203540259001c010051304010303c60038100301e4540b0940501c5001c00000f4544480140300d4024010010205601c94074155121182951b0307000062003800e0003000282010300c3c6502c1a00c500074001040038044006031540c1c64000701e17a81d8100c41001e40540881e42d00d0000c02c8449100a1a0444403228000b00317a149011081c8040c2005e02402c0c0c10480d520926070002400c001e001e0441140300b54400c1045d0000180c01e00c143c140c01c01002e040224411105c10b10032205d0f0f02030585405421102800b12035100d04000400c000040c03444400c4950030004280c00300c2e1a0b110b0f40320050596032003840d030166050b0301c2400e0382c071f5446d000349000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 967949505 1250 967948255 967948259
    0x102070b0c04050a29090d05160f23040e03070c03060b010206060907050a2a0b0a15060c031103040f080a03080a05091f02120f041709010c080c07 64
    0x1458094005582004981c003000c40c040c803140c20b0450851000c2c0484001020101c000070b83c54407544410702e1080881d903540031850050031b807208041e518840d5449000d482400d00e03070080c5007013040c40350320807000d002a51003000603800c40104e042c480040d1a1060007907482e40343c03005100107003150322040c4101e80303c200300d0134000c60004004030001d107200f05d9000c00c0c20520348000a14200d00504035912905107035090090190b044401c44941c1125410300c440d03034071211456200d002d030b0110a046503040c03219010b05c01300b0050408591140c0c0a40c5001c10007242c0105800c4111001805076401040081200f43c000c02d018524800c080d020150403645084d444142920030060701c2e921019280c1c1c45a00c4032410582c104c9015070788141c810030200160714110300d41d1a52a90401e00d803050b802d1011210024841d03007501182c0000c41c1e02044035901c0d09103000c031501c8403141110155428901002004002c0b40b80790201c0d07070602c1c130581d180075000c000e684a01b48660b120040e41d20082c8568a00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 967950755 1250 967949505 967949513
    0xf0f030307080c06091c08070e030c040f021b070f031e02030a0c060816080117011409210313060e010221090d031506050703140313020a06170a0e010207 67
    0x1400450f041402415541c1440b04a441c81d182c0c0304110020402c0c80f005001d03805681c081e40700d0b03034402414981014503081500119041c44407070803d85401c60b0a01c2e503080c2030500b81d82c00070007444801d0303480c141e04003064603034860b00c0303036040d0242400b0381811034001c10124420160710708141c40d100c6001d5800c01e04a50000340307052015401290380141540040081c0754025007019800129124800d50000c850b9100903e4401d050242d0b4500c91683c2d8100021440c0940c80041d44582c10110303e0388a043c05801c0a80e200511840d03050710f0b101c1c00449100c026080c5096a014220501c81064038100c2070b59404090103075240c6404040d9400c3c043e0781c1e510b0410001804038104816041116400c101500d54140b1240c8c04400c1c040c1418000d941c05280e04502c0008100c81e00c0749881600e810880c6000c50f203814581d040310418281c040140115100031880b860f00301403080f82c25503203855449005551146508072051551035020340091704a22203504500000301c1043c000610b82000395603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 967952005 1250 967950755 967950757
    0x318070602100513020a060302030a020d060e0609090d08062407230c030c0906040e07150306090501051f05221706040b16020c06040b070606050a050f0f03030708 71
    0x110000040c0e00074804255004002d00c141d54101316216803503064400d1300c1d00414000c461902c40c2c0341c2050390010000304041101d505840c8080021041480302e00e640301c8a001c3c0685080d526680b08990400c0440c02d0f904c400070301c030b0072090600d80f00c1e10b40b59920300d001c01400b1801c104811503415840d80300400010040e90007012014822030152030540304c4428100345900841c2c0da600c2c126848007050500541e00042c14000501c0100c4840c44113541c3e40c00842c0152540407502c0c40e00e81300e0341c50080780c0659004041450502d05950401609959861800c00e541080c071820342c0104104421181c000c0c40300c00030403050b00550400502e07020903401081207480980080d208512001c01c0c06100110084007200d20fa54046c4006025508140d151103050745400340140c0c081c0110402407813185c0340240640c50100c100200502d850b80c1d55000c0c1c50b06070398060b03501280e070035182142c0402d241c40c0c29520075050b190061f00790040c00d80c0c408240850882041103580d0b140c07102340000c1c0001205a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 967953255 1250 967952005 967952009
    0x309091407140406020a080d200c0c0603131e0c06030e070506040e01050d0c051c1103010c020309010c080d06030501060512010b01120b0d0f050c010f020a0c0b031807 73
    0x48041400340350a400040c4200300c4410082c108032003c01c010040380c5e6000458040541c4c21041c015550b2201040400c0140074a03410403403040310401703101610300c40d404040c0075903a190b60242c0d018082c600040201512046851191205e001800f0030080781040b24100a00e5060030350314030b04940d2030344844100f00c0322a0300000c0001d80703658003510310302030034803841000b042c0070358019052908003503101c07481c2c420500030a40a1100034248509201c880c101d140000c00000e4040c841c1001910315a003907d086000c002c0e00e40c0c0c0f10040f01d4100c46c6c1414403488150a90b01c0e4040d44c20642200b004541c4030914413402d03100d84600344541d021704000c80c800d0400943c072075400040c0c1d05180000340081521400780f68906649003c0450b201660490800245155a4540003404200d00800528103100b030601c00f61443c0c420745000b000300040040e42c1da130480404d0b240c202040c4004e0030105c0c1e4030100300134002c0807400d003003030200080c001c0507018641124201812000802f12501894070b008643d1b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 967954505 1250 967953255 967953281
    0x306060c15011419092c330609070c140601170303010f0303030b060c01050a0608070b040501120905010b0d0c231804022b05010e28030909 61
    0x1400400a07801d02c9160001c1c903500540e6403e085080e2841089040c070301d1482178402043c0c0f030f401000c1c1a40442c41c021091089885030350080c14140e803600580d1031004807032203210601e40b024900040c601380c00c0c10315405c004000801c8441c1d950701c003e001a104000c0d2030402031160384034a1100140c0c2640e83d4030101ca6280c80205080d40c0751581c1d030f40d0701c0c200100c00c4202907002040144004030306100e8900c241c88d010304000c52921111404199513100f40c1072807140715440c1c14284080402c603500600d0840303400c141100d43c6251a2064501c151250b071203418040340590b05100604003050300042206070083c40001031301b410f00400300e030305008003100c201c1c0c8400c900d20061114402e44c1886007400c41020002c40350f00001c03d00450100c0f0240c016402001906000003001c65540d00720400e012007415060007a500c0c030342180010202c1300000e04039519400c00e1542040300320b0001d5141c0705501c0781080001400924030301203030072448280041e000c100d481c034401b02c0c400982e80070384c0c8640b50f0f40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 967955755 1250 967954505 967954543
    0x20d1a22060b04090e06100302030a03080903041809021009120303050a021b1507020607050f1b0304060c02011202030f040206210f090114010305060c0a02010b0a0f031203020316050306060c 83
    0x8000e40c181481401001f816078240d22150030301c05a00c2c001052100c203903050034000f2998644022291030b6000c1c9900121049100080340d07440030095400c0421400d201346c0340840000c6514074252401c405900640100c209203891a03c0464445d41046400048400006140080c0c5001080341c416441030b030760003203900c481070020202007140081540300000b4806040c50f4140040010150f00c501c0764403038540540460310300f02e0040400078248100c40000700700c0c0d980325a03425001d4800c00c80098181d010801d800481c404401c00781c0200d030700c0f4400d147d00440c02581ca541c20400650040242e602000000848001d0341e072400643d201c1c01000482040314807403510300002400e44d0208110746503281040c100400000700f00240e610780105100b4541629501124000c0340140020486d00781d000200c0940010034004801c21902585c0c05a4144022000c00040a4080e03100c00c0d140003e2614410440b1054a0720075409150040001440c65151060740d5800382e241c14401150361007500c507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 967957005 1250 967955755 967955771
    0x11070317060306191121040b100b04090903050c151815010b070302120f0913090201120506010c0203120301061e020a1b1205011a010311121513020d1a22060b0409 71
    0x42d0305070701141e2061301b42d00c00027225420031440a000780120310070031549603160344c070200803d4094419980c81c8151181114282001051a0500440140c075480481202e158010980c408049800c404107032640d01a0348040c1d10b010b010b4040c50348111025002c41c0541c402052004010000034015400140300498a0f40008810040c00300003850406941034030b4a01100c0c0181d801c40c11100c550780040303000181f595141d82c0180d980720368150009526000310f17030b11a941c01c0840c1010b14165441666800d5003002c242116405030b14418060001603400041d00c0800501011000c8010301e0f01d514001039510f584102103001402e05003012075959468800702d003014041500c030200d9440091a050100813080c8140050621850000d0041c12002100044036070ba418061002c0d6200040c2420001c00c620b1300400f402074000c41c5003000401d003031112000010350b00942040300d00d60014002446030741c001c840d880100400b6071a21454640310200003e2001c2c211000d0001042038040c0424019 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 967958255 1250 967957005 967957013
    0x30726061005070201020d0c020f060d2313060e10020a02010e0d020105070905040e010e0d111207020612100305160501030b09011a0309011107031706030619112104 72
    0x1200001103000c116003441443c000d41e0303000400100045803810001c044481d01e0002c107030540c040300480c03500f02d00b00040300d01035400507501191521224501e0030b542c41091000140c11448152a0f400300c10044020410128100ea404640402c0c0c00d04221a4010303c40c400060a0740c20005004001d81d40d1240c00e80c01b20603003407204d42c078039261620081100c5e00d00b10710050070410b418001c05000d03654801c031442542e0707000d600200b018101d00c4c0c00c4030b0b40407e071b2000080003104108911102801408600c0064613034507000e8950070f0394002c101034280405202001046807008200c45080750503201c002000c10380902008680392003a01000340081d003800d0002d01500c0c11104954021050000104449100310b840008640540104141c0d00c0c1c0311000b0040c05842c21089040c60080300056a0341010b8008444c0150031045400c551f4041c0d40782d00806884807400c5a070080180700000b04407201000c1a804200b540007074407141400d180c1c800c4581048a481030500c003040307d140e041408144 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 967959505 1250 967958255 967958269
    0x80615040905010b07050f0f10110c07031110030e030913090c0315060522020f0706020f1308011a0118030602030115090b07110d1505041115090a050603072606 70
    0x1f000d500000d003d846050342d8090b80d1554401503080e500341c0e89407188030820700d080f1704a03103569011408865142d612030074030241000c400700109201c0c00d04480002c43d01030203400740c24940e0209001030350900030640300780414414107041e2521003603950058000002d2166802801035400b42c000e149800d0020b8901c40111009600810f1040c0d04855012807034940304540d84e18055121800581c58001348200d40c0500d0203000002031520380081048207840c0d00c8000540040c20404410541c83c82c3d46041c0c80c0d00303d030345101c88485101040801d20b2825400f518903240800009840c04c0702c03407070f541d494540490b0020380103016010f480941d0011f503141e001c240130000e459507801c00761a014641d95005499040418024011303551442c100062204400000400d01412801441946801e19050700110344690500303204103000d010404500d00d5207000c0c0c0700c0301c5101501c500c07003050500b81080040c0e040140320707800700107007150700241880300e5001860b43d1140c190a002d60f60b083c284200058 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 967960755 1250 967959505 967959523
    0x9080613110d111c390b0715050601050702040b0609060c030405040e030309060a0c02210c12091008090c04060e09100903090918062c060403080615040905010b0705 72
    0x180444c03042e5540b0104080d050150f00b9070070543e0380440280030b0303103c3d115254140c641c420038903481c22850014031205450001e1800303d103c2d500540680100a4500c1c0032941c1c241c440c58002002070000c50010704040d48540c601d688014121810702c4c54801c0091301c55404003449082e01d2f01f001c6010803041c1864044c0c034000030130100186045151884500b561000010410741c9102c0d21038030200d148034028059051018001a0340302d4000f200c5080f10700003a03009c80b44a507018402ca6051000d85d041002c113959078010014616090f401007035404030b03561100901101c00d1401261941d510913903a6102e00710042901e81c070a01500e2400003500ea0511041c0b03040c50b8505130a1801c40c00000354001c500c001952000c0400151602c4214240d0018149c8018010041403070001c902e8911202402d200004901003402e411001030700d289050f8840c042600c00502040a60b008203800e46031480b07000a9030f404c0b03544264140ada41e1a00601502e40aa01900f0608800901002409010310607024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 967962005 1250 967960755 967960789
    0x40b0a120c09031a09030f0a0903020d210201052203020c13090312020f041214010e030c1e060112020126060f040504023006010b0a0306050109080613110d11 69
    0x509182980b00503407680707d051201800d51400142150f400c500071046480655000341440029540e14a080040016000c064503291030100000d48009881402902d2280090150801120314400c11640201c44013240441c294018101a002c40ba1a0305040620401d071300d02c00403400c0e40c15400c1c050400030b201c90b81c2c101c0481c010019007404034503c10846003180c02d1801c0240100314907040424800c1d01c482c00040e41075080100170100380c400000584402c1c0a502c003500ca00d80e0120441907184040b0045120058000300c00411401c0b4107007900c0031090340103044c218941029040001c01c002461060300741940447c500703204a030308110799010101d000a681c2040302d03040a800203940c8807031004041924100b07140800c5103180c4030b0320403c034401c1e000382c1c212459075842d1110a14131b904102c1c4480e0000c0c1c645803000a481d8861001842150344d41030191806441d142601c03610b00c02c45020690700c0354004d0303032012280d88810b40b1240b0028000c8018680460000040054091079910000303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 967963255 1250 967962005 967962053
    0xf05120a06140114030408070c0b030f040b060d020d15150603020a080709120b060609120c0f040c05180d02130b15090a140301060305060112030314010b040b0a120c0903 74
    0x8500e4516801201c6c1c2013904000103580300e45681c0f0700300003005440d8220f00b0007210048180001000e001c09568011440303a003402d520b80c0e480e02c050000e81d41c01c10b1b01c0070f50b2101064021a0110f8940850fa04c2804403100d0040350f1201c40340d484c181c10f00500d81c0002c0000c0c0d40040c1c0503007941e80c05821942c10403607516116406518008185100586115001e04aa01c4035000300c0e24540c1e0380d1044405076000030b055142401c90b29500f81d92940846103d0502502e510340d1250a1827401e48079076510700c103850f1070b01400c00c2c0528406249e844d03d100802e940007210000b00d107000d65544107500c9800780c407042001c01c0c40b0302540c3c00e10415101c2c80c103024074104000d200d203040556600d80818152084090900304400310000001d014207450343c006440c1340682c0e4008220380448925441d24a800b90300d050140d40101e08903c6686403092044c0080d610302808280060785211008200031800c0e032074416042001240c04000300c401c0942c5900200741015010003c00c00003101d03003c0c815616a90751 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 967964505 1250 967963255 967963277
    0x10503060c0d051302090a0b18060102150c070f060b01020f012d020405040606030c18050109050f0102011b0e03150c0417030c011803030506030604120f05120a061401 73
    0xa1071050060742004190607464100040c403000f0b01c541c1c0b8242554005000718038a09022400d44010300707404d007089009607255a4441000e0003640341c0140075a00c10380c02070001c81c1b120415075440300b8024243d4400540200f010a01080104601c1c0c090140501c900203410351800c030001e803412a181641002990400880000d0142e901283c40c01001c001c0080d0074034070040041c480003d101d03c0e00202d6002d407400201003881685544050644001a12086001d04502071100c3e00c0d24041d10441380001e54428013480700c0d08140c0c20380041c0c4d200600001c50b150900c00c185100035040c00014500291740c03612900524034040248166000f000d9440111504020700307050b2091040c2d00490590000041405c02c0b550b1041003210000401c0000811052110001504111a00c10b4040d00000d0504000c15000d260205880e802541d1100c01c1d01c008807001c440c1074440840101d100002c0c00018898003000281c4511030720b04c83c084900e4002034107410401010307400c2c0c901c080b0b49410007400d0707012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 967965755 1250 967964505 967964521
    0xb07050303062b08030601140c062d0105040903050c01020711031009030206060405040227060a051210090302030c011508010c03021c11040902160203010609380607050d0801050306 79
    0x40030060981007000e19a50766240001a61623140f00882c04c2140078001070039404170007011820314000c603444000e4004030000e09a04409507070603469404021700b28000108190f00d01540082c0f22180700e41001804c20840d860345608980104c1c1d4280c0e104548400b0101082c41d0512501c0501442450100003c0100707841c020340d2204001e0a01c0d0055681d030010406556401c0b084410400300040340385160f0b224a80c180c0380070a01902d03500d00507200c0da1804642c62610342480c880d0b02540b1001030400281041c411030252071644001d5080d03002c1000a040c000c02c00b070140c4803130206007541031032a10b0b1801d00703008c0c2110040d400c0030007010b1052011103130351010311543c40500791000c20080ba441038000c000b0312076845180e02000405d44001030300c44000410035500d940182c000c800030069180c0c0c07200da0b84213035003100203100020140c02c401c10394144088040100c03c901c0c1000c410440108100c007061599201d11000d46159008101e018440c55111f10101c2c054001600a0b0cc194100a01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 967967005 1250 967965755 967965829
    0xb0a030f0513201011011a060f070f08031e090d0f080a061d01050f0901050f12030408010f140a06080c10030e071509120b04080c070b0705030306 64
    0x2000303100140741030b80c2d4501c64000c00d030b4070340c600040244201160041c00f51302402c4660116642c98081d403c3c03000384810380c17000c0a00d04c3c280030405404d1034500182030001300c03200c0c0c1c80354800700c5140c114444079101154a02c4041c5124007880f030100f4080e00c0e085500c03c032541500400501c2c1d294801850416815440f03610150600c140d4108400c168a451a101014100c96005000083c1090205290124006400038100d80c82038a0f0314401c2003103c0c003800b404106c240103442d00312160600c100340c00e0030030b0032585100203504001d80b400e140c1c5850003a400d4940180001540b03903104e10440713914140f043c0c80950030410b05001085450303c0c0100c10303034543e52103500d4280f04000308444c0380c081074000c1e080712540c030510005803038107642c0360451200844010209240000e50856012462000e080c94080c0c200303411241528281c0d07116681c07079213268481c1c484c6019a0161040000e00d000800020307082a030300c558003079612858036400f4040100450f2a1020000810031030071040018040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 967968255 1250 967967005 967967041
    0xf070f120b04051203091e0d020d1107032108060d0f0b0a061d0412020c0a1403070b0301030c05100e100e0102160303030213080c10030c0207050a0b0a030f05 69
    0xe503248500e941d807400c009051060705602c81007005000010084920404160010400d01180da07211103901fa04003269603c7c2149940003015070701103403402604034000c0d580505010900c04c11076200c00c2e202d0303a030203010103411010f02c0b41881900603000c540d5500650042d5000e00152800d589000c100d481e4051000c040345c01c0070780902070312404180ea0340496080f0101038140f102800b242c0654036202d80f521080100c074103540311003140c0e200c1440544042841015080000c1002c40004d0610411030b40400c1c007100366951503c10b43c1000280d8003111400b6500850046035044165032418042c8032908090403054420800480d6840a25945920b03c2d172003102414608044114400700040c1d2401d074080c1c180c09403041000600104241c0d042c2c00811150650750140007a1645d148101a6210322950680358010354107035101e4941803188e80a44403940c0e10344101c5040780d41d507001103640c4450036042008092400580c2686103501800340c9005003600040c00c116600e041c0082c1e004440c2d8503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 967969505 1250 967968255 967968263
    0x70b0408031e010b0d050f100e0a0213181a1011070302060f071b080d080c121009140c0409020f040801110c0d08040b280903020f070f12 60
    0x100114086082c980c0c4036650102c9141c0d103110040d41c488110100e95044100941000ca007480001500318285485060241d0044c901009040b81404891620070000030700c446146030f0309120452000e14011a41c200820885143d43c107090184865441507440220301c84404a64504008580351541038194080c20070618104d40c6070f60019071164146020343e84081d43c460000700748506a101490001c00d902441102c041c80c814840c03000c040c0050945201e5003240b60015032003608241d008015030b0ba440071700400c0303040c41c08040700e0940d0001d0005440f203075542000c1810503c03480b0b00500ca1180403040c0b40002c6000d600d04600c103202c035031045000380b400941d00030070105c040c80e0704201500c0140c81108000e002600d10048141a19001400e0005052144c03000d29203640303018445060103a0341106085480d41c1e980d480b02c0401c0b1032a5251401e00c84400e500301804c40c004c6105103035000d03101e503003d04a0004008400c62400c4041e800408001120010070000d4000d40c040c819502540 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 967970755 1250 967969505 967969507
    0x512060c030c0906310e0c03060609060c060405100c030b0d1506050d060e210307050310170d02211b03040b1c060e0f0a2018090705070b0408 62
    0x1640020030b0b010b0041a0001591803943e01818800e40d14a0130f081540c0d2000460400565541d40480f0b131045500742c4012641c803400f02301240650070100010404004080c00c0e4900c2d2051480006180c40f2040368140e50b140c0003040500c0340400a8015000702000900d000c1c081010380100041208550690041100f1201980d00380041002d4011310b0003003d004040c9405115282412406000e034007000f1101c60181d00e82000e5a0b000d030a1a09442c2e01c4900701250441c0c0d00d5030810748203684058000ca1011501840000b403c880041002c244032100c00064400d140f100307030001c8d00e4102c80e0103000400e62000100c00c00da40080e002911820828007c480c01681e01c5020310301d045100c0c82e08081c21a080004400d49179111751005034220a400580c1009050f555500e0255540f10a4404010754883c00380400c0f0701103402e40003048501624401c20a16091140c1034003019071003924a5200003160000001307103442c00d035409039445a42820268501101aa030f43c08440000a000800c0000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 967972005 1250 967970755 967970767
    0x10150c02040f0e0a2d06020702060d020d02090310051306051b0a09080f2a040b19050a05151b0c03030a03060e0601091511010b060d05010512060c030c 66
    0x6107903000098050000034081101004034607441d611614022801e84810301502d0380078905190304984001c540b04121201060700100b60307241c101039480808103070b90200040c03080f221158070078401080b154441d01001640d86002c2018141031400c961014007441c2e140ca02004542d4010451100f60207174030980008041c2d85812072414030002d010f600a11510000c80c1c190159504204000240c9410360120b801a003411103880c1e03079a10711031020113021124480f144448090034003680c00c115100400116820800c00c022948a10980303c559000780d070303460400c0003141400f120038400340c002920790f000f00b0b00600ea03003280ae03441a4183c0f111100440004400c80b0102402109448080281680d41da289190001005088280542e2441e80041d00c0411600d60040482ca01220800f01d00409043d100640c2923549440300030003040c01e03548902909243e641c0d020010032000d0721850340000e940d4104070500180070503071480d41c10f46902800600030b5031448601941d80c0104083c04c481d40d548 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 967973255 1250 967972005 967972009
    0x120302030d0e07050108011509060507140a031e03020c1903090b03130c080303090c061c06080a14030c060a09110d061b0e2803140106060810150c02 65
    0x4480e50001a840070b140c94024121410040360220468400f641c400455076241d454031080c0084940303611010800c0040104100d034062000b40070414000c012059807170042e000224100b00701c0030f03412000034611080d4003004205540040d041400c440c41e0442c102461551543c1e505c100d040d0500b2505414922004109071240442c2000b410703208100907283e00b0440799840d0405080c1c070742221350780c210500100707140c1400406d480c442e488a01c020441c240d00c0d1002d200c036503841018298008a1215180b00d0a200a4020740b0000c0c04e9200c02410059040e080c1203800b80800b0360441d0f1103030810807030092031070300c006001d07500000c0e003840c00141c2040c589003218007280548032090f0405189640d00c810b010003035000940c0070388000d103a00b80d103500c2000101c4140180c80a0954050070441c500c9a090714142160b5182c131046111070510b0030340f030791154071001c0140008440c041e9107510003132003044d500070300345a00b20314140b990a140300c0c100702c00603c2240e00c1c1b00508003000741ca5081b0f00195 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 967974505 1250 967973255 967973257
    0xc060904020f04090509060a1b0315080304060207050909030307050415020721051606050d0e031b03180a0510030b18090f1606020606101112030105130c020712030203 73
    0x164441120a503507240e68100d130b6000741104035851070f098040e460004107460a213000b815030036062003140043e82210300384117500801e42c0c0c0600e4114090f8034140407900702010802403014202c0d0f42c000303010307461902c1d08004040301c1c01412003400b90000d02c280554950000241d074180c0701c19070048100c1200c8858106e00c1c06400c2c1c2d000c94429a611401c4242c001258010b060303c85000340266008008200f52600221900e0b11030000001c5d8200701100c800403031076108407e0f110302907007039a151030061280e0400d0881c288094041c00c0e08000b81020520524403c410039040041d0380000c00c452400d400a00040c115940c7e64060607100c110602240c0d6a5103a40c0074080c442e0040c1465600705030f1b100c00c2c1d46002e065041c20040c4176a404040454410805000489509900401740c99441c0001d00240e10300c06448002032000c900001e110303444080c403091001450300030060703860790314000c20882c070000242c0000741006e180c010051803941d404170b40101901c045180408000c4880d150883c99 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 967975755 1250 967974505 967974517
    0x13060e180f01060e0f0a090b060d020a1a041707140d060902090406020d0606080f070f020f06190501050d11011b21080609090a030c0c09020316020118050c06090402 72
    0x110751070f2600c0460034241c0c4900c018000d400c80881c019181c2da81d10300c03000480320203401c0a030400307103450b000600516011880c80942c40c03001d000c00500a03903604412403000080502e9010012011809100d8140706680d05c100c028401401800c8052038880c0e8410380c4508030340840e001d1130140c8540000d1142540068403596805070801145190500f8a00001e400207500a040c481c20b1030f500248203171141015034002d15410665400503182c02900b6980500c007988242c06601884011232003c06052068a00c601d14014640d625800b56086400480704143c02c01845a0140380d1000302041090b8072880200c1ca00f03013840301c0c09a48035142c44100c1128640000c101032081a1484040c5845003071113000007a8076122510543c0307035a410003400e40412110074240703902602d000350200c0d114500bc01e102c01c2c0102e0089483d02d4445000304223a900444213101c0c1001e4030301040301c0d259424855039045c0d1099508111102410f550740ca5202e2508544845c440c52001c2020701150b902d030350450b14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 967977005 1250 967975755 967975783
    0x405030d0309110609150306011709010c18061d04150603020702040c140f03070e04060608060a09200f09060c15090307020907050a09051c0213060e18 66
    0x420405004024250005003122141c0f918070341030141c0d00b00f00050f41c80c000e000605619555200030010303200c03604002c00d01410401e603500092102c4c89400051800ba8185c6800421104050b4402500d440b05407085071350013110035a000c126681c0c1c803020011091007601e0004d00002d01d04d400141c090107186008842d0402c2210f0001503c58042e0300400d0014800c1d20144800303041c20314140e5040139401c1502003812001c2022814000001c0002e5a004a090404606171050040803404464903900082c0c0072a80e004148412858070400c2040140f2110034107021100c51804140326800b86d001868810300008103019010f2800341017558002c06001d08555140c01c50074031802d640c1c21030f07002c1c1c922850301c0b09404a00401800300864503942d03006054403806455140b8212081da0100c0c88a80c01c00c00b007414045110b9072002401a10214500c00c0c0f08510b04180c0100818480341400041d00c19240c24001c05c0200307c0134886651101501070500039030a00210002d017050040c01d0f00c80c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 967978255 1250 967977005 967977013
    0x10e0d111503070f0e1c0b0a140c2d040603150909080301150314061c14010c030b01030612020f13060806010306060b1812030d09060b1008010f0b030408040503 70
    0x10030f1669002d0386030719541401e680c411520a12880c1401002c02c07400f410205c199080700c0c5568040365a00442c150004405140051100d0101e002075844000603a40c54559000008104254103044204603c40d10031200000d2464224120072500c0e91145100e09070526403140a00e00b4001243c01d401030041c4202001800309120382c3c6484003043c1d100f405000d52003200b80309003804c0c1e18881e104201841f841100d2411503600c3e20420401c0c0d406a03c2070310034484040c4400070001071880315101c415002c40c0400031400104000c006000c1d03604450034079040602c0c000c81004101f4814003034512450301035511007100a074180200b410403a024024034212400c00f040040c90310000100d141c100ea02404080080c2502e4109602c0c161180781e00d08800170f21582c52aa2141c6841c1038145404640ba40460785401a64094001034410300072054504d280d850381d00100d030342850750b681c00c0710041e245090741103581004684000300150740610307140c200f0044002801c001e408411240904030080482e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 967979505 1250 967978255 967978261
    0xb090f0f030c0909031b030c061b0f0a0f1b0519081204030905010906080c0a0e03010f0c020a0606050906010c0b090703020d0f02012309060d0612031d010e0d111503 72
    0x5140c1e46da03c04000b2401c02c520540ca0001600701c0802074079215240035024144503191f494881209100c0c1031350311891200100b100341c04030b140e03040080c01590703800c6d202c1a45440707c002024001003403d29010849a059040060009501140818414640204411200f003403818211064022030b4542496441c00340300b80300916800049103011160266a40c03010b040e11050101d1310702d40f040c0c03040082040f041c806c2e09106800b50240d4120b1240180000035402076911400c0e0a0f26065007204002d40c120142403000d11115000b80e4025150a03a07101c075060900c03038002006140034240150504540c0fa020400300c00c0140a06001190014165411400f403400d000ca0f52050215003280414244100303400030100712100300c0c1c10421050500c5082103210003c0c000c01b80e102c40050b42c00707236640350030200e40c8404180c07000100d1030080d510f10308002ca00900302d401f406150281e65051140d0940e94100e81e5481c4170f103010344564800f400d03c1c414950000441e031443c110f1140c1c401059008010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 967980755 1250 967979505 967979521
    0x2090d14072d1508060d0311030f0408071d0112030302121005040e0105090c1309060f0c0f030e030d021803060c1c0b0603010b0f0409060303090303090b090f0f030c09 73
    0x50b02114820880404030407681c4a10800302008600b0109001c281c030400028102d1500d1340101d00e245010342851000c01c080c1a4180782180e00820704001991004101404001c0c410018140540304060010305105141456481103241c14450114580b5441e2000030405101e90141d804540401e003c0252380e06007108140d83c2440b107802034034000c615003078018290210500585005040001c0a842c00c00c40b203400780105840c19900c11106280c41e1954030b00003070342c2c601c1002c801604e030610000e05e00d050303414010711070780821441c5801c050406088040e0740c503010040700e002404040005035502282d0000240c4400d0300d03058594180504400c020b540405c00004002150404003c16a04148944071400f10b0314041e8049403c42014001802000c9200000b0020880d921740c2c42400c107917441c181c12066400e19001200001d01d03220003001016004408030003d4503003107070303c1c5081c4260100429490482c00764090b2150000f610310f95507680301807000c95070824028001d010a40b4080c50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 967982005 1250 967980755 967980809
    0x2030708040e0c07170d181113021303060504050c09090c0d060b040f0b01180e01031506032a060f080412050910030e06060d030c0b040204110d050709080102090d1407 73
    0x1344403280b2820280e00001171502c104019840715400032040c8c4545500000f44100c182c0282e000d090140d40c00c00015004100d800050350013181714210101700703440d00b490054200110b042d05c05010756001014000c4910003ca05040704140984004583d020745d8107081024081400d01160050310b8540c0b04c500c04d144942065998070801c1c3ca940e4205069941d0401c100100c0344600117903000900014000035481c00c02c3caa2809118501c082400b5480b0748650b0310303041700b03c070685444c5044050000c042e103111504c0800140490709122820b62850240904501d0005000034103000350b0302e5013101c1b443d02602c1551201800a0966603a250603030701d01800400044019841038414040001c00500d0025000c80c02c203940740e600c07140482d04039501c46a1320240a0310499000b600c4000d805442008107007e0f03b0a616200404200b60400c01c0b401307000d0412a400c44101d607401040460f1984d12003210300d10031564091700c41489207481603281e9040540e99000300101a40b01d6542c002c40c1c0101e00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 967983255 1250 967982005 967982017
    0x203311805010803040803090105030c090a0b030103060c09050f060c15010b130806130b1009050a0f0c02010603050303070f030b030304170f0141090706030c02030708040e0c0717 78
    0x50000c00c950b90300c5165440da24080c51003098200c4e8402c02420000d94410300255402c4207601e203800d4141504100021b0b911101d0350010503544e50080010018000503016152440d0070707500f0848505410000410340482103040542c0c09590f0001d801885414100301c0c2c0c010300c21170707860064000c1d61170f030481e48070343d620410448400580c42880805c081c200842e699000301892201259100c066a8803550160300061114904502503c00025005400e0050a01c5642070030b4001030f0a50201c00340710101c0c3c0c5101c05500c00c5a141010074400100c0000031a504201103041a40b20404841c80480182200980141d0980400301e4002081c200c910401c84842c550001500c49c0e0300f003140d04507422075001c8036a400015811190f240c0c89443c0c070b01c0c000d1448451541440649101415984c18840019a00001d803030b48464820066160f00d4815a02ca00050388041c5182000a44442c0014055409802540303104117000c038400305840e030200c0c2c0740c540c5c0c058480524200e0306105600250054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 967984505 1250 967983255 967983299
    0x23a0309080705031501060e0a08120301031e030e010e03010b120303090105070f020d200a030806040f0c14090a1827030c0b1b07050c15030403020331 66
    0x36100440c26103400310780745c450001007804010060703103007003012243c401c55043d1841d00000d10001c0440d100000784061041194541d083e503a9079403540c5403d10044c40c2c00c0f9400c0e585d00302884110400264011480380c40c424092a0000d0340c4c1c680e400c0003a0040600741c0f03aa95012440d85540f0300050000301c080c502c1112118020032066848480940b90105440381c13000060b0030900810300824050079000105541150150084000c00b00c01c2d540b8102104400350003244503082003001c2e074078103405410201242c82405000c0304480032009000c10480789040c81c0d071154045040c8006407580d450040c02842480c40b0034044000c4020204000d02c01036581040010007111442000703136000c16850001581590356202d51003581c3c480c00742c42c0f0b80150401050749002c101b4007a01c0c0700ea00c0040c0803c140544058011a200c075000c210503103944c21160082440c0600400c80440d8000c4140c40b9072aa4045040181c81c80e07400e070000341d0000c50544204800d103a0000410f001d0003060840c42080c02c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 967985611 1106 967984505 967984513
    0x3090a0b2808040507150c03140d1103040c0e33150c0106050f0f0904060209060703050703031805070603020a0c02100309051603023a030908 62
    0x5061007a400041d8900d061009022080c032008005142080e0b1031a0300905645000c0e009188121010b010702410207124898004000125078203020361040c2008034468100c8004520f820070340d0141c3c1c114403d4100400e56038802d0341614041c540d180710700d0020030b41c0d08030850810348940241d480002003408060480762180a036481c2081090780c46151501c01480199003101d0031a4001341c81001c8100d0040360719103031a140340c2441c07541603e0159460b6030301c0c10541e02a10401c4280c0741c00010015a10040c075904c0400703001c00e54803d540a02c114400914035880507143d600f0003518680048204000b014041d80c001e10346d20540c1c0c200403544140c903400284d0489031b880d03446004281c480e9481010420184a400124007201c9a0000b4440c02c60300807424100c0540ca040c9041000c10814102e0040070381000c004000d540701310b00e002410395140007000452544a00b00c041d1003 = true := by decide +kernel

theorem cover : BRFrame.Cov 967805755 967985611 := by
  have h0 := BRFrame.cov_init 967805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 967805755 ≤ n) (h2 : n < 967985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
