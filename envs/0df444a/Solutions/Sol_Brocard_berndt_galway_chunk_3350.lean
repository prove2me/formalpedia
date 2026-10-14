-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3350
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:24:35.340672+00:00
-- url     : https://prove2.me/submissions/e77502cd-ca1f-4f24-8c8c-1868ac417370

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 602338129 ≤ n < 602517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 602339379 1250 602338129 602338147
    0x406170109050c0d0f1b0f1b050c0613031b141017100905040503040806101a0d110a1101050604020f091002191b21020130051b 56
    0x551041c82550044c080d0380340705100b00c29646820a00ba8203400445654000c54400750140003442034080010004e0324003131001c8905a800140e80c3d5a590700880204420710100060140f0780e400045000c81c581044a000000900622040e00417039225148180501c1e1070607411040700e8103010007a0307102c0e20498460f814400d520a02880510514011402040d1210b05034400c2e6069180c10501d5418100401c12003031000c0000108101d401144c21a041d43e0b49007181c1c0d402d095010700070f080b50122008a0619403944040140031010000c0300b0000340032040d04141d000c01c0d4003101e42c03d00460035040051103018030030310650b5031201b8180c13000d41c0351200d43c46003443e03180310b41c0341220f00c02d0a1504024817401e1082048070311356500b50761003515903401402d150110480013070405424040e1150081000d58405c0214480c03160141084800b40e20103034019210002203c006104032100c8125100307244006814840140c0100301c000075043c200110031200300c0c0450352088045404c10401f500d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 602340629 1250 602339379 602339401
    0x30602121006052d0403060e0f01020c06070c05010212130204060f1d150307030503180301090206040909301701121509020d0803011532040b040617010905 68
    0x18400400052420240100e408005284c1403c0441507900c1c0d00301280110820005a21008581919000300c404083e03001a6482c01e07413081912481064214002042c6040e0050105418441c440c01c00507042c2505600691048002107030080c6201521503001001d509040c407c02000d040c41c006240c028030b0604130740402c0a1040d25008244c92f0441000905c0711054000058113040000d003a02c0d0100d40d2801c0480c0e980c1c0040a655481d00007070358511320307070386414400e0800d083e50203400b26083c640740800341002040c40d00001c2d14034401441700c200c000d140304080740c8061400307901030401c0050842d40c02001c40364081c402c0001100001c0040c482d08200124183d02c0e654004010010180344e00c0d40500075183c50b5000075003224041d02c040042007032490196040e694170350420009955510011503115242440140007030140790300e00c4228182c484000e04c682c541c0c07582001e24260b0b8032083c6040551081c0c9c08a000241d4000c61020030b88891032070a0b00400046409014038284001100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 602341879 1250 602340629 602340637
    0x10c080301050f1f0818030307080c0304020f040c020d14041a0a0519031a0d021020060108030408120414060901031e0507030c0c030c02091f03060212100605 69
    0x1910480060544200c01d54070104d0302d80c061000c44607000100d142c01080a03003411400d07180d440c801c0100484510980c3e60010580344140b802d43d8a0000a45030a9080c0b0328950000d0010780c0c00408102088100b0303140d6018600c80702d680795004041304d1070761140060280003030706940c3c1e04400c03080204200070585480d040c3c0344e825248032460754034059110192902c1c03007a900b4945001c184410303191080b0b41c16500c0a0388410451800300c4069100c3c0b420081131101906009610a001004080c0520311588031071a90404000c42440d81e5211001c0799441c04400743c5c046d0101e07031b10005091043e00b200744482c82004002c071402c2801c26051041105a070404840000d00070a40824a81c1d080da12907027000180e101521414040d005116200f88003800007150408003090500301c410380498440d200c0681810340541d00c80c030081c1d80d99030800049910240c4107102c03a0550030310000c01d203c2d41010035801107118920045e44c1c2d280e400e00a80c0f90070030040c10784500360905c120400445401c07200315 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 602343129 1250 602341879 602341889
    0x4031b021503070201091401021c0c020303180f1902040b01020c060a0302030705090406091b02162303030c100b060909010b2b02130504050c090d060e100911010c080301 74
    0x1c00d48941d26481c04900401d8202c07009000d0301c40e201409400e100781036000307140030342c0d060107011310060602c01ca10341580c1c216042200103070b02c208001105d84107040040f6140c8003084007078030612010859280c1ca80081101584600017008980074118070305803098840307180082c005420300403480000600320380660102c40301456000400902c60300c1c032940403280264401030003001304940f2045103400800f80c1030b400610882034040300c0c0403001c3c0001011202401c03000d5030709444605049442d829030300d40320800071040b039010410000c166001c0c0050185140040010003100d01c00102c400280c450740c4149501894003005030306c5907074440e034001364156484000030581c0e490318800b44c251406288035400300000c00e28100422a070081e50000c001440003081d815901680b600c2c2084101ea1050b00d11107210072041106001d139080c80c4101e00840c034010790300001d040400521040c2040f01c8007110030005a80d85416400b0800c60b00300b9041c0c507150a2800440c22185a510180d2600c010300070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 602344379 1250 602343129 602343169
    0x20c072c16030906090f0210030b0a05190306110910170a0e0a05120c070902040b1603050f0c0319050c1e0c1f0201050601020313150e030102030f04031b02 68
    0x501c210060090f040058940c1c2e00140402a916841c1060b40d481e085000c402c0344560954403c80800302c1c820f000f41e0340c0d9100c00030030400d0700a19080400c074200704030351001201c542010f500000403980e20711035880900c406401090307460038450308001d00311030401c2c010010b1103101d40e0020601c0060100321741d480700c0100000101d40c1401e0031031520708240700034020454400c4141008080b07880c50040c06254103482d007294600d5448a404e00207902407400340c01440e0005020303075032000701e81c0d41c5400083c07070003800c1507403a10385400302200e041d034040c0380c269001d07600c0015101c6e542d0b2044166070114600c00d2801d00d040ac04210b40d829120b0b42580b86031544c1c1c69060988018400040c405070650110003400700380d84000500300142003048468600e0055460b10380003075030301d5002104803490000e07880c00b810052400c00c9003100c400705c05000244200101000c4030f0110f510b09100542c000c5c0c0d080d003010078071380c82c103803500030040304c1d802800042e03003403a01c005080107803500700c610138040c0c0001c1c41c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 602345629 1250 602344379 602344411
    0xa08010b0d09022e03060e060d030e0307090e0c0d0f0611160c032105030c0f0409020c010b091f090506060c0105010314120703090b0304030c06020c072c 67
    0x24280e030142101d40b00295008400d81000c407001c0e0500003500058007820001140e552044103029000c90f0402e202c0c0588000c40703030b80001e42501d4009004d1103030707900c2814884951000000480e02d454130a03044454001c0e0348421030508400100064048000e0495040c071104825586841d004080810014001c0d91181c41029181c04054103030b5149085003000220100c00da0704240c0390200c20303403105881c24004a0f002185684070610080c501c01150340310186035850b00c1d4492600c9600140c03004041c0f03442480003207400d5a1600040c0211a650700012a03044800010000c9504001d000000501c1884140341c604082101b1000225111104006078558407503021a1052080c0384040c54154039050020040040daa0b90116460000004039642d0420010440110344110f0401a0100e210701c54100700101c4004000d540c424400d00c1d044034108070701e550351400e90b00100b0801943ea003020350141720076458021000400804420365140000741007601031030114018140b82d07a40e200c804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 602346879 1250 602345629 602345647
    0x80912041e05040c0306140405060607080a0c081606140610180b0c010c08090c090f04020d0606141203090f01030203220303050417030702151807080717030a08010b 72
    0x148050700203000c0600300380700354850354030b00600604603409502e6540e001f10402c82101d081a10a8901c200409041c10780b038030390a0384030b0360b10541004040c88100003911001e0000540c80f44040d101103500c40d05002d03000748203460400c094446030108400c001880b1410031419946240000540e003030720341040341d41066540b24424103000c0302c1d0400002d0001c00242140300c004150f000d400a0001655055220b844a4804989410ba0a0f600c0341d48000c0d0b0070301040041d254444803a410038401400c8c06100481541c1d0700382074a440ea4404400e0f60750781103901030541072080761400280130b030001441c50421400e0006920380031070503079181010381c0440040c0c115095001d101542441603000300e11000d88904c0c004014140441b8102c0e03203140c281d01060021510300080e01d000e08180d03005000303103c410342514030f60050010281190800e00400e09100140140044030103000f003000981300d0170b4100030321040d01001c0c031108200c0c03a60082210702103c1d94401025810341e0b505078002c41da13402d002c1e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 602348129 1250 602346879 602346929
    0x1c020108010e2211030d0c0c03083a060f0806150f030f07031a040b310f050708030304080a081e09060403030e0106080c1909061508091204 61
    0x30454a80c4030300710030280ba06000a144007500d044c4012400c6824009081c00219240096400e00030700e0005801c0d010300003d055100503002c100d03c0c600740c444c06180c8082c00c28140c0f90740034101c105d99070300c01400303070000307000754051000a4040344801c05545881d1141c0c0c0c5955110040000040701454180c2c000280c0e01e10340b281c40d20201c02012076001c0f13130290902988803401440f04507a00240802d5004809100007281c500c41c64119244402e03541e20f41c0381ca50702c10003611524500d005c00f210414000f44400407a01c40785140500341c0341c031000c205403400d5464a0342d9504a03d4955109108100000380510121102d00c41d2a00e026030140d119a05100504105ca50800d441d4900020401c469080d0004001d88918000da809105a08581083e942281c80c50b000e0501d05401c501c4441403030782401820150306040c0c02c0d10b00080d46a0f2200400c08845c3d00d9004024030707190090024000a910481c015004144600680000c030741141e0203a500f4400c46c410400503096a855621010800c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 602349379 1250 602348129 602348161
    0xf1905041a160801080c01090b09030a150b03070b16030c05070f0e0a0f15091112010303020708100612020108130507080c100c0b070813050a050c1c020108010e 70
    0x10101440c0218188400700c0c0700d1994000e4220000200034000000301d0500001c6d03c2c00300000182c40d8004250704241d000801076010140e01500340c0705002c0e0000c0021408040d402ca25007a140300094000600c1c82010306158456004407100c82c801d008035244c40c41424a040c10742585801c1550328243c0500c2d0503401c04845622205030070200100019619840440f45449600e02a02c00c11010000034101c10031902c50040c9014601100c10040c003441e1041c0c0e108105012401c4401c904102c0703280e0145190740c0c800d0300b086006130410042006140030800c500401880101000e1001d20700704508034411500d0044040d0400ca07130395020800c289103143d68102035035045400e071048a52254416a9038124880815001d5040000c1101102d441040305d032108640c00b180c0c40307030140c4404204840b0304070064912140d902846c2c000200042c03003003290519452090000d403030901442d008014125100006503150241c0c1d00080400503a40184000c0c1560081c00c0c1e02010f58484204180b00514 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 602350629 1250 602349379 602349413
    0x602090f0d02060d020921011b050a1707030e010f0f0c0c0506070507020d020409121103040f181e0605090c070f060c051e070203010f0b03031905090402120a050f190504 74
    0x4051740178020131f003042d000002c2c800c4246948000081154004407290300c100f22a0384005681e40702c43c0307806140c13039588098002d00f01d46004a10318000d590800d013110340d1801d00841072652192080c0400c1114000c1000c06121070030301d203204004e0354aa03152500e500510302c2007009030000d050f50442da5882418054141c028208000c030239090710b0300b001000302040c16030012a02074004021410780c000204d030213441c0c5188994811505c0d05840c0c00340c18161440c19200d87d6156819180007001011300c403a80f52000303c0b004200d07240351609021103102c0c01742280481c8102000203130701042c0c458403849a030780d5000c1400105e080b0001c03401c8401e8005e1564044001034400c160100200314200a0a0400d0080703000304803e542c01c51074071040f030760003481c4103030550428816181c055070480141074005c40582060351504241c0c20010341264051414101e5100507a01400790403080d074403070307554820081081c0b51000e0401d4810368900f44071114180041c15140d0002504100029001ca4040a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 602351879 1250 602350629 602350669
    0x50304050a0c080309040b0402030702100914010e0706140414090411100e0415030c0b030c07061514042711060301031103100513080c0312040602090f0d02060d0209 72
    0xe4590100f50784a9010083c9607200718101001000e05203024803c0b01e01802d41c1da0024089800000e0900d0041d00f0a01c005940f0340700d540c031381446a40c3d0280030382c0c07070400050000b1b004d9003402c046020303040310301300d00c00c412500105000c188003051880810507807407031013255021040c0d83d5900d490304080205003103654224100c1c220303203845640c0003d008130040034121000e100582c00a2b4000a61100740c1c84050403c50003400100069208840159000f00503070340240d2410129441c5c0d14291400600d00c2011140c420f0010441c650070700056109840341164180141121080f110060110744a1840d01000d003070b0740d1650812075603001038010700c6009040c00da10303580e40c1c0c10110f00083c0074000242c0240941c040b004c10048192188034031070080a00c541001c2c0d403503a100c840003a0405200c40300684400c04c1403003551812010158030461180e480541e9604240051211942c0d8404540b40281070741c40c2d400c00180d461005881d05404005001a00c400841000070300d640c500424004005c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 602353129 1250 602351879 602351903
    0xb0f1812010e010e010b1804020409080c03071208010e04120509010c0203070801020304061419020f040504050f090d0e0102060604111603080604111603230c03070c1401050703050304050a 82
    0xc02c419008920050800ca008020080c901740c10b000096603585d9412581c80340b003100007001482c1991150104500807003ca605240b0b1802c00303d441d40d484404281c820703a268a4019101c0d40c0d02444107405011941b0090010b07003481e44d25103070140d29460303c110a0100100712007203182d226001d07035080d29400a0032501c10907a100b860500075807007900c0c1542c1850610038000612881614070354020100070350290715401d00900f1000003500020308480303100f1801c020000c1da664450040a000740340c2c80c0c0344a19a4100340218519120591602c5414051100301d8209640c0c0c012920f1940500180c80c04900d500700d4100d008020300c10003803000506102102008181075000b0139407071140c1010b032010420a5030040364221a0300655684060900200480b42c000034411140e540301d075040c14118580020303c40c20401d45540140d200d110b081d5201064000501c48100000c2c8024065129080b002c0040480001c2c01c512629002a0601200201003410040304105000390315400030045010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 602354379 1250 602353129 602353151
    0x20060702090c090a030c15090503071202010c061d01141512070b16060b0a0311040905010f0501061101061505070b040516030303140a0b0f13020906030709030209010b0f181201 77
    0x8140490050500039141007c4020000340a024140142c1d94000d00900c1218034041c220000c01a03105022030400c28644491030014080b40a07520403c000442c1e6600700b103001042c614211000c041d152022040040180042e00034840d02000f1005000c0d103000c0b6040343d14401c883d1410010754082c01d04010002410b40d84440c51004030400c09203c1c0710240110b494120030801000e00601000d0180b00042142d10050320f002c1e44003800300340c410800451400f01d010328010032603509a2090000c1505000034140441083c443c01c8041c049404a00441c00c0300610f000701030b802008001040c005102000c5802d011080120600b040305240002c40780070340340c1c900180035100c425400040340301101c006c207041f04114014000400c05c0507100c1d0300c205402504001b0f004002a0100c5103107039003001200050b8562034015889425036884081c00b1600d90b10510104281c140d010301502d00b401d01c8514502250101150041d0600714007a10b642e01100300000c85d44c18140c12090f015618040814030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 602355629 1250 602354379 602354393
    0x100f03020c07060215070207031104270b0a0f050118020a091e050103140f04030f23031602030c0316060608030c1c020706021f02040b1620060702090c090a03 69
    0x40022900d215645d05448801050f655030a031808020042003d0364039000725420a40d001c0c90707011681096001c80c0100740741215175010900728040d240c5103030300c500b00003840d030450140b400905c1c1d002d44208490b40c0340a2209890009240c0b41d6402e1980005140b03070720030301c22880302c2d01030403102050111042c0d0400900f180d02c481c9106041c0404e0038000146020080000520720410050b101000301d5662a42c0491b03049404c050100b040c020000102040c01c11410303540740c000c0f050301c11041d03601d040a03402c45100b440360080303000c21540100040c1c01d101c0804810745142802c0b0180c104812540c518100001d0038042c0c0081d442d070b01c000300e071807200c103503000a15100c0a0348090201240c43d603021001c0703890340e10a003e164056405001888401000c20070b9840180d0504440181410340724011101e080d23000140c88000b43c220800c0080601a020380000e04011078009400f0003e81c414011a6045c0140f04d0003a1040f8100c8000898812545c4102c0d0600380005111203522034036894001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 602356879 1250 602355629 602355643
    0x30a090503060708070c11120f0708150603070909060209041e0509070605090915150712031404230d030c1d0a1e090c0c11040902100f03020c070602 65
    0x181c424400c5601048250303000d814600e01a50241e0b40b0f03008841e545403104403a45000c0740c107450f04920105d010b280c0c26641880408080300490300905020341c40c10504920308008140301090300d540c60b07010b01009603000244903040351480400880c101c6081c1c200342d002800745d034103d1500709007044100b0700c2c80f600c1c0c0850108900104803040100f40c4400c0c040b103a0342d1600317024090209504002da190145000001d440d8800500f44008104550500204135407208662031503024074004103808042104203031807900310901a190030000d02407203414030107407030001400141c940c0010300c0c06070803401250080058405028030840380389020600c03006001340004180f0a000921a55030b011000340b004000c0580c0502c02032a0004080c1040940d402a1540544800310000410720014042e8001e00503004c0780c8005880d19601c10290381410b141c040001d0148511032440e01c180c0c43e0050303a40111040758508645807140e02c480b20143d0543c0244510300a80c0d0040c42010000911240d0025180b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 602358129 1250 602356879 602356889
    0xd1803051501061e0e010c290609010b1905160605010e0130020f120a061a0d020d080307090504060f03060c140711010507020915030606060c060a020a030608030a09 72
    0x10000c030001071003051304004251840000010301030040844150700c11500c64902d113008202c000410f510084458400c503444141c1030390a00d07604000c12095140c902c0415006100c8450024500314211061142c0d84c440b40c00380c03609000001c02c64010b15010224440000344e44030004000c1035854411584141a0074420290300101b40f480f401c2001c7c1d0740c10354600072041103580360980701d0844d034208202c4441e81115135030082203e0002074800c3c0801c03c400041c2c2c0340103400004130100c804242d0410341c0160751134607000746107034407030351005031594404c0c02e95150304a4402516500c0c1c84e00111156155a44401c0d4007904120b00854004100401507080700c0c451a01003146170b01d865803e90f0504054100c440c06404140448800705520402030402d4030014506946040b0705640000c05944c0300b030300c100c00054400d0f652107115040810405030002d0045505904001700c2e250290382d205001881703904901d070081120b1030b56a0003508400d028160001c1039a44841c0741c100c0080c450181c4e8450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 602359379 1250 602358129 602358137
    0x1b08030f0402041a030303042a120c050a0302060318070b04031118010e010311040f090510051f061101060504061211010c0b27010e01060305070e07020d180305150106 73
    0x31240d14011020072030071301070b00f003e40a1400c1da9100e84503603401c1548815010218902c01d850f0100820582d514440134003400d0442c0c0614800798200180c82030003e410450086112440610240ea101d000ba650700800c1d80b98100040c407448004c10341001c20b6680204907096011401004020405403c10700c0210140c5901070243c21a12039043c00e0b40080c420107030f10011035001400490b40c0c0620703140d03150070060404155012900070000c200c9580400980d126001104c079010015001d00a0f01d821881000d055090703400440800d1160829510419050100c00c10030281c0e44482034110b10300504005104000311a9150007011040001c035100301c61034030380360011241560048044402c2d940d00b111560134140c4c2c1d0101800e80064007454140c404640c540c41000c00d428003405460480e10080e07001190192940c81d05514010341030708151110301c4034000700082c0950005500381314088a2401603c011803103030b0035800c00512500043d00703d000306100e0306c66441043c5d40050480d029595 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 602360629 1250 602359379 602359391
    0x3140d030f050c0703110c1507050c1f0f0306080d0302071e0f030e03101d0f060411040b24130510090e0619080703111f1b08030f040204 60
    0xa000803110101c2d1480d64600342413082c600401e10a201114291004a0454403520100d100041d004400b9a0030030400c03450001d100f030208030050055a95200040d6006141403108402c076034128092468150104000b111054501c0362081e040840280910000c4c0d42101180e448010b02a5010640a650007640300208100c408403500303510b00c1e0a5000342808484401d0760303504440c0b9421001e1802e40c144590820040600701902c2002c25403511309003480c1941241c0036406082c1003401515041c283c1100003000f0201d40d044440f1080804104c40004e0480d04007000601d040402e5004000e210440141500600003000010500c4640080502c00c806039240108201401103003841000952680c0e030401c620f00508181c0c6420550080c0246550300e1103a6a01000001541c009652903100701c0c810010300429104102c0c03001c0081da481c0920085071101c000704200c3c0050803d0411044221640310f484458603008009684510019034908007680020740b1510185c8040c4d2286103041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 602361879 1250 602360629 602360651
    0x906020c0a1b030c06050a092d0f03030804140708030706050106090b0306130b120d0c1a09061527060f030106080d120f0207030207060909140a0c0903140d03 69
    0x8000c00b0300b103a40c80607110303601a0608000b21130340e0f0841e06554040c45508080400c8809614010305011000300301c2e011080f8900302c10003244100a940301d215210441300702840840c2d401750074503620513002000c0f00a0500315508207072810344158071540107800003065a07010460180c10490403501182d543c92105912148500e0407448140c17009584210a4032903c0320050040c0c1040340040300c02040c003140a1141d1580d02c2c00c100d03040c00781100080e0520300c11000c208654403440824a007400001809242030b002440c1d0341c1c60064002c00c211a02d030780182407559607515100c01c01030185030801d011899848035801c0b9100d42600e08610408c00c040b000340b000d05051080c042100c1d800802440342c0c50309000c060703d06030508580d0607007a50700c0303100e00c0c18040190f000500b08544654002c1241900d4030760010305615080d084407520500b8948242402940c000b030098000c0c45150000600c0049000d0560f804038180c0c0c80144946684c1c282c252100d0030208540342040d40e00c2e101882070b64032700b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 602363129 1250 602361879 602361923
    0xc05030f0a0c0c0311071e0906210213110f0315030109020a090e0a02030d081609140906010309020405010b03011a0405030715020a1a04060c030209090411040906020c0a 74
    0x140301100000c0703200903004080f91017101143e00e080200810358040307035160b108124003510b80d006081c24050000c002088000c440e17104582c01400c00a0f06041e44040340070706c00c8032501d00e0f8030010f840b500034500741c2a0030440d1540400c20b030209820b80e103036440e00105c10b888800c0d013044440e51701d1611a10b900b10348900701805040840e503401002d49130b1680c18205050f000b440e02a840078114482c03e100d0f4001038900300040030f490961601c4a030130904e040c82d0281d001e50380708201d4608001d040c00c4100111a00d003008450155002c983c62100e965078000128001d107500b0401a510604020001411180c003a005606030307450342c0b03004103254a80078490300b00f9200b60310880b5003560012800b000081c07002c406464041c1e4036841942d28480c1c694541c480c10fa0400c403a92003040e00000c0900042200a1041c1011010542025401c100f0a00006540e1110050000d040f50b04241000056651942d01c1640040e5100c01c04644031012200c2255503050061421a042c05210210081c4001d0b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 602364379 1250 602363129 602363141
    0x7110a05012f07030209040f0c061e050306150a110c062d09060301090e15190b0111070b12060a03120f090f030b091e0706030b0607060c05030f0a 64
    0x29608502c4a0901c841035000503129841c4200560181060210059440c507202e03c3c001d5000c0d1030a0706094007181081c0205680c5544800180001803044003e94402502844d20b041c0107810a90780702d9032040040790144a02101c0440341e0500002c954507480d41003206400d0406800c01280c072100300400621085100e91407030700510001e04045181010000900302024a0b21a99418206407941001c60081d400a0b048100000d40340e2586120700c03c810401c000b090700328256408614104044156018034010321003146085d06c410860705680d01842080030388588c08800c42d50220360f0340300c022149410001e4082010302403030012840626104092205a079004141422014201402541c1e56000000381800788030240c0c1e0b00240100c02c3c009007000440c02000030000a00c0d20b025154100b0f25100300001c41e803e42e0003d00d010502c0f0010f40481690f01c0c0d42000900c105414002030303598002c004000306a03d0400c502020b0f001d07800009180200c2600c6401419034598000c40000e60b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 602365629 1250 602364379 602364407
    0x15020705030c061c02070c15020c0301021c0c1404060906020f01060815040c03021c11090f1513180302070602030307020d031a130b011101051308130b07110a0501 71
    0x700a00406900302031058001c1c040e8504d08a00610b409015618020502650381c0006012110b00c50f8072480585c06100454141904030b00841c607201401c00c44418010445440b0f1030b0040c1d0f98941804200d004022421904070310380d10940d00c844d601d600062140c0c0d014040c0100600070411451200382c0e05001d04400c4e00c4210000c0e0280c034058040c0340001c2d102c000d20a80d502c0e03407078000c0000036850703a00d10540010101060950344d80240d0900741401c0ca1203004142c01000704808224046c030341c0c0308942e41c0142c076000c1070b45c000403410701c0004d0101c0341c002c00100c0d0b414500b44103084483c1250020003030281c031907003d554000759140c005030303101e000c02c80d504000360704101b5107001250300c258807840c0c1078640a010002c41e07270805d1000c164186240051003141c580da9403400e00066820a80300740c0030081d40b1000b4041443d103207154440403801d03100020700c51000459016030795844e1020358406004007011603511151581001d1074156078601869016140c241408620380d44581441d100c600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 602366879 1250 602365629 602365639
    0x14031e0316230f130e060405070815010813081602031207050c010813120903140d020703080f0403050a0b04020a0603020316110f12130906030b0c1e0415020705030c 72
    0x102018221110b5500c440301c16050340a040100c20391500a031070000c0d0151128112030442071600000f800116034024144800b4004c02d001044464520301c00142130b150020b04c1d10b801e880d1502c2e421008425060200102640740114190213201004d424803a4400c1c02102241d40d01c1402c11281107072482111005070054000264039003040d401059a550045043c144401103c3c0490702c894680d603080b00d20300c800203100142c080051002040c403014000c0d440c00064801816140340184d0b0311072140c400101951404541003854030700050507a00210381220580f00054210b1a00b82e03c045400c68049210b03ca01d01004181e95109100fa00e2140131b8101d804d10382c0d9030112005580032403166221181e00c1c400c6403421000107038240482662080300c0030120781c44150080603210f0340c07220b0784c200b809043e14001c4100f011585684c0c0b03080e00007031070301919603a4241c1070119034a10504018071184174400080c000404107241201019191001c1e07003a21015134581c0c04241d01d804034840c0081d441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 602368129 1250 602366879 602366927
    0x60f0c0403120e04050103060b03060a0c090303030504080c0313031505060a140312040915050d110607060e0a030804020315010e07050a211d1914031e0316 68
    0x240e00c6640d1008040003070300f41002c003006940001011740e442600b00b103c0082d150802c03c0720a003000c10440742c0108002c0010b1042039103d0000804440f19488040c00b095100c801103818031000404903005841d141b421780c0d5a42c543d050002c0b08005252004881c901e846551140f41ca02c02482882c0c0100e00c01091402880d190514500d0644141401c155260140c40003404000c4c60301c1e00100f0007400b038013a010907a01020121142250000d501040c001d810400c090400200c001c0c9903803090f03003402c4030b00c1500e4a91504002008000740d4100c00e00385c0c403c00d031030801490340208507148541d2003141266841307850b01a520b44188400c0c0314801c880700c6103c1c0440c44031402400908900411440c020072402e034a0402a903403810565143d40c440d5540c1d084d0b50300408074411030307480b60710b004800805a000c507500f40003544081c44030018104910b04034203040c0c0000180102d422807034035081c00c11800c0392440c03400c034142c2e40140d81008900780306092081d9040c0c010322040b003084942111032459 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 602369379 1250 602368129 602368133
    0xe10030807022d0f04020c062205030301030303050a06080d39080405010320180103060305060a06151103030c0903010b0a0801020301060f11031c0204170f060f0c0403 73
    0x1807904901c034200d034010030858500303c4000603c0810742c0809029005044212485820b1141c40310501ea1020b0145004100c0c0e0740c08010005117158000c808072459156110f844903803016a40c3d0381280091590000000020906030301da0065406680c558004124143c4d49002040d5192110042c403004100e003001c26054440388802402880441c12034040d050f4224043c080c0c08102181c90201d0b00010046001d00440d40d0510903d0340d40c1c1440381e540503041100040b560a103001390b00b0007403040d40f02c58000c00c00340d0744290803c000450b4048101d540b02d0506101903405000c45c1e010f9012100100640c3c400c400d84520b1251440d0b692442c00b135840c0d07899284a0a040703034040502c10741c1640d01c504070741c0241e4032119009002001075000058032541052401400b8100014005040041a442615001c4808001c03603000c4080095140005039400000c10040e0003140c0c88a28404a0410050010760001c00c004042d01c51020540d884d591300d460351a1310121007601d07415a003140910040c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 602370629 1250 602369379 602369393
    0x60619030f0b0a110d0f050c030907030b190c0518010513030816080a320418060902030a320115050705031305041404051c030213060206010f0e1003 65
    0x2d0819091500030819030000c050180d0107034407010b20500c03082d1b80c69a02c1c0c40980320303500c1000d403c080006442e0f49542050542e8a5840aa0307000280040c045140491060310300c4031050108114070031000e005101160341e0241c00ea401c0480c00800000c2e0100303030000c566104078115580c490704a28a000301a0658903508015040380c0e102c0002c010940c01ca19001c85c0e2072401804110b4860364407400b034440d4406100c1c41b10724202e2402c022460300025030400f010f202d80705883c217a5020210b11261083c04c580680f0140000350710010380144000305001d01c8603400e070004440b54440d03142900c803844241e20030416401815208012201c1d502006102c110110f4449040d51a058940302d402d012450300c4560444c0d120141e1001201180c140030412428640103001c2d01d0010552104840e02c0c0540b10113481741e286c4810f0711b9038041c00000e0706990760300a030b0660f8564850113084076220384d22203c0107541d03144203000365a41500e401000152015030071030030500c1005102803c1e03400302d2031507031120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 602371879 1250 602370629 602370631
    0x60c0b100608130807060509010204180207050303010303080c0909010f0f0e011203031d07060905040501090516030f060803030a02120f011d04020a0b03090703030921111809060619030f0b 82
    0xc85042c4100002400305065000c2d148c003070003480300010303507a174604440e040b4074a0042e012008018014400300002c1075003c0241d80c1120740600b401b072015610203000380da00d88504030629030f11900400010400c1a88481080b0a840c0100b204a44454403503049100b1312000344260204e050600301c107400041e00c241c026036007082c10300400c00f212032800366140d42400c0e6240c01400020300621020880e6241030f02940d4014010204100607501748088140d004040c001ca100091584841d40b005c8802c043c3da010100814005d030a0b2078881c28410506406540049001c0b48a0b00c080e03c0070540c1140000c48550480b0010000c1d4807c000c951800c010f55880002d0082e42e0080300d5071400121351418800540c800c40e0190050701415045180103059445141c0103e035041151200200c01d01841280046503281c001c0500d560940c243d2000076041005802d50080c000955014804a40320020310719000d00b1048802c16039003003103594041d03910f01c124400982601e2400c00344401003503c021540f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 602373129 1250 602371879 602371883
    0x14190e0411070f3e1801080a142415010f020601030b0a0b0a0b0a02070b041a03040f1a0114150f09030c0a12060b0d0b1603090c060c0b10060813 63
    0x254000e41c0c90303c16800d040384c0680c0142001041c200030070410614142d000003114000c0e55469500a50500008075036907040f00c00024804544415500c0d61581f04001107180780034144444a1401d44404002c094048244c5201c1c10a0220404400541d030013200c001c010000b0750707401066240e10f1a220590350700700181070b010816585130158091074a030080380d140a0001c5480081c0d442560f26402460304e00c1d43da00024100c10f044c00140320050456840e00c1812810104c03c5840791168200100c401d901c40b5401404041584440310321800520011412569104180300020240e0424001c6007460000302d0f0b802e501c001c03c66420107071311001c0030300040c1030064115008400704502249580c40560030410407140c40000311001c0120030301541c0d541040130341b4400b05a501c29581c01c44003130005401900d410b074200c110f5080d41407003a404000046d41004c1c20003015030361844054904400032005030703058681200040c0700a0f02104190301202c00d40e5403480d030b203903541c440310203010b8080c1202 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 602374379 1250 602373129 602373173
    0x606060a05070506040b1e060f040c0909060608100906080a03030216050607021b01030b03100506180f01060305010902070f110607060912080601020d020703020114190e0411070f 78
    0x12030103e4410050700d0302c03c900c913108180782400d05c1c2c1d4480401055455080742d203000d90604110a64580030100c101050f403c0e2804118910303071801c15240c035080398202801d018648100022040d501c00c103001c6c0141044402c050700b06441e1a41141503404d580544412031740803801260000e803180d4010004820050500050341c0030303e6982e10f04110003a2484c1b40164040a0124080a0140309103040c590382401d003040040d016001203034482d50000e200f0f541456480000441c0380d112040c2003800100ca68130050460b00c1e10350a080c40a200a01442c0000391070000049030080440c400c40c0d1219030020100c116070241e0b035507801c01020384641a1500a03c0c20302050000500c3c2d4007446001a100e030341c2070040400c000d18001c1c5040ca000740818115481003901e80846600403075248240c1e5028038008840729140c501403140f03031264a00c403590962510501e02046a0301c58007014140c0e6045409010b403162000d02c04040e8001c0580240c0b02c00c0d14101d4910005004580310b03070240098030a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 602375629 1250 602374379 602374387
    0xf0605031506090306091c02010c0801090515090408070c05060906070b040c090c0207050907020d08150418050604050c192105010203010f08060906041a09100203240609030606060a05 80
    0x1c00329040100643c0c0aa246510095641f48080c2c0d2100c120440d4003080c5c070003041114100503005140c0881071007001c414690318408070759a080c1d200322400070b42c440542024924102407524071860380c410681994803011303011010030603242c0003080b5103440100528150822440e42c4502301030326000f400803100309817060f40010b01d103100c40c0076107443e4041f82d40150014928207410b0110710640104003004542100002c4208030b45c20035000f9812080c0100000b84600000010600030304000302d000d15410b07424860b0004105000a001d807159125000f030703444590090013401201c0681c00801100304024005c188451210b000880b038907030905d6035140044034103075290903089034420380003401107846649040c4042d80c030420016401c03104520091695181540340e6410910140c0650b034104005ca02c0807030300580301001413881c0c0e00c8410380c08542d6424444c0361403080340102060b10550303007032080c40880103140a00682d003d80c5c0003d000781007165504002c03c5196405400d0400c18484184 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 602376879 1250 602375629 602375647
    0xf1202040c02150c04080c04020a020303070804060b190611070b1b01060902040e04021f0509040b0105070605150301060603060b090405041505090d0e04091a0a1e02040f0f0605031506 80
    0x14825010f0321343c44820680c0c850515800134182000003074031a0086004200e1200900d03030002c1180e6010341c0f64076152030b0640fa80e10707201e0007420354440d4180d0b2180508002c07000555102e20694219002c50b1503000c00d910040d59200d80f6080107110303c1721a92010b1203008844180f44440d02c00c034030b5041c0000150581c03038000280803a04260420040c2a13a4042080214140a02410160441700c908a0070490103060010014414480d4140c0929154488541564003030000d468090b640000140680d14020716101210442070491500c2507013080c05c0040c00781d029200d05403e4a42c44012185402020400d020292102400490320480c2c1c1d0005070b0302e0b4110311f1003500e000e10460f50151840400e200002015411008442c601c07652402c400071000640d1080d80358031900d480f03a02d10025684a540001c0100000c2451082080b0a1101d01ca0754050550003001a135000c1c1450b90040340d00c50164140a0201e40034400118004001182003030703501054044180400a00142c0703406140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 602378129 1250 602376879 602376913
    0xf0605060c031806030f0115030902031c02061501090b131a0418020309030d1113030302061f080d030506060f07080702012d050f0d0914070f1202040c02 67
    0x91440750415080410145205480114146020b06040b11300c80c1c15801d08445e4104141c40c180304041107130100201020515019802c900e18840d00141070b10351441c9005500480ca1181000e01d00c018001d1600061400c1d400c185001c03940c50069490070481814800304001c1c0707070b0101100c01c6030004040000600c01c07144001d03002001166126007502c0d1807030300d01c8030262980d4400252840e203005008100110000106441102c014a603010517542d401c5020031409100740961045503450400c004014117030005680d40c060070600d8048002d044401d100c025400300c0a0080c010542c011410000300d9600c60f800441d04010003c080c2132a040202d0304121842c1c1c08a0011514103e0104441c1d00303540c1c000720600a001f270070060110942c00c003100100f0701542ca03080d8103000c2c840e000c00c240d180b01c01c8420030b652855081d42700400c8440d1142c1024640d4216420050a16200ea0382c0003007000700d551013154003150040007203d5584041c0344c0c00c10004d051401005811441141154500c800c10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 602379379 1250 602378129 602378137
    0x3020c011d1b0d021e13060f03050f0105040b040f0812070906030c390203030f0702100509010f050c031c05090f0c0a0302012303011805060306070905040f060506 71
    0x780001002c0214261080c03600010312070380304a02c1040d95410040150300e802030030240c46924580325001c588a0880051141d40113001035481c05403510802084008605000c5401d0302c0c046c2c81214045d100034840d0600b40d17041260020020646500400c0c0054060070807614001c0c823800303c441c20203c101007042c1112104403031a40020340120b008004c216050b114190303010045c1d03c1c001c1c01c690110035200c0d0103000c111140c1c15030700208002c0d2510b0500e000050381c040c0340d40142034030781e510031460b02100107412084d8140d124a01c0e051003941d9941c0240116066100c041c0c440401840c0e02e6103042d0b4298100d00440c040070b01040094082d80702000400e10301000c008200002c003424541000c1d03140910410320500246c2c000418040750356a514450f408407035092070160300c500c81903043d040009001d904a0f90070f5030307000b10011481d402001030f113071607184c25200100025030b03680c0c0070156601019a410b5020840c108800d10403400e0582001402c81d64004000c601503940b2000325101e03504c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 602380629 1250 602379379 602379431
    0x80a20130e06041e26160b04021009080601120201030e0616090914010b0702010c120c17090108040f110d0804051e210a0605070507020901080f0d03020c01 68
    0x800000c0000700100c0700d41e000c100482c0450901d2150404ea5144a21a11060311800300c9421859a944031520100e040f19407060303088201d118240d01390f15100441d840291070407442484078843e10034a840c4907017400c0301211b00300001030440e0391801c00b15081a074806942a410503845100703800c0071103070810106028908007101d03c1e5448821480061203c242c1d80c2203081001e0600480340714803510340030200d054445485a2503034600c4d081c8016142101440d00044c90310036001408400a500034100303015407802098018950218074100301051301c03503001c20901044004000c80d02107101000c4189844d80314598441c13103641a5000682c090310800000c4403500030001e000d20050070650340c0580c20700207200c2e51440082101d00014070141c0c8403200308150903003002144060801c100702e00010113401040404c901e08020b08018501d5100c404143d000300c3c41030000048092002900e0028004d1324000b52100d00d808103070890207580301e205901540d640b1034407800c850201c80c13040f2000c011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 602381879 1250 602380629 602380633
    0x6240b16022806110c0108061f021b0a0e0a0f0902032d0303040309030b100f090222080d03020705100f0b011101050709030f05011d070f080a20130e 65
    0x1a880d0403007020740c0b240c1d6410440400008100b5200010f13000030340919000d40c02d01b03040c440b955441d008600c24015440ca100110704003625050100d5070081915010400d10f04150f00c1900c070107609000260301544141c2414410f660b000a03405507141d40501c01210300c0d10b0010a500d00345400103480c1c22070300032145000c81450f40d994001031039a00c031003089250f031b1a0701179070075480e10341c4001c1d100c460644800740001905000051141850a55201c05040015124140b0320b44070081040290000e01254003a000c040100d4104d4800403103050045445030300062043e4205c94604802a40004c1412101482200f5480154000c2800345212003c1d02007400070b98101020b00040202c0e2501c507042c2941c1e4074060501c1003d50748040c1001c1940e802c00c4201c2404012454001d0041001c003000a200c001611446000310300d003c5900012540000c100c4100d035a140d64950382c403150808001400410200c000c03091046642e000305410b0840107044541d03c10700d02007408141c407840a4aa0345c0c50b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 602383129 1250 602381879 602381929
    0x31515030901140405030706050912040806060a05090f010b0a0e040227100c380f0c0c1902180106110717031206121906240b1602 57
    0x120790901c20f00118003076020340c42c8240d084c41d4a5040e00d0f1320803030801038806070f103c0002440c0341c2004c1200b84e05007850001d00c15036481d95031006c5034450a043e0b40740c82c81608424000905032502c2c400d024060751105c131422200d40d1801945090b20b500c0a00c01000b4004003124010b03c1d0382c2c4510280100c842c2d8000050b460b981c1c05c42c1c480c041c0030095a0028440e0f0341c6103004041d13080d4003884044146074000700c0001c003c00643e01c841404440c0340000001c600e071b95408035294588465145000d04c823000e009040359180c603201c0002c1c2c5e009902d0b01e855103620000302d21011002c1c4001c14402d181c005811501541c044d265028040e1000760000400706900407880c1074541c0b0204051401090404030a0030842c3c54281c919403070348102d140303285507442401c0100751280d540b03050210301c03040080c04841c01280b09406da0314400d40c1c00c10081e50030b40d26040c450301d40103a851690000f00411a0001d5140c5424010245090340003001c0d481c00445484180c80d00680f20100714840a0010f080c001d440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 602384379 1250 602383129 602383141
    0x4020c0102040e06060a02210d05070e181b09040e030c0708160f171c0f0215010302030a02090915070c060e01060b042603030a1b020c090c03151503 65
    0x21443c0192840d03001da00304001080c0700e01e40c0401d400c19a20444242c1d0b185246000c46180c0c00c2c0e004075400c08040358500014010741c81e800460425501c00240c62070000c80c2da10f030503500d42800d811500d505098680c070b141c800c0c4110344440200a0440b0081001403180f020504003442c41d001302e0702480040c0d100c49018040480704001303112803544480403103038403103003045c800b542d640344980708803009034221800c41d1691550610501d00c4507600300e81a98401c16200e00000e0213805d11400307400160013140c0070010305d45007620907981a00d40150091681c0900b6500b8080095801020b070040d038001c10100c1c810400c40089a103024800382d507501c40c60035072141050400c88265800301070081e85400020884084200700783c9085440c2407555080c0d03400242a030b5039540310000407103602e9000000800c036040e030441d4031000c40083c0b400c0b10001a00003441c0c0aaa5814014000c030f80d1010111001980e4441c5a600444d40314290794401140100c4150201e0001860201445005107000c030030840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 602385629 1250 602384379 602384399
    0x60906011a0910020a0213050130030e031929062b0c0308030a0501320a050d0f060506030d0e0409081605030301060f05070b06010c1104020c010204 65
    0x40509400c404a005070744070201d4031056803042c0342495008002078035840d00e07290700034001110401d401500001c00500801500d0000302030901508150884100444038521a008504c07080c0c610520003a200c0040b89071410b075035071948221a10b9040c401c029502c4078040a1425504000f445000c581503000d1406d0490a8000389241e80c49280c0200c060401905a0b030720048440c03070640c1e0054444440d80d408490045c0e0316034000020b4400c4a040f8000810044d1001c0110f100765014a0100702c1d60b601d03040200c4501140c1302c0345807651521604d103001900c0001c920000f440100600804c24980d860010030386c041225081a25012075560345282840918041c1c25409070044000c4e01010f40200c0c0301070003c12080010b20b0055076143d08010401c080001125450750340710310103903101d180741e280040d600d51003402104005402c01600b408110700407400e807016a0750002c0d4042c020360f1080011500000030740820350700000600042402034450b1310040c0104c0110303400140e030f80e908044844d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 602386879 1250 602385629 602385631
    0x120c031c080f0c091905030c010c03020c0d08190210060603020c030a08090a150c0e0102070605042706081605010504060509090a09150b040b0619050a022505091f1205031209060906 79
    0x49c1800300042e4000c000990114103821200c801b140c0180202c140d60034114a140241c034044000500c244140001840e0001882c451151000c2424442c49454040407400d9000300214211580c2c410310107140050b01808107240d0000046003200c400c40c42070340311107130b512082000c18440c40b95507031044403445070721400c0c042d4070740020300081c0304081c6070035001041031146100d101280301ca14010040550b0071103504000310210001c050004548804200d9220891082c0f101c501100301000000e0030350040d000c0d201242c4603511074505201c240000c0c4655000020140c4151039511815040004c90340201d100c49000d04039030001d4902003503020b0000b22560310003058072601052040d8200101d90090b0a00140300c5842c0503a00e59a02c203100f645085601011035959040c80410303188100341c2a142c41040b18002c40c0d107843c07103443d4010800e101d404030080802c0034141010060002c0c42207a040803a1042c8117508891030400d1020308144550001d98030502981c00240030b0005c1b5880400ca89 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 602388129 1250 602386879 602386903
    0xa0f02100f0b090901050c0d1109040c050406020f010b0d110409050d2109080304020103090f0f05060a0b0f181302060301080105090106170604020108070905120c031c080f0c09190503 80
    0x20451b038105007400030b0044c01381c4626030740c4050b02e45010080001019080d2512030401810500150b0740307148000d00700782c2003400313000010703c24400c1055024bc2c05000e58224004042d010030000403841d112040c58000c8240002e803c81e842d5404080003a4081050542c502c016598030251095040c0c0d28811032522142c503880319909209108002c03401c544200c0350044d40c2402d000400010600c5d0541030006a10406440240b09104030300a0040200c0e00714800c2050007400c1101d00e405508201031503d03c0302106400a540d4109120807121522003260845011015095500055030018405500982114201d039440d03505000300d2000034001e441c058a00c002c5000c403010480d0300780940e0707440018030280c100311201020030401c601544881c4007030700001d0101c1301c541503005a100c0d40e40d83c503a20386901034469184103050141508400f0302d09200c40341d83d1041c0310b40305d9885003440810041c21071842118200000c2c0c40c1c40d505c1e44100c002c2c08000140400081d0703d08010941407140702c0f895 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 602389379 1250 602388129 602388131
    0x906370501051c091b031a0f04050a06090804050a140414400602030601021c020a0b250c0302070e060607081c020c0717070b0a0f02100f0b090901 64
    0x94005196072070707007401191480007400040c0d0401c04d0b050001c00c0580000d10381c04104142e240200903c203200718404141004982000c005407a5400c00940d0320008072805010341c0c00038064130000030346503000300d411540a039584508050702d800014802e0a810b500c903280c0f102300040054918181405803000c8801803000600041c03405d00392100040104580700c440c541e540c90b0f20f40400000c0d0812014911000040e5011038140500d00070000790301c16a00103002d40329a03002e9100b0b2103200021070342c058800b50301510b103000d03050f52002800305c400781c0010042640d0306500100c3c4c0c803032030f403d00201003003d0383c8020341c500036818081e00b401c40da5001f401e515402081005503a0703e9910840c1c0b03d185d4000b05003952208482d40380070100f480a4010464107000007040c48002c0000075600054030145c4200920541c0c514032401c2d80c804551191030030a20042c080c455000d80940e17440c000121080c015aa518003030155100100c55448100c400c000ea0350300a80159400c2c119075003903010304400c0c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 602390629 1250 602389379 602389387
    0x10902031209120f0a121715030c09161817032101060215070201020904050c040906060302031302100903080a03200a020606040b01140c0303040b060102150105090637050105 76
    0xa00117441c2c0390184405407880340c40140400d040361140702c84104a01080c0d550240ca414024890103c0f1070409284c18400c1c825580355504074540108403d00038503400c001c4d0480d072902040d0680b2503111f8080c0032115015100000a0f0040141c0d00743d50900c846400035507a90520080120b400f5980c0554180ca86514940103000054001903001080c8031100b400c40d44030b035500601280607204149a054001d0305003020b20004450300d501803c252525194203220281d10341008a041b801300310f800406051010b03a0300005810012446204000140307442686580c0fa40c407000031a911421446001990300c60f0901c001c01c061000900381c3c0415464024036108885100a589403000342c4107521442d60707a02d44e002c56a000300c0081340c1c0a002007013000d883c1e0045035a03080d00ea80040310140c410784036610004005602c04502c11014000c0b040540555034240030034004d15940080206030403a42e51211410403500031101c10301c0a44026040a8020a05d0007800b15410082d9001a043c00301c280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 602391879 1250 602390629 602390653
    0x307030609021215040f21020c03100c1220070506010312090501052a07060e0306060d1205090105070c1e050a1805060411030705030a05160f0c02010201090203120912 73
    0x424150000e400c410440c60b0b111050074200c0e0500311031047c02843e5010b1410300044141c0108200030303000800c90542e489095188030340c50a80b406007040c500010f04c04041841032850740e601c0b01001c108606215049110905104460b950044105840740e900000040040258680c00328850300054035000b0182803078200040d1850064105903e6040b9580c0c6503010500b003840078110311034664404540e10166281005000c0f10200c1c0482802030103845c00003892800e008056054142d448078030311010901c42c031821215078001c14000e130b0401c03100708040804129103615110240c40d807502c02c03080240036025803541c143c405602c19405101001410440c04000c0b9a40200c2c0c40e0f190030700412903650b680009002405c1d09440403021400100034802c0f80c5511101a41c42036003000c00070011600ca08503c5078420002580c80d80001d1044030b18104818440c00e030a40c651481800041072011140c2d002a00307202d80c0c2d881a200580c00800e80412520b0440c0c43d81001000107009460014160 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 602393129 1250 602391879 602391913
    0x20931110712021f0c020106080304052412040b090d1107060f050405100e28030201050a0509090a0c021209090f1f09091a0f06040509030903070306090212 68
    0xc0c10040d0000d0200c40c09441d50500030301010719a02e600e0311100c00c44d080c1d14103000c4010f200c2600d003640107618001c804075824000000322001d880c00240280303554050034050851000c0681c5e90b040c542c21080c01540301d85403004901d14040d030711405500e07001e45011000f2a1501550140107010002c0103500c04008510100300001034410074502490500744c849130617a55880f8a5000700c0d00050b000b41d07001c5c08540e2120a442104008941c4004d4407803002540a45038180e007100403550440a0700108010340c0210010314504096041603070901004c0d02c00112070140441d0b804421725154080707105445e5050003403800b08400d00d01c0003800c00c1000004601522401409401500c22078008940f489107041041d10000d10410521040c454840380c02c0400750900c54800c03034031852070203c03030741200801910707807481003e4050401c0c209940b01070401c00907100c09401805140801c00c1601919142404204050740c090300c40031403201d1462041c0001400c082811840c20780295108603452403103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 602394379 1250 602393129 602393137
    0x51203042c1303210902090a0f05090a050304211e020f19090203070e10020f06010603020a2708010204030503030f0c090112020c1615080106030606021f02093111 71
    0x180710f001c043c12880c001d00600091074050340c00780d071143d500340030401300409641013071005460410003445a070302c40c00c5001d40d88045a40300107200350000d00c0107100c6a5600c0d011021400018013050140c0070b8280c5801104002100762011031151c035280c40425400d00c800003c000e01c41c00d8544103403007100c10703841d15540c034a11700585c1c078401c0d00080403981e03840c810305891300641e6008000c0d03001150300d00340103541c82c11500c641c07082502448000050701c0c1e00074400d403000d01c50952500940551400f05003c2d80c07c52205e4146202540c0d1680410351140903c0908003961141000316544d080800000020003c01004081307640c2041000c85580e981c05103000785802d400310310250703c812a0030506410403a5100204030502803450000544482d04c5400c042030b00c01a4860500c02d903220b68080301524a68065030f000750b4000030008800b81003100d1a0b82c500b042d180c02c0181096801d0000441c0400c480c003141c562100da411032280622900b0b04500080051090b04209601c4011040d4403c0d002d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 602395629 1250 602394379 602394407
    0xd0503120c130522020f040609090903050a110f120a08090106080d080c0d020f040e090706020c060f0706020a0e010f03050f040305070203010b030d031b0c0c051203042c1303 76
    0x1001011140c0e21200509882c000740204c1a05645902010707904140c1074006104000006a80640c00524107980e8884e500040d0f426a44203403401e803c0c8581500c0080b010fa900005503c5142c140066100c0140502200e140f24040302903940d070b4145200400fa008083c20452050f494000100100703500083e14940b0200c00b030820105680d03904404820074042c10f616a441140001a0f03500c05c40d98140041c0b050b0f0340440041d11058032880c040644da00725502500e40541c1c0503000804852410801404010700100c00c07151804000d6a01d610690300007041e040042809003074007038565a04042110888d6045240420039442d06ca2100c0c01301d15000741001d000e021380041c04105540f07081d0420351140002800b25240c804420300300400400c0d541903014101c01e0000d440004aa100780710700c078050782d08800012200e904050800040b00300301e1000c0e14691008200008095501d410664111240c104c03154102c01002241c02d0000c4a00401c540340c1c50714141a005d00190f0840405000301c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 602396879 1250 602395629 602395639
    0x110f0d03110f0a0302040312110601031122060e0c0a08010e06060405030f15011d061e0306070c050105070801050d1407090f020306100801031a0a0b0d0503120c1305 72
    0x210040c4000400340c8984840c00c00361050001e03081261503010340041003120310a083c5140c22611234501100d50000800000c1201c1d0400401003001c00e00d00e4940c0d07414520001c000c00c4014181120203005280503900307421029480701010840c07649006001540b00c280c07000c0d800c2ca000010880148032510500404070320443c0200030550b00d0700d6910035034018140c00340031a00d200314140d00b0302d50743e100d26048820001b41098000301c1c201c0e850003440d56450717140b041e00c0d42654480400300414072180c01c100c0d550a0b03504c0381041703134030340e8007049a00d008110b0390b100c140e8024813034101203003590301c0108800c051100701401000b10791500c040d41050b240d0020000980c0014040b011401c6c0744e215400b06e42c4041c00c00007180301180b40c2e40e00031400b450301181c208100c8041180242d40c0c55a0134480a0700c0b15407a80f000301c00750a81c441075194008025103002880ca03a81c400060158240783c1c0084e00c2d660f00c0801c0d80000250050340664100704142201c1c1d04240100c607603401c50820600a0313a000b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 602398129 1250 602396879 602396891
    0x9070c0c050406140a081b09040f0609030c0605060405010501080408030406110301060e0112050402182a091201091e0303060b0d022812021b1c110f0d03 67
    0x301916500c0e510192200400c140301c0103656513640301c2040782040c64244a00600000002c5c03901c00043c003490401107072802185100103d504105203440c0c018001c0e500720590703c030103000003200341c4204040144070346c40f8650309603943d051050440d02c000349103c1c000d0b85448018082d0ba80c00807146603200b42d128220984e00c0d41e072031400c00d000d02114480c5c000140b00c044000321300690010102e800d40c0c0800c1e40c030f604e000e6078000503110645500307070740c041d402c643c120307d15915898038802c40b140c1c0081000c0100b071240b001c4104164901464519094492201060301c02c51450700c211760041c0d0040e034400a00c94403519480e44203a191441c5e060108151850f41d040e02054020380118000385a002400c50301c41001c200e150b03001e58065424441e65024015000841d850f03c0011001d1440c51551043c491121580c0303d00000d60002a24120311510344004004002041240c000404042001c40d40da951114038054555000107007490798a40102000740900100081d0316644d00d0380c686008500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 602399379 1250 602398129 602398133
    0xf151c050c030a050d17041104180804061d1e10090e1006030e03040b160602070602070318050d1109060d0f0b15010c0201050d051915030c050d0209070c 67
    0x10389981c149059030940255442d05040c8980402d68220700203107074a60321a50051340b124005008002c4400038076440040c01803424908040e0300c51034460070302e0703005041818015144c24103290070651140d130001e541010314104071000007e480c2c90f40c6400362007034211620100c0c0d43c800803020000109028501c0c0e1100515a01e10504504009001040109500d804c200001c0c419064403401185c000ca0b00380240c4521f002400011035080f155100c01090410351411116880d01c0c066003400d852580d0203106d0744000c01c030303144005d03d1024400c0d2501d0240140043c10918080d04551200b840340185840490104a040100f0103c0000480d0302001e2640c0b4140084c402c41800c3e1009802102107a60340340812011001a0380075038183c0da07021425044003801102c440c4416100240014804d010061544049400c200e41028134030045440d1030404900000484541c40b4200c0421801014100203000ca8207403000c020708000e03642c0700010040c43d0086001c0140281102c5d0811a4602080d01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 602400629 1250 602399379 602399383
    0x1b02060a0f03420e01030b0901060b03130c0501020c1c1505010b0a0e03011806090303061503060e0c07030819090503031617010324020c0a06050f151c05 67
    0x360030800d603004030540c0300244072004503808001d6400c150501c00f45410f896018456070b6410704560015401d1065a82036a941010000000d040c2c00003942d280d400c0462121602d00c080c600c034405010419401605500700300300103805660000c0d05540250a50741225101c04081080b01c41640d55152104600e9140c01c228580605036044002441d041c0085150280e000050107010541d030780b2407101d1a9080109400c9130b20840021001104190b840000140d450b005210404d019042c00100b05990306010040c00d403902c0e4a00c40020354554060080d0340700c03a070944d03030072901c81203005003480740540c1c000e00320381c02c0500f80058112182803003036203c17089504007844071070344a401d4a4481c01c14408136000c50360740140380004100346d0a1104a200b003e03100d018100e0350004600616103030032030a040c101c41841046a03180540170000741100c10400c100688a0910900300000c1918207941c1d818a8040041d12400c3d4100c0103090841c130790303619815003080c0701c8091540c0c05640119890b040b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 602401879 1250 602400629 602400641
    0x108031803190602071709030a020108070201020d1505011d060403020d0c0b04030605060901120b060609121501171204060810091d060a0c02030d15180506011b02060a0f03 75
    0x12003184030040c035030108421600030b806110310551440b9800c0000181d00546c6010341034059401d507105100340400f543c030444a50741c10102c0c80c0001841c10002c21064001d80e40514035001c44070070903100c04c0000e96030100d818256000708a00c00e0f2a6000d0460005078180702d5440302030320404002c0d06540c00e00c03000c40304010003401d8200c0310903529580d0380741020280100b124a00d20074080c0c0d100014021310000296960554405c000b03c1c55907540c4020000d0321b0b0800c16889420041c01c90704600e24540420003c446441503040e015415850321495400044550403608001c0d0011900e1b43d480c02c0841c410781e0207a6800341440144e603551700d0306418590a480c0d02c240511804d02024141d0a101c412030440c0c4604520180c91032581e604140070141c3e440c40c014400161b100304401448001203910000c004c0520125600c0d690341c0d00d100102c00c0f945007080200009a880081c08419a00841001824841306d130105108001d25000104103000341302d001c2091200b1300b01200c1c0344620030342c018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 602403129 1250 602401879 602401903
    0x70b0306121504020a060f0206061519030e012019020c0607140f1b090603070e090708010b010f0801031b03140d080112050307030f03140703091101080108031803 71
    0xd4070b00c00c500305014111224150340584c010040c2d0280401d100d8032070b42c5205403040e02c903002001540c481790144401000312401d06043c400c0c05000c003100d0341c0c0e0b041e5020000c046040d6408281030700408070960840340c2e000c03c1071300f00b403182c2c406c041001c0c43c3c0b400c01c1d00c0030000200d0360b10000100c3c4040a90800281c01102a40b01000180c4281003115030303200480220b00c4141110300c0d4403c01840c403541e03162007402c04801030b03860301d80a40c85441e100428981c0402e0282c10b542c11150b44805034082c2010590300310555402015040c403c40909110f00c20541e403003482c210301100003c2002420700784040c00090000031188035026214084d0f02103000065500000c103030000305030300341a070b5160601c0c1c0709030400050010000155a000d40b181a58410760804059881c0c00300d19601610114940c0c07488800345500da00301381d2103040081103024411040ca44010403407244525042d40b20302c4807003810f40d0501070b8180041c04100c40010030f407030021600c0c110391004181e801c00000d18142c410744103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 602404379 1250 602403129 602403133
    0xf1009060b0304060f36020405270106050607020f0418030203030118110d020705120705070303080603030c1c021501030c170d0c081810030519060503070b030612 71
    0x1c5508005004511460280b1001c104810b00c9444280540e495060030b60b050764005442820001d0001071100090a800d40c0f0909201205074089000d0b01e0003210400c0049072012040d181c2e0100c40590510b90b0402c040c001c0203040c0c00d0800052481c0a00302d0040c3c06014220644091074480e5408400044100940000201424500255a40d1003401026220110340d400891041131a000300016040d030400300764142040314403984025002940251414801c4c142020760701075000f0010241d650242d009440241d04508000d002e0b051b010b006240603520800c80080d02c0107002c1140c0ea03040e08a9022904241d202c00c3c0d00f00e1400040307050006201160b24000010000c162000104503a11061000c08001490740b0341ca440e4600d11035050041042c0d2a440703030009051074001c085200b05006040d802d40d10040200340d86203c0310780e048011036590f02c00d0100208811040c1641c0b0881d06000707000844c02e020210761540b41c070344207204240b180440452a42c0d5100454840c1100752002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 602405629 1250 602404379 602404391
    0x1503140607020c0f010507060f2d0605010e131d0d030b0a08031204110319053004030602071103011404110102010507080606070309090204060f14090102060f1009 71
    0xaa6100c04003030781c40001522402c940f585141c1020601c0c40c0d642c84050b11a5814079800d5103032070303020700120800702107000d60f1052030703099113003020100c503070b1140640c840310442c039220302e440c80d0464407550032103418041034110306141680d551001c0701c85d8440092002c220003103444940100f0a4802d401008580a030408d0508050303815030001980720400c54070b006049694012154485c41100110140401c000700040c02013a07400b18038049991018044404041e90781c0c44090752001400c4013182c064105141d00840000110a0701000080d0118171802002808080054a12031440024801900442c0b51002c1c00052000d05445c0070000d0024001c0c07030007451147c00300e64030840c1e0032145041d8840e00c861283d44144078141c03040c140c0c2c5d111102a44c45000401c075040e00100d034210100300b481203020905030481e0015000420f0262034007515405415006008100d803058031200484d4180641c1200341ea0000740d06821140340c5a4501480e00c9928031010701914a030400c102540c00c1c65 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 602406879 1250 602405629 602405663
    0x13030209070c0203060c03040f0f0c150c050c010924050d0e060403020f060705040501031d070f1719030513120804090e03130519031e050127061503 65
    0x60b80102054421010358030703542d58510300343c01340340001c2c0d13406403148000041000005c0d01c0a40340707000d024000c50120b186640d87d0070400100d1800083c9400c000383d2111080810080c00f0014030050100c2424000280760078440ca01d102c80b0003041c800f4504d460350340064020207008804503100c100010030f060100c10f90148082d03a40d100c01b074404400510401d044401c3c2d10314007250850050380307581d642b9458170749040c1c011000761000d5608404119145d403a9914803030f004203d840d00518180f1215560980f5244040410680301d1032102d009410909124408140c2c0e4500e4003600e640c1428401c0d240c00310b1030000900e250180d040b174031001001070059414014000090011540c89007400e011200802d01d2058030380c000c5580240e0740000d03400e800d2285141a600c0c0800c50202c3e50340480440d1340c0da840b4021050f06d80302c010544400010a0030042c480207020300301d10b8040320401c10403421032700303516000c1014198502404080c0c0d12130b06111048134a40080000399001040c01042d81c20710 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 602408129 1250 602406879 602406887
    0xd0e0105150a08030f0304020d0309181514010203031b190207031104141305010e01150302130501032301110a0234030305160507080a06200904021303020907 69
    0x304180d0b4851030200a000590600c0001180c3c5070440c0441e90301c0c215140c982c03d200c0070b41c50307600c412403c0c4822107001041d42105114000e030000740c1000c0200359403403c3c000303000020b80315811640c504410410b0b44030703490340c00000702c0e13400c200c1070031a140c400030b280c0307000c1915402102030304d0300c0107100d545910307002c0740d0f00080d40d10a070380c0690300e190200c02c0c0150800048400d12100c060302c406113800004c1c403c030080520100070a005000104e0305820300c41400e0f007103030081d004540c40d071190a8424800e6080ca001280003d40300340030308002e1385d410f68440c91502c0c00008005002e046144404144c0b901c0203411004440626140c01915213010400c02307503c5d104a541c02030b403801209441840f0301e1258003014000d2542c00415008085e0a5841c219a03545c0110b10b01c50060044202020010740d041140314018111400540200d807a280742413010784a0401c4140851441079200da916294030b0340c00c403880c0c960202e60060741d52541200c002200e08a503800a50301030314050030041000d803c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 602409379 1250 602408129 602408161
    0x607050a080f12131502030912040f0f1401051614030a030b031b0f01050d06050d0809011706090708180f030c100513080f0c100f0f200d0e0105 63
    0xc001c2c400c080341e44d4050a010741015045010740307110703100c0030155002c2816a00841e080300d05d01040c3d035040203a01e0340a0f0031a60183c1d0003010100c50040d800c00450540d8450b08019000f00000d0508400000f40020818090038800030b031442d0390050b481c020460007000e0420040406030507651a1201601c0140040c040400c0350750003030044a0710380c081124041c0d03400f1029100200b9a041e610b16040044a5903007000410108080c2c0c1c806011480d1b6540c07142c04038000d032051042507502c60a110004200b04010f9600703c00d141c0019040c01825910348101c254052440d141980e01030b80e900b8558245142003c001000b5402184900b54414502000500c12049250b044801301c0c4441504681203403801c8502d41035942850f0340000010700e034080201603100c0c44134150341c20b0201502c0107a040096031428102c030550b4860210702529220301440400105a100400c40c207242d00c040145034010340032811210710350010784a003140c15164400c0210300f200700001c02c42868a448180c1580d14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 602410629 1250 602409379 602409397
    0x10e01140114033301080f070905090c03010213050f0109030f02012607080f0603070e0f09030c0313140a120308191508060c030108030a0c0309121110020d0e0607050a080f 75
    0x1900000421342d02000a070309011010341c01d004000903803400d49c0c4070004000140c4082c00394080c0c03000c090031b11f41d82400a400c11403500311040e004640352504005094140075a40c906008120340200085400214a4842c1c82d40a007003010050f50b004950055402d4120201032180b86141c050002866101e49598890441d20059019948522080543d1210940302c2c01001d054058000380002c0e0444442c0d60304051840200c90810280900c56420740c1c204420382c40e1000780c0b8845c10000f02c2203494030000714078002c0d5201c1240505140c081c00c80c8005032480903060104d0900440d022202954201100240e43c0c1406c0141445c0d01404910016051098070001e1040c04086640c03c580f03a07044134121071400009600d40601c0e10030590340807d48a106500f4013258010000c0c3d095000341100001522032814200d00007200c1c1d00f00302e10038001c0c0000b441194402c101c3e840d050354005021600e40f40c01100c5043e00c1e40f4107868942d18040501070b0082c608280468000341d8501644050100c1c10707 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 602411879 1250 602410629 602410723
    0x504091a12011d030336010e100b0d030509010c020d0503030c0406030e0708070501120e06010603060314070806130203120c010209130e030304080a1806020f010e0114011403 76
    0x625100003213a0781740010380700c09418407035065020701991180ca004521002c1d00210032005840103aa070a402c40f030260741c0d0000030b508428168080e0340500c1c402c01c01c5014045421101c03044142d00c0c006c016008040d051414099045004020340d650481884c4280340c0c010112076580c82c0080c03200480d03410510811010a05110400b0140140484d0800503601082c006108007407801d030046404c100f50401c5060501d542c0d03401100c4a0406210041c0603000d1902e012034803034030314a07020300a007101c440e6110494006034001d002022012075125088203207400920701401d6140002418040e038809a07526241c00010202900441900a001105011112400e4083c2c0314440d4009462408169000d143c1081000800043c0000041c0c110306280d46000d0040384010f01580760b40e286140c02c102c0140c2d104070034107068003800b4025102000204e030300070b001040c2420003844110300180510034000d50312241449440c1c6041085840c181c00720200181703400201c2200c40181c2e424034198580c54 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 602413129 1250 602411879 602411921
    0x10020c010c050c0607080402130204031a1e15040e0a050615030609070302010c03050403120e03010606050c03030411041503060e011811010e0f0d060e070501020d0504091a1201 77
    0x1034040c000352010f201014015004541c3c80040445030494010000c0307030322071002c2510110b4840203202a1000c0d62040310342c6002c080e04004108000c240c01400d41e40b1050641060812004000d4100380d0451070080e0080301c10102a03001a0141a030080b800b03249200751800e0005020340020740c94000c260b42010403a04203540d40906845410490700080300c0d40c40030000f000103510030381c043c800c9c850103403030018101074580d601c02c80c1041c040d0b04005e0025070f0720426124280f40138422100104054100380b450451014030245d00ca000040c0007a08408400c00144401e49640d00100c0c81e10940d985030450842d22031030028000d010502e003890f031940c40e141807141035010f640c41080c10781d80c12048861024052800440c1e501403030915290b000366151146203d02d072162125104914881c420224600791103000003440c14000d80d12507411540000c19840c21560400b0440d01035a48020001c1070b5403030883c0a00b038850700f90402803070300071000d00720440444074194040f8100c12203604c000b03908 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 602414379 1250 602413129 602413151
    0xa051005090c010f08060402070b18120306011b06020409060609090b19090509070938010912080f1803010e1b0f0102120c06010609080a03141b10020c01 67
    0xe200302c90000340340460503040102101c240500100780e4441c0c00100058030b0302c4410ba42d0800100c41c150341c000b502030301d00602d44625440900201e0301c80c0040c0c00003607007140b400b500020a04100d5824848103803268400740003e010081d0100c4010f003924080c103004807941c0d80e00061510805119202040323240102c0c01c4118605500c01000d103488000d0111101810662650300030400640050070501c900c0c800000c0c91020760045603007030b00b0300120660700e40c445198021454000100455510004010b080c3d02d141c0c5c100070309205441b540b40003030304403a40600e000100c5108151444002c01008610803603581030fa100110131120b4103030020b000d0404003100307a55507154032205105002c1c4000d1b480c40003c0c00e200b83d03180144081441150320009400c0d0031083c01e40d00c81c088201080d0050001440615000b1300844d0003440c180780103200c444420b8900803c4200c804030444d060080000e0300e030344405081c8202d00d40d40140c0c041a141800341c00c8007210000d40c0a804003403c15400d00248010b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 602415629 1250 602414379 602414383
    0x20c09010f030803010905130b0f0a0e03070b070503041e08070c08010218040b04320708090a02060d1b08010603060f120b130b13020922020f01020705030a05100509 72
    0x80302d6101250b04d003103900b44045807002d008020002c00079002d800180c100416214100b841c02040000003000307003400c151785250290344a015024a072070744100b003540300140c0c100709000e501410503c1d0079500d0703845501c2c05080c0252924181d68086d2030308120b150601c282400107052303080c0706002040040d5901e01d0f1460a0740204601c0c0340c11030580b441c0600150601d50000400800000c00001d12030110800711100c443ca10188070a401c02c40307200000301d07a852000401d40002070750804442a203000d540303203551501800790003401108080b07004808420360343c03c4110801e03000c1e40042410301c0386071001020403109206080010f8101030001a6481c0000000c406407100e0394822088401396440c0d036441540044c142e5580307102c090003281c02007035a0303184141c0185920025002103441c0d030700401440e558041c02000b0301501152500391001c02990031790700701c00e505441c2d00e403540241d440140d04009059200503094000e070645001007000100c0c2c07050504000910030021070721a001c1143d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 602416879 1250 602415629 602415659
    0x1020c100c03140d0c05090f040b0d1502090901060c2a0902031915080601050a14091305010c030207050105010e0105210709020a0f020d030e0309010c1401020703020c0901 75
    0x20000c90740d44a1940003007885448200c10b000000103080745400b2014405104032041c01d0302c0040000c001007005c111500e030640c241080208100c90a00940200340d00180c0e1038020030304014803559541281e0064010070f901528401d0300000c3c5603120641c0d440401a061a040d60422a14040102d940e9100c1c0e100c03200000004020766080103410506014120340250f10240282090820b103a21003c3d42d0049800748010b103100c458400c8040d1841c200e4410b14040061b0025031181190f68000d101100c0061a1443c03060f504031a42c1c1d8240e15440050020030150701d03401b800e41c1d402d01c0107055419405030010103101e40310794020890b607070b61864120701d01d40c028041d455002000da00f21031140c1c1c6501a020741240c920000b940c8001d07a50780943e034126486040b1080100d1503110b08280700300e0301441408a440f10f181424000070b641c0c407003070b1900c0744034001000d41400f103000494070a0000c5002803001c105600d2000b1036803044c0d2802c02075074907251001a288290790700b0700046844840100d0384 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 602418129 1250 602416879 602416909
    0x60503010c050d1518090c05150901020714130207020409022112030402060910111f06080d020a0818040f050f090a121b0609030e01090801060f03081602150901020c 72
    0x1c40384017a40c0501c05000410401e90310040c8000c1c0114880d030b1403e10421a821103804180d80e00c81d00d00002a0400380d182d4840313810001c440099203995215041c41400c43c2c038208800694400701c0e84005401481200300180d01b10601c00b00020004440440b214404038200084038004000030f440300702c50348801c80e8020342140040c4040e41e00750030140d51200d2000c0450401c0010750343c0b48007502d442c200d481c0000224081545951410345c4a261182401411141010b000e1102c25041e0180d03848417021b1006054410020340044200c0f19040a4a81e103c4018002e03c51310300082010005003100360b44c0114100240008a4906400022809000c9a1094560a11040c0c1c0070302030741c034800c00010034456042501c0880c0c00017083c42c4a80c030710682c4280c0b02c080600804100040c47d4210a0b04140401d0707141c03001c2485078207036020078002102da2001000b980c0d8000340c0302071a10820f50b40c01c000c0d0842004003400088400c0d920180481c0102a0b0840d0700c490f280f1401c01044001c19043c1d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 602419379 1250 602418129 602418149
    0xb040501050f0705190b0a050601080f1324020409060509010302180403050909131b06051804060302180f060114040303030f0e100606201e01060503010c050d15 70
    0x54204400040500450f40c060000e03201c120162203c46102d060305e5003000c50700b0020002c108007011110740300e0140c0040f001c1c64800d03198030b03284013002c603020341c0540000203070741401145a08211041c180d9080802c049051800464107001207031000e5046405410f000c60708040010410341050102a070407680c004041c020080540d52040c030044c000548180c0800800f04040000303522013072030302c5010700103981c2d09c0d0b100c1904034185008107180d02964403400d1580d10302c040001685c0082521860030701854241c00b04419030b030001c4c00420103980700941104081c005084601041000580b040c500240000080d9503102c004440007200084000f212040901c014000302e4480d5000c4403407140028000202060a0246d65140100c05640c914000d81c4400042c8071981e4031041c10110101c1c6100a51703a5a14a44d143c0d90302c541400070300e8070381c0880c108859a20f204003500000e00418001c1c0080103943e086680c000d0007580031040d441551800c0ca480c1050180e107600740361003210b00c0781c2c40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 602420629 1250 602419379 602419387
    0x51614090c09090c0a23030109050711120a091d2a120c0d0501090b031207020d031b151401050d020a050105160c0b0c012711040f02031f0b04050105 65
    0x1414024a030400fa040001308034102c0400307004030351130707000c8030460348401c0d06e00d81c1d283e40c50030000001341c4034000d00520404c0103181c003424071410005080000d40c0005d90740e040d1181d5085a0072190b80010313a018140450700990780c1c280c443c050389038031030160105003110404400000b42409036103001001e600c031780c5c1008201a041980d00d110310541c0055503100810300e0440c1107815001502d4080e045665002e41d00c07030b05d561040c0f40c104030203010076140111180c00d04c0c0035500012410240e10001400b88a000c41c91032482800f90030b401c14080b6400020407241490f030601400041160703d03410020388450b040007041a151880d0140304403a4018180c2044d6428030004642d42e03040309444241d0520425030100002c0c002e8000c40000d0b003406035030f25172034114242d105402e417405000460403880782c00300c41200041d01045007040d46601301e01c41886000340707880894000c02c0400c0c0c801e0000c03440403050102d40320030013480324081e05204402003c0c2c80e0311007811646905c00c922500b804120100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 602421879 1250 602420629 602420641
    0x6010602102705070602010c26040302011b0203070b0c03271606080a0b0409120e030a0606060c022107230301020301030516150905010507051614090c0909 68
    0x1d08018803070548070118410302d180b0190712020022880e1800c8401d50001c0c1c100313110b500da091040500046c81480c00c00100f0150451a0814962100e5000d0788051090000340031326000350000c0d01e46010b035500a070030105a40b00001d450f90410300e4100ca01501840c0800c001d10351080c00c2c0ca01500441100d00543d0401944600307881071009144582e9009440804100030300d0400701200918254441c046503241c081090400c90700f45c9000a440303603141c0141c100100782c1054024014050354184a4a0030b0700030070000b480c007030000c28020140340c10b0040c0400d9059120300f070300f1201c41c800d0f1441203140000e81480400e602a4a6490b8407544c05002c0801c0b0410200038612282c0b030030155400665074003800424207a81c1309800c10380b1107601400c071480c005001032a5010061404070000520031000f988001c1050800b4400c03a41000004030b410310900409200c041c0303a0440c0d0701070124180381d07519030351400c2d800380600c0300b03106a04070400234032822510b0084a1640c14002e003842a543d47d51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 602423129 1250 602421879 602421881
    0x50609010309031e09090e0d14030a200a0f110303270a050106080f010e030a2106260a0f0215070803130c050612061203120123030601060210 62
    0x48825010042c4c0b1101c6560401c0121074018110802e907a144111507003080381804c00e03035800b81310400315030744054400703006540d00c85481c071652801617500503569100e281c2c204d0040c04d00c0c80c01a12849602800924001700498003c10301d01a090b00c409840d20449a000e82da1003e0740f10460826410800008400106c1707548040c4030250541c40e400714101c0200c140d140b2303052102d41c00300c07400e0390366070000d01600c80100108181010350100134003540c0c0b040340f41140c6070b0242c6008a001d12220103a1406248100c101070110711440c1c0c035040003050359641074070301035203503640001c2d510b0401c4200c005003040d400b0504083c41038008030413119004d0f09900303110703098448104400040d202841080c0010303200340e0044d40030f03040513038421100f801d980c01e142da0766035207036409140f09400400542805407884505aa4003210072200c0e080002e0f0004074a9003540b03c2e03103200c7c445100d1000300224128007030003255440000c460310003042040c401c400f4503503213800030300030301c0096070140c1e0101c04c201a003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 602424379 1250 602423129 602423141
    0xf070918090b0405030403030e24090105040503150a050a02130b1b0d090518011508040809100c14011104090f0f1a1305010506160501061512150506090103 68
    0xa00d00001c0d281c040352103060b40c080742540e046509801c006402c0081c9030b400072003072400d09411a5a0a03210554404122032612103074178100000d480400c01d40303640d0303001364255001840060160390403054807141c11400c451040350350380c24036464400425018182403090f01c0d00100d0242c400f00c5510305045a40689400452042c0005050304941504260041c0841030b100e10f03564440c4201e040c00c007410400c01c04020940ca00c0038192000041010000c41001c03400c2180307007070030009003e03110f50806100c18400c002e032107500404002001000c1c964011030b4401c0e0b540c0554483c05203044000350306801e90710700b000c0c1c0340da0540080c41300b40b004440c1d907031007245040c03c03403000003681c9845812020240c0d940c010780c9101104103191600c2c11404c01c40108414080308500030051581860001071160240265080c01e03c107540e40c082007000025441230000d45a19001c600f40084c0b007a400a04180f680d244030032004d07041034221010010308495400668800800c40c9003443c40140c011002070074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 602425629 1250 602424379 602424419
    0x2d1404080307060e070b040e04050106050117040b060d060e0c0306060a033c060911010908061b0705030309161d07030b03010b1809151005450f0709 65
    0x6224000545070751b0700380040004110240510383c280c9014202242120055400241807018080c12101407481c0541044c1d8443e03400101880103450b4000400d03010820140014102854190306041c100030000d078006412400321f0841d61150b1300c1c1010320a40f0699448010300c5d04010981690f00450320f5190012106524000b07580e000c481c184485010391990302080d14655071301c84100040c800d9080c3c41c2c101000c801c1c01c1507680366141440b403a503940001012003840c0380c03400020380b240010720340c212001c0d07030f810404582d140d0500010480d143d800049e00108031800190f000a1a1030620b0b20000ea0032112004c00c210f25660460f040d0081d044000d05542d055581d9101011156102e122801e81300c407803507031400424038281003034500e001440041d141443da80c40c010003d441a00d00c08031016900241c51140803260722204010b0307124003420081b1101c80c40c200315000030711950610082c5d0800c419949060680f02c0884500e1081da007903079000d002924a01003400304050150107805152 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 602426879 1250 602425629 602425633
    0x20f060c0a020a12080604180c050114120406050f01150512060409080d0b01120618020f13080a03090f0605160c0801060b041508010e0a0c2d1404080307060e 69
    0x2003c0c0d50740324058001460b0300705002c20303c0701040c8800d904003481380c00e03200ea01000c0c501d107504100c1d841d21710068066108460402c0802d240249004484d041990280a001035201426040510301400507220460b04003500a501c0c50000804450314121294000081e40343c1928080042d003ca0300b800c040108034603089500c5000071000101d08000808180c610b02c100040da1088000c0018050b0742c180071001412404c1034001d0040e00102d0040300a0000d120381c005a5400f43c5604902013800385c42000b61240807105d074001105440032503d0152203101c0d541c1c821015441c2c41005141c0b070024001c0030009401403203074065040b040c1a10402050003144640c070340c40d40d95000702d4259007203600400030080e000f190802074811000c201101c2440c83d401c040d15258140f462104035050010300c1010721644503004132103101d000b014003400800f030441107030155010481c0701800f039164114900c0300003400b1b80c00e8081b1414501c01920151913105001d186042d000340c66840103071126030f604540798 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 602428129 1250 602426879 602426893
    0x240402030718051623070f08040b070302061303090521030a03020a0306210b0c0c01050a0207020f01030608030306121903090f14060301090c020f0111040510020f060c0a02 75
    0x541c8125001921402c90542c0800d452a10b0120000a090b1902141c01408001c940981801100303041492450b0100c50b959030703da01103800d00182a640407c40a0f200120015000c030364174040c075005040d0b00d030198084400c1c0d5260b4004450302c20341b1100001d000901c0c404028801450040d0480c02d10204060303102c2541c20111a08034115030210481d0801700380e0000b0440b08507505805808000c00c003460600e14040003070f00d001201100c4100c0010030303080b01a000241c030b038000700c4250b80800da0020000c204610f45405564000d510801090380310b41c4180f1004017041d88a0f005e00c40544814001443c115103c2400780321110b101d040385d68103075014450700c211640001e100c1402d00180240d9550740f00c1803809800250244290304110011000789007204056201d007011241100d400900000f840d4054140880c1040305943d014001c550034805200d560000e44000341064542c221800450440385240590ba0303142d40c400b01200c990000c0000402c400100b01c00390820b850103005460306 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 602429379 1250 602428129 602428139
    0x11b08180301020d15060e0103060e1303020f071e150207090e070302120a032601150e060a0e0a080c03191704030308011d04080d1509021810022404020307 68
    0x5403018502170f9080c1d903178454000c00640f43d1000c040aa044801c0c00c04010b00b0342024014070291f40000c288001014010680030304140c420440c507080f1048110030f80310201c0c1c0380c48074001540d61015040a2500741038001140394020100921071300d010f07030b0300280107a1f454042e5200152001032002e00e0a40078440002000d40c440440c00c01c0505686405010100380a143c098120460382d0f03041e81e050461021441c0348644d49003940e0b4191a407201c0c0658910320f22003421039004180c42c85503a041100455040d01c1c0710b400181c8007030207980440b011040c2c43d071104040c0d0354541c94605100e901d507001742c45103000300700a4010710010500400021410f49242d2260065507801a03004400280c640b400422140040c21107150907010a603080b00031601303058844800c40d000e00c07050207003501c0e901e181064060342c907921840c0c010941300340195100c01240c162905140c040d040d0341d5008025000ca05c2c002c5031720114291801034004203050744202408160280104002002260180f103074500100e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 602430629 1250 602429379 602429381
    0x24020408031c06080a0311160905190c0c060b040b0a06050c0601152f010e16050301020306060f070f05060c0301050f0919020a090b1206011b08180301020d 68
    0xc0c080c1000159a11280e40000d115410600c1c1d1180b40a10300d040000e20000d5008901c0207207450305840c002900840507182d06003081da080e8615224070f40380300c2c00000e41d0141900f28900c58440c0901c4003001c180080c29507000da80c4103081c0400041ea094080c0400280c1603800a0310210000d400000d94140d4140858020320290308100003256000c2403501928a0400c85540542401d0356405040c90390200050840c684c121038881004901c0c000744c407601c90f007070014070b0f030b0440011000b40704d28a207082c0815264401c4c0b0074075001741420f0520201c0c040c03c05001301ca0041038060031107403806919000c0011140c120400440700084201503020110b40d0410049001c1d001c0d02c007203255039525000400c0307500c202224006001c3c800e400104007000b00b01500c0622b101c03400160140e6200c0e07030b0030412598541c4c9030b040302011400c00f1900d1181ca0701c0c0c2c98082c902c120401e0b01c4800011403c069450f40701598203500078000325040001e1006600821400452502d025002504041d00424840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 602431879 1250 602430629 602430637
    0x2030f0a0c060c06060f2d08030409020c030c01050403050a03060b1201090c0c0507060e1201181e02030a050d09060203031501050a0c150b040b042906040f1503110f072402 75
    0x400c1c610100907d260224040740c114510b180040694501040c981401d035501e0f40501e01c680c1302c4040d030104001c102d0000500c111000002000001c02c41e6141619002d840c54200f01d03c00d40002c0d24200c400310f2030b05242d81c1110000b0402c1204446140e2130310a0510150044030111402c00885108501c00107000700944c00140c440f07500c2c0c1416022401040c007900800d119151091681841c0c0003c00703a40302d51180c8008640c006500d0401c0502a59034000300082656000b0b406204030329901090000100708400400c0680d40d91100941d03480c1c008a0383e0f80020344000b01c1d078810880e6a451503600540040c50010600d0901451010050b02c2d4000544a5906980c203110f80390420380032140b4052003002c0011800b140c08201030401450700079000030014641c44071580f071050641c1c40a0b500c1a00342e40081c0f40762242da0345080e403030f800150210a030380c00c81032012034200700309000c040500105840c1d10700641c5440c0c0c0d050644584030300d03580c0700d9405014096510030104144000c2c00c907000078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 602433129 1250 602431879 602431889
    0x7050304080615040c050301060f1805060c0604060f0603020319051005130303060801230a090b0403050408010507050304080a030b01090b1b0606121509010b090f0402030f0a0c060c06060f 82
    0x200c0700f012500007070000b561080710784130342048000c000602c0010741100d00f0300c2c28101b281c5801e40303030f404c075081104010001e1908807a911000100d5001d040d80400100e0522541c4502c0040c071465002c14003040c207440d100e01009601d500500c000350121001e00d4003d0503414000c1048440c400e9002204204807002030342c41c020300f070084003156401d268141c002c010040042c18001c0000c1c0000c0c1c0504400d2030802070507418030030380c14004142200d40b140c00801c2182d800c010007000b5030401d40f60160196001c3e12034000503500f490b00164903140203e007a00d00c80d50700300c0383c4913280011049080f0020719071030130b0700c1c0d0500013240e0020403004050b00c040c00d080c0440d1260028144041c121491800c00001c10242c480d020004002c40546c80201c2d035020394601603030200d07086031550009a409800c5030f4100c0c45d048281c802c10064512031514005016a000344c00355012071403030800380c40e1503544003039014258000711a41001002d220f86404040cad0303070060000061030740c0c9420741e49a96400507404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 602434379 1250 602433129 602433151
    0xf0706060e0105010206181b01020109120309050607020a020f0d0618030201050a150b09010806281503050f040b060a090e0c030105070903030e04090201030615020601080d1106010b070503040806 85
    0x14401545c0400c0400d4125264210401700f041f50302c4003043d5a00e0504243c0300c240c0c21a50310800250b4002d4110302c1486600000440c201003e600009000703107942c1c04155414420003001c514014004640c0c042c000c1d401030300c24020796405900b40300c0c1068010500716801e607510301d24100108043c040d00b02c45a0300c6940080f501d0708010105c3d100b5a03003450380e42c24016041d01020007841e00c01100300d6003400c000782004450b580e14240000c0103d07011440300c0d00c2c084a49011044107488c0d100500c0c0c2603400507000410480710398401203040310800c8400407031003c4542c0100c0c020030342c80500c06501c50b1000300550005501c81d22500140c0e040c00c45d600381107502c69028400c0e145420300806900c5030b46490051015441c3d500c2c001c003a14a0804014081c603600d50b019025a40309030004005010400842c40e040601c861009581d54030900c1030700240c0c0502c011610580384510740f480000d5034401c2c020702d00ea0f4241207004040d030340401400c031098881040006440e000c10300511344a503108031340c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 602435629 1250 602434379 602434381
    0xe1501030b010e090612011113061b1e0501062309010b120c0c030d0606020f0c0f0d0b060613030c0305070506030f3d1e0503030f0f0706060e 62
    0x1409944201076001c2c1800241010a03003640c407011001d41d40f04008950301c0301542c1c240ba6602d40140b60f18a51440102e4000903003440f6801c0c1c07420100b00320f505a42d1080c008910440007070128101c001b50061128500300c50304180701907210a10280d69010740c000050499a4000c511500e102207804000c10344d5402c0e9078002c0e5464110500d80c0100204a03180c3d241c200c82d4086001d40c040020407802c001840030a8419071200c08000b81e0b6070401c910b180c10050319071943c002030758032003050607a000c05100c1c0300054900c50030100d0005101c418094152441c10010f651400905440101043d41182042c40481031545c116a4070b80000e50140550f0f055460450620b03905104e403d4016601402c0c0801c1030007034904031604001e6120b100007021100c004035054800c5100101e044014541240030781d40240c0381c038007200c20700084071206200081c1410a4105645d06180c3c0d910500b07900da0802e22002c280038400b00e00070003a14405a041d41c0c0303001d440d5034030802100c810790000310003a05405c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 602436879 1250 602435629 602435671
    0x40e130201270815060108130303110703110c041109010c0318120201080703090804050418051002040f050a030503120621100f14060f0402070b0a0b0a0519030305130e 73
    0x100c4100200707501d5135666030b41e518200c1e0000e04200c402425402e80c082003507200d841030500c20b03405414403c003820410740d5a010f00d0f00f0020030f521880341c0503081c1d9009035003a107282071074584116118448004030482c240109000195900c1071240b0341a400c0c052501c402c44249044010031101920030030110310100205400010b2103007400825480a16150040d000080307410b00d015602101c404a40104941c03641181c11804580400030040251282101091100085070041e0007039885820b00030a0456036901008085078042c0320142064004001d460520401a85060380c45140540717440c0d60400314030115010040c160b0916081e68101201e4101090321034086c2d036030050400f60301848501510340e00c020600b0000344c9098440d0720200b12000385615190103580700282c01c110580501d14001c61030740003400020b02d0f4030784a040d00c100c0111380752800300c20b10681000104a10a41c40342150350558050b4414409600281e800540002c3e1640c1d2400c140c0d8031864980813504008660300f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 602438129 1250 602436879 602436883
    0x90608030a2c13090213091704050d060c0912060203060a050a0b030f180118120801260a020604140a171207021201060611060903040e1302012708 64
    0x280000c004060340c0200c04400c03102c40e00040400a80084410b0a551164030060074003d00b082e400080d004141c0f03a095445560b0345521640301c0d03e004481c40003412842d962110b0451056001c0c0076030110700c280300c420200e8825804030452891a081c9105000e864282c2c86840e04000310341283e41e01c2e00001040b00382d081000341d100c0101002e8440030240ba003080407840150000074201c0060b510201c00041d20212640240c00740b0064a0b0001c010301e41c10300344000580c2c82c3d0405d094036030a4034136404203a082e01c2440494100e542011084a00109806081d4100e82d0800d9010015110b10b007e25405a82e034500240300904031601c0050b80d6000c10340510540e020154006100c9078510444071005d00408250160190080303030f0569640e803042c0c0300103002c5e03040c0c0610000f510b600c0d2a03804161b43d6004003494400c442034030b00710395950740d0701d64001d944e0b40300358040d0189404075070b004110314403c00c2440c00d40261050610f00132503141000641c4440c0f80340c5441001400030383d1402c200f00300c02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 602439379 1250 602438129 602438147
    0x90f07030c090614010906030905120309010603030201060b190f050403020603071d010e030c13020d0204080d1b2321030a0e06010308070809031f0c080f0f0a0c0207090608030a 77
    0x925903008402d01d000c400640704c00d42612038042810346030707042d6404004082c018111304241c0114bd403900da0030003021846c028900c50100720090f600c2d01f00f0108050349808140c407600302100b01c0200050a00004c12141001265101c00500500340000301c0144d42d22005107100390b29640e500d16400c4030024221070700c8802400da0320305011282d46865203e031030100300700c4d980210541d11095501c0902c41004024402c000801c048544041400f10300c00e03101060100d88180340b945c428656802074104428070100000340201042d01c4900b004000038450750b0041070611148040d642044145c0c0381001c04a0400c42d5641e41581000007006061b140d10320541d01c40d6001000107103440d40c1141c1d5040101d01c18010040c01c216004a41200070f65000c00c81c501540c004100e015500ca460348100304041d2400c81c0f10a0042a030450000d041d19049540692044a000c080030526807100702182006028607034004045003d0703080c2c04075041d6000d028150003401841c004507541c180c80d500060010031303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 602440629 1250 602439379 602439389
    0xa060b0114070b010b0307050c07090501050a06050f040e04150509070501110d12151805191a0f01030b3106050102060a1107060908071b0b0d05090f07030c0906 70
    0x7024040c00c004a910341c3c600f0f03419a400c095490380c0c2c80d00c034900b0a40f507074080e02c640c6181600c50341c1c01c04143d075030403504994120b074001e40d100302502d6101c00c01506c00b40602d0b194800c400c40213010400ca1040c06581c1e854010340a03000b41c08005032200503000540324200c4441e20f40303510003c8200110350740884420710010080c4042c0c128800001c0004011042241c0d8a0040c1500c03040c5804900040d40ca1041c000c2c00019260180d0540e0812044083d040466440c80e84a0112281c806401d4080c041c108070b00c2c2c03280015000b45a5050b04105e01034584096203070404d5034174000d404450322200005c003190462800059800c5041700340143c80803500703004260000e400c0c01000c00159800180e42a046100940c001c100c1d410000c001d2010b6000721071000d040541460b1010042c01845801402800e0003007184442055004a0420502d8420700c1000481541080a2001240c095110f1900211202d0903600c80c170303071104000c1e0704c1e001058000780d40000e48184200107603880b40c424840145 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 602441879 1250 602440629 602440667
    0x91212070209101e080d03020a080c1309020406050405040513050a150e0d110c03010c0f111c03021201120201020706050c030912072c0c090a080a060b01 67
    0x2440084024554051a500240240456404214079070314103010040a84906043c0750440003034407441d5404406540300e562002d0090550241e81d1034401d008680319008140c80345c0700d00342c583c411640c0c66540030108090940036140e8010426404600081c402000165100c544070342c00c0c44104000c9030005402c40c01c40c000b000c0040b400003400820001ca00c1c41d0002c142c24a01607145456802030802c201404046008001c045183c041d0003204489074620b00314112040c0c00d0a12050600300c6482d1000b140204221404000099229240103c95040500151503081d80c5000c1031380c41480711350100300f010940101e240700385801802500c500411a1500c5880710103002e800107074a510b16805840c1c100080051034046140301003040307812500c809095007d18601c11900d2940790107550007000c003403018640c0c0800d04001d03504200350424800204c4203080d038542842c3c3c6020360b07002d50a500d0700641c1820340003604000c1030001da045140144004988541140f00050000710010411180d003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 602443129 1250 602441879 602441893
    0x130e0d0503091009030c060c020706260c1806070c06140304030903031206080604030e04060801020f0d020919060c02030c06040e07080702120a17060f1804060609020706020912 77
    0x200000040300a03440c90310000c0004c4881c0542011100001d04020113000c0c83c1c10005c0c1d1203195a40060b03c582101e40d555039584080f030400c82540c4003480c516203906454a0550081604451900010a54024003030018421a19118003049480d081018203072201000d480c0200a050b0304540b22036088000b0802c640d28503d007594018100301a540400b400300050308880007201492130344101e02400c000e40c111074540c034141c6401000c501d041d0303690501850402c0700005a00302c0500945a56203444a510ba0070b140b03a0103132000c000c0d04001038581e80903400f41e8460644190b00303134140000d0006075842c010001014014145000300c1c1c004003d008150401c030030005100080300310b0360050301d549070121407515030300c60480c0b5201902c00c6508420030300048102c0350b580c0140c004124102912113078002561071070108120310002044a42d0400220b21a948040c0810076102d076110788140c0300050980c0c0c075409010100d8200d80c2080790b821758001051070b190f103400090f403807a90303800e40028508 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 602444379 1250 602443129 602443141
    0x50a27020a1b0c0302060301080a021e0117040c0f0e090d0c08161a13020f03010507020c01080a02360f0604090b03011103070f0908060601020718020702130e0d0503 72
    0x41c1c00b00c800740c03035020a044844400200700003403007200d0085030028030031b54807540c460298035140c54000000324130540d02c03c0c4424045102441c04004d01800507124101860582c04a000f14458010b00c00c80b4541600880841d00b0f80003105803d0181503100c1c2540c1480c94204140b91414000c86842e005215121034000000380c002000c582c0d26801d41682190340f001341e8030740200e082040c240400100342c0142c04200719030411982d1004028000c0341e02c000304010140515080f12410760301580140c00000111140354042d2521030b03082020100e0052600c4214542c1ca2039068554080d070701d001e1079004451904a20108002c1090071040742c3c1301c4003800d0703000c0000b00d407171046104080c0510385031102004581c0c0c0039030000314680080500b40d60b480c40c2c0b494000703000c518000141d10216111890114080a001440510880060700180100c07800d242d000c0964000d01405a149190200001c10050b1910451102c0d0a4194840843e1601e40560304909015800740e0000c01c200c000c1c020082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 602445629 1250 602444379 602444387
    0x905070e010b0414010c052407091e050f01050705010c09090c05130501030b0d0605010b070c1508340201050403020f0c030307021203040e0903120606070f020910050a27020a 76
    0x441e4440c2400d01000c40c2a0303514180d41085072501c0700d1120982c8c40400020125401c4400300d10940195988024480d11a048002c00d80951100025902c515100500c914208600b000508500c141091810f00d28039503502400d6402c001410ba000440c2601c04011940c040e0184042d61182030034010305101801d500a0030000c071920071141019124042900700c0d844052500c600e80d9001f02c02801251f84400c2c20400c2c1e5030010030126144070300312a0000e42c21107200084519070b1035980c0c0e144640c2c2c94410b4518012400c7c81c8008113105a0400c02800a002060040ca400c10060f00003042c0c5240604020b414565a209440300d1900300c0e211039245503501104941c0341c10341c12079001d0150b2406c40d000501d180116001000c0400004050000c80c0c000000a4021200703252000c2c03446954201c14408a4052624020410321441d0010380051030107100c40e5600100a4460b000c0703240e9070314002604060217a0161000094001c26884e54030010741003042030b410180d000354984900550014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 602446879 1250 602445629 602445659
    0x3120b0306040f021f11120c0303040f0819030f050604050108030d020f09030610090c18030602031504051303110c0d1b0b0d020918010f05060c0c03010905070e010b04 73
    0x5201c1c81016101008545d00c401c1105160b4441180c00484110740c2c84002e008803210310100981031040003c107900c2454803500710789403103050f00b01a505644495840c10320746880c0c4031084a1480382440880303d0690415981c049080d015500484e8100c0886099411601e000d080a03004a080200520401310f00204580d840b01e008440103944442c07820541d1010700070405d4941d410301409c010301480705810781d00076058401e034103c10403d41d00540303c2076507200c141c451003104440d58203034100013203034081e8091584040e0f141401e000e000301d0400041c080b1507080780d5070b0f410640c0008190051503404120182000000c1d0001c0c20041c0c86d00d070003d070105030400401418440e002004240341761107181d101c1c00510395440e0b041c0c4c54100c402543c00c080c0d005980c24038080c1c2c0303d14500440e80c4d20b810390014129106d0000b00100c071828003050148a5010000000e680d108403a0459840e40b824030681c0200c5014002070490241040103008074188181d109511283d4248424000e0a880000b24 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 602448129 1250 602446879 602446883
    0xc0306042315131d07090203010609050f120703210c081210120f031209120807050f04080c010305010509040308070305150d1b06020f0a080d02040509011203120b030604 74
    0x410300b01444800090600b851020003a14218102094900b002550400c40c010195011003520441c41e128260407049010912802c80000e01401c801c200f642083d00c2034940341c071000342130076030350011000f055890001c1c640d2003112040c000c405500c12480034149942400c0806260400100c86240c40b9840180a0400c0004001c000000401e14140c1c2040c0ad2200419040414000040340b9090604230301c2c10020040c0e0104070b030f80800703100201e00c520894005981c05003012049103006907040380e1054005141c101402003c00c017028806c1d5161010344000c003004401003c8403883d48000500707841c010391206000300400800d110000c0e420940b40740c0e00101d18a0b0000e0716507182180000e10343e83c0406415004128500850140840c911006030703000c00a005c450384c66666424101e03910807508080c214150821400d040000f42440014410300c0c08100c00942020327150030005161010a91001e9070b1030300704103240f4007015000f00412000807102c210070428440d0f1300c40420b4440f42700500c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 602449379 1250 602448129 602448151
    0x1009060206010302040f09050f01020c150f16020106081207060f0204060c1106070b0702010e0c06030c0a110709140f0c07020a03030e12060108010b1f0f08070903020301050c03060423 80
    0x2081820304d07042c0d409000e5440c8c100c0215240c65122a200c0c2e4002d601c440007043c554003a0441410a9500a4840c0e902440740201c071403c1da42d440d40a2401d80700a0010981c0440d500c0b0800090b102c2e5007040001d020714805429180d8444440c40c04d401111031241140740401d0041c00100f20300b0350001c0101d03d0f00c42c1c11a0300601600c4503640016810f12448400038056400300c024054050340c154064003800002c2000c403207070142c003901044058001100e626040c0181080f0b45610b003403188043c000600c00c1403041f030b072503035841d0b051180541e1480c400b02e0003422980c00c10000038201c1c4440c00b0b504030f603048034480e1a09030540c001c5604102240009800e00c40340c0402120903407070b4402211051a148400e941c047d5845e118043d0207840c0700381469104180d0150120401220b1142070b0000d204283c44060070180000c0040c3c42c0c1001c0145820180a00301c1c0380003025880030b0244038407a02c10451603070340e2480e00d00100400c44640300000c0070500107540030b10100c00410820103400444c42c401c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 602450629 1250 602449379 602449391
    0x108151305120d091b03110f0d050a12022b0f0203090909030d0c050306030601030b06150c070f090b0a05010e0f130621110f040f140105100906020601030204 69
    0x20710514004400c0015008000001a6525140c59075403210f400c0b6446510340080340e51408007400200c0304240800b42200c4400f1584015610b0001c0741c1360807800300a07007044862035043c0c03100d90921202d0903043c0c1c0c5c0040380d8008900306caa41405090b20124442e41d4002c0d41404440d603001618400008440038000c182400d8070120b4000c2069030741d0400300030f22400040c0340c070206050312600108141e0143d28180b2402c112142c1c0100c041e00c1c8555406001090070340c0c65522400410b520180100303030007800300ba15801a02001000030070351130020b40001c1c504140f920f011203800001c40c2e400340314042c1c07811400d012036030350340d1141c00c0441d0002d20f880628240e0200004100d021220721642d4001c0300d1100e801040750701074010500303ca50080384056848040e840040c125500548003c181d5059510b00f03401918000c074162031102c1020f84005403041d030340756402c41141d0084100c0380c20704200c440100141c0c649040701401c201658503000380b585140102c0a55a800d0601000340b0580d1291 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 602451879 1250 602450629 602450633
    0x110d1e060b03010207051606170c13080d050909010e04030203180310140f0105010306050307030807030509100c020a0b0408211201061805030c01140d1d100501081513 73
    0x5048441c190000400841d0f40c1d98092401d65500c100b9603603100d6003072228000008110f03005051303140408030f00c865001503d83d41c0c0281c424180d4071541207101000018080400d040800300f000442c030702e44a4594a030303101c03484010004110016886481900040740030480040d90100a5440c49130003865044604802e440c001f9040440540d80e07920164030386210440c0c1d0028819009015900340c0400c3e1100da40c0710030044056500c540180d94050344806400c00000d940c1c40d000780051030281c0343c00c5081c4031401c400107c1e00100800381c200019406400c17142549800300c6031200030000c90540e04d2400c1e00d000c5000340c89407020f80c01c540d004035590188404401d050310031684240307655003807074941c0e60311500058220000c40f10303a40c0c0c442d0299400403c4034200043ca0b0400301d0030503101d0b01a0f001c03120f840100144e2003080c0900087e07807200b09465040070140e8414074215180000780411070b6840072080c04844050340500c0d2a5401142d205a4001001c079170349400c80c0903400e40250280440c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 602453129 1250 602451879 602451881
    0x120a0f0b1305090c060a030614100212070326010602010b030604150e1002070506010602060a0e06011505120702030c011104050a050105091503100609060c110424080604110d1e06 78
    0x308804176044600000e040106913403503842007040d510701c07c0303121000d014043c0500148076002c1c42490301591000d249440b80f25148805002c8080c864607100c4140031000003d214200341d140c0d05803003420309180043c0b007019028001c03001c401c08180c005203100d10702a169030480d401580030f00d8540f569510f40c01d450b18001804000094a02103200355502c07001c0d841c005a50380030900c80d1301f0060140301e021541b42c146a0080c0c0c1e14154400c4018400341c0d0802d2030800c00d601c3c00108000030f000041202062242805045620540712a0051611503481080341c07070a403001091440305803002040140556075941d01c035803040d14170a2030256152420840490144008206000d18540002c403c10600311210b4203140c054500540da000320155036200d00f40c6003401c12040c001d05505184d80541b14a08040d485125041c68010485004406a9a07000c1c0d101030260000c05407504000d007004107110700000c5407007130380f0410b032400320310108280c441c101c5102950040c0007080000749282d109100c0c0e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 602454379 1250 602453129 602453143
    0x1306020d02041d0114090702032203061d010c0e0307090c02010e06040f051002030903030711071e0504150803030f0c131503050108030a020307060b030a0602120a0f0b130509 76
    0x289528802c00140f0300740d00078642c034109214038030f07040540710348915050400c162000c0c0110003540085017003202e42c2c01404848510010415082e998120000001c03075210f0007408c49803045002c5140a00804980d80c500750303810180402d0a00000d8400201c150314000381000403540000000503a003003c046040740034003d1040000418459030080c00180324802140b8095188078008a0780b500c2c0c80041c80c94140e00048820ba001c5030407e00000d0341d40c9001d118000c86242c88207060b01c030041d8407150441840250349104401c1c0003072800003030115042620480302a1071185880741885841d02d0245540ca02c4024245144411020049404a50350030305403440002810074010610b52222000308040c41b0170503e0000007800e0200020b110803010040320100a1554083c41c6044c0c026140c01e4050f000444c0c4140d090b00c215a12580480e4951020381500340b18444841c030b45060540004094071815540000072900e4400880d87c1035403130407021400185080c101007020355030010114180b42d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 602455629 1250 602454379 602454389
    0x1030b03070e0c04060206010e220f0b010602032a0309010507030908030d020a022514011103030c07120f050306041e0c0e01030f060806010b030c0d0c0509090604051306020d0204 78
    0x141c454203100f012060003000c3c100b03072031507035089070156a0ba03044045003600301668007840050140038400034a09820762610445030003040244031109080e500e201d8080c800340e02110044e0004250903039001007042c10400450b825030b403460900c2100b0011180c40f48079071030000307041c02000141d180c1010700800340c1c24001d00250090700c6d241c044040d000741c007030742c4034491100c0140207541081841a00c06003220b44001c108034010403031503080c012015030070300002c00301905104058900340d0241e0410001144100000d2402c5500c45006251041c85010b60021417418841090790918400d03501c0000c1d0381d03014030200d60100b07409000c000290104244554200022800c068400c80da041d00140005207109080c0d13010011040c00c1010441120514001c01d440398015030010000390700c7e020065900600ca5088561070909001824400c075080c1e400f86001140c40030880840c0b51400e00b10560f4480e10981c0c0a1000c0c0c50907810303102e80c004110750700500031540450600a144d0556042d02c012701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 602456879 1250 602455629 602455649
    0x17010e18070608011d04050c060f091f020c01050a0806010f0c0618030813080906090604050d24060b0933070209060a0e1305010915051f1401030b0307 66
    0x545425000744504030074003c07540c41500b0303052030000c10b205c0b41031828452900140070381201501030301002001d60220003800d50401c4203001c403000a55a118801408040c04038894411041814000c0e082c0794200130307440d05000051010080d0b86130002d01c0c040c0d2100092030085001003148502361010300840700f0191083d480e12107028540c0c0030150012842900039110341d40c860741d401440c160b01500054000700b00c10400d00111a09080643c00b41120303010003005241801d0703c031300200303502804010f010340c0c00781d400c0c1c00413500328603001008950907400c2a1003445118141102d0108611440c10b03c54050300007103c0a1180821440310a012841e10040c440f0140c44020024515a04261400d83c81441e86002060716032601d00c4640f400c40f0050034040f40559102600125101004c8806551954a4050210000b42d5049030249120000e0400080b60305042c458001088200210081900880042444080c503500c803c03442410702460b0100b6000140b9010904000140c2d019074954 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 602458129 1250 602456879 602456893
    0xe04170f0a0e03030910030f020403060504120e01020303010e1602070305030a0309150902030706140d11030702010e01330f080304080d0305010e0a051e240117010e18 73
    0x1103440320008000d900c5080c0e41c1c0d800004600020940c5910801001503070004510702d14064107402a00018488400c0c0134005040681d03035207542d401d560040b80c0890301815600721254a80ba00940b01020443c802e02c0103504541c109070008855030400b4001c5407000030000c0c00050203610810040000d15407080680303480d10320f4000f024001e400f82503001c4900e02c80c000c14102800390103101c0c48094540040c01007140c2c0f85011400d440703081d8510003001c0c0f0b0101c108401440b11174035004402c04c8100c0c55481943c0c03071500500007800c4501005580d4001e0341401c000b403032540400c4810802c040c070000f41d05441084113401200c503281e240d6208054082c840d0800090010003c0042d0084400c40420b54240b141004c0048045030024015907030702c00796030400324480141176481140c1c000c0d202400f03240a072081c4551131070b00e5407084030f506002c601c07080c01c042e18803a0614aa030152b02c0007824210510b600c040e058420307900c814024401e000b016140007031414001158810001c81c107000030f40ea44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 602459379 1250 602458129 602458147
    0x30203060708061c061a0303071119030c030c03021c0b04020120151e0702061f09090606150f17040203070b04030807111e09060103060f080a05010f0902030303010e0417 74
    0x94424007215032131401104107901d546e403c003c001c0b038a585a002c04d0200391084902c042042e01c00c1c0f03120200c000c601c4411b5001c00003820b9401030310040c0d80903446401e409072039441001607111640e40210400d00039002e0801c00030f42c0301e80503950013980c2424111070b202041508441da410124250700c80b40d11461b015460260001c2200c0fa000c1e240003030701d106c1d80108078040030403070100c180c491100581c05040020340d0b040102d00c4884d00c84011141e2089680d0307541005000780c820b0b140301a95410303503940c2c0030070048a203030030350700c960310b10600382181d400d900307010003404014001101203e41d01c103150005003150784c1406420040c3c0004d4281c5525681c0fa400e0488070350b040703800110384500402c0d0410b01706107070414181000c0300d65800b059004142e003005115a41c0c0c4054a1241455101c1d0004103821f0203040c40b50028100c0c90f0020030816005082c02803c3d1a403404101000d185800a05030250300c0c00700c101d80c15140501000c00013925140f034030000c00e48400c0b080e0480c009000c140025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 602460629 1250 602459379 602459381
    0x3110a030e0c060310030f02180f101e03060e0102090442090e0c040e0a06110301050901030803130602070b18370f0c1a0301030203060708061c06 64
    0x805000a041102c451203109410f000c0e1610040c0c0b2404108410003c04000003510186400c20452024020b8160480c07400c0f0540c019450607615044c24640321810060081c2c07440118100803d180c225203040020009840302c9158910b010180819031208031100e2901d0007501120b0a0b64009001041900c160044031a1465880548201400c90141030015840546105505190040c1960340407591400848000418034034141030f640e400703440f11410030f90b621031003080c40e420840301c050a40300110745068011189a03040c4181c44480c180300520140d04d620080905407a40603503040d689440c4da001003480c801031500c004220302c0c00001c0d10f5007000401803900b4050031090000d082e40d5421402006e1310707a860003840d441005500302c0c101009020703411200707800340005c0321401c14500c01ca485840d044541040159001030340030104100020340e100f03502003000da040178601c2c2594116400644c60305030291005d0304000c0200f0116845030b5407591852042c16441080f6141d000f29894104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 602461879 1250 602460629 602460641
    0x90609080a02011e060608180a06090302030429090f031005190b0306070c0602160215040602060c13090507050d05280207020d0b131b050901050619030b0103110a03 72
    0x1c1e180c5000445010200c0c0210300a9900b07a548985442c101c990303c01c03001180c0488e00c2c811480652064146603008540e0030312841480500030340c040e65540382082c0d94a41c1c0e428041d030005500007041c0d11915001c42002040d900c1ca01d80841d0305240001c10100042d1401e000e442402c41300c20f107404140034441042d11821a42400e208009000040701c03175003010348520044511701d001c200c2102c0b182e000285203500030501d201d800c42040030b5071001600801e5003149141010107099200103028080356804010490b0701c03032131079841c040c60044283c203a1049407a96104a2580549580106e007030a4040e20540350b010094000c100204e10382645550000200c8000c608102210b0315400801068075001701c8001a80251040051604982d5180d030301c00d03401444040c040c21440d1400c0b00082000b070390809198400c020080d102401c207410000381a406030700c00ea00c1003400300507504607074082d00902d103c4070040b814001091100800180e000e851040340400c0d0158001400720002d0360964008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 602463129 1250 602461879 602461901
    0x16170f011505090f040e0102040f090b0a05030c0112020c031608120a290a030501090b011a1c020a03062c0a020301030209190b030d031a180a090609080a0201 69
    0x5800710481850103680342d1240d0303c080750300400807141e40103d81c00d041e00841c185d02c4549000600c0c01d40e440003116507040458200e404c8040d25020140400d14040d1045009440c0440150506410101c000703040d4820165050100c01d030003260726030091900b0301c255915901c00520b248000500b0786817086003988030100d0011007820680c08a90044038910a02e00010300b02d411005034901564590500003013000d1140f503114505000100005000307008000d0000e104140c181c285504100000040d5901c888203004201e109124a0b03c103003800308450354001050304401a41d80241003c12030140c0342d40d40028a0500d014041d00168610403951141012408822004142c80302448c0601ba40300038800030b54032141817070201d558905d03001d04111800c0022000014940f6601010900f0044d10300c0658000c81c1d51685550a0a1804074106800306c0703044950040842c903000c1c1c103ca00241c0544a900503660b0340c08844100301c4a075000072003040d00f00c000c1d96281d290313012009010304040114 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 602464379 1250 602463129 602463149
    0xc090411030a0326060303030106050c0a080724020c12090301092301060504050103021f02031608120c09010c110f04150f0815070c0206091903110a0e16170f01 70
    0x1300c007404c1500040107070003404020003640c0b070f6903e044011666504006200350041c000c2c4c040e12000554050000d00c45a8414020704071404001702002045c0643e4140c0b4021a500402840c000c080000ca131065040c084d40d15100d80744c01300600400e00600120310010011500c5485903e076004d40140103100140400e0300038014a618ad1003800f096030020f01c1300a410000403440e000618400002009100e4074030710442e070410056500000c3c012151030400d0368a02c00c009000030141c0c0c0d48540e2994032911940150f8503141800000802c0c2c4400b02a0280078558113107880d20003070751004000550364000800c03d00c50482c2091003189072184070302c100884940b2048001600b81e102151850110300070121000041d500c803d02034500750500f4a0032a40000c0030003c40c440c550391000c00616236862960504003850851810804424060180901c100b1b0610420040781300c1c40d440c082c0d071104030a400d4001c1d103d41c940f400c1d0b1700707044804003c0d402620703443e0400000da287c55075054101d4000740e403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 602465629 1250 602464379 602464427
    0x10504060803070b0a18030509030d17190b03010212060306130f1b0902040e0a11040f1712040e090601301a190b060c0c090411030a03 59
    0x410041151040d2040c00115003080c00004003041c3c0d000002c0740c0c8500c4154010401c0340745141c000207440030001c0100c0114902052000c100c1c2410410142014840d042c00c041904407800d0708170311408001c0c80c0014956400e40c22420740003d642043c016880d024000399110444060141003020341112a58024455100010680a1041401106c0326005542c10320681d00544401e85030601c0c1c9050044100303040d036400941680a80300a01c010414031080304a80d00b859501001954030881240780f0361402803000340228100c00f110803040301c00d203402941140c1c3c560000541000740e103400500c1942400308000451902c03840c5051320030614034064542d140c1e250401c410501c1500381c1700700c0c4500490306e00072024042181110752014001c20f0041c04940042c44041c0031580f00300c0e421820100142c1c401c510034481ca01901c0b44130003080381e50394240101881c1c0f6995903100405128401c402070f1002c43c0601144d050001d021420180c10303a0b056402504020740b0110480c0014164108222 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 602466879 1250 602465629 602465639
    0x608010b0a0608240d060c02011407090b0c0a0206030406020405090c0703020c0f010c0f2409020d06110412050105011409070806060a05041e0501020f0303090304061206050315060901 80
    0x41001c1c1c095454940f0303200b586486012078001e5088989420328103680c070b4071415128661700c0600e0043d2403881030b00040b62030fa0017050020700b5606000490200314130540207220340180c00c01040c1d03007a1201070041544555060318040e02d040d02c0303d18087d4221800009000c188031044d0001e0040d1001074450300301c42c0c0c45030007081c0310b14850b12034042d00680000d12094600d143c84000744004680515100340186003544418190400d44902203038000c1030150303401078206200005a014040e458030800840310250040b81f02c07212170b0007008140f155211b103192903808140d802e41d4060250300010340c1c446040761414500074a420300403200ca89508128201c07007450030444851060a603950381c4a0941c655609028803034010201c04814040103210100721040300c80ca100400c4000e00319141c2a9078580000682811003148040d0b606800800820004100c008115000c039809850032450350329828042d40f00415603074010940c1401050140204810805002802048115404001c5990b40e0b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 602468129 1250 602466879 602466889
    0x3250b100f0e0612240702030f040e06010201090f05070305060c09130518012d060605180f04020412020a05030d02070504092604030512091507060f0606030608010b 72
    0x60700c6207022181064800707001100a60342c075580c2000000d400003890ba0b1015840c1810807641a0002620038904594203001d000c420f8003c503007105050010310703d01032102d40e04440b28429402000c0038083d8a80c081902a4400d50040250580103003c0e003014044038030b08507841c0d201c2c80c8416101d1b8400e640100311b211090a084400006c4000c202c00c082d9007002a60344082d0100411480d09581c060300e4100301004280620f2010100122281a048801d0098140f2602c9a14030700c40b190303481c1110503c04290003404441441c00400140c01802c1c0a900004200604c2c140310103411900118002030461902c0c19040d128500c00c442c1e0811a6803910f0515a40d03004206110780141e20500b0200805d080561003940100d000c0c0c00b400d0040a2070206a8000c40361111003200c007814001001c1003030210130300c0f1001c01101c4502c94580382c844841b0014405c40c0107800300d80d10b22640040d4210030882c0300c3c0e108003804040f0038000d004140c3d0f5060701900401e468400e07480036508201800010f8941 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 602469379 1250 602468129 602468161
    0xf02060c04061e030b12160e060f1c020d0b090c010e03030d180b070504030b1012110402120f06100216060c02120f0d090603141803250b 60
    0x510b43d00c0c02e9140ca001c2080c1551840210300980901d5514102900d541d12190381ca040140f0708400140303540c98140f081e030100d044290340700f40004e0407000180162607640750201080b68030216124007980c5200c55018692403400d0074000e40c0305400318040420013626184131b03840f4029600030341c0c0d1040c0840c001929403080130941d1a51603081000710600c00704490340580c11a00780d00780e008484200c01da5560205a03c16a0901d0200e00d010400700204030010034000d034030488a12481451626010680e028061034910091001411106020003502c8582c190380f4031307481c1c1240358070090924204c100114801035820740c1c0600c900791895005a0300024100b60b010341d102c07608042c094900102280c540b04201000c07603221106407283d24411800300082000112010050680c00b00a20409400c0001d1503101d0010b141c01c0c14600c1c2e000781401921203038059280f0490307a0342090325015281c114420a0b10001d0741170107038540c0b045ea00b000607048a2119114000328221902c0b041054400501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 602470629 1250 602469379 602469389
    0x110f1206041431050f100510180c0e100306050f01020318060309030f0d021206150904050a060906082a100302090d0b070302070512090102100b0a0e070f02060c04 71
    0x100841c006908460540c007285000f20008040c0b00e9144515502c5a080c03455403001c002882d4007121802002d8030640c481c0343d0b0840c660224603120b03603280c000d0400001c148004c0c500302c415503400e902400f441c00b5107245d0345440e0004112141c0c00c507108002074001c098600400b405080c50104010855000008480510100b028195078101d803c00411034141d000a140c6101c034001407151202c10408003018208031440e900e80541c0310381550040d0258540c0050800f8402c00c0345850304d075070014404007228a800c800b0742e0045495030f500410360f8003901e2030760b102c415850320344540003800c0040850020702d4125044a80280c580049040805c019040c5007042d511000003002451b00c81d00a50080100c0f0b032000d0160a0320024a846241c05a9000ca0340180442d40008040080020510600c61a04088142103007003a442e040000e40c3d40e40501d8900b1480e41d5a412031030426958206800020682d0000c00442071410420003800c49200e0021a809445801d002c0b8034442418003c1d41c094031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 602471879 1250 602470629 602470651
    0x70c0608060f0415091401081006050607020409060902030706030b0102240f0718060915020a08041205070308040b130f0b09062b0605030d0918110f12060414 69
    0x7035828001c0000a14590a01e982c600041c4400001c00d51021b0017000140403011030300c100a50701d804079050810f4404260540d1652a0400c00c0c080382d6200001e8031142c81c1c064900007401400b84c0350000c000c12682e1000303075062058210002e100c0d0740c183c02c070000001c420303400e80c0d0b11116101d65040104410130484510310084000040c80702c3c00080c0c0890b400a01454140c8070941c038a01d00000c203000d5034100e140005d4010200b440800400d046281c0346449620007030405c400d05458103a00b81c007446c05441141c0c484400d110742444000c00c9403078051074100810790741e80d42e91051f9a0074141d010303003204411005403c00009030071002c0c6941400329800008a50703e07040c145000c01c03400790f00c404400b010745902e440200160080c00490340300443e840c100005092420721007014504550a0600410851425010302014215480a9541080d103410214103109500d15124160141c41220560000d0125041c135001070083d415501400040e54204007070b4030b9041d82540c080f2001c03500ca0441c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 602473129 1250 602471879 602471899
    0x927020d080702031f140903132102090901050a05010503060c070f06020d140105040f0e0c0d110904150f0605010e0d110604030510050c04150c022103070c060806 71
    0x4180420300400d410b600c014203030358160310317541e2034110318030307210400140c840707a40300c904100403004200c0c40703908040410010750506201c4c03006051500302601650348150030000340703020303c07444450201e8070b803c2d4000d000170003620740440d4083c000e00d0103c034031503940b03400d200c00018141008545203004046811500d45841c00d02d03102c04045d0300a40d5811540140c1c200070240c040b0000b0f101d054681c809407400090b19514290411066480c10341c9034100d0b4a103009080c005080000402c249802000d47d02002c40e003160b41080c0902141440301e554000c2054002c200801404000621242415103010445050480c1c0c40408440807802404d000c90b480f1210f002452400c11000d8110910030459802c01150b050701003412500a680211256440040c252882020703170301400782d010307148400b501e043c135142c41c0710703c5404940a1051010f101d81c800bc214150b4035420280402020a00c2403104030984080303000380e481e1701c0907505907001307012074802281051180142e580190f000a040c4084 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 602474379 1250 602473129 602473133
    0x31e1207051b0112020a0e04110306011d03010e011536150302100c1a060904030804050c0405040f0b070f1409010c051902011706030304031106070c0927020d 69
    0x891480741030303040c0f005180b611001c44d00c182c0003c0019810b1680e0300944501c100041c002580c1c3e489102400c80d00d002c1c8100119030b6030228098501d01885084007941d40682c1c030209004104070282400c8550038000000c0c11b07400c01020660450703901400c1744644160304100d03c080202080c8400d0150440340b0600c0e6400074454000703030910500c0c031107106000b5603613900040c0d4101005c429100410303804c02000c014001203d6040c01c404029655061091810400180a01000074402018800801c003c138082c000200210300e200a000740c01000a420f01b8104060008146101207800c11030010000b4040ca1188034454038000c01a04d581c460262400703000c00c150307082030100504100e00c0005080101d48100704003504240444403450044505000042141080b000c8410241c2482000e200058078000111012a5000f4800d26060a01a00019480c2c811001d001d07188003640c03800420170410380d50024640801c0d80096005060415502001c024849400a5448800300b003003000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 602475629 1250 602474379 602474413
    0x2101d01050903010e0105240607050d0f0c12020616020f0607050d1503060e060108060903070602031b0a080a0501170c190f0e0103050601060302030c090d030905031e120705 76
    0x1a00b08001000440c0b42541d511642d42102d078200c1d49049102c80fa9918202061040000c04000c0c03c01a00c01502d806450f44602d80e813002440900300410003c0340200c41c2151040a005000c140d120403a005484007081009594420654500c6040007025142200342400092240744201b6014017515403540c03400025500d54219104004021b5141c100030034490909502e103401451003034500040450040400c0751428a05800c4010164403403030500c5203e0070000142c5020660001c40942c0d42d55401d114410030081c21414940e1a10000c40c84c4406035800001c440d2183ca083c5000f04407d03a600c180d050b641a80c40424002c1c40c0d040a003090070300d810b0540703105a158810705580404190b550380381c484900c0150b41302d80358101200c1f00610800509111985c010107480c80c0a504504007003d0f41006486600c40f400c1c0720300a074190100405011740c04080040c10001d05541034030a58070250540040201c00d40c0c0418020410500800c03444582514041c58201c4020003455102d910050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 602476879 1250 602475629 602475637
    0xc0b04080d091d0709080f0307051204060527060304030f032f030a0b0603280b0112150b0f0405040b1203040e07111902010e0d02310608070302101d0105 67
    0x341000400c80020506e05c41c20400040c103130041a0082d030380d81c525402c00d00e0504940710b0b221801050300300410001d903644203040c3c0b07480150781000b01071941d0b0310607694007500a80c90402508960003200304402d00d5000100001d4500898605002040907201c074110a4480c0168807000e66403060382c0444410b1010000d598814580100040c0710200e041c002080d0b60011100c800780d070042c201c0090b01300d211401c5040500c188041042c400001c220002a0002ca6121950300c191070f0740d009540b4240010304211401800300020456440c440c19041100c00e52090140d075000358200511580b040c00d054084403501e18468000c0e506040c20702114a00644015001c1da04122100154039680881800415641c880200241c16440264400500001c10b0003001912075030204c601000580c9510f24804001002a85000403811903460039480140d402200840254074106000c154144000b40840650340220b61002110381c0c031260032241c003170a541c01003640b6030090303140e51900e50190740a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 602478129 1250 602476879 602476891
    0x902040515031e2503290615120a06090b0306010e04060b0a08031204210c060203060a0e0408031e0907140a03022701140f1009030c0b04080d091d 64
    0x1590410101308040034042c0b00030300c0003501c80c01c48100100100080800c8040d01d080b24810140c940701d03040b0a10f4840f8000040070f0501440e4400740846000410004959440e8025400c1c00c0f0f0034205405004000c04aa000d0269210b02d40300e2006007614000a481d41251411038401c0e07401c0e69141d407180003404912140325088282e160300400c91550600c0544496010103014904138a018108000b420100807108070a0003400e821a4000c5a88108900c1480d90412400f40e56901c9800c0840c440030308c00d6000c1ca401401c010103110800911500450003001d40901f075a1018604151034400c82030706072440e00403a408880100300c0d0707c171500c1c828125040d000b0032074000300b5a25008580e4a64886120b0400d5008a800c0700101581e140101030141c880e000340b40000d40300030b9010601403c0e03405141407044c10a0b01441748058481c00c4140007565208034401030b5590703203803840034103a08580202034a9006581c40d401c1c01c43d02c20100c10048800c13900801c513801ca0200303a10b2407902009400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 602479379 1250 602478129 602478133
    0x4060b070f140f01090201080a0603050c010f0905030f0106141503011404110d02131a0d18060e03040e060603271c09030c05060a09060807020102090d060902040515031e 74
    0x510361221105000000c00f08400000124038030503039200051001c1c0380241844041840c10351b0620216000003000c004a11083c2808030080c0601201600d840202d0b61202d40d162040923001c040d1060706400c0034041303580141c1d01400c906407050810041e030402c0340d526501c113041440104201004c2c2504003002d0a0040d1000a680350b1032500e14450b0b41c41419031250860b00010200c00d1400900652401441107110308500c0942c503030401181c81c410200d40080e4540c4454811403c4004015001149940904100a4804080c800c42e80703a0700701e480791025084400c4000381c410b08111381100d104240d01419403007019036070440c80b81e000c0810fa0301c480c40c1c0e1048071450904907025000b140d03400758180d16a00001d07843c61030128072520440c3c0249004100500001c49001c0d0005203110640c1e03440e0405c41101c0c0d4900e501280280150050030307920501c45007806052005682c422071099000352820310440d80d13103150380c1c40102d000d420540c0d0140c0c010400502d0341070001d554140c0700303880340d01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 602480629 1250 602479379 602479403
    0x2102031b0705010f2a0803090f01140a020d06080a1a01092703021006080105180f0c2806050a080705162904050c030d0f020c1302040915031104060b070f 67
    0x8000c1580c5c841d026007113588840020512148500401900c0102c40161000f0b01c2049900903c1c200074500103402e41040c00e4000c90b40401c0c0807c03a8000001408441d0101c3c2c00880700c1d4142220701034401180380a41c03000520011404a00600414812500814400b607444110500d851050b400007442981180605018000303a4000360207480000d0003080000b090f44d040502101080800c0d15001281c540e1100d2460420b80a01140c1c4141300c06044404072803107001c80801120000130281850080301d01c0c0322020541d10f030084050104141c05a5808549546840c000d4030741e032140000c0310040e5000e074085980002d40c40c604c0c1039038400080806660200f010240c8115000b42030f01c00b100c4c550024403814038107050810000714655820701d00b2250801c00c0d40c00203501c0e9840060602d00a13a40702a50f0021100f054040310700078180c0100420400d0141c10744030000d6070740bd00040f211070116400c12a620b01d041c1c02524183c4d44041c0c0410f04c0c2c6281d90f9207a1094000b40c0001b1552002d03c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 602481879 1250 602480629 602480687
    0xa080d0f020a0c0606050604050d0f1e0b0403020c010c20150a02030408012f090303130303020607020606090106022d06130b0c070b0f042102031b0705010f 68
    0x70026007440d0b82e9503115a510b0020500e4940b0035169aa00030390b000314014002080607640f4aa0940f502d942c1200076000720200030f0400690100541155203842904515142c003045078803883c00784510f0095082d200c58620720390044070141e11f001800303842c801e0703505107043c0c100010619101003e500204888600c0c400700782e00403940d0f01300e00c4122000d600042030410603280c00f809083c1d01400c0448200000e43c1030400b4071051790020a00381e010416022070340790390360b44040044038444411a8050681c459403840c0080d60f8240440d10480140640701c0401c0840c00c004090034103131801c5801801814440d0145204443d02c4514503203800b211900281030114000c1c07007400e00840000b146100180880d06000041074000f030504400b22600f005000f022480f99100a50000440b0058a60301c0e00d07507007071080c500040a040b0b01e000034501c01024815540000040110135003650440c0e081c030303440040c07035031322911144151808600310040310420300b403140d441d0008105070984410441c01c009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 602483129 1250 602481879 602481881
    0x1181508060903070308060405160f050d02180f0f01020c190f0603051f081b06070b0901020301051801030f020f060d181a10090213030b130b01050d050a080d0f 70
    0x107440c00b00c016040050b1207410316074056140b940c401803d890038001d500f401c403a03041003040c90031000c10811441020f0501414890130031035404010303c01c030941d299110844602081c880f5080c4442c480c0695100c0d00c4c0c69410084120181480160040c0c001c1c0d12040040c402440310114485122601542004c07030145000d42944003d050f20380c0e00002c40d4640480101011140f10b10700b096844075a040400c98948009125442c000d030034100000c413030706520082001e070301a031080200ac030080d4000b000080781d0158041d40c103d4030b04440e001240545180700b205120020301010f00350715170007041c00015090030034008640c84005440d861070a034000e07145504603002a885214402418034401c800d0160703140c004400c00c070210070072401a0624605003019a0b0307040c0310b840006600854203c00340d801d000c00c108015500700b14007010b203203090040881d003152000c504407140800c48001098a0601e038141035081030340040213010008180c5c8a20550381c2046a41641c4261203104250712510030b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 602484379 1250 602483129 602483131
    0x1009050a05071b08040312030f020d0b0306131a07020c030d020a0b1b0d11040503030408061807030c140316080a0506180a061112190b06030118150806 66
    0x342203002545080c1050010f146100c10400548184000518140030440b21800c44040701d0307100c10503509002c4407060690103001c80c8441080441d00c00b1071840f006180340d03000400a5032041b4203880c681e50f1240f04052a907170030704030043c0903061442580d0242692203800300703130445100d0048a004240312000070786030a1a4022080c0141c020041d1003040106c1d84013610303000900e070056400c8c196000310041816024015141240d9034a4118070364121004004036001b400c4040c05590392144c031448003d0780c4034021340d014a025910a880d4409540d0007040c2c05060702d41c17011151058038a0260010369040c40c41300000d07031601170040c40b0750700c001601d0095002481010003074545183d40b800c0442c201400108016034016800d45441740c0010082000900c0c198443c038005221074140c18403801c10700401c0c6101000302c405e0410322500e82d0740003042c901600c60001041c0407501160f01404407500081c1726038201c01d0b02e003280300040072015411814011041c540b040c0d075003a0380d5070700c41450080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 602485629 1250 602484379 602484391
    0xb04061b08190f08040b0621121206040c0c1212150510080702060c160b0f060a080102070b07140706061509080a08030103020103021c092306041109100905 68
    0x1c0c50321024a0301c40d0000041070f40042c1c2030505001d1443c107034840250504004000300e11580c02c010440301048104003124152a0028044980c203100302d080c40c0105521051070003c054000e10000b40441c82c1601510315015181e07074401c800005c1e00c0d51b03001000d641412040e0144642c444521502c0180ba105440c204580f1040c1c81640700d03d0507052200c4c0d44041000e040800c5a88020804034030340008240c0e400031460003d0a0380c03403200301603101034009014801000078200350f0501803850403902509009410448101060a40c0d07400d11394200d00c2240c9005141400420010b50010b00580e01d84001c4565141c8007460801e413540d9610490380540c0100d000c43d06203012052041c1d510a004202902e41d580c01014500d2882d1038042281c04140700090406400003000a0030120951511606043c3e1907414403500c00b07241740081032204c12100003143d0700070b840b20301c02c4440400680b650082d50440c1c00e0341d40d884041e5040c40000200100f08100500001c400021102803034400d45100307507 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 602486879 1250 602485629 602485657
    0x32411090a05010e240f04080604020901150f05030402010e130504060b030708071401032c120414040c0e030d05180612070c06090b07020a120203040b04061b08 70
    0x90308004100540c07509820060402c9204e0320520041e0302c1c0c68511a0210078540c01003c035600094407650b02a202d00301d4004804207001c2800036030b0000003d0114062392003102c00d0003a9a882c0c1c59403082100012041d40001190a078000400170b002c0c2c0700440e0040d006152940c11882210003080b0310703c1061a09030201580d40c01003009011440c403840751803890490203010414a811456665040c00740101540c0d20451801035981d6800382d40001104071700c00422501e03441d1b4500050240000100c091081d90040b00442c0350804440da0844082d103002d40701a20341c500c40e0106000c018190007003132a0910806c5c401c0400b6641c1e040101c46a14200d55485c10740e01c00300b0050032a00106c482d0510360041200380000e1000c00c1c1c91060003a4000114603000002246c141856005000d003c080a00180b80d01c0090001c00d40c2c0c04621503c1d6103000340241000c030440c064049030341e40b103940700b0380400400c14402031050601c2019800341803d02e19001212a0409840e000003a038040b4030396190301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 602488129 1250 602486879 602486887
    0xa030522150f020c1b040b0a06050309060709050108040803090a1b1404060302030d08150952050d021908010605030c030c03070201090b0403020f0106050d0c032411 72
    0x104007070340a140c421500e0b81d0402e42c202000c0801907662240c0b12a880d4004050540682c0300c26191030b40003000c2c07064000c01c0401a5a99141c018009610944891305140500800644031600545130107084407010380d5005400da0700c0d52500e0009400c003802046190003220030880100c0c1217195442000800b2021818100c1d290486524000009660840c0144e040060400c0907903004034036000b424425080c240c00c0c555a0b40c40ca00c0041d0b500340c115651040344101801300f0300180100b540b40c10003450705010160309114441d4480d5009944401d000510414545a14404100403151034654103040c0241009001c0d8065000d9030407590394220701e910700c0c82507114000d5102c052240103244904116103181492070200c0b81610005156840e100400401300e4000d6201f544003110b0316420005494940c1041d1134000c1d19103031944c5245e4601e608003171002c00c0c0d0740303030513580842429030050f182040d9500d940e813000d490fa400d0401d00c6801580030000d00045035000d000f015201030004a0055903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 602489379 1250 602488129 602488163
    0xa0605160e01090b0d0e0a050d02060709091e0b0301020702030111030603120a0c11010905041401050306060a05030c2403040605010f090c05160c12050a0c0603050c0a030522 76
    0x440c20301c100a03a0420255a104001c031070009403c0f20240020b1810114112280782c1d400b078501a80c0100c014003074480c040c11010310b41e81c00b20b2464003400c0315550702c12030b440c1d40d20407080546880d10011410414071810004070040540d2088180c64805070004d418102d80f41c001034211545184013a090110001c10082c1c289014030080040d8010034803150f0600d500301c407000b4014414844014207280e40c1c0c00c000001a030140549030001c0c10003d0090202d40c482c8403130944220710a200d054042d109980c081601c503e80440401c0545034054010030316011103204010300d441d60714581203501e1505041d4032017001c180c14001c6100f54002e82e0082a15490300442c025290b038140d011401080c940b03940303100165840011140135140c5882001030081542c10015030b070280d036502440d4480040024070040100216003410624004c2d01e102000540e110016400d80344100c800508100c0108007807003100b80640e0020f9005140e09483d03200403481035101d00402068100c09035125107483e20400700d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 602490629 1250 602489379 602489387
    0x504020f01110a0803041b14040c03020316050d020403140a1104060311010c06060b0c010c090e0f0c0c0c1305161701060e01140f0a02070f23030a060516 67
    0x60030310030300c0c00c1c400301c018141420b0303124206088010054400040440e003804902080040000440d40700c1c00c400e00d5640002071260100d2685c15401503062545040c001030080c42940d2041024030340025000701e603c04226101c6c0d101d40740103040250300788400301c082480c05494110032280c4100a20501c0c10500b058001d00150540d07481c0b09500708141880090701c0e49118002e051003e080c4940d4141d601c0c90410042c0900d41c111400c0140046148a461101500017007204121522030443c8261201500c01200c0f03012260713003c1507080c0c0c0022034a6201e040c8018111150712409407a200815100081ea0b404800103500245540321000d000d2600743e41c160010200d06079003800f410800b14100f4101d02804c0c148038030014003102d4070307002c0c2869018125030208906012003c0c0e90b07030660308418200c40d41040002c540180300d103940108484d800006040103861100003902e04891000d40c008640441c08101c16425004171024040080c00c0740c0940781c0a00900120a2185030f01580014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 602491879 1250 602490629 602490649
    0xc0803031803071a070c02030615010f090b03130203150109090605090f0d11160906140a030c030b040f080c100b04090b1b070b0a0c1d03030306010e0a120303050402 72
    0x18a41c02c10424400040c6501a518280c0d0844800411250f500e2031819141c03581d010b0000794050284100300400f440c07c4030801c1e0f0410750309894026014114031000c0b00e00704158040c6401c201e40400108841d50501000c3c0f90303000748020111003130040c00440310000d14100381d0014212a4031000a030742080000d000ba20352009c03140300100700d2544a003000c0e56882007041b403100184809121082800c003018403032088094002e00c1054075069894108000405c1c0612402c401d44201a682440d03510b810b41000342101d402c83d600801e040c1c1103494119109401501c201d4451006800b104001060000580307100303117114000d00650403140140409070b40120201ca8411842d22110300000f502c1392860580104c8141ea01041c4001c0c03a1030209905d104982018000e012100d007004400e00058110070481540c0c0d99070f003129260b0140d4041c92110300300c4084c07035050704140001520355214500701e50301d180008204417030342030340d910040814441040c016000a52508100819400c00081c80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 602493129 1250 602491879 602491921
    0x50d02030322021e2b12080f010b0c0c1c0c0b2505010e03120103110306070507030315180b0102160f21082a0a0b0604020d090c080303 59
    0x107003590b50300076030000e59000a940000c074041c044808a103c6140c8400ca441c1c2861050500c01014801425018100c00417800c4002c441c5c0320a210800c0c000729101d4914940151490000d5403080e9082c500e4070f01070f0344c000c80340c03503100341c41446d01908055035041003250701c3c00980c4400d031801c5501d60819179500003481c0c1040c41400800c05c00382132100482c5074100004031125404580d0010103181803405070403007003002045d520000c140300d0902c0c0003506001d030403a4420315401c1c00b0b0100106c00d040c6c0b115000c6407000041002400101c02081c02034015011481034109164003940d241c850400c003150b02880c80c0400c1170741d01e079681c0b80107580403c990700c0281035540f0031050301e82c81e10151140d1584507010340240101046015420702d08040c2c0d0b80d00a0940c00120651250300d100120040320b407038511030079000d00c40440c0545003500c021565208558102540c030f0300b269140810310019503c40b105140c4100c1c0c3d00c801000200e29151aa9000b6000c10009595030f41040200001101201e80034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 602494379 1250 602493129 602493181
    0xc071719080705040b09010905060a030e06090609030f0904090c0602070609081b0103020c150405030d11030f0604050601020a0b0925060903060b0d1a010801050901090b041509050d020303 82
    0x921009580000c00e03513040399030302c4d01019502c941c40d8004907014101030703000c40c2e00050041105000c0f950590004e070034044040040f0f400d680d079200d10156541d00f00b036440014641040099220b02000355000740341050b0060000318201a95550b00305514402c0d500c0000160044002809040da103c0d09020040c8100b400410700b011000340c0c040641031110712024180369000840d00c032014014032902e07603900c1451002403514034003414081d440e039000400c0340c03041c180b82c0081c0d44103940714001a207028044204543c8113503507942041c0401418007801035410b501c1005141300c00260302c295818810800800a004402c003003050301d000c0c10182c0d0b88403941741d42d641c07001845950b501050401c100c942095001c59100511001704442c1039071001e010340905d040000c50380150650014003812070310050700810441d42d80801c40b5003201d0108000901120303440012501141c2008480c100e2442d9150700040c06c084079941d01c501d8503800051441c056000881000748896800da030144181040160b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 602495629 1250 602494379 602494381
    0x4020f0f0609041a061804140c07020f21010902090921180a0306020703180f0501051b0322080d050f07030306050a27020c03040308030c07171908 64
    0x10014400e0b014004120f4096541d901300034108070050f0200d0306070038002900385035991880c02c20300400c810700071590901560402543c1c3d60300324503014255100c1c1d008500d007a82840c00d42e508001d00c2110400c91250300000b80300c09804004043c411031000000520000240b1201d1407042c00b8202c400101780500c42d40090740e040d00500310344400c020301c20300ca6454240d80e038095100c4112400c0803e1075282d4002401441c048100500c0b0360040c2406802602c03001d51100000c04003981034a194040c0c2406022842c10401c140c1d4041e101401040130300c039030307410b500341c0700850070a1541d00b022201d10414085000b80d12603196044201e0030250680c030014020000880e14050420b203e1a440030000c0e0f400000d540017854880d0340240060300700204a012007594903104500f03500750001606000a101150311700031203016208a070a5901c00f1800782d03080a00d1a1600d81c080d80005103120b0101108200c0c40001920304031004040390a10441c098991071000504000c44416150103428840703100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 602496879 1250 602495629 602495659
    0x1d01020a0813050f0d0507050c19050d030e09090a0b1602030a0f0519020f0706021603170408120316032c0106090e0d020c060403260903030307030504020f 68
    0x2200e4aa030225001800ca00040c0b11403504030301d040705051030603200340507055614682541c814003c0c54424050340484503469146030800034000305610095044824840e000c010078100008802300b480e001c0e0406940840c0d100700843d80c400c004847e02c100c00e400503203200c802c104284001302d0304160120605040d144541070302a54921560042c202401035049044451510540031201400340016100018400440029681d0300303851459074814069141c1c00300f4014800500c40400701082d0145040103855600c070b00b55070a15090504c80c90440401001c00c0c0d88204000d440c1e003400e8101e202e15078038603000c003035000e0074003240c0304c400c00300b42c140042c5030213000d18024655206101b0042e400e10080840c4039160041105a0000840504100f11820090130100c1d61a40b41034050702a00c91403e2000204200341c0310b80d000c010845001401040c0cac1d584510364100f45103040c0164840c0c640700781480000e28642044684034002605e034000c000450802c280303810f002440a0307690f0362280c5514 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 602498129 1250 602496879 602496887
    0x5070b0a02070f0212070f15021b030f030a020607020c0a0803191b0303060513050421020316050a110f03150a060f0f09060e010e0106111006091d01020a 67
    0x40c106100a980204089041c8007001e000182c02a9006200c1c04400c62100100d0307448840d03511a000b006484d51000144210b15401d00202064540d8050129080c51900e14900a4501180c00c1e405100d001500164450104001c042c030a0194000704000e20305030b8002460140340403095406580d00350070401990b0300010546542c11410b10b45420340492000302150000c0410086218190300702149000b0b058041d80020140d41c400d885400b4200c0900d1103810170b403141610000c103131038007107580c0d146007084400c031307413000700704180f042e240340160003442e103184608010b07000d85241d0044a448820800c0c07031180801d90201c1901c0042060382014002910ba540080000440c00340041c0001d082480c0c17544850040c05d451807105102d43c2e00c030407041d8520111409807040903841c1ca00b0200c1d0304446c074407601d4102e0300110701c860f1060382003000440c0d00d00c041c0706001301356220b00a400010620079001d110050a0100303000500b108003840c1c1d40400390105200885c0c5644108000c036074039a0b00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 602499379 1250 602498129 602498131
    0x302070e070924020c042f0a090e18030a08160c120f0c05060f06010f02010614010c150608010507030c03110304080306030a060603050129030718110301080705040c05070b 75
    0x810200551018810102642880c04150495510030b103442c1a21103910640c11100058050311080c0003484103e40690507c0d40c030458082c6801310310124000c0104601d5045a10741c410460709400d00c3d1140664038561554001d07440e48c0e00442c6818080204103102401c60740002a65403070640d14108040e01c0b0122500301ca8560102044146030012074903a00802054180702d510104071002403030403441441649500b6184980051500300e0090040f600c1402200e01f44c480019805c4905081c010054419040c101c8040384c0d140c40c0322a400c1c420b01c2c100e00c03c0c0b0004110000003c2098070300108010304940d040004401818545a20b10400e043d00d4426039900c03581c03102c641662500c3d5000041d1420446400060402c0d0038480c01004009040d041044084044180010009540d456503651401c05c041029055400340604108051000e918036604c0140d00f0000126040450300072015035100740c0000320f45a101c600108101c1c201482070113940302a03458041d0910020b40d07952602c10340c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 602500629 1250 602499379 602499419
    0x902120607140d0b12070e011d070305060f04050702010504120c0b01090b06040b0c0106030b1810050705040f080c0a09020f1801050d061211060405030a29040302070e0709 75
    0x8001c00c2010a0010950040c00d1214000b0032080c846a417640c44541d0382c001a0081003d60380c0110000600040340c1c2154070660103a20012640d90ba403561000c400800008050b030703920211418001d1702d20b445512503d802040300c3d0740041041c0c41d0a0602561086000c100d51040010120003240450103400ca084c1c1580c034415008283e104035400000d5030780c081c98000c2106c04070002140045818150300401c1204e100d4031382c3c421640e40d011800707148c19520b5003e03410240c00c0380722110120302865200c2c41d030100003818114103181c0c846246c0e00c00038002d074004880c0c591041a850f50180303003210400c8010111aa81540b8010420310b9503000ba014401d443c0494220f143c0c0400030030381c062420703502d042c100c2640030089a035442ca0307006818030032700c0701c2525038400c0c004040304030307017080001c036025920050020f000144c81c6650b17030400d107030004400310455640020f0490684581c80ca5582c0a40d0080d07004082640c1420151301c0b646030081d210f002480441c3d0300400070743e8001010004480d0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 602501879 1250 602500629 602500667
    0x30e19030f0809040c05220518060112050703061805101509090c08060f010206091b0a090f020307110a1a190504150612170304020303040e0a0902120607 67
    0x40145012200b41c01541051a8071505060220b8000c80e0300101070150049035240c6603800c880341030984801d013140d60140030781046140004681402201c03400c82d402017011301d40b10b0105034088444000716030041c0e07089800261650300c10407100714500c50340c0741d104148035010003580c02e00541d551030380100d5100f01c00a401200102d044000d014100280c02408200c40500c48007d15017002048400101c4041d0b02c1104010113500543d403001400b50710a00b1820010204468100a143d85c03560340c105070b06601181c150700208002216010728807415142d400051307281d003804480901441e2186c034100d016035100014a03004030781d9400102c1c0410012140141a039210104048a90f40146001101e16170410382400100002e01c602d010201010480c01c00081d034403a482c4280810721000043c2c441c020048a160b40d00340c40f40c1c025900684001c045030300d0b141c1d80d091070554900c803c5520000c0150303101207200a608003c61940010454000508450301d0489005004041d41c015082001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 602503129 1250 602501879 602501903
    0x1709030d0c02030f120f0106080907140f0301020c070501230306090c04050415090509123a0e010f060503030703121107050109050f0d09030b060102070b040e04030e1903 74
    0x2042c020300840c0e0408403d50f0b500c41e562508110405802081604c801c5499855840001051741c458600a80034111803009407650914200300c1070790102d01d05040f15401003403d542410159801d200030201d0741c0b1b4007005070803071a1802c000940700b409402140340311f60440d0302803070b45640c3c8214100c0e0b51040b801c581000075511a0742c0303852168003454000c0c0c1c3c7c101d45003070705d0b20948079450448641150306d004414000703a581c1220290700c5012451070003505001c10b0154038440703660800360840055500d204080016070b00042c42c40c030140700d49018515a40c0d61990080050028001c0c0109008018024848146080b0205c0d0f520f1248d0480941041803da04c140d0000c50180c103c0700741544614001130320380025081c007a008002e0030000302c500788107540340d4014200021440d20310000a90700c0d4422013a10303580710300500d07250060402e1304501521001040301503012018001403c004042020b01d40f801c0d1401400715000103180c2841103020b6110481c440c100d502000041d00c0e4071246922407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 602504379 1250 602503129 602503151
    0x30c030d05070f0605011805161d030102071e0c060906050a0804110306090d030608071202060a03020f04060c110102070e011202040e0a1a15010801091107170a1709030d 74
    0xe00441c0d400014400c0c0c5c100b40c0005001d4034694620658000c1c410000c03c0036444d161b80c209442210510700c3c00c0494032200302944a026a47c0c0820703d2000702500149c90010640e8074403503491110340b50380c21600c000d050402c0c01d01c02180861400303000c01d820402125800c002001c2d113a4055540130f0390070880c400001804100b40641c00c0c0b0302884014048584a00308550300c241c8411240d6400000a407401c00300240321480003c84404450f55084d1310460401c064080c040300c0c3c1d1102d041c51040c10340800c2800392900a0400403c02400e455450400503681c030b00d0006041a803c07101e090456114030024404008071812203130440d0089891541020842d00c049000742007655210b60080c040d03040e1400c240280001000c0b40d2000035050315a041d035404c000c04402c01e020b1803a50703000511410061005040ea44d01070544400f000f00540c0c207104c0300307a40b00100100504203003440250082a205c80f0750390080000020302c1560782a00d05030303240404140da035030300484401e900c4240c3c41c3c00e103e0382 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 602505629 1250 602504379 602504393
    0xa050301051c0f050606010e180f09160f090507030b0f1309170c0f0a17071703190c0906121a09010308040f0b0c060a1d030703020615030c030d0507 65
    0x1004070f500c140d42c015006060b0030011349621044503001e0125070152665002442c00e50014142c6000102c4200043e451760841e81c540c0f880000d1464015120302440b04084c1d9902c410300d8002040c055054041301400c0c10340b0780f4182c5001420540c2418100481485140e841808450402005482032305413010303080c507107070040c000606003c1c007803109402c00c40440815200080680a54600c2120754050301001d9440d40c81c540d080f4046e103071500f41c01e120407203008070400030606030740608002207030800740d079280381d900c0c0d48151481441102c00703403c0c214958a1741e02480b0120300f6036081c041e00d4903141070300180200d250546c018280c50b94a40c461196484108103080d02d10360040c10a0b0038940c0c4900e00246a90f20900a080180e401d43c8000030301845914122855010803101500b900e8441030950006072041140b41c24091503041d0f05c03800d415204001608529010340d00078240ca0a1010300e424402d95141e900710f0080c0c004160b000b660361000542c02e04440c0c0c0c030341303055582d52109051401d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 602506879 1250 602505629 602505679
    0x6010806012318030a050307031413080309040b0a140904080c030a050c061609031b082a0a15050309030d0c080406180210050d020702040903020d140a05030105 70
    0x100c2225440c00103012604040340280c5681d40d0b041c8407403056078000f4400c0554641803000000e00503441080541c0000e803042c4101c0c600e41e401510414100800c1c511100c3d80e1440c41e170009001540082070342d118601e843d00805001b1401a10b000c0c1240e402c2442c2642c81c2c04c6100078441c05002443c01081c2004030302d00440745103140c070405a136100c1400080044c46580704101003c0785204031404120b0750517225041040c0f038203040d1101c64106245a94081001301207a051041e07021803001e0000e101002403050500081401c41c1c0c0511a50000b100e103540c6001071001c160042164103028065104050380c50b50089a180c01c0070b580782d90b6903030100c625521400c1082c016845c140506902070540004d00c10b4007540c840ca1082c803030001c0191508030b601c50700180c080d620051104442d6a420700400c0203002107224242d02600d40070007600482c007074941080084005030300c0324202c4130120741d000d01030703800c1c5080304500149040310310b000080c2180010b01a152052701103905080c81c00c03c59002003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 602508129 1250 602506879 602506907
    0x206071d030a0515070212030a0f020702030a24060e042a0608040c060201050709090b0301020f0f0d11031005150712030606200a060207060b06040906060e0d0b0601080601 75
    0x545145000346441601c407102a5135140103412060003103124540003007901d80240b450b450803d4219034800e800403002d480b0600c1c24a0795075508004072009030718107000c6600400d001c0c400c811074801d54192003440b00c2e6a0310700c2080340e81e031400000744003102d280d1b1800d541154101ca002141e0b080c6001062540341c03a100105040404480000036080b42c011092a00c038034014402c10702c1030b07903070340c50241c4c04e07a1811582030000602d205024006400e055014400466025000500300350911003d54903584c003800a4000d42c08000c510407a00700c025000d49613800c00c00521550640c18242c0c1c1340800041e080c00344c280300c3d46001310610380704140d140903100310a801000140ca07244100c0c401500600c003602444000454501925901c0c0040d160b80007804103011000b81403800103034841000a40102c4012940c05403240c0c00784a0311381d250000391002e0b140c00324000131454940701c0050704021000700824002c070244001500420300ca642050b0780404282089160b039079484004a6035001200d8513 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 602509379 1250 602508129 602508133
    0x30412020a210b1003020d1407171e0c0a03060c050d0203151509030a170c030703080106080f010e070f02011b2a17070f0b0c1c0902010206071d03 64
    0x9203944410341d428440480d0300603d0341019a4681da400c40380d80340803600020b034100100841120000b1800080380e45640810707001d407003802e0f496054055010ba0324050400701540300c418107015601340e88480103040d028490041034514031382c4001c24806941da20000d01259584c074015089036000e01c0403070340c0b407004d600001c640c2c9242c09824044d006c50700c00c13030040c002c9003c07803250300d0030200e10001c9171440040200200125038007540d641d0440d1702540840c100c1400144403484022508002402c0010b1003034542540355814040c004000c3e010062110701c2407210315004000e00d1042040d502c1d045212858540f00e8110303401d000f80c1c0075140f8990040b0116005070030b0605c42582c0070f10006000e10041d40352440841801101280c1d0f00401e80002c1d0440000300e9980340e60b041110010500540300b00d400d01e114000f140c0320400c450324201e83c98111418001042c140c0c40d548550940c2541001100c200401d900d5500000d640b000000c1c010402c1c0000908900c07452103151101c0000d000d00181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 602510629 1250 602509379 602509409
    0x60503121e070b090c040e060c071e0303090b0c030402060904020901020c0a170c03030315010c030c120503010f0b070b070f0507020a080c010e1f1b060e0109021f02030412020a 77
    0x2802c0020420f040360782000341d0150703003442d030124070701401303103840e081c0c8044020503060f02c4e840f02230892540045401c0301c00150703100001d001c000342d503410101c030350740a91000149495035090107600c011000344480c620942c1001000010307910070003522451001034034016120005100140e01e440c0050701025807110304c051002a07003455011015407a681d0342e000b0398081c2011402490b80d40d0006440d4081c0080c1c08070154012075226401c5449064001d18121882403926102c412415041d074030140000f410000c01440821142c1401000420042a0040c54036580d42ca4407040b4000140c02103040100c1120b55500c1103110304107072200240c0040162008a030355200e1140d175803038401e103050b004ca4028210103034685000d082c0c0228000340d010303d004141c0642d0108580460794040140c01c1d202c4012a110003082d080d119580402407007000002d00c07003910380108031643c4400c540364414003030b980d2140021981c1c08004e540455020744003800f4a01a18400150395144541100082c0c00c1703001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 602511879 1250 602510629 602510633
    0xc03070e09090a1203020703080a0f02070f0b0906061c1704080304180f050405061303050d0608011509151e030b040804030303060b130e070e03060c1c060503121e07 72
    0x703c0d00c1140786114442001d40d100a6250640690103070b1240580462482c000145002070640c200c0d89013003014840040c0f500705107030703280d00402040d40300c1030707134050f01100070000703078441c2040101d40051f0101c2d9044007030404601c64040010170048000d1241a0703c00c910300c184480030b03050710080d190355025a6110781e2030f49990300d500500346000c8084d00c0d00b0070080c0c00035100d1130f00c6400e02642d0403002a160702e5451003852244202418802c504100d42000b84400b000842d01c1a080603051078000814000101d00b00010544074540020620303d140c403c455010101c151640000c0b682240b01465000204103e030b40e5400f403c1c0c1e80050f20301d401c0030302040704108500b401042034138800d03102000303a0754595008520740d0042207800c01101541c00018006c648030b2240c4680d00048a280081100c02035401103405c1c80800d681c0095500e40220b4148103209040203078aa02c2d6034040420440c4c18078010000c1e94034103545c2c03001802d4800002d280320a8181c24004500189a10b040155031b0313003d14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 602513129 1250 602511879 602511883
    0x12091a07050a0c091a090702072120010e0f0604090e0a0c1d0112050318061605061501031b140c0f0c1824030a0501090b1f06080c03070e0909 62
    0x30306881d04c0308200344410842030324200041d18000d40a13640100506414581c0542e0302b0802ca070f034030f078000c07a0315845404002005850170303407816402e05401543d00203640002420382e00c920a02144140005007610185840d5034082ea811100060300c040f5190b9200c507a041c2c00e141c00c08001400c0004c4001c400f1170355000011280085172104a00100c4903030381c800c5e603401c02119031140100305410400200540805104c500c0340310b080018682494040702c80c02400c5d12030507081e41201e19070450810400006c40c0403070051600202800d041c02a00c0d00d0000d811031200d81a4508402c2c40700304140c0e840f45001c0c0c5029603400440e00401c60b04002d0b40480c0d03050340c030300424200b60711850110088080c90002520580c2c090700841362504a644002030b040e2900c07056165200340c051181070900d40103c0c0c0c4c2405040c490b54043c1e041e650707260038890b040c031010104100100046920005041010990068404d41d01c100d00110703080c3c8a4036299000c0f9001c615030440283e21040000034480701c4540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 602514379 1250 602513129 602513141
    0x16020904050307050606061c05180307060e010b0118031424010807050105070809010e011e09031a27011b0f09210201050706061a0712091a07050a0c09 66
    0x9101700e800b965503d00c01c00030310340f280d42685030400c429032050070000e11454004580000880510028a40c940710b107242c40c64003c0c0d40260f03005600ca00483c2c5807100300380f142220706c10b401e103407000c81c000f0881c041914080103840001c0401c40f104400c14203411302406021084041d1002c258904400c0c40381c0010840400e0080814a00441c140002c840d800346046a0b0750039032000401d42032440640054900c004035600e15810302800e540400502040414001c400420b19220720444a0547c14451000114406c4905070090090280444416a205c082105400090769401e0140310b100010340503001d51006c0e1000f03248001818800f072034202100700402229070395004684e40c1e8483d0006a002c8540b0501e10138404940351071005544548000c010702402400c1c0420740300e64030000d40740c1c40b50f180c030120400950042508030400c800303c08480181d4016141c854909401e05203c25001001100d16800040000503d42c00700042400340e000f619130050184075400ba5154a402c000d40740d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 602515629 1250 602514379 602514383
    0x9070905040b1e0f061e040204061808010903052a1605040506011d010c0501020403080d09140a0512090d0b071808280302151005011214060616020904050307 69
    0x3842c640d22884041d40ea1a585204413000e034500d03001901d8000078814403400e5550b9121200404688420f40c90b102d83c0000d10042815079a600d051202c05404500e61000c15001030308540d04000040c40840c0d40030064684440b0000c040c8101003e048618030610030307407040309654a018000704104607e03c442c03d084200c03034050b54240201d550b244c00441e02e200e160641c1c41c00414454684c001c10394480c60305080c0040c8500001490305444c2d44481ca841e0b0458400e010195858241d05400c000c00401d0003854840058000c1042c3c00a40d5501d603102c001e00c0140004034070001c28004003690f2a001c080e0070701c64001e5503007025800d00c003200410070950300080d43e2200e200d940c0c0010b540300c4001b9002602d086121040511540c54110306000101098001e90451141d503104880c20029024424012840a201c00194034070344030003d071602c8420300c690011503144c42d04c0000c810a6021005900080403039215a1303d0002d210b50414421941d8001b9400990540c100001c1200001c000d0031054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 602516879 1250 602515629 602515651
    0x306050a0b040510090b010c02031507110d050901051c0c0f0e180402041112010b030907060801081f0f02040e010f0b07080a0c03030b12031c060b070b09070905040b 72
    0x40320038002e001c01e80e00160b1341103008503c0c0000c10403d5034020350203115466414500700d40346119a400181c50014480410ba51031000101807041a9400098400701ca64000c8007400111036215000781c000d000e00320445052020014400055011b00b0040313172409a1500c000300a600300e521340c0240101c0d24825283c2c00302d1081d42603094545000c1e040f20218034030040110a0366501d1b81d007404050100c0b0f00d4a540c1c00401800000c03907603404d2648080c040c2c4081a0704a8591070a01c0c4068507000e0140d00c070344c00b0300281350014841ca40c1d020600014000440030306c07803400c0e12021242c50080640301c204154142c804036002c541581c0a440b1541241d01c030340051920b90340c0340ca400320028800c0d110000c00401d800c000b10500035008600584400d0700034107001604820030740100b80c01c40c0b1100180c1403075401c0081c070a4820501040f502c582000801020801141080c12070744581c400d58102074440b100c800c0c0010030f03024080245502a100420050010b0300b045d1415aa540c0d4094944010302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 602517985 1106 602516879 602516891
    0x80307030c06090803090d080f011a03070c05032a1b010804050111030406020306010206130c1a0c010207121e120b21030c01061202090f0c0c070306050a 67
    0x502000026011f10302e81c0701e400510320ba0000701303403596820340d4100500c60019984480c800050481c0103203a03480c1c81c1d4150580303011400840041c0300d4800010f0240841d04085080d0350000800a050a041c20310141d240351200711000c85070010000d0040303005000d610402640b60014000c400016a80d42a9000e1205660080303d080d0340c420b070008107000d01b42d43e040011f1548034504080d0045a490153340380d1503035807107c2c40340040d0b401d134402c14541c074103810f034080340c107142c840b50004c6561b4146880c1c080c00950f05100b403103020680c84481545101c90354030038203a603c0c0c05aa200c0c030303007188001070b00c5000306448543e0f640c01281208800c032071410800c42219889030341300b000f140c5401c42200300702d0035100d69801c03804040c0000f074520b40041c0c48031044560000c185052070340752540c40341401c0700c59004105d642031040c450300000205021290f4441c90280b01170070390038028 = true := by decide +kernel

theorem cover : BRFrame.Cov 602338129 602517985 := by
  have h0 := BRFrame.cov_init 602338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 602338129 ≤ n) (h2 : n < 602517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
