-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:02.420351+00:00
-- url     : https://prove2.me/submissions/39731dd2-411e-4e8c-9125-ec42758d9145

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 368345323 ≤ n < 368525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 368346573 1250 368345323 368345399
    0x30312020f0309010b01170c07060b0d0f1a1f06031e060f18060518040f02060f030402030d0e1509010c0515190b030a06090609020901030b01080c0a030b01 68
    0x2c0282d9480195a55400352240c01e5600155400c2c0c0d140114040003c4c40c2c80c1c00041e07280c42d0320071880018a0307566074200c05036999484d000382c940265080300910904001c0d601d015046204580300d040c550900c0f0302300252560000c81a200c0e03590302001280b203621442c0103007c2d4040d210180c080004050821103404003000c481c401c0d00000c01c0400020303800246444450301d80d29451800d0080304900b01803041c0f2442d2600140a074584220548000d8143d540c0e0a04802500341008001d5104800142d0181c49090380c9000e1401580200c05890360400c01c42810707078112000f6411507403c48110325011000c0c0d0300c44030240c88051810305203600800c145996290030b26421000342002c1d030700c030761003400030514610b2410705040805c2d201c208483c8160100180c0d4031038031464020b12660b00c40c2e101004014894001070301040d4060100920b80d41c6910304842c00070824003620b550f9100d8246214602d151031540c500489401254110859080011000020142c84617840c2a021400d0000603050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 368347823 1250 368346573 368346577
    0x10140d050f0a0f020306060a0e010c17070215070b0a0c0e090c0a0e01180b25060e06240d0f05030403080406030b011d0907030b0409051c0c0309030312020f 68
    0x1602032401c1e11007807500c0803500b000c0381c148a46054038284107204010203030b1a60340c01c889100b0340307c0c2413407201950000d00498681c181c9060050103844480c50355000d207a07852014040b41ca1003181c02803204003ca00304058540240310018245030301e0308c0045113000302213a1101050078014034041040003000e0700800d00f20142910310000f5800300088000f0466844601108412024a09980003aa03030009139031004840b030043c01410b500005400501424510029505a0402d0510f1100d01264202000180020a41500380f07008520029610128440d040072200b0070800038050041c0200c4240003401f6110316080b103010301c00410480c04100c2c1040988000d601c00c503543c07640c2c1e605104008043e01c0010342024144100342207607000009100b2000c03c00c9010540328402d0075511000301300c02a200b114211508103180c62041400e21002280d040d404c0c0024601502185c81000e00444458035030010150000d0b000349014000688141c440b0f41000300c404a0150a14400d118403003402d0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 368349073 1250 368347823 368347831
    0x8070e1504050a06020a0b1602060123090c0d050f0606070807050c09041b051504030b0621010902040605090105090112080d020a0f0e0103090308130609140706080903070210140d05 79
    0x507906c6442c05c0c400f0002d031807482c654046a0300c00c4200030b000700d0f0b81029650b14818041c10310402d040e40c0202c0700c42091250118031400c0000c1441140b81454294045540e01040000c4010b6041400013001c028130711400c240100d50140c60303a0724110303045d11040031503002100111842d01411030b000846542d889107843c091401901001c0946078241d80c0405840ca09500080c0220070100700d0440012240040c2c40c2241c0e040142d00710f45540e140d0000b6030090b140c41400092100900105540c3c3c4415448840c44a02c00d460800105481e1803c20041c010b0900c18194030802650050101c000c1c84016110310300c0c86507050b1418510080b600c0e0069030080780aa100240400d0003000c81d856000484e4072284200382010841110036890080404900810004003818254561010488607601180d44103070404411258100c0c2c1102841c0c50740168401c3c2000243d038800403401444003c8121113545900902c58010031510f10010748410a5024640d4203600041c000d040c940100340c00b605120b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 368350323 1250 368349073 368349077
    0x1e0510090e010e07020a03030e0a120807090b040f03060903020a080711010806060c060718091e0b1c1b05100c0203160e060603091e01091208070e1504050a06 69
    0x242030815400c0781030840c0c140d100401800b0b800d028410125000b00e1900b00098140ca80030030804a000031142c940700e640e90008200b440220308502c0c0031940310704418007600240e980c40082e07990303d1040620034029402000b48540c030101c0c040000411036444034074000e03c0790054900c0c04503942c031113640c950401703e025114602c07911124421076a121041d80d6110f201282c24178101a6140010395842c20020310a030184005800070900c44c0f0b05012112008140d04e40e800e008004050304d038030f0101e88001203511005410300d1266500ca1030070b069020407082d402071030441141003030f480c1c9000107046840344580c03108000304042043e80310407042e100d00700b4498442800b1443e051040c107181122171210004060f0703100030140042c20f90b00300310315080310003220069240e0703c03400e00d400e0506140040407524080800040880d03044107401c4442100d009411140d02c0d2242c2c01030640343c241049804100007803848403224010714010b00d0703095545411842080c10145c649010a1103c2180d400502c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 368351573 1250 368350323 368350337
    0x151e04050a0203040305180307080f07080f0a03021b0d081b10061206020f0c010204080d27090509010b1216090b10081504050c030115020c0a1e0510 65
    0x41141020300806801c800d04040442c9545402d460042c000d002e1f04410882802c420403042c0220703034040041101412180c011360708c1e13013524850701d541c0d10b01141c400c8014502406508802c8880040b813804245909a0050541c0c40d201a40c203440200c2c80d41405648840c040303152502040585000e8140202c6404848101707242048410f46070542020390304203040d05000c800c0c050341d410000f081e501503030300000160b1203860f07403100d05c500c9020303103414180c1c60361000c10000741504c00010040d07113407007498642107a05180d80300310b0018002481071900c8414080d0344100302e0401141d0025500c41021000010350756011400559101402c2c0c200c0c08140c0c0c032140ca9031030452501e81a000040004040401024105601286e4010701e14201c0c902482a0440080c142c994694208403442c10000d0080010345418050626103400a004100b500c1080310f410004130303400082c0c0e80c802c2140c0201b510501034035000f215800e04200405080c1103080c200000103e58490300ca00b002c80094a0b21600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 368352823 1250 368351573 368351629
    0x1503060207030e0d05120a0302040512070f091104060f020c0316050109061e051c020a08040b0a0b0f0f04060306060902180303070b1b04050d11042d020315 68
    0x501e082d4038540aa44035841c001c8131900007501c006600491403070a1b005080d00c0388800e00b000d500038062a44030540012a41007111031019003c07070110140c4a0502039203819945840110040b0354055910b02c4d6400f00c01c020a0292500501004050a030341b881266440d01c80710000c2814507140b014003802d03440e09100207000305d40e00114203074058030440ca000403480031515501d5030b013406188c02c0c034014010001a040500192294050341901103800c0a568803192004020319208013280e098500700080b1010910380d205600484881000040c143c0240c01090000c121800c2c2c0e80c0c1d4056588150f5030300000000a45d14040d680c02420a41c100603102c02ca1103201c1205498a10b890f02c0c0700380c200304000d0000854203404960041c2c13040e01c03901101000740900901c2441150441d1341e22a14480c040002c214500d0006010000250307000e0003860813010b000d080940b161051000c0c0348540c0b507080c03200900750b42d020303541c0140300102680388600b07284085085034500111050758041221100c0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 368354073 1250 368352823 368352827
    0x1330305040c1a0d0f02090a0305060601090f050d03080c09031009110301090b0a020c011d0d03140106020a0201110309270c0301050f13140117010b040c0203091003150306020703 78
    0x20300200440c04500d46400140d0903e025580714592150022540e1101456190715496064401800029100040d51910303400c240380e6480d0101c178018001684002d010416022b203e41d840c045030f00140c660781c441e46440d034040d51b0007200209098143d070001d02c00421302d0b60701080890358003203a0040c0042e02100d0350a2000c020310b0f906d03049900981c10f000301c81c00015076040340250702c0107059400603190944130701c1040c00340400359080c50500c0380c14200c460b07090102084a044522454504100001418080000c41e0800344a80c00150b00702080000255000e030190503e14500181940d141c0340c070240000340300451a46000d9200011351044a614a180b501c80503082101d03c200b20341558503040009408201c1898140d005990b001c4009940121079003299022041c044603038101d5603101d040c084115a1259403c108035070074034100100d1418248920181020154040c1d460010b184c024021050b036205001c02c10995180d1110704048040315040f0055485881c01603620540340c180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 368355323 1250 368354073 368354093
    0x809100e04110c190503070308150d230d050901180801020c150907030c062006090c040f090c060e0a090509010209120c01090e150d0615080a03080133030504 69
    0x1076042d48010011070001140000040daa01f00b60301d1315018102c0d80d42c01001881d10003903d121541c02c002c80d00604810071403641c1c075998202c445c001060416040250b04541c0c0e4280043c14080410700401600400d035101c2c04443c2500c0714507130307803102e10b1a90310a0b543c0d00320b0384800790090380c6d5002103015a170501e600003001508440f070540241245c03410f54580405034803441c4510410b10078203c50ba0382d603d00b1201c4001901c298040152041c51824142d50360721900b40000e40340c070031442c000d481c412642c40f0b8407440d401180c00500345480a400d00704e003920300708082c4003015440f1801000014684045008140c494880c2000168a8030002c60600c03244903141699180c59810044007044166444218441110200064418035844480c030445001c0c0007030603174541095000141409002c001c1d044101d00c01660903503501d40a82e54800c564459a6004004002a020b103004000400c403032140c039034210b12000f0b80700030a07102c111510800e02070540d8040003c03e40342c074100020b204006c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 368356573 1250 368355323 368355343
    0x19060c020d0519030507030f0c0e0a1707051c080a0207030605010e0903030f040c0906170d0906270f1403060f011d04140f0703110307030809100e04110c 67
    0x2480c2d401c05401c400310120540c14030150204140d030700c0d80003840052098112141001d42e00f4030070400046983c90040c051000c10040c28048c240d244c03000510380801c1c03000e082c2140030b054003070f0020340d080c6403c005540c0344000e900b41403500c5525100d00450100002072a001c203c54004200d11890340c60000188c0724140d014050144141e410040c5101c808030407a035100145000e002001da440303141000c03441d01260400c2d1900e514006010444c41154040201c1507000c09044480c0b800740c00342c0483c0d0344c0c08140030710380002d00002d0722240d09105454101d4014a1500c640a81c0d940c1c81d02000100401c0c190303c565000400076040903404c4c1400d000c1d0382c1e00004034004000300e1307604103660090320018800074504e8090072000054148400386000703010401c0e015003650000b0010390708250366042580005d44155440e00044003940c507000441504a983c01290700e03080c40e10020800020349483c0c9400e00a104070b00c24000c442d40e442e44203500400768001c09481d1940d0390030001502d002d418030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 368357823 1250 368356573 368356577
    0xf080405090f0f06010309020a03030e040e1903120b1008190219030c020d080105060d0b10180e130803070201180302330a0905100f0c08060306040b0a02090319060c020d 74
    0x147c800d1300540ca82031196010f071b98140c1040140242040702080c010260821101c10a01541c0c4400382000d031004555003406000c0e80d2a000300382c076180070710802c40e100808440d43c4082590003004c405805010300c650710480324101781814405d0012a0030503030388801818145140040d10156200d0303010302c64003800a4891004140c5000c0e00e100103400048113000c0ca0b845441d020514001c220440d07000300030000801790036526680102c081c00380c00411000700030350000711798807004140c185801c0c5503148140040d4101d04900c9d105500c0e041c1c4540d20140429003103540b6080c0c0f50700c01d0f0400740a2044030910a50040650601170511100384003e5121040341c3c1d4440030050348040e000310b0702555000b11460ac1c000900c0c58903850300724030b821900862084a14103007256040542643e03800700f00c515851762100741c0c1c141c3d2403204151b00c60308200c0c4d00500741d120140200304250090b84c0a0604484046e0499104590040d210510300003440e9040b5031140e100d09002c0641507060003241c0c24a0424 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 368359073 1250 368357823 368357831
    0x70c030908011b1d0a0305030d050c0a0e091024111504170910051207050c0d030906181b0504050c0414060904090602071703060a030f080405090f0f060103 68
    0x80000400c070001c0250740d0041000c00d82e0132a4111101c441000b40c0028010101c103130040c0d4a1910640780d0308080804403c0c0e91405000031396040c06801120700900b036a1791500030100504042000203034000c1c00f8018014840080071034102101d025003400030240001512005404a60040c001c01e40c01d4000411b541100400154100c030b03545489421a0b480700410200142603080c0c51464060744905a520000f00c2c4400030f201070b0400010407040e241c0e20007032030b1103582c1c003141074035180308540007410698848030055600074801c0e4030507005103200785404030742529103c091113120100d10405a424800043c00c02c4c078410a5103507a04028442542c091007585041500030045008620841e0002c80d400c041c0c501031b568030003003281d04100e80200104007022442c1840700c0290410101150032400c114a5481c00312504405c5c0c070700c038000040c0303451103107400d6aa8086030206103d00031200030000b840302080c640c0e10520650312980e04442c58118030703d40054400214000074000303034103241c94 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 368360323 1250 368359073 368359091
    0xc030605030d050928031103070f03060f06090f0209010210050103020a060c0501060906090b090a110f13030203011a190b03010311010e03120a031409060609040201050c0303070c03090801 82
    0x209650300d100450f81010341e10383c2d0a42d004501d01e44d80e0020552020b85106038092585079580d6000010340340203080c0f0700c0e1078584c03d4051655a102a00070350340c401d80349070003c00000d0b00b2900081d0468505480125510741d032603017001d0075147c2414481b150075801040c14080c6580c100075400c120100c03c4024001540746401141f0b0002660003a181084440f041440a200c400d41045c0700600c0d105c03500b0000203548500721b20003407103044a8103100311080c3e40419080d1100c1e001d102c1c42008040700440c545400d907609c24006521424904d5611190941c0020160f80e0a11501900074101c00c803604c20003c800d0108030230300c6601608800882c40510080c004442070005407070540340e114600390b00c006119001030f00d0034521070507020341c103100e088a04001c408170000a0401200039071818407604414100c9401200812a4204019841140020020700c0d190703000e29002401810003910304441001810f080d503004484290224a100c00d482c000c040d4054030100003403200d04020404556 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 368361573 1250 368360323 368360329
    0x1b140103150e0a09030c140c1315060f03090b1008060105030307033507170c04180506040b1305010806150907030b031903030506120111070602070c030213050a0c030605 74
    0x2c40a401c010059a035801c0b0001014000d14110f0841c503040300124031444035000741d081d41d0394240d4422a000c1c43c0c41d510359a540c001c444c0101c21507040356801d105409802c044003241c108000000400c101901c1d40060008a0400c4c03000600400c100d85140c1e00c11070070241030b03928203001a80724500940c130400280b0042a84820705001c50300042d50410000304d54110b03d060401031040404182410600a00c00c283c2d41080c000401c03100498004009a41c1e0311203005124000d0303210b0360307010401071400e842e84202140d020542c803910042001030708049001c003084001e8030300c550030401d41c5d6035440140300300707007081240c1c55000100d05a080f00290690b8089901900d000c0c0c9464203043c0c907403484682c1507605011062005c00c22a03a042707011081d5050050182c20300392200c9009502c20306c0194050304041c05800745440307038560110b02e829190f907030f2301000351702070700080c0c0b4410714003040400141d45075441d108600c5802803000c241400c0031000201150320311f0064030141482d00c1420807083c1c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 368362823 1250 368361573 368361599
    0x10b1002031e090a03060f3804020d18050d0e100c02040b031e03070b060a08061909080a030906140103050705010309060b120a1e08161b14010315 64
    0xc194802501e85560100c0d010030401060340d00b008200500381f555202e14003182da0701242d80384c41581e011402042200440d210b2401403c6805081010400c3c14041c0c5410241c0080080b0980301c1d200017080032a401d1125088205160221481e401c5004000c01e5554440c0c00e89240c1c4504860400140c988607034050240004807400a008540f03601e14010b082d81c041c002001c0c03582280c42545d0084d410080802c0d00c80e030000c801100d03144c8052012411a00f080c00d40d02c811b0b0303003122000781115180e0303030050440c1c0c02d1030032a60785180342c035050b604001482ea04050703c0d809030142c401082d4034940345800410340b00c00070000d07100b080e010740c01080030407000141c0e1402c882003800c00003404001d5041c00801b03024a0300c112600a0707200420b60041c0240007503d0941940104070003001c4ca0618054100204814940603102e080148146410f44550052410046208800343e46820282c542d503a68150406c0c1c1c8161310b451000011610301c0c0d45c05006d11081d5200d4151240c3c00e2a0406090304410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 368364073 1250 368362823 368362867
    0x5030c040504110c1b040c08040f0204024006050a021011070614090705100e190e040303060f12020d08133308090a030c060617010b100203 61
    0x40c0303440d0200000d80402c1c001c201d510b10652041a285c0c0414240c20751074083c05140c2074207000e140b80c042d805404c54811103001d030240340d0110714102065242c0c1c081002a40058200e2844c0b48482c0740c1e40041442d44401e050b132081404405c1c8400d031480034940d80c0070074403c1c2c0d00040c00e01204000c0000c3c00c0394003081c00c06035584c20b0000007074100380144000d000d500610000600503441c1ca0103012040751a0483d1300d01c50b824400440300c2c000d03111001c2c00340410740d6402c480301040b80c0920780581c4d4a410846040b1172400c08119420150760349080300c0c0e08020680d03081d408280d503848180440c6840c4030000300640100c2000c015502002d41c08601010344009015000306030205140300700d900080d103080002c180b070403900c0c6141d00d5094007500d900009490340900c452805505030310414000c0c01c485116034048409400e4910594a003556080076001c012500e05e59034020100f0801c1542c0c11b1801050905000090007581c2042440b203142c0000311a00259071040c440401c401c02608081a81 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 368365323 1250 368364073 368364079
    0xa09051507120501170619060f0602030c060a0b060f0a050702090f04060b03030a020703030318170c0d0804020a030b0601021501090b0f1206010b2808040605100b0a05300106020d05030c0405 83
    0x1c5c4400c01f20000e191313507000b0580400095100040d00795000018050a01810054894a0715211400780898000d06038243c1c100b0420300c14800311751900c402400172203d842c2011480c01c2101c2e80043d010010131140d0800c80710b40c000c240814401c0c6e5224515900c4800e400440c945405160040d41c2d80225210050406484a58484240098040c8001c0780c9511821340c42606003d2181c58000f038200700302d81d41d0148180050300040500c5044000d004a4000c0d00040d190b9003103440300180100000c045905501c202c4451044110004030101c0c002e0030341c900e0000740c0c06a000c080040403d0000c04040c0f0550703613a102c0e02d42c49074010514031f0440300d03000d0417155164a110300b1603a9140447e010b81c03408070320320f1407d0466190012905480395105a034204150343d5500c0d4084041c003403a0050381240e0700c05001c02841c960251001f0703d2600784003007402981c003240080744641080c034844d0b10640592144010800310360104103d51400449003081415032a0a05030742d12240035611500348 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 368366573 1250 368365323 368365351
    0x10050f160c030e0607110a0305010e0d050a0504030b0a0902090c0405040b01030b03030d09030c05030c030307030605010f08041b0506030103210203190f0504090c08070207080c0303030a090515071205011706 90
    0x410000490007100c1800261241f8000c40da61705050303000b8804000c5002d014000c80301c41a1040b4400c20031100314480c01d88410341171a05645480c400900300801080d021a61500b0300030141c0d0312810941d01c03501e02c041d0701540d90342c00c12040c402030301e030a2400b5505040c00c2840750051a0703000300c144c0304010828200000c00101c541800c458140c00d004c006042400009583d40da8410f0100041d0f100c0c404a0b02e0074090311340d8400044a0707600d0000040000100c0e1100403c0000d0028a01411055054410000c42a459000040036a07000b03030b00807a0a11703445410914070420014090140700300a002031800c00120045448111410740f0041c42084180c1c86130501c41406001a213024015400d01042901c11018000d845280280e42d08005407003044e4001882d0040041c0350102040d0223000b5504544a08000c00701419005104560301e0083c0d40c401600d19a48940c9648658420740d1001d40340343d0f07188541c408681c0180c0001c2e804030310b615092036040c02d0002e0700c590088201d0000c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 368367823 1250 368366573 368366587
    0x10308030403050f12010305011d0607110c040c020703060b060c1902030313120510020a020705090612030a02031201090507090308090409050f16142110050f160c030e06 74
    0xf030303040c030462803001c64091000c82c1c09004008030080d0710341601e02c15002041001540c40e1b40c4d55036907000c0c201079240713548070100107200148119100d00d480710403c0111404401d00000203002d440482c207103980160701074030b0f0400a100e007a000310007560710140c48152900700d0354005252980c00400030000e0b50032203c40040c0440d101002280d000044502c00304110319110440c24150f40004603050300c09200b290000c5001600e50f100b242d0015546400500d0710314500402d100e5004001440e86a002c050303242c042c45002800d1000f402d50911650280d46d0714640a03901002a20041c2c00004202c2e10706010010003d8100c000f85080d80d4100b1502074442e01a080040c0c00ba00750340000804600442c04c20802180c0c2c002088004caa030750810107410281c80d41202c45141644040282c1d10921190002d0002918407018070303a213000130800e4828500003510754074282c9030242d85541c3d0b4084802c080003105a11203800c405c8587c810320b040d0380400703241c3d18000c001c1c40541e680e0510076880000c3d90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 368369073 1250 368367823 368367827
    0x7020703033506010807080c0904090804030602040b0c06011a030708060f0a0906180515091801110901090b0306010c02010e032a18040c090c03110711040b0414010308030403 76
    0x20750822003204200b5803040d903084026000c02242940d200307021540380c0c400315004d0743c003c40ca624031a900c2e01500c13a05052003502000098448404150f5501c08108000f20100e0020300007400030b00540b110a0740d441c00301c0e02c289854150140d01480c050340c034541890b51040c3d0b804003280d07001022803510b861030307444e210002000c240300c01c1c101942c030100c071741c10004404e40c0035013001c02280c4201c04804216041c2d148038406894086034454820134040d1400d84240c50300046080d000b210030300002d0f401840400c0503d0031115460202c4140d04000301d4155240d60740000088040d0124840c83c43c1541803070b00020b0090480c60000a0600c004c81c030b410095902e00300402c2d6045424000100b4000d103450300c0c0711a00702500c2082d98001c0c80c0e10322440800c0424614940c2c06079900c4102c811600d45086002c0c0002c0c9668481442019100c0e020b01910560702d101501449000301d11030340144042ca0f0804c411695114202400345080040c44513500a916440341d044a0300050102d55942d228501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 368370323 1250 368369073 368369117
    0x5030a1e020a0906030c17130317040f1209351506040b091006050c0c1011060906150112060f031505061e1207170a0611030702070303 59
    0x30490000d4804500c1400195002c00750750100e50f050744042045091840d012074400700620328a00c20450b0000200310070315014031400416500034540385940d1140b2079111100990240c40640d01c1a068a010106224068030400030907445400c04040c0b4900d01005110401004100071840e00c4448100c082000502026240e0703031200c40090b111226140c0900c80402070095440340d010f6460310940c858982464030740c00d030164400300001c0c01401c0c500700080344e0711b91003110880d40c1800382c18010255601e9054402120300015182c91603080400348945160a000400b07500d560f50045080c0402e80042240c910004202072808051a14500b107903030b00602050f51010002c0400c14200200f400950811143d1100d900c40e800d000c15200e4104003c13505414a07150110303900e140300c12101c0d130f1602d40080d80711820703c034046d1400282d5980c8484c0402403500038149194101d19011400c011b5a8803641c26101d00c0f116030981581804000250313182c3d00703400010103018500603c00c411911100d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 368371573 1250 368370323 368370371
    0x41208090c060d0c090f050105160804150302070201020609150133020102271503060d0215030a0c03140c0307090e04060c09060e0f040218030f070302030601050a030305030a 76
    0x40302c55070310b420903240749004016809288002880007040451004c601091520031540165101e40c200517960030384400c158101c400440345084100400903155010122030714101d403090703c005880d4101c42c0006401d20800501110881c0c104241e80000c1c1c0c188110402c2c1500d50750480c440b4a1051348000781c85000c00c6d0b4859012071104079590f1011150b0540040c54040720f1890340d6414504168003c2c05200c010f8006280e228021004407569069500c000c0d59102000414800b64980240c0214010070a88604840407140c000700b0058000c1e55030240700401940d9140030044080b800d801015208005401c1094089001020a082b1072161201d5005050810515806428036250036401040d100f80c01038042462808000b850b9030048106040744600030340400980f0500c502008025400303600403904504100811110f540c80c20007041d0031f0142c6880c02803800c5030a43c01007500d07060059020350700c0b03580400d03c1400085d41c405c06503504165104004941d07040628111850420001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 368372823 1250 368371573 368371579
    0x30f020f01050a0e071a0a080a020418090309210210201f02040e04030f2601030507050d031b110d0308070e0303090307060503100e0c0703080609041208090c 69
    0xc0184100c0c40707003e90001443d403100d402145c100982e504101810410501000301d030008040c0202107019010703103001540607600c80001407a081c2c540100500c40740a20301070b01405503540244030700301a01725100c040a0420141c105098906c581e4001e22180262040240903a40308200c0c01400d9005400b6040054819104060f0081549088507a602c0d0205d082c0301c00d02c1c5c00031801c040390307190920844045e10440945500199510740b41983c440c440e800c541c0d010022428100e000803003411310902c0e0400352201c0c50000c25491810140e00d0000c4a1700000c3c030a05080e29000c0c0040c4d0068042c400d001c984240b650b10007901820f1240710800ca2002c1c090300b21560042c0d950406038402c015034403e400e10340302c6081401664051665174001c030b0503000d825500c104001e002c4a402880510b03400348038518104a110344800c512581d001080d1030300c030002107000c90729400300340e00502c40316071000040e07445072072510706900c841250318480b8204509110400b4041002ca2a040c07041032902c56004d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 368374073 1250 368372823 368372831
    0xb04020706141b13050108090f100f06080106082d060109021242040f0204030314070b060618040e060105120309060706020f040305070806061309020a03030f020f01 72
    0x9924280441503045035071404048114000902c0781d119482035440c010713210407845166034104030055039480c8000d80300711050b105410b81c1d942032007010010003140701c21002c000300311110b00085600035550150414449641404001c0c05141c1c0001400f440405100250303100340801000c1c100d0b20240c80224401c141c1c0604000801c0da40f0040e001412061211150706029a9581000f5040714848080c118804000c901921880d00342d5481070fa0481d4841044a202c072080503000501120380038060340e01c200d500880d08005050700690030210307030880107035030710b241119542d162007203420001d180030301c100d001140e50346a105100019000c2140c0c040c100300020207008074401c0d40c52a0912038280b041c4040c00800f03072501004025111080c4000d84120b082890350b50320640039400803e8a640842c10502002021a000700702d20802004010041c4c20300b41803d40c280314514482d03c001c200702508211a0800507111184900103c0f42c141c03410000100419200302d05104800651320f40940c24 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 368375323 1250 368374073 368374091
    0xa0801020f04031e12080703022101030201021c0503040f060603051f0e0307050312061206070305090616050a1202040906030c050f030a02010507062423220b04020706 73
    0x40754010800d40303001c0e9010346060b00740b010589080c40b16000c4010200303101c0f0305a1030340b0740340a01c042a4119201d4100941048054a02c50080242d514504100306486000400665030140016034200e84501c449140e240c4a600c00500f85200240c00200480340c44941003086c4400c942c04140955440030a5a543c036070760b842040d07075844000316465070251a0124044440000100f00d8000540c818041c50410340c41c0914007460702070040c03078107401c08110041e60041c0c54090207018480c42e40758030002040d061540c1000c0c50424018141e212000000d0b5444002c103400405540d480c4980d403a003010299600d140702400381c0681d6120640703060410740702104100ba00d0b14942c05440702a102c00304130508060401d550f80c0112000a404180f04103c1c103004a0340e0b1303030041d401940c01421440d41e80c4250224a4000002c2c44c0d1046100c40c4175036031240402d114145486d00714000c12125000740c80c81d4401070801840d162540c501907580e45421140300e0703445030f40640c2c0c01703107402a204100c2d45070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 368376573 1250 368375323 368375347
    0x20d05090a02010e030105190207050703021203180d032007090e0307110a0f0b39010b0109060f030b010207081501080601061e0f050d060323010501080d0507020a080102 74
    0x5007094124040360710581440340c3c9080500c10f0512036004200400c2c0ca442c149040304000798800b01e01600c490044103004009a1500b00b006000c00b0b0810b0002d6503034840c40e03940c4110b07240354403000c14450350405c01c1c100003280c0e20103a803611421154004a0003480d03000700d0b90385403580e00e600410400e03040c0760644058040c0840079254450090300102d03408001407081040c820030394000c0110700d0650807014015400c001c3d0182c1945010521210b4031030f10b08041d010b080945200b000d85916900203c50540044280921310074000c080c2000740a00741041006400d2095001c43d500070103943d441094403581c800c02000c0024000402901c400b096002980714040070240141c541c0e610442d800000d400d84a007002c903901d501103d10280d90484003d0044640d80f8000f40b4402c10044240002e192900e00c52142000840c801c0c1401c4d0650000010300f00e10b810108109121141d14040c010821860080307031030940c40c8000d18181e40d4074a5140700041c2284801d070000e282c5507202040900ea5030b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 368377823 1250 368376573 368376583
    0xc011b0504050a0e0603060703090203030403050312190b010804060e0106030b100602010606090b07110103091a15040b010c0b0c040f0305070503100b01020c0409141614010c02030a080904020d0509 86
    0x82c00075110443e003a41c0744d43c00e101140c4401e0b41c200d5007680c00302002401240c480e9014180c040d2004082d03e2410307649844007403854215160b0088a00b0034801488455040035111050b0311441c1c41003402540854000039080d6074009001030715103921024039020541003135000070051540072030702d2022801c050999800302d03c3d641c02180050340c03070103a020658074001d4403804c04440e80c21401070f00c0c004031035503141207503840859900c1c10715032902c00d0300300003420289011442d001c103031891011620748061401000b889440b0034901442c6006103a428a0364050101a40507401003040615a2240c001d80000c40c030075540000307880c01e099040401044404141d00007220004c50407138410380b082c0c400b0282250328240041d80580d1041c110815135041581003030303050794022003c01550300f11411200f4140720403010106480c1000c000140a8101e41054580c3c03081420302c3d20b14070803c0c2c42c2c0e0100383d5546510b45e01400c1080042031200c4d0a0b034845c1c046540f01403460406200c54213041600e44c0e920 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 368379073 1250 368377823 368377829
    0xc06181401060603050105030304090908120c0702040b24070206090d1a0105061201151419022413140715230a120b041a0913020a0b0c011b0504 63
    0xd508002000903d0383c413a0007614142e44005001c3e501d00751500645400904c5c0400d02240d04500904c1810070080c000c4003078512a8aa00d0205903a0b0f41c4070f44100412241d40420304d80c400c4505010304008207180307080039822108500100c030307540c202da8000180310b8015640b20550001010003010304010355008080102c0c1400ca41040c0c1c80d03602c035401c0140c640214081086003103121401000114940b070b0402e00982c9003800c20362080e0070688922030b60f42d44031b501311100d907c900140d9885055410000fa84403e00700d4001c03420406141161800404005881c0c80702c10045c00d010901030064041c03102d4a013440c05c50440306c003607580e07003044a050803180403541c0100364a41c0c1c1041c0d00500541c100368064022450681c40c09006000640381500c05402c1c51003a03a5072940300a800c2e841c0d071312645400c0490307000d112040e9602c50040100c450001081e2401844c0b90107060380c0140c48040c03100c02a00c0c0c29465070ba4540315070b6100b2600400021042c0144825050030b0310900c0c5030800000e10030f03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 368380323 1250 368379073 368379113
    0x22d0111030408120705030c09040f09141609090503180112020c01060e060906130c1101091a18100b0d0609150b0f03070315060e090d030b0405060108070c0618 70
    0x290362820f600746c80341c6c0412034904041c80e4041013440c1c0320340340507030207030801c588440800140e15007151244801180c0c01001c0710320307503444030318400306c0645c092000f1401040d0848003401039100f031344e50b201d460f40684003400c50a07010800117141540e0041e0300740c000702201d0303641c00c5492b20112020350740030305540e2241c0008030407602c000c10401c2c1040140e95100d01e002800401c9516000c140d000d00420103008820b040002045281c1c2850900380646150b0901a52031840e00a24841d41868218400344c003440844003081002188500042000d09802215200010341c1001c55004215400803032840200080d103000d48180403c10000c1c00e24021140c654010040c0751030b140180a90244482210340d8503074422030040000038000d15074450042140c1401141c0c040d921a203003035144200742c0b83c0751066000003006800099051148c0040884125000d01250510301c00280c00c00c0790103016001044006007026080c002c060300564440300e200109481a090681010b5903000355070124401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 368381573 1250 368380323 368380357
    0xb0a050702090601030902091504290901050102151602100f0e0615060906160b180d02010203040305040b0a03270606050303030106020c1306050d0c0510022d0111030408 74
    0xca107505c00d2280b0311401fa0301411803079090300d504034901c0c0c0c101d482e01c6c4801d0303029440e1040411400c4034403464007003004000c03141c002405805420000d459005810003811907104e00d200903a050262058540c120b07219042c101559008150102d0500510740c608241c8681410800e5a0103030103503121000a00c0614190b489503100ea101c40300942c1040341c10180d000340140030041306c51500c140205004002d0070141082e40300c0d590345078145281c048513400043d0040e881400c0200005000c280340148141c40214694a02a41d001c0c042d80614054100f04200101c4c400f0101d5000f988a1600c070060034803e032070001e958030300c031500c2540b1404084a1050420f0000280c03401c0c00401d40381031314141d8001c1c02c06503405030248030700500d140559405403901e031440024a40c80c0c04640041d914081c00c4104080380c14081440098000381103400e0455001090350741a1010400346600840c01c035024650f101000700d0f00890241c01a00711008241e003002051004000141c8000d100f1001980b0341c0364 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 368382823 1250 368381573 368381581
    0x310140301090302030d0b03010212010b0901020d0c030f2007080d020d0e090103060221040606050114031005090c1e0306100903030806012006070c0b150f06130b0a05070209 76
    0x107090364121580140036138810b01c14100140455009039407041c1016000600701041150980300d1000b081e0311141054500045034681540d05124150203444142004a00901c5070340d4000d1410307070341240d410b0801010140041c00725034402140e035203480c861002c444150342c441040c42d48490b420042040941700d0301040e52a80d03406200c09180000c1c000740401c805030720795100c48020758072041000559140b07114030000c002440104c090f001750300486000030b000303003044c00244c030342e110480741e48900040500800c20250351a0000e20240c50040e02d0038901d80d224a40301041600841c64500818044003001c00f00c00744000d40030703500c2080100d03550780d0300440c81079043e941000503020260005003c0400201c05502a00200d1501c0361001c861342000c1c54282c14850078501c0503942c0100041c803d444c2d0109000b228803c15800c030115100c032a400700e043c180014010315212000a0050700c0100b081e2941a04031210800140b200c1c100c034a54868164400800315400150f080b8891a8418081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 368384073 1250 368382823 368382829
    0x16050d02010b0a0b030c03091c0e030606040513030c020310140f070302041818060501120c05091003060905010216050a060c14090118090218130c05070f0303090206031014 75
    0x40f8101d926100d00d141c5075848044035041e4992000707007551818400c2c1d800120b404a10078440842c1e015581c1c0e41e268500c610720041508020001d0400e920803400d0506001030003064040302d0070310680c5800d28660102c02ea1020030b0421440e800e0183c4003a140001c03950301c042a1214072489814280907558140d510a04280e080303000301e008200d180c0d01e0400070710409180c0c580c0503603814180d00c180c0081400031603a50340160f842c240c0010905c426211000010009107000d41c0c0b01514044903100c5161034800d000c91101040e80c400500303590385540382803007400820343c100c5100064000d40c00e5814020f5090940e9500d250f02c3d0103c0305980f4000132070740c0c56449034420300b1002c001c1c4401c107441d040c03601c40112004201802d569151b495414000150000d8910044c0469000440ea203001c2d02da1550420001501920b8030082d020709100c0408501540712080361415a4800c01d01718881e6080d04003200140780c50b940080d042076000040c03001c5800340300792010845d03c2007405088070300214014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 368385323 1250 368384073 368384089
    0xc03170c15040302060429070e130605060d0b0109030803040b180c0102070501050c010e0f011b08010b0a1b06050103080d2a081537030b0103080f16050d02010b 70
    0x1020f801600400085000142072403101c030304500313035440c4017020035003600030202c2c0d030081c140e0b03e540205115600750021400d121580d03070341c18a00440100003880c513003004106144942c407941c8440d956642010345050380a2a25240519001080903880c0c1c034080c41c104000e4007054912004920280418220040c80094041880041039000e0507044d4038160064401c1c0d00191003004065488804018201c28204000d450680f0702c00004a084400301d42600d8200c40c00c0326043d410861210018008241c5407400c0b034010050a01d401c8580c0018865000840c8204060082007142008000414001c00f90064907410114810401416583e601e03405400c3c00c60001d0049000c0c80c03029000c800c0c60007801d006502c07030b0fa05100c02d4000e80d4610300044680120f0300101a5a40b01000c4184101070000e0a00c5c0516060200d800d20043c110748501c0e0411034140b0000f0310000303001810201c2150682d003070f03a400550400b030401003600300385080790300c0315020380c40d4800640c44c2085d000c5541c540219 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 368386573 1250 368385323 368385331
    0xf0608031e031e04020d02090406060303090518060d050307050303040309180204080a02090402120d09150215010b0a1407030509090a18020108090f0712050f070b160c03170c15 77
    0x40360315280344510f1100c07603006600a1013a603101882010210150f01c442d0b045a1055204480020b0158254600900b441005801c540d0281c01100803000140f8904003815401c09011695001402254502103195220740300000b13115020100034401003541140d0401c0640d0340c10b810f440d1441030040f01510483c01103215901c440e40c0000000381c05400e258003e1a0401c3c0003800d038282c540b8103050380918045105080b2070000d58011010080651142034281f019515440603001c06103200322a241000c04c107006601c1c1d2450002000c0207010300892a1944410100c800c82d074440e20309040c00307052a004120058010040440082d40014a034820b8042c02e6040e040d602001d18500e400441c1c0c500d500400c0000c6511401440140e100e004100000090440c02c87c041c51410b00c61418500b80b222490100110b68001c40e428003170b038100b55099031105007542c03441041500240c141140010003550000d04800c041c0092403101c00700308402454101100b00c21901e109494005005900c20f00321 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 368387823 1250 368386573 368386591
    0x1a0105220b01091a1b0307170f0d1107152d1103090d11011a040c23040801060b0304230f010e030403030905060712120f0608031e03 58
    0x182900300d12480c0c0380d10401100340e042c9030035282540c481290440003e03504400c2041000040380010165084507081010740c250070003d9420141690b4404991005c044030030b05c0c8007407011941c50306034821442a80c07600a2140e4082c4814603500c0b4007506a0ba100c000150b480705c500c2001c609449940d4000c01800505035182316058014600150120800c0101c00c484480e49035120001c01c4501d180c055406100c0a6014005080000402900321000c040b42a4160790400c0703005540c41102060100002000b0f48001c10350240d009030031100c15000c000703a038200d03018041407180140450000f510603141c00d075000300100e94503680c01100306c0c0000c0341c000f0b0421803242940744140c4411908030f803100030008101c50308007001910081c01e40c0c140c41c600703900350361012400b04241648141c034a030050030280c2e0558540099038444000750a0540d80550600c030505100310b5210125622070913100704440c5007041645c0e05c5180b015220f40c4000e584681c6c481d50a6918090300403241c0850b800384d0301e88 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 368389073 1250 368387823 368387869
    0x3e132705151903050708010b0108060306070c030309080405121501080f1b011803060b031c02060a090212030a031410051f02070911030f0a050c1803070906031a0105 72
    0x14020400889282c071903015102078059000400150104120806020654000f2402c00ca0b0600010101b000040105210398444000d010040360440c80b0000e8440d007519004c02c103241c00741003840702c5220f503521064005461800c0e0003441040415503010184a00c0941021a6038070724605a4a0b00c20740030014164200e00180b1401c0003200f5034920701e109045c102044814048105242101000e50041e1030050f201c001c2c02c1c03510700c1c041c8000300803c02d0205820f0820503920760003e5684a00a104202c420707aa1751065080d5900d00040035019402042240e98405680e0b40040150804d8210213840b5001c0e10003040150860402e0701c000c0e110046c00d07603c9112003058481c0c10b0810f5607181d59041d0300600b4004151050140102c8e5100380081741c03881e41d2414503440414a460000382a585820308e003000340002010307440101c0d121040001103a140c8515000300003400c08109500844410303140142c00030800603c01d20540c6140440d0340d007850260798078005d2141908001030003002d42055 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 368390323 1250 368389073 368389111
    0x1813060510050702031005180f0d09092a0201090201110d0503070c1e030c030239041103090a020316051f021f0f3e132705 54
    0x2c00c00140c40ba150004088986001c824840d0b58206c4109403480c0ca844ea1000d000b1aa09800401100d07500120000081048102c046001000080d45003c0c405801e5155a101c551340a0740f01c5083c0e00210050511200f607107808480a8024240e6190890108607040d900c0300c00390b60041010900303201151603440c6596145601144c518190003412a00c110700401050113407003003010306a5440340310b510783d21141102414081d03c1c007000d090b41040c0c95450040b050800340a8000c11301010102510282440c0c105040050050319040c404204084408130410900c030000050f18900c0034029416101894201840c150322007c0342d00810b074001841104160121a9414a4442559580c41696510200e192401c1c0304485000955401e1940750070f0024520819485000e03070340200c0800c40c0c003845942180340240c4c03659480c4c0360001a1038982071074a1040d07607001100e8581200c141c031040103945600c62640000101ca5580168016002d00f42480b80e40d140328880c0500ca0303101c507410180744 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 368391573 1250 368390323 368390327
    0x8010b1018030b040308040201031103090715050405180a0b1215040c030f03080403110a030c0219030c0e01090606050702061b0309040c050315030703080415030605061813060510 78
    0x2405180300101d0601c900c00040400d42c0f2031000c0740034034802c0d03445100604142c000101610200b4801c442d1000f420030501120120010b0380703404864a203c1c00321082c116401c0207840c580129884540c01c0100f2001d00501d4400364649a8130a0a0035501003292007800400d10490071040c001c69646940022200b580d02050b8681013a442849130308004150340c0c50381d4644050500d00c10085000c250b0f0f14050008054024540d1082030400c1001002e40710069100108480080030000c0d024091042c2640c0d600c2605c050004040c40d00311180d032245564501052599200034411560000c0c030b070681c081203c078803038801c44180540090440f41400710b040034074180d0441243c0908460b100c10050382d446c2c3d4860340101c03054814540c407025102c1c0f514150001081141c1c0104a100c0d801c020814000a10100240c40940b06d0300d40c014104031450400581c010161074110940c40301001c5034020490307154100c85d4001c440b0640c3d52000401020015070240c441602465600244001402400768 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 368392823 1250 368391573 368391587
    0xf14040f0203070b0d0e0c0102060903040302040504110d0807060b01050405010503040b060301060504050711060c0c060f0703020d14011e050603060f010c120323072f070b0d0608010b10 81
    0xe40020140d9006540d501c40e540c0c01903008140803201942c0b1b40010050385075050028640d624400e002a00b04da1421810a6407240308900000b44942d07500d1001c80c0a0002d01c07020b03003040400140c20070040f040a420320102c01d4012120840d8050300388010340342154410310640b022070b8010386540c3e00315110340c3d80310850964002d004540565803036900047c0c0b0f40c2c0c0c601419001d580561100a05c02c61b41640c224200a002003881d07818034020042e0400041002800d00e501c40780540c80c81d41d441c2c4542c14120080d00c5100c0004003000d041c48980b8004580800065040f0356800c0d00d200344001c00c032042e000000d0020b1040660082e81800007801c0d6040504911101c214149041c000088040da1542c07000032085121400195a0f04d01e000009812442184801c902c0150150894600848003d03c83d0f1031241e0400c007020041c0003403466410155800c0c1e1003090318401981c03421611041d641d0030640040705d150003840d04040c400a0381c40d8040c07090352529500600f0f402c142217403c070740a035914 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 368394073 1250 368392823 368392853
    0x240402101e080a0606050708030a021b070602030406080a1817070c080a0507270b1f0f0e01030c0c08180607060912052802010222090f1404 61
    0x80704010200808540d559600d0300c00c0700311582c41d00381c250b040425041e01114042d40140e41800390401145020440b0f00d420359a003c00180c00259075248441414540031b40e5520740d052803442011b001181594010000c2c20070740708540d54190280e0741c1c80c40420291090300903820788444444089902041c156000600040c41c1d82c1e03113451500c0e039035540c0d02c40c81600f07a506c1400c003a04503140b0b000401c01d0500c010b43c000c066101101d42c0c48004042c040300c0c0018848440c51070603540f20042d14643d11000340f80d182c1c030344414100d0b4414140030107010b044d0800c2d204801c0d0000c1c40d03605c0c0c80d206a43c00381c031620581c40036540c1e034a00312003c10798400f112607103c90b604480b444070034010b0202d540d5a810080070040c1c410540450500d00310b10700031220310604659003050000c280700780c4402749400c2c01118030003a82d0490307100300d03401702070b030203a0091141488040e2080c100040405502c013a019481c070403141c0b01d00040140c941904084411583c0031400d403c903000c038550208010625215020034a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 368395323 1250 368394073 368394077
    0x30a0513031e020c130e0d020a020a0e0a0b090c2101290412054204031812050709090803060105130e15090604151208040905070203040824040210 64
    0x114045160005c1c11100c06a228550126100c03c4250a486000c0c014030030008010300080190b2a900c0d4002100c1d111180609040c0c100c4c010006190030009400c100e09038440074102000c3e600381444507504591191250211021f1003000f594800e10b4151f43c1e0b05e0403508510441e101e2000990503c0b41c25603d02c0e080d85074904402e01010a12508401c07401110f60f10480082503540400341406e180d0030030025038080c0a02c0900c150740f41c4685400c07070004045804800e1580181c1d103516040d160008000f28000510032000710100d40107489141070070f5140d00650880703844595400510080d1240e4240041416405101080c500d50088001e40b280251000c120b10009450341501030801c6811034554010b196450689405410b00d841015001700003a90240b0050803030307503c01d40084c001482080c00c902c4e104003402d820700402c982035501404c24110184420709081030025503e801a0003050440d00942444c618085030903450702030502e0690b810082503540d1602009191100c1c8458001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 368396573 1250 368395323 368395333
    0xa290907030c0c0506010605040816060c020913140c0a1205030703110f06040b1b0a0c0209130821090f060103020906130c2d090e04020a0302030303040503030a0513031e02 75
    0x20018134103018050180c206951000d03202c0d45098003603131070035001da0608044158541c0c0d052040ea5407000c400d290f09074041d01d02c0071141d140d100100850b04030f1030401030a05030340803a15114131000420381c0310070780904889940a064076900b8a4041d11040c0c1c500500e254410880540000e01030080660400c09a0040e03400040c101e49481e41440c4003150201c0791464a00f0070422502090410052503080b4081c0c02070811000d410003401c58603c01c1c8010b881103541c54001050601100e101b072286a0b03001107813940714549801c120500b640d881015402007000003000490240002441b8451001e1500003450141d02e15001d00ca401400907002c10303040400c050383d1401807015400380030984030441d40c0e90403010b209008482c40030103c060200352103410042d50311445e01d0f07000d1040026510707150308801c5291590300c005120365000750f00c0250940000310800050103000b03c061031080038416411700041e07490001d121080c1d00b00c018010081921001d04110b85035441c02e0b54011040b0900440d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 368397823 1250 368396573 368396597
    0xe09012a02070e0c030109140103081812030d02091804020d08030a0212071707030203010b120a020903060f040606081204030305180306011202040e01050603190503120a290907030c 79
    0x2003030f03480040300d900103490700020041100742054800c0d10041240a502d545480d41035950b0304000344284008500b001890f05802e00d442da99400000c40b00c00c0020742140d68422000f90994040e410201c4206c0c8181e000c0c001c3c1002c0b1884505025105a03401880800c407104c0c95502c2c0c0d07185e904054080e00c2c1c116070910041c078850f030301d0f0125240a01c4064076003402070483c2d00040a61000e0003411201018014170042000035540740540d110705121030950701841d51030b8503540c80203000384524150b05118400500a44c1c00d04102032a00030b50041d0410b000082d20380d440142c0d02c04140c914a20341c0c2400300030410200748101c01921000c01d10035407016882c2d40e4040040e00e0040203820009103040c00d40b00603011441c1600c601c1802c0c2c000d0000a02c8203103000400240c43d098030070035201350325040d040504c0400c9001c0c011144600110003900c2038600702541044000e100c10f00e0300c1c1402d01c074020310342c40b050f4841d22620307010710750010440c01d400d86c0c0d54501200941100d00000082c07120710380c165 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 368399073 1250 368397823 368397839
    0x8060109110a050d0b060d060302031b0906010c020f03070902131505040506220e0610020601030f1e0b07020606210601170106030b01141c0503070201140c030705070e09012a0207 78
    0x10604007e0011001c6201c60a500401d401c107000b50300b0720250b407101903003581910317242d0008155200000b42400f06440d04c1e0b9001180350007520543e0254180109a404201a51580e015104080d0952100100f60340c80325280d151002101000e100810024402041145002802016050409041c049100185c2081e140e10241c06411940240302c0c54410403080e4104039040764002c5401e44000d1401d03502d0b41c0c44680710b030090304e00b01802c1c20702d070340040c03182c4060002c801068540c1d012081000324a01a4002034840d5000e9440c14865994030b00206d44d00800b440711202e250207004007030a0940d2a2002e039181152241c0425038081d5203d0100001140307e0942c0f0703e000344004108085021940403c0000290304040154408407440e0310313401c0440c10001c02d94070400e60a0811403440c0e092419194075a0040001c00c40141c80300050700c3c4204080443c46c5021501c0d41c418500d070710385900165509883c3c4407105001d500380107000134501080198000d4101c00340600564540c241c48280b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 368400323 1250 368399073 368399077
    0xc180e070915081b0403020f090406150608101203210f02040902040e0c07050a0b091c0e040c14160c05060f071e03121d060108010608060109110a050d0b06 68
    0xa0070100390200100068000f01d540300b10013252500141502d428119070000c2e52849411040a010701c0354280010100119580300d844c0013101c1e811281c10f940ea0b5100000d044040840706c0c502c02c0e001c16080019401154082c8102039540354640740310b150405850824024a6140400c0e5110f48417a09011501080d100400203043c00810144e0b64078240b07416040502e03000b60060134890010484000030410118800d2819a8030095178000c42d00c44c80d43c42ea2812840b00c13050350100307000004400929030480c2011840a1054800740600303902c001c4143c510b21401a1624120740040103142c0c40709100243d13441701144608028600a074982010806c290054140c05030092030000724141400219540c0c00e1100f80110340880c90048155401130002c0b0011820154842c1c443d5207443c1030415504903090051140303801c50b85150b07502c80e1340340d028040a04c0b072041107000d28000421220b609008140e178210300c0708205482d058041d082251268008000c1415496455904490642d0b0f0040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 368401573 1250 368400323 368400359
    0x4050a0c030e0a05121606061205010f1a1504150315090908042303060a0b0111060903031305030c0a0501060e091915020d020d0504060c180e0709 64
    0x21000486500c1040c001d01103036148800800141d00640030107000440004c0d6415504400b0b0f0a0141c50310298102039010846040000340500d0907c003022803040740000d0141100c60094009000268691000c04100d070030b01460042c254061210107002c900740654900c2d82c0f5584030556500d025a909d400200002c03490001400103622010b086081c0782002c3e00b01c07400b421001500300008802980c3d00e0840344038074840c3d15040c1d00c3e22011200401040c0c0e00780b00f10003e0140c16100d0071700d0516941d0f40208090520b6501051803008034241d082c00002e1018811410b000c019840c64403400c0c004a10080c024100715000d110400031a1a089818000d40c4220303407103400040381d41d074240f0401c1c04034120700500340ca43c0380c2d100c40380200c03000300e801000188094210790b103000d00407110003c4e035020384070722403850310418000191441011840c3d40b14a20442c0a018200320742e8001700800c5665050217010000c0d41050a001400580280e10700780350040417600f84004010703520010003003142c511003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 368402823 1250 368401573 368401591
    0x1e08091207110102070f0b0306150702030d02150c1809040203010608071e14030d0c02130c051b01060608040b130b190606050306062d070f111f0309020307050405 71
    0x140e0704002c0740d60108101d6018100503601100664113104070b404a43c08014412441886441c0030304121954440451300256005025941e04d02c4c14140003950b29085a00d2174074080034000009452102c01a080d1207080303e81c11280700040009000300040000c02a0043e40c1c19581c0e250001441a020030852000f44400281140000c10108081400d000c0aa000c00d050300440051141c4540c0e012030401c1005005041c4221086142d002060328044140c804c6105103282ca075004040940100c05032000305460140410064000702c0070a007603c80310301c10308011502160200d8006009990b240e07510809100744005506210b455a074260542902e00f010404d1511545900d10120342c01a04040e00141c2480351031800c209020844a1259107003450300240d6204100205070400541c0c0b210900e420220b9130b032900210b0030401242e01c405402152001009542d603445030070207140400c0e03a20708401c001c202031194620300307902601c4034040490340741c02110008945565a441014043c248078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 368404073 1250 368402823 368402843
    0x40f0612030e01020309280f14040b0a050a03081606020a05070204050603120a0507030504150207050a09090b0a020c0c09040b0106020d1403070302090604091a040c1e08091207 77
    0x141005000010010b58640c119042003022003176907102c6103020740c40b8849000060a11200030003501070040b4998002038891141910b0004041820758a40c05502030211001c2000d918044104681321109101e03040c1c0101c0c0050f41040442e00550180c000f40303044080705101000b1a90b1401c080780d000e603404c0000304001184032015801c0510415a1080e01900201010090100101220f0080503c5801000b00000f040c0d4201440f031001e8078000c040801101448203250107012b911106640681401a181603c0008210744103000e2560801c2d0400314802090f1224080c882c0a5485084000211b1190042180703030b40e150408000d1082d80640001c10707c071f50404174000d0a01d0076031001581046480742c22400079200c90001c0703c0c0c10001c2405c0c016a1070300d011001c60714a01555001410062821903d140c2d6140c00f568800c0111000b00c07020403110900704c0003915444051101c08149902d03104240720300900480c01160028600710896180c100e0115a14000380e00c0360342e0480d204229 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 368405323 1250 368404073 368404109
    0xb010e0106140a0e15090405010315050916090c03060b160501150320030a0b1f0605041d0402030c040e0304050f0102010507020303070c110612070206010501051c0902040f06 76
    0x3100580c2407248803141915031a20051020090483e00204452440b441940401d0709a184080c002c81b04e494a01800a10407507135a42001070b44852010010f2008900f02400140d568001051101c82c0440c2c86400d150828200b02c019001410034500100034159940b4002c603070403d18401602854508600c002c0b40586280f4004d4251905194510340903040b9031000e2002812441c822000070103081101e0014420160009281041c1d40c400030304803c22040031301005d01080d501d21845100c0110001036866520142101c0070320aa100355070019032005c088031019145180c0b800c1e08140020b085801c20b00c40480064121285141c1d842c030203501c000740401090030a051002e013888002d00081141d0b00d0010800b81d1244001007a5008100f134902c8030104002184111211005018240580b2500720304034040720b0003c107444a0700940b0440000042561140c8204c1d0400101c28410341101e00d00318040c60b01400c4000d9007264001d407681c0c2e540c241c82d4101d1181400a00c503141e42e44c01c803841 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 368406573 1250 368405323 368405327
    0xf0c08041d1b0a0c03050c100204060518010c03050706020310050301020c0a060f0501050906120f01050a1410050619030608030703020a0309060801050d0b1305071716031a040309030b010e0106 84
    0x40c1c1c015281c590b403428800302405070742201062003180e4150030045d6a844600c0001ca00340710340c1c3c410680300244003150105181d603000c0c0140400007a16402c0b040c40039011001920325030081c100040c00140208070960000300d1b0768020715004a19402e4011003607850360002800d982107418880625071000d403202091003000c1c003408035001100350041003694101400300b111000010f1000340134030048004201c8045040020b040d0706107208008201e2410590b523a10f01601040000b185000c4100000c12031402e000c00e02c0004540303001f4500c0b4030702505803488190190203003640206150350b400001403109401c0c0010911944664003500c44200c0e41d143c00f42003402c46411038401c0101c0d0700018410b03502c0d5008182c10442c0c000340c2c0c44941399994042c04901c14520800208a8000d0540004035401c0841c1c2101c24011140b0503512000035451740c03640041d0306407001500c04200c003040741c024207003180e6080350401d0003490301d00d07806a142c3d100c404920708207a100000c000c3c00c41004101950b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 368407823 1250 368406573 368406601
    0x4090f21030212010b07030207080303010905190c0c11011b06020705060f07020703030302090f0d0b0f010515031b040308041d0c041503051f030c050f0f010f0c08041d 73
    0x200d10303040450034002d080c21100c508003c14051900010300028400702414000c01c4010014800c007000c0f01d50301d40e1a0742000000e00004c0d0b80c00c0604040f8420800d1800307e082c0145814240d00e030b41c5100c0090404d40b01d100e404989034590300c0c140301286541180060545c200a180c0d180a0f410241c7e407034156142061609000510030452014090300380070409502107031190803650107190240e1102445d03800110206810080c1a074030209200c40007080122003124135201708038000150784d05c0da903203405109542881001442074060f00304005035120601404840384010950403c60810f42c49070350b0625503910030b4001080089020220609444900389000c1c3c1c490f440000751820549482230502c401c4181401e000141034560001803920304003041c030092810300d6540c50201e00b5940341020f410850302402041d008602c4001200d07964102015160400041030b52981000010080c0440c0d034000c0d184011141e40d203040200080700100c07071102e60729903800541105514146003074050580c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 368409073 1250 368407823 368407883
    0xc0f0604051605011707170403020d02010b060f120406020405090907030c080a08072616170f040302100c050a0b06031e0303010b0a090909110109091104031104090f 72
    0x5124142c1c0a10035a6444076102d444000303001e4900600d03448058041e90301d04454a0055003010f03605041106141d40001e840441d54925002004400b0002050001034801d40041c2849000301300240ea1017040b403640c003540e1190140c100141080c3d00d400011b185031009840219865100e030710203006024945000c040140042070080600406555490130240135485010f05002031000070303036909003858001e0b402d800d2801d070707031080e41d40150340c41c00300e801a0200c106403540c18901d9210f6000c241d40c1003c4a0303000d4104120076042074916800c000c0f20310a000c480c2003c0062442d51040010001c00030b41e11000e20a913420341591514a05142c5007402e951907402c0d200c141c0203a607150325a00442228159500320f021030b0340c1c800e081d400c241c40220711039010000407841c14103070409205c1c00c0700c0c0000c545e680c242c3c0c41140780707903032080542e050300d1102c052240110750030401000060422a4003001e051000b40020074800f0041d01c0315068204044820f5505c0e040e41e070b038544038144081c03030301c01c4107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 368410323 1250 368409073 368409103
    0x638010207030215071b03051f14010b0a03060501021b0f030a0605010b07020909010b24090a090b030c0a1a13030510051603180b060d080c0a12080403170402060c0f060405 75
    0x1007495500c85960b27540600b20a040d40e104003007007250f508102d80e002aaa13a10040c00e2400031565214810b0320540d20841c81e00f40000e191100c089001d41c8041030f103103481c8403003815074042c1e402c94008010281d00799070078160303041c070640c0c0241d0000b44d05402114000c004286a503511600180103010403080d0080003880c89914140740d10401c0d64842c82c58180c240d5210310a0204c8213050a40c15082d0b00c42c903001c09a100020440c002a4038980b900040113040d019000d8900801404052081407500c0307029000f0a4a103903e83d00c040c900081780540b40c960a85850117640c00d991b0b0b1112802e0103e00703a806000030381c48a0410003603807041d0801c44044240d902c0d040205011001200b0350304981c81d20f00030a04c542d070f00c3c04100d035660781a80d840704007500411425510303290100d0807a560700038200d0848a4540144070407081c0741c004c861300340c40f4070b40503120281c0c821089110303020310b800003d0080382e00502c14031611402c040300f00003034130381820718030010016800c003800e0041c41c00c0707511b00e10100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 368411573 1250 368410323 368410373
    0x15030c01030606080a0c02070b0c0f0f0d0915021f090512090a0909020402090303040f060f0c0c090c110102041203080c0f0901050307050702100c063801020703021507 73
    0x182035403107130080350310668000c000160046004012400d119280e440803003644004580240f6110010401c3ca15010384c0101315644103410910322a12400080c0500d0049104140d04110b0702101004142281d042841620032000d900501030840d2400f450346a41499910040c0c0b00401a04014440c44c10388225085428503410100040c17004410780520580b10391606003010454566030160754840c0c1d801804c1e01c0c1c0380c80e102c2050300603409580c8201000a07044490070892113018481088030300c2e03008405188110f0500c4201d1000c1d004400b040004c01a0241c400350b6450340a10141001c3c041c400612044c0d2440760800070002c04010b03000042c021401c02c031250b4030302000130031144418000c0c00c066803a5510108190f580c1e00a0080c065002200301c09941c1f02c841c1d105c4841e03048944035500c00c002c1161174000e00c07007049e214082c5400c04c1410f03c1054859003541500540d2401e00148102c411442e241d6011517541030340305411600104010620008004400c106818581742180c8914 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 368412823 1250 368411573 368411579
    0x804120e220b040203040f0c060804030215070203191d0a0e040209190e0106060f030507020a080906251403160204052715060a0f0e09031215030c010306 67
    0x140315003601e400d024008480c2007401d10a660301c1034100204201004104540740d01c2c060410040d0304041d1501142c840202c0c00011507a64007500c0380354047d0b90580c2c003c0c0030079001088a0b406000003d04140150320003402941425000401007001d450042e5540f101c0c1100c0b14041e800e100c02c0c9084136644119244402072203404140c10070b283d40309404071404040c940b12651b00020300d542071502a04820309000c00170b1003284054000707404441d00c9a4030071511a42e200803c90455000780c8a90005070801522000400d210300c001d4201620014200340c54402089524500790810001d010a0002c60312448418000015400340300c401c0c0f10b0000d107143c00010810b1074103010314030600910465640c000300f9000e900e4040301191016440008201d8030a094030544c3d9034502030a4003422040c0e0030400601070342083d00040040301c001e2142d4054042c00c005c41c00710103060041c4a0240392000340200600c1ea44d80704803041c040c01d0800c101e002030414110a00d801c00d40c1490000b410b040c1044410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 368414073 1250 368412823 368412829
    0xc010c030b040c0f0206150111120405130b0603040212160807051002122b0e1b030c060a270f03061b05161703270109080909090f0a030804120e 63
    0x7183e4030201004618090045d8040189c50440002294801c0c5102d0804110210418440200f06581c811245016450340c24289402500e0000d540140c10100a001140060a201142c0d01e00c50b10313040141c60502440b0341b06080f010000b80d102c7d0754141c0c0581c10400181c1080c1c030740c40c034140d807091024207039400d171241900d1058412210000f000c01e1080301e1659203c00e45000741e250300c28180800707000d03500320005004d580c1c54031021481c2c03080f000500f40e04079074900081e1104045201070010390904000300000e4500c10103544266801c0d41280b181c8420341d03500304c500d140c064011000f5040c40305040d42859012a00002c0440021401c0080f0810425030088169000b001d540b04608903080da1500d40094040c03002126510315034804014003503d180d4901910340c01c01ca84400d401030b001e0700f1040190a0300c0c1035030006094101c0401841c05142000c0600c50741c400544002c1312000b0080e64840d514050429a06400240e130f0007091104000c022140d180c9451858903000d04410440400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 368415323 1250 368414073 368414083
    0x90f02130b0723030405130c1115070c0204062412020304050a140f011104150306031101050c070e0403020109030806031507231303020f0604060c170c010c030b040c0f02 74
    0x9400206800010f0411540c001c0007154003401028000b445143d4040f014a000341541c0425500803580255400c540240d0006400701d200c90081e014841980f501c00003540c4241c01301d101641c00c6901d074140481c4041e43c00c42e16428120460320a0403044c602030034010403841280303102c40000e0740100140301c0410030019058404680102042c0b03050845d2040b1a0324210100c4420f6040c0e50a00510711756005101000c3d10890b0b0900403c0748110782c094004030708840d418013005009422004081d405944520042c1002c200030758221603640c4d03280c000d514244030381194110300503915501d840c000c05521602c21074000034160014110500d440003000a038950043c500c40c2000586180008145010401c844664000c013a0003a542c1c103550043d1a00c0c0c080a00050740903800e12a0040b007076040c0207040314116402d90341c90701d0a001c92a80c580ba0503510203d08100600c1040c8000303898240203124406804016480000311100300c9014082911041d2034804103100a20710038031a1b154022034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 368416573 1250 368415323 368415353
    0x130903020109110111060403050c1915050c0c1b040b0306070201091118190902060f0a03060b070803060d08040f030803060907090503120d06090204090b0a080c130930030e010b0612060109090f02130b07 88
    0x10486400601440470030028102d0111442d8103124220501c50143e13010f500c02ca059502640c40c50b40c800e0b81c16000d000044908a80c0c240b61582c003240091250b8007800304003180201d4071400810003e41c10740005a0b19000480007030006d4400040c01102940c05200384002081400c142d1420420706460300c40640c0001800240a5010410080100310700320f0200c6010706058984030390003989a00309a80960002c0710068059040007000c283d210340240e1840040703403002002000c10460340240c50b8025088800308000c0c441d110b1a0114402440b4000382002d0882c100740003a050203034a00b000003900b2181e00c0300d503254114001c0e04010b5103070b00c54801b0401c040c6050226004007585010312102d60800b100e0184016a070381d0660101e02000c802c2c2d1304100c0309903414815100e144d0340250894100c4007641d540103204200690806030801c80f03e075400f48050601130a8581d0342e9a4050540d429402d801342a00d42c000744584d104001003000e0405000d118031228103114041c0d8400d5481c0407410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 368417823 1250 368416573 368416603
    0xb010e010804030e03030a03091407032109030b2503060302010527040204030f0b011e0512010e070303030204050a121a06130903020109110111060403050c1915050c0c 73
    0x3800280c14103024081c0200703801340207421207560320f940742c0004000301007980d000c41e03a49080084007085e00070002810300a50b904031008550300906101a00103440000341030b101445200080000400c400d4011640300e41043d020801a5a000040b0800d64902e0400c020b400d00d450941c0c01d03c0540d80c01300640d080c110f561050304601d0341c100e61078044034000c041e04240d4001d00020300842000040244c00818a00c2010700350f0f881d0b622101080403c07481010901c45801d800340301009a482c12a84907544c40607041c00000d00300c801a1b040b1821710800b50819004a80c000900b0000750410040039001802d40344003500c0b00e03d482d9603131010308030340c0d03101c10042000548011401c150368036114aa1010403141042183c4079036882e0184c040c0144000688048a0724003a02000c0e50080b100380c4088008080540540d40e0340740c3e03041d41c039900f10040c402c03064800e40ea880c100744000054070315221800b50042448804189203e00f0a40718000c00a0611240500103100c42d0540014080446800710b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 368419073 1250 368417823 368417837
    0x1030b360705070c0509100e09010b011b1101030b01030621020901060207080709090204020c07271109460906030f080d020d06090903090605031e15100203040f05040b010e01 76
    0x100710308147e2804941083c082070081c1d8040c040c114105500c4503d4240082e01c81101003910912204000da030034000240c102508000b1490066200c0e621a0200c80814140024201e4891171814030700d8040700070108140086900410a40c40d25403001070052106200030035045040400480d10b030809481410740168452400c0421580c55406075440d08001e40c0031140c01e280d5910540400c48908040c00400e008010400450344040f0302805403405408006180b406070860b0601402c04840b18030000852212690b541c1e0036401320950004180076480c52030300e10041038104280c03003552680201c1030701d032400104100140b0503000c8880400e0700f101d0b104e501d07801200c6d200300c041e04c5401c082140301841c100d004100442c583e0b0004074414000d47e500c0300d174030b911000240d4543c80b05403140000b4541d001101305080035a1005a58003407a083c0d056001104094080349103904075a201801580010609002002c00c41c9081c0000704011a0103110b18014900007030403203105855030904005072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 368420323 1250 368419073 368419081
    0xa2105060a1202150a050a1d060306121c0e04050a0b09010e0a0b060403080c0c030c0f0409030e090403050a0215010605180d050703150b0f03070501030b360705070c0509 74
    0x2445030400e0389100b066580303580e0303640d000c0c000401545c080075548000c08d500c02048240c0015031b43d2491200040680b4282c5992242002c000740c510004c0883c0203903110b44045521031448500c0410340e44000790719055581d840c030204020540d4402803400c2113191030f0101607201603440044041c11030f0321410450b0881e40b0340300c10a2000c0c2206502440d017007000003800000f04200400201003852052007034901c0740249000301a02c0e265071001065114641010711890780c40c0a5200452607842400c0c4140c007079581c8004141000000c607000c0d40403072408038032404c4882d0140482003460082c404991055070400002420a004e00002c1d080201c00d906101d101c6a01c1d005100f41d1040d4000d02164240c5589291020f400707505550706038142800c144041d01c45003030540c10403100c800c0080190040d0790402004500400c20480f060340d001c196111109664269010603524803072104c003403035080b60160190000f0008016006004004040011a0100d82ca41c641401603801c21030b42c00e151915 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 368421573 1250 368420323 368420329
    0x50604060b010c061a1816030209030a06150510170705090a17010501090c02010207050c1215040606061d010e0907050c0f01022a1f110a2105060a1202 66
    0x1070b48000c018030079850709111a007002d140c1e5140f1103000708100c03000d0054046c3c1e001030314400749050342e070640e5418a2000d188012130084d0040c01d84003001400f1107140038555101c0750305651003140744a40f540240c3c1c4007800582002d051807250704480e41000c03d60002600140703001050001c00003010800085070030192941c41d86560402044c4842403401034481581c48a40203050a20030031004900c0d0407031a480c5c81d40180240e4071100d1b003290161400c2c01c00c440500030b444450b001d00030814018640f034400b20380e44030352801d400b640c040d980018040d03040c00e10251032030b06169401000720345100350000460780d1040409059040c1039444625031b07203640f0010303206402150302e0010140103909070f580e4120300540c080e000d40030121480002c1d902c1c40480c000c000202404000080b60401c8030302c00d4540d40200c5448040070b01da0300000800071640444000765800000080c400a0400038844100ca407100c1c02c0000303a040755010030403150404d007000034240d210b00c0c8603003108044184000d5096603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 368422823 1250 368421573 368421587
    0xe06091f020702040608063c100e0c07031215031e02040c0c020a0e0f04230d0e03010b011403130f08030411150418090602130303020714060304050604060b01 69
    0x15501404c00c2c00740310b0321202041e4482d14100c8008416004500c400901c0300e10107222440001c02202c544d090b8140f00c8890b089000034010001c3d544882c0c000e030001245510141054402d440001145461b000c043c0780003090320f41440e05000d0300da41414190440d090100c0035610840398414020440c101078490031040a151820010f944a071824400c4081c507900300e500c140d145482103961288031900c40050a820010540d2180e41580700800028001070300c60303403c10301c0b160700c003d6441e0003042102615440c1c904905860400a07020880c1058603007801d000c1e02620500c02d080001d04000310b011200d810380401840248031a01c0381150a0a12100a200108861f0450031290340c03458241803560305078034014541c40c0101c8d050800707030071403c441070141c8099800440500000010301c01c00740d000341464010507900301d0307402c21200031600924040b21000358448d8002c0c1c0300f198070304400c4011118503400d00902400d41041080000350010404c1c0c1c0c1d01131780c0040001501420800121500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 368424073 1250 368422823 368422837
    0x6050a1101180305090301060504020c030322082b051e282a120506010e120106090605031501090f1503081e07020108041104150b0d0e06091f02 63
    0x200501c07040c2c841490303802002403510320003da00074401141e440382444228400c80300f000e40c10750011700101d071504090078842440e440550f521128082107503229004190f00411104d1a00c04121000c0707071100c0e410580b00a20420303030410030070152030321281005010000e8810b6403d0b66407400d001449114480718404040340f8012114545044002900c600512030b1a10a03103010f440141c44240b100c3c003003e01c0c003007511031b5070780c546040400300c1e90b00b8005000f0241c03126041c031a41c0104000d4648649400442500c42100085041403402040d1401c85400303400080c040c0e00300c1e88070403400c50464403103607044440d1000c0c00207001c003044240600030880d600100c2e600000142002061000c1e0344094803004c02c4d01c503200c0003155030110310407200c0c0c440c1c1103000b800320305450009800301d100750030032140185000e40007060304814405000d40c00e28168000d0402002e000c00c0c911200202441108a006484401450f142c2001c02c010b40d903426031038100780d05001c14105124103107540c0341c06039000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 368425323 1250 368424073 368424101
    0x6020d1a0307050604031a06060f0703031a030d0c0809030705060a1119210c02030f071a130e0c120a050103030315150f022b120606050a1101 62
    0x403002100030500e50003240c03030118510a01c1490742c0070600346495404c40b4112a070040001380300303000524040000c1000104010f511103014442607c2c404020310060016030f00c40c0d50002100411004143d048224107100b42d40030354418403007603281ca0b411900c00c10401740c2007004103072507566800000c4d10305806600002d403c0716010420408450f000042c0c04c190103450002d8441d00d2006c3c00c0c0c4001210000c0030081c005421038101c1c82460010074402c004802a00c0c85c4c00c110404550700841d00e0501d00c00707901e44407070f84000300030071600e90007400280030364038806251880d03c840c03108800403204250080c2034404800710081060031420320221940300810a00350700d101d03d440d406000003040309200607004207042100c811041c038407405204068442c07180ca45000b0f0b0920f05400c850030300a9500200540c89429484174008034041c8501c28604002000c4940b03443c02c998004140d0040c00303a000e0b20b03403411b000e81880341c3ca40050070744a0040c064a4140207150103401c07964050b02c04541031440b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 368426573 1250 368425323 368425331
    0x30b0a030c0803122a0702010507060516020c1903021903050d0e10030e0d080c09090408180603010f0b130e0f06030d020a020303090607050109080406081512030702010c06020d 77
    0x514107034040042e00818614803152203444d900d0166005040c80541740482c0078490740300c0001441d0000308080c11680740180340050400b400c03030752204101c8100781c0d207406102c0c0f80b400500d21032a0f8100100402c0c1c141c240c03030540801420140130150440b0a01000f84118001d6038000074a29942000b034000716003010845851f080c000801a1941603017078026801291070318000741f081030080c099030310300f0440d180092221203140501240c820801602c2410715803020482d401055440e403602c90302a6001e4140d16070f035500c05264110880b22580c0000d409010180010846403203d96160740c04c41d81d807140d07415500c24540030350890180050708048140b16a03281446038154001421a108100507401c0300c60f150a00c1070141e03a100500c00c002949030340200203840d0030741844400781691a100301e0001c10280d426980d100c0d89a0015001100050b8403c000c1003075034800405c04d06184641a18019001441328031683d032248a86400a41400710507230080c000c05c410f55045841c00e49c40140d00b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 368427823 1250 368426573 368426579
    0x160309080f040f121a060402040902072009040512071a0108010506011215140316030302161406030c1308010c0c1502091f02010906180b070306080c01030b0a030c 71
    0x40e140b50403600800d00c83c00710104020410076401c0074141c00780c0d80c00241082291680f200d041e030000300000c00040d04035400b8000000d0200441c00035001c0180300b224410721641800c0400451452012001c910405840302071002144010813800c60103021030400d55910313205828201810000080c20481c0300e910314000040c08072043d4000380c00b0301826070312142e40310104003007074003603e0080034216082044810100001181d905403c1c050b00005001d45950f2aa00440a030071203681e42e100b03802581060141c55801c1c1c24007102440580100c070302d01d07d12340107038501203405404020b06d41600c07640001012080b440c4551401d00040400300000e08c0b002c9111030000f005050500300c215501030198036012031040040c0282e0700080005091800c0501140803101e501c08901d401c2c0c4410355594050050200390280a86058110304494100134108281b50103003000500500d01310030145044000e110100012800301e50301142441d011401044903000070341c0b880c09592000300309464a003000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 368429073 1250 368427823 368427847
    0x3090c0d0b010503011b0519021002030f091207030c060b0f030105070201020a0212040e060603060118060203130510121a13091b030305030403031509020319051005010816030908 78
    0xc0d07050f107506030001e11428034100c2c0c01c03042c10045919080081603003400504501500540c1c00c00c40030301140304480d0100020440c21080f68400e68062261101d400c08020b8030360001c0015143c41c404202445141007101d860091070a12042c100800003034440d03540391546d940c5d114140e0041c45005008000904203180d02a0003544104048005802141c12600506003201c06940c00c8a0300600c040c1c0180d0385400400c4403036407008204905125041c5203a0f503038422010080d10180c4016001103696101c000d9100085d02c225601c2a44283c0c958540d43c01070075804010320003034a846401c040b40c1c110316405040b03591114844a940c01c070380e030700310f034042440d295411040c01c10f400349055007014008481c410181800d503000207000b044041000c20002071003580b050040c810030303a52556089841751122010f0743d00070b94044501c01404c02c07440042482d280304051700000c141800040c1c0c1d03483c1c0000070307110020082620100e02c0c0c03030111462a06001e600f100540680c810b034200e0740c1d640c1c0182c2c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 368430323 1250 368429073 368429093
    0x7050c0a0b03011e0915031203060311060f0f070f0308010b0a0f120f0e07030b01091401150c211107120611090a060918050c07110103090210020f06090a120503090c0d 73
    0x780e5400d105138041001a500078420ac40503aa040042c02d0003c00780002407100315803203400d42c0c9400315010010041444002c030050031700140321f1401a031181c10341c1d0134010200c8406801200d407207801040101c0c4d0781d030340100300141c403070441e42045001e01c00100c071144000e0a03450345241041d824030588608260340443d0002c2540d210b40e02700f80a84c2d0722109800110340c80c410244126084020060207032244a4060200d044501e20740100c4e2901c2c0c9a5641d00310643c4001c1e80c0700340d8660f94a1000000b90065038030b100e0f1030203e2004001c503504c2c240401c800c50700091000703007510307560b00c0414215665010440302c0c02c030809410b0500059a50900420102191040802c8a48625043c100021a9000c2d0310b000d501d0340c030580c508106407510750082d07450070460110305050341c80c0b42060050322000c00044803007241d60050841451520041801d00e0320003414040b40c0d030801c2200d1000540c00c5c8071a151001c0c0607150003616903483d08800d030310305034080701503550111550400c2d40030416102c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 368431573 1250 368430323 368430329
    0x90b0114030c280b0d0b130603030203030f0c070602040902030708090109030816020f0615030d03020903071406070f120f09030203150405071a07060c030c0e0f0a030204090807050c0a0b03011e0915 86
    0x5030030087c10714400b86813000c85907140802070060f0410008914880b07541100590403184590354a0315004d4140d8810080303903c107034081c0c03900750340200130000b41682112109a0040340d00000b44014042e9640c0104580701c01015800c40e07008042d0301603140c41c4200082c01503410090111082401c1880c01d00d4500c0010641861180c410300201d03261192290080d00c030700031009001441201e040c0021502d48043c02200f0b26003094050000c00040b404e03104002c01703903030300a0010704c0300c42110b00c10041c01c03c000500c0c590203103c0350303540c10001a200000c3c0344001c400314040488003a00c0b01d02c0d0181c14901c00381d004042c44030724a81300c0c0000184c0c050040490a1048104015a0044074000c1d415901d081c282d44002c2103140ea40301425081102000b440b14600038054546581c9946c0042c084032a4980c0955400c8400314000d130800c0001c110b17500055508a405c81c03d0f044c900500f42c1202e110500480a00000c030342d028402d4182c80880e0f00c0c0c050082c030b0205001761820a020310402c5480381c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 368432823 1250 368431573 368431579
    0x605210c161a06100801120602091305151207030f02010e0d0308010603060f060c021003110a03060f092a0311040b030f0601051e03090c04090b0114030c280b0d0b 71
    0x303400308009144c001d01c018801c00b0f040d1254003241e80b030400704450030381c000c250943d402d907002c028070070342030b52003108114400303000c1a0300003001c0c180000c50242132030240038246d0142c03070f426528030000c80c3e00040100c107c0e50b1040540602103014070049680741c000600603a04240810400d80415070031415860507202c0d0f07550100161a542c070f022000100d1548070b0000843c03104021800541420200b48504400754200442c90300020f08803968141d0200e623550000035903520052200d081403d40003401441c040005104030901d144640b13103501a043c1009034003009008001302c0d5140282c0051410390b4000f00002e444a640e124102440d42c801c50300300d0194100507000840e198080c0003640d044881c0f09500d81c03c0049030118802c0c4651000d010404188100a5540460341e01c90042100c8244600400780390365151101c1054184c0c030a90f500c0c0d201e43c10a402643ea20b0303e450084104048464901d41c96038808a4551200014150080751f800c100000c3c01d0102c50303846411652545a082e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 368434073 1250 368432823 368432873
    0x40b0310140d031704140d050901120b1c140604150b09010b1c020c0105010602072c1302040216030e030d050c03040303080c0f0a090504060605210c16 66
    0x1801004402c200e03a000040c0480c00c0800350a2292110040107076000e48111003c045140140e1070161802103c40c04620010380c0000d0b107200c43d540d200030348841c01d0320000741c00e111040d00c01c3d0008103d1f1040d895110b06e05c030601200c900c00c0c4040c1078040224200c1c03181c10342e490342c201410b281141003681a1202c4280d42024004c00b11801d00450050480d040303120300030b081c0207008203002d0707881c1c0085000703213402c82e024000907400040a1003814000e2a5030b8004083d200c0c41e04911044024941c1e039150b0264440d01400340d0f04c1e84400c1c200d00d40c080e81416404800c1145803000a000340100205521243c0380c0c64044020144c01a44841c03007800110111180307220b81c01d400304c41c180300300d00441030640c01c140302c10000280a018170980160000c2c007441e08001c40781c016291281c0081103840005036001c2d20402031800c003480b4140140002d03140c1a03181c1001d02d40f00c0440f416100c01d2961b240c2e1284000205090100015107201e00f00e81480303203040c2221400d00074a80850380300c00c801072040f5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 368435323 1250 368434073 368434109
    0x201030e030307022509061401031b02060403051e0a031d0714090403140d1a010509030c010c0204150305150a0203061c031b0308091b01020a110402040b0310 69
    0x200200b50380c4100c03029802019100303c0d8110f001030318206031940c010780c0c1003507103001300b01e81c449401584040c044904102e030340c000c0d04200040a45c1c0d031645400c20b851074008000701c1e82580c0490000e44c055090305000745d84980031060000c04251040050346099000304864520542c5034000030542d034201030b260004a007500c0201c3d03450b00000d100ba282d1101200c034031002d003821701d003e9845e0711030301034144460402e00000c001d00c001e81c4584000c8040700c1d40c400c181900d0325450704100703042c0d4100703180440c2003d280c2c0000c650348042c4054418103000c400c0c4515800c660f950340111a6600b0100c080751135007680da01d06107541c5d400d2500303442546451400014aa07e13030910980b481020014200100c0c03005d44c092a40314040d8190701070b01001031049003183d800c20b1a90000040c644030703a6a03c8200d107403240034582410155040006241903070a10010140e90010388001c2c0c160308030880861502c065070001b00244516400745055a00100411204442a507507050485048d58108140020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 368436573 1250 368435323 368435351
    0x7050a0e0603060303040905060d0507080d0207060f080a050a0b153412050c060f01080f0601062307020a032d0c030b0411031e0d020109081b1009030507020103 70
    0x101c43c12a0154814407041010800b2504500c1e00114050085000c5c1d16880c0c40c0c8a081c59000e0f0003014941c1d101000011781d9a50402031500200000d00d45084580303450fa8004290348000f80c04480529103841c00b04202d640554400a40d16800500c00c40070100c0011104516820182cac2d14040d00e403180e0010945494103070444100052400c60030703505900c0580c1c0e81d07a02c401b0701c040d0100c202311040c0081030600700c042060601440203100c01c0101c56161212061800c01c00c0e8141c0c1440da0446401088820b070854002d280100f00c2e2081c4081c000c5814070424254001c0100282d8002e040003000010b014540c01c1508414541102c0744406a001d2480714004000301c00c0000c080b01040c03038003000461403034103081c0d401c54491110b04052417400c100003403a141500c18084101c11354840c86107500340040049a9502942e0300003404407240a031282200f600802e14102804582d5081488021505000301c00344000511410800250142402804c1d9000080c08a021900d01b20010a03228 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 368437823 1250 368436573 368436577
    0x106020d0f1403040602070c1a030114030a0b070503131e030806010809100b130f05010f05100504031b0510081009063501020c06150103051b030c0f0307050a0e06 71
    0x203480d81c44503440e58546170b640d00f0003540f101ea0140c8140500301c0303002c0b80a404503030350203003d01d070540d8809813a941403c00d40c0f0280710104165034440d80c031aa100c9000104c030002d425034880c1d114241251aa03545131010010606014402060705520000d4201c4445014501c1000d0038041e5079400c0c51541c4210065071516415101070505a1004201450005094210041900d000b0b0410f44500124501c0c19080d140e8104d881e40803241c540c00188021599485840d0080c501220281c40c004081030014051307108500000d054405000801c40000001d50001001007030090802e4160a042401c010901401600d207145c100500c41d070b001451080c1801100c007500c0408100c0d121a01c02000c80c410010000c0c1807104456607603000582d8404006c0c030160041d8000000907140c2d40ca07010040e40d10300d454134000241458035010034000350110403000c4100e288a8015044c4c3e4940b5040b0440f0210302982081542d030368070010030444001e03440405007010b41c009484225a81100404001440c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 368439073 1250 368437823 368437847
    0x106050118091e0e030901020d0504060e04020c0309060316141e03061f0e0117040b0133090e160806040209060d020a0e01120203010f0e0405010b090106020d0f 70
    0x1180c611106000d08038050384032524180c0d51105415064020f0304812041c0e0340342e400074202d15040031519200c80c0d60148891040007031070f8a046407500c1e050041c06451420000c45e8140525400300b01c41ca030300700d400c1007119030748403005269588a10300392a804001144120b16500007403401c030707441ca88011014013607581d4600c5d000707035440120308c2004400d8250b400040219605c87c2c2250029800c01c481c6030a21068240707255100c61402840303000252607400c044c01c072841d256210000b0000481c201c0070300c20741036804805000308021500400005100000c08430b0074511201c400032600c445400200100c00ca41c9590130810b10f0380e40d0100ca646c04441041c8080700400e01e404009409894142d00074081d202004100a0801000d00c2e22201207800800c0583d000c03401c030306012181580c021400400d1043e0801e401d51443d810001c0c4014943e88600c80c00051942c400c1c04102000401c1d0890040300c44090214101980c0d1080000c0d5a04a02031030700c80452010403203a08003a01c220055201c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 368440323 1250 368439073 368439107
    0x3090303040308070c14030409141003060b0114190e060a020c040c09081002040503011b0c020415151d10020a080f0f030c030417090f0d051c08040501060501 69
    0x3036940300c1d2819074440e03500401d24420030400c130508200140a9440e650302a07100840110348072400d12420004641c10682101d42448500d020042c1e01241580684140d03940032a010801d40c68941c01603603a00d00c070309003031030000074045036000800c03c1100c4031030f1403080540d44111114941e1014800c10384200c07541c4d200143c00040415405052139040010070300b20a00d80b215500350344004007401c0c50391031540d5036002600010100291300d024040d080300040d11350480030f52214410400303013082060b440e00134080e50302e610420600d010381040e01d10082c550f4490500f408415032034000d0412400f40e02c2480b40c80c421000290090814080c000440348840c0c0080114034440d032980d103055000f5041c5181410420480f038030101d8401c00146006110100c4816180e042900e05120490f402c2c0001620160082c08560382d0340e66019401e1481d54000d8520140f90480e80c1045802c001d62040342c02c180b00014491595101d03801000540b040f80580e008106032900d510045444851030005211 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 368441573 1250 368440323 368440327
    0x14070f0c0b071406012c18030f030915091c030906020f03100e010b1b0a0f0c0f06050a050f13080102190311030105010c080d0b09011203020616050307031e0510051302030903 76
    0x5011941800e034108481e902e00540080315500c002d0f285078009e12004c82007040110903c1660213082100703546860540644030310602d0000099035549003200922841c1c12503030028001c0081c0a0303409103030420740042c2c00303540d07800d2580c1411300365070302c02d40308100c0044400d0b000040a412440289040c1c40e9103041d014900750000c0c0e030a1800b003484240010090040c0b903850400520f04a0000b070301540714691020344c0504e09050614004015444542404000c04c0f14054481d03000d8102c801c001e0040c07006070b86581680b41024080e50131904100e4066100041080d02c0c4c1c0f10203402d500b41c0d8102c0d59014450546103a550380c0c5240000e101c0c40d800b1900380340400b40040c01c6000603080b0f074012544009841d00e541c0000a00100d42a4001010741000381e401c44103040e8107021140d4440440520708036001c602e00e078018054400144604c042698503443c070410960b040c00c26800c80701098100340910b04045000d10040b5807284a21489503204451400201e503407402620310402c40b02021758 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 368442823 1250 368441573 368441639
    0x4050103020a26191b080702031306030b030c030c0904030804150c09030b0901090c1707030b01090c0e01090e01050f040b030a0b061014070f0c0b07140601 68
    0x16000e074201d00900e00a1004000562024401c0c0688001010303c00410590303150a049050b0300e40725500d007800808140c2001140060194401c0880140d01005d2a2140c1e60380d440020480c114010304043d40d9812109050009150754540c0081700c0d600030440649882c1d412034010141c0c0d81c2c405601c0c0d0b540104941000501080c0129442644180540f440c107282c0346a0361821421121501c200d00702181c184c58050060100064525620031910402005070103103d845070300c0009080d02c5442c00c01c0f404620095032011081c019040115030042161900d0b586035120040581800903900340080c611050400740303517204403961022205000c9205007241d003041f080c0030050301020a9190802d031900c0203103086407000c0101d17500c0180180006d66450512508004071b01107501404004c11101c12028048511003a00300e0341104d502800e0111001c0d000d1501040704280c507480044a107801040340c10500840c441010316560f644002d444450f07884800110141034000204c03000d02c40c40070b4842e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 368444073 1250 368442823 368442827
    0x13090302011109010c12020f0a0305070501060603230a0b06040320060406120b0f1305060901090b010906110c09010e18061b0919260f0a080a0e090408072006040501 72
    0xa106c101b4941e01c15101c03444c0380590200d1501076072990450010f40c1c001400400d00000713100c0c0101400c12440c05009019a1000078501c5450003807100302c0b030215601c08111000140d40c480180040040c1c9070503141c0380d681c18180c540480030025918035000a00342c0035030601d024070031502500d5a5884074141c000c074030035507a00145010304241360440d5004019a28903906c014000030030030f01c0040d01281c58904030040c0700d141603040c0d008942e950309026092109030b802c0344c0c0380b9082c0d0301c60740f4010b0300ca01e940d11a074620707104201604603044080381001040e003030007004205102d1600034104010308107d12407160380c1c80300116024178158400b400c1444010035060020682a407000740403403201d8071690001010684164050340080a003003011007104c50540c0c141003c400503541c094400303130000700c0d40c00d07407100380d21200180400b20010303c600c1c00c40e0080405610a04000c1e00c41c02031440e040c0b030020710544c000c1d181558081c40a00c22040c805d040d0602020840802500e80d504180c544001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 368445323 1250 368444073 368444093
    0x9130b090a0602030a0606031b021c0c0b040b0412090f030215070c24050301030c0e040804030804030317090a03020a080a02030d090501020910140301050d0309030213090302011109010c 81
    0xc0d04915006000200c004103416002541c01184000c0c0000b451a14001029044500c410580e142c2c41005200c40c0143d160086070b82703200624030071445501018038003412030f80f001c5403010003480450030300c084c00305110a03a40314500c503a105099481144e00451070a03a03855040d44a402c04c4041c110200703100508040944800903c0754400b01410002d0599560f8500344058101c10050030400fa5200c40404140ca01300442c496941031542c03455040d034030360914001c00d42c001c00040002501c0030a040185520407100255008401103031250784034500208198408032640c00d900c0b0b900c0020810b14840440d4840165616030014802e07080c071079030303140084e4001154640650009100300d581a1001d8054000b01500c9030b000103a88810150800c465240e8000d04e140412040c908101004040d4204480c10b6400403541030340c44000900c0d080320710042d00d800094112644480300c080709415508840407143c400e4000b80b00001207014113030140c1c02485412070001d095804503801081200c89 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 368446573 1250 368445323 368445331
    0x120d050d0e0a14070b0708030a02070c1707050f0604061709030c010603030905030f060601050414060d090f0c050102010b030307060f0e03130e0f010b0708030a140a140609130b 77
    0x12001c1607038021403428038280742c02c440007580d070300455143c450064142880000040c01c24075003c14200801d949900c05680801000c3d01802540000c500061120307400f850001082200100a280c800d001d1916844481922a107070090a1081006c0c1003450b061044d6804c1c0c85c130a03540c0d007031160b4105900d0440712101410041c1140420004101e0342d26007070203110055400b94550608a030b1030001070514020748041140701030b0304071070240000f41e80e00c2011a011034000c042d1000750b4030380040c00540c41c1c0c890200f07642115841c10301c1c000701b0403140408183c91907000d10719030f404e0301d076a60340103a00380c0341c59603a07241d81a081003100c040040c8440e8000c40040c80c4849000130090380100001d499540400400f0118221040d0200148050030210070740c4131003282001422540f4140300070740d20340186840182203103070202c00118031040f140e014888108511101c40d0060800500030b42c001d00e0400c0c820f00480c4808030000303840d410014506802428404403003086921a511031b0300c81020090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 368447823 1250 368446573 368446597
    0x1517010624030605100215100e06132d1406150c0a050f0f071d04140115180b03060c030c13090f0b011e090303050d18060b0a05120d05 59
    0x80001c20603450b90341c010b551440c1c080c0c0090441d00824505480810001800b41085004d4a11b0274480a80c01400722070700400181d80504000303241528000c0509440022811440d803107031150035080000d0a00351400d00504c0d102000885110035040146800803a03a00d0740110301d81100381c4403400e2502c000c1c6000505002607c00d800350983d91281443c0b55130394444050340c042c4107020301c0d060040c03064000400201e0211841e015030707502102d0341c0660042001d0b001d11054550f500b01401c0030b4001c0814502030918841e120b82e104d08481c404801c00e6040145c442e880d00701e1054080c10000340d4603001f044c80c44811411651050090781c41940840031b140c00b010700c075070070025040081d03003d802406140c40801140500f100d4000510018000e0044489110404c1200c40080d4000304180c0651b501441c0181d0790720301c111886405084051040070500340704c036102c0014003203584e0050b00300d51011140c40e030303105940300b040080c4070380210381d81c1445400070b40408031064080d00c001c11580c0b002d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 368449073 1250 368447823 368447831
    0x42009060408250e0103030210050703141006080a020f04031112030406120515061606150308180f031e0705060c0c01080f130209060a09151701062403 66
    0x101452410700101200e50407100d40103030540e040c1d544002c41c0c0c40d00940710842d82c0718140c5d031654800030342d00c01105070007c1d001c0b41ea800114045520070780107400e444425810300c00d114103040d9241414002180320f624000350071040880c091341500c1c0221042255949410b85c1002d086848400d6400354a2941da58001070040c1b003001141001e00140c80100b03072079100c0880218a04008c841600c030000c0c000310008450100382c244d540d46070416242c84107404c1c950340a10b1f925034508070006027901142d140001c0f50b1100000204001c5c64018101e07800324030703402c1c0c00340c217184000d0001c21030101c0c0c02c4685c1a0424604040c035040b0189900300643c0c200d40031241c0841e41c3e0000718081e07600c4003050390310981209003a0456541c00400c2e10b5008074841d41d00c1c00451902d8203e03410b50502000d0028800c2d400c0c100824840e0351041c0390003019010480b01000b40882c03c0700010210b070800d100c0c90030b40c084c0512244c06900f0040c442d4008076201981590301107215400ca20300c4842c50542d10005169607 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 368450323 1250 368449073 368449079
    0x1a06030a0f14071419030203280b010905030a020108011502190606030b06090f0117070e070806120c060f030a021b010e0c0f030a2607050a0c050420090604 68
    0x19800b40c900780340e00203902c02d80b0038148400000e0081c0145080300c1440c100030096881c0030f803d2407041c0e00350b6030032130f10700140c40341c60300c000f128885190115190010100c00e6229180c3c80c1d503030b50115040c880240c0720016116a1001415260403d003000607002c03c4500c001000460128090200c2407512032040d1086015003020311201c1084000041c2c4d01207550389802d20812241070045608014110341000c1285000c1c500241c140105004201032450b0040a41c1c0300c0c00820043d44002d028070001c02d800e82c0c5820000180000022510340c0c0c8a60304101c0c44240f2003201241100342c2074005010a0319044c6280c0c07410486078000307455200d1a9608000b1002461402d0302e0104240c4110400401c5048030b9258240c94001c549001a100751a22440e0110f41d0f80c00090b4000e80d04c1d07000581c00322403d02d07120760502d5189061031104c44214001100e10421030042810300c00e20f846001300139100c41c5c84030240710489d1100d0a04400c0c040300d4400080306900c100000e0050711400a00301891300d40c13 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 368451573 1250 368450323 368450351
    0x30f0f03020a06150f14030d261305060606030c0306010c030905100f02010b0312090f04020702060705070504113108100e0601080a051203040201300b03011a06030a 72
    0x260741d91840c1c66404c1d04400b8004400e0708820000180b07002588441301c01d5002000135210350131070400e0414403501c03000e04106000c00d454030141301c501c4032040c08018a00702201307142c48079491038202ca95000b0040001d00e503241690940c2c0c00b4a0314424424103694801005443c41c004210055040c04000540002c1c61341d45e07c1c4000c40c04480a60361140c188070518400303403d603507070011964401d401070490740c080c441c1010191282c03900c040741c405070285039072004100203101e1502c0c040d4020b00000b803604140701000450404940b800d07501000080b0301c1c2d00294006000b10018a00d0a60b0b00c2015107200031340d44101a030340c1198640e0880411640e07240352515003035660b03842090f51901e03041d0075041000180401401002c0c441d0140a030842c060303072002d44542103612284003018000c000f0500356403142c8014400d09251910000500d0031410980c0c4e0a2116880c40071309a500b45101190541018000d10300c00c400e000c514402200590300400c00c0d160401000040b01641d41c04000e85000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 368452823 1250 368451573 368451581
    0x21b011b030506211b0306010506160c0e0c0408070e010302010504030b0703060504020a02070501111203042d0b190905120a110a0c0510030603150e0a0203010e06011806030f0f03020a06 81
    0x2684c45401480a00d500150340040b2100b8408003a1003074001a004110359124035003215012001042100040c00091501c501c01e1860b50300402d81820b086001c00404280c1d0b54000e0003540d50a00469080c15a00c200124038282c1c02d0100900003603043c002040010410b50025070800030f6030901045e20b07902ea44c080744c100d0700014085801680051010440e6582120300d1900b1107040601030100e94014211040c0c0c135100143c8003c0c1600121701d040844103213045840305003c89849072400c6192682d04051031a2441a951000e10340b1819500c0414080c1c0c47c810802c032a0b034094040c0883d1101001080c1c895000031860700c091020030482c00500b1181845100640c40c8600340700f210580c182030038041d024848203a9082410714102040c03000c02d00419a0385001c0d9541039011810104080500341800700c0c0301d400039019030804076418000040800e51a040e1120070300d4440d201c207501d403030940558020340300141211607201741600105900668908055000340111030000c1617a80e03a031002c076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 368454073 1250 368452823 368452879
    0x30a0f0c05040e030f1801020f3c0a02010f0e0604180b0910090515030114060306061008040206130e090c030d08040b181f021b011b030506 61
    0x1008480350901c1245000d11468a91000700c80c0250b00303010712065180018400d01000c43c4c425640000404c1040e0300c2040041c2c03818041005841d00e20046048640e400c85941094400580c42c50f01c140a0705d040d07090405d2201c0100e9402410128280c5d0010764444903810303641000c008824402c0c05840d00c80c03600600042c0501d840b0096034112003025041141c1c01e403c10f01c1c0c45510700105021841424401060540d8840ea8000640752101240c402900150900c4540c055080c107403c2c0044480d07040e4202d01c00d00c000d509030341490f07584070100b00000c000c0200981c00316000c08041009810404082c1c41109924140003203090740b42c4581d42250f660840700840380d54003a58018125040074041c3e5001842c05040003048c504066948828860340140a040c490030000c0404030407610801400442c440c1c407860552003070f69030002c204003941c00058108807030780d00f000c5200c204241c1441a12401301441c54072084a0000c580d088020300009000c4030b0340415403204464010024415100c52 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 368455323 1250 368454073 368454083
    0x30d0504031104020424020705090f041a0610033b0d0306050904140c061603020f0304081c0c12120f0c08070309020315011202011106060f0609030a0f 66
    0x15107285180699501080307001a034066401803104101d6030400001c0b5403020040841e054183c1580000200e1030400160b01c4640c0c00039280c7d0a000011121a030034900960003031041d40d5106c0d03401c580c540d20151b0280c82294000c0000050030100a1195000c800c9003000c44100d22040f01079070030711201d82080181441c490041085142d004c1500410154480e5502c44c02d05204183c5003400150b41e01328020300c00350210184120905503100305008880b841a0028001522401c07074808032034a07803540c908228090b04c502c001030f50320040004280c50842c0c0c142802004641c40c150400041490240390300300610a0510b03103440014480580c280c403452803580d03015104044085c107803040d5034140d403200701d40c41d00d045a40006281e100403816407080a0b0306006c14214203501c003281ca08001c141ca00280302c00c8000010600501380c03513040810314001d07031740c19403416107030a003081c1c0310380003034030619441b19070b41d4440c0340c40381084400b4200400340101540c00e00c1c0342c50384520350111000031088034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 368456573 1250 368455323 368455327
    0x1018081201061e020705061c1514091302190306020a05030a0506010c030801260f030306011e020a0b06040e010f0e1902010212071b0b0a03060e06010206070c0c05030d05 74
    0x480382d540854160400d104141110061221020f00a13445404901599010300302c001180d095040c2d8000d2580300300c00c8402420011402d41e860103100c44180d82c005c030b20030020040a8211140741c5600218000c074488003c000350301d5203d60821118213038000c4410080c803500f00c0c2c000301103005803000e0400101140c6400b0394074600054007604a0390000d0015060024002004004c40da0080c1c01d039064400442d40d041c0c1080c6030401c0c5072403c0c0404803410b401880342c0c1d40802003d41e40030011b1401035000f80c0307906190010140702ca500b204416401100140d002022440109141c1940d0640142c005031000501c501ea1440890944035400740c540c41907620343e88060f0b0015401c00c00b070302100840380c0011201100c10340c0001c3d2540c9079103494a10303d210114510742408004158080d2060076840440c1005955039005001600003280c5100802d20f064800105a03e40d0904203108540581c050f1486660368041610342d5a05800c1c01d03203085100e0100401e0f10b460400154070445043d880303c076 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 368457823 1250 368456573 368456579
    0xa0605040605060a0f0807230903060709120f2909060601081909150e0a031103070b0c0d0e0712210c02100e04050106030b12010e1018081201 62
    0x5440d480c1d4407090161100b0000c40e40c1407944203220340d0745d1204a140142854880c001c040342c1d140415508207004c49400c0403000c044003040401460680001e03026140241d803036081c00d486049880c41001000c0007271694040014590030f07440300c1401d104944212400c822074030b0540c08820180d9040b20b0022040c02030051051080060a502c69024a08640c0c1842e0180340c13941f110b52a644420449034031508402c2c01c208143c0320100c04000340b10420080926914820740e5500c20804c0140e0129075489041141034101204a03148240c100340d80601548400c1d00d1080e0590114103000459a0745001020803101c007408518020502491040211003c07400d01e07410180003841d92248000ca140309138103c040d0004103007120150100d0b030301e0b140c40d1030f181002d48011007610b402d1a405172810001013001e42e0554001c580840043d141d0f2032552500d0081a400c0f02c501c0d00d0050726a600003540ca2072120b020b5041004030382907a1601c44072981c03566440d4031641e0803940c4205c041a807004014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 368459073 1250 368457823 368457829
    0x230f040902091807050a210509070f060e010c020d0311060f06120708070605160c0e07030b0415030b061201020c0c120703150203100b030a0603020a06050a0915020c090a0605 76
    0x1000f4215003940100c0c51400c02000c09001d91044924510900010a803401d40702c0da048000c101800340c184509000f1440d016883e03070703255040d902650b2490f210064022401d0344c4030b80340781d441303071001038541ca112040075800b08002d881c1445e41c11001c00c481c480100d030785020700703120b1540696901d01002d64582000302c104042400e00c80d01644950748005020851500c000078604d04440301c90038030795a640201da035010b41e030f034403603150241070010302201c0082e44004240f8110f1040d40b0550f810030014003103604000c180c2c3d00c80166031944600c0b8030020f10115209000c0a50031441c000d06103600f0310074420400b0300b6a080b024000300313150011000800c960812140740c44180a03d04050902981035035515803a400352150790441007580440003a0305d039450b0301c41d404003814140b10750a44034940707010500702500a0303020890041d2042d000c00030307640d030085040e0b40300100c0580300e00c6c0d021400d00510605280d2601d52900c11031243c444504180d450741e03c94075010310880140030851038181414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 368460323 1250 368459073 368459089
    0x5060112110f0702180f270607030509070f08071409010806150102030706061e06031a01050c0120041505070f0305180306090f07090606230f04090209 66
    0x35444540c1440801c0840003024021500340b88102c42403280c48503030701d0020030303420740300c903000602c02903403401c10300c0610b80075405018850003010070300c0c1070307000300390b540c8500c880103504c88506140e031200c1c020401d090f001e60001035114900344100ca540307c1c0d88007400c42130003580380c1c00001107400c040c1c0305026940082003201f0f034070341040d41c449065503d0101410768400c0000c01c070201e8580120802685688280100c070b140c103411020502130240c4400e080850f20310b014040900103400306000054186c0240030b01440e038a1120004404044010f005507200d0740301203240985550b07580380c100303c40005490300c1240901400c1d880c41e00c850800b40001c2100d0b5030303001c010042c08014030900001801c3c854810783c4040c1d05143c0300351200c80864440540c1c090710f0408a615000301800c004074142e0018200640b090000110340e03889941d000a441241d02d54001c4c20006445840c00c110400104c0340480c140722510103800341f03801c103400040c01c102d4009802ca503401c0ca800140c840114501140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 368461573 1250 368460323 368460347
    0x31506030c2115290a032a030b0405040506130503071208010807170d0e030c040c030221100611031b070320011e090503120c01060803041217090d0501050601 69
    0x190610210b13484060b010003d40e000b551104810001444100d250b119400405800c80400f03520624001040c6007000400040004c1100091a2030748900d501e01d0700d0b000d60350040e81c000015000715200c10f110400480640701c4180c602c1d2200708000c0c000a80e00140d1180019110b40d200609941000b140c00d0810160781e0040c80315008000505a804202203502c0d160307440075041002c0036030a280082414462544d58455100f45482c261416498064000f0085c00c00e40f0480c0c44680c01814070780d82400981580c8080c1882c080704001e00240d4001c0114044054070740044074108691050003454440a071500001d064204140030800c10010b64040740101441200c1c0180306050300b00020304800c40510700002031007034403040c00e02c0c039402101c845c0080d00020302038500c1d0f094017410414075039100034903824256181090006001c00c01009403816902401010186105039131256808080c0300381c030b48940010208105034150f038410101c2039501d84194004901490300800141c081c5501c84 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 368462823 1250 368461573 368461589
    0xc110601180b0111060f0604060b0c0c15070c03030203070b07030b13090312091a100605030c07050c060301080109030908061909060f1401031101031506030c2115 71
    0x10060203009500c031508008401c8403030001070160900310040742c44240903105805140150018800103d2407101540c1c41803009440912010369030b0703c1d90a040e8403410703030413400307030f800c441c007200114685800881d00700c0e40000042414074803280c5039130201c0c10366907008034090380c80011442c04005088045c99800f00c220705003081200361300004034001c441c0d00160302805682c3c9404000030580242710542c5001440c03502000b0300003440c54500400d104110031078249840000c000ba40c0f0400fa54140d8003540c22a588403821504c031550600c1c459001508129207a0181074001400703520b41401440c001c0c1007400c004204404e2a00303002d0728600094001040940180d000c0100c481d18021000f41c03d40080c03007000611040300e05001004000e49807208840030705262a88504144214903281030300d0051600c03052425040005404403410700c0303c182542c0e0385920341040f419001c1e6110303000d0042c0c2405c240e1805489090350b104103003800052010803640d100c2c0144071910100340800044c120300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 368464073 1250 368462823 368462833
    0x60e0307060f15050d0f0b100501110a0507030b0c09060d05220c060f030e030403030906020f0604020a0306020a1b32060406270309050114130b0306010c050307060c11 73
    0x6200c40c3c003c003c10b50003001d025100d0f80021000b0044060a140546504500c1c92040381c100340d8659007030310113103100d110300041207009400801c1da00070501200e5164403400802d8000d280d6502e00d122404002d140c00c00c284801e01c81070307045449030f00060001e03801c5a00b002400d45002400300b00c0c60b0960542c28150f500c1e10307241000019620340c10150988281c0d080c4a003403003403102400c4000e011605080c01d0f40780008100081055088039032002960003580941d40100c00e4021000d0f03403030ba411100603501c450091400c1021074904d03801082c03070003d41d00d0000b00d14202d441c15110115070020048a072001360380c0c610041c1624140c0100e48406140414500070903461320139982d604030261001c0d100694034010030401e0341619503408580803000e0040305035554241000741601941e889111f01260301240802d14400082040311190700c2da10000c1d0340b0003410501c50418030380009009605005849116202144042019000c0307540700f000c01254841404200030102c51a4031101e00d00340c0d0203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 368465323 1250 368464073 368464091
    0x606040911071e0b07270f0e09060702070605090409050a1505061c0b0601110a1401050708012111040e01050a0e0a03080708061c03080901061401090e060a03060e0307060f 75
    0x1000d18080c5c1c00204520f809003525131040024201c6400d484030f290242120700c1e80c001003000d0426840421a51802d510081d03a0b510b1f8041030745c9401e01181c030a070050300300417010700c6154001c402800c0316010240001881d9940d55484500c0e15106000a403040a540042175191140d180210390348840c0c1601c4140300380d20310a1110550341149100182000c4803000010010703441a4224002c1200a100b00c40c400725072401d20082da001d0300c054003026942080c0018a02034010020203049652400f00c5941c581d003840203002405410600131a03600121981544190366075008840405610344000a035504010040b101103521028144840b030300600c40000200703400a01c01a8031041746c0c140120710340d5034840025100d0449070401c082a0010710001e00606500503075680c030a149460080114644900c400c6d1400550000d04500007a2048001c0c001100030380041600711030003a00202e401610780d40c41074252000b04203100800d51011844505001c0310740902840c0c00c140090400c81c81d82 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 368466573 1250 368465323 368465333
    0x1d060910060b120a0f06121e0f260309010e070f0605041701060b0f120702062404090609050d12050c07080a020f06011e050102030316080606040911071e 67
    0x18640045000715100c2000450240e5182c010017811040880b04000484e21840c03008500445640152181401c4000d00400880003805011005400c1306100080b0100c0c0d55a009083c401c403000326900d49442c4810624070301d480c2015502031600c40001041a00d660b02d00340e49800c2142e481110a646d0907401000200d80000845054a92001c44000c04c005030f850303c14050813041e80904103d420024404803c881240041c0505840c48610100f540d2203508080b41c1d00d1a017543d540404202c2c0082102c154210b01c032403c04180800380c0040703008131a58403290115803503000c003910145c00109080c201103900c1403c1100308584076000700024105214003506600403070751b00038407900e030024041c0d4001c0e00070810462505d54034400c0b0742c0d040d070f1100118159001003036040404070203a524040b8856002000340d9102d00301d07101e030041d04091801012a10001c4c003030126034200008100106542159000751200d078000031642d50b07a40c180901e001e1340d003c0c520a14881c1c05d00e0154480c040010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 368467823 1250 368466573 368466577
    0x1207060219020c1212220315050105090f071202160203120a033204170c0c01020606040902010c110118080102040e06011103072003030d06030b0a062105011d060910060b 74
    0x50701e0055070424611b0400002c0c0b012000641020b042c80500d501c0c1c1481d040b4107074000a05841094404202070317110101414250750b000d454080120b20300d10701c00105108650302a040c80300981c0f00c910754024158011a081c4820f14031801c58448000503100940ca8050290b00580c00045070f524801802140080b103504181d4524021404000c0e004502400312a401301c1e80500c1c41c10116659a00141105698454548510a01600405000522520b454031440f26001e4042e180c440c4141456a0b812110701d5260485070b0602c00d4030300310149802081d01541c1e000e01002d200040c0e0325400c1c6460000145070042c0580e041008a04541c800c03080044161050310f0b9201c40c2050060a41c00035011541401416403070f01031202041e100d1580700c883d049002224041c0c0380c003058035147d03c2000340503242640514610001ca0b090720a40d0701d002c00c40b022032181e0043d4000501403040c5a03400c00703402100d5550104ea580450300384070f03060100f030003554003403159424100441740c070b0314861003ea8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 368469073 1250 368467823 368467837
    0xa1203080405100f0b04060821030901110307110f07180507140c0d03050f130b070201020c0313061106010f0902250302070e0f0403021207060219020c1212 68
    0x400d0a1000c14100710b41000b2402c0440c4221005200c8048401c024000520841c0c0d56680b01c0c6040a00c005401c11000c034040101c0d40f82190740c20100d100c81c00c1e080506620141400381290350b00c00841945030040c501a42c06021296942d008082e8076000c442c1c0340144003020b40b0000c0c0c2200b08100b01c80c5e50308942441400703141c1d01000c43d090341c0d0584143e5110805803101e0800c2080081c80d03e41d85240800c1ca070b01211142d4400700940e8a8450b200624007004983c0f106d5031096100b400b101080c050310003254850120710015260090700c54005003560003440e40b03c0b07078101c441c1909010303c603044000940d000d45850000c01c01585000703000040c01e4020302c43d0b60003042e400580482644d203402d00c03944010885603120030103074a56107030003903594007107200c0c07051109070310400306c0e20081d25440d403107003d150147d000300203c419001d85a0074a900c410001c4a045600f0020041d0400c500c6810f005c2040303076500900071004158040c0700361100415000c0c1e0b80c07034111a04003014461008155801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 368470323 1250 368469073 368469077
    0xf09100b060d0f1404060c0f0206010503150907240f020a1a070c020603010b03070e0109081213032f0301092004020403050f39040b0a0f0902030906060a1203 69
    0x510316201c5061802000452070306a1346448810401043c0543c42c0c0014030308801d2580e80c052102c10404040380c0320764003030054a81c15040307182d001100e540c0180b03c1c4d54008200d603069a000b40c0d80c0343d404400c0341c9014018000c0e40440400c03108102c503044841c05441d030140740050140500c2c2c035501e00890103004110b624401c000d0703c0104a0031489500460502540600487e0362941c5032122030340c042e0403c03605080040c2582e020300301d255210384007400c100d4003880f0040000044a1007600da46030880c0011940010b010386001010a012081c0800b100c000600c500746035500400000b0710f203c3d030030303484240a40c0c1008251400252a80c501401400d4190803041000d41c459000a001c0d100b81d5101034210300c11941508440c04000c22203d68000284031250190700710007800b50303d20034280203c081b1804400401401c1c03801c0540110341e1050000300104810b5446840209513505690850481b482d401b000308507032040e00700070b00d94200504803100c2d01c5561908580364103040c114000181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 368471573 1250 368470323 368470331
    0x3140d0e0d0209041106120411220b01020a021e04050a051515090405011d070305040c0902070c0519030b0c0705060714041d09061501090902090f04050f09100b060d 72
    0x1050003a203c00c262041c0d40d000b050070b5a1a2551f10f1618020348055a00355401001c03c0104c0440345800d04180d481072440c40d50792107014507003040d0130009140d000381603030640c000d030020350005035070f002c15907804a510010001a83d05011090200300d0300003c0052004600d44018041d201c900303900004c10006080f20b0700c0d4401452000c030441a030062004140d0000d04000c004901c141010100120138580303800c040b1055a9050300482c190350082d20040d110301c946507001d0010305010b4000f440e00718000d003042c0c03e00aa489001c01e42252a049010442803880300c0d043c4200084440620340142e20740076080c0c10007a5984806032100f8029040342c1c00c2c480620003003440310381d610003610300508101c007401c00104c3c440718402011250403a0440c500d402000e00180440300d91414490500006a4a038a281c60402c60030b00000d5000c045440c2c1d102506042071091075980707000310780c800c5e00c00100203d01401c2000003e46000020129004c40714106010346085490307031000c0d103050380e00480000c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 368472823 1250 368471573 368471581
    0x9050708091e0c0402040801090b0f0c030103020d1a07020106170a02060a0c020a03050303010b0d0e160b090103111b07060516081e12070216030203030904051503030403140d0e0d0209 80
    0x1450700000c50f942a800c40d00206000500610640c441c1e00d05c40d000f516800c0f49aa503a82e04070f0750120084508451080d4103000620150604940920142d4450072500d0515440c2c48407222101001704d440400513034449000348040100c40513010403841910300142214206136000842a0003070520003800c00580c51040c1c0c1c1950b64412914004580103030a81c2d56a585a00340034540e903110450300840c0c00d040c00e0070804d208000080724020860103942c24000d55091000c82002d40d4000b19113036040617141c0c918910650794040051401d1184480f90005c0c080d0b50300c401ca410503007168001000e120003030149130417440d10300c030001420170f600005503942d6044540140724044541c0c8118450b4401c0402d54007445200ea40846015015070b1b02111207042c2e5507403d03840300c80018040250543c00904c131a80d05401c040c0c00240c0c100320404042d0a11000c0140800d103540c01c542d0050312403020046401480075414807800c0814030f000e150049200740c1000c023107841030031014802800740700408006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 368474073 1250 368472823 368472883
    0x304060b0a05100302070506011208030a0b01120609060e0c0a050a11011103010303080415051909080d05070203041e0b03070f090b03100e06062a070f090203010905070809 75
    0x85000c2c1000525410160840020040080d0030100080b203061140800108504070001404024941d100e06468034503611010100042d0003601611030500c07002c1317240d4200c41543e03030280741c0180201110000d4180c0c507012820410080107040001e11180030401e00300c0780c030f5011040b64440615820150040242c2ca00014010700428004082d880004030020081543c01261580598001d0200d50120303800f10140703408452092f00c4008108034035201c0c44050401c82d401c0042454040d08160303040008203841c00701614012612480160000102800802001e511201450b1540d000c52180c050600035810302520015100318148041e18081e04249841008a0405080e820100e291a401d01204c5489520030030302400d440e125450740003031001e00b880c200b039410555604030b02d10510341c082100c45101040709607203100c40c1d0280040104158060004200050040040043c0da0390300d040a0401199000f0f482d83d001c00c2504814840041000900b0200002c80044444a0b1030301c0785c044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 368475323 1250 368474073 368474089
    0x18050a0f050712060c0e030c1e0f0310020a020609010b15030414010c05030603120f0a14070b0411011e0e041a040e0102090f1507060c0504080a051c0e01050304060b 72
    0x880c200100c2d0f01403040040000c00d0b00f280400d0304050305d860160854078800c0588881c001d610b03960704040b925088000114a40c13444800100000d044208481c120300d0100782003422842c1b46208a94000902141c0c595040041680c0500d40200800004c0031680004041c0010040d6407030a8100100c0411705010312481240010040c580c001c01151520001c054581e41084400301d1003800b40c14000003403203120740304030744808501d084000c3c5030140400003560b0404d0b10400004030500207220007000240d04216290095001d58260818025044001002c2402228243c1d400105981000c1c0d005504200b0310111200300300c81c0450040d00c0c3c00c04e441080c1c0381c50b00185034080d0500030300d200345220640c000e000c500300a4401d207040e03810080a0100300c000c1d103018600102d02c20040b001c086031307440c1d1002043d080d441c0392491a096603101803e1400c0501c2c4421345a0743c12020144604003042c20018a80504508208003610800400a0180c0c000288041c1116132640301c09800381c1d07070300f1030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 368476573 1250 368475323 368475329
    0x6030f07030903051c050114060a0e040c090305030a05040f05060a050304060506120a0b04060c090803030c25080d0608011e1a06070b010602060f040f020f030a06050114010318050a0f0507 82
    0xc5c4c00d9003d000b00141a4014220a10440c01e078440580e0682c48070b0b040034000c40300803481940711079901410410a01c0010688007000750200004410301200041091000300507404c0b0517030b512901d03682002c9299854682c181d01c164810007080003900b01f49500002034952194120900103441c1d03480c0401305202c03690070070302e58515010350240c00040001e90000580a0350203807100b0410464480c80c1900d08a40c24021401581d005100103814010042c0c000c1880013189803500c42c000320190b281188108034000c0440d6030040119442d1190360003846034600908102c2c0092202c0c6c90b40748503080d580d1042c90292049141c0302c0100400d41c506d04000c40280c2c000162a041da5040d031424540d2000b5400e000c0d5100502481012030501c003c01c00e4824000c0f40c02400b04e0b25903900741d500308180000740d2880301c1d03054092402030202044403885801c1c020300c1a42d0b000341d40e13481e124000404407100c1c0540d00012040c260902e002103040040c914904030b0303021b8181c54001e107882c14014a08000c41d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 368477823 1250 368476573 368476597
    0x906020301151106090a1b0305060f01030213090b0a020d02040e07030c0f020c090610020118060e0c0a1a0702060d09031d030f280606030c06080606030f0703090305 72
    0x500782d0b04042a00801803590341d02e5482190103071140c1c5454010581c2c0d00901580444200c0c004104040c002c802c40e42d00c0d09900c030004940d643d03520f42c1401d408482c01142d00c040d8400400560078075111100c8a000100001c00c02e8902030f03598002e003000098002d098480e4042260302e0381880707950445000d0582c081400106140c828001405411044080300c00202100d2074500483d00004003122003030300003840c00d40181e541d0020302c400d90907029070000031507494048840d0401c0500600c0c00542e400b035000807481c2071000311500d1a15030300c05410760217508544420021503c541850b10301803507641581e266516030600000302540103044000400501c3c0c1001c1d8800c1581000b49030102e09466084000d59001c240101074440c90104900762a81e080a5a04500b49035001d9a00d07110445d010480c5060241d292140d108132119504219407200c00300005014451b04102c25680c41001107618918529081d59400301c3c0030000b920300410304d03881d0811741c070805000300c0075038080140352 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 368479073 1250 368477823 368477827
    0x4020f0403060b0a15230909040b0601020105010b09031903140d27032f0a0b10090912112424060720060a02070801061409040201030c03090602 63
    0x10b4246400280101220584210091400010b4005404102d507100318119118241d48a04900c10f484884078410794031400804108500d512541d03c0424440c040e80c020139881c035091030103a002908603101a0014404202c1c18421500541c2c1c00203000c0e02264220b021a002d2003000d85016641d42680d401002412040882e8000c8129581d500c9000c3c108152013107011038481515010104208000d40500083c491262104848541c5050542d41d144081d90b4800f041c00c40c0c0d2191410300744220411070308c44440c90140040d016040700305501600b419070041002d01c41079070b01e884004000c2c1201c2003d1040110442c8000502446040000c9034681d100182504a819031080c0c950700840b0305043c100c0e05850007960317207c1005000d060703031440a0b0106240080c0da85410481401d140c034040000302c16045200790035100d01c0702511100016070020f000705030810b208582035a40c1030b0402140070324081150b8800b0742d1405a0769400c6030b02800c2c0011060300d8070400301d001c0c0c481d2000c050480e40c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 368480323 1250 368479073 368479079
    0x112805030f0412031206050609010503041103030f07150522050f01020a050a020118020604050f0604050d050609060129030a02070210050405012003040b0c15070216050402070b0a0b04020f04 83
    0x81c101c00f400d44a0310aa0340c80d144c030100b01c80c0303400c1111181e00406400650502800b2010750055005640141c09807410354520004000064a103038000a44e16241c4400802c000d0100b0910340c00b054a0403007440014812441d0111000000c400c00940f5940680002c2950a06000c002d00c040d00c12801104000e660358941460060810740c84070aa140040d81380142c3e41c500c4100c0c3c401500ea2042d8000e05613854149041e0030000c80080402030389602803030402c00010f142e0b460300c1117445e45d0741c40741c0041c3c042842d1040721035083c048164031240440c0b03154400042840b1101e8a01c0c9084c40178802c0b903d40f2600c07962070b0a8024080c03d10000e4218141100d5401d607c0c0d000009002220403d903194007c0755043c003041040c1d2090806180b00e50b5000f07200502040c99075101500e0400540c030b0844007174007002421603850200960b81d00000d60007070f4500201a54003128048007416003580c0c254500007940e5120811544000c1c110f2019554600000c0703800d03507541c1c04440e5000003505116440b140c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 368481573 1250 368480323 368480339
    0xf090803040605040c030b150a1d0106030c02030c01020409090203060106020a03050901030203152206050103060f05060a0203070b010b041a0a020c010807090f06211122090f0903112805030f04 84
    0x400150490b02c50740a90000240d08000c034038804a152043e0501c07003407181d233084030079005424951406002d6010901180c10056002d00c003500080c403062034003180c441e00600601d030810b5010381041045404c0b000900000c030b03400034211943d01d4400c0c80c1c01652541c42030b4800c903070003c1111840d81e100c2d0b444042800c4804800d50070302144c150780300003040141d6840c001942285c61500c50741c11044000c031820060303841e00d5005048500601d0040d03a10341a840d07a5079494103e002d8000400040300072506210551507050a03180c400d0004074164030380428204065a10300700111228104031404000a40c89403040400300c00421690300e920b201240c03038102c041d0a014001d0300c10580e0032a440c58004902c084c44c01880040b511021400c5d00d0849280203c05d420360500c440443c065a00180020381c0c5680d0f841404080c038112000050300025a207001001d01c6401e48000c3c040707a000c0b0384105002c82003c20540c0002401c244900e8482800345001d0b802c5015220007801544000b150004080c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 368482823 1250 368481573 368481601
    0xa1b111002010506010206090c181e010b0a030c020c01050f0307020705030111180307030b191512050c09011a220f0e01090501030b0106080c0903010c020309040f090803040605040c030b 81
    0x100098081e907145507500c2c021295100309512903a6441842903151020ac4122160740319000511804502c51207420800503a000300300a1303100f8000b9010006c3c0c0390344061b51610585104090a201504c1501e9041000074003a0090702c5000c00201000404215074500030405c00d030003400301a00a00c24451203074a030b0381d080c0d003200e81000004100c85039595000c0c80c01007601e0081d268003000d854180d481e100404180040c818640300c566560fa40d0350640c0c4481c80030100c400612240c2c48010808101c0c0c035000341860002440d03180102c04030001400030091884122031100116a2180e0310344a9049408500b21400311030f4101c850060a0f002c51204010b80d84801582c406a000206503642c4403150011182d09120180c007121990005000c0c243c03044a119030172044c00c0d4040c0d8104280c1000203801c48580700e840d500560300000c3c90207618245070240345c00e4141d094400300103100454a031400e0a10000f08001c1489070b0300c0300010200402850300901558008460040d203103000f0408079420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 368484073 1250 368482823 368482831
    0xc221e051501080c1b0f0604050a060c020606030a0602030a1104030c05040c0815040c0905090703050115030902010507120c08071220190206042102040b01050a1b1110020105 76
    0x4030002207090080755006411250091255880030392810048a075a5460070381904000c400d02c0c003c03142c94211041041004a000b40c0c000e5010b4003400c2c40301d1070701344201d07004107110078155084101000a50b503000306e003140303070160041c1000d43c0d6980c55070500001841200e11618a05030085030210070b01180140030400c0c1c40c02034408000806038601c1c02e80d0100012602647e004601011601d440d0401c0d4118080c8654282080384400b0b03203c50000c1c1503081e044440704000395613440100403810403480d000100101d5030a003006800d03410380008140d803003880c1e00546000703070384103072811007a20940d40e004401d42c02c51001c50b2145d40380d1800c00101c002800000001417904a14828034040300e1000a01e00c184003001400e00e08400c084600c8034141c03007102641c0c002d100f4400061030240d0481031004215400b034090b0082109441003104a400c040030716410800b041c444080b1f80e50308049134a0413401f4000c00d4804078000313454644294422244110b801002c40d1504c1c61032290150429401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 368485323 1250 368484073 368484091
    0x509030d200106050904080d020f0a020a0605220305130909050a0b1f030303050601020c0a06030b190f06080901020706021207080f07020d050a0207051c02030706020c221e05 76
    0x30000340508142600c0c031030b001306644040040040f07400650560000c003048154128054144078011401402d10381003040794201680080904400300705141c0708281d48440c0120541440061007215183c414008150003003c0c00740020711140300594488400004280c1024148071003000c500c1c0c003503122a4034141c01c0310b810120704040303094001c0e00307000300d80c0c0c00c40045240c5004502e591001c40c0074100140100d8151b006400c3c41d1880d40d03d03501c1e4600082d2800b500c02003480501c910601081c1120000d2815413a04451000d00403a640b03840c451017152100d140c10038140c0c41c2c0c900704500a10031204001c142c20301c005a10300000300d000180d240b141c2c120f41c888280035076441980da01c0306042100c2d0000182c00c628165440240101c0280c404100140304850f80d03e5100c0e0702254409a900310700460640080781c01c0d80840c40c2c1085164081d04403403014008801241d000329041d4214500601c00c1001462030304a11203009500c12564600344501d0b1121a0f42c056482500500c02034580100c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 368486573 1250 368485323 368485367
    0x2070906060f030c0c0f24020f0d090c080a03031d0109121d1207031218050d0311151f031a0405010b060403110406090513120509030d 59
    0x258412644640d804480d519103492090401ca041e04400800a0000d01030030302154407241c6002c11089012003240c1d43c41380c12560120004407009030030044090384401850750040040c05180f41800742a5140044225004545141d46140004020915400c1503034682b20b400c80140030305915800004601031800c0c00746486441d4102845e0030313210040c130040d0004500903082d607042da205d401c4011600709454005840c2c05201800a0b117036851600f000350103540031200c1482809508011b0780d00003e501d042c411001a0051580040480b162180d2032154822603000400c4c58060922032103c005407e05503007606030010700302a280f4030300b52240c0e03218203000070b60700f102214044100c1007565003005680d4584420042404106000188115203d54840802d881075486440292001c0c512465200706010b4201d020700c01120f219503c1908024104402c7c0103801039900c2c0f500c2c61550300711880740c440081a400070341da540f0406582c03d030148100c40480b008250700c0038042d5280a0030b102c402d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 368487823 1250 368486573 368486579
    0x308131706061005280e06180f010327030c08030112030e0a1d1b03010f030b0c040e0606211806011e060c0614100509090703151d03070507060207 64
    0x1110f5005034901c2201029000c4034414002100004015100000349800c00c3c517480406c000c0f401c19040086280c201011046d041500c0d413078070140e10a04158280307010098540d00c003140c050400007410140d0a1b6080114801c802d1502c03400001d0b4605400c0709106a4a585d5104242501d1401c02c1041e8009140036880c50020b20b003030b44041084400c0400c902c2c280f010b101402040241026001078402141c417000d40013407001040c040c500a280308064000d03058a03508100b08401d5006003e80ba02c1c401c1003005100c181c2c43c01c02c560782c0040095901c9034441c400592402018001c10001e01d200122040411160050180080c8080e07140317501525082c3e41d070340f0306151248100e80300c01030003081210402d01c5028070800d090703268540501404a00c0c507013911249810f01e8016190018000d141c1d20b0300b40f11905108a0943d00914510002e03c06c2c1d80c80c5440d450032601c3d90301840241a500d4152058410100d4904102c2c1d07400c40c441580d0b5a4201031034115640c001c00e210307901c05401800000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 368489073 1250 368487823 368487827
    0x30c0314010c0c030e010e0f03010c03020309160b0406140d092105090d0b0603073b0402010f05090a08190614010b0304030f09090519050a110403081317060610 70
    0x14940c0c141d4903407174210228000e40c006460042120001039001101440e80c65a1a0380c240240000d80344a91801039590a080c0700e220704140c2d0b49802c900038000c0381d940800010f0700b1002210102e405a203880c1c66207041c07204c074845440c1705680b02904c665081c1403084003401045103070101e46100c010103510140512000030740d0140546060303244c0c042e54140407440441c0305051120785c0041d00800740c94000307468680c142404800c1e250008092030841c40342c400104102910201e8005a4070100d0310140b078560f000a1600142840b80b1041000100c1e10401c252500103100c03019007071030303819600600714564012483d004404070039a4007a04000d07484c100c0035200e07640c01e0305907101e41c1c00603481c603501c98505803003514002c01348004103c105000042d400c2014401e44e406800c0813141715426054441001041d0344c0041d100c081700601e0405410b4402144000315011a640925501e8072007402070b1101d10802e0059010303a600640c8044c81186c1c150000c02c0e040d204d02400c0303030042241e9100c6003003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 368490323 1250 368489073 368489087
    0x510061208030a020307020a020a090605030c01050309030a271e120312051509040f060507081513060509070503040501140f0a09050f07090618090f020118030c0314010c 74
    0x141c8a110204081000f140c0c86400842d440501401120700c001903e90100780a548140d01102000790b590405000c185414410100b09810910f04941181800300f0320030b40b280300d403111240134004480d0340f041d000490240c2e40050b19012503d501c45040d540e141c0e80c0300340c590740c0369441c815944126021030001c1015400c448c5e41a0165103000d80488503144c0350300100380c082d01d203085641e402144941c1b19a05c607895148900d1244d009021038a12520b0101e041d91000342130101404a1a810001c0342c0c080a065040142c00071254425001c0d120b0b9441d400400711500050741141d0003208200e030b119000b000541c0102c0c0301d08000c211010302800c45200311002980d5071006100d0310f0000c251b4008542e0004500140100250354102042c051800e10f0803560303a02a40030301c0e0311807804000341143c040c1420107040d049481444207210b2a0355102001ca41100c5c0203040c8540118201c40564140700b0f1403024603841400405403503241d00b814100c1030500c8a00790030740e41c01d00030a580500c3c86100c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 368491573 1250 368490323 368490359
    0x506270a0803131e21060f18030f020d1e090801020406050901020f060c09060d0e15060109050102060603031e04120c150f0801031103010e16061404180b0a080a051006 73
    0xc02803c004000d031015002c4645e14460035030f02142c4a0803002600c0c9118401c2090f2003c1041940f0b00708241d9140290007440c03070b15001000d540105184d804055004000d084a120078145501091070038800c0c1901c0085058000301240c0d8030104000c03038200d0300003000f818103c20236000c8038032003100e031135105607203d400300d07425040c0c034400303112a020070704215002d81a0f05a9400b40454400943e55240e0328002a901e6800b061551303110601090b0358206032018007500082c8098070b003074076150002c41c1d9a881010701d0512449140074440e000e140c4c08405440113045020b4002200f03c00c03900308110803a0550107404040940c0c4101d02039010b000d038403170303035860442a01c85446a030310310b03183c81203030003c6003544030b41554886180031522007086c04982d203884000e1a80f284400e051071b000500b1018003114000155808010500480c0006c8090000f00f407104180403a403000e00030046280140141d00801c400d12400000404001d40031441500c510b42c2c503a003c100c603550301c40290071300c5101c0403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 368492823 1250 368491573 368491589
    0x909030f0a05030a020405040c02010b12070b03040803041b0b0a0f050a0f210f05011401050a080a02090301110a172206020d150b030109060506270a0803131e 69
    0x82400c401c00d0240010750b0303100070300306001821701e80c1e1103000c5420764244142510041c1d5503100c01c00e545250a006141070800707440020030b129818038445100502c0050800761450401200150800910b441e0b030300c1882c070008003022030b404e81e68520503809400c132800f400d011a00c00d006521400740705e40c1c10f66007031149956a95500401c1000b0980d804010f91026810064461101a607401c170745000d42d946074000d0000010f900d40c50034008600f40b4120115250402c01c0c00c101085107558001e1041360052180c4800681d22600400004d004112507400d00f240c46002140b03078603038030780c1144104004500c2061140d003950380d1840080315070824942a0b0030b001d611211381401292041d4040c3c140203035018400250305800f030b0189000f02c03a51b6445134240380000001400700000b49d014001c020316013030301e0031820903102c1400c0390708041c00c40100a070840c03200c44410605a03600004103004194510546c0d540d9001c2c40c0000841c440c2e10701400c9419061002c0ba0070390300698103d900e048484603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 368494073 1250 368492823 368492827
    0x41814070804050a080a050702040b040501030209060112140a02090906040b06041205070e041b0801020304020609040c0c02040c08010602070806190e07090204080706080117070303050d1d07050909030f 88
    0x1050a80c0d500d040504283d032140f040254000008101500400c0b079204c054440d5234131800548108819154142159400386091200401c01a1681201720b500b29409080082202c909807443d40300401070048000201c8000000b444140c148030380c01460445010340d202076450340c41e04148400d413441c0781005a001902040208202d0501032104500700d44181c0a071240c940d0b44da00601020700c801e90342907604010100320b03142c04800e00140c1c2001428103000940c11071810380c0000d0114041c0c0c021140c01691034149648200380314101c811030403980180308200300c01004d840101105c100b40110005481040350110b4015000070351540310b250814410001c00006603041c2010302040251800684952400403c01d480c40740040c10180010348000c000427403414100401418040e4091113017800f001010707042e4040c02080e448240c3e90582000f40c0e485500100b42c0c4020f141c0050750070801069031103580c003801000310b44002103d50403100b4500a840c1c0c07002c03080d01ca20800020704890001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 368495323 1250 368494073 368494081
    0x50d050105042003090309041406190b181f080604050105120a06020904090510020d0f09050d080c09060c03090406050103021c090203190b06120c01140f0f0f041814 72
    0xc2c001c5038030405d2003040d0f900b05a02a03010030b050b20320740700c0c6405089107044104941410034443c84001c07414015900d00702589032000c1c1100c00e10911007a8140074520301c0c29582c1d1500c0300030194181d180d070302c21304085141c0d20920081441c1c0741514a0b40c800c0c0d0902000050070303e81444100d00c02e1142078003800740c001c0c20ba0381d100020b501c107504894000c0d07224003081c004141c00303001e1105074018003600960b6884002d4074140854582a42c0c00c00b03214500304000c008600c00058101f0707440458100203a2944030224002c40314010001d40c141c0c0083d00040e0112100750100183c048a6010303942800400c4d2101c0041d03059000311900541025401514080f01194079000b11642600140603245400c1d503e4901c100d515811040541d000103800c428021603040a9a90007400d041d0603001d04401c0d2820800244001c44031001a201800086850401c044504045544814200c0c5509556100407030000c8883c0d005841501007041081d43d2449000e4140e01030784001002d0302200502c1f580d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 368496573 1250 368495323 368495381
    0x41a01060207050f030f07080d080907060c0605100801060f08070537230f0109080709020904020d060e040b0717010302090702011d0f1905060105060304081207050d05010504 76
    0x904911565145c0b00d0b01b0800c013420002808900050030310480a0308400c4403203030001d4903010f400340640d0210390241c0001c1090540c0b140c1602d01d5168002c1c0c0102307980d00c8001410092180c0c40d000a0410b51800000281c96041d9405072421107051400741c414483d510010020300180c4030440040b1041100b951124100300200b90480c01000d03041d18103422502c0e462144a004070940c840c01d2740b1003010807c103406e840e007030000003554602442c1c00c0203400d040001c1241c88400500c922000d042e00405c281055aa80340c055603400040c80a040210607580e07900420b41f21016a42940c5565103c0046190144100c2c05060350840031125103205918507030a011036490010b0180e01103560300c55035441030960509401c500e01c3c4c3d101008003810101407903c0387c140342d10841c1302c9100b80320280c926000510081801411a001111443c0d03e81d5a13500b0010754a124000f1a40c49a01c0d1001c200301505030081d018180d85500341300c0801280c1e80fa401404100c0740e540e010a207006000c1071448440b40307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 368497823 1250 368496573 368496589
    0x102121302060c0613170901020c040c170405150603030f09060a0306030b09010c030e010c020a1e121812030203031f0f060801031b1505030604060f0e041a0106020705 73
    0x240c07014044616101a0510780781c1464801c0e0b40b09030220a140303001105000300c07000030410400210030b81e140351045803800030755101400304105015580f103c6402c1c1d8076500505071000000040c051040e5140b0305032502d551a901c3c1c80a03040014007944001c1011400e00006491081c1c0e8101d6100746403c090314100181a085140c0c450300b00b64503054080700050a001016000f4080b00303001003400015940050251ba014403000d1000d60b243c00f550505103907000450700c010a03004100d0130844845e28141d0710420351031b000040c10121040340d07031444e0142c1c031400d5102030340e40e2100c101414544501d01c16407110240c2c8400707030069009102150036002030b400c2d0705505c1200f00038035005880c0c5d100d01c400d03280440340d8002e901080c0680c00400510038616117203488000c404c0140c0001606001d001d46604034885504410800e000c0005001e640b119480f080c003800808900541c0f460f69550360040d43d0300210780480c0c41c60580b80d0011b00362140120102e041c1d0761a42c01520500e03060400b0b20845c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 368499073 1250 368497823 368497861
    0x307030315050a0b0d0c030c270302030105040803010f0e0103080a18030c1d06041104230d061a0312160602041205060105120a0503030c070812090c0111010212 70
    0x1c80110100246681c1d405040c40f000b884144913441e158100c4d0b0f40d40310120b5980d03a40750000c0c1803c000040801036441806120241c4906c8054600d441c80c1c3c1000360808800c68000070340541c46c00d404d000c00d2002c080c005e1030407603d0300c0c03d0001200d030b290740011301004403c5c031004043d00d405101ca04032050040704035505003c080e0200203903499403512500c0c10308070a6840020031092890b0301d610250781302680346620840559040c4251213020221800710711840c81244115006207495985954502c20030214400c8011f001c1080d810300340c20540000d290503885090701e2030910034110b15501700400c02040c458503142c002c03402e107200307135000d94182080498100c51260b0b00f00800300b0440607d0303102005485c0504000d00340c80d818441403000003414114042c00740c0e400044001d0000c4c10010490f50b1080d002c80245881d83d0051501200500035500c03407020716219601044080040092041040e81c0242d030381078440400d1a01c2e0508034410081103c00d0803003160300150151104415905034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 368500323 1250 368499073 368499101
    0xc020103140c0318070810021c050a060906090b0109090e190503090316140409021f031406040b030604141203070903050706050a08041407120605250203070303 70
    0x3001c48500203807010041140d202e0b150b50008014083c03c808540000d02c0d2402140340100625418200c0280d901c01c0c1c2c0070314601903140c0000b5050f100107181ca0003150030508490041c40b403030410f00c0107240a07042c0c0d8082d0002c41403034510001140103950088210002c81030b194826400d00f0540304401030613030302070794466511815218841d50108100400407546c0a50091920f42c180041010b00345090074420400b180c0013000c0901220706502000c0000b490103c0b070004184441e480400d94400341341e682c208500001b5030020410326096007011052102120400440b40c0e20700c02084100d4902c1100207805070701200004000400605080800c554108221040c00c0712000383c2e03584030350040f19805c0c0000c170451400c000304a410080b5002804940c2007242c2403906003070b801030042d5030062018010701e00f00460b40000080522441c00500000e0381d503642d01c04258189040582000e82d0306003000402c40802c40720141103074070407040e10320840d0701070f605d0160759450031400340810180050b9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 368501573 1250 368500323 368500331
    0x100905041802061b03090d06060302040c0806061c0b1206040b0a0509100506040b1f020c1518010c0501050903040f050a0b040b0a0512040b071211030c0a0201060305151b040b07030c020103 82
    0x351b01d0340c406285030920f074072804d4003050303407800c0d4418803040e14503000109080c4810a424031085560340001e0b03601024000d48031052401d0b19110b1100901510823005410030b0345068904804100817a080740706030700a02e0004550b4551040c06002c680048500508a402400d04a6001c013195044541c00a000030000f06610110100049001d10325906910091540901002c9229010701688007a070000f1113a101109048102e03d940c98880c0220084450310720100c07001542c1e015100b4050605e030400001c0040745005c90105035070381c2c001e025040e08000107900018843c0f40603850401900d11140403a030400e458a8101c0030103400c9100020305000051100f248803c00507a422446a8054900074000303080540b40980102c1c0042d94103003050781044100c0d02e01e200d883c804c8a8012603d15182556012071000480c01003029802c001e01074040c50030b060500d222485005c50054030501840d401d00201840310708107604c178621175641b01c40d1003403010001080c01003000c04405801818085 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 368502823 1250 368501573 368501587
    0x4060906081303301b02071a0702010e03190501020c010b0604031707032d0305090c0904080901180b210108071818031101060815160509100905041802061b03 69
    0x20306a4180204099010700b01c0c0030b50100c4680d040102200070308e102c804800b40c62081341820992441401c0c2c020b814024510107514031924100000c07960841c243c118414001781d80e04e03116010358040d51800500e0342c28003180e0641ca00e02402200c04890380000386401d1070b10b6203d1007500d150001c0c0c80c15020b1000c100181c0c4848213521241d8a01e4103460203d08240051060f005001c60302c000d0484129503001c03e2003000552200c8114503001900451882d0b2170b0500003004031403041d588007462640e4074400c3e01c00588422114060500040c0c00e0101c50042101c082d4200f40c5980300344645069503102d250208840007100385a9100d40c03290300c80c0482c40a804c0010442d0940501c102240081c3c1320070001103044000f0310030301015201e0540602a081c0c505800b440c501c3c680035100c07028005640700000c511901840454a04081c00b0701092500034031100080c6ca146450710580c3c0c0241c0c18a0b40c40300c1d0390180c0710381488a20341d00402c0700381070000c00381c0702154020000ca503c010301d2000700110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 368504073 1250 368502823 368502917
    0x3060b011e05070c090911040506060d1d190b01090c03020714030a0305060316031b1508043302090a030c090b120601030321060b04060906081303 64
    0x120a82021a1100707941da0903603143c45003000140340e01145000e46005046d10010b80d8400c10010440340440d408111921600c0004900d071103045101c9000c0ba03d843c00d0303c0c00c054110b0304415450009002640d45110700480c1541c0459183c050007052007400f13070014440c1c1e50f400d030300c032480c09140791400504040541d5908003c1c2c00041810712034590021520b20f400340d41c940030707030381d070104082c1c020f460092220825541988243d0100130081c0142c1032035a005461600c040c4e200610100c1e8032400200ca007140080c0a091040e1010b07104060020382c0c1081d626050b2028283d1f003a03114205207031010700b00844800a410030b001c640e510009030200040480c02000c841009408841400a1344120000412011a00c1f8009030b0140e80c009000400100e40c004640c1c142120901e42c0d62990b021041d1a030700001c00180d0840d4524490210f0b02080c100e070300118100650b01d4644900c030850725003411001ea555403c250042c00501305101e00da0b120100000c881450f4905454030f825010100c0c805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 368505323 1250 368504073 368504117
    0x1a06132102030c090727050906180a0902061204080912010c0c1e05010e03030a060608060a03031b0b0f040605281a030604120f050a05190c080c060115050c030403060b01 74
    0x1042c8086c6496503814041e914000083d160003420032a14041c0c80081d1003080307078030b503003004117a070b4200b654901002040d915107030122442c00700075420402c040c3c606880d154455400c0586002d008100c400400d10641205104200c400402d03500c84049441d041d9546800042009040720301240800215a00041c400d00400c420076455001854492908143c00b03800ca8a81c0e074420000c000c0410700b03100700c54032401200c0d0706423900341c078041c40b1010b4600c022074100a088000207080180640400c41c001014040250045108850a106a4580c61005803da2407100102000d43c144c10342c4014641c4034940c02180d407112441c2c0c0c045841d150500000c0d00b0010111429200f0200d82640d011b81d141e800a04504032080505049052201048006219010382c0e6108207602d0001510003503060302814850004580c0001070300d682d0b2040303100407034039048284120303020b6103400c5144484050054060300e003050ba040000358146807031521410302500d41d550400f41030101c0d000e0000308106803400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 368506573 1250 368505323 368505377
    0x1e0309132304020f030109030e28080c0108060411030a09030e0a03030503040c0906060906050c03070f030e030106080c031f1d0307120c030507061a06132102030c0907 73
    0x303150300c030320380b0b4014000d403401009101d0744246d02d02000000080d41240203210744050983c1c034010101c48029104030105040f9003c40782800420b44002444070002484c031004450a0741e6003003c984500c410302090f41c124240d00c01080d841800010250240b42d405202818007a04d8103100c102c0501c008211581c051350000d400150340007081006105894806100501d10306004109080c60028002e01a0b030041c014a0100500010b002085801c00c00036100d8150f004034070b149400c0214640584040c00c4201454000c0d42440000905604081419039100d0f80180141003c11089641c078055600a0010700c06180d0360380180b803000c803a443c04500440303c0104c000b5559002a403e03e0200c004581850804110300b090f1180c001950110648030000c1e80f0040120f41d141e8004507103c001030400c90b6290f0065004680d14040010a045020448455900350000800c290401a503070350706294010350554460100c100c82414080590b176884019442d08698802560410703003007040c031100c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 368507823 1250 368506573 368506631
    0xf061d131e1106030601170c0c07060509011101050603190c120609021905011704030e03010e010209010905180c25030302030703110a0f05130503120307021e030913 72
    0xc52181c200180242d88801840e800c8442c03034107518100780002c2810381010302c1040702d0b81041000c191202400401d03100c1d00142e008c10384483c01c1e200e15008205403c0b42d104113001410709288980d0121062241e035003d40e04c0a406000c00c081c46900076400f0140b03540044401c2c4110243c001100380700c1c400300c00321680c41400d02088102e00742c01000048491032a00003036101843e101040a82e8000d0616605900c290b0302c1c0405a0b6141d040075034280f03544000094065090904140c1040070640c010b025484098079582d001c0c540360420322000d01601160030414a058102094815400c0b01c05402c0300040000c000c00f100b041610980c0c10394000c000110302094011040c080d88507050301981801400b4140e40364282400346000070a550901c21a810902c407001801c218900c4680900202400c7c0c05000c5859503080301104903031950048481c04c0040c06107000c11810b0720713402c68100c6070b014807102c000c41c200300820080040d0314120b030304400801561400100103010100f8215040d4510403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 368509073 1250 368507823 368507873
    0x280219030201110303152b0506090d02120913150f03110904030f0f180f091404080a0e010e1c0c170312040c030501110d0f061d13 57
    0x148005003003800510f0a1402c260400d100300503c00380100380640c0c80c1203040703403010680316000b002142c195050100c010135403c0310310030410620100040450040102e9800c0380e1070403001d01ca00326250a0103140c0340e50b100904002d00305940c58001c2c0b05a0080550400000c0c41480e220240f02d4103042c01ea00c0b01c1c044032000d1030108180080c5c903842290324042a0741088461038141d8000748002007141a040601422160110b002441a07010452101072000e01a1890380c03105040755802120b403284080b42410502d207241c0324038241c40d01500aa038450105800e2034003441040d261440302040c114100910402940305598942404210040885002459035030440c140b080d040a003d4100062610f0b42a600d50410080003084814104501202188940f0741d0301d000d049510346a0710190166003403103500d50004e061000100039030000c1410070002041741c0d1245800707440e02403042400084800030718072501500b110105600038100c0b50031742d0021509549894030503840c0121244440ca07030f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 368510323 1250 368509073 368509079
    0x90b1c0509060a0c031104051306050405010b090a08070609052107170d090303081303020111070303061d060a0b0307110f06071206051005070314120402010f080405280219 75
    0xe10301c01d0115118507445e040c4034007181e103c01c910b900d20640c401c903401603411031a003a841c0e43e099403201c4040c0c6402081400036580d16600326140d600554078035840348200100005200500150110843d8019152480d004c0d00c2c1408100342402c1d40c84020032805811842c445d03804009200c0e06c405401c141d5140d0294050140050303141481c103507206c4051091007001400826007101c0c1c0c0d2070f4000c0c103840980b0590700d040e14049014100d07400c01c2508400c0c000c1001c1c800c00d078054101c1e0040d1080f1514201f41186040c2040f10f2400c81034548541225001c02c00b4042148804001d55000300c05040401c2280c145950207480d0030346495040ea46a000801070004165001700d25401000f088103062001d00c0c2407000041401d0440c1244006100002622004150040158080800b2650281c6455030a4061140c240f40c03001ca40c1240050480b41501c1400d03130144040f580030b46d800500a1403190100050b06130780c12080c8500888031403240a201c8016903915000d0302d40f010310080c40140300d074a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 368511573 1250 368510323 368510341
    0xf0804060f11070b09010306080312041a0c0f07020114070606080c030d0504150905220c17060d020f0d03030618020a0f03020906090418021906090b1c050906 69
    0x41c12040a0104240a0850802c1c010005400001e40303d400000c41c0d680d448000041e1300078071896100764450300004c5003030b20f80002562651480b56000d091140f02e0804070030442299003d04807030802c1c0c81841840400100f0040350082c002151040c10104100c100b02c101501c119040366000311100d42c0ca800040c44620003d001140301c101041e001040c2190420802410341e024901845a2103142020b14144891040d08140001d00e00a445042203c62101170042c842e901007007105e1001d42003a404000035842041c030040840c40220684007140c60303a00c00c104841601c000142d9021400c2c4880d52003d64a240f450700c0094400c0d140011601e02e41001e0ba48110050410340803031038414080c010310b903a0020300c04840017096240041ea2000f003480040c01502880010a400514101012045d40d202c6403801202c14002c489020f01181820441e0000d000103001e818000380d150351003044681e0590000d0140799841c52009500541c03000404000c42e00c0403516604079034410b00234041608 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 368512823 1250 368511573 368511587
    0x121308030903180406181a33040303091205011b0207031a09031207020f1204360209030a050303072d08070809030d0504240b0310090f0f080406 63
    0x90591302407003104c3c0303401c03000c06200c044500d18004160715041d065110440a4082496007440103100035480e20340c0c00d0210b0548020b000400540d0040002c8030074048000c0c00645045981c90b45d126615181012020038218003108003c0382c00d5901c0342c058840a68000c43c18418155055004206107403543c240309100e01020140d00690030611800c0c41300c1d040010040300d18000c040340940200f034a51040880c600321036240030310918003590701018004150f40c4000c1c4216502010050b104030010700070b5034070a120510a098510000c040c00e001020702540180c4070b4244001c1c243c0760911100d0325400d080d40d0040f00e030301c03000447e00f81822004000144070703401c40302d002400e4602c0316010480007030320180025000909201100300010300c1104c08004845181b13203154800c1c01641024a03103000380518004110a6040e0099040014a803c51041c0442440003c0080083d107400d038940000403c44041c00b034030098400d0342860040381c00f9038a8048800d200b10441a80c540c50154018004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 368514073 1250 368512823 368512867
    0x111305010309081b0a1b15050a090302040b030a140102090109060c1a0c16030f0221032e12021809060708100f180f05040503121308030903 61
    0x8945402c6002d40441c03c0d4800f524800b54503010102c04144040301d0040c41c284103070078010045a804200c43d962040805200022640c034001c031002040b0210800b5100e500071150318400061a1107002c00240c6002d400401c070081003d07064400208142d16050204100c003040d03140c15a40025904042c0d5a026140c840104040d140183d4111601ea48400040070483d42411200007944081000f00d24517030101e582c196503444c1d210102049600d4050046001445c2c444054050042841d480c590b90f80c1c140710aa009a5544a245030f8880c3c02c641141c030121442000409030b0400221983d2901c90030a0300900b00140c5500122801e80c81041710392032400c40c0059001a410090140c908030006076990010018104011140c1c2c6e41c1c6001e0001503803d41c8142c81c900b604d40400111080b15001c40c216100a00c0301c144001c074404401181500c0701a0360041c15030380f04005101c080a218a0b404c0e0b08241d40300d59050302580103884030641c5800946545425030000141c880381d64036104200100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 368515323 1250 368514073 368514077
    0xe030a090e0915160509040f1505031f02130521100207020a03292e1d0c1611040b0a0602070b09010221070209010803090a030204090201020a0611130501 67
    0x360b1000101e80080b40d9001034607080e04e040703104c0c0c0c450081500407800e0b181054805003080020084552040000c1c0001c1910103811134034494001c2190b04000c100703c00c508030035100c0c82c80845440e41c1070000952165005101882ca800c00102d203c1c2c0c0d60b1031034008a602c140782c8601507090701e0f8000505012000b600314500c10302c10043c010060f201c194186003100e802050500c07400c10741c601e40c960003c09048100107079101c4002082003030300703200f003103401a29031609400806110031000b804882c1c1281c042c1020407440840d4104010001c0c090a9a00c226023008450601d004401d1001a000030380f54103c414110340b10109202d81014480c0c54400003080b03401c0d44415251a03000382d141c080c07a004803903403980000b078690700b07a03402040303419003c49a1020348002001c01004510302d41d0048071007248100d41400000030007450010645400c0d0f04010000d42c1c4141c9954200700c02890103007006c0703056000740300801004c00d00b20b202e440101c0d100101c1250340d608030410aa0390302e802c00e80043d41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 368516573 1250 368515323 368515333
    0x6080c0304052a09011502070e040f020d020105130b0414010201150902030703110705061b031b0a11010e0a060b01050f040306020c01020702060c33040609060e030a090e09 75
    0x4501e000900740701d802c800d0031207401c011410265040e0200b42501503550810785413400081c4002608050201c8612070740e007640c04440e140c10758007000d42415203000e880c0c950900481c034050320f081001e00c220588141042480c3c5446510f407408111250740c4188031400d0040ba04000c0c4c190000c3e20b000441d03000748000c0003040802101d010b0480c1050252244c0300e6808400502d0385c502a0b8805c441e5007400480c095243c040f5840d1040d82e4000440c0c441072440035004190b4a5404880e050302e020324544089041d1085846140e01c03216040420124100150034840a1b800102880382c1d0a21f00092000b6000e000484c0c10a081075071040000c0134100074081001c621151001c0c070942d8240d07544941c02590710280002e0070b50281c000c0340800395001600050200d17030407138000ba460704000035140410596800035840c95440011600302d195094400c0b200040018943c1d901840901d442000005208143e02c441a40303150480e081c000c0100d13a270300c074040c441031960a402d568007103041ca00900c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 368517823 1250 368516573 368516581
    0x308060621060102030c03120103060f02030c0f030717070c0308280e10050c0a1206030f03050a020a0b0907180c050406050f0705030d0204232107050d0b0106080c03 72
    0x800c412407108215241035451000b00d0000d80c403d108452a083c201000c4039243c0450002035140c100d420320088990900c0e251903605040818000e81c4d2003000329683c0682040e07400f122030740b10340e07200418102c03c0000c07001c0e42c074020703800d4185042d01034606940c42c0c0e060506540341c054000300c0d020701316681c1c400e0180c81c0d1340e40100188050340741c2c01800c1603000c1282d00303c0000b4585482c011594940245082808000204090b0405002d0402581c1c2c0e50404079505002e1840031507641c0d000150884140d41c0304100445c1c003c40062544120b684100e03241c48885132030341c510700c00042c2c0324400203801c10074080082c100d65200601103c602c2d42d90800120038140030141c1644503a20a0406015003c103141760141511010b42d150282c204050300e940e54031100e83c00009602c5401079181403040c00b81d8001d400700800c100c50140d20b2001c2c3c80d280301c3c82c03981e0114001a40e130f45031110f404d500c122400403450742c0700d00701e154801074842c2a0415a65040a002901d024030040089451520030700400c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 368519073 1250 368517823 368517847
    0x201050f04020307090c020c100503090712020609040c0e040501030309060212190e030a1505101403070e090f0a11101e05030a020f07051b0607030e2707030903080606 73
    0x55005c81d101c1e0302c0001113001074208140e0810b000507480941c41042d0000c403480c0103801200440c0304d2212a41035400440d02c0c2e10f903451100b4a4510b019411900c18841e842c614140741e4003c201207581820641079100c1d07100005801d9413800d030011000904a01d8081084540400042c00c1c0002c180451034240f58031500f01030180e80343c207403500c003c1000c3d80c1e84600c0c003514184680d1005982140c0314079104441212821702a205c10360b0102021008080c00280d16902c0349420000950010081c001d1280342c1007400e241060090b203070780c0b00c6000e481408211401c0030004420303e01d01c1600000e404c0382c041c108009540b45e55140c22000d200d05904402d02d268201088110344008a081c0b65489440380ca511400901407428030403400c0100044100a000f80010403901102d084400302e0340b116551406e0002d64080c00c100100800c0c8503100e00c04480c60b094610540c00504296182a0210391200145404800303503201004a9030f80e28516082c140e12201250788007505694141c50b1140310400c3c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 368520323 1250 368519073 368519083
    0x9091a0d080a0c0b0a0608070f0e1503101404060f0c0212030a0f09150e030a02030405041109270a1a0402030403181d0f0103080a0c0c0302040203010905070201050f040203 75
    0x30301c03840d0006400d40040740503403030032403900b03401442c100501c0c80c00d9400d9070014030490144000c0c1d07105400c0f00040310060b814000c0b00b542c40070403004030a80c0b00d91140901c941c1e8040d40c002d6060180805484c90f103003292140140d40c0d40c000c80c44c80c845081070b09000b130460b0314040340e03001064104459046000d400060000d03a443c410100d0603569507502000c03070b0040c0200b100c0313001c030182450420b0080c0300e1043c4180345603e800c020200f000c1c50840c0400c03580c0b485141c5070503001d40c00a0101304110700d0540e0003642c0c80084159440e24100f40e004c0000c00d04001c182d450380755000b1124506400952030401140c4c0a0400d110400c000c50605a40c0e10841c01c0e081e00c0644295000030001d010103114020300e402420360481403030b100a480b4210b4002c545002603000090340e4803600024000c10ba0458614100c0350491442da1901c901408201c8450803080c4095890f14a0840c0000060304c1743d1000314020030000078001800c7c2801c0780000d0030f41e1005841111034402203400d00000d40d40c0860 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 368521573 1250 368520323 368520349
    0x902091e0339030703050c2e0f0e03070321050c07060302041508010b160812090f100501030c0e040812150901060c030e06031021140a0c060e0a03060c09091a 69
    0xc3c008c41c6000365900006001c4152000541c21041e0480d00d004070541c01803180900000141c5401c4c40f2072403610141030ba0ba8010f48800717000a180310f400c00c6c1038441000c0f805444480302c1e103450b52803ca00812114a031540640c04600040e900050400040a0360014030310900b49500d044110f55240a06081c918098416196a0100f01e1041e02c41040400d00403204003101c0100500800e01d81400032075165803550f90010f405e40908943c20010318038a00c03466041e640c1c014510f211013418190081003d00006004448001b030402c010310300c840c0e021141600c07402862400d030400c5d080841c2408076403035043c0c4c0100244403000b451100081c0c0c010005000002c4150342c1c4030344a90b9800134066114420394094107240c03010200b07480261038140e00506205000d0f280a10300c1103016440180d5500360a54041d202e804071110611003030b4403900801000d944014140ca011039220b03101c4400300c401100004022500c0c02c0b2081003502024080d076501c216040a416415043d13441c04100d034546240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 368522823 1250 368521573 368521579
    0x40b270c060f09100918020f03130519080307020d030b0f0d0534140d1412040e0403090501030c36030c0f0902091e0339030703050c 58
    0x462005480c001c8582a070320303810001002c0202d01000700002a000d041c0078010318070710600340d81801b000705010780215440d00094120803461952004202d00c2090740c00c0604031414000d04c3c0b503111004d0594070b120b07071000c1e01a0441a9076810201c201901e440341e20841403080c1800d0001c164400d650300f00d0f6285944109a580c20140324040c64241c1c100034000e000402102c040410480012403010340800c520704900b80c10242d07043d213906120306454180540c284d40181030200f010300285d40c1101c3c0ea110049620216181000803251a444030780003034200c0c003481214a802c0000303040c1c0c4003004100801c400e00302000110340340c0388011301c02041c420b007108940007100950342200116000350341080a02d503201d004050749a1404200814061107200d40544601c003002c20402640d00c2152085800201100c1c4846180d6118031801c80c110017589516015119007205c0105035940c41d4024000b04810200c00c1d0416120340688542007100346a029502c40301c800d00000302c00180c964042d00040b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 368524073 1250 368522823 368522827
    0xb180c010e0f1f0e130207120c0c0305010204060e0112090c051221120f0f15010507060f050702010e030913050c07060204060210061d0610030212040b270c06 69
    0x2040200320f249401c0114140016a9800c030b000c0c91070340c005004001150300300c440801110201807101d0584c01b03004000780c809145080110025400380c000c0c21150761141080464050b40c98544608980103980050301260034644810840c4d80d11a0000c6007401071403d003000807101036110555048207074000c1a010b43c03c021104074681c070b01000b400c038905081ca0906600c3c1122080007134110b4120300c001100c0c1c0441c0c1404070314000c1650114034400c036081c9072465490382da11000844106100020703107051060420844000c40d92500620b08156503040c00401c050600410090071038820b517400e4007843d00b00344901c8200f50341c0e100110088a05074413020a60b500c5102c20000a0710030a43c0041c02c96200080004060780c0114050207402e042c038408001d60b80d6940072040c1c081100220100815294500066245c5003120045480000d030b49401410040380c80749140d044881a1001c2e07852860b90400c00c094692511204104406043c007500307001301031080119a11113010307140c50310900d80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 368525179 1106 368524073 368524099
    0xe190e010f08060408070809041d071a0f0705010e03070501140601030207080a1116080717010e0312090a06060b0a03110a020d14040e040b180c010e 65
    0x4604054010f607a92039a40800e10381c050f140c11240204240004100d0f03444510861055581da040e24a100d2000400200e08d460050344c0301e0b10344c0307036441c9160070404003421055441e258241014940c0707071a01071810364094142e40c06401c900d40f101007850418840305404c895042e0051110340140c1da103c202c011400e074171a080000d0110001040049035152103000351201007040d0006907042002c020340300c1d420b4108640e01c041825405a64240400c00016a400085003016402048017000341d2403110b481c0d0156625615118005100144000074180502c1c1c00980c1d20200410225846440700400c0d500070984100020340740540f071903410400e55080742c4000d4032503002420055030006048a10f480c40100340b004d400c01c144000101d8a05841d4124011813103038040c14203078940300158603070740d0401018443c1103510540105550703236008410640c140c00c0c15550140c00c0701c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 368345323 368525179 := by
  have h0 := BRFrame.cov_init 368345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 368345323 ≤ n) (h2 : n < 368525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
