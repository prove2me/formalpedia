-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5524
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:02.191121+00:00
-- url     : https://prove2.me/submissions/8167ff21-ff5e-443e-9eb8-04677572d391

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 993345323 ≤ n < 993525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 993346573 1250 993345323 993345361
    0x191502010c110a260d110307080f0f060402070311030a0804020307080706020d050c0c03100218040e121309050408040906060509090a0e1626060702100207020d05030a17 74
    0x1c1209922060381e4803c5004003403450820380d00c4010001010050054428842d42c0e2002c46881b548a20b0414000b078102c0d28000c00001800c040b907030070455025801310189074007403003c580050701e07145a8142124202541110046203202c0021654469038126a695204a2080303007100c03030b43c503203c5103045d4880c60b59200f0b0300056480b55081402150082014091004c42c070011901c05816041c0024070f040440f0501c425055400148075988401401100d42d1450003610b044c40642e9982a004e0340c3d44543c80600c5c00d006002143c082c3c1c0e990704403503a440050801a00510460820f42401c505552081c400e0201451500b84000380103401401034403241500104600c0c41d42d6900107024024120702110030100380680040c04484103c43c249100240000805401c2c00d091402103000340c604507803540f9030480e84880c040000d1a0360001d0f86900e034488070840075881e4181d620110303040c410b0750a0300510a020210707040301c003550300408449914801131042e00c2107455100b2403800ca210851 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 993347823 1250 993346573 993346583
    0x20c0703060b100909110702031014091b150c060403120b0405090607080703061a07111503150d080301090e011410030201210c0507060e070f05191502010c110a 70
    0x60030041c40085d41d005003050010060786525000f01540003d0602070f00d03000ca140700c5950b544407982d0103400ea1600690103c0280001c105c00028000c0041d51241c0c00b04001c1d102e1000c80054100700784001065540040e130302011a82207081503c0c01400080c403100c90700705035610f0300c000781c00329207001d014007402440848060056920360007011141c101c4010b018100303154888000050180c43d01168400741d05910b034038a45c0b10041481c00c041c24001e403803c03007442025490014001c401203a01142d030000d03002c44065162001550100343c1c00c589240c0050721110000c030002603801d80c0381d0040d4200c03480100007000706600410f003412140405441601c40c40c4402d44c000d02c01540503d1501d18072851000d0140341c41036010790340d1401e480c3c0c02d030b5492001403008144001000414043c00c441070440d44060107420342003206c0d45016040d203102e0240f01d0403851512038100201c050a100c0540402c08402c4d03005003209038041d018000d4115030300d0000c0e690800c1ca034801080400e54031041d036404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 993349073 1250 993347823 993347837
    0x6170f040807021020280506072001110301170601030c12060612050c030607020304060e0d110a03060b0a2c180604030903110d03022509020c0703060b10 67
    0x1540a001e4009100b03600d130030521081144000a00880c1451642039003040e0f0000d1a40840580045022002c0a00d040200d8940c010b00c000004034041492030348030410f442c28807200c18619840c00801125a02004200e502c0d0085905040340d00d41c0045050300c0010110300c080c4001c40010035665102444007802801d01080140950610340e4071144d00c6c1409110041900d03901c8000060301d484000783c08540541c4201151075880c1410f100d10760340056130340051820207103440406006824603401640c0725054000d41607080012034040e42c1c0a1440c0507204059482d100e241a10080101c1c5c0043c41c425810b9407000944945414058100d010051042d4010402d4940c100443c0c58170241000765025203034182c0203003106003003003650700c121b0213a900c10600d54510300b04071510001442c1141d0145030380f1942440442e400103a80d080088d941240314002c60660307090368131400510b400c0230550600024515036101000929402507a001f15003c00501900d00100505c0c3c42d40c4003007035000710b45c0c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 993350323 1250 993349073 993349087
    0x1005010c030c173c1315120e0a02010207050d171b120d0c111e030d0e010e0f030322080d0203180705030309010c14100606170f0408 58
    0x80c88000030385103140600c003810131800300d44601d40c0502010b600103204c40c0d4468800c020b01d1140c591542ca0801c04040d49140c20341c0001410344a015038003505045911071407502004074410b146e4140340052100c030420000e08440f40d110b44454a1020983c014400c2e050046007d29150040a0301154003102482a901c1e100502c0d8400d9005403409004200040e5100c5405801c1032203003440003481007500c1991400340d45004011900c20002210400205107614601d0341c00020b582c082103110060200b4403c04600411851032083c466140055070a0202d4a595204150441d400c43c480c410280c4104407043e024280c0c0e05e010454014004110860600460b0601820f0400a40b0b000d81d095506c3d20102c1182c030700599009407008500f9404403070700424008000d0280e000601801c9016600e00122400003c04009d00300c1406400c00c0d50369074205044500810400d0140400301e0742c14840e075550740d90b02402d5449180b04a9041c2e8511200142c2c5004c01d40700b02d1442554419403e40c24029 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 993351573 1250 993350323 993350333
    0x1090f08031c15260309060901050c0106031403040602060f0c16050a021503042f010f02070e09150a180b0a0209090a050603010c170106140f121005010c030c 69
    0xc0048904010196a03c001c510780c200752840080292403e12650100d400d64840e602d408850342690a0a09410038044600070341d942e10115840704800b46001138850b03080c103443ca8010f10390b980c001422401144008440c1c104044042c10884030340e902036404650311490f002d0707a041c0b01210801d81c3c825081103005003000c006051580b015000e681140e11041d01c9078040f4000d20416559175030748043c04400c01c420485600400c005480c1c58030200c598180142c0081820801c81101c014180b1040c1541190410700c01c00203600200031240703204000781810329140d501c031444945142c0c03d030300e070310030000310300540600401507508802d0f61685860000c945482c1d800010150003030306429003c0009056980c0c5607aa5107000b408a1000040c00d41031180800d42103d501c9003c81c018450701c0c11143c60908408030780306045481c982800407a079899000000130728403407044d13110380d03202001c1184c500388100e2012a0344207041034940d010702e007601d176001910014004640100081c1c2c089808a000078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 993352823 1250 993351573 993351607
    0x807030e010917130312081603090203060705030c0d060e04111206010504091401050403120e150f131406090d050702130b0402040503100b0301060603020705282001090f0803 76
    0x31314503240c3d03014180c4036a40c044a407400d1130302c0c04000845460a000003a6407201c0c5c28082d8180c141402c00c00e141440d40481d1712410010224028451301000140030b10b8104001c50712180491a8100300e513980358560255001e1043e41c0076035103c2c11201302500799051900401480501c8000200403d030700c0c200402c00a04050502181c10302d5004200c2174103200c09004090140c0e00c039031252441c031464600c401d8100c90096000c1c003501c0d401245020181402c8403c0d840c0c00000c0d2141d031541941e11b04c90588004c4030000e0000b03089883c000c212140d052004140d103401002c1c84c1e400e0f41c2000b034003108101e58a000b001d60107580030a1540c108100400164800b42a03000c000d00090b0a0a07920310010342000c186558aa040c50340b66213400125250a02c40d1102503c1c2504085007001c105855042d664000e10101c0032060380c8040d00c1c05002c021036101c0040c05c3d42c0c07144460440c61103004910342d41d2641301c141280868011240814070310410590340b420754034507034015402d00c5420200c000003a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 993354073 1250 993352823 993352837
    0xb04030f2a090228082401050d0f1503031206052d01180609060e0d11011b0602040902040617240111010e030a1206050a030f020414070807030e010917 66
    0x4504d1040f440d10328103a0070705040100c0b0150340742d1000901d00f40f0000c039415911540c006000101c41300c9a004140e81050946030102d1180500048001d10b2043e250020120903080003444d504440000041640c042e142c00d10b098243d05050003a20740d0b440c14401007240c0c210b21800011425000850717190301100b0312101c44041454609062422041e2144400c42241c01c02030005468200c10b00580b500024580b4001d8015607455841c08030a880c0c03689203518411001d410055913270990810051001a901000350b04036008650b50342e99000b00b03030025841440341001141400302207042103001d81d114544190380340310442e00e0740d590440c15424005c0c01c80103614180108000e03c207130a40000d20034074802501d600011a51400315041c098400b10910340c1107019242081002d100507194240780b00c0c00c40b5400091101b0404007840050003501e004010310700070810704000c0202ea00d41c000002401007543e52003c00a01e6a40d031401d60076181d51480241a80032035505002030207003071000401c00703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 993355323 1250 993354073 993354097
    0x537080f0f06092107120206070905010206060609060715110d0c0f09031103030f0313061b0906140d0c0206011509050303071e05030403050a03080601080f0a09030203040b04030f2a0902 81
    0x80d010300c03a46c512020030450200d9100680c881803c00601c290001459400341409000406541c80c20b030f80005c1891240300e1090707005560125440d8200b0040d0195441d641c6c071640c0051284c8080d0f610f080302c890f080000b2007206241407041c02c0e428540103e107080443c061595800e903800d03045032a0780462000303d0310304913054401041040002c0720740f5005140180100003185040c000c0d90b0504109440355080c0c00f002401c07664888a41d0030707030803464603001c0703230118100801902001e0b020f22200e8040d160068444900344032000329042e40c00303d5100c0c1618540e040c0385109640c041c2d41207501e19440d005058069204001c0d150118603201010b64000b1382206644100300e40c075503101c43c25500706901c11600743c2d11440300203082640202c3c0781a8070100a203015051403914180701c0c40240c4c07010b00011580e40c0e071204020b082c54802d02c220f070b003d810350491450b40d90380c0c2c0c0d2400c0740c00d10090a1080d1540c107000204013290201e5500c40c900758800306203a614081d4101629200250302075580b60007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 993356573 1250 993355323 993355327
    0x2150c0f0904151d16030e03300c07050d0f0c020607020d06060f080c2709101e0f0902221401061e0201060537080f0f060921 55
    0x60312403c201038443c85254540305160050034614200100c0c95051050070b000d040c10107103444150300d800000e607041401610419452704003607084910010b102582c2c0c0601649404041203286400d103001070800301d00c036004440e0740c074480010440780c00030400412000104058030340f5000d0b103844000341184500040c0190298465070f96a4404c41d11070b0750003400508240103041101c03031402d1002c0000d10405464400c01207891075075660f407545804458007032000c04403010600e843c10801c207105100c2110b9130200070111000c00d40103146072030070a0800b54203043c529041c024050601480d04055070242644c0240a0b03441211a5404055045c0b0304509a440e80401c0d0300c80c0400403080d00805454580c154001c04e480c120b18441c40d504840c0109582c140700041200e9200e880e100740160100b000d0040c600d080c2000c44550852441502c0d00752000420004a0300010214146031078003850011070780b0825040356020380341d50701281c2c80c0945404c940401c0241901c081c450b81484000200424 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 993357823 1250 993356573 993356579
    0x71a04081606140315040513151506050c0706030c020f010c091d04020d03030c12020d050f06090412050706020405062a0a1707021801030302150c0f090415 68
    0x18074008a003a9050101070300500304000340c5801c070824280b030b464001000c81c61440c0c805540d1094a1031000b586003e241e5520000d2000480031401c1e5042d20380c0102c0d00c00784a20005440d10242004448107154541c2d10200000c14a0040c0101c4510802c60f601429034185007c0080d4000c1c00840365400540c0a400700c0f191040500388a4084805440d032035494146080010742c00d0011401c0e403504521940c6e4105100150f52100210307201150b041ca0041031600e40100100da55041540c403000146001150040181046801c150f108044c102205035960340d40000304a424941641c02400d16026a064610101d1003000104412401590090314190340c40004c81d9540d4401d08603070003d80e030a084041d55012211102d07a4585034854000d0071404010b480d400040d41201110f10200c81000a94504540703401caa203494040ea021160100ea42c2d407420041c0d2910300d0f422040c1002d1054100284038500031500313541000306c81c0d10480e410303d40704905101c002c1001c40308070340d51104000000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 993359073 1250 993357823 993357839
    0x10b0315060114070b04060b040504030203120c090a180c050702010c120207030c15030f06080c0103150308031008010e150105130f0c0e010e04060e1f05040f140f0603071a04 76
    0xc02040c1d100d400c4c45c3d0654135050802c01c0480e100b40120314401c80c140800e002c04640c0c000142c03098400c000980300c02580354500040114401e4070000c1d90082c4282c2c400140100d00c3c01166903041950354424056145103a004a03103510444100a02003aa0803000390b012136665000c981c0e00b0107590040b544400e840c6d845507c000b01d0715030710452503440e0748140100801d505005400d040d944030f0409101c0b11741045c21403071b1580744a10120f030400d903441c1c020f051000f0051450750300450700019029a60b007001903140785e039100e041c013400c501c0e036003004e8080e000e4500c0054208808035485402d00340c5a403e080800180c0c0c900c1c0d116440b8100d840c1c42544510004074440d2a0044400d51200c0c003a1440400025000310300354044980701e1803900004002510a804070f00c2d50020b90100c00301c1e00341014400b0f4400d80c601036004680c00602e08905c1d04200a904c0d8480c3c0c60701c01c92500d15940550b01c1000c64030b03042d00103c17810358040c2c010720820041c2c0d00d4400c8190040402d02541c09041c00e80b60211 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 993360323 1250 993359073 993359077
    0x17040f0b040b06030f0d0801060e040b041838061801080106080c120705120a0b04080301050a0e07090b0307030603140c2404030f060e2b02010b0315060114 68
    0x4203a810030921010f21006140402c180860500340c98040c0c500194200b030003805255051041d0010310002c281c460200e03a40d503a10040c0402c2c4c0c0140108508140c0305540704a0011840c0c045078005148c482d92084180403c0c0002106801300510306156031041d019022060f1019019a410030035140e003408054551701000d43c064010100009105803510200340c1c5880803d0280900541c1100f0f07107511000c80108080081d500c099030072504c007100300142076280c1050380c00040d200588040601040010300001141203030001c9800300f02c141e80310003145004240c1542e0480124140d12820804400c080020b9a440101c1307042c006911566600ca1103101c0c41440420405a00200c0035000300f407401031140820210103a040c055a200f98440089a0784240d010140000c54101150801c0113819000103221519a074192094050769490401104180e41c2e0b004180c40020300385d00e140544144134141182e10010010185980320345e207240c3c0d0f0f0301005032143d4104081c1e0188038001d002c0381d01c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 993361573 1250 993360323 993360331
    0x40f080f0d0e0c010305010603020c06042a060f021b0603040f0206040803040b1c050403091806091d010e06070e0d14070b030901060909030e301b0a030317040f0b 71
    0xa082c50310083c90004086a0f4140c005406040c8140b260b081c0d100d2000030950790081d80143c50364600164150545506001c00a1020f50849180c50108203a0b50040303042034600300d00e03000c1726100c0141c0c101e05800c035030107101d03d15002202032001038003041040384d01d002e0050010f011580341a807039910403400c0d03034015041a00707210000110b0b01c0b107c0700444004000c181060404211a040c16038005010180c0c42c41510201c01100501d0302007518503a0062008104d41070040140940021404038482684016403600e03504c0c01c0480a4400c02c0442c1061250380141d6030106d031881660100a01c03416581c005032a02001e2040c000c03040e050030003500e0701504800d1031080d12840c00c00307811401d680c450b0700142c0f00d4505115004c0f0020b6000b503600c800207401291510842d041602c280d10403d00c4510960040401d1003c100e41061400301e10540000720320f03001038691001020900c004018188001000142000e6100101d0451401c00c1c541041c03143c2d4810081006070345955142090607a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 993362823 1250 993361573 993361601
    0x270406140310020424050903070609031202010e0718020903011424030d050c0a1b1503020301080706050a022e06090513064101050108040f080f0d 64
    0x1010004107440c00704410101c8010750842545002e0500d001410200b1015035041c0f0a04480a502121540604103031202c1800107021202803550314040100710011a04c410360300307000b0064119401d54818081c0300e407118400c0c001040d0641c909a601c0e10001030f08c4903042402582408050b10035502802060003050350b0380c3c0c00c1440e42c2000c0b050382c901189860042c41e180c01440407003010b00e40700419035081503480e50415540355100c043c0e116061000c0484010225100c103080d505075034540e03091110a403580800454422202a5425401c901c828000d5108540c4003440403c0703801c1c0b244008041d20701e91413040d14205c03519401c2c1136030040140743c01c84108141603544491501074034460300b0011701d1820401e00c0981460201c000c00c4101007034000c0d04081c0c079090743c12010302c0b106000014004511140c0030712000200b16040c1c02d048181080110a001400001803030f40c0304100080c0500d82201c01d04001300d10a0344c405446070700408012103100e03014006107640761424898087c0991500d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 993364073 1250 993362823 993362849
    0x6030a0804030b15010c15181b030303050a020703081305010207080c0307110a150305270c030d02010b060a081504050703020702180c121b0f0a1112270406 68
    0x1354542c812125211a05040044202c40507001c182c0d1083c0c20514810350b45800107103400c02002c00b884035540031402402c29040048a0f102090400b610340c41124040c3da4108400d032909500c800c1030744030740741000e00002c404c400824507201219480500301807058000500c2c1ca074680e07540480c10381282c610315105802c0032030b50f40c040c00464a0844d8081100301c2c1c0200c0b4090410460080204600701d51400705542d402c0082c8102c045400c1c1004030152005006000141481e44186e980075860b82803070107805440c21081c2080e005001d01003c1020040032281090503103241181c00000082140100940c1400b001042d03884610070a401041e09a41c0583d50310482d0050207092041030000c201c000b050700c0c04004c10220802d040c1c40d24078880c450940700c90b8555951104000b84e03025010010340310b0010301d03814040200c0c002002c541d039a039101d09032201d0b181b4200a0722040b006460400040040140c0a4060342c054100141c151440c1013810752900c0c008040340c01c603049a001b4400010708 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 993365323 1250 993364073 993364081
    0x6050915040b0108070504060e070804050a05060c04060915080711070509100e07112a09070503011e0308090103091b080709060f050f010e1309050604150b1806030a0804030b 76
    0xb40f00a4014000030f840502035127140811310446600b005200d1410800d0840c00b15080160a200d40e0711820f0b00304d000c4580c04c0c00c000490f040d00f58000d21031200807641212000924001010303942145540f1610342d002d04e941c41c1d0a050751200200d580c80000ba010f42c0d071010035291350344c00da114040c9a01c0b00d003031800181132004a2001c4500500b43c1004d20410036440103514100103481d61140b04051710b100d00903444e4808860040f020020304590208850041110325940200554102d8000c403019501b500141421500202e03d00d0201401c04041001000429400f0350804511a40308080180b41000905800d074a540307800c0c0c200b080c0340d07040f41c0010405803900c0d001300005402d60704d00b000b2081d45440000740403254400e0700175041c002444d01c4d821070755803184072035852180540c0044c84109894605030b43c81e1070080701e081341e9100301031814011a0085107d43e4881c00c001800340e02030700261048640310054001c040c0307589481814110000611440040d1005500c0755020f56400d0070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 993366573 1250 993365323 993365339
    0x1a1305060d05010c23070c03140f010e01050406110403030c060203060a0b1812070501050d0531020103060e04030e0f210705040b0108040302070b0f0f270f0a0306050915040b01 77
    0x814405c85002001c8284503420208220035460011241d00050680001407a0400241440e030b9261031410654030b0320b0402000f0000641009204a2003660100300044112282c1e0394980074a000c0500040d40c4644004000780042d4021078001c0b80c010301c15602c5a80da00c010000360f83c820b500c08070010445105c00c0c0c0080c14440d910001403071010f00982211818040002d003240a151309030540540c41c1c8010a07513a01440700c5900080e407040f0100050410310200c11040d520340c12000300c1c0020b1618400240031007540030020302607079041c3e03030781079440c00a5410000c40b201501c81040d80219203180e0111907405801c601c803400c0301e840b0003400425140204100440d401951880d040c0511302082000080d8081100400d580482d0811a207500c00304071008124000d17a06044000030000401c40c100c111141440070890100c0546000e0141c0c5003014000041c110f0900e10f80c0080080c0301c14030018040307420081c0e004001200f240c3c840b40d10040d85208000090701d0507101c5407400c80052040da8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 993367823 1250 993366573 993366617
    0x180605010506090f010c020f03070f030c0f0e131a10030512070b13050127050f070503120d020d060b03010312020a0c032003010e0309041a1305060d05010c 68
    0x4001114850f091010402c04112200112011321741084804c07071511085607180441c0003030050028040700c3d81151214800440038645020945202c070021070005407000c0b883c1a10030035a002c2404128098075150b0400900c405950750403201100c0f04810502620510a03d482c42442e4952070280703001d02e142422824400c164074815010300c020004800031405042103542c000400c074040b200803148500b4424010b00b00050381035117030501030011680c0900e040c20600700490107403003030b5038256504c0796507240e40c1c40c0c035031103000c3d010740183e501d401910103403501810408540900161810700d8500200045401c15080000c00120110040c0240100b103004440300c82d5250000300021001d075101d47c2d800d07460798031005100362040150092001001d2098030303a000d1020700244202411904d01c80d4680c2c02649895001d20300d402049442c0424038600d4a26200000c0c2201d6925616a01200040c14001f015207801c540d43c0400d13030000620074458608280754581c2c0f001c281006604c0c00170049 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 993369073 1250 993367823 993367829
    0xf01020319140138030406060e19050705090604030f031e08010308070201090308070f0b07170a1a0312070512090f240408010e070803030103200301090618060501 71
    0x40c6842d000ca00d411120400d82c6041d1007000f4251101c0300042c0751300d10301c1280840c03640c0280b140041c80410107110750102070b50041348180800d0102540390b1006103040c400841e034800058028051151103c0d401ba42302a4000281303150a514003405400481c9070340d0711a43c0304a40e6258422402414160710034106a0075540810070003c005010000003801d40a040c040581890400101001103a0103501c07910000c40c0e20a100c542c4582d0300e810046001d40032220f040e50203904140006142d184184140c1c0340d00c50401d00300360350355103d00410702c00400041380660031640100c5c1a031070180d50200700c101c41c0c44500801140e500c00c0903240040c18a0b041843d860451031040c04401902d6582a001d01464603040d500851209010001c3c015031a1600039211101500054045803200c1c040d00405e421880201c211211595100095a079900c424070028010703194140f194294400b0096408045000080003c81c0708005a210082103440d000f010711800316000003c02c041041c1ea016a07401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 993370323 1250 993369073 993369121
    0x916061e0e030715030603061d070e240f03300304020a0b090d0b0c0406090e070818160608010501020f0c0f01030b040e150117010c1b050a050f010203 66
    0x34403031840c0800d555440358000c00d0141c40c4c60001c1e60090781d100e5407084005540082c402d20115503402d0074a40c08070100c0001c0310441c020b5450129070042140078180c0a42003602040760507800b2011100d01d41c41d100c0c805a40c3c841d07810b2064501c10f607010040311840b24000c05c1c45c4511440804011a800d42103d0b1307810108140520802016075607540050044406d0444d5003565807a4030000602134018607040146a800b2000c10310030300240d8400584140c91290b12040c0030319850b12004140540201c4a0b01c00241500f0300082041d82e1250140545c04141421190f584510200c0100f484040c0d80000002902c0300380100120340c1e0404c02d00509902520141451101c0500842e25030035246010324185516030701114202c0d140e80d40181d40301110724040e19a0546004505030f8419004e00c503100000340c00c403d00c41083e40041c070440c806103180c2d444468044401840f0b01081c0740c17240e00c043c0d030301c1c0c0170b80203080020800c20701a41610301108000160340340341030078001248038510468002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 993371573 1250 993370323 993370337
    0xc1704030801060c050c0a0602011d01060e0406020c030d020c01050403091502150606090a240503010b250f0302060f0108010207080d050a0216030309021c11090916061e 74
    0x300360409003042c1522100d24181d480a005424982c2c540f00d00c14007901e0b0000d10b501000a030342d50b4190b002c04149045940218103050074261305900342c0781c050142c0f06080748441c022600044c041c0c4d0042c0f0130100424280c90603c0510b4808030300300d0308006807800d580e0351103074100810075600001c0340c405803128a9201400100e40300000303660700e0003405100e000740344a00100310300e5501d500070707038060003001843c1c0742190b42c80d00020301d4488103010022041300301c01030300c400c0058003031001c0d41e040c1c1d2141001c02c1e0415900003004980101e80070501755141c41c85018600104030311001d02103495009400400302c0741480510302209410507030140c0410f900c14000400010360803822241960380d0300b100442e00341c6421210000a1003071302c00c44000020700030019002c154040d00806080b40c0210b03090303030700580b1b442a003076641c13810b080c0700400303d0200701d410252030311308105950b4110030020116003818000804909c1c41072510f402c00c0c1d004c6820300e2401078480c00407a68407001c030869441e1042e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 993372823 1250 993371573 993371581
    0x3c0b06030403050a0e1513090e030313060f0908220b0f040e040218071e030b06040902160507090605120a020d08030a0f05250201090507060c080c030c010c17 69
    0x1e02c6401454610f00030043d000905c83e0595441d10225410080c49604140d0348500814041320794036854421900210305180030b41480480100980f44101c00705240b994050003190340b040003d00443c034480740c4039603980e070b09540444c1c0a01c01610090304202007000c00754030041d1003251018980d5000c417241440800040c5c201c01d07855400d0b60221840700d00034107600c0c0c40714030004403580040a800e084408400307040216040e40560b49034800301b6800601d11058500c00412400d031041d094a550b00400100010801041c03268001c0c0462005030310003043c0340e072140d5a4a820669164010145d181c2c60700001d00c160b15003502d90704825481d0a00801050020b540450005800424044e100c034102000184c8615516048800c02d101c00d600208043d241020781c4007012001d503a09800c0384d401d0344017102181c03401442002c0d034144e007200040c01c0a0749090000c4a0040a405040761240303410700ca81040c45104001404000301e50341c0000c9640c1c1d402c0c2074000c0020350000190542e59030020180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 993374073 1250 993372823 993372827
    0x10b0406121e0c0201060905070309020a060f020303310305030109150305060105101806232701110111040302011404180903050919050a0807183c0b06030403 69
    0x81d00000b104400c0c04140030709040c80980c0180000d5200075111070924040285065043c2c2c8180ba04520031568508a1500c9003000c50703174100101c1c140b50241e4410004030b1080c602c00981d0055143e20108100c2c440103c20b08038240c03184813204100c0100b0b00100061105150500400842c01c0b116506240c1c1c040c41c548a40b542c40006100d86402010407200ca02042413280c007007000c0c0c03100e01d03210240c030540c0d4582c40104502204107030300c4013184580c240705408000c3c1d00c04981e200c0c1984880620801c02202d8460202e4140450f041d040c001c42c1d590403520248280140340d17018802031500c90304c451540c000540901c130079000c1404070b580c00300010b0204414240b0b0304207032408100700010703400c2981c0ca0309540b82c0c4204680640e100942d0941000004540107449058072808c0da078080c0115030b12403049a984500303000b07100d1040985070102003c100254441d850000e400108543d89400c8107000c0b40c004808003900400d01c101c2c04250103c410f01502400241050a45050340b5510b056140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 993375323 1250 993374073 993374111
    0x6061d06040302040b030102130e061e010c02010806131d06010b12010b0702010306181b05030907050f181003030f23070c030b01061215031205030901060905010b040612 74
    0x84c4110355803c110301e81038409505a44d0003165458052041d9074032080351030000301c01140c015206d95200f500d4844007105c1d114521030840410303180c503801c03059541e005458600c001017816420580007080703000801c50700d000701e0389040c05145a48040d8504104580c2c2060300503000301145081c20000c2e808102000d0359041d0460781d03072581181d11200948012006440c07580d2006014200101015101740b40a910000c100e0079100800d02c02940404820f46160104580b144540d8100d001c00f046207041120a1503500c0d040201001002c0a956100a18040c0103580364004541c0c918418420150007000040c0000e440b070601041d00b0080ac4140214400c84d00d2540c00c5c0c140300032401c3c07020895000b6000e006582e218805030050b40c2c617190000d040003850780c01d000307441b42403072007007401c4003a4070074208242c17034001501070990310306080c0c203451030391006d04101c12035903032403c00084010540c803a190180081000255403240303480802040000d0100e03481540b41c0c9004030180c103881c480b4070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 993376573 1250 993375323 993375329
    0x3191d09160306051509010e04060b04091d0f06161e03110d0f0203060a1208040506030c04030c0303050901030f02191d03070306050a052a1b0a030306061d0604 70
    0x7034485444118007a088026060940c407030350300000c103403111420a807481c40c0500072058083c1e03118018114901c4c1084241c96a45c4503010055404001c00d00001009420040003094100503070300129565081c80d91074000c03844415072468002c071060140c42005030703c25094900d0f030741c5005500c00c40080c0e5940100d00b00c5040c0f0009040c3d5440301c41802003100d1055914149a1a0007003140c3c514042c00e02001e540101c60f1076106d07050f89000818203c0701d0340c10349507500303401414a501b01810a81404251f500280140e49000c1d0107010020000c2d0090b054600610b100b0750383c44d82c803036050b0030014041c0c807000d0322454401801840030b00d460620414074103075200040d25010310600c1c0d5980f074000c400c42c824410303103826006030304000c003d103c11a003101e4082e00c55010b04200a55895070562680b481440014817007040384406016101d8201002d0201c0180c403860742c0d285201c0328581d2a1a00c03402050071400300751505000c21450b85c00400301c2400c030003414500301c910320141e400181144540c2c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 993377823 1250 993376573 993376591
    0xd0507092d270507050a0f0b0301031704031410050a060311011223100614070b04020310020d0b0102010516273317190b0303191d09 58
    0x10410b01c861a85801d91032114252072000c1c0d85507070341410255100c0388140221805903800000014818001c002200112070302103403c1c0d42141d0845c1e03030301c00c2c04054007000c1140040007400301001003060681c1c609256081d08000f010321900890b115403da60008244004003860003104001240d160302c02110801c0091030070501ca48600f8810070010592000c400c68203200f000c4404800da102e18014502031030068080804880d540ca00880b8024002401145001d81c240003900000d0400804190007c0c8000c0c01d031507000c03283d004644200c0c1c1001c205017003000d48651114007556028440c1e01e4000d1b400e50000319082c0400a4003038030400c3c41d12000000c8201442c0c022001140c170266003006400d140e451a1200e51400408400081c191002c900d600f10959114501c1c3ca4010031382d1840b030303101da80c2c410151913841c0d00403100641800405904a00d499010305400d555050004041d0303803c0b040b1300d07004540d440c42d0005140c1c2410100070a4040b000e05107150392560b4017283c00703034405070740 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 993379073 1250 993377823 993377831
    0xa0c05010f231306150315050c04180e19020f1906051b0d08010e0a060608130204020d141506030408031617010801021c020310061206050d0507092d 65
    0x280500810001000c0d18107850040302c00c080c2107078010010112402000c1c0301c074682016047d03410444000f5140d200032084100420007440c0d85803010f0415100080300c2c0040c903000b520300c0c0c007400d15548560030403011448014060071480c1180070142e09107000d50f00a80700303403402c0c0d205050207003090061200740b01010598240910340c946110058404000a07a8812200c0c500c1c05086202e0a016074150517541c640050407400c00b40c03080354100e541c160740d00d10782c42d1213001c003d190b50b01e10b84205907002502007160440080b02402108400348c40913199101ca0710b4a00c0641860f9040d00007203600c115002c0060101140d003150650f500030f48000400c5c0c00d02401454150381200400c50758003122004500009407004c01907000e05a2000d007140720060481145000c80d00301d20003103d00034400300d0041400e02c4030300d11466040d00c02c03050560001860b03c3c1c03518001808420156022a82e96000e95414031030b400c29030181e40c110300041004003201041c2e0004044413000000720369890b107903807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 993380323 1250 993379073 993379081
    0x2090703021b0a050607030506060a0c11010c05030c0c150a120b0d0210020d08010f060206070f03021b0a170304080712030b1e010207081906200a0c05010f23 69
    0x4102680080310003501c00c4070405003c81c900191100000c403402c1001c07d14060000742c041c1001c00032121074034150303943c007080d5060300d03500c01e01c4400f044003455040040e101002c4001800403c02884030003069001411140d04c10000c02201c002e4081140140750300a11044580fa5009400ca2007400c1070902d021800d000b0310340101d00e0380c50000720003951081c0da4410394005203401140b0840c004070b40e0b84c0c0b1541c1c0e6030380b01c24426403802d08600c15200141d001c0800102540c4c41000210460760b4186400340c034010000300030401c0c0010b1080184030507001114600100100084400080c04504594a0440c60542c880504902a42a018000c400d04110503450755200b0b5102c0040c0410092424102c4455655620201e001503641c05000d0b00c5010070101300b540000501c0300210040c003a0304410700b00140c1d60100a42075500c40210100c0c8540718054056000b407010705200800d503a00d0042c0206541442c500b91400390154410b80341c903250a03d107451203091500c828200b800940080c150311 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 993381573 1250 993380323 993380347
    0xb0f03070224040b06041e18061410090c2109050d171f0308130e0103080c100527070b030406050708070513060f0c2a08190f1403031f060c0209070302 66
    0x1011400052216142101400381524050ac085004012840e0101e05e10303034441350b13041d0448880318009008214440c05030043c101c80310340030400240008501040c2d04200c1e03511309141004002c0c030301021904510040344103040c60112694842722551488110000f50541e500165a00c1e01002d40031080021f81c2107903c102d0943c2c030f00010a003801c6038031525070752418249560b40040f40100e816020b06081d4140c01400341c010540180d0749082040f2041e4104552084040d160300110f000c980034400d80001c0c0b01d003450f0081c511450103a000032903286440000180309800050408091103030074408203441744c000500640564074030341004480d90130444c50a91307164584007001806c01d886070000c448c10585029040341c0d04010252200360036915140011344410014001d50412a00720840101040d003912013215003030f00495480d0030455000d000c06055600486004550185903c018261a102401c10400401441c40e04a21901c400d40c000707210000c000d0104020140c021440005076a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 993382823 1250 993381573 993381611
    0x11808130803130906050409200a050402030f0a0b0d080a050304060608060405010f0b01090515071a04062a0c12020f0109050c0301060b040b0f03070224040b06041e 72
    0x11554200b1a61100020180d15110040034000d684000741040030008150800d4090200c8296100c50064004414402c0a5003554080300d07011768000e82c5254009480e4440e88015805029000e0290f0f259280100300c580c02e94034200e03006405280c3e800c035081c000c079440d0410b4502d240701d40d1604a43d80e4445003001e001500c41c81c2c02040c00c90007180203000070410705506c084601c08405c034060003100252401981c07e0805032040540100c02c000300100c82c04617000007080b0303031807007120000c0755049003220382980000c045404550340c07682e921400d607a00703c0541910011070100c40184000081444000b840d0862004008100745500045c10b024140240030094910702444006c00c0300d501b00d400c11507603603040008030600030751070002c000ca0400225411a010b407001a0002c82c54204212000b00a80d031000b84450218003490009020911456298965281010494292504003818041600c40014080ca403103185021940d0780130445109407248896141c80001600404658482d4220 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 993384073 1250 993382823 993382829
    0x90b0a030219081e060312250f05010e0c180615130f15020307080a051c0504031704020a051005040b0a171b0915090901090605030f01180813 62
    0x4981c0c0d6080120141d501601440c440d508100202102c2d44d244010310b00d44500641c1d05c2a01500f0003100421a60030400041c440e2460203901e010070003000300e400540503c1d83e07000c11600920501018400d221003401200701c40410b18001d880c00d100031000043c0a00e80d2046403003003a10b090400103000342d803030b100c02c00030350300c034035091300c0d0303030b0383c20116003242000c105000300c444104807000c4c00716002c14040b040b00b1030410345c3c0e00114a4031703610343c50b400b010350040d100c1d543c10042e007080182c10945448241a036400000880460982807a20340a8020140d5110901c060201c540c200009130b91400d07819011a042924a6001c03010f00c07500c100c030288119000307400d5030400041c0d0154003070b50045140580400d803010704c00c0140c07250900410484807640807400c2c0f4200a106010352807030110b000092040b502950289050384030740200d9080700090380034a0031503540d00740411103810117000d0901d007243c3d03040003003000d03940c6121584d013070b41d0912070064074030f00001c0740011510f20f0024506001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 993385323 1250 993384073 993384097
    0x3061e05010e0703180c09020c16081b0f280e0f16020613060510050414061003061805040515151c030e011d0409111c03090b0a0302 58
    0x840d07840e40d1180882d801d059a450780041d20b0407a040344071070340e60308a100865901c03150361008586801c40d43c10181d0040407902816001b82c20b007003030b22040d0542064004002d820064039a102a0030920050406040e125a00810060036a0342d001d44c1ca0b062004900d22800444040768030700300001c201440d070389400c900c810502a009111101c2ca241038024410342c2e0544056401828200301241c0b1013006460340810544114154400075005800c030316032001440081c444035a81d502c0c009010343d900481100f4041c20030005122043c1071840403129090f4140c28188610351904400c0301000e0601c8151104070b46d40c40c40403404002c41400103c4c0100045104880c01d0309200d0351801c0810a001c880c0303441264001d8240c02417490341b00c0103546040d010380394803002e1243c0c580107440e00c00310755498165031086d0441c9040c1030340e2603100f80c0c0322603401088000c1007110300c0d80501c9616600d90780d20341800003580d402500000c5e0302229410545a05c2014140c454080b210242c01a00030106607600c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 993386573 1250 993385323 993385331
    0x3023d020f01090c05030c060a050a08060d02090708070e011b0209060402040302090c0309010c1d12100e010c020111040f060f0302072108130c1509030606090507090902120103061e 79
    0x61000c18820072040c5c0c2e100310140c500315094842008403278410044c405d004100240b04910040f4020400e203a440341c4081e290417505561540014a42202240c10704040b40c40582030000d11540400f10a100740303000e003840c80c1d54076441e001505a402c59040700a1044030040e00203070703ca40315a010781d001158098111121424650040800b64108560b0305480e9880d00001000d02c500c81c1c0481c0240d40700c1e03008107150001480d401d000d2000890900d2a0491250008105410b84584119528041d840000080d0b10400410007400d44078040d104d03011108007030001f0700081d10041c000d542110110309003c0800c40c01034a007540640604900078092118614040035000d04240e0f14251824075950303401140e0384d508680351101100d03614080e001040310b59042c06a1940a14412104e070010704040c0b418942e250380f124165401d90f00b0240c1060740714414403031540e400400b0340000d0020180c09608141002104c6640c6180c1440060801034a07404c00200f19011403105000b51042c021080c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 993387823 1250 993386573 993386591
    0x327030d0c0215010b0403020405041a070201020406090503160e090a14070303200c0108150a09060608090601080309060a0918140603010e0a1101021c0903023d020f01 73
    0x2800820005031648058016030403031043d0b8081000c0381c9070607a40340c44c5440b420141103809000003413100400843d86401c00c40725007965035140c2c0412601c0389100da4005a0707240c3c10040014001d55490380903130300a601c429880d840d04405ca00054007a141001e450350410350702e00c04140d1901c00c0849000d804542c055094803200d20303010a0f00c0050380c0c02030725110340f00c4820360100315031417140d4000c000b44c5401c5525150b0b03041d846020183e4020301c0c000c40501c6680b5480d0b000840719150781d40600840e44c0c1d0b580701000369135000b805d1164003200c00c4020b0007241d85000701440d141d2090110084c0b1602001481c0c0c0d241c1e50042051078003401082c01017014420b100d920010080500d00b100c6089100000005131091030140102160744d500100600504034517955455007090040706042d040d8080c4100306020704160b0040050301008555030003100ca4a140144040302c41181c2e2201c600340814610624008644481c0c80610140c0301207a5070400202c0070208d051903c4503218034050b5003007405030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 993389073 1250 993387823 993387847
    0x2030705060d0f14041e051609020306120303060102030d091e0605071409030a0b060a0e0c03010e06030114060f0d0c2c28150b0c1c05032703 62
    0x10000f40303800030041642d0f400d480c001110000c07030f00100f24180c4411701503100e10001c0749004400c1e1098040f120ba40300c00d1a08066111802c0d00300042e41c41d40801080081d2800c0e02c1300110000e080342c041d602c0d40c00c102c00000e480340704e0180c1c459038050300d8080020030403600071621244d42504102c1491012840d207007400c041c1000399148000a060000d81c00c01e502d160b5001c88900e283d0080c0180038110065070741d8120000300808095006c55480000229606180600b51040c54085000c42d81ea604140c20111a45e1014015a00036071400d86840c24540704400030781e4101404903000711491a14200242079010600ca0080c9400c202c09000a032940d81d0f58507003001c4031410b070300c0c0710303002001001100f5035180100c500c09070522004030a040c1740c10b03c2c058003280c240c1c1c00d81c0c0c02050724540d2180102444035564014540f04000044c0d8a180305003c1c0070305440340c0e100c9581688407918041d00100540005410460554003808001c103900802640d0b184030b10304408203684e1900104902c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 993390323 1250 993389073 993389081
    0x50c120f04050a0203010231080706030b010e030d0509031e030f0304140a0302061005180c0a020a08031e0a0905100e010b1504050a0b0c121b03070f0203010b040c051602030705060d 79
    0x250080710701e841e072823115807824002d4000144c640c61001850b002d407500900710007406040485a041c0141040405080d072010712080aa41e5183c1d106c069840382c04c0070030316242c0a08203040d200d21395421148101c8512010048807900359980700415102e44660408080d4454110702c03034216842864140350070160041800307841600000e40420981c0d0340c0d40d003482020102c101e280388031014070b1000174516210800141c1501c040b1b501c100d60401d00203550b40b188e150300548910710041c058809040356403516004090b4003810a1406101da0090341d5681665511000440c503109510703a1003420320903400b54000e5041003002456080c919450f814142e1581c0c4c054000d441c0036840c901e4000c500b8042480807185206040f00c006c0c86008000b2460031010340003855000541114034885134020b010400107844094050381d80c20b00000094410507086981441b18240220300b00107000724801d4125003a111031900403141022103083e1840002d040c06c01039040345500801c04603210740c03c1481a40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 993391573 1250 993390323 993390367
    0x5010e1c1113090309052103071505061503061e0310020705010e211e03010e09280b090c04022101060c08040611120a0c0303050c120f04050a02030102 66
    0xd10004282d454081d044180d07038030401c014011039800c50b020080350410800b900490300d00030144614002c0b0741c0150504503800420241c961040300009410784202c180704094010404546404142a000b11428114040204020302c101c40c49100758035101e0981e2050b5a503413000070305440007883c100d41c0d0309000350030581c1e0682d4150301c0d0201994414400003494811800d0000f0007034000041d00c580003200d40d000c8600020715040143d106000200080040c50281c00040401181482c100c0841460f10f003841444101d4011a8090b500c0c00030715140c1e0304120250031440c0918681e0703801c5110740c40c01d28420781254120f40b00055184a8605060b01c0b00400e040030038840e082c80e6038910301258041041007015008030000c2000f0401075001700c0140f41c9140310b0f081034900d104081c03070b52400250050070407500400c009030001c9040550500c900c5070701c062400c00c4103040410120315141410001403c000007401000081003e0100030070059a10581c0100255170ba084132550b08d0760340d481c80308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 993392823 1250 993391573 993391579
    0x103270c0b160f080c01092409080412030c0c0b0a08100501091710110306010207090626030c06040813050906010206190b0d2a060905010e1c11 63
    0x401051203400c0c40222403007940d0586034a102c280c00c03a02c800040f1010420100c450400401c0036001c41e5600380108890f8600a0020004c0c0c2000c10101035a56100304880301c0707a031454034050500140e002d03070030b45064613602c140780040c17030b03000b0324094450717605180c4003400b01c0d45003510000b6410f005000600c44031441d640c5042041c1c8803010b254000312918026540440c41c058800c0c40050020b8541d030284001000445071220070801810007100ca4480d58018100030001c00c002c195601009120020105658104281450203201d40e003104002001a0903400b03451100c00c0c0384a1007081910300405040d070949644d0f00301450222800d6124004a01281c5005c5100044d94034050030554400c3c2d8041e009800d80d5900c5d00100440749100301a0584840d5403101808140d0301c51134030841070300e4421810451140010011b0000169518040150601a035402401050b074005841c41c00c4440070f090080e0104003080000d903520010a90030300040c5810290310b801d004001c0d207030505e00030003a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 993394073 1250 993392823 993392843
    0x3408031801050a0f0c0204060b0705060610090807050d02010203040b03011e09050106050717042d080616140f0703210606090b0c1c0815030610090b010327 68
    0xd4801501c01d030268000c61800320b200c0c0c07444a01054000c1489850310b43c40180300180098a850700442190004541941c595116800300029800d0110040350708520074140340084615141c1c4039683d03145603001e1140218420242d420440e4000c0007503501802204031000d4807580c441450300f81c914115620b1003001590410000b5004c813141c820f142c1030312125920203141428544692041200d5504d0003254018100000940e81d8021300c001102040c0351480e400034110860050080c002c0c0b070382c02034003a0b500004288079246002d032140070306d40202818180a80b0380d040d820004d10380101c4003180482c00303001501c0020190f0045548000007005183c04100d01040e44039901110400c2c041c51001c56250101030204861071700181500c2c0200d04100c4410380309080186071b10103031054200021450b44001c1c4081d01e60401805040140150300401003458402d0613104440c0c0c040c0b01e01040503690b50010314080e48250400105020542084486070790101180224042c001c001501c4440c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 993395323 1250 993394073 993394117
    0x180203030a1d0411030f060f150a031505060304031215030305090438190618060e15030a0b0a03050607030e010b0f1909090c06030c02030c340803 64
    0x3902c100e031900c004c1000d4190656507500e07030800d00c02901420565204000944d15806650782403882c901c2201140d01d40c230385500d40c1503c0038003941c1c0608019880c41070f8114007800181c40c0c02003035036400b07038151400c5610b0b03211014802c001031800101048000006140202c24035411900800c1c040302c05440c100b004040c900b10f10b84001400c0c4e60804a440304003400c10225002403000949944c200625a00c004030000c1443d90140109920a40c042030025200e00401803c111040c80200400d00303041081c0030081c00000c8005100000c010010304002c80801c0310032a065000300c0c1030000c0034080800300f031748905081da5071f82e02c11542c0707400090400b118149036980c18050000c1045000d082c0c0000301d1403050401c01a403c00440800c500001c9140004134508640580c0741614092104071004a040190040c2a0b03008421200700f55442080b145036002c10003d031000280041803502040302a1316200c2d8000d003003c1041d90500003808460208803110080002d042203c401424001c600725 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 993396573 1250 993395323 993395329
    0x5071e02060c31092d051008010c0206091603080d09030e1f02061612050405030d15080106080703080406110a060e0c18060a09180203030a1d 62
    0x4008440000140c00c40c201103000300c2000000340c5910308800c2c070700c90f42e07004800780d2154855808420074040020643d1040140395920f210300ca48051a00c03000029100d0346090552003100c1c2510f52010195444000030766120f10307000c12201030801c24000f8040035180e01360003991603000703031140040d9010b00c1c6030b88030000e150b92408104480d0703c06201403d2a00304400c1d80010096160b056043c00040c0c0303030198843d503459420b002c03281241ea1298406004c2160000c4c40c1c030700001c2100e00600c055250001c01c2a41042d03104068406203e004200341cad03124035040b815400ba0714000054103003070881d444c031101586103219063b85c0c1108000c0000c0c99aa00007980e45402d43d200280486a0400092001c1445100030b07040c55190f0b08101d6408a103e541d91808903803079000405802e40184000a000d45072030b030301444224040202c101494142403000806104443c858014110364401203c2c1820214880400f0844d400401b92038076403000707110290440d620030b0001ca04642d010307509102280307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 993397823 1250 993396573 993396617
    0x1527063201090527151003140c010e240f090411030610051e04030c032006040915030b0a0603021f0905010c030e03100204090605120a030e19090507 65
    0x206005941054a0070700d0074103a0300302c903030344c105030f13500900d0300300035090100c0304505004a0040444078a41c500e1400d200c0034210000c2030642003500005084202a0b92003080c03090b4480080300c06110400850400b1001d068050b550241507240100d900001c420900c4c020b41000d19099a0074003500808a4001c3d4040c48100c0c0d003581e00c000710450601401e44942302410002650102000340c0e402c2c03150301d1889030340040c1c0c021940c2c1c100c01007003401006105240800c148034540c040000b41141d003800915075000343d01841c050655190100c00380c856040c03800c0801160032800c4c01c0100c1c01c3c42e502000c0903105c1743c001680101d0000c0c424031740b054404107071014804540c0c0d40e250f0590b401c000c01110005001c03c01601008030314001c42a8665081c08600c2c5050005800141c0e1a850019600305892559110603c1800d410140300c40564020480100050f4149084035411000a0005004402c1902c00000892400c64081005100fa40c05140501040d03120685a00c01d0513145509030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 993399073 1250 993397823 993397831
    0x9090905120c031e0306100315050111010b060f1e04060903021c020301050708072006010b031003050a060905070b0f0d09030201020d0e060415270632010905 69
    0x5601c45000c0e09085000761014052100d011400e903442c0c0b03a05400c1a03140100c0c8903801401182c80007041c40001d1604c50380e030803406486414180521440c240490054443e41d100b1541886005119440469000c0d80f256034982001080c0c81e856003a540d003000455000380c014026010140f2082145035100c0d8820303142200e1056480c0c0d004c40d800d680c02c0c0001c01021512022804a0300c400075801030fa42030241d90f216841c2d039910f84e40d0030300d810f0400824200303040320034800701003050700b0502c1d00e4040480c0e9107040d200c81000c40b40d0f0744d48800c40a01c03e0464030b039001403e2401903101c420704100d26900000d004a010b4800c0303404803a10381c2c05942c010f2065881900046608002003003000100e5008018020301a00006040004800c503000c192000203003003002da9009442040b0422000e804003458040c030f001010800180803001c2d100000c5000c00341e500c0d90044483c484820450150000800c0c44c184801400700045040c441c0942e2010740c1403050808030b00700c80041158a01d61042d1485 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 993400323 1250 993399073 993399083
    0x907090b0f0706060906060314070e0d032607050705060a0203060d030305100b04080a02010908060f0105011b1a060906030c030309150708070807120c021e0105070b09010606090909 79
    0x81d0800110102205a00003001210031035102d100003c0c441100d03214900052950b91000f04102452503949072840304d009209e4010300c549900c0701003040e1076000700c0c008610751606018068040d101181c2d40c40c090001140b00d10800e000d400c0101035540b000c045c0407480c1c86007040780c02d2030322094140c0081c0c0c001110301c650000840104500400d11070b821454101c40541c40300820a51503c0301c0d104180e00c03540114025501902045045580c02480c0340010803400010301086d0900072580c981241c410312620b4100003040005c12586400759980b03241c0940c0c040c13004169004a201c09500c0b604040b100c8a21503594880010b04900700031880c3e00012400402441c030300819001048800303e081040c7c505911414000b24000504000050042c18010482203403210003900e407140c1d4011083e242c1c04100b020000040c80189c48101d130445000051005800c68078285500480300d134003800b400501400450b1082c4040781c1e03810761028050fa0700580d100d5034595101d4072440305883d910200240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 993401573 1250 993400323 993400327
    0xb30220809120a321b0915040e010b1305040b011715070305070905030609100507120e03030f0c0408030405010c1110110d030c0912031403010305240c0a0305060f030115050907090b 79
    0x400b9151841b150340d030011080b403821f0020030218007c54111042d0301d0b68101c4580d507901e81041d00d450154500200590140d905200074546543e42942005042c442e405103060010716100e18000188007406241a024102e1180303403801d0310000f005008143c902c0c60200e190107101103600e040114003a40314605e008001d00301004115840b80003030400600050800c0000c0c010707404210258000c440d0400c1c42100216201d082c4075402c19200d85d4060003464184008103c204183c1c10040244d40482c0c50901300310f40058803038105110f85081e5031084540c044180e510307030300e40150483c1c42121800c1502d422076404900200050342141c01054180011480f18001003001004091500f074009202e4a410a030782010a018071840e0340081e0011035245c0c0207103840414070081c00300440ca0400110f4402946802c1500d1400c80760312446aa010070951501c0010314152a540d10f108080da4001d0020442e095a00d401401c140849006031481009640042008141716120500540310000b0f2818 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 993402823 1250 993401573 993401623
    0x50a0c03060e060f04060b0c0f070509130308060103021c2a050409180b01080f1c0c08031005060a02010c030f150b30220809120a32 58
    0x440c0078110041c405038486e40300da41c00b0030040d6000c8050400070103500e0041512030001251141000d46541105000301403034010420381c41c01101c0f0301305074903402d400c0502150319a180120046d10850440c0c00312602f02c0ea11190429400c1d5010001010002d4001006081101c1c140800e4030500058840000c00c140f20510108a259001100d2a80b44094100d180c8010359180048281d099103d01415000f0140b848084041800440d0394260f0715020300040e032010510107803080982c80800740c20901e011002030a00f01d40c00c1c0d0000c0192000030400d5440d1010034100074040c1c4041d1040c840082d0408180860300c1d4481c0c084c00403604c1d4a0007000c418241400001d030f646030400894051007007509001d07052059800c564607511103080c540d1075005440c010200c01e0311608109040719411001380d0000f80811805802c0d2030041d10215040d100c0d06240d02c0415181689a00e0042d0603504040610101c040446260b40d071020780840480312020303c03480d030b140e844591100c41d6414460034010a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 993404073 1250 993402823 993402829
    0x6210303050a1505040e01060513020403120e131e090c06022b0c1b121103030a120218151218030901030c0c051504030206100b07021504050d06050a0c03060e06 70
    0x6c8417440c07a000c00025125500d0300040c6211707601445421005500080500c20b001c1000d52002101c1184e040c404621000f407000310340d8514040122145050b40c907610402c540045030341303074460300003402c0b001d121083e458145640340b11180e00c60140540f0424400055071a80802140c01d19a100c04503c01804440b11080d10a010894011640110800104001e050784a0350441c06003424070544d000702682c900d8007000300e50005110300e10070f41c010301001d0219548100b0385058007600b600e015880780441030101d170918426440f1075a118090000c82001821020090b00e03c01c031220740c1e01160341d1a0b0800040d84040c43c803c0044c441c0c0c0081020140c1940290030809200602d844c1c003840303050841d194039050400100364902c41015010501080c1907040100641000c02c12081c10a040e1408200c1212841072100c000c0c00340d50b011491a0b02c030703070b2007005407001444040c01041c12040c01d40f03495001800d080758a504217514003005011228420711646003901d850a80c0081e042c1c40340c030f0070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 993405323 1250 993404073 993404081
    0x60503010e1f0b0d0b010503060106110a060b2101021305040b0a06030b06040506041824050d0f0813030501111804020306031e160815130606210303050a150504 70
    0x1055a2551560031409603504d4004e000303411140901003948195040c81c2c02c1606047c41a80400d0400c21400c01010001801080108449a02807400a95250440301080b5036564034906410180c16111800e00220419001050108060b2003031101198469007000112400004101d411545ca0602400181e010750710015007084018080b6040641d1a0000b40e030030390194009079550010007002480e540303000e00860f48064038075250714031101e50000d4400c1019601e48109403003140720740740039024018101c447c04102900030204036580c4607800c2e2040c00180061100711215860310f40740c088000004001d8902d094201e4000a0310000d4440401019401c0030f000c00d980b50051884a050008828103028500010040540701201140d600101190180d50002c002c5030040c0314a8404020340301d004550002c0104c1c101000b509150400030002c160942000b50007501186440488c04210b14030620810320076507090010b03a44012884060f00e0300020b1000c1803c940ba2002c0c000d40c901900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 993406573 1250 993405323 993405373
    0x308041a0403080415030c2d030f050f091c050f0307030e010603150f05010b04030210110105091609150612113408161e050d03060503010e 61
    0x25a0074542c8030b8807201d000d540540c1c01550a40003504094942e03e03058002e00720b070811941090b030720603002010054200030840c41c1e101703e0759005d0406445854000d0b805401e14840107982000705281680c0b00e56040c040c255595039045c41845003032540c00306050b0311040b0560841e034840e81809440c4c00b800c4172580002c3c0000d03050540301d0021006140c03003445048011406581309425011054003408201c6810100e01e4a00904180041c8044000007003101d0480745e0540f2031013240d4440f08411100c40304100c402103840c0d400c1070284816102d00155880004541c52003001300b41e9600e08500084614510f80c141106020074030030042d940c0125421000b400a060010800381d4205207484420741c8030401548841d4070b1304030ad0440c410200f514840800e8440e88140c0f1001c4032030f40700c00301913001d40c0d02c21030588003d02201c801040040d03564828104010364150000400d24602207844204409600000900d8010001042d207014040c18955118410203058500c10b41c0c2c00b000c61158140c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 993407823 1250 993406573 993406619
    0xa060806251b14070f0816050d032c10050702100c061d06041208010503120708090411090f091308030406021608070506010501050406050909090a1b050f0901030804 72
    0x4100b4030b000c101c0f0440d50300488824003002c0d1a400742400708101240302950000d40103035201c02c040c40f407500094001101642c000b2200080c80301410716089440c1c0e4060641c6008890481c8440c01d003010758692000c41c0e45200b2504085030406444e0101c98034020520042d51104030b440d03202c2141d602400001182c0b81c00b421012942441100301c48000545141c1c050410350300c00000c00041c8282c0002c00a800b4007a890700e04007551400c1c00199454046480b840405400001c040c010060303076204484000d400075001384440403071707148003410079040010058024400107484141d5843d000e01c140303204481190400c034940086803a454840d81000f070040340e2281e400c101507008207458039180307100144140d2503103560303c0491921034200320069000318144001440203120090700001503414400e030a03a03910001d55581d4881e41e281c805507000103032881c4a09200107400c40c07101800e64003501e4041c0d415504a411403c28022072071001d200140c09000180300500c0030500007030020182d800c0c1c01e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 993409073 1250 993407823 993407867
    0x30c0b250218070c2f0405072106080607091404050601050a050a05070506040c06090e1b0c031201180b030c1e011707030c080a1b05030903040b030a06080625 69
    0x1a0707480c0e042e5200b51306150f072171945500c90496541c82c51510781005420042d24103005a00b80003c01401007003400d25413206004442c20700000310803055100300300500d140c0d42250309509015901a1070080207016581c07112a02d2090715080741003134001c1500420060350380c1440c20500f0714089585030400d9801c041003081c00c06c15000440c104025540c0168080c0c822120384034a8540041c1c40c14489500c00740f1200d442804001100028840211401d2801c9040c03940d200d00f003070301481c2540f1802e840044484a10000821030301c4460f8035a5080300d041a4080094280480426a99049014850380e00440e40015107480f101404404447c0b12810305103501c618811481c000945c1c9400c5803810006070b0744100182c1019481400700350040c0f14044100400100c80c0703c08041c10500c40f07102e105002e000408544070080c100104c8005068050a450304c034100303a850140078140500c13520042d8403880010802498440b18012420811020f08040c0029111713800c3e154128000d8910030310f410780e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 993410323 1250 993409073 993409097
    0xe0d0f0b1e0903030a0b0d0b19020f03070c050c0a0e010b09030f030309030c06010e0105030a0303050c160305070c0e060603180705040903080703060b31030c0b25021807 74
    0x800303201c0c034022041080515100d00c2c0c0b001450084074244000036105000c0500031802140180140a801c101401c00410141b0401d0324401c01030710854103d01c90503070300007042068103980003040128051241c8291000307124058108003c80505010301382080b20740c0c43c0104030758400d00c4010982120054141e840000131a0029401c6420440e900324072904001680710404109210300c078050000d10080c1801541010042661141c107680e00405065460000c0b50300d80013840c0640b081e160300350100d40c0401c4040d1070001d0440d003000f00c0440360080302d044040b421480c160049441b0b07110180c507560456440b80d01d00482c00c8803803035803101c15015903500415940c1ba03d008803809035000f519000020b04000400404942d100d920003030038a0014041c0c000e0b00200c56007400f50307400e070240c0343e1907a030740c2e404502840c10740c000d44c070040210b88003000018800d02240064941c081551f40021050784078104424a140c0ca0240000d502000304600410031942e201c2000780c000140e441c003240000c034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 993411573 1250 993410323 993410371
    0x4180f0e07080307140d09090c0314011202090114030a080d09051002042303100b01181707060c03020712030516050717011514030316030801060e0d0f0b 67
    0x102034201040d2a040004c8480c2406a5a0081c035000c0343d40c04020301507000c80090042c001c503814014082555202c0d014810810b2194202c003680c100800c2058040d1750395080c5442d41214455012405503401030000594150303494101880d12314040d000d8030485031540d0303600006a100340100494141d50b1b044441c0072034030400c00d0141c00c001c06580107079210f007000d1040f907542e050b00409425480d00b403c40011252004a01c0b10211f2030b41d6900480e81e11119001a500210311f03400012010700c60704400500c2c6092440244015003d400560b500c00f5280d01c000c5400f0512604050090703400000200451000020a040c06900a01c0c2640c24000c02c4000c0a00400d00711000f81d030154010041804010000005003210b40d038a58006c21284070003031048510240c80348070b020720130040701101950720386007403040381c242051128a9035089041c925000d07200060a0090b03100141c5020700d1740001d07080c404c0d4001481c42e00030650200c140070704e82c0c0b80701582d00000d10480d8101c001205c05d04000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 993412823 1250 993411573 993411583
    0x41b20060c1c0e061008010b03151902070b1f0303090e07030f090c030303111c050603010b030a060f0b09061e19080102030f0a06030b040b060616050c0a0b04180f0e 72
    0xc3c001c400350072142015a05841d40140780c1e000f001450345841032016466500040d21004c0c6c0d4a01c0a85180517034485811280c00d00003090216502c80c0000fa01070100f050403d8428410b59040e003100c1e210042036251400c400e52580402000305000040034081043c0d84c82c07030b00d0303032140d035a103808601d00200e80c01c0c6800351213a00c1c50488401717035417100600030950140510001d908900c0c0e00503083c0b54012600f14480c0e0003800c201c14240d0744d01c0000c1641600d0a400000d9400009000c840e41e0301e0192030910010105040580c180d80c0c5040440c2c980d03864901039981c0103400081c44284032003040c045144149415401303013944800b80c4804610000030505012004081400005072286402c0009518420740100b029a8245c42d004051001404d40b07030365560090b4110704c4070a61a612100410201c3c8100c3c0701c1a070520b590260208100140010440343e02d600c255885546541c3e140c09000c02030183c1c0c001c003600001d410480c810500c80310360100222a1035080003240000c1c9400d6028240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 993414073 1250 993412823 993412841
    0x70f061a13020a020a06020c07030f151119050c070f060c0312060b0418090c03081c090506060d03180b0c06011205060c070809041b20060c1c 62
    0x1218982102482450400c400c281040c1e0360390815807401260110007920303401d034010003c04040d40800c102c0303140e540402000014582c40100708621a11a08000c514200251016403e05040c003074075980300c03014041514a8100004082c12045014000a8955800c01c0420300ca551203210b000103409015030382e4400080215803104009503540f410024100511030408405050a016080091420040440c2c0442e060003c07400002c00400403800c018040350f40025040c0e0344610804828401c17150014690070000113880c003100d95070b100458003542d040c040041c1150700b003840061250308040280c0344a01384130340780c00810312078800111901500709810030351201801184000e05000108104d0f0701400016100803105411a81c459070749090007040d07070401e18004240241003088403003d440740208024010701c91008403040181c100070140d4003680c0081c55a1a0031108103004405010f01c003001500a0230459a490000c0f60041d40301400c100103c02981d480c0c90700a800354451201c0c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 993415323 1250 993414073 993414101
    0x90f0b0412020106061b0305030c0c07060210051e0a0f0b0603090106080705060705031e0d1d060c090f0907052203020918060a05060f040212011e1505070f06 69
    0xc20804488003d007142e40e15007200082c481d402c281134001d90354807002040c142e40d241ca031080d0340366108600d2480364003409004c25003510411a01194031900451a110003c40c0c0720410021a913548465041c1500c10724500c06035030b071045010a181c00890b4002c098965450300d070114008109002044496008882509080c4d648034030500100301c06202c0e0368010700e4211540ca052a002d519003c0c0c4034411490a885650265214592850070b0b22064231090324410700100032002d0076110160b40300010340ca09101c18084c1400040d030000d120000d0310005507010300061100710004080c064104409060541404018031108000100d0301d0100508400311003a01ea21003441d51061100d6580c0217000000c511017080b00078080303c02c00140d00c0b5131220344c032480400d00392142c00c0032803408440c0c0125190054000036108000080c0c10b01294104d441f18a09154007004008c004403000c203141c000e04810031200040000a588a2006000d08170f0044500c008411710340d648180c1240d11034007074110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 993416573 1250 993415323 993415343
    0x60a05040e090609060f090a080d05041101140d0519050124050f190c05010608030405030601150c0b151c06051005010912050f03040b03011502030418090f0b04 70
    0x8090008110340007140580100f0481c14007503001500d1720703030003080400c80c0000310001500000081000454940d0032601540c1d0312201210300c080500400c5500b95204117540c1c03042c46880d44030303241c80c0f0080b12000501506000b02d145c00640034040c0034001d42d0f20801d007213200030f8064160744565402001801c20074001ca59201c5c440740308a840011000381804018041c0c0d02c1001c403660120707a0a0308140745446224100d50f40c054400c8071160314090003d61801e034011842180000040055804c1102100c0d580d030307a1107001448101d0310045020004221186030000105140c040c660844e01c00711456020000110100b84040c0c00e1024250681c3c1d1441d44030000d01040b48951600400b0240c0d12031643d44c2481c0c00608480030034418104050007200c2800306114081c480402040010020303659100d0b034440400706150030a0040c1c80108560440040125000004460454101d01c04510903140d0085c0070400900084500761000c004600b070542c0090345010201d88114130405400c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 993417823 1250 993416573 993416579
    0xe0a021e0a0905180601120504060e0d090611071d07020f0109060c120b10110a150603031103070507140109030f0c0e100302130902060c0604052a010f0f0905060a0504 73
    0x104040350f40409903c2014134100f41324140e43e00006940c078980c42d217480400c207a10341e0f00d016001032680c1c05c80c0741624007980c104810082e51054002c2e081300e240b82c0c2c6103084020201045c1d0b40b903c81c03074442c8010001c295100b160004201d045004d40c07290050066500001c080b1003044e007550601c1808841096860702d03010a09a000100d4200c912098402004482989404648108401c603107034001c2c0400382904102c444030030807843c0c05042d0701c092a00c4803003c0743c40401000d04082d01048020405642014060420020a955600e6007120050402c541b40c01d5101b002032b0a0700101c02e0422100034804004100c0010700740c035030180f080364522403403490141c0390080c81c03101030481078085107004010800359461040301c108400400b980050350400c40e1002554500c1500810082400b400c0c0801c8240440414080701c1c4051000421100001d1400300a0906140c000d549022444a500c211030a51055014914004290805084aa4581000403d560881081c0d000003c40c001018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 993419073 1250 993417823 993417829
    0xa180905011434020a0609111e04050109090c0e040c0e1e0606130306240f0e0601020c150306040e0712031701030c0302190e0f1f0e0a021e0a0905 64
    0x665025000e4401d440034402c4090f0081d16109015800341500ea00c4070400c074180940d841c0c440130401001000ca241c40302c114225482c450320182a001d210320718000c00090001180c0c020080c5007070344038054690b8107040440500314143e020f80192030541d200039002c10350f02d01140040d406403150003182581030a940700c0340240036600400f01c501900041c0711a0f05022900c0f0140d905980d4840c0c804036051040c656540a440c906403900522000320100001d108201111200103840d0502500d005680d6000300583e51285040c0125821400c2c160b045001c2d04d007030402542c0c12040080c40851340e424010007403440c21301c040d0440380b118261510844200b680101001d842040c803640421240d61640d1151240c0d100710307101c080c0c02400c8121101206c0010310401c0d40107000c40035400c1c2102d00780111326007140e040c102c3c1c1101c0143c0400565000e410f50342e00070402190784000700305900750f5031042c5031340c080e400100e24501c80071a00302060b1040801003000e80035a025603914081c00e180f5003010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 993420323 1250 993419073 993419131
    0xd0f020910180c030e010603060c080c461805150306090606070b04030e0a05040b22090609051005011a07030f090803031003110a1809050114 62
    0x814100c0741c0d8050100256480c2c0803402c962452921030006014084040640c080d000f81e441170140c80d4601711000c01002807d91042600c007410741d49400b5a50b480c0d983d1034540707129440303460300c0113021080481200e055022070321180102400051660310703d80122018854110800c14021441000d103007000c001641601c08014041241e60075130503801000c0720441440040c1c11030340181c0d060030021f4100e4030f890003213880156200946660610305820001d14890fa0211440d2040107511030010302e91900780500001e160004042c0ca0004a440542490305000c1ca665208000c1d26451601e02003807540c8200300380180204007401c0b424000000e1350701162416000409a54440c1105241409400003515040f0b0b90504056905e49802d40d03042e10502800ea001400e03610000017042025030005c803070041224411004d040000c1005420401041c0d11405000f80c01085591617858a5034590080003546015100010300c0c4907600c0c0e8444200841101c00b4124106415000e07044240d00c055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 993421573 1250 993420323 993420331
    0x12030533011b0c141e0409021f020d09150e13060503070e0103020315090d05130f08010902010e030606030a030c08090d120206160806060d290901080111031f03020d0f0209 75
    0x101070404001c4200400c10b171510002d011801541d413428014119140c0301120345202c9050780700c00038402c0340c000f00203540f10003055a89001810482001410754030081c80d84450040d241c65446540248009000d0000c40240a204030540c44a100040580301400182e025060012043d505036066005061511284454481c59070346c3d42000c01c01440d1010945c441e2009103483c00781c1c2c1d101a400105020aa203c1d0003001c014818288001038000f030560000c0a41d5100fa01c0d4460049009070406032103210494803213405070020301000d40001d10401007010f4030352007200543e0600804002040f03000180307039000c40701401400d80d0819819010015540d000410240c04143d00a04000c000d090100183c40321b4000c000104001c115443c8981000e641c001c11800504d031041e142c02200b40d0381c03c0b41400d009006100d22030011840b2241801000c0d03030240d40004203803440d119051181c803054100f01c1e580850b20f00d00000880180d4034644c1c4450898090700f42800103951a004202000d04050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 993422823 1250 993421573 993421579
    0x2f0123010f060f0302070605100e06031b12070e0702070303080a06050607120c060509030a090602030f07030c0203070305070e01050414060306040b061c12030533011b0c14 75
    0x1004020501151981d401514414900501045000c60302038003c0c0c0544100240041c1c208003c018031401c00b299030b801141c01082d42c6c1849a181d00781455140c809032950142a280a0988100e9034140420182e04600306002154141c942d2040d5030b00c1c80180c107845000058001103001c10516920844564010380420002c0007074030f1518000500c0784c4203034800180f940081213405034001340148406241580c1141c8280b0180c5031140400d41c40354450426a8080b449111022075105d10020a07101e0f50041201c1c49440c20115860a407900300001c60100d91510075124040000350052001c40003d002e6001141d200e541003404100035240071512000d10755504204000041d640064021f42158001410701c0a903103484020070310f01b9410f40c2890081140210801c010400020180c18500700e640d17600300510748a00c0410901e11612100c0302c49070600070021845000c040c21500700444605040000000d02110b484108200c0340c001d00751a2868a4502046580c20914401c21005421 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 993424073 1250 993422823 993422891
    0x7060905011d071413110307170a0204030c05060706020f1803011107080a0c0203120a0503040c14010233090109020135090c0303030903040f0f0b0a2f01 67
    0x882d40708100505030b0f00e00d1748110803140768a1203040c80355001c48000b080a41e00709603a440c02d048003130090601490414220402400007440000851003035400faa540320b108010000c0c81d04040000c55001802d090310345035820881044040903e40040290110513450740300e10b8402c02d800c1508484881100b60400981088408000f50f650001c8540d000091f007841e030513004040c00440e240c2860b4541240d81d00c500024020251904200910b100320310845803507080740d40b00c260303071403920002c03102d4907002d03a001c400e000f8035200c0c0840368021700c031309070b04036480c0483c42d00d80d003254603c802610000380d641d42d035108031425543d21a207001d18802c5021000d1307030721285294000c070712241c800340d51440805c0c2c40c0000c1f59074110180080c07071840d4001000c9940b0790601030384040d16030b4090701c03d1103205503508074006091010360b00e01d08c00f2245030100c01402e01c0d1080c0003da8404034504402480c03410052442c07240c6044d940000c0c000350594100000b10800d0040000502800425040000c0201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 993425323 1250 993424073 993424079
    0x24080f0105041e03020c0406060c060509280807050105040b0106030e120417100c090e0702010905060f180f06180106050a0302010e0312070b0a050c070309060f0507060905011d07 78
    0x6626010081c0f0000d00c1182e5500d090242422405c111805403090750003410020002641c070b501c002060040c42c010001080f19454030050700b503854205041040080c00142c405507590801700c540b40013114018a41e141c5451450350b01e0070300f191400c4400701e6203440303440d0052000940c50700c240d02c494100d0300001d00045a120f401c41c010750143d8800c284111305200d5250b400c0c0d540030302c40e1400032040c07030901703004041c01c40c04080c100102e1405040307040e190001c0043c02d040c0c4140200c028440e0404091715140d2164a00e0b05d500c40d1008180c1d103c03c0e6504081f0b1000d1400c02c0180601e1141020050442810b24603c40200f002c1c0c1c91a43c041c150313040000074020381d80c82003c030074200da509090040a403407101c2d011030b0502c85c0c22249814400780124040c81805040081c40d0b1080d403038020100810341d2901a010b6082c042c41c2c5001c0c001500003502800858010030140a10f01260309100b030409031035680b2182914841d050444559469858103c0c00080129a0055440051002d4122142 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 993426573 1250 993425323 993425333
    0x50106021c230904020d061514071e0c15030f051e0105130e030c0c0a230d0212160f050603070507031b230601211524080f010504 57
    0x3100030303030b42c0108900016903405550f443d941120361201509000380510396075606211a401940c0d1400e0006c1303603a01040318000080d00d021101d02c0c59110300508178400203035030380d00c403900c460000441d40c4114821b0049030404980d180f411200850707507800b082d2141444c1030316040c0c41d00a0410340201440d40c0412103c41d079640c05090640301c2c1555508400e0112608580203403003c1ca08a0030309000004948444800c0803503640c06445e4162542c209c00ca0361141840020b905240c401144d41d00091224022403501e000503420550006068039644c081e044056400d00e0f4055400701c1040320400820091480c0540d9a40001e1004859150540c0340500c00030b00035200d0164010100041082c41c0c980112320541c1340c409668000e003c4007180c110780b1805410080800e590b02c03840e80305913000014160420807001f004080610840e0810810b01c1d650400328469481000c01402d846a2251030f240c0d40010100300147c103621072000d9500c0c5404c1c1c0941c01e00c0501e15201c001c0382d05010400020036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 993427823 1250 993426573 993426617
    0x30109051b04082e11070c0e010e0112060e12070209060901030b06010c0302011134110f0a0902030a02130909051c050702040509010c0e041406060a1101050106021c 72
    0x1040100d001100c06801c107400c0c00a0114030003c00e0340703031600c001c0c0d030080005d24005d42449032040c41204102c42d141c5004002c0100244501424603a40038018003115181c103002d030154a21410001c00d04030144001c0e542010404022140702140c04100e03c819031034002511070b00040e05039003901c4207506588466640c9a801045035040c0070000881d502054800d600c0401e040340781c00b103c00d0f1514226410b2104020035202440600020080c2c0003c103040800c50780350b0242d41c0107a03503079040c1c078451050128100c81c900c8000d5200c01a2a030016075292280025807155007c24801603076500982d040000c00d00031074104984103840c20144030002100065a41c0240d650611004049803212100b00c1c0c01c0c0c411080300a400034103100900040d510150042d000441c810348035500c043c21604140003c0b035158022520b864035402020595500702000240b88240962505c200c250369500046c41c00d40308280d0103000142e02600e01545e100c00ca0703480480c8440d0952070004444170049038410905 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 993429073 1250 993427823 993427843
    0x60117071415031801060605180910060f0302090603040609030813110906040b0319051b061e040305070b0903100207081b030903010603061d070f060e03070506030109051b0408 77
    0xc0b50001011415070403544494440c18299100240511511801d00900680002451103820101001001c0f45864014500740c4a40760300d4407504000c034134000c1e088805281c1c2c4c0912000f496400c0183c85a80c1d2103500c0250b110328050300021403501d02d41d190041c42c0c0351005150880043c2404060000140c3c1340c081c1d6446242708840c0c0701c1c000c2c0c0761400000e008240c2030320300c80da01d44102c0042c1c004074000f203030200c64032500036016244000b9007141c0c0c2c400700c6441020402d6101a0421809981d21140c80c00c0329041c0000b8944c0500b000d441c0c0d46c40b03600e020300c242c01414002c40c02244440d1589020462017403640c8081c0c07c01c0d801d000241d50b80e40300f1806402566070740024590441000d1060410544201d094010000d21889070f503030a02d90000c0055400d00d203203a030141031581c2d010710000911300e000c5540420341806610f2510f8804c075020a070a405990745800b40e803100007102e80c0c1e001c0c051806071400d10000501d9050001400b41c00703001020320b00300b40c05400c4c44104400c080100e4030500c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 993430323 1250 993429073 993429109
    0x117061006030e01141f0f1409040501150308041703091507020d02040f062d060f0507210201180503031b090402040902041815060c02030f0601170714 66
    0x85240000c44203001d8070782e02c0741040034150b0b007004011b0030030710a001c410003800e0008418a185a12070f58541d48224841c001c0002c01514041c1510381410303e0460f15500c240910000251042000c41502070340d049940256004c01020406200e81d401507101101c28103140b900035894440328074081140c13544100e40108032994041b500d0025503c0d0308045250b4554010403c108060301402210300815080c06440039040102c009511580c8003810300f0300380348081c58a1203510600c1c1030011203102c8403c100b0700041140921040e8002014814484c0704405d04081d11f5491a01d07400740242103c002001010107014010047c1020880100403230f07402c21205502400c0b40c10a003142d020b49071240d1440030707800510004000658060650180095803100c284400c0d5100c1c240e0080c505581d15500d595400c2c181e4500c08200346070180d07015818075480a0195440c00d460001c50300d0400350f09038016122500b90a00103408084140800c1000d00501c80c000c144190590300410303c01051001c500300c2e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 993431573 1250 993430323 993430331
    0x91f0e04060f0f1a0f18070507170304201f050408100b0901060c0b0a0c0c08030711060c180607230c090c04121101030f0c0206011706100603 62
    0x60102540010607950303002c110502140900c0308103c40108003042407070b03000b03c501e0fa4038907125181c030700f03e410300d01140180b0b003c901001c61401c00740c404601505400601104012803800a480340220311507030001c09620030b80f81c6c5000d09001514010002d516903010070b02180c110111341d0b510f80b00460244403080c503106140001401940c0030311880e00f00072058401c541d0004814206500040da04500503240290266038441007a100c031402020700420790344078100056841c03072207a0702001540b40c1c50b282c5000c0d81d103550344039881164403d55000000940d05409544420803c00103140c000d042c08030280c1c9010075a00f001d90180f10310703001e014841c4030001042070912040d40340c3c0300150f402e035041c01e03070b0301302c840d101e0081da9281c07009042c900548403100003d03002c034120019201103941704030100408004581c1d600c01d0641e6440421418555161840b0502c0803c0c1c1c41240441e5046070002c2c4100d5040102c840c65171852044503a64503403000040101141700360211104807005410045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 993432823 1250 993431573 993431581
    0x5040f0f0602033f040606060e1c06060e0a0902090903090a030b100b03010e0906010501020d080a020325020a170405010e09072c1306061d0607120e091f0e 68
    0x181001060000300308480480c40a038440b68400a240c4d24020351003910101700301540ea490036548040b401000350342c8103074000502110710703401d4032820f42c0c114807840000400b503490f1520701b444030350151340800c0520780d1031180b0700031804d00a22a58000d14480001c500b85408200010b075014503600005082100600102d07180b0f008000709140640318081d9925100d40c1c450b440f0204800003259140201d1145000004265002285601080f034055941d01200d907900c407150f074041d600103040c0b0740140c41d40c419004105504848000c40c90b903041d501820001d002030500904022020700c03190703003800c4c0c02c000c1040716a0700820b50080c05082034541c66203c0d591010203a40f85049c4000c20000e070042c000303284e91081c8c0d0390380d022029400112901414500000600001c44442e0b014030710114140c40a036a15100d100c003400140c49000526407454401d4a60303880c041c00000710001004070308030b031140043c51f00e03028a0f090703400b82030030402c1410140c00620307a4802034064402c2082581112001c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 993434073 1250 993432823 993432877
    0x3010510050d0504080307021615030218040908090f0603060d02040902180f040b0708090709021342080403120227100306080304231005040f0f060203 66
    0x1854000d682c070784080001340380038100326155510403160a001402100281c0700380c0303c0e0700200d2109955018840e03511042100409400950002c444215401c10043c404181079503980684200c2c0c03803145142549601c244424410034802818846204243c00e01c01c0010f0707512021703c8001426012280469048580e00109042c080c05405540305040d4110421100c1c1400040090160340320362030400456461000444110341d0a0310b44c000e894011000402801450390044d118212580c500c9290040d6180d1031009000801030400154001ea02c24441c880c04112982c01d4024502daa031281c8081c105403001811201c0c000c1004007404003c00000d801003510350b055401f8042800410704418070880c280760a055143c83c00c25105010480807000481e00c6800780100b10784480e0001c41c00c142c20042085821440d032565440754801c2d400c81905581e03030f621342c8070140c1000f5884899940e82021f4110426501c150080c007031030040c4503401c1103071560000445042c1d002143e540242c2160034910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 993435323 1250 993434073 993434077
    0xc060a090e0c0306100e090601030b030705040c09090b030d120f021b0604050f071415070804180b0916030b030a02030d0e01020f01090b060904050c0301020d0c0815060301051005 78
    0x6162010141c082115420400004501840b4111a40080002c001000b00d80c02c0e040303441029080380b403400100b0103c1d4025001034030760b680d00809552500d611000400c040b2502041c04400050b1590401c0200000c0c500c40c2442c0785c00300758060508040031440160115910b89504001c481c1e88120b5940301c001a40d060b00c80440604480728072040140084590350042a0303000e9806001c1c071291440c00c0744001540e5811102036000078a00003d061080080c070031101144108424410044c074000111180018000380400311704241c500c3c840ca036092000c84140b440003900403100310060049003061000520a01e64061070b0200303c0351086404a03040c00c0450400941607c81c1e425503000450b0409046401c82c24280d080362600c4a0042c1a14240c9421040c003800700301c50703d00801c00d6820904184e41d84103000c0c5085803041041100401e003240c0c00582c10b403004540d03030303128140d88a40c03024045070895107100d0b146010300309040004080f44010f01c52644103407009032641c84c006003c4c1d02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 993436573 1250 993435323 993435329
    0xf07050f040303090608101a0c0307080301120c120305090402030c19051c27020a080f1c17220f15140f06043603030608030403050c060a09 61
    0x11640c0c0712556450050050060b5020f010045616140068034a40003031803100c3c04ca071380c005200c544000030600f00340c116500044138000140420400000807032131150056000f4510150301044103c818100102c003104181c00021161220115007000310350f11205035180303403008841c01607580c1c40c3c080410141d44203088000c86000f40914003514a0798101018000c1e42e80c40740b8040da0080303040222141155001084117070080c90a40007103024013a0120080427040c4041c00c0000b0464895a80a10b016240c2c54501c50690000fa07058000340c0c00342080c44220010341c2001e03080c09131207807000b080405c0c0c002c1c0030703e00c0054826a00d0300010221301c50490680d400c040800441e00e00d0f41885180d44001001c041e06032410896505100c40c142104240700b0b8484904c4181c0035142c0b102000301030005025281d1410008801c0081141c0a0006000201c036107803881e000b05c481e06240203001e903565980312802b9a00103110400102c1c2c0080b400307003089c99003160395966584440a082d00c068520350 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 993437823 1250 993436573 993436597
    0x161805090403020c04230a0c09080f0a1b03030e09090102044202250f090902090f06030307140f011b11160312140f090a0503030306090f0705 62
    0x1405100074140c000c04c514000b02ca098406000f4100d030b26040b0709014503910064000001c0d03281c00662020306030342c0842c110038610303c2c00010340c5039100d0450b485c00310500400724198000400460800c00c114080700002c0c03000c856003ea680346103407400350250009812060207541d05000043c0c10100079411a0051300d0700c2c2903002d4950501c80c0c808150f601e52001214031101d41402c0300302d0380c040121150b0035502c800d44d00030000d4445440c002d2485e050301e1500701c2400800050b01243d0041f10b0800280500f034400400a1414164010003c03101c2d00900922010190901400300b180c41c00320032100040d402c0650f0110041c000c140580ca041401d540e420019481c1603164020720040c00c0c0c0800b0345c0c0245a0300c00030100c80001041d605c468590f8241402505560307400c000094520712030a844c90024180099410030081c07035280da5920010401c500c842c000200705280703103401d05504000d01010b0f00214114038000c404070322145400340100501d02010400141e81074450310440741c0c3c080c101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 993439073 1250 993437823 993437839
    0xe070f060e1903080703030902060c0a0311120307110304090c0e040f0c08061c12020f0f0d0f030f15060e1804020616020d14031306050307021209040f06030b010815161805 75
    0x40c00c03045433144030700304080340002d403082510281175a0010f800c04480c0c17201501103185455203001603849406056440d01c0f20f0000780400510b05c010307441008082485515000d01594004c010842250f0114402070700032860700d070305458080d611107035695100c041541c49d54110301aa10119803a4911014001d101d80108441c4260341580412610b18651100d000c880d0170940b08850366480b41d14117118400090005103800c04510300caa04558041202000000307101080d11410b8014001580c000364041541c5992180c00f074100b4980d0729001c02d00b01c41860307010f402d003a400a6020310a0102c0c084c1003003440302e05c00f429980c40d480380c8084c80d42d22800308143e0a4420f80d40c19201e07046190800c0b03400851200000c1c003207002c0c00403070384520b480b580904240644402c02c0c5485801080400b60003580d61480d10b41018501d1085001850203548854502c0d032410a45501d054076400d0711070400c05859060100003c01d10804400302c0c001800c210318440359810360021840700382e9020541c8140f40c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 993440323 1250 993439073 993439087
    0x60f08031216030f09110108070207210c0e0a1a012c15070302240c1204110a0b0702030106081911031c0512070f02070b0d0e070f060e190308070303090206 68
    0x511b03a50030300b01090030f0326088082d0342ca2200c01d070b0301e40f04148180101c004515070000440c032041c10710303056607a210705182d000e911784481a01c54462021581700450700d654501007142070000754021a184502407130141902c1010418001820740d82e008030040050811959088503074415402c49c011200d51008035840740d1660800941e115407110795410001d014034401498903200d600420b11602012404074a0000b2175030544401e0f040c010700a944d1080034440d000c100365501e001c100020120010b071240c0794003443c0109421252158400d580a50112004010181010303d0525000c3e802040072070607142100f01203030810250500d4040c2c03101c0005030081c880c54100c40a8030040c150030f08a64002d070340740501580e0b004810410013001d030744842001c200f840d5010300202540d07030b0102004604004203a142d54034100441e000717080030300364401040c0801c0c0e40c020006201d900c0100c4044034405810904e20004141c0c0d40406007071400d000403090b003030601175042403003029400b52000350342c2e8903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 993441573 1250 993440323 993440333
    0x11160609050114010e010b070b04080a020106080d020c0306010b12042607030c050d0306050640180b0f010c02010203090a03110f0105091f0c15060f08031216030f09 72
    0x3090041d0321017a200c2900101d0102005001e50702c0d41940800ea41c08103445940303541103141c20140702941103649030900450010020b2000250522150300140142d800a0b030405041c42c005030007140d45e0180c1806600c40d180d040007451604075400c40e0780303c40350103440900c0000c0340e8151440c3c074030b51110001d0394500301070303200c030060701c0c200d010b40c050364107101c0741e0142141901d0740c901c0f4159024106001802c280903844585800302c001101c151450040416140140132004180240d01e04040f404204051002d10b00480d48444200b2010000d00482000148004d00300900320790400c61320742d00010131039008004598140c0002800b4890380d80d80d0b450141c1c05000030303103801401090700c030700da2502d25402035095a603d62030041c000c030043c1020305404100145071003526420006600842c0740482c1000790103a00503204850013241e10f50038507000e407060401030307400030702c05510030031840300c800341949101038000c05c00b00d509101c8075100070f00c00ca002e0000c000300c2c18901231400d4000401c00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 993442823 1250 993441573 993441611
    0xa0803090d030b1009030312090f08030a150b0a03021b19050d0309020f090a090f0804140a0501050a031508161e05060d050405011b080613111606090501 67
    0x71625034041c032180301c602081c030649500000e10800400e01c0204103100003030203030f88075411640410000040040c07213502c41601c4140a036400f9502c900000083c400d0355100750003860580030155041d20344092800394013502900c50140300004042c0e0104507949000130307007000b400300c4550b03100c215036504034131301d001252a5041da581150310740300705c00c0200151402030140700c540c41d40081180d015603011000380301400307100621094600f13075a903184000040b01c1103181d0840a0150450541720740c104001080c04025040016109054401080210f40e80c40412611145058517001c950017000583c0003081400c02d411000141c001c0304a55041c00c00516181e004440390ba4a24001e080d6001c41ca48121a209024280e004001046010070700030a0341c118540203031040c800000c910041d0b5401074400000c141d002c0b80020303012400e1143c903182880580c01c54041455080001c07212522050003188111008840c0007020864440140041039228410454100c030090240850000c0288034038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 993444073 1250 993442823 993442843
    0x2060a05071b1b120f0b070e090a0f1b2d050a0807050708120a0b01030b1c08090303040308120c0c0307060506220608010e06040b0609090a080309 64
    0x41031425001440d4a8032841880751145800e00d0507012030160b03038594021810b030a040040c09489807010001d03400440f15062400740d4019105503002080c1403800919804014015900708008600381d4440c82d600c6400309500714040040c0003814991381d041110141c4041c1488240301c1500c0ba060020083d044070700104203003040b2940002040001900d9443c080c2c0404030240011018003150ba0300601071801c2c5a08500b9604045d400c000c66541d03071303440344c1e8030110100a481d40144203000008080e0f014942001e5000d0074280040102140490040e43d00c003800000200c00c18001031013403046a10485400e80310240989507110780702e007411a95503104141c085000300301100010b40c0d1454803002e91705d206840e98055858a0900e03152030015000180049a0010019800c0c20084102d00303c035088101200801081080c80c111030341e4210b42459491036410b0304a00200b00004032039000e10ba90110007294003100607120710700102d241002610700107003951000804d220000701c0015607007881c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 993445323 1250 993444073 993444091
    0x1e060f150a060806210705040225060f0606080f0429090307030e0a03151505030109030c0c14150a14040f080706031a22110706181707061401060206 65
    0x7095200d054011542c02c4481031480740d5080700201f40050301e050380040011904584940c0170700f100e0341c7c0c0e90a1400070340c00c03411110513a540c42d01640d29441c502034100107001074106000a272600d90040b8017102760081c4001d05100380a0b461040c0c9e141980900b85480c03030550b000070002d02d804000d5950340d40c0010350a0b0049400e01400e01d00c0d41c68031b8910582a6680300c62140c04040503125490060f00c0322190f00d0320f10089001700840d00d6103091080c090224000e07915010f20100a00704822410504d820000c031640300c0c0b01c40c0003056141d2240307441c440b0111181541d42d5400001b0115041c0042c581014840031001600140c000c0c00c04020005642c0c940e02030711002d90b66031070168100e41899100009407698442078403240e10304050300d00540740049126150a10090103004111003e00100d403142c204042017980500860344a001d03500700c0c100c08100000c3c58242c940c00c1d4070a009502d0300c6551035000070b4a10030000706030040089003031800d80b4120656160100030b51107502c00c40e400c1d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 993446573 1250 993445323 993445339
    0xc1805040c0e13080a030b061207030e030a0903031d0a180b01020303161b02030f012f0427020d091b0e0601050903012004081e060f150a060806 63
    0x42d040000182c10380c00b03214040180a12207a407079031815900c0d04410301d850180f5a8603001d02c4100d46910700140701d82105002c41c0c0740c5ea490721000c050100c0e141d43c1c542081c0c0d0303031080c0701c40b01d58141c201c071004041c0c90f01405d041000081030890000a601e09110242e0422581000010080c10404110140b0001c1e14001c2c80040702c21801203981c0c1c00221043c0c02500f2550100c1a5480e0244080514119000d11030028401268002c00e1601010201c40a521303035481409090480802d0400e46404020b10384009130402040c5110829004500800300081f03401241c2094006410a5414aa10000300e0964039107039078111210003850448801e40d80d0180622100701000035120424054654003070010f14151191001160103030028080e4503007640d42c88064080c080305030b80d0100305900c00801c0050799035051034485403c0c075810120003188001e04002c40700a103503010071001d034046410100c0000603520f038441c0c020310303a540700030450f00300c40104001305000d540700710114070403501511811 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 993447823 1250 993446573 993446579
    0x906050a0e06010507080903102a02160e07230304020a05040b130f09050703050a03020706051e0901030902190e1e0f0627040c0b16020d0c1805040c 65
    0x241c5940011a21540010820800303400058a0800075080194000d011280441c00c0c0301061030445002032011488036143e80603044080386902615040003106102401d0448010940500c2c1d1034010301800303a501030100006040948100c0028080301200e07540101d000411000701581c9a00980f0140d0151440210100c0c450805005110340b031040941141d161074607c801000060100d903a0181c0f80548031003003080461800c00544000e180241c0140c10f240c905450701078a0300401d54004418080306100441c964201c4100c890070b112421220a5900d480400048000709480348000b580020b00a001c02d00c098044070002d4140c1e125801c078941941c480e01005124000c0c2c4001d02004085180001654035098501c841c2c1c200d00c0150010000d108880080c0d14041e000a444100c441441c608000170f00c0041c0c4041030050845c010aa45003103108020800c0701c181044010b401400c021140a00304000c041e0031400801c117030b641410444480e0b406881c0580b1b0180d070180d80c40000c8403408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 993449073 1250 993447823 993447839
    0xb030403023a050d02070605010f0905190b0303040e1801050c090f0112060f0315142202011107080102180f0f120a0203011b2619020d060906050a 64
    0x14158029104507031a90282482082c444915000700b0b0070200002407201c845000070034005040803d1040401044660401300202c0c61141207a1060a034541082c0610520300360b000303890348501c1001c07440402ea082c803090100e89903100b140d00007a1032203030310820084102e40300003540d011039050200078419500c880048000c180101ca0003907600000b00540108c04d507000e10b42180611401c0c01b00850050b07510b20042a91040725402a02c0c0109820b0b003d0140b4840707071064412640701690585401e090446003000c003407504500300591268006480b006581c040c89601541950100485441d284c5030031499010b90040007880c0b20078400e8268000e0300380741200255800480240400b089808007208100e2072122101c1d03913041034040c440d044c4000d600c0038001c6c03010040991200440390900c80c01c000f81840340501c10800081900081c42a0840103103030b0160708080b4035075a6417071200460900c50002d2051048521302d0510f00a00018496025040641212401c0b111440d21540e26441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 993450323 1250 993449073 993449113
    0x316020f0a0f170f010c0305040515160503041a04030201150b030f06220f06210f0b270c040507050c06130c15080a060504180b09160b03040302 63
    0x1070408050300601050004641c0d66070203940f8148034000f20f07901c1e1080c9030469800c603030000301e01c480080e403901c0c10042881410480d4525026504020450f81c0c640b00483c00303200c15081130311104002d00040400c0602c503030b100ca80b28814000803003d6035203081500d4040d0081c40d0883c0f900d009001c0156001417808048002d4030b00c6031100c500c0203180d523694081017060200b4078405101640c881c1a10880c460307a014880c200e4032440c00800001d84074103000c1404e034902298102d442ca5080240c0e0018001450b883d8541c00455000c02e501501d502d4240030390015001249480c50340700c0010001074003d00c00000c01e002c011000791001c10141d261a042100e5510031000215a0360780001d0108482a1446030000c3e03030580030b1203100040399142c4054148400c010400c0c040020004001d004403a4044c1c800c1100822040f5010000740c007400400840788410b00c84040d01c007117034120002d60740300d002b403201090003001a01a82c01170340e1924484042034005072800c6d0010b11503000083d41c42d1440b414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 993451573 1250 993450323 993450329
    0x60108010c051602060c060c131205030a0309061d1005060604051825080405010c031e050a0902120f15010b22080303100e0a0c1e020705030316020f0a 66
    0x20b40c2501d0020000004420030b0301800040341c210b242008811907210040c13208500501103482c10a9071408800401c0701c160f4100e030450f076660408000500c0c0007520010494050317030707018180030600c039406007806001821002c0ea403410080071050610400c010110700c000c074082000d01d0400a98079824184140c1e8011409126045817091075a0820ba01004400300c0d404000c000708071801242c0c00c071100200080101620001c902c43c8410320007042405e0081500d00582890104546081d5584040e100f40120110110b9240c0e241b01080198003542c10490090b0b4014040060301c088849409607150040000c940460242035070010a40b4101d07100e003030403a4107004006082c03075000c0b40000065500352030700d03082014842e000000e409005202440c4100d100900c040003103031800f009081000d0008000701b00781490b00100000051b00400803624042ca42c268903221550b84090992030140c403038218035403601c000b0444400e0b90340c1e25904042000d100341d035a0095034200005120f60315036580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 993452823 1250 993451573 993451577
    0x17040302040f020708031b0c01020a030b030d020a0b0705090604030f1b0b09010c12180b040f08010b09010b0a020a0611190f140d1508061012260409021803060108010c 73
    0x10115006044d5684c8500d14100c665401601d41021408c030030f0300b281d10208091010985910410980b440d080c07103500d08210740c5001500c2502160751b0780c21501d42d0010251818841c020071070034400e442d00c01c1510050742c0c4c44454148a40181c1c1015005884d050082c1440080074035004108103040c2420f40d141c50b14181c40c7c1188503241541c07100c1c12010305c0c020040c20070500c0c0020007040141a00308030000c5c0880307901581e5036414080320b425000450f80207c0714507030600d00a840c036510750342c40413811101d0b41d85110752603034002c40702207084c0130742810050000ca0414800e4024012041d0040c0009440c0341102c0e80104480d60007030b01c9410303600c2007850104100088491444001800130042c100b034080c0c002507070103940c1000c1d100c03850560704950100e1340240100f08a50500c0d402ca40f0152000c82420803840030304c0c0e2b41d02130804c6840354a0650002014420700402001c3e5030a403400303800d14071410b41d203580c1403004141c40e40741b1400845110344504000040d180c0010300c034030700c0050803613 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 993454073 1250 993452823 993452827
    0x15100f080d170601030b0301021207030b121b21010204090b0906030c041d1b040f060f0306020c0c0d080a27090203150d0b01140108010e0403030b030a17040302040f020708 75
    0x54108200b200000900b0f86040c5034440d464104150380a10081c180500c13005201562070400540040460308060720850281c0754032002c14282c101c0008020040c1c480520703a004101d0050f50214500102d11480700740c01e0400715004840c8404190003810903a106090100441c2c00e0080c00c12514001c285d42d000c2d0990002e0040310114101500141d103481010070004440c5140307040e409250280000780c0000c41c20405541c1440e03450b1500503903044010280b030a0242d0350a0141ca00c91824203884010805031703000802c40d031002e1060000c0700c01da040042144c0c1100303819051a4203d5400300c11410001520002d031554100104051110b00c1c0318480c0c40245100d051401c0e40f8003d51001d00100441c52000031020b4184e40d4401c0e07400c0d0024441c51a00c056940b40c040118001c200750031101c0e041c803a102d4014031051551000480d0b10580502d004a820300c41c0102007030500c0780800e00030b00561714500c2500482ca5050001f030003241c0c4240d8040280285d00d200c01c208900036000001c00000341 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 993455323 1250 993454073 993454097
    0x30c032304050603090c090c040302040b030a020906060d23010302330d090c0605071401050103030507232a031c08100b0c0a11091303030e15100f080d 66
    0x440e5014640c800e100d80c080390039041c800c1c0005907c6040444800c12544000201801103090034003990005d144194000c1880183d40d900095400000a00b198019040800c8064940090f90887d054000b41040142d1103040184281e03805224240416030190800408240c1c104a41c000a0071514261081040030880d1300c900841c0d00d0360002c444040140d8454980001103148008603000800b59a210950341701d100b4904401e1391101c2034148a2103900d400c00400100781c0140441d83e078980c0c8101840125144040a800b10200712010013405118010342c68103c080501c090381368100b540f2500350b000381c010104241d50b86050020b1031860928603402d0400e0180140000c1e0b401c0029107a401041036140d45004800b0b8002ca410b04106a103c501400d0601c851184200c54400701a00e08041c5490314804041000d915104003c003010b56640615a00100a000454500c92800f01d680c4090500001c8001040020300581c0350102d40014005800c14000404108041041e22042092a6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 993456573 1250 993455323 993455329
    0xc06030a0207080f0915040f09020d09080c0c01181409100509070e1305040209040b04140312160f14090301090804030f050d0e06180d060603030c03230405 68
    0x405003800312100d400340319450020340040d0150282c00e1075003960340c0d2030312401410082038103c2c8a00c10500c1d003504010130711000d41c18805030b8003a039003005009a6980741c0218000c0081085800180c40301001094802c01d1010106800407a180240d071031a1858019801d0b00725005207511401851a80e1030300f0f941175a05154450940c88007201e1003800c1e601e0360741c602140100070100c0f514000240192041d81e454178140320405502100b89104010a15083d030110b94401c01c003400140c9081d892200040411140c540113803001c100071400d8036100da80c05081488007682c140c40b8051110301c2c500c080c050352413113001021018245542c0314000c031400810b003c0340350340c82151600d4165481c0d43d09913020032032480040005510400900d4035505881c20110704018a05c1c246400f007003081004045507984a6054900c0d0703900c03050034a542d5042071000103c005450380801414281030401c00010f05170045420b8a0b4940a52100414101290070b06100712221020310324980e03030103100030701c0076007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 993457823 1250 993456573 993456577
    0x2180603010b1e03091b180f010801110a0c030e0d05030f0912010c170702011104180e0703260d090807020114120f040f0204090506090c0a08030304080f16060c110f0c06 74
    0x50010b01310310071010520b47e02c881040310440b03010145e0840040101700440c024070a1042d0140d84500c03c0d824501d080702d000309a62001c202c09800c100000801ca1465541c00d0000c0e011190f00504072a540c0801c085240200d801c0590107510680c1c45403041804a081801807050301e042660311507207461503504030218002409003244007190340c0e440e010b840c0340203220000d0005e0904040462400b2060140070002e8030440801c00c427068100150410000780504a203030b00610444e41c561102084110100c010b90140d100440b41c0307141411886014020510001c1041e68002c3c0e0351100e00130808044070001d403060303042e43c080454003030b00000d02d01c42d20780c0c2d0002d40261040844524224032a0001002d81e8003120080d0380351703049482408103074201089038001c2d914082e958204c8276444e0920703040e100c0c000144040c000e5540080c20649a0840804588240203200d041e41d4111185080c038000500769420f4580100e46070303000c0c0300918071340016000510b0402c403008240009035001030051704d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 993459073 1250 993457823 993457873
    0xc030e030706180501020309010f0b01110c13020d0513020102120403080910090b0304050c10110304180b1c05010b090108030a0c1e05061f0308040902180603010b1e0309 74
    0x21040f150041000140203000440c00348641100204841030f020b03100400310313003a0608103414058807072302000c5c180e000828aa40038080c1215182c03030200d0183d20041c01fa105010101c10300c98a4082002a81c10b4580c00d0081d9090007a801c5030032840d500c601e0003119114500015102e01e609000e22000b5280036515942490040d190640d0703003554603002e94480383c006070b03000c403000c0c0c01c0080c403500303103080c5450b0140c0041958a841072040f80010035443d2280308900a2480d104003002e0441c4454406400c2400e1401000d441c1907000c0f12b03009104001c0d00c688540494040d401d0000d603180038603284507110b043e0780450003e14903000c5035060170b5510042114045884c080744001c10000e40407084110801d1074003903c003030318041c5004600200326207010402d82403003030a170720428008941200191005c0d10211200140e650040170321907890f2100010a0035401344002001007a802e04500180030001c0b50040e0036a4052b420b0107100d800344c0000c03914841c80d03038481c1492107010750b011465003444c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 993460323 1250 993459073 993459101
    0x20303011a2d1e041404020721050d181203241202091e010303081503010c090e0a0e0d0309020f0d06020307110c010c0206220801050a0c030e030706 65
    0x200411114082119620000004aa0300310104500d20f10300700e110000c00038011003c0d4402d2611342014503040ca20f4665000c0309000d0769000c00e070041001440c4d6580022560311081d2600025150000100039a0000c2c0241683ca4103000d1140d01d0407403d103000c03508195101e003080c209000c510b44201d004060440c004a615442980401f8aa048103106000901040e18015100c101c1038014481c440e2000781c0658040120200c03111a0340403100c0c03003070341500d6142c90030742031548410021002100e61400f4242c6d140d442d2061101b0300c160440604400c44040b2052134a555a9560006c000c956046005010360303080324181e121107501c00c0d40403454651004003040005c24200b80410010f209014084804a50000c1030003d06a0020003040c07098000a00030324907680408002001303900a040002e0003942d001c100a11100040880e11240c5004031030b004400981e500303c0c01e4040d020549840043c80e240142c15110544240900e400c07800703101004600d81841507a66500800d019004c95070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 993461573 1250 993460323 993460357
    0x201020d0905070807060504050901120305041814060603040201080f0901020403060f0207020109170307030806120114011e060914030309060a050301053c011b05030415020303011a 79
    0x40112107200d21184540608010f0400508007415585018110740000d0103120041c0300400440e80c0c0c1d03504460554040b403e481c0b0090034545400d4802d40590b41080c03651420014012910000e150300001c9220150900c000c1540c8601c01401494401614041c0c00140414009260701178180381d40c9403c02100400141f0309596519001c08a50b0211030440d141900058442c0541da44082c10f030000d40b10381040c003404030846a04095591203000740050034025401c0c0000e20b640d44900c200c4500112a000030f1090845014010105207002d0094005000700098184003030030711409924240d99141d16500c50490911214900d640c8004240a6040c0300c00c104900072743d15400068065103103961203640c0c0b81d505140400140c81c100699201d42c62071448005a08189103180310540c401030709001c4542182c00d000121a0908290740712510941e5500002c400c1140001c010710485415190901801000d540126107903c0300b03204140e007a0918001d02515020600e00a08000c55103248001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 993462823 1250 993461573 993461587
    0x4060905070804260706020c0d08010b041e030218090d030509151305010204150806150901210204151407050c01180f0e150a0513090609211d0d02040c020102 69
    0x4525644600d908481b5160042801031841404101a21002e092410003042660501c400c0c2c5640d030145101d50000402d0722180ca00041d003151070744d0000786401400203400c8c03001d80122038001150956695030940308541c1180a4079209104040c060340445d00500b1070300e200089281c1c000c503000b0340040007210342640c00b800000c1003440188002c2c07840d000b0b9039452070810302015041802c010007850203100040565041405150f0441d040390409082c0707114680c800012a240c1c0c40c0c020f1010441c07507440000c0c041707208041c80038500600f10141d541e01c90311002e5440390340000d00039803000601070343c042c08403d8007940c05803903140d100e503030103c0c0050b00f034941c0d0707c480c02840f1179568400001c401040040c04a442c0c5248070250b07081d10103460514109140034007103036644002c4a260001c1c2641c40d82010308000040c3c010070342080d044658000130907295412802d00d90900d5500e42c010461003091610310041111035001ca105c401890b0340c50b14892a02800081e103c0301080c0f20842d50f00300604 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 993464073 1250 993462823 993462893
    0x915072304031202060a2c01270201080c120c03131401022505060a0b1807090f0b0705100f020d0906061419060516020d0f0b10050d061d150604060905070804 69
    0x502e920489c03501006036400c03040d0001400040d4090b14806450034108005010034804060040e00584451002c030354035521900780c5101603019800041c0b17000d1005000c5039500c1d0054001d0000748003118442e0345580070424514030b4581c0c038420b000b000b41e0890740c0084c20314402c41e800031512010141000d00e0032402c0d032554503649030f801c07206240400c518080c103000000728811080c0280007012402854074130240c540540c7c1d1082c80350b03010410342d21044c10170304107003864054810a51016030140201c82c0e691a09102900351030040c01d8041417400c0d001d040310b14018203140c8107a031501c62020303100381c1024011502a032012003c0c00410100b00c20620042c1ca0351101450800c0c0618149c01d01c0406502c1c0039100e0700c0c0081c041c0303100c01d00c10440912140d55883d0f41c68800583c000b08c00a40c0c00c0b03407104c0e900d041c01038940549403140510762841400284249840344a200212003c02c601600e0351080d104441e020346840300040c1030440001c3c001080d00701c1f40c2c0d01002d81e9058844039078014003a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 993465323 1250 993464073 993464111
    0x106050a050f120118081309091a1005060d0e0606010302121b090a0e060102060c1312020a080118120206130b1522050915072304031202060a2c01 64
    0x104941072040010404145000480410090a600c54081c0911f1459880e050302403a129840030203800c2e05030021854bd11405002c902c0280301c0030b0724868031419089980e000034000070601081c030b40108000034404d58401d10031100e00c41c82500b4100c1b1030351074020f00072406180c101f1000d02c1e01a400c0100300b0039503480600410003868003911008180c6040800242403100261407281c0c068000d00401e4039001e45c6000d81010307501314018044000c00d280c0006000e9003282e03884043d00d546040020445104080d14000c0c00034054001000b6100c0c920b601242d031028102d0b42c0c20081040001c013a00081d4402801c507800184040c489402c55600400081c1d01c50000c90f48006085211121150a03070500c0c02210360000440700178044940001101101c00c940c001c01d036a0403c50415031811704d0980724550740c905822210650703501c071900d0785080701c500000e207a84500940704800001e1501429400340210400505040505a8640e0615005101954502c6144954031021404100d01d41001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 993466573 1250 993465323 993465371
    0x120204180b130b0f1e0607050a0221060a050406090203060702030a17040b0a0c0c1e0201120e460210050703020c3d020106050a050f1201 60
    0x1002402040c20010440031a1002104a41c02800c200f680512a40c440c2550016a00c068403c0e00364942e00e402104080e2180b8001e469000f4800300c0c00300c0c10311100185012a180c802d40f06000c0036251040611000300051200d0000340e4481000940311841d68ac10040d08175211b000d02181c1100617a0029080c08001c80307200700160f00110b0030150140d846a455600844003d030710840905094680e07400041c4000c109103181c82d110500c840105105050540350740d500321264240b01000da800400e20600c5071403003a400117112000600b040031051141c601c0a00c3c00d40010f10701e020149034030715400420a00282c1c4251030404482540e4940034481644038440340c42c3c102c60b600d0306441003000c8281015900c00411a080c00048000703500010064000c0c80103c5a010754959000c520205804c809104004100fa4044001d00000100072010000f118250024014140c965042c00035500f26403081c15882084070b525070302c0038200201034500387d20a80e40041a00b6180542c0841c4003843d101c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 993467823 1250 993466573 993466619
    0x11091002011a04020906091c0c0b0403020f010302162411071b050a0e100f0303080402010206060f0a0e09010212070207060e03010911060901030b040f0e01050105100f120204 76
    0x24000112912003121010042c140c200c0e4110706051800c00414603c0c084c980c0b215024403550100c028178082c464a08051140c0d0098600c950107444103030401464100e884201d02485103600c104036558000d00075981080e07010480c002d00c880303444c1c4840240300c440c1d002c1c0119001d010740c2d00f003d1180c881c0c011040740c101c44410302c9a4030b240382e103801e500000308884081003c0311070b4401480b540d0b81e002c402e1021186000c08810140e103800b0901541900203034000006801c80660000415801c401c0c110302c0b4034003d030251a8603903591018071005115000704264044040300c0207106402c10008017503001100135000504291282400070740c550010703514000981c1c4100702c204a101e5000c03604040401095000340800c0d0071076074801c03003070080f451496841f6100101e43d0740d2581c0d209a001400e4050028824000c007010420fa210040c82440c800c50510750804001181600b8840509010700c039075a40c0d0680e090380034107130440d0351517000c0d80d000746819006c03c800124204c1034111114540c0e03c803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 993469073 1250 993467823 993467831
    0x14010914060d032309030a0c0e060411030105130f0504030207051f050406030f09050601030c08070602030f0708030702070330021609020319050108100b09100303031109100201 77
    0x1400846200030002003440b446200000540000a13602c2180480c0d042642c0c0e54404650b200440400f20314042c440100c2e03014810b00303001074140312110490808a403441007200c6255224070043c0002c0d03503074281e04c004104804000421131401c1c0048100383c46181e0140c001804510041d4940607540c080d20f0940c0182d011600a11803440e00c12048203100e010002c13140d8140321001c0002d8028080c40c41442c007415a2964a100704544940010010b194008141c5480d0340c2c481c602042030204600803401c81c1c1c81550310110b10b2500000441d03c4c01c4002280700760030300c000741da02d0a603240c1c8010000310860281000000c00610b03040750f02443c20250545080c401c102e180c02400071110020f4204045500042d28580ba801807004010141c0303850103405640da5480a8054856101d10900d41328a1403620b800003503010b601281145501c080340c842030004031515010009005420388241044c40303500c83c030030400240242e000b01c0c1d02902c0f0880850070701500d140000c00003448814104e02503511 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 993470323 1250 993469073 993469091
    0xc091b0c15070903050721120f0906020a050601051e030304090b100906080f070e030d0509030c0d1505190c02030a140c0a06020310030611210f07050706140109 70
    0xa58201961008040c80c00083c140d2a41d11007968500651241c283c06201180c030407280c4e00110400d0640302ca810620416225170761000007400c0d07442420322200064021140403a12034804a001c01d0780030f070401d00600c2036034284001c00242074480850940801809068100d05071002d001920040012100004000060b0014000d0100140500302c0403ca0118000d1024507003114115030003040c04036540300e156031455410740341010320369100c84d41445000b04d00e2070319992010052250600030707030230b42d071404451400707010005e0f404040003480c015503070400052581e1550301490f8400484a1811424110700001a044405280d41c00b001a0000a2228581e0360001c0c200070b10018203d502614104c5101030680c0c9a0480c5000245855000070106070001a82c1001402464015200700003204441c02d12803051392240b0403c0c46407180341445c0c103061090802c1c80a11413010703070a40f6045c4d0b0b680c25608890359800310768100c2d501a9208400c980240c80001c0e014040e0414030400525112 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 993471573 1250 993470323 993470353
    0x9040b1315030327090b0f0306010803041a0406140a18030b0406292806020a0b0708070c02010c051501030627081206030f01020d02120601020c030c091b0c 68
    0xb00b000c1c11004d0f9004515411001c650198082c104440d10150700156000304c00d80001c0480c04074580069051086c2000803805800104c0140f0444850301031f0440302032004020440d0b45d00551040380042044101c101d202036000b0001042d0a50251a00d41e0b5050180103541d4080d04140e0415100303175004108100c200950b034400c5000084440c844e1150105040c000b0560b40b00e07064242601541e003c010b25007134501d140c0c6440600ca6001c0741e4810003607481d100021343c0c0e13040e80300040da01d242000012400160140003800e020300e10a075600149508a9001550040c840310b004481d18807942a14076540e0700c11080160107540300742804519240c609e40888503003102e002040900700e00035180c031000a011031040310881c03050041d0030039495640b0700020b401c01c0f0307030039400c554194000207100110300d07115401080360f0091403410086a85602004a0740d9079021040716815501c440418860703450314170840c0f91b0040b20b6213500440400c6040c5100010f0300402d1080c0c200da400700448400350702c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 993472823 1250 993471573 993471587
    0x130f17030108010605130e0c040209120709091a0f1b09030303091c031a0f2d03120c06071206080d0c0605010b090a060503040302010902360c09040b13150303 69
    0x42c41c0202c10300c80d19a407041c08684507810030230700510481c1e002824403010380b202c00201e1144c40001d42030700c80c01a61100000050301d81070400b181c02c00c01202034031039611206102c050041140710018491581c1d642c0c00c2e0031440740560011203805106112904440d03070200010351190000c0c0000d07018018400281d80b607590301c180304600506060076007102c00f8070784884070381c41c03808030032102000b0325400703030b004280e08042c1400c5412154056001d0810031900c0140140441d90302603080300c5603040464040c010a029901c014a5590001c0000c500154459900b06d800341901b2100000d010ba40c94101c00d01e0100d511508101180c0101e00d0341c4180921031282070700500c0c8079810a8a0030a40f840010382882c0300f405148284031002c4046014940300350702800707449034040c007014140c1c0b0408002440070440c0c0048200b0726081551130714100082014041e002d08040e40415003002c0c00e6004000c041c0246401c03580d007050317203014400e90402441c00703507001005d20071000c16001d6065042c01041c10b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 993474073 1250 993472823 993472849
    0x17070b130c170a030509060903010207080c0d1d0d0302120316030f0e12160614190903082a040e1b131a0c15060117130f17030108010605 60
    0x10510142c01007031400c00861041c41e1290b25140040d43c030b17182600002c986015a00320250550301c003092110402c9411001009403400c074804490402c5c0940b0f200b240c60025071028000071856a26001005040c00343740b5070011382c844c1c010740e81400c00500c0b402c100703a00106c80450140e840301c440900b003241c05101c0c460301d000c090a8240400152000700c40c0e50786514a041401c00c0000103400c40d03500812070070000762250b11100500c000b00a00c1c81070103200344151800c140404038401085281041740c450f580c20503603d03445903009962404680e000c03584402c0318074159481e0356100c0d00180c0340d2000c001c2024102c641d0b09103285043c0701300038042c905212100940031850802c00162405c01241145c8211249020648581501100a50168003500a0011041c8a060101c1c2d090382c4c0c1c00c4020034401e240a0741c0c2e01c00010744410391240040c2701030798002c0480155400c0c1401250a80c116040304600440c1240282608080c0301540e5610980c8005056552004180002d150488100000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 993475323 1250 993474073 993474089
    0xc0a1104060501020a02030307030c1403030103030f1704151a1f020601050d1502090a030f12020d05040b0304080a1707021b0d050c091b0c0c04110f0717070b130c 71
    0x4040150346c0825540d00c01c41d2070203018020309420900c1080080c00440d042d002c5981c00f901d4495a503840c0c046c203001840e0300041d0114030b000340d00b40004810503554501c6141c00c0900703010b02d248000704030380050903d0031400f8100021016013803c40d460300100070140e210001050500c8a032a0007009041c880180c2200d4032030388170710980c1d6021403c128202c1000c4120201c005a43c4c2e03d100d400a0074420150b0b0000380842c60f032681ca00140102030041052161181e0280c5003500d4070402d00319918030a81c011001210824030100c5c1c04600480c0181c030303216017103003003000001c1d110b034111548401007203480c0c40040c0e000040300da0596803820300404845078280d03016220340f4010303030350107444143c1d510708940a043c0c050b000540501071000b021503054400041e569032001c0c03c5426641714131164a421340034604009401c41200460300407589121140e1102e00c1c01d198295a803110040d21580e40001990014042080841c200354401c5000d8000c42d120380841c9021440c04c3c4030010030a50003422 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 993476573 1250 993475323 993475333
    0x5161b030b100e09030d2c060703060f060c060f0902041d0f030a1d0d0204050c0d05091b06073f02010608060c0f0f130512030a0e090c0c0a110406050102 67
    0x1a118000025207031038240314000403910030110031f080528411500c2ca0204505991029034104400c0071640700c0c01221650380900c885a10707548440c10110f2103104074000690130711041004102c1c503901030002082096004612a501a000201640c51034500e000101c000c01c40d5990444104001c11407080e0343d41ea01440c00c2c060b40c9400982403000d0103075260304041001842c00f1259840d981d0682d08c196004000700b140382002c042c49413a540041040300f040c0e61400303020a8254500040b024032440200720308580c0b020712101440b245070420308084841c00940710700d02c418110300d18145041406511121004610041800b50101e184d4203940c6080da45086400e2000300404101c0c0c540c4000c03500070041c0c0d02d04031141000458401d130344442159450120b01000c4900c8a00c0140003200d4049034030000c0066038082aa07180d100381c940802c01301c4c01d2010120702a0400aa00030ba100606403140ca00300b440c403450003424140c840b00200c0d41441eaa03600e41900785000d10840011f04030a2000700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 993477823 1250 993476573 993476581
    0x20c0106091524050d0e1e01020301080d09080325080a0507023606120709050f0c0c0d0c031202030a242d1a0306010215060105161b030b100e 62
    0x242c2944604e01840141607103c01c400f4048031b40410a03121022594401c618184640f0a00503000f50000c2c02031440c02e000d1603a00b018100c0c443c13540380c42035800c010040c0d03241101e02a4490402844411b810b140d5504020508010901403409400200c1c003684500c2c1c0da41d11584100100c10404140810740d43d80c0c800d0b0038048c0300000c0c028030403204050000c00085a15a0f20005010b00d4000320080346500c01c000c1c0103e006c81c1d10350080c9002d020043d824091940b1618143c11040c007d454203c4842e600c075030a1000e0b12881210702c0112240682003d034a4190500c46050581c1e2088501940c410744a8505103201d02c00c3c6a070ba40c0300485c40f0004030380181d040441e101d0040c4600a6141c10800034403400c81c034418031005030f2500804075500130066038035080384a2100c580080f2840c501500503056071484000154282c540f156805075900b501d000000b01820603002a003801c150b400442c90440141c0c5940e05004880103503004011801e460320b400307141280b40303000c1d58000c1900304810310144 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 993479073 1250 993477823 993477827
    0x109140c0720220603020907030504030203070303200720060c071a0d020a0801031a0103030f051c0c020a02040b0411040512030c0a060f0b010804030909020c0106091524 74
    0x8401207103210441030b11607182d003100180c040e21401c1c07941e00505010001c0d242a8140c294000d0007101d1007542e9000241da00d081083c1c0440d0411600036000d40c10030400a000a88203a0103c0500b04c2c00a5150511383c90b100c26061580e040400101c44c15540c54030400c248041d000b56502405138119000c82c40d0040450046499040e0780c410f6000c203400c0010380c08041d90f80c3d0420f82d51241758a003c115103981e20440001c004071020b1101750740c141c02e01d000b0042c1a000c1103050606072501610fa00c8039585c00d1070821035456000060340e021140d0120740c0740b481075500d40030380806010341d0360042080200600410017101c103840303103182c4140d1030481180c42400c00b50082d40c044030301c03c0340e04180b42041c1c600e9850a5100390400c2c94031900404041d04100701050344441003030000d80404000c070808600054031407400544000d40400c0c10200200101105d60b0014004211204000b117155513071000c028040c0c1340445198180e0411a810910000300d4074508202011721807000819180500540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 993480323 1250 993479073 993479093
    0x901140105060d1503082214100804050c03070e060f0a140d0311010c051b061e090a020d0c0317030f1506070813050a0f0810020d060e0109140c07 64
    0x100c3c64509407910078481041c000c06420400a5030000d49030f5649210003003c442e09940e07a0070044940c2c100140000c2114502d04418508081014101d001c070101c681c8001d450640d002001100e152113580f099035000e841c01d010940c010544806030552a00b012008c0294240121380c205000d05426081082400203034030600300084415129240040700d2800c040f1100b001064041e601582810000b80c4032540c020001d01100ca611000800c590134800341e0070781c85070340a6030007200044442040d50b01c4510001312440c0c0044612040740c5055030b95902049803100b025400755240c00302558200140407440d481040e03400c007000045865490860312144003140090540741e4001040c841c442c03101d031501802c032001c05030401e082a440b5030b030982000c69045558046c02c1c2c0202d034480700c0024904001c1c008a420745101c440034000003a0140a030a009400040784142100d49480000a6954120300e555018000e070010100d466101030055480c10321000d000b600600c0e00402410020070f40f5444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 993481573 1250 993480323 993480337
    0x1503020a0813020a0314100b04060308093102030108150f07080631060506130603020c071a0c07120c0b0711130b01020c06070c0b2d03090114010506 65
    0x591000b88401c6400812030004542c0c20003441c4140c80c602262801c03d000440401005c0c11314400d0102c2440d150601081c0e4500f4840140148000c6c8494941c074a41083c415903403041544102c036686540c400c00000410b203c4001c03020f12503000006100d034010a11017450504040d042c5076442d07041c0507490201d003007002004c11040154140210b1460341c0d0b03c041c0d0401e03420b07042d640e00d600304c4441500b0014620701c0c4000d110106241880000d86070802d372060314006640603180d01010392501c10264041d503c05c10340301c582070080c54130100d03107000301d01c40141a01c2c800c40f030780b03d48401e820040f03e40f61034610740207580d1003074503460304900051040c0114004d480640710920b0b161742142c41c0c440c1c00031030164503039640310303400200e600003c030101c0e44410740300c1c0f109030300300c44500400c0303014030032180304d10300026040c011802c0301031081d04440f0b0024889400b85603080c0349011000070717803240b15155180c44072848480004c2440b480c66402d00403801c8180100d50303542c0c01c80d498a4002645031240d04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 993482823 1250 993481573 993481591
    0xc200312070203130e01060f02150601110a0c1d0a06030510021c090506091e06010504091716060b061602010f090f0905010306240b09130906061503020a08 68
    0xc0d0014010038030a005030342e2442440440c0c01000341d00c50b1082c0b00540802d004460010394015210f00c0d00c0c43c40010003040851200e0091a40e90b05c54500468201e1174001580007540304421504000602030030407c001000600542d42250080c00702c09016808060182c400782401c1c90170610102d8800b0651088513901128016079500c0301803a0200604111503524080354601185030050000100b6100d00c50114601070724401c042c91a5640d00d07241c03001100034401c1d84110014081800e20754041552280980c143c1800f00b580e007500c0c002240d12500c080100d80306110a04800c000f010301035201e0250040b185541005120403040c0000702c20046c01904111010441d10b120501403100b003000b0b809a28a860155502c50008001501080c030084074403610300461001507280e080c050104286032140715202d82482c2248416039600026100f0b0350101058205a05c0c00c0300d14070600b000103101d40004120207143c24028000704481d001450103140c010410510259407040315503901030286 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 993484073 1250 993482823 993482857
    0x5040e0a1505032b030903090e0403050c03040b0a090e06030d030f0b0a1d0604090302100f110d150f0f26060903031f03020d0321020d0c2003 62
    0x1e542541890305041c0d0210741c0600074100f07402980800140c5003000300050313103c03249600341c5006045044890200d8081c0c0010300200052094259207131100c0e8009019103403c034200384140d84d0242c01d40c3c1c420761103007803407000028001c41c2c8540c10100b00e00003004990043c0d182c2d8901400030075260051212024200355560b580c101403000c041d408130305e00c181c0141210119079266242c00030703080d08104421000c680000001550351415008080f062a1305038041c0102c0f0b0440741a0001402c004400740c50095120390305c2034120761700b05000d444071480c98070b0007103030306004800010703e007410a03004826080d01215041c0810040040a4002c0f00c482c0c1e21440b0200480c9040c03d0020f0142c115240300901848092044005000000d9170080c4549050f00e0140c0c005200b1940b25240a4031000750004821442d003400f003030045401c1071038800f2040310f8054111010800700200d80c0650105246580c0d641d01b06a0f00a62010f10a00c1d00c400440b20303d5200d80316012a1a502c0c0184041d1041c001c4039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 993485323 1250 993484073 993484091
    0x3040f09020a2309040e07150516021807120c09060e0102030c0613021e01080c070501150801020d140408160f060504050601061710060f140f1905040e0a 67
    0x30600c02c24a09880c51414090b61a204010b00b040f07652003408641d10460034420030000e0100040340e400200c1e4510009100c4031040d5a0050b10f56400070030081d4840f0090102e5040944c4580c03000c2d68030300514402445d0303d4175228101030554080080d00c086d0070392400341a00001c5030001d418405851680c02c280158140307100040f0300d944543e5452406d280510401e03c14907901121156804a100300c880d15170740409802403a0460941c40f244900042080340444c035021100380045c1035a0340100c0000c0740e010071300070414200010607808075034541e50025840d500000c41e84100c040703c030000480034029013069160fa000b54000da004500f2803250308000e0204005078034203000d02080d8400014452490203051064448200b4814540484d0180345403c0084002d080d40504c80d19540345c00603015800c0140031602080000c480000b40b111704150102540b0441c800b6001d012000e200076a504e091600d810010300c0f540d00080c10900409200c1400444514200300390301c02e061100015035810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 993486573 1250 993485323 993485327
    0x151d061003240e01060f3c080a03080702010e1204030b07020c09072304031a070905060d05011a04060903080306030a1e020a0b04050a050f0621090601050303040f09020a 74
    0x1060a03001d580b070510702160080040010341000040b80d5202c0c2c1c803d000556107948250030228110f04084a0117407045201c03002500500485450914000a50800940312a40700e850010121001d8022500c04010001c1241e1709000c3d00c4242c0c690800075000b29012900805080e000390301004000081e42d100048000c0e20802c22a00742d680c00038400780c158107040001402503c8403a00c0c441d001450500110a00e210500454003200c1d88040101c1e610f01c0e86821200c05000d02030a86020004081d800061a65410002c2c0c841e0020803074000415525000115604002c0701394401041c541c01c2c0010080c203034202c2e026104890b00705041d1562a40c0d090006800c1a120140c02440c0341e00509621500d9080d40050801c140d10a039004400503443c1c0909019038000c1e4844c8a0344881c950030b091010742041c160490b90080080d044606010b80c911510010440d4030001c044102800400c208031001c0402c601030050201b82c0c0035600d4241040e0100490034118090524215000240d09010b14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 993487823 1250 993486573 993486623
    0x14150a27050414060906011802070f0501060b040512070303050313140a080a1101110f070303060b03011527030f11030d030c020d031a01030513151d061003 68
    0x200ea0840100020300c0c2500d000c061100304142558007030310420001401c400740c0090710606035211131050380b18890140040002070f50042c042112403005e0700d05480d000500902a60340a0254412001d40b100c1c200014007004644040c521051648003070401c1000c070343c00c10100d81e0480e085010028111500382082c018268981080c01800d109007604041444280002350642c8480c540ea10440001b491001c3c1d426102c501e400010442410403026854450b81e00080c00703243e10a080104007680e848516404542090b40140703034000c3c41d003441c040141e034171410300000b1440c26200055982e0600010030006030a40c000104440d04222110007070003100705810b2103075080203046441c0e4a00d804070003006441d1004003503025200301130760001d40d140a4055440158010480f040480e4110b20046005c0d240c00303000006110700c1107040f240032801010201040701c002e000d02140140860b1801402c15840c00c24000803500a8428000040c9481c2c0a5008803904048001441e80340b00041004507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 993489073 1250 993487823 993487889
    0x2112081308040308091f120c090f0807060e0a06050306040b040b0d1a0105031f02091f0509010f1d0405071b1407090c02060109020a03091514150a 64
    0x72180031070000100500d01d0000c0204020a070795101c141141400041c00850070406104040b543d40c111b441980a4035030311400c05840c8a1800000f295581d4841c0c501c00c8071581c0100110341c0203001c2c144034071500319440000c650310540ea00f049040c41c000000b06140401380449105586801c2030080c50755503500070504035800200901165a031320324100600700b00c00000f4070903141030340c4000241c0b403501081c041c4002a06244011569040c0180b1400030b40c0208107040d40001030011020420002d070f84100c8440316651640f66541142000140a202d001410703041040456140040000260008680c0074001034402141c5038803104030940302d00c1000a0400c403030218004d49002442944c04000e00c10304410380c10340b50075503210488902501e0081481c2d10150344a02c00400c0708070500d0380200050b41c1d0b2880e00091145d01c5595031000c8600b10150724841c103031a001c104983d103802101036500200032103c540c1808201c0f00100d5807041e55403086458164940e07001a6210000e5000c100003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 993490323 1250 993489073 993489083
    0x61d180d0e0d12031a0405091e011b0207030501060b09100e01021e0a0c090e03030402120708030304060f1508190204060e1006021605030712020102010e12030121120813 74
    0x141c2d0f580300000400900d2200407414404160300e0744851542054403c140c0074041010291560901010501f0031204c0c40c0c200c0c0030707030540d03880011100bc4804618488e117081016405005107603d18113120307080d1280ca030070200a80c00108280205541c502e280d448600d00036007070241d0f140c68904010f0f41030400143c052551403540300c6c2c08a02e80200414641d45a0b482a00002c03c05510b070229502125a41104e44c51f050b80100089005844d00140354400c1d4092041187c09a9842d01940f0f030542d0000e56040b07500c0c64940c0d4501038612194004c80d11204210804000014640303a000303136036800003000c60307c5015030f45182c5e6829521103404c42c4014065904810300142000e21650280c0c040c2442000c0040c05000380f100004c00301c1420310400c6400003030041000500b090b61002c2580c010344c0b4100e040d0341d81c3d0000f03002800c1c81840050b210403010440c1948942c0742c0a02078060342c500100100c01d18140c602e1101c0003070200f004408458656140c46017140e5168800f00d07040304074809000e03003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 993491573 1250 993490323 993490343
    0x80d0905031215030d0822081308010e0d090e040b0423010c030b01050a0c06020a110a111c0c0e0c070209090604020a05040c080f130c1e0e0f1303030b04061d180d0e0d 73
    0x1802e130f2b00c15001059001c1c0740038200d59800f0040e090890741e0401d40c1c025040404040d0780800c020070201700b4860342260055500044200c903070079624085440c4001281c2091351901c0801d02c0c143e400d4130600c1c01038902030030540c1c501a212080140700c0c20702414001c00180e03000c0b403005d190074850b82703000129801c102c2c01c440148840341130410002522652040c4100a105e540c0e20058841903003083c002d662011004c0391441c200b008211804100614100300c40b4000d00c8200d01580e03416200070b020310850400345c080f9050074010b01545640c0740e040540154182030074508000c0d0310032a40381e0300c242c2940344000d2a07110070701030081070300100ca40681031403800c0b400450185804580c80c44004202e0580080840d03451000e00c1e8049402ca561211000c003850010303007203103100c2001403420f0340700b442c00042c2d150404000070100c45554100103d503405420054000c0203a41d4103003a0071405200c0369048500910360110303610784034100c0200800543c0c0c02000d403142c44100b00c0c0c0f4403155004180c0b03c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 993492823 1250 993491573 993491579
    0xa27050105090f1603030f020c0604090f14100911041203020607020f07030b040201051309050a090b0901060f060f03140c03071b080d0905031215030d08220813 70
    0xe01074034064441103054014496007401004000500e44402d0a41407216846285552026100b090000ca000801d6015020000001d03548500080001d00900000001c1100218a0385c10403150680c0000e01400c10420030703c1007402c44050701404440665802080c094085200740c446402a40e001600d07207420500140300309034010900742e1058000f6804c90b9550b07190003802d240c0d980464403026101200b0480842d015500c26001003000a071841c4414505a0796048800110780d802c841090700542d40f0780107402007040c0701400e160003550942c000d1141900300080c4540c800080e1050000303002c00000022082d07030080e00309610500742c60140f21018580300f81084110303403080324101d00141c0b41c07414840e0082d6130900380307400070f0fa0000c6405040041a41000c0003c05070104182d80b03e1105001180400410741c3c1c00304d2240c0640803010802c4135101050514100700c10750407005000c25401000218010166550080c07c03c40c54a09850911410005c14a110301072604249442c1102d000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 993494073 1250 993492823 993492833
    0x90809090c04080d0e130b04020933040510030c0c05061303120c2717071a280e18010806090c010c020402070602040e0f0402040c08010602060a27 64
    0x50411a4000d8042d500903141c03d0404585205800b10596030009209034483c0789441c3ca9030047c0c80d007902c050001843e240f01240043d0640540366590b54212901021038036280050059000c0441d4200c0c00c440e0030a030800e000100b0307403c10403002c1d4081656509804035090b1155000200341508007055403820b0903c811010380300100c400080c0c3c0824488250900028924072602805a600d0b0b03a580da000414012400c4801860715010358481e82c8184010070b01070b202e400c0d20050910120020002946040814001d034490784407402c0303401006000010f21207452034421066903400ea103440180d00d0900c9000e4030800c001c0368146401c200300d43c5450300a83c2c003003403026040e00d5280003114619500c404085540f040013183c07850029149900b150010b05141d005499103030711600d005420b20f5241e5807150107a40d022521034200c0c05c5103106110660030b0a209a4240c2c0c00b5625003009190f06081c0701a586140290410720314658859803d0084024101441c200e070641c44007048002c0034600300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 993495323 1250 993494073 993494077
    0x20a0806040209011508041709130506040606110a082107031a030c0f240a05130906030b01120c0b030c07060629030a0f050118150b030a090809090c 65
    0x2240580300050020070000100c0000c2c0c40c100e11709959030b00c4283d03a156607510f429003140140e5281540107121048460340d580c1c1c01a985030070780400c000350300e190800800041e2442a4403c20600641a85044540d0004942c0399500c80d0405035580d40c4081940d45008140000c1d07640c291407001c040240800b01d9071603000842c840d403014156000c000400c80405407103c40b110105036008490251500e01d40c200b81c28400065040d401c2c1254850721010f90044c40e0364404802e403400a9000180305108240301c2090b10090800c2c804100113840c1035984500b81e611041c0510b1190700441e210803010811000c94071800791110f0f141e05078803400d0820150030a604102404c580c40c904000001c00c0034120360491488583c803127204980d9a00309520501840d03070010f8000d01c4c101d61107019440c00001c680c00742a000b032101404600f40c1e41040b4200100702c8000354036007441c030319803600704010703609040043c0e94200d00d1080d40001c080b646c07071504851500c60300c6001034111407100c0070043c4065203100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 993496573 1250 993495323 993495331
    0x7270207080306040515031f09061a0102070b0403111507021806042a211b12021c1a0d06020315010c1713080f1e070819030309020a0806 60
    0x1800d125546410440148900301c14560307c0d0180d0000b083c45507080c1d44002c1d040810021210001042017040d02c0704000c0e0761030306010070070080d9000c500f03280c6540e040104400600d000030350641004c0c25a0780d6117040d10703201406070380b05003185100105d4500500040300c5c0b02990051810500c9441148200c5d8000e03003c660691003a0310f81040c03d8141100840d800559000c0b074036400c050788014144c15a003e0042840c510059480b16259200c3c5040301e10801d41050700c0e15070420f01320304541c0341c01880d00a1819406021500510944007522036200d89080d00500001009c964009070000c2114002d16030b0100e5980407000c00b80c460140302c1c169006600441a00c48080880740c03081d00103481c075000910009140503011203070309c02c3c1e220b50480031707202411183d40e01d144030590301c507400c3d440c2503054125a20560130038040386c0207190442d0f80d446d8090000e4009401c4407880d01030181e85030300802e01c41d0700c10100080384031030030035220783d00078681d03141d0003005500003685500000307030348241c115 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 993497823 1250 993496573 993496579
    0x120e190501110c1f1e03020409050a020c0a030c050f2a03010b0307120501020d020a05090307090513150b090126030f030a090f02040c0c05010b0604050307270207080306 74
    0x41c0424120000201d81010382d40405080c1c44d00e441400c015801480401065000401240050071140b041d040b000424081c038003960b002da03c49007030041d094111a809441d85e5000380c410881c0441c5100701003001e446031501410f06450f8081e0b9401d1950070400440c001c5001030040c60818441c00202c1880b4108504020226001c07640380c40090600300e500300d520f50340d41039100e440e04102c4400003050030101c0e10710450026091040c90403140c020fa03080342481d280404c2011558581500701082403c0050180c01024001030a00c903032400c4080d030502d10040c02103011507a500241000c5504080700440016011024640e540e180804c494507400c41020039000d4403480140700c160300002a24030760740c038502c2c0c010b01d9500e81d450614014290418106c0342080303603048017000360b0b035140300304044c42c9000d40f02c15035281200c2c0b50440c2115404a03a4511403c810310040c080c42d180041c9031015a0406005c0b03c1d08441c40702d0382c1c0c842c1c1c1521003a0300142e10f400000e034081088500c0300074500944040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 993499073 1250 993497823 993497837
    0x20a21020f010e030f030702030f0307030603021f0f050d091b0509010e0f0601050a110d081504060308220803040303020a03030e01020c0d141605030304030801150c120e190501 77
    0x2a4003403402e0b00c0400c0c0d240f102680c014040780d900102070400550300031801340120381c9403e40502c06000c058000321049004245e4601d010015030a0100f4040303040c410b07a2100c5400164000c40280040500c40c000030b040040228441200380241d61210f05140d0b0445492590a0501440340100307011034000c0501905218000003414000c2c0150f0718002c02c48030444050643c0c170103004441c244c014010800800540c0603034500088000e004810413000140e6680c007407403410291002e91180d4004005028a24080c81000400d0f502c02c103440f24400c41c1c007901c802058550340307501d501e00c01541201e091400000bc00104041e00068800d000300e110b030324140088684421140c1c200c2c01030748178a8403941c10461290b4102849078840d808941c2d01c2c911a64241a0400200000d031502c80c0c90880d00da41c40001400103054225100c2e83c01800f02c81181c0000e50200400144482060f150050510b0f50058020305e580380110901a10210301405d2000a40040950b80c14049040d114232408100c2e5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 993500323 1250 993499073 993499093
    0xf05010311180106090317040b0315192106022818030b0402041104090c200a080d0515102006160e19031212060e010303030c020a2102 59
    0x100e40342d00c9040f0303009030700c1d0b0440061a58480c4540c0b40440c868026020104010110741881c0c010040c5001c0d4076401010380c404904203060164003284402060109691140c0400040315221100c00c541d0000d03906402c00c101c0340d864018013034084d1720b94614a04181c013210040301c1d424440058800a40c982d26581039042585030b43c512058180000360140b00c40c0b100040160078a60800400003010003005072809940d20254012216445080c000260225041c1461404051003504015900001070980003405a03500042840352442030710b0019152400544c001c103002041ca1034240b0054444040c00300803103001000011096000e2600404a04030400313910400070703901e4416140c001c400410400c2c00c107019030b011410740b01100d90090030035210309400052400315100551160080c080b9208409001a1501d5171200b041c40b178061900d20104100500303e00420304684c3c25040002d00c56034010030803401c01080000107031410700414211a440035403050501031b030b1039107a42981c81e854a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 993501573 1250 993500323 993500359
    0x607030507060f0b1c0f20090a060b070f0f05070f08010e0106080c010e030f0d230c031b0a06110a091403030a2d200a0b010303030209040f05010311 65
    0x301c4411490741144404039942d40c600c00b1742e217041c081c841c0501c1025a03440f030320385c3d640d803500403980c440b8003200b8040c14010b4022307061a00c031054104007013070b40c2800b0071402c1c0810100b490250740b8002d411a9a4203080c1000d00902d52000a0702c2904901680c210907120344c0040c3c24600d80344254601756281202c58655084188590420340e21200003904144c45007400449142c544c000d2100d506002c0c00c1c2100f489040d0820204116800d6a103072104400078044441c3d90380100c200c1603903e43c41003000340008805011084414950000301c0040400c5014103070103282c070350342c1407004181034a0300304c4c24000140000042e040b040710b0750365102803594580380d54a070004040300c0403075010382c024071004000d64003500c019a9116035000852074250403490746200384120790040507020900b1800b1514090003440910001c0b40311400051051000c1c9a40d05601c0c400305200240030541c2c0800c00701c0444c0d4840e0020b010108000005100b69616070810700415102481501d101d4544e0000030b000d652 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 993502823 1250 993501573 993501581
    0x6060d0c0519170a0b0307090609050412080907050607061806090203011118100c1a061c02091f0503010204091a1512130c030506040210090b09060c0a020607030507060f 74
    0x843c180403070b0300c0d01d81c030381c000d24202030800031054950501603208045450b400d14440c1c030006000e860004130f03450806003021404d09441c010a00c041140130402c00402d583e0000720481101c0301541c0d410395030590303030401000802100c070780c800b102104c01d01810148481a0405400240210000c100e168040d48d0b2800c1c0c24850302c41303800f4450032400003084080c5804100410317111401e04015190380c3d1a0307a10a04030002a02014902030140401d0005608219441d0040b250258052610907a403940005600602c01405400388a241c14000125200c0000b0f14a0040002400940d2101d46407a0580054514400380180c401c0040c12001402e29140f0000d0103c4880b079501c6918024404441100f506c400030018402c03c1d07010100100046c520681c00002140a08040d00d4541400d104014142c0c004225070010851014000e002e44800c50301200c5000e002203c0e184d54500c0c400e03c0c00c80c10081d0090b4041d500c40c1010070543c05160300310008201042c400c850400c25840c40c200144101c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 993504073 1250 993502823 993502847
    0x30115081e031c02090a030c380f090109170124050114210103080a022515020c031605120d02030d1107050703050d030b0904020906010806060d0c0519 66
    0x400d00f0342c041d1201100c2160300070003110102803c01960141c1780e071190800303164542d12011903000954042c00190088500840c2c0041445206041c01407035499485c5060280600d00b0380342c0d01e40040c58900982c081e0991a00a05145c5030050540c0c806008003070082c18485021608018032214001c41912903551300c0e400e40743c050b12540c0c1d08208800034680d035608000d03504c3c048003609916944561f00c0303848506008500c501950b07076540c061000d00174108054180090181901c0190500340720301c0095a8400365070f0101c41d00700011701039110407442c10040c030544a426015440e070001c4503520380011202940c0b800e99034010380d5016002030703e42e622250010600160401c0c4060702000500f90000011680555000750070801907444440c2840f40720391045469500c248440280c035900750044114100301218881c1e01c07490650049a042d4500800003030411150307600040d0107a503124282c0340004615141040012008203002d03003e0b0f072080100c41070301c1840c0d4010b110150300c0b4050000710 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 993505323 1250 993504073 993504097
    0xc02132f0d290108190903140c100b01030207032003070213050a060f030b0103030e0f13060618030503030a0e150403020c0901050603090309102025050a0b09030115081e03 75
    0x1110038606040f1700502d1134000480410281083c03002d01d403400c40010f0a50345007248003411030340251003060012143c06101da241894010f1084002080d0070148070a000080c1682141c02c44505010903401d512403000000d60002100501c3c3d1007001e86544141e124000c480010007140d034940710303d519209124800103258010040040c030000f44196a1045e8210024011241d00c0411070002181507220003906106d10f43da681d41080400d034482c40c01c1002e0905070342400c03622401c54655036200e100c010300c000f440d551640a4201d5686080180680030044c072801000c0300d04003841d00a40300c1d035440320100c1c0b2902800e40041034514040086a004511600055103014581c40a00520700b04034014502803003414441e81c502d400c030041100d6103a000080107440c0311605032a885245c4070380c1d1226826403620b201d00034803903519205140c506a4001c00845520781000c080000d015003c01010800c590071080300000745c025001420141940c450708564200f10b40101d040c1c0d580f80903107115418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 993506573 1250 993505323 993505351
    0xa06030b1005070506130f080304030305040c060516080f0f0310080606040b010504030b060310020d0e070b041419030f141c0801290a0c02132f0d290108 67
    0x10716040d02204942d501f485100c104501c000280c4410034036130000c440940c0402d0322035080008001507800b4201c040c00040c100542842c4281c100040ca941c0d0842000384001f07400030b021044c500240040c0c50080054804840d501d141800160140c001c9070b105049861240704081400c0340380c6402400605030060392243e042900c2c6803111008458003a000e03075018001e418205024070310900050100006515001c62010042840340d440e01106902c1803084000511080c8601d01e12034800280c1080100c880c0c6101d2040070400400c1c2c41c81c0741d4030060010303102c02d41d20b0040003d2000280510306c043c1c0b06880c0184240b603800c0d21440b0680e2085d07c001881c0c4801800226000d0000c0b1008090348050390507040190100d00025510040704103000c101484580c904620384000c42c1000d81125640030b12901c0058003140c0c5041c03802078100e100001e58524840740c00700c1500140c41c01000c045006203c40c1184516954450030000000680400b00580c032100030350241c2e0109000f10700302d0607060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 993507823 1250 993506573 993506581
    0x120206071403040f1103060f060307050910090e0f0304060f0e220e0f0304120c12050705130b030a0f02040605030a02090406090602070c06120606030c0f030b0109050a06030b1005070506 81
    0x61180110114101c1e80c011740c0e050011007070745040010600c80c00c1c086442030740608210040628180d0340e640440d11030540401081203426400145004486030100c02141944026511034184011146400060300c0003080c0001c0142d8405841d60035135100b919825501204002400403031a501c00b000d2150500c90490310303a5820841e880414105140c0094811803032a03510340c0c60541e032141d404032541d01c1080c3e11580901081c3e511101c0149034001603108048041d07036520780c8403960341c42200c0c4200c0124a1480c14a616904643ca00010007801e940c0000c80b10700e0002e02c0500c0c081411790241c0d140103402b051906000406405080e0000c12082056440342e44043c05015a80011600c86401780900c00004444100d4640680540d465955a00c0754485c3d4103000c444c007a522000030141000b00010034a900500000e0214640d45000300700c6910420050710860151b41c00150009040100090041c4e03040c1c1c814440800b0403a0014000107050340c1c11030319070007401e201500d02e030001c0d4045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 993509073 1250 993507823 993507833
    0x30f0105092e05180103051902010f03050c040902040608190b01020c060702040f0908030708070f0e2103031603110304050d12090206030c030a051e191812020607140304 74
    0x300801c40042d840c607440d030355103030700103e8002288440c1c180d491207140801401000300c184050f2061100d01c4005451600885d000202242c45005030311040c03540e40d50101d00401c600401b00c034003400a03224255030f155034501e401440300c00f04031101e100a24111002400800c41c41c0600340c6036042c160300401c00e00802800b001403070350050300100c0e4001c0d910400c02c510354195006a56040c0e014907006910ad280c4905e028015400c002c0801082020b4030056140040d04a48642c02e000010b640302480002003ca4544900c0d180b20325034000ea01c000300401ca40c0200c16941d0505088007a41e0500c1143c850f4280c200840c0415100280709030400941d9801c0d2902c03801c0c0341010261515004100c243e1950041025903001350740c91504400e0001c00c10424117030b180541500219007032078078035011032030300c3c4511074460000c1e03d01031050b2088026034800105030340100244981103204070900c0c03000382c40c062031030842c403005a6016010b100c000694032802088100700b40100c8100031841c0d55030b1a610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 993510323 1250 993509073 993509131
    0xc020f031e0c1b0306070302040f0308250b091e060a050709090e070303090e060a03021002101e110307050405010f050d05040c050a120f110d0f08030f010509 69
    0x142481071414050321030a0703603081180304a4500341001007294038100710b0a02d42085002091074040c1070040104001086002c50b43c0b1049a82001c500c1e910303052407408020490315503800900718540ca545000c018004202099801858240120f0f0800b01c4105804034912a015003085110741100d0300042180310300340c2109a0003089881d00c009803c1e103412031402201d428862000e00381e404064180201900b10400303801501000f100006e0a01e019000150400054003000b4054041c2e031890301c1c4564020008410b01c0d81740d40109002c40c0000b0480c0840c01e240b44071070301414030305040c681c00d03200080c0f804481c000c00d01070303480c02d26040c00c0c44015200f05841c01c8d0303402c04020041161030181c103180e00c07503503004c1c1d0721600b08920b11600e0181041003410007a008400742e00300081c020000201d0141a101c100c6502a294144600d0401c0c00100ca042c000000501103500058900e420841c01000461041161000e02c002c113076268402e02030350150448e05611442140700d1006104141042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 993511573 1250 993510323 993510367
    0x60301031106041206020a020c040605061608090616060c030c171e010e040203070609050307060c02060910201f050a0b060a0c0b0604020a0c02060307030207120507060c020f03 77
    0xb00040c982a9520380005075940c3e001c0094801c640c0c00305c3d4100c103681d410b02051210890884080c4403203801c0c080090180e1069035004d07440200e1440e12802001548001d076144288010100b07a1501c1001c1c176940084c42c00c0d5241190f003a440c091000c40d0450182c4104401d4a0780ea40d64080358072030003111614410800b422624844030000c248210f8080120500350190030850007001641c2028410300d4506101c03074200c401401840300c1e0510482d100020703000119030381031030105462002c0303001090300352081140b0b840c0c22009400201041a40090000722072030380718102d03800780341041200075031180703501a110f0070380c107846031841401e00449801c51508000d4032000020380c08034200c0042c44941c0f02030309030300205844241001c180024901010340c0401d00b0746040d46440d40c401e00c000c02120105400902c118004000b0a8000d4802d0781610242039100c1c031040c0c1852a20800980300b50421101112500d003030820100c0c2052002c078a188150b242c0000030f5040c00887c1440e00c0c1d003410006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 993512823 1250 993511573 993511579
    0x3070f0b040b031302091e1303050d09060b0301020d020715020c0d08330103060806090316031407061424010e01170a050709050607080406030b13050a140a09020603010311 75
    0x1c84c0c44c13405a0b44041809000341444582d900c0e00321810ba81e1406141d00050030f46c10039056075009100401d40040c11210801145040080c44100518001009200c0102c00b140c01d9807010035013004541c195801040c8540c05809982003100500400b071044c0d108828200205401c4422290050f40c01210900d410140d80020000000480c3c190342e00045c070600b0341024412030440040446503010301c05d031006095500c0140505240034800c071070303491064110702011890340160704018588202c0d00900c0d40000003c105940d007026090034000390004d065084081c201607401724070144444400c001d50f80c5400500d51994807036000c015202c405074010602d050021003003503001c2c2814042e0455104000c003060001e10740c10003203c02401014032b078101c1e0b130055008110381e50104040c0016582211810726012030020711350004035520100c0342d101c5451281c00c0200307021140b0869084042d401c42601140340d00c13030b500d02040380280c0b290b0400294000804000500105103103208480b01e0701d50207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 993514073 1250 993512823 993512851
    0x41d1e0316050d022a010e2e0f09030b0408090a0e10080c06090315190905010219180b0f120411120706090b07020609100206100e060a0b0c010912030b03070f0b040b03 73
    0x19241c0896103490071080f2310907610307a10000d0845150401c115030030003041c41c9000d0782454103650303c04d0301988000d0005003120b40081041c28140ea100e0740480701070a04840381d20750f5402e00f200d292603100c40b14000c0b0340712401481f42045242c00e0400c199800000010b00812000c03500304260781c0340940c05000071900305106461036649540601036005040c1c401c8000581e0f5000d0061040175025240540780e041248444040312485002c41c0c18006075910f060a080c0c0e540b120701c81a401c02d100d01e00c60f0310b0341040490200420300205100301202e4542c103442c4114006c1d2900c1c0c0c1240c03604400d0145d000800e180d00802e02c110300d408805080400c0c809070420346000c00da240015418125101100c00503807080c820003802000109152000300b080d01c056294034200030f0002014017001c0e00401ca11300202140041500000350807802d04150031101d001c0846110f00401405008800c552901070701c201c060000f0352074903802d0524115402e4410140c141030800314031403102d900c094400c410403100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 993515323 1250 993514073 993514099
    0x40e060409170403021e0303030408030c190e1201112530020c0d030f0201140c030108010b090112020907090e0c0702041d1e0316050d022a010e 63
    0x19840b42919108408400c5034440d442c40c0b04109550a0125004658402d1071403201411f8500005076600326034003078102a169035400d80c20703c19a0280b42621f00140d030300300010384955030f0880d000c2124903005450a083e0300310400d9660f0f080c0c45014094150506040040482c40032090300300041070034019001080c444e14545407005103403501400390600c8601410f40c0204003140854103a082d03200c5002405050751000d000500f280f81e1800d000d024402c01e203601c0c41805100b94460103030304c601004802c60905000c003c0b560f86800074010741079950b1071300390203004514001c413865040b502c0300c1c0071500d4109008e03824044820006000207050042c5000c001c44d0a8082002151288440e0707508561104443d00400064410002c4410145500d0404900c0040c5000c03401258054400e02c1010328030f90251411882e40c1702e0b206d02440310b128001e02c1c040c108480400c40010b031101c160300311660310642820341c0c48600c07404a040c20585032107210204565004e101c2c0c002c0c40440c000c010703504644c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 993516573 1250 993515323 993515333
    0x61305100513080607031b02030702011b02030a0b0a0c0e1f050906030a0b04231f08012a050901080f07020a08360609061b010606021b1005040e060409 66
    0x100d5074003c201c43e90084e0301000a091303410b00c1850030404995015841000c11110065100d108450001e410003128100303c1d20a0711480d480c00400650203400c49102c17003a24280700e4284201540c0414003541000c183c104114420030966540c18030041c0940e45402500c0040600b04c1d010300035603000e20030305201640031a56a00060f5101d126500004030b00d40e07814408001c1101d10a080e01c0e250396109108103d10480b440e08070580c072201c0540788007009080403040c0220714903550b20001580d802e00140c61003a05030104c2441c9450f050300c4802500840c0c617401074490b0b02030326030154000340b1030303000103440c10505d00d90315a003081950043c0c03a00c83c070640d05c1e0f034403c652001c0c100502789041c0c60b551102c08540e0200b80d510008a12019900e001c48070300004004d8456030400612072100454254060284c03103903020070b44c0080c40001c02c421591000c01030b444800743c2464541c9941c1c828429980d504041a014894100c41c0d9202c1e4039007803c040381d03100c121304003400c600c1c1c00c04c0d51540d094002803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 993517823 1250 993516573 993516607
    0x40b0907090303181818080f131205121b0a0b0106110627010209040e01140a0c020a0b0c16110a050109080a0f140105010b030103110613051005 63
    0x10081d0360707054180c500b1030901800c0301440c0c94038007081341c0301d1040c1040015800504800c40c1d20140074003258800e03808801018560a115016021500c0010764204170980180100301c0f41081e240003003040780d5030303852210441440c403001a0081d002100d03541c41700c050940c02014041904102646600303101e2044628000440b0340c112080321410340182300040d0051402e01c3c40038984401040c05152105c1c01e0452600100006d08103580e00c1300c0c00750752440081d015903040743c00c0130f442001684440c40800340030b4044071030810f40d4002e035040468000a01405107080c2c900142e0014001005140c0d954400030381d0003440c00b10714050034080c991a4424400d404100d66008094000c0144080410420310420941c011414050040c4042124110201e0026156600f228204451070110b0500000c020707480105002c4552828001084a03080b0501460617640212019400c5405007824080d00e0b115808006c1e200c40c0b5450002c01013071030403e40310030495090349062130034078481a01e020090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 993519073 1250 993517823 993517831
    0x70c080d020109140c0d03230c070f0f1202090a0204051c020405100e1603060b12010e01060309023a2303071e0303021b060403030608030414010509040b09 68
    0x60751581003c4003403281030b490b8080040040c0014142c03810300040001d0040d8101840201030003072401402e001488980e40c1d55490660459449641d00101c0d6800b98803040c01d801500ca182c1d005d20004101a144800460700b51121500600110502ca03001c0190000c3c00400008150380c08020100356525652201e0007210700616444c06040c0780e0703104004c15a10010300701008640c60784c408002071b072584581103401041103680001c440d00300c02000c0300908160380141100d10030000d21402100414907546049900e11814000c0e1642c071040120300355400c1000c003035031028040200900c40340d002d41103001810361220703002c0d4504200160108495030071820903502003800612912101c0009d40d55640e032a00000040c501e4100c1a680c0c03e00e02d440e02081d9808030250380f440b500101802079049403100e4060040720740140041000c025520304c01101e04600180c10900000382c2c5400000c02c0d201500d20180c469452903201c10011500c03a0800040306030f002e9255074501c03c290b04c0da442c1441c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 993520323 1250 993519073 993519077
    0x90524091b0f041103091b01020c010305130b33101107090f0b031b0a0e07050c10020c0c0103060506040b1e04260705011b081b01020d0f0b06040506070c080d 69
    0xc3e0b1800b1b400c1d01d81821911402820070a801c0c1d241082c0aa0f40420209907100007405e0000b419160551824220403141100512858141043c803403840c0000d410152030085000e600c1601c0000c411041901d450301540c0c0c150009840a41156500e0050549a540c50381b4202110a604c1e520a441c2099884801610011903903d000d83c2066080030f214405100c1d41c9040d6070906c81c110f400101e10402c40d5886010256601c04001c55009441002141d40b640461401c80300004408061900294009010701c2d00b140700c0c001e410121940240240021100001e03c05402d0030328110304504168400004070061020740501c211804803410098805010600c0c519160001850301c940510000ca0f22840340710360200ba810009030ba448580d0b004128401011500d00301403601d010b1800d80100c03140d60b50720342005001c0503884441580070782295801d581042c0a603101c04540e05044550125803190005010803051003607040441c001c00383c0c1441108141031a0395181d85290424500401c0100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 993521573 1250 993520323 993520327
    0x40324091506050a0302090414030c060903040608011e030b090712051510080705040b010519112103150612010303031a310f090524091b0f0411 63
    0x40304041c244240c2001e0a01912160381c40c50070343d000201821801030006103800124180700c01810780c04d0059480f420540811910b0a042440c1019220781050082c3e0b80001c503000000111010081d03e4194110201140f000000381541c80c0e100e00031100801a202d24814403100003960b0030040b10b001d0286000d080075010340c00803201031080c0c024001c1d01d01a1003421625050180708000318141d41100c504590028020b034441005031500c0c00341410100010f00e0300700d0b0240e075541c0c00c4185080315541d4078059800c003e4500c06540030b00c01c2043c01074003011764140f000418041d11035145007180503004000c9030803c00c012040010b41c8000742c1088002984409616a4483c84942013483c6403500322404414111649280c1e0404007100351500a9660b07010700b00080010294092070700001114810b112a25090500990300c003040051102c401595070b40400094001a600b1406654110050511000e218800100b00d55214240d80d50010f05802c190b060740d80c42d4801c4031802440c070b02a060f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 993522823 1250 993521573 993521603
    0x13061d030d1d1f2c03180102010e0c19080a15053d150309021905150a02070b1b0c030c06090616060f0e0d110304032409 53
    0x118210348058000c0503910000c01070305009218000c0c5607403083d801d1400106407001c0c42e01c4904440d0a1341d0000d21101d103440d2020084203020000b4a8910000f03600100c0070b41b04900124220b40030f4810301c689030740100300c1852503031506401c3c20011080e050301485040343c494010500340f082188003150840b4020401c010349003900e001389584942d01c8110003100d548190060000840751750a010325514510342c1c0c0d0000100740e003000e00054003602c103100c94070024201025006140022059104804d0600c0340d156807002001c8050540c4c401800034400c04886461000098200784001000d6002d0744a02240c00b082c128060f00456100c0d0f030001c0041c50401004608119500301c0c40b9000c0d403c480a0050680c4034841142d00c5c50310141c0e00c075070740c42c211170007050710440a21700c00030310040c02c007902c407400c42500f500311032440a420001d070b0f0060f0104090a80b5500d00030089480d40d50020f110400100e03500204440c0545070240312062104824040601100c0c1c10360411201e6003510803000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 993524073 1250 993522823 993522851
    0x610050306130209150103180b09010f0213060f05070501090c1a030403080f090a0f20030d020615060c010504051614010206010b070602090907050309120313061d030d 73
    0xa10b810584110310050700044940102d06001c1004164100d590504840b1115503480307503000138220080035020b03c400982928292914a90030307a00e582e10381d800c0032950307560a4464400c4942d511890000d411111f490618141e500d10b104030048424010144240408100300f8052521620711403001600490309101e003d00d502d81241c1e0b03040215010034030810002a070410f900c0c80e0030002080b00b10a55a68036019a0318208100c28000c01841c02c91806e0380c10402d0021040c40c2003904084a000c02070441803c3c15621448002d0000c0180d020401080846640c60150400c02d40702030f101d580380c00c408400e2942580c005650456159224442e074a502d00e01242114000d4108400701c041d8140b0001d0000f581c50a06005070754078004001401c40030045507904481c090324000d07142c1d0030a4a401b5801030807581049134842154090340c01c00260018403541100c0c030800309481c000780d405c406074440d84000e040c1d20075042d00b10443c4a01c00100d00300200003420101800f80d102240685d011644 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 993525179 1106 993524073 993524083
    0x3090a02091023030f19030503130b010b0901020c03030310060e0d05011104031e0807060e070801050c18030c010203032802040609051018090f090506100503 69
    0x1100b0301c0303072482048000001c03089007605c8900520b103c041d41c07540c0c1c0d840460500050308031106000a800343c1c0285811901c2009005403d45c46642c079444446402c0c6c000c40500c01c804aa11103a45d130341001004031140d02034000c0c5086041100701c5c0c0c000005c81d4042c850034070204805218580d20340708802210346070818024132400c001c4043c41c48040c0d10034001503038010003503024598110002c51040d0891680300008514240460700c4550040040c000030580e0390141040010380d21009002e072038092440c00d541c03a0781d070740849030340d140801c5040520305000e40c00c8091002e05a82c0c0101c140d81d40300d042e40340c6603c0000c5081000341e0003074a600600c1109980301107800b148150380301c0b005100382c5000343c5e008207035100b4103030095400d8111f000c80038404280305079050040301026000321410812900d40400c1c007a40d1965114103088046981e82100211258204a00d20701000 = true := by decide +kernel

theorem cover : BRFrame.Cov 993345323 993525179 := by
  have h0 := BRFrame.cov_init 993345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 993345323 ≤ n) (h2 : n < 993525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
