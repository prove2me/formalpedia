-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0375
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:29:28.517992+00:00
-- url     : https://prove2.me/submissions/160cab1b-1159-4de5-87ce-aab12fe99022

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 67266189 ≤ n < 67446045 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 67267439 1250 67266189 67266193
    0xc030f03070323090c010315120b040317010509070c031704260310050d050f030403030c0605010602010e101d0f070602010c0903050a0f06090f0b0403030608121902031902 75
    0xa0040a030f588082101214246410414400b8800052800306903410111030a00c3c01044801c40616005c088090551041407039030b0125003030509009402076514042d0384280d80303090054000f944102d0304540207000d0554800844004a50840e0194081f00b9545120f410103903521440341388105401141190250750381041c0b003c10844203400301d00b65440e1008283c54040c25420242104842e520240c002c56005101c40d869050070f00c40100011140c8000c20b0b0201d0781d07907984070701d402030184c0090034089a10034200340c00410102e006000703254404265100521109000c000440c000c1c14681c0700ca2000410b041d04043d00c0c07002c050054500300261000281141031404000908441c00300380002c0070001c10810034030000300041039004656400440500c1030803610700306400280400c01008204101003100d04003040140c0c021188928042e807000c0082c1a5039680309903d49041c00c500c01540710040001c410345010b03d0714200a01c000c0d61044904181c0c0070100031911944d4094104c01603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 67268689 1250 67267439 67267451
    0xc130b0d030f0305070302120609040503040b040b040f0504050f040201030b0a0504020d050412030603030206130309050409030e03010b1903230d090306060b210a1b090501020615090c0c030f030703 86
    0x2d0b40d014021950814820300d0118601501c1c880340f140c0c1c4000140c000c92040e46c005011800f44030003041a82c021b0213000c440d8580d50b66448030703032540c00d6010744101c0c1c0944c5000803000440e840c1038402e03d480703034420000c0a69665200d1b80110b0040585801e0603900c19000c010104403503c4900c0039100100100c5000915402c290504150314024607a00808042c1000c03818400030b640458159001150040303008071840041c40e00744e80010b160f410054103e458044c509050592043d101400c4c4c030010b0f0000c110725504107040c49040c04849802c80d03600180070740100001111941801007070302c060b403c8581d1909281c040c3e1414203200350b5400b00083c0c84900140305001c014800d040041100f002e40900d400031740142200701c100301d8843c1044940070100010807401403a009030301d110600764805450345030034810207001c0d030100f4080c660040c1308040005640498219003c060300000400c58421595014490000ca5000a40c80c0e0f646000a01c2450007102000303010f540580c285450110780 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 67269939 1250 67268689 67268717
    0x3010803070c080109050a03080c0c1506270619030c0b1c0e060f04110a06020303070215010b16021309050307120f12150e0c18060a020c130b0d03 64
    0xb290032036080342181c2d034541509100000ca0001c1d84814055060070486155a00c0e103171009800e0040001040d001d000c0c01001c003d041030443d00070340c4240300454680c058644010740381000c4103800800401d1034080c60780071424601e822194080503100e4082c0300d0211584070783d216220007041d94031a00c0d40e008041240c43e8442c0948215071111000e1050410220352500c2c401551048050300d1038a006181c0030100c1c00f8840f080d100d00d01d407c040584900d598a82d501d43c02580c2e0341c01103811034018010001c070849076a0707402e04454125100100190b06102a0480c00500141c50b4141242e00c5a0940e0400400540501540e1121400790010f03685840c9036042016105aa858280e81000b00a8840c3ca234144d030400818083c1c3d110880e00000c0c052242a46003010082a41017003003014491030820802613000710081c280d070040380804d1f41405c0d60207001e0105a01554001e040580c0040c03890071010304041e030108505030070500c0085035501002001c900b001100c0e40042d40005d0b1483d14580c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 67271189 1250 67269939 67269953
    0x606040f2402061006031a091602010612050c04020318070303020c03010b18130302031b0303090708030405090403030e010b0619080708100314030702030d020f1006060e010509150301080307 83
    0x299100c00740054082880d0009584c11440c2e80c0c0c0c0150701c2416541d101d01122607001d02ca00041d10b0b000500070b800141000400001140160791800c00198285800400d1032030a0410342d11041d540003000f422001d00907401c00020750030003030114041f4035800820141f44001040b0803001140a07030040c146628106c2d0a042c00d41c1c40c1100c203980201d9a203004914000000f104207507211407a00f90151203031f05649412421842603c05651010740407115555442c0408801035005070034241c1104c24450751902025203d0180e03104242d40a0003c07800280841d000c0c0e007094440c0319580c000081d8809101c400035046400156901a0758014040c01000f401d403c1003030907410007010b007012015131904c05c0810706410100c2c00000d207102001504014029000c00a07070b1005075005050310050002420020360350680284052690b101d100801c2e031200040d48900d03016225250784602c000280d540055a182c0c0c40f80c00b141c3c0e0403080511925040200e4000598041c0031000c001c0c44c1d84041d44e0078800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 67272439 1250 67271189 67271249
    0x7030b04060c14031f091a04050603071208070314030a1a030f120a0c0b0117060a09020109060f0e09040b070e0429010504030b0405100509030316080606040f 69
    0xb0301800403002505005102500c1926072000c6542021081c5158102100404103841e41c080001c0702e040903080c030340c40d44815007200c0c1c403d10240d60030045546d8000800d541c40f422032280e42040c1c10709200141c045032a0000400b241802401d00c207042944c9041c180e00d0f04d81c000c4a10208040d500d003100078543e0300c2000e000602c904200c00420f00f0056040d921925804001075100380c0001c006001200740e40a541c4403580607401114180b11076039034190b0040f04d41044c20824a5500074a400540d03209118450a4441901070b0f680c60050781c104071040d01c18070850304509061102c1e4003000c030059620103c29922551195040c1100fa003015080a403860342c1002480c0c0c802c2d0306203c01002c68005c21000100d81607020b03044903c5410b81c2e00c00580b9684603a42016088100d01003c000500000054682416818020070080d9903a1100040d490f030109488003170310341d90b8101ca45030080784030340201d42d04114000d040c2c41c60300e1382e0754032156111035840e8010036098803140a80031600030501004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 67273689 1250 67272439 67272461
    0x120c03090506182a01020601051e040b1f0c0b060102070501120506010309050a080403022704020f03010b0604060207150c030f1101090210020c040506040209030703060906090507030b0406 82
    0xa10800040341d6501d41c90b05401040ca260407a416828400d848908006949039040004100b0303400710051103a01140580d0596120f000d807262200026143c1003407002c00c140188607507003d150030038000c0100030140c124202d41c142d2040151000341c4540359a40c248450121168980e02c403216035501d040b5080d25001003899049d5007002c801001a40d030401c4e0341c07000700701c1c01c1c0100248035070340d4000613001000c908070041c04a20a903420102008010401071042e00d0007101d81c0c0207940c148010354091020300341e020b00607403a88003000c140103040680100d0f40c0c00d00e006001081900040000c07a00d140c03c581c3c449001680011800c2010144414404004e0a2030340750044284040d0388015000c041490031800801000048800280c0c0007944041350403036006101009020345600005e554038100c0d290f56200358501000701d80540307054821106a103034003801a1890918580380c2400901d410101601d0407511004d00d8000540c041c03060031b000c3c505c240d1080d1842c0c1080c0c1000740c125241c40d003403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 67274939 1250 67273689 67273691
    0x60b040501081b0a0f060c1a0403090b03100513060905010503030a020a0f05101104090506100206010b07030c02040603050d080a0b3012041a07082208060106120c03 72
    0x52054200100c0d00d400b034041c0b0b41d400c101601650f000459250341c040d9000c20350344000c01c41d0100d10382d0382c003282e4080d846000b1400840d004600c1606185000010748005012880c40c402c100690502c401c003450303210b98800c00840a02c2d50f00e00120700100245920050000d984441c1409a14502d20030329003d00743c150020340c248010b03008007075656007000201034010304100d0500b8040003002c2081c104954524042070141c42c10600c821401600300780a0340303038041c4c1010f00041c09814142d084458120048d07004200503441c00914069640c8600c901781d00300140b00d04e070540035807107030700460740114401c000600400c203c0b034000800f010406010b461499041c038203030300352540d030740f09010b0491983c416148050120032402c140e42d2031a00c821103489402502c0c50541c04a4420014104441990401e042d61030b030b060529003198070900d03000038035010090204802036056030030500f0152000e07500c05124039440c0c081603480d1102c240e00000c00114040d0848110381c109000d102c60034401418 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 67276189 1250 67274939 67274941
    0x10e1006140402031003140601090b03060708070503130204060e0405070b070f2d120806010302040608130203010b060d05072003070303110910052101080d03020a14030c07060b0405 79
    0x441201039001c400300a920480e0040b001c94038012060610200440d80640140450800b0203030540c1c44450074812800744c5894444000e45031306010840e24492140c6a4071181c455448000540d0580c101504610070790425900c0240142c46600c80d11000c0c050408101900b490545011032030240076800031860f4001c140000310001d0503500c113030038075541d1000c071100d038181c0e6004110304850264840b42400c4600c014428043c0844e070901d180c130300d0038240d847c003040f5540c03000150f0680c0b09512500e00083d014200291203910034103580c55443e0300c020008034281030101c00041694001d146110310465481d020301c52042d81040703200307280810f03c0301d03504540c00759448110344034020040003030300f80f40c0c0360091810040398000484003040402044940c0e20819110024a207400c1600411451280840300340c07801101e0380319160403200528028007103041c0f00c0104074069040341d0552014403150422507c4406c0604001d184a20145200c003a152440e80c01c00e5016200c001d0000d5002d286804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 67277439 1250 67276189 67276199
    0x812010b0408120903150a020a020609010b010f03050903070f051b0109030206070303180b0106020a031107030b0112030302120f0a140c030711030403050f010b10020705031c0e030609010e1006 84
    0x103e99180003803820080f40d0345441d03059020070704181c4c0d14441c800c160403d6034200100d8411030350181c40b9030410340d8210b42c0240c0d0358482d810b08071803180003031a004c64600d54041001a105c0c0e0091a4040b00d00d2051320704190960b40c80131103030007c40c1c400319a5070f0002003052070004407000038100d44e042c0c2483c00d80c07001483c6801090030b07171013100e1000e000c058a50030801008803c01c00440380b42c540c0302519802e80c0d0380d900e5009448030390028003100003035222000b114046100151600c00c5d02d80003a402140e591a18141a480c0f4070000001c81c00c0c1030b000e0040c503c103040d800441520648110444141c035180a1808004491455942040c00c0200c5418060407a80d414146c90b800450f5050020b00710b149401c0d07036881c1d07010365407000f4050700c80d0096120800f0819081880801001e0718200703101945c1010507600d0727071100d0141c6034041d44039461049140304140c51440351450681001152000c2240100b414504100c4458109070344401c0703564000315007008205e50841080070100a464140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 67278689 1250 67277439 67277443
    0x1707020307020a03060c1b0507050301140108060a0203040524040b01060302030708160908010f060918110d1e03020a05060108030a0e0d020f030a060509071410030f0b0d0812010b0408 80
    0x3d0001619480e07861451b03030102405250b00c0e20180c000314800f505d0421061410036a90441d5000303040c0a5420850071401d8003110010150590300d541d0050201c5030345202d0707075070002d40001300169007034490240c0125408190103400c03585042140f02c0c200c200c4c54907080c105100101030344410b0805104100300214194000c4100c0e8002010203000519103030710b4202154a143e040e00462090b5280161480d05640140e00410450304003d070140301703400c00c85182c0640030b050241b000d010703219410b8101c00980742c08948065014414000c007010140c89550104070881017030422005a440040c4640600404100329401405100300951502580101c001c103441120450300303005490b4691641704665645928212452000d42202e803031070142d05000f4043d200a4070118001d010b544808100885514420b48619101600c00c00100f08148001c80c02071500d84041c6200b13960724012104195600d03421800680d00441001d9150390028201a44081060b0f0000d809444108010481d680380 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 67279939 1250 67278689 67278709
    0x203070306170a030809120a03150501020309010507060c0c06020c0604050f0607020c1c0501022703070302010f1209060e0d090e15060a0909020d0c02210301090b01030219170702030702 81
    0x306241c205e0b22500c4502126140405403520790440c1341010415502295066101c00035078154000300ca404256100700684c3c40344680d50703400340091001c000c61804142c1d1900310b41c08141403843d150010751480c0d11508101d800c40004e8040c01d402070001c2c401480410002203c904400c83d01400c128104040080c1d92003540049660140b85510884142031301c0569011803c0354001000795030714000e11000c100700c8018042001031110f52a10b810080742400260341e002c3e81d5060f100e541c034144001c0c074256030002d0744460301c0c5940c039203075854000061150f00450091103105070017043c130b038600e4450260905507190450740903008210b04001250401c0019110685002c0c0c80c0c541c1da541d500c0d60120359801c4903400c8401c040d8000500740400e00520303440074800d070500380e0980c2c225590001c58a1125045034404014414044c00180113120703407a4401d00000d04141801450480311150448440060340c00e221302061524600f4141d6021106c1c400d6407150080c0701452804001d0390000c0c0441e02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 67281189 1250 67279939 67279943
    0x60f0a120201020118050a03180308030105040504050309040c02010b040e0a0506010e0c071208060109060e03060406020a0201060e01090b100206010e040b040201110f0a05210702090403090e01090203070306170a 92
    0xc05100440d055900039400b1038a10f90500125007091541414025a610642501100002c0ca41e602d521480380450006a041d41d40c01f4807903e1445e40384c00200005044042c105480c00e0100b080365001681ea02e04c0703000c049001d40d800120701411000304103c1210120202903c03180c2004002c2c0f80050000b25201d4150780d40c8160305111515a410000720038002c44100501c0451103010300103609800100c018441d150076610a0074603078881500f1101c010840c2c001c0703a01640502c0c04a400102e454000c1c0c40b61100b50300c00080d495543e0060469004002c0e803000c070900f5541c8031010740d40c0c1840d500241400c07050303000501c1e0035451b00070707410781c000e80c0141301400d019250b80104045a10038071201c03141034030040844840002200c660780d200c0c245040111120302c0340800a403640e10030300c440106005d070175100c9181400d419400748041c440005008404010020380b02103503400c2070201c1701c0d002e482800b40060300c914060350007038100d0312240c014081405014101903a222000a001b2450325 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 67282439 1250 67281189 67281209
    0xd080f0603070e130c03020312030604110c0a03080403120c03090c0b0a090603150e0a0b0102010501090b03030d1e020a18060305060a050d02010207091a0103050c0a17090f01090303020909060f0a 85
    0xe81281172103ea40300d180c3c3c200079407501a00b208080551540b101a5004030421501000700e8221207003070701d29510508100c0100b5420000180020078081d0103510f600c0b41c007a0802402145008a42c0401c8503134940201020941e100c80300001c0c0029500c04034050644088260719040c0740c40c030090200d0791a8131501080580300d03a22040407000310350501c0000d0030350500380240c43c145a51120040d00e42c44146500540c60100001141d4031a8050313140d102d41c0c0a40550314048906120344041c10304900f440154402c0c0710358601c0038203503a200814039000b017a41e038480c088421010180100009134060020942818184140c1e03946620f08581100e04c01c503400c16012070b080c40140c2c2006d0300ca902605c3c00910782466018403400b002880946035209a908204954941e01c0d03e08850181214500c001949481030719605030040d9062a003141080c0100e444210550b5089401d45612070402c0300081e0300850f8140040c00d0242890fa00b21b1011961041441100300105031000460b101d040101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 67283689 1250 67282439 67282471
    0xf0405060a050d06060f080901090206030705090a030c06050a020d09050a09020a0c060906020301090b04020f030c03041716061803020a0b0606070b09061501020318041505030d080f0603070e 83
    0x14002c10855511440c824001d0140d2541c07240054090200319905101045540c000502c1480c418464461940e83c0142054250344590404039800c0e005080c0140e04070803000360102c08600315640003030007803d05549842d6218038000c0c0090410010200c48070501043c2c903020311543d5603102c0e0440540d84501c100688074100184102e07541400078501400702803505e500c0100f8025143c00a50588041210501c04c08000d441884124407c4540c41d500c40101807010440c444150401075030041d001e008021030310108402c040c60f8960103410004104000101a00304001e4a03010f101081c04c8403e484c07441c1d050f03c0b91000783d2a1104005c00030012024140052410b50301d1000340d803400740e0843da4103103451402c0c0341c5955441900751140001c3c6082451039000c258800001c4814981d000340f030b0000100421030a2101424034801482c03102502c00f500400e00c0c0c0c500708a443e12245a0361703503c185508011410b0031190341c02070420b6020340c005c84014809440d0b48400107803c02840d203070b0451a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 67284939 1250 67283689 67283707
    0x30f010308092805040e0a0201080103060e0a020a1d01050a03030206040b0403050c10020403020306131703100510020102070b010602072702190c030801122013060801060e0c0f040506 80
    0x21083c24800049214a001e261403038103140c0e6010000d070755080e203080141203c1d501d04280d40e02104140280003d1004c1c006000240180d002400c25810720b20032995260201d500003055440c107a0080b00110040e20001e0920a8025a0080c01414140d42810340c142c2907440003900c40c100144042d021105440100d01051300c60f500300d88480e10f5480644103100d41ca40c1d2040060341c05840141d01c03a1007030502182030344034240340121217507911030b01001d10529840f50708030a58000802c4001a4034104d44002200e844454030015800183d5000680c1d80804c0d10f46140c20000c1038208408551101c0002d101c104490b00740c04a20f940c29422890450721849111406840395660610814600084038105e490304840204e0741d5511036190810242c0c0c0b41c4e071140c0c800c45510b02020f801403449421240d444101c405015034041800303400800c0c1190103805440581e00d460703100207110b83d075035941000f510300b031520a280c014010003411840c100c0107403c004c803a4003450141d54400c040003e80030324 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 67286189 1250 67284939 67284949
    0x30506060f0403060b0f0405010f03050f030a08040212070e130b0901050402060327030703020a0311060c04060f03092f01020307080d0b03030d2316090608180f0601030215030f01030809 81
    0xa0303220f100030000d108662b10354022403440f0307440344000c8030301c0d200d01440481c0d40140403041d610103807550759640071320b50b542d602004400c0e40b06043e4040e03280111500410030080d10f001e100c1c8507052851180c0001d013610720305080131440040400400ba450034051100695130704040326001900e007182058600c10031812075240c1142c3ca071000043d4400094070300209a0007041300c02040b80a51a84854507501150036a00c50100720f811030100c9104100500c40d0303a003d070400c03008442d0300b440c7c001840a101d40d6542108100c000f041c0d0009204920782d040c0329102c0386600e0300d20b0402840079505000309035586010a008100325600c440340c844114468a460410507100f95941400c1e00340085104098114100b80d079007070458030640241030015640c0320304500030584142c1c0c242d54004e074441c50300508540b85c1d10042c04c94400044035042214115a042140c0060001054090021035140d803040000f6400c6940f400140c0c401e09104004100c40000c03202411030341c2001d51143c0d200c40700380000d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 67287439 1250 67286189 67286209
    0x20c010204050301050a0905061806070f1b050705100f0503040803060301090f0311011104060225080304030311010c14030a090501090804030b0601090609080c040e12041203030506060f0403060b 85
    0x64043d172800d010030000c504190000c1c5441c1e030082d419518261a01a00d442c11622100b0703200380241d10031000b20781071a1184006003c06081840c10b0600d1400340750b9880120341002500751035544c80094240007615007080c1d507020310a0a42080303c10440400400b612901000b00060711041020000404a4400307400c806c001d1075000e001c49100c6d0b00c082c40e01a03c001c40b03503000920b15600c1c1c0781050088082d8401200d043d0340703040c1c00900c28400a5043c80f0101d0314030309500c000c078412403400001e13404c50030000741000d10310039120000c410405500c017500b11541c145c00e4408016806010f0010742c2e41200c2100d410102c10000860150303640d060840c0580ac3d400e100030034003580024004240714501c0d20850043c1d0003661070440c65607a501e030444100c1314074040c88240d0703006260100581d01c0c240e802511405600c8080d182e171820458401011038006611001580d442c040d040003c0540c54850103612800c1200da040c109401008019440d00540c04010842592056540c000e80d649100740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 67288689 1250 67287439 67287449
    0x1050d060e10230c03010302011e0c02270901020702060a050711060d0501080d030c05090d031e030e12040b03060906280519051e0607060c0c0312090302070504020c010204 75
    0x24800c6141c3c200240c0459403041d510b5460000c840804103000c0313898202128102c0750140d44446000c080ca180d50004a40301407892014000c40105070030043c0c641c10308410281031840b200d030040c941d4002c504800c1d03070001031010890303034410011080142d0b134a900350754800e01c90307103049912581c983c507020b2041590f45200c50342c029004502489800699000581a1020481a64030500240c401074055903c40054000403440600000c0203505062410b00314140c01b07490490703094083d82402002c4024030b05031000000381c8596086100c860200018600d03203070084940e030b10300380c644030030340c01140070191007039114403d0700e0301007050303036940b0f1102011542940d204000e0342c082c80b186a40311341015104803405810610340609a25400340300040885402411800242c40701c0d442c001060468081003c0c4c3c020014400303400894040c1c4070fa5525007440341c403a041c25000f6420040c24029000f07844170211414050407800096002ca17200341143c905941c0980c40b0b03e2680706941c0a03009903000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 67289939 1250 67288689 67288691
    0xd080a050c0f031804021201031101230a0212040605071209170c0301050105010e03030913090b090d140301061b0204110d051e06060a080a0605090c0c010f020301050d060e10 76
    0x240701c0040310100c01002900e21381c0c003802c94200c01030710034013099015030a80d813103030f14040030010030110740c0d0144240307001c00051400d0502d030440c4040f004180780c0e60340345800400b500411400311450301048100c02201e820b00e1110b04103131421000416a103d10140202418400300c0c006c00c03240c0c041d144100161a0750303079040030070840500b800c560f50241029071601c85c1d82000700004482d402540340c0310b211030780500074601d03007843c0034144101400500c4002c1c24141c2d4890f906400b08502114041c00b4460400142846075250b10009007140d40c145901c4543e10010801000035607001007140b0080a15140c80c4048024140000380003085228000b400c100f000150454618036154883d61007002080b0140c4a00311221405c041b51358811540c00380c01c080c08105084a050150910b01c0e40100034810103d0000c1d00c074030100b1386a00d4169030540c0001c0300801c0030081c200b0203010381c0c118120390035811800c0d58500000a00011007452000d00a155030320000041d6010511401450301d2030204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 67291189 1250 67289939 67289953
    0x1060b070516050406060e0105070f020d0b0103060609020f0d09150c050c0f031312110607030509031c091203050c0607091e030803220b0c0a02010605030c0d080a050c 73
    0x205a602c4041c031500011039101c072541c010a0714a040d00c50002a50281c4d41e8042d030030340d2a20019501503010307070f0b015240c030b80600f10200c3c0141d9071107a1020b1030303034410080c150711945140b80c82c90903941c40c0e8000c0352019005102d100380101f90f02c1c040d50f112404481c03020501081d81d00307140300074030b02e400202404941011402000950040014401c42c4000412201800b1071040310b5a01c90050350b6036503011542048040180e10040b00b18104254020007070540440305460016046a00c00d49003140441c030086540409440c0030f10032000c010081e00d41500c803050050000802c80212401a820010101c203030b10000c1c07510840c262406c0c114004110781e035608140c0006082c09065105604e504014030510007030004103401040101c0340e101054a04544501d1008114003034020b080c4c0310140d1402c482c100100700c800c00361600540341440d4040c0d07140c81001c002401e442068200c0c45c0170390700c00044062107444d514844540c564001d2240c9403251510203044406218009600c5010300c1016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 67292439 1250 67291189 67291193
    0x109050f0c0d0b0d110f09010305150606190c030305060108160f02010b04020409060e2d070509060a090e1b09040c0c1a0106080703050f13020a1214071410050c01060b07 74
    0x200b04d041d0000702221b140c4803200d403070420051400c0c000d00005200d5040f003204e4140c1c00c580b4690503900024000c10702420408084c001028030300081940100181c01f1000190600d138042c410282c11038000e1805800754a81340400d44845045000300c00104219928244401d500c01c1d4010a02d00c80c004000355961030f6500d0001c03014103ca405284100d940e4000031940f9a1940505040c2c040c5480c0512240701e1005407484405110040444040c03040030009110143e071220700801241c00c80d5254000620700303100007400245401058102801c0c540c94414840140744001e48007550f20813100810000032040f411552031800d400012702d0400303101544440545032013800340c1030b9010b40d80c905400d50396152b4201c040e55400d841c0c42c4c1c4505225004115415a40c0640d614000e0000d0100b02c1419996240750b00307140205070060b10140f0b030303000c1700c14450101402038000410211607480525055000011450b2031402c80500500c00c2c0011045800c280a401c2140208269851640c440e0118 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 67293689 1250 67292439 67292453
    0x4080307020414060d0f020a030b09060a0c020d020304050d02060910050a030b0a030308150a0305060921030915090a0606060c0510050906010911090d060b090109050f0c0d0b0d 77
    0x408401c91007203040c4000d50442c4040701c12154807034440204405000c0155488140f801400e0300c4080e81c010782c04150100c0800c4540000b2030056005800826881c80c2840764001100c52076032102d81150824045141410760010a4505842c03084541208034400e41c40020024842c1e410300503084680d44000e1011282c000e0f003d444c400301c003501c09104114104c0c04202814001d408010701040c3c0d200c01060782c100303c0050f0044a6100600b0180351340c0d4580d11120f161020807224141c0540c403189182c01041101400480621100481e250850070464103041e02c449612541c11200096400050f960140400801e82116009402002007686a2000802c8400e1902c02680d5601c00c1c0c601c01a0f61047c43e104291203400d00c50007800c9142d007003000900150440d50070814140205100510080d51044e4208007001c0c071410b000186038181000b8425020016070251000500c0c14041085020320b504901d075011128403017103543c815001120344020515a100c2e04c0c2c10080040d03ea50070841d81c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 67294939 1250 67293689 67293697
    0x3020105040308100510050c1005040c05010906020109050c0411040f08010f0612240b03060c0301050301140c0403030f170403080f18030d090c180603060f1a09040303020d02040803 79
    0x1d80e076020071a40d50030b0f091350f03030300c0c126202c0c5540000e071416070000094462030203013a80802440a031103685080c18558000e17100280c40a4505100c5030340c04000542e00038103090010480c500003070211203156100c860b1584041040c041c040c1c0e4542203040c04452040d8110b5014141c2c0640d500700319070f110442d02d4020311001c2c140012040c030b0b201c000f040c1281505000300a40f94070103c404c036a07030513a080240401d0014010f15034555105d2442e41440d40c1e00b031144612070074100503213540740d616060405003910184480c10343c00d410882c3c24860302c20042c500b01c405403505414040c0c070903021101c08464013605642c14410030540601030100705035018545034001d90f00d0400464294807040ca8070300400c2c81c240000300c207550080000f081c0460080d040f01e0300c02401404841e8400350388581c951941c210405421500c0380c0e0380c2006100300900c03486501c3c22482c44d071108000324040c000e03150707001010201240384142d0b42c600000b402c06220343c0480399056400f2205545480c0d90b81001650f9802c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 67296189 1250 67294939 67294943
    0x6020d03060515070201140418140a0c170c0f0307052a0a2a0e0f150105030606130819030905030607170403120507080702150105012106120302010504 66
    0x3007441400952450840100c1d0081851822030900d0a45980d006641003038841242d1054201c05104c00102d920725191043c180070f0b8070b044003142e03804501030440d91020008060a0718546000c2e042071a280c1d220107950621508100c6e00d00c2e0688800c103020030140103010603e0b694090000402a415174403070080c2905000500099180f2400c0b10b440042d030071400305201090398010b804401c0410f078045584c188000550b881401a480f0a8040c55580280e41e008104106c01c1d0000b030100032004080c0d01907015449541614202400b0b2000904074840074101c07511840012411205502244100c0b100a002450441d071131410800381c1100c445a400b84158086044c14130001380a040100d141c0c0e20071946c03540d4040b444981d00c28081d07a8000300ce0f005400300442000c0907240070340390b44115405901140c4a00006141a000c001d260000800d1508140c0320842e0040001d660000c0704010300300c90819006041c1c84690100000078507807540190000719030040762206058046d44428040c1c0c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 67297439 1250 67296189 67296191
    0x61103010f080f0a0302030d02070606050901030f0314031e0402120a11180f0a150e01061d010203070209060405070c151406091b0f091f08090c060301091d060106020d03 74
    0x40103403d02502d030015444041e0150304100848410b200440e801406d083e4030030301002a1070f07074075400828241300007600100d6040c0c00150112092580180e0400b14510325204c00610398502030810a800c80305000c0e5008900d050007010030700b19540d6032034441c04000f0070310460303c0d41c00d120700b000144c1c07008100300c00d80580c03c5d009001c014880c5c0c0050b0184201060790b010341258440442c85001000e4608050174001c0152700049505280d0745c128034000c10003130380e65000004480c1c800c01894a820347d0114107552007005440f00680340c990000e03030301c048205c90000360341c2c0d128041540d0488040400030110300090340c1c042080d5040d82d000380c000408144564100f0782e20f99040c080914070039501d12070b06181c05a0750700c62000306600100301c40106070b40d5050504c0c09586c04601c550481c060181c290b10010640c441809501841d01d6600244503c020070141032000d02082e198441801410700c010307103503210100064490007050790000300700c0044902660355810f00940319400850b90324002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 67298689 1250 67297439 67297453
    0x170a020910080705090405010204031202070510050406080f0604020408030a03020c0706021906021c020d0f0b220e011803020d0311120f15040c02010b01090b040b0f07061103010f08 79
    0x7580c00040740c0000d80b5070b40001007810700e0516040060580004100300d5a56400300b00210001e400c00400d011300440c540c00601c1c0c0c07a41030030304010303148049010320003c00c42c00380410004540e00150315a0050102e1081d0034042e00c3e5207000c82e001c0e104540103800c86100000c1c12110b0103525500516221b08600140d0b03443d1510342d074040ba1111a40001d403281105442002004036903581e0040c00c90f01000650b900c42007120100750010390f04440d41c2e00b4004d07603650744800402d01c00c0d401b91003600013040701c0144060101d1081c11103904050719a0105503130341c6549245491009520070b141070301c0710014400d8030b0026850020b541e86105414200024107001000710032920090944241d0546202640145d90750802502c581020040101d200c900c1c003419602c030907071643d01ca0002100625400412490460b100140205c3c0c400d0303000b004180782c02c020421441100d842541d00e11a10320f001c2c1680e0708142d0034440060041c8a4003449160000000062113466400a2600325004c8070103445d80c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 67299939 1250 67298689 67298701
    0x702120f04090b10090608070314100806090c03030406030f090804090603150501051305040201021c02031801020303090705120a080d020703030f05060108010e06030a060e060106080105190302010c0c170a0209 91
    0x11084961007030030105e0b400c0c400c18040c0c2405200e40503031065180c03600003085250400040f00414040d0340c11281d500d0f451005102c00d400500120b548038490000a210458040011981e240300790720645080607039840f5004070612040d081035a90030342183e10310380c60300d4440150200070407403884200d42039004c00b60350341c820440c01d0042c00d0494074014007112808144480844c05041d00420403811030250780801c10010312010b003042901c1255a00541c0c54034800c100039080d003d00844c4481c1503620034010031881c140c00081d441d0a41e402038426519403c20120005e01c0d11290800040c003401c0d0101703004442c440703698060315065001c1d50301800500325044000307003114000d075180f0340007074039003801407094040b0390014940020001d41110b185443e1500e60104981442180404541010004210301ea5001c030009000d08412128000100030003d04405240c41d0f5100082c180000800e2440c140140c40d80e101009004032854040e4281d41c074144543c036182194000c85c85180f0200105070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 67301189 1250 67299939 67299949
    0x5091c08040b0c0f0910020c0102070801090c0504020d060b0301030f05060601030209091501260a06051203030115030b0a151d060403020d0f050d1107050102240702120f04090b 77
    0xc0200e800002010b2a0345584200300d400781d011441c80700e030803442000700c00443d88420701444140200e540c0a002d400909070002404c000040e44100c401d82c2c10a5980d030301054441444104a40b0101c800580d50070040c80c000002d080c0c194821a26000c0c044000024060040410b5500a20440c1600d003203039514001074080780540324010340c01c6815000004d203944140c0f2080c841e0840c0504107801c1c0744980c0000454450310510203420704c0c411610502c040d14503940103d5015190459949030354650f41e014072540c9020520881e031800316115613104081d8001c1e444045403002c01b520001c3d40585592000b005201c500b50180c001907640151a0076440000f01c3d0055140b5004142038035081ca107408001c0810b00f150f5054034041824400704000070000c12880c000300451380c84071440345642e00b4802d401c02c4401e501c4141590002d03419a0052219030303144025154400905200341d866503c0200d150800d404001070425900240440e600c0a00c10041d00c01c940b40d203802840001d0150003444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 67302439 1250 67301189 67301191
    0x9010c08070e01030b0310060603020d1103011a07110a0e040b06030111090105210f0403110c03030409050705130f050a14090f040f05100b0103180c061b050105091c08 73
    0x100c00603030b558076090b2580d0b11070381041000e007900400303c42c0e907080700800c807030111403541e4480b1012076070020b102c3d00004124004e00c062088100441420740d0314014401c04190400a10410a00740000c1c04c2810890464801c0c042414003801d618201501c92a039184540001e4606454246042000444034a07050044049080d00000c4280c01e01454400540322504200b1000c031803001c1c05912900da504061004503c45d15038500992028103040c280504058003c00c007808054101e041004c0c2e29031000000c8a0407200780c24000620760b03481e418111600d008032411001c3e040d5040b1700c00613807603005603c4542500c204561030300b134a6986000482400741903180d05500160b4640c0041d800141000284e031344140142d0f0401e100000940d40e090502510120380041c6540d140080095940d043c4260000040c00c02200c1001040e00d4461070920811445000304010152880c03c0640300f05051080300668880c0080c0014145003e0580c7c031074024080300380340000990796141940344922442d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 67303689 1250 67302439 67302451
    0xa1406180c150307020304050613051002030307140904060509070201050109060b120c0a050c0d08041208090a02090612010e01051b120a0b031e03030a0e010501060e0f030a02040e0609010c08 83
    0xa41d4a0349030102d0400d140780c0000341081d06600081c00001103507118000240200f80c040d00f08440c1840c1081c0421030a02044103e0400b1540103204000080d0f420109034040008550b2040340c40d541d0241c00240a003140d40c010a80189000042c04540b40d01500014140c402c80041400341e192200320024550003a1a00011718010b442d01180c801c145601c0141a07016040c41e101d0f01e01560103001760305c2c0040328000c1100040c00c0e03004104c20712a811410f405840300c0c1d464005018280342ca036013a91400340aa02034400e00800d13020802d25942c001f11000418030841c000d0259880001c00513000340411142c0d200c80c2d0101c007516801061800044500c0382c6616030304c1101d17035100c0032413500003400303140c0d803103078251141d0001c07004a600404049002592158001d40d6a4030380b040904040d201354140c15034040e81000e006021030341d013250000541000a8884980100645000030301d0300c0d4080502941003031902c0c550780ca5020380420303c18841c000e4107000f40180e598400c03049918480450341 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 67304939 1250 67303689 67303699
    0x1209010507020c011b08030705130519030209070324050109120c12030c02060301170d031b0f050d020d02040e31020409060c02010c030c0804080301060e030a1406180c 73
    0x3c0c001466025040302520307500f650031200084002ca07520101c00358415520400403c0700440c0c0c44541d1700b051001031000d440252903180b200d00181420707041400180c04000d00c241301c03090014100500c40d40c441000c014003c10286404110403826002040040c0551400a10a41c802080d09000840c045400030f503c60201500c0600d003a803800c441e1201ea1804030304020548030110050303a10140998041d0054400710f100ca01e039030801d580e2801d11041090020315050000b1540c0a07011005c4110341c160407810102c0c4070190b0107604458610540070301b107804501c0465140c1c201815540900107079006443c28090f40e4650000c1600c041203041c60304500707051000710f1070000e5150f041146961030320103440426590b010b41e4501c01950501386084006139511141000c1e80b0b5414021086884500c2c1040301c064203064481c0c005520050040b00c044c011006869a083c0d142000071084036501701c4144240c0c2c0e400d084019480e000c05031030b000310000088008450711040880c1c2c2d90258840142 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 67306189 1250 67304939 67304953
    0xc0312031b042706080f120903031309020405010806011407020103181202010504020307120506011401020a050f0a0209060f010503061504120f1a0f071101150308120901050702 77
    0x814070029035550741146141c0181404002400101440b41024594043e04034401c3c5604101500d421194181e000d07001039404055003c0c49100045202d44002041c414525030b5034412001080c5184507180e111140002080c2d00000c1d80a400e60203807060340d40036a03807146541c4070070004440980c03180c00e0700c14a442c000c00a0341d00560280e8025110881501c4103c039100b41c0d25190b600c0071440b002d0480c40541d4481080008501c5e0a02204001c0d00c04d040220250b44034a03101c203540c8070414000c18003841000d5003480602d030700810500d0422a400340031181032104403085035455000f0140124080d9092784082a214502500302e0600c0001c1071f074490341595a0b070030400491040401a81280b51400c00000c14590900742c0342d111118041d9008131040600c86c40c00c03a03e02118002c00d0095003801d802072048407076803140071940041007458001010f840240c061401080040041c1122200908001080100c510041c1107103da44203200d1905a81d91041107080c3c8008459010040e01f02030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 67307439 1250 67306189 67306201
    0x504080d09060b1f03110c030405010806060409020403030203040801061a0d020304060b0303031003021e0102060f0901020409021209010c0f02071205100911090117060105090c0c010504030905030c031203 89
    0x15101c00d2806000350808650b020200c1e01150404074121a0a4a5540b0300b040c5050b209030140a840c4843c041c0006542c0344c940c0e9039110584034040c5000302c6040080c44000b0031540d0b0750705000e0b00c02401404a08658459903450081d6880d440707841988400d500309440003829100308101c8100c114000300b460351400c1e086243c1d0030001d40c0020011201c903075a40004500644007000514815484d101158030800d0841c0104160000b6540d20405010080c010345103050740e0104616400040b480b0001c41247c0720110441e01a00460b005041e0a03480802d84c8610f6868812085018040b010700801591a160900304c8420748044020000341c0d0084004000481003000681c034103501901c1651121400074020100b0f035110b081007503901d112416121078040c076000c02d1803801410000c440680542407074000e43d403107000500c681841052503900144040ba8250102c0fa94031130000004c2045150a10b00902800f485009282c043d100d4840002110300300059820750312003006c0981d505540d212 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 67308689 1250 67307439 67307441
    0x20918070c1101121a190807030206070f05030703020a020108090a0b0115050403021e0a0e04030f0503040609060e0d031d06040f020a0302181603020304030c03030b031c031b030504080d 81
    0x341c20010304000d1250071080d481c1e01e10307201e550100e0b43c1c00e00c00898102034070001c02100d812807001410115840d106c041003014000203408044a90556005840e81010f0402e102e912410b000701030b20b50b00000583e017080550100b00c20241c10300c02d0321211006d0700c80005d05503035002c1c40b2000900b020014001844114000010942c00190700c1c54010f00d0300752030343c1c003241c40402540300322070001280d291080c01d6803038000125005001c3c5881003441d5403030b158400529202c0d01100090074400008041001d104094100083c00da800140034482520381401260b030b544980d01a03d00000d151404000160744040120b280c0048200020310b0903445030b4441c008641c4d030012040781d00c1864001d0000040c1c40d5000d80c00300d0400544454001494480700e80d040c516a558444410503204000308030010f40c0050244c19810740500d80060040c1c01007001c00e181201034100301c61005c42d5000c0d00a0b8603941030b0001000c1007100840801d040503d0801030b000d036075007036400500194041c0003181c121109 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 67309939 1250 67308689 67308713
    0x8070309020609031002030f0105040207030906030209010c0204090f0605091c0e0303120108030403030212040302060a0e040605040e0f0c0f0d02060a090f0303091d040201080c070f1203020918070c 86
    0x40a407072401618038006460800175004a00300c542d0040204280000004078a600402c42600c06615041e0b00355401001404a4000c80d018558040740c0d19016034400d0041801059028108000205490802c528026039170101100c04a051000041c40000085089200442c040c0c5242444404e0880305586454030703054119014842400712100e40c0c401c0c20843d134020070007040696925410350400a0405103444400d061005080004100688a0710200c0d1020b5401d441e08100d1600c5101c0050b0180c21594401c0782e2090501d03080d45812000481c1c510300c00c12810048800510303002042c8007104a80c0201c0651040140b00c01d1005810210010402107a451400d2140381d03480300b004c1c41078581c03d0307007055002400002c0184200010015504880b020300511288249043d034002800305000814400e00c040d4085101402c018540200ea01c903d41c0c0300f408440342c5441e04070f0003402500103411031482400446000380d4183c091100d068003540180c2d58556210029454205036004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 67311189 1250 67309939 67309943
    0x6060d0f05060a0c0f05030708060423040321050105030601090203040f0605010605071502270604050612090d08040302060705090f090f01030c0501030e0a060903090b0d051b07020108070309 83
    0x4803980e20500148092080500c903400c5900300103220301242400034500300408a0a0082c05003c10a00443c2c0e42c000c6081684210b0469002c6228809181c854003120f410f42c5410b42507100325000d010406401015417500701c0000d6500201100c81c00c0455402d4490a00c80d89406400250050000980b0b5400440d4054041e07040e078030f469001750b901c2c0780465000364000400030310045034903000c00070108032590500c03007260025403d200c03101039490002e041a034078507052403880c0f040c80002c648540050320020100140269121a40b000150740100b2003100e40007000d01509000301817041c055544140a242c0590090886d96260303a000e841a90015100d20ba0204651405452035522091400c2c1700d1500c030420b00707815501d1454880b079818401c3d0040b5040c142810540c102045000804030142074200c0c00100d454030590406991a00c0a60800c52220200203030411603160300da0030082c025103051040010b89650801002814004c801c0c0c024002002c1c031002c10081886600610070040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 67312439 1250 67311189 67311203
    0x10903060218030a0804031a091c030f020c01020d0c0305090615030a0206040303030218041a1302040b0304140709060f0513110a090501080603120a120e010906050a0506010c0506060d 80
    0x80002c2000a2526408140c03c4070403400000d018400c0050000550b29440825403010820342403151161342ca40814401280b03403062104d1002c0c0c00a48607400c900b4804500120071591103801d00321982c081e40c004981402c40608140c5072941d514400d120703107407080d91828007401c1070307403035410f10b1144a00c50804400d9042c0324003045280036136180c80051004510a4034010303551002104e29040840200c11018800c5142c100340800c16140d400601100c02002c4407001114072020490b40c000b40a03e400010001030040100810890413190070031409107000e003120f655540c0c541d038510a0719010300481d01d001c0c540f4642000345003000030000908854000001c6401c90700120041003d07080a440c5a00290107140100301e00c0d60401354040d00014154040c103c0c5203034103080c01540d84602d245802c104280c403842484c2c101040d034070801c5a081d0780f0b802400141c500741851005000103842200c0664540b1001c070700b1541c09400c0f1501c08a070b100014002903640c43d4200880c601c941101a81d0b51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 67313689 1250 67312439 67312477
    0x1a1504050a02031f03020a06110102070b1305060a0218010c0201030f09060f0c02061302010c03090f030b0f09011506140714030c0f0f060a2a02060105010e010e0109030602 75
    0x255190301030244a403504920040e00d0789003444406074210076030030401416025422050015031a0190700c2c0c025038401d400d10030b0216403a1a42c03d4028481e0140140420804400b403141c40d45200341c2da10600c50140040b00c045c0e0301c80c03207841d5049200e80c440b19a4030028100c003600c9103501548a188146005040000e03025064171a0201503524020b000c8880d6942c070b100e01101c1c03469910482d40170f4075441c401441e107481c00c1c40400103480702e15100607051040c802c50141c1090710031002d09015001403071200500580d2803030255007206081d40c6500c02a48101c0c0024080390381480340100da44d9104003000c581c9031a0800903100c0a9425030800c0c2c00b60302c1040724501185006243d0010320140d00000c5d179640c800c1c00c410038140017410049404642000101030782010740040c5098001c282e0280c0002c2c80c0508101030504248200c000249081c07040c102600083c3d0081002c604844081c0c9400c0004000000116000c0c2c00000301e40d400701e000c000e4107101080455000c0c040b490065030149400b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 67314939 1250 67313689 67313731
    0x7020c0904030306180b04060b0a051804060b0a080412080705070b0405100e030910050403020901181b0e030c0102070f030303020310050a0f08010b090c18040f0203100503070b071a 79
    0x20705c15101490340d84c0c1e5207410031002d880c2001c0c410000186036002da21401c02d0602400184184601d6040d071546600801d81aa5669103551100c2c0c02800008201c0c0d9482d182c05c2d20244c191281200c0640d5504c181c0c100c1a07000360b008440b00d61042d440c0350754007454004603a4440b80030722000341c003e40704ca00c40c0e600b1419107242140304601c1442701e2007006584650500080040280481c0342c940d08211051004100585401040301c1c103481c01c13081c81164084200300300e01c0c0101210510580030000d01e10084c003c030b5401445900f000541a4240ca440400407001603070359400901c180c6581110150007040464840d90140d80c008501240c0d40707442d81c1c1e2320030000c0c0c411103c1c1e42081c01001d5a1607401c0280940074420800c6910054a4900180c40c0031120791544c0c3c081c0c9100800988079410300c03083c41d991240e100b900400b1f4901400c5440741440780461a039488140506400307031052410204420504406413010750f176010f27817480e00e0813008030014080d40102402c12580070318240c458041b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 67316189 1250 67314939 67314959
    0x3090a0c140306101202011b0b07030605031c080c07050c03100203091902150307180320030604050613080c03040816050f0f0108190e0a11030607020c0904030306 71
    0x4001c021201c405526020240101410620003501d1044034810030542000849140321807021415024200356005a1032191a0b107400011a50010415a075510801c803401c2d8141c0d1008045c1d500c26000c85200c3c1130418000c006801103056500003291143d400202e12681141c020162640300d0b800780d0f2008103040002c2450904071010349200b443e0048200809004100070741c5050400022806403903001c941c011520720111401d28620440b000000149480d00541200c0a1001c40111454009503203007880c04002200c01c03921341819404120075102e6103000070b1620302803074100b1b001e0300d165240d0701039902c11901075036411290070b4420721045024103024000342005003981d90251800001c040190400c01020f500894490340f0100303e00d42282d02d81403440c119416007802c020416448841c0b615140f425400241c414650030468440c9848401265821099200d081c0c04c0c158183e81004054564034200c0d40000164003060201c030840c5410703e8025001030003400c00154003526494551 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 67317439 1250 67316189 67316213
    0x9050609060c1002030f100f0b0d06051012051302010e0f15030f010608010b03010e18010e070308130512030304030e01050d06150f02030c030904020f16030903140106050603040803090a 81
    0x30f04503a02208009460019a0380203512500040c0191069402d060141001da801401850b0300b41d20013040d280c1407074110f076118501501005000c1d140c0559403040041802c40b4902c0028085818140807a0741c0c0700c548410486901d81c140c6030080b101166405100c50303d20002c40540c3d1048601a920b0038012801c401140502000d001e0381c8510740c10140060000700701a404135440c9041000100b00b0398850000d05604031801c51000103030f2a024800c52409400079124850403805500400000c1003a003400400140e9039404800341c80a41c1c4008101c03541c148085002100d0300208000703400a84a06425228103105052160800664411034402c40340d2642158507030800404007880000d0308810481ea0a1503248001d41c50030002108641d1a8002c26100074000c907008210b040c840000d032010f44514006080c0c50122621403030400502546061005031070f03c01850001a0350f5000600441d415504042c107540d02e95156543c40c549140d20040c40a0303030b14001d107114400040c0d0845201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 67318689 1250 67317439 67317463
    0x15030803090f0a020d110102211e07020102070302060c0a150c020c030c101b150c081302060a0c031101050702030c0c0f0a060804030c051504150c09050609060c 70
    0x80e2a8540080201d10b01000000844400e910420841c40140d442030f8003903100301c0c0c0c020801013402c481000140e2130140140c4004086036402454054641c0003040074103c1400380c0c202003030210418a9103200303d842034000c041c0c01078002110500150800000901202c103410088801d80da00e07a44401c0b00952007601101204c5455022140794a503040050f00c4a4290840180080080b5000000c5400040881c05424490800740303a1092002d070026520b00103820105c00c0c2218501ca603804401410124080c0010540b03640c04078500d5200d014000b1010b0b9809080d03240381039965582070303c001441c4202102004002603c0314041d04007030007594020325040c1c00441d2140503201079a414030f14820216406a41c0e5004840e0a99990301401c0c0111501c0f810164029292410304a69503448064041c100744078444602a0082004020f107110307901440039040842d20f8811100e0582303a4802c00071002814070102485a46420401881b60300c1d00100440d01e000e08401d4030501b044914070007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 67319939 1250 67318689 67318703
    0x4170304050304140301231012060e0f12070803190e0601051e030a08030408070b0708010e010b04080628060b0706060f06020703320c01090609050120011503 69
    0x1c1140202d0403060440c144c1c1c00310024020302050300743d41d40000762115000790820101c24081902c0e102030f0742507000604862812030000414a042c91400b42c070500701c070203000380b1030720340c4a1340914000b162005400459580c6680740143d0368131900000c0e0006082c42211140d10101140e21402c240301d8003910107100c1020707010940c0351504000c0d444003003c00d24402111000da003081070760b802240c907030a0036500000700ca0716602d450a11060900485034014466000c1c4002d1001903500192a07504a4070045044043c40e0380b10582c0c1d28150045100f41c007959440390740421081248034110810002c00d40000c03c04480a0101210907548ea40c0c0c040c920320680001c1c003009002141c017802000e041c4402006240c0b0f03141081c001d40d900810305c0050054188040103042e44c3c80a5804c0300300d41800045403100848000c0d0740d1644451109031000d0214010000010310316010700d017080c04894050310b412000e0604180020041c10702220308080c5d07550b9485252580d50300341c8076124050b40c01020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 67321189 1250 67319939 67319947
    0x2030a12060f0323031c0203090a020d0c1403030a0f0e1201020d020c010501050607050c01081b0310060e0901030c050d0c0f09020306010f08130305071a0901020306030c0405040803040308041703040503 88
    0xc544003030050b441c1300400d40c1e0020052a0309a01020341c485201061000c1d0042c0c1c4c80d42d44032110390929500200003036005040c20004000c6c0400c0b12120000d81d50904071074804c4480e65020540d403441076000c600c012500040781905224020120301d0043c440103880c2201004143c10f089003241d0005003204185540031800b0703440100240b10395405804107480842c5010000d40700c007a560039440900c0790420031080d00086030710140d180c8080001c1e0786400480c5d241d051070b40700c40708140d00d9030042034002644100565468900008064102c0ba0096890414242400e00388820f41c5684582170350340d000580c500280d000001343e03c0380d00401094500503281d00b4a040014002c5403034411032020410000d0501c071011288564400c0079035894140141d5811881c5000300544002040345880d0220180c104110a00c040d0001c520a900440948140c4540301c4e040000701c074810349026010300e200b0300020300024001c1400ba500140121416451011440c450002c242c2c000c0b142114150000700d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 67322439 1250 67321189 67321223
    0x914060903010e060703060e0105150a0c1a06090a02091806010c0203030c070302010806030a0c090207020a08060f10170309100905100e040510082a06040b1c020a02030a12060f03 78
    0x2c407d00015284681c00940107525042c00195120800b00140540c46000101d0f002c60502030a44030300c82c291b0003a1030107142c03101d0001000030b608007110901c0c01483d914000440e4440180708840c00b014004040403031489406449082c0c440c401005141032000c143c4148015030703800c20192002421010081c40614210306c0010079603500503020501039401900d901c4002602940040c09940e00040c3c010784441d00b600018900550541c4981010b00550082c8030390081c03e09801031241c03a1400500003403a94540c4403100b28020171008014a41013031103290060300d401084601d01109500d01000159298800035443c1400700312000c0100e644101c40091504050080980c0180c0d110004d04c1602d14011030903440d1000401c141410484d8481c41c641c0000c00c00704008c44100c005802c913510303252140710004040c1d01140d052800c503840d400722207581311154000c40750b500d07841754065800c00811380b10980d0b040c4608160f80320f480d80c03079540c045510150321000d400203500404044d100c5154030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 67323689 1250 67322439 67322441
    0xf180305011a0607020607170d02040303030c0f05041a130801050112030e09040f0f0302071a0c0c06090a0519030203011103070807030902010203040b0a1709030a0206010906060914060903010e060703 87
    0x50102d90b8003800c0240036410141c1e58140c1514036094105c0d465040c8030500702c1402c001803007050712502c0d01500c082000b02c249076256100440c15041c640702c038448079803071100585190140c0c3c42407503400c82d05010141150300200e00540a101c91441300030706410749440c1e09509464090b000110440d031098803440505500c03500854080d8400d0715071182508090729031420308011030ba005041400d9441d40c0e9030400d4405c100702c0008021114447c4810748011288400340c4d40f0030b4208505a10401110290500d407960840704458002444042c9035440c0c02d040c00a103400321807201c5403100b00c8440000158a00780640072150301c103940d030301340d891030319210182c00210003030500410549440791220050360004129010f82c1c601c0c0420a49610320540200da2009021031041d0166041c0424040942000009420b45036450b4007903d5113a80c0301c1c1d07406401c07100c192180e03000280c6950302c1000240d12a1090080340701d1702400c40b601c0e11200c0c2000c0307030950711f050884400c40d41c82142048607040d49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 67324939 1250 67323689 67323731
    0x14061c020a120608210c100b0102070e160e01140406050301050915030c090c0c0a08090301061d0703020706020d390507080a020106030f0501021213120f18030501 71
    0x1188420843c1a013880c01c44d95440416085488501c0c15107004c2001002040080e07034841c801c20300031120403070010322401c0e02411030104024094403031620041000089004880d104400043c00703d1161030b43d0700d104861403680c140d000740c188011580c40300c41000e90f4070000e0015001a032140c5942e540342c2400d00845620080c0f44864000040030440c105503004100d212488400702c0b021500c0e504ca400c0b1031860351148584554480c4541c0d10680c003040521000b0b4007420100f24000c100e0107944286858803100c000c00742160b21440040061310041c001d601802019000350700c01402c0c0402103403304100c07030003056041c07454560801c81da054500090340240102e02400d40034505510924409011400b40c5034000b0046003010949841c010300c00d5021034021504404089030004190070f000d4000d5010030b440c49117104074000003808010203580042b90503275100b000d00c010010212000c4030390070f0940c2c5000d41004041c40414501c0698100d40d5000b03180248000245507a43c0c800b82024111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 67326189 1250 67324939 67324967
    0xf06051b0901170601120f0605030114060108161205070e040b01050903030d050402060c0114071205040206090105070302011d0f07080a020f121014060915090114061c020a 75
    0x81000781066603020040c2c0c040b85804601c0c0c0101c075112040144c400d20800319180c0446403514104c0b40c142840b41d000403013100c0040c0d001b0009210404426034146004803009808030701204003088102410650308c0c8035042e0103141405400d103c80a00b6003d854080c1da41400103101c4d0070007007e240c54184100502403074242031407032602e00c03030101294582c021144209101da588200040940d142c0b401140c61102d00300e03000b00180403811015070500381041e078880d4006030b00e0100e0000042940c2c841d00f40216001810303d03040141d030200460f10b0340c2c071581c0228119500c40c2c2e080301c8408a50680801405039000140c890501749110851811100341d05c000b020342e01000820f005a19a088011303107080c4251854409051580d044620340070a55080041d101d141c003841c42c00e201100c0000c18051501103606209075200c4800a049400310003503070381c0d8043c0b9200b004000f0581482c00b0910b146034042c042d54100150b0250920030503842c4041c3d15102034000404048590b40540c0d1054449 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 67327439 1250 67326189 67326241
    0x20f040603050d03020c0f10020717070309050607050102130806011503110a03020c0f24060405060f011209050a080d06061b02090709030f06200903060f04020109030f0605 75
    0x9441c58440d40e581d1101c0746044010b01d6030000c2c210181d10014444101030401c01d0040f94840406039082c04001d600450058903840b840d000101c400015000c01c5516480e0560341d80d400c154109401c220300340c7c0c4100d070229074a40d03080056201148000b82100d000740b000401400c0e07150b2500240101ca20414400c4008051826181c184809110425030306000800c0c640181c541040c0401c880c9007041a04c412082c0d8820455054684500507183c0b0044d4003080203803000c00d031a10014001503e800341c920ba5803003a03440c0e804104031f51140c4d001050403000c100740410b9800c9141c035007508040d20903006030340000c000900c002da00704042c00703200c00410403840d0062507400c038442441860280d04200a10408a110200d805207104540391005103421120401c2c60302d0b81c2c0d2800c10000c1c4582d0804002c1c0503d24806c000000301d0f034070180c40c01550701a0280040c1e81e15119540a410701c010822410321004000c00300126090030074240100340b103001300003501d0400182e484000700040740d800e00c0304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 67328689 1250 67327439 67327451
    0x2010e0106033504180c140a03090519030806040c020606130c02100c0302190207061b050709090803010e01080712030e01020c040f06031109040f03050a02010f06030b04020f04 77
    0x602128840c00b0340f5456995216401541d001a1610405124184a442c81c4000c0b41c04103040e1a5405001040400c414003000500c0c40010261030219850b544809110018803203540028026040900c0c0b00d4820403d54007907009a103101d07000d20010220544c005450082000214141072081a0440d9a51f000500e128505400041d82c01095102807000c42074a0380151030721135000704007542c1d840c03001980901c440420414010001d410003844014044c045104254107a40017046032000e44101d0f507075841e003220110100d00c0380d04a400380110340d90322039280001422011813058004903489111440e0340d03540741841a4500e04810382044481d80c1066400b00b010a0300f2040803443c4130380c141402c2c1428854800140e0402c11440da082c3d42040c1032299600c5000116480002980c0c4540c00150031001508140201b0010440700100003007032003c181d01c01f0034062406044080c42602c00400d510704044941c01c1502c0950f40200d982c50300724420301045140100c01910056010750b010401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 67329939 1250 67328689 67328693
    0x504061706030304151b031e14041e0302040606030b03070f14010809190b070f020c240d0603050c010305060402031302040b03070308041706100f03030e0406090e01060602010e010603 80
    0x304e10941c800d15810403000c88011500c140164680360017000000b44e00005a510b900b40604000d00940c1a06419070010a00109150181e1486441e018603022280e0406080c0012a9001c06044509503123440c3c012900100507643e80c040c0001030700065030081140b40c0b41000b0b040c60604e03079810144160705140c500340007020700404001384502d024608204940c841100031810114000e9004000308060241081400052004940200303402e0b034480c050a0106101203071502c00e0703803140e1980056400b0441340c03219501401040b0b0068040d00701c80c0340640c402d03c072000700c500703e60040b5856082207440020a6806106040e88a82c090700d0a40c9545002c0308000311100c42044024825030761600d258203161420081c80020310781c042d40302941c8035120045241c000900f0400da000c28490100068013401ca40000c5a0881d400c02c0380c00140c290843d9030688591100b140c509400580e916070003e80d21003d806540c14410030103000103551400d00c08000e00391040d20101d11601d038105413007040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 67331189 1250 67329939 67329943
    0x60503060402090607050a030c03111504081809040302010c0f0305010302090604200f0c06060f011202160804060305070206010504051b0d020904090c140a0b0f0a02070b0a050406170603 81
    0x39100c00110341c016994a01c00c0c000690f240140c8002405034841d103003900c000c0513041921f021030346000f921203d9842c0b50500400f031382c9440304604100b040c44200b021034009030f030380800344c4100c1d59444481c128465401010501c010300850b01640140c0d11000401400e03a000342002051084500c0c00313000030340c155004180a80c0000c3c03c100d000b903540d1407004c0c080003c91100c0d8411000c01d000c40300e550780c40c06850807105400c10743d40750845000d60004605240351044c0140d10020040e1150000d05400802c0d00f0001d400405a0f400b808900309a5100003d5001c0010000b41c0041d032400151410700010080ca0a881600700300d005030b03c2d14090020750160304207484d1244a401e0030340340c2d4034500d12100e40083d00a00e181650080c0c1421071a004020700002e811041d10454104520000c048108004540802d881005d402c80410441401c01014510003003811074043d004686c90b055030785030b8044c0746074001d5182100007203001c1010302449034001030194000014181411203800c090000076 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 67332439 1250 67331189 67331191
    0x203060603010612090b0705070b06030601240e09071e02010b060d090303020906031312020307030509090c070c030b010906060504050a0b031e151c050a081b03030108010e0c0307060503 81
    0xa404c0c011034052103810320f001038101c0106aa4007103c41240760a1208010b0401c6c1c004201c00c41c1d03500c41400001d401b6090010b45e06041315800032007002c0c52a20060100182030b546030041d010051520004102512090651800341c41c4a0783c3c1e40e00c0c1600741124030704000c0708072a014021a41810303031070766107592080241e8072407408038200040c68a0880ca0305400a01c41c20341020b400c10008410014002c668141e001d0009008102c43c00c44180c0142040340c5a1140031401000304800780848901820040452540224080c21880c0b0345000d80d12091540641c0394012038051140c0030042c0000c03401801a80f0050882d810841d0409041c0400580b8a54141c0508011807800ac40058004292400710644035064213070302d1402801c2006100072410240c841c1c03140201000700d54065148e040542c603000e8541c208002c2e00071401c05a0798843c95500045104820b02c1c5d0130b01240001c088140000c5009000d40000040c2e00f588906642d4100f004403001c952003030304985030401195400c60304503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 67333689 1250 67332439 67332449
    0x30a0201120b0a030614010b03011d040f0b0405010b0406050a05242502040606090b1b030d06080a0507060201020307050a0c050a0803040f02040b03030a050417010f0c0513060201020306060301 84
    0x403281001c03441c40e80e80c0c000d0141c821550f0740500c02400001c248181a03001c041c10204019107014641c3e281d07a0744003800d00c020700c074a01e0380c40030101c600c0420290381d54a45412038421082c2c1d00c03180d08240c4482c4850302081d1419030b1544d5507902d605820386410b2041600a10f41034503d004030529240000d200ea151500f840c02403901d907149010144071215013100c518a42d20a120020161240710a9050010b86141240a00d261400204003780140340d480308071050589a50b1504000036494006c81c4c5d40c0b402c96031203c0c8028007003659000c889000b040080c00c5000c2c001c04e02014903013480341c58030b0550340c069810b591040080c40007095000c03045460703080741c9042845002d0204d1410394a41401620080d019040100600c020054071034803240903e8000c0311300740700380e41071001015100e2007603611000101304100030800c480348440404d0035400e507154000041c50f8110b5120003094031400c0032410300064002581c601c1081f500000343d00502204d200850552074000c1c003050140c4418051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 67334939 1250 67333689 67333697
    0x110a151706030c030a031d041a01030e1e03070221060f040309050406030c09050a060513090606050a0b040302031002070f23010e01020307120e06041b08010504030503040204140402030a0201 83
    0xe489840802c4694000c143c09011145e411040e414028410440c0d640c54200c005141249401a8130b0075020340031841440c1c025050801700b8200055000740300c0e0818888580c012a481d140386040c032081c0c5001c000d182e0350090740d510140d9204201c40c0403841c1030100c070300c154600704000c8010740008183d50302c0307903064140c1078498486080946510900e0750201b90302c03500f085008410045042c41c90001c40f5028003050015444428044044d40c0844c000c0d1900030862404c07d850303030b408580040c1302d800c0c0642400608191228042483e200084d0407114110000150800443c24100003140404413032070021420404a5503e0007030803205110701410b06228071081c9200c06551031321040f0071407010030080100120781d26119000c0c2d04125101d0020810380040c91080c8602401403590884008014040784c2d661959400c24800c0700c9003c500304164002c0012885c603409100e0280120301a44410380c0320303d042e20400042d9507000c24101000b1000e1780078080182c03030000b0075240c0f150782428 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 67336189 1250 67334939 67334941
    0x30121081905040311010c03021c092d05090103051207020609030d030e0c010906200109080d09170c0a060f020c0109031107080303071409030c0d110a1517 68
    0x400c8809401401514004450141c8105070740942100050085900c40c0030510f0840340d0800042d544120b0801003d0096000400703082c1c0d8000440348003a001801d1070808440d0951a000d1a03c3d02800c04c0d28101051712004420512101d608a2514024402140c600c0c0c0550305598170a40c9900460b503010807010b9010500b00110f590707042c19503e011ba40541202c03100d411545c801005000c881704200500e008000c80325015522480ea50700035a0126112581d45080510010703c42c2e52061551000c55544c0b1540c44000412460003003072900e814041c042103440c064140301c45d01d05400000d1f00c003001c000b004100c01890012400141c082e23004540010b071082c100401c50080d11404031481039551801c900c42007010340081d024070028403850200d0b04c0036510f6805840c0d8900c016034100300030520224030b82801144190044c01043c070b01030140c408680c8010f0100d221400b4891040340c943c0c100b800440443c9c100010303400d00405854210755910040854054400c02c0300c9034200c1d0300300030018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 67337439 1250 67336189 67336193
    0x2030d0813060f021306030c1710050301050915071d01180513021803060f0f18060114010e0301140613020c03031e16020c010507050c03161a030121 65
    0x210780a400160011401d00050116001800003940205900d04140c4444180821014400d205052903025152986035901050342e98243c0c0402c802010381c81c50500c1c6035008982034500380100c0e8003440550004220644d003002d040d40484100400d4031080000b148004480c030445a800900d44d02c1081c00d180c140780000040d50440c2481c960080d80c1c12100206440550001c207900800320502121032a03c4407010403804c05480304416211103042409501c045880c099013a000d4640051101304141d0740c81c184d081c221030411400341c0c01603903034600301d80e8100c080c0d5070082c6401c0d0400500b200204000145042030110405024004c039000d59120032441780b003054594100c419030180c04040b030b903d0f4907107618005030060b040440054203848200104000c0b9910712810550f40c2c1030f81d00507003840c40104004403040d410400381910a4030404a0103141c0341c41c1401210034240e5030400d082c030182d0070407401c0d12041d802004d1800c0b01c02c504000401c2100c10320f50f80629002c02064940414190314 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 67338689 1250 67337439 67337461
    0x80408040e06040f0e0d03061e090c1b03020607080109090b0a02090406080304090b04060b030c0f1309150303110f0307140304150305010e0117060f060109120303020309061302030d08 80
    0x240c04001c00f600c1c14003c40605c09000600035081525940c00b4064642c035480040d04034805600c2228a20041901c10b00c0003402c2038120034a4024039140c100d5492000400846034540e00706020760141c0c00070414025400e9001424a000d4a90500207105000791a0340d00d10140c4030050070540f0865000c82c030010103a40f81e8200320014204401281d032915110300b0800010002e8074071a512072454054002a07070602c280540c0d00c200102d0b043c0c00d05200780350742e028480790300c21034030f50b0010460b0003001326600c107192180c501604a20b060303405803941140b0b005412444403a240d1005640102481c11141c0c200200f1a052258041990400c0c17240345d0390410302c0e50049400403480e180c40003000d81106645580640c0c102c610100321200035903a59100d00300342d1000000790101c15003007000006c50700d0070000a540d03007040040c548000709990f101c50324a1181d0358940d040307001a0f0004280040007404006090300190054020303280605d0960003e9541c00700391000c0f0003440300d603400044458401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 67339939 1250 67338689 67338701
    0x11d0406110409020d1b030c0203220b0d05090c0a051e0315090a03030b060702060901081e0106030213080d0804030807050c060a092906241315080408040e0604 70
    0x8480b4103548a01140c00044041d01c007411604c2d003541e51b80039144003010702c40e0094041640c0d154025520300f00e1a100700c81d40d45980486a50742000034501c0014198265200400c45c0c0b80c080c00700040c035418488507440c14690721310025481100d01100a0002d40d5070000148070300d001045d5103554900c41240440c1c00e01204c1c00402c043d0010242c1080580d4201248032640070740b2950b01041824042d80400040d03019501c4040c0d00030400303100303090455006500c4075030840b0740d01001c100885000701c58201210030036084080000c0c2c020481540c114032441d00f98000d0711109010700007804080000420003079008101900304254400400d40709801401220080e0071800250303001340c07800050f580041e004111007260b07003a06441c5510344405d03407000c00c143c0203038402503c0d8100c1e8031180c2c200044c00c00404802c80c1200904c1180c07451502e4120024041d14041e01d0004601ca03140201e8440c104140b07091034010300c882501088006402c0400f03c409403502900c0403203040d201c50012400520f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 67341189 1250 67339939 67339949
    0x2130e16060206040b010f0605040b030402031e032a0c060f040f0f05120606090423060a0506040c050408061303030902060c0a17040302060409020705010209061602010206011d04061104 81
    0xd450400460050b80c0420810311550003152520041c0c1d0381c07412444101c4d203040c030504000601c03c1c0428810a041d6000450f0010300050485003500d2a1010b1044000300c00c441c4031016610000d403840f0032842030b015003034444481c0481c019807021044d08407926010843c0c2464801c4900103120600c283d030f01029a005000c0303483e1403810030f5459034140041c540c424041c80d4424503c03400d598038003580024446124400161000d00b141d1141c0c0d0720131101243c41d0410715406012000001c0716a402003142c50301c036019110303001c9000e081040c140001c4410486410341008070400052090400004040350491003c0000c404a0741460908400a0052080080d40a100080c00c6c0400107070000b2011507150041142d050a041e4049200d9200d03c11480b009401002c01d00c8200500c441560240c41c240e400380740090710344814180005c0c66170340000c03a20305003500440700d40c0c8150f5034104030b071502501e240e6480c00310f252042c17890b180001400503c0207100310b440e1840648c5065a41d016540248 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 67342439 1250 67341189 67341223
    0x60c0606150c10020301080c0906010f0e032404060b1c080304050a0b0703020d0b040c09121506060504030c060c0308010902030414010507051209121b010b0a030c0501031802130e 78
    0xfa02c0c020010010390b01c20302c900c0e94940318892003490300d440c10b040c1c580d01648058448808000e4118002da40f40b444800c505a81802540c0c0d00d4002581781c8a4202c5120140c0001340a591816180400840302e00c0706849002d60102c00014000c17055a40e0034149250300903011030f032a5540c603c0c0c0300d490600c03030740c070010400016081440b44150f01900074141c0c0603040c41c024031410350841e090204540b602030207400016180701c8104540c44560215015041c041e40e14204050311240130304013a541310368000400204002810030034800d008000c2d101a0505203403003502a6030540340140340002c1809060b02203075000011a04011104440610740c03100000203100030b07d4000400b402c1c64001c035072003006c80003034080046e940e8140482e68401c02042041c0c8242410015040405962500c0480310259980c65600d0b4a090b962080048011445107008940d4a402d1500050a82d4081818420701044034048000169560121500201d008440001e080f03206d840d00e4902e08580008812651 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 67343689 1250 67342439 67342453
    0xa06020f0306040e061504150807030c0303080703020c0c060d1b110c0a03020915030717010c0e091504020a0c021c030e120303040605060d050312070806060c0606150c 73
    0xa14026030180d03214800c12142000780f19100142182c1701c0408480c0320304200c00c0401c00540b9840c090348050098207030350b000c28885503100d18589243c110b1740c2d0016110001007030300400400d9800400e407a408030301e5280c1542000300710341109640c0d040c90204548980c0010840e032407010300d0b5134072001c5c0111440f0840c10301c00c02c00d403101500303041701a0072080c142d01034454140712a04000740d0800c116607010780249142d607550f20038040300002d02e1003055854000e40c1c50008902004154619000300c0240c00041ea03910341d0030000c0c3c612001091707110700a941000030804046100668941c0c005400c0d500540e5480b000d0008640c2d078506950f0003940074102090b20380251001e616000c0300d1520a4407a0204c00c100f0f801004140000301c04001417aa20410001c2c0028040d600070f180c001801501e4a0a119695035506003142c2003e484810880a44404c11401c542e200c20107580066058900524040410484a880b05030090040380140030040244083c0a020b0040350101c440c0c7c00156000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 67344939 1250 67343689 67343707
    0xc06060607030e0904080f0a030e07140a0b030a1d010209100c020303030609180f1609060e0406090f0807140d050f04061b1e0312060509061c02041517010c0813050a0602 74
    0x4ac81089044111440b40c10700c0468454460303100031181c60801008992100c1c51f0848055040d40000d05c10030399a0384807180d582c9010300c90f0601503003205901001503240d21102c0244200b040180c0e10385000c008800d030395a800360720048200e9401c14020388010046660f84003020308081c4065609801e20320416190244da030710085185804000020751410045689890032400d0340d69034021200c141c1c62610100e0001391169001c080950311a0000d01c400700c540e03032980074440e009071400303840300a0150b50400880304244803400401200c4c0c1041410407800301c0c4510003d0085001e03500500101c0820300c00e5094654011010301c41e4090000c003140d041d00c0c0e400740c5030b840e032022088000c075500b81810514113a50703004510582e0000f52086203183d40700420010608200116000c0614041c181140940c603540611440c440034408110b440c1880c00915800030703c0707007403100b4003a40d02d81221b40c42c0240d8000403542e0880b40001070803200030914105982003034030351240280314a10003d920341d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 67346189 1250 67344939 67344941
    0xb07030e0717010e0c090115021002071104200f22090e06090303160c032303060a0b0f0301050f0a171605040c0206010504110702030f030c06060607030e0904080f0a03 73
    0x1400b814600c002e00002c50f00f1203c103903982c1324291803540d111106074014001a503028640c420240032910441d40380c4d11002424100300c2c2d000c00390940d090b0040e8003141c0b08600b0075010320b00703401060080c0c4405003060050641c04c240555410050300000000e08126603c0c0d8802c64001c585511864928026544401003001419580030802042c010000002c61a18022060f40e01c1403104403000ca1451030508022140e01e0100401101403100d05000102d042129086486c01c88070742046156982c1003040801160441c0da43c0441c464400411140311550501021f5034119002510b582540d18400c4002800f140c921b9003015060ac450001c107800705010000700c40b0401000c0c1c2207030300d0300c083c1c80d002444107944140104101680c03007003004004030b040a07170080440041c1d00c3c9003039050a003981d0000c0d0070f0003403a1085001c0c95001242030450307040180540c3c0d8128000716403036840c00f40d06031f9010f4000500346881d00c0c45260400700250500c4160b40840b001d100791040010360310000d0110180c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 67347439 1250 67346189 67346219
    0x20c190e090a02041b020d051e1b16052b02090906100e06100e03010f180515010e1306020f0a081017030405090402061e0a12050f01030b07030e07 64
    0x281c4154203000d200b00384509400a42040560700d07501402c0100303075488094030154022709184c801d20a5400c4034100140d50b40b400b500c0441c0c101c1e20908a206c4417000e403245450740c010038074586980f207181c04100d103958001036105010f42c80e10300600d00c244413451502e800c4030002c10294000d042c0300104005004041021032140040040e0003407807036294180c1070b224100482d899034100c101d03646d04903216409081d42c850400b40c010004039110358101c216200340c2d10302a00184000d540413003281c08010090140c0c08100e180e0700c3c420b02c0958508110032410010150490018041e00c050030400c0c08000d404450790089040c040e0359545040d900020b007680000c607101c0910020850001c11007000b40100103800103075031030040d410325041c01c04001000c44081c008980c041801c100e4641000d44492610603c0007103c0c000c00d80f201d0b07030b114010304004001c0810b111582d04d400100803440d843d05181a055907000340d0349200969406405600800210328855418411100009402e1035208405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 67348689 1250 67347439 67347443
    0x80c060702030906070b0619090603030e0409030207060f09030807080403050d020606090a0b0a0503060703060e070e060a120b090c0901021006150c0f06020a02030d0c050a020c190e090a 81
    0x1986196184841241c59008040815621000401a10700481c40d5090380580105006080742011a82c24410251078402a44619111030301c4000400905400100031109203100381c4041c03141e0309459030002e4a030900303030007070805100040b491a1009803060540d0005540c1c8001c0030f80d51561541042080354100e440202c50501ca10059410200d102281040c05160090a9101c4a0700c8141820f40601a040d54540d001000a03200040c1c41e5410403d00d40144495280014214185071100c445010010140d0b01030000e40c40306515144c844108954004200d440c02401004000b9100b00180104040869011001c04140300b2442d402100422000c0d400340c08031040c0c05165a028404d6907202d100d6000308102481465820034020401031110900c42d4084071680c648a550f0380c0c0890300000103060042c1d1011800c1c2034645164030561f420072886040082c2401d404000081d900d00460416501804912a080d00c1a4515040e050040c0c504005034800e186400300800d030b91040c207143c00b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 67349939 1250 67348689 67348693
    0x7030c080c092a070b04030f1803120504121a0a0b130509010225050c011d10020309100e0f06040e01030b090309151306030501260a050604080c 63
    0x2009040021058100180904034012503581c0b001d12454083e0410a01d0014109600c448452644140010034079203110f5100324265042c03905000b0314159210200d0018804d44041110040004c0d9100e041200d0f441034401014070708a805c200c48500407648820398450b4680d90000401480d641c5001440c2e40c040e02c0c0050541c0e601d0920300a51b502100c03102e4008141000c0c144215181d50000c503840030340003002514160307030085004030f01e200700d0008245200300e07806003d04101050140c11040e05092802d808114981030000c0035040791000c41c90300c41c18250344900d000d28000e106541d89544010f11000f102c0e01150400382450319240c1c076841c41101c221910800a02d0039000381c2d01540d00c40c1104e0340c0710782c0c00c5581d03540c5a50005004114103200510020710155120000c1c40001201500d15039201c1c60400301c04000c09000b9000201810305201c014400c0007440c20704a011071080441410320315041c803814504120300c0301d4014055018020400081c000c08200611501c100401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 67351189 1250 67349939 67349963
    0x20907020303041703010609092004080d030e010b01050d051008010c090503010501120302120a050d0612030806030105010812070f0c0806071d030705010c0501020c0a0b10090b0603010902030702071203020703 91
    0x130b80b4900910003402074202048005805000c0c031b10040e4400542001000c172825000b0740c251031707c0d00003604030b07610142c07036680b100744000c2c1c2150f494022001010100d1b4020f000c03070492100007030720600603040598011541c5000192840c00c00780340c940d004200100007040964605c2800806401d014015903000707600340400040c091020301c2010350315a8040d4041c103400c60303266240c09003a078051071034581084801c0c82850f541e091a80320340c3c0014050400d044801203030a242c09024040c1c0105854400d03403500d001041040740c00f0600c07020500c82c82d841e00da42c940c0b16203040c4400c20301001b00034029401021000c07a500000007000b81c081c103400d488010758001005000355002040a504a0301900075450820965004042985a10740305500250030583c0741d2038498038060b541a42582c0c032100c200d081c8680c41d203a01681d4000f508549605210040320600810407610042c480c000b20755900100080340b56100b80a41c402a040300152000400c086042c000d40c0c405181c0801d59141900d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 67352439 1250 67351189 67351223
    0x409031d011701030308100305151905040c030201050c1005090c2d01121112070809010c17070207080a0305040806010e0601020a150b04090308011a0c030714010902090702030304 78
    0x42c1505891104407902060580c210341d4110780303d540180c03606000030841000400010070501042c0003450410516031140e1611000e031020071201860640d85443c50141400b021070140d001c0f6405a03602802d0a42c0e0b59032400d59100d28254100c96600f000a00c2c0c0403e000100e05c0108000d240c010040b10020781c0ca041c0088400380b1244200210501742400790501c80c0c595000c1e0303001c039140303503041c100004400903103945d0700c515640b09001c000c1026254a00300036a80fa08501032a4000201400801c514020300c40003920035031028001d20b810542000000c0c484c6482044010040d00c003e600380c4015607458907002d4041d410a001381407440c001d400020842560820089100d110160b0003014000c030140c440c000e8a0752000e504180e01c5840703a20132099034032540222081b0900ca80e5906185600d032071200002244081882120780c10b0811101c01120b4000040d550040d401000600000070f820341510700402c0c4014000350080481d104210105801001841c8030340d0141001940c440010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 67353689 1250 67352439 67352447
    0x1202030310060c030c020a0306021e0406020703080d0908070507030519020901120501150605070302010b041505090a0216200a06081317040801020703020f0105011409040201020c0409031d01 83
    0x115074002107001d03015000c200c0d8500c1080c0d045160f60083c202030480000c0d907008100a48001c1d0800c2d20450340000b802c030071860780001d5420201414000c1182481d0030100000d4461a072880301800203200824140c9011080d50300207980680d1103040300b69659518900351780c0b103000500c001c0e50300340a40b0054051240d03080b101801c030300758000d0035152580c0c200016104d0041401034261400c1d07507200e4002c0c900c1043e500e1050094403042c0c0b20540c41d074079076260081c291103008112500031401c06c00e003400408031032030a50040d1502150300324400d542e1001b1400003401856440c182c12440c9a0600c0d0902c9a000c400300c810b0003850f000240c500d0341e42c03414001c806455104400006405a0014900d407003803011081005105104100361401031041080c4030b42c0094000812a946c0060940200364040020142c141103940c0280200d6141c800e190500c0050310000e14020181040040c045a2081c0070000d40100001c208028031807035818001d0200304200801011802c950202900315805 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 67354939 1250 67353689 67353691
    0x6030608070608011a07050a0525060302040b04120f08030408030604181a0705071b1706070f030b01030b0303070c05040e0111071415090312011202061b100f02040312020303 76
    0x2011403014010544030015440b5401b2280607641030042050280020700240304ca81c44c81d120b4110440d0b4601220820140c6903491030340040245441000200504c00c101c009075401c58a0200f4907008900403400c05462940d902e803c01090840300208000406c5801c0340070354064002694100300b04400c89241648841c0184005012050500c4407030b940749400d2440340307030300821915085041102d2681c0d07804008082121462580401c48014880401481010224100c2100041c101400c1c4a8009000b01005589080406450b0350340c00d50700307901035000200401005401c8940e5010f440c28071841007512406580d2241d030600c2c070303c80b00003081402040205610650b50074a0703d6032542d1410309191445403520554000c1c05c84811001c021500d1103407103000100c0c003031030740c5044421108a009805801ca034040e4618900c00b81c0c056140c1f001031b5296007080b04107901c8003c0f0880c18442c0303451602441c4c0f110783d0342042c102c1c005100068000c1d004403841002e8110025102c00d6060343c032400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 67356189 1250 67354939 67354949
    0x702010f0b1f031112010504050603010c0f0c020604030b09030d0c0201050c0f07110409140105130804091508010e0109150902090c0304060615051207080105060307050f0c01060603060807060801 85
    0x7000c180328140440540020009240e503d08000428003111214103c01d0b401085184031583d6840004100301c1c01c050152030b0307018504038000c010b481c41c41c0d4000381030380120419110800040c40390030f030115196001160065a041302982d6064a0070401c0940d985e4402200c450505040000302c52605005020b854000d0700d000d11401d051018103403101c07072541c100c2e03801541e602c40181c0100c0c01c0380d20f55101c3c0760446401001c910680185845a450070f5030000b074000314801403e0250340c004200c0d010141d0303060350f81502c0b0101c1e00403503004000c0c000940d1508890915482c040840f100250150300c04041c06200c8e01003000c0c50344030044880100d80000e074000e90031005038000a075040e460140110380c800d106007c0021119124070181030443c1d1415950000b0440002d880307640e02640d030840603848200c03032a11100540c1400042442d5001c00760049080c400c012480101850005040c0e032402540b810007007007582d650b058010042c103507038400d00519003d40000480c41c944101c6005040e15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 67357439 1250 67356189 67356199
    0xf032603060d02010e091f1205060c09040f1a01020d08060901030318080601060306050a050402030402030a081803120403060b03030307090e07030b270106020d0e0d05030906030a050702010f0b 84
    0x3959140078007820b82d004980403810080d0034281e07107100740d440000041c040c01c04100f254100d1200f2040f1080c03020b210fa00304103100701304643c1010020f0300c00958141d020050840c602c1c1c03140c10340382c0400d0103042a01c050310315180c20030101001105040c005110304400036030848014840c6014140d4510100340c07455900410301e8030041c80800d0017645d804000341e00046171a440ba41d43c23025441e041100a03003140b00040d4a80100300030601d4886181f00207041d08590031031560420b41d000903034036040a003004240010101c0c0041060b0004400c3c01007050001d000e941e000c0641000003451a8081d01040726580e140220100301420f00105681c4036403481d407281e4013402d0034240310351910300f07004144500f0142c032a800648180c5a0307101c02100030f507440c0700b41ea07491100c400000d640407105803c1403085500c220450040c0c5607024502407410781060307411480e01070346030426500314481c103049640c04c060000203000d403040d003562001e403003001e0a074000c020480048591105490035400f60365800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 67358689 1250 67357439 67357441
    0x2030a1101051e031e010e04020904060b0301061410030902030a2418140105061305041401020c0a0501050c1204080a030b0307090207020a0e06061c02070b010f032603 73
    0x350201680d10042001410803c0c01c1204100864016031129a01100880e80100500c481030808101c5521048200504000c1d0356060404081c0701e4007000b8806072181a100021a0030301c1201d0784880d800b04406030003404940c2d10750100320f0748802404c0801d40a2404801442c21551103449000b40059004001d00a00b01a40e100e110380504200014a8104500c12405e01c402050307218020752045040c4901c030542c2c04905009212900c4422541100e03418a0200300180d0b6070820700b0880038071301c40000500c41d2102d04240c0300000381041c14841c1588001031107244500005090070020380301c2c1c4003e0185a40706004120540030724003800050100c81d0010800240290020342981142443e0004841c02d4401c0024a002c84130791006000b564006071074070650422030348640240c000404607451301d003401030114481d40b141c14665440310901c5880350300c6040d80c50b01107a07166a00301855a0390f030350b107504062107501c0003840102c50081511204060003850303a20740e21001000d03503840500f1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 67359939 1250 67358689 67358693
    0x6040b130807030b132a03030809060c1c06080106030f0c0801020c12210f0a0b0609060403030503060d0804030b01060e010c020a05041509060f060e1503040312110309011a0a0302030a 80
    0x1007005214084a500c400c204202c0c091b104000b1242d880050389200000100c2c2c85c41c14090b0034010f01800f0120560442e000300050100c00700704444900300c4001607551000100b182c1000141203e030402580c07542040000000e100305020503103075143c007030400001100d644822040c200d10440744803e00d16007121070b80c00c241d42911406020440d0004070526420041044604413254007194a000f0f402c208401b0301c100380405201d00301c0c1c49075098920910304046100000c900b402503200040400000000041c1c254407118991810780d07034044100c0e526151240380500e07013040c007405084001181e200b286c034000d620070300c0c0f00005181c014100703030342c9141041e06000c090320f00c020355802150280c02e00001c000f186032203100d000700044900002900d040420042c0b00300d000034580391040840741868440c02d48520212504140d1505041c0c540c810f1060712040503240701508003a00104c04030400c840810b041d080308040d000503070040c4d0040e03880401040109040ca0201a4050b4490040480 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 67361189 1250 67359939 67359961
    0x1050f1e1903021f0201050a0c0512040305190905030d0306050f0f040e030d0204050f03030307020312060d140a0b010e19051509011e08060c09010c020a0506040b130807030b 76
    0xe14010701203000c02140e07480f0380102d01001c011450781c210f01c62000240380040c650a02c601500a940c41c04207005684101c2d03002485801203200f0700c030780d0402c0d1b040803800b0140644111101e9540d5000d03a080c810489003000340c40d840700c0e8801d8a000c0e015040d24102c1d0141710740300b6602500c400070011309981c0d50000603c120100c0100195030010ba481c03c1101c4088410409811031002d03001d00969518186410300c09180400c0300c0c0b060003644140240a10307260080251044140e040f45102120307074a000c000781d003078140100050f01c030036014466207842d0b000120308004200d004900244440c1d0760703003201c2026000200c405e00c801e0145010000c61046003600900d030094070300c1503420205042400007032802402a0300800c14083c0d00d4040104010326101184020040c3c00c000c5e0910340380c102c1c040b0120380f0039240810b04011102c1d48001c11541c850365020050180503115644480c0c50740d10000840c5d210060040c80000d919500095540002408005485d0311030703003140e955215949940 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 67362439 1250 67361189 67361209
    0x10e01140106080f0601050d0c020a23011103010e06270a0e01050708060109230405010b07020315090a02040903050c06010902030702010f091208040807061806050a020702101112040b0301050f1e 85
    0x40c0441c01040610bc01260001e280e10f182e081141c4000c0350103160980d022800c480100c040382c0741c404410300040180ca0111f0060540c4400c0640b294803407071000301960700d8101c1000c060401c410050105004c0d210520741c2c0305c4060400e6500007048640c40340313442a58000012628640000c4a140b07080c88180da80c0b8203044d850080e402910407a0994100c0050b007542c4098000c2d100148020499a040d407a0030028241c0040000c61808041d0a01908040d1900d081c04c3d00a401a038540d0420340425210f1000c842c400d4583d40244e88095840700c0038000170350b0054440790015820080e241100381100e1180f0707090564000301182c180b1900d80c101380c0f202440240141c1d540720040c03012001040c0ba2b03000b42418071004800d09507094a071443c010080750401741c03401403664030610207000161900c800000c00c51200342002c0c10700d840660a101d00d014113003107107200a00004140090800004000345068035811500d21820000071800d0004505040f031201c6856100c2a50000c0103051241c124 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 67363689 1250 67362439 67362461
    0x3050906130212070902160501050606070c09051e090c03010e150115110a06090c0b12040201032a030501080c060a080106080a0603060e0c010905040c050a0809010e01140106080f0601050d 82
    0x1c4c4001590b0380b41c0c0107049030044807400040341c8038000d040041000a1180d240d0010086407558203000240e2204400c10f100e42c010300d0000c80ea2200880d080c000d2400b1b01c00b92000d203004040c841440d2005000e41c4401d100d582c018000e44c00c225204501180116041d8807642824810407556032070801c403492503410840c105000c1c08031110505004a005004040005018100c0480c007141140b07011030000c0020740c844d40c000c40d803e10040903000d0310646c520703030090b409113808142000c03110104a0790086600560710307031841c0707002d088030743c1901600320030b04888040b400d54148006000c00d108281c410408000002174482c001448014043d0803903640100380780c100064815101e43d550303011109032a41040c041d40c0700c0c00700401a0f40c0e0102003100a09404d444c10310042904a4001d0090b014200c44401480309031030001e003800c402507200440d54080400244500914080c0601e42c0c00400e0090000040311240055400300d9000711203030040206075a110f2502c619100564002d050010748 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 67364939 1250 67363689 67363693
    0x50d020706090f050303040c080a020105072a08070806061905010818030f04151e03111207090501020609010b0d0f140d020607030e0a12030228030b0103050906130212 73
    0x6582c0c046440c1418426550344100000e507660b0510341040b118440c000d5001c007180f035201201d4400180da00c482510b004036400907034068801c0300c0a042c80c644014124000106a02c245c44c00150700100140b030700c04030ba01540a89203207841c0d14080c8017000010301030903940780f103400710200455403041000b982e000141c40c0e60342900c40d492032080da00b15030007500394100300c0d00c020400b80038802e030070000d199020030310381084c03510489002c004540c41c0c905044014149035884800510315807124040b00c281c44881c050200442ca0301131005024904180076160062160000181d80450140f01d0058001c20040406100442c965107856001403810742c12a00800c1a0034529040c400402001c96040c0c980d8014203998900010b004085400020f501c40199118000110105500080c4001c181a4624000d80d40e446000d16041080c01100d840c1d81c0590700e41c4086040440c0d01d80e03c603a809a600b41c1e8188402d840b0062010f995440c1035448030f800c076042c004e5050040c0b4003d5030030f0382c2002400c1e003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 67366189 1250 67364939 67364951
    0x110f1206100311030f071a04030204090c1a120114010e0301020c0705150a14030402010e0306070f08130305090d060609060308030414030a0206010915030c030311060f07050d020706 79
    0x1408908003141070714184031094480c00244200005120f800c010310300290010207113010151a1681d80b078080d0311425030b07012141e0f0031100340340c070005040b54040d43e000707881840007039401c0c038041268000611070120354811482d04c9118282c0d2030302c101c1340052529048140c843c0d09112541140c1445880d066041c410805480300301074400f03001400b813494411029004446c81c001c01e0040003403d0071060b4003e41c608105040840340c0244008441c003845085080d2203030755a10050b5640307800d91207015490b00c50310041000207a485908842c04000c2595a405140c613a1121803011410041000300032071401c3c4048105800c026a9400080c0d0107000e0104269990b1541101168038641059403514400401c000600040c4a000c000c2094200c005603d0901c100d5030003510380f40c06000b00f0211580310518240c0e84910070412202454002c0d0a15502540da1703d0080c0419200d050703203d5a600075600020000e162200419218905036107440c1c0c90000c1610110b40294172074541240c900c0d54490b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 67367439 1250 67366189 67366219
    0x70303110d0501030b090c010201110a1103040807030b090c0a060927050c041d010609060f0c060c0302031501030e07062703030c0203060901061a0d02091207140d110f 73
    0x100401c0d001394015100d92019050440006045c03a4200c0394280c19681040c000544006a201c1290740f0000e1600d084042d010900c1100360941c80349602511031b51240d07000200371700c400e03214100d00920842003200c180209010034813443c40403520400010038000c020820041c0500d030002040e80c1142010801c621942d0344402c401c442d0241e44a600d107480c0810140560401c22030f803013080403e00c480802c140c0d0724001c0c004080b4007860090504102809149444081c01402c0c0b8030000e45d8880818031031011002e00c0200250021030b2450f660202a40c40510254000d200e1180200c0b034680190030780d64184002a55415201c00301f90008405800c1400c903540191120341020714420395a40c842103546004061070090080d0a8122503403410704108100084c0640280191400c8904640c603081045000c07002806652001500600440140d4000e180045580310a599039111100103940261092004414074984020038100780040c10394072a160180d42d000c02031000030f0201c00715907000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 67368689 1250 67367439 67367441
    0xf0e010302150f1306050d110f03070c020d060504050a0c060503100501050f2b0b0a230103020405040c0c05100b030a06020d180305070b0a020a1d010e033a0203070303110d 75
    0x217588000009100801c554881e0000d5016100b0401c0168002c0b500b854602c20010f1218400030f081c2c00288420119604c045444907015032481c0703500720404002a00d8070f418aa52074080d0b10b181240c8800348a50085002d900802c1640c2c0246071038000d005000c1d080030010745440e84030f074141410b03801c0d05021152401078030010001c0c00c16820a03e10000107803140c01403003603030003101800d031060000c0d05050200f00e4072403949100c040000100c4461450107800107070000d02c110340000350810705044400d18180e402010340310b4494410402c691a00000e240c840088607000703044d156041d0002d0a541012501e0303a0007a00c84444280c0001031210000840340e1802800d000003100421008690581800a0703001526070107030351820150b15000d003220009000840b408442900c004005c00d400b44140d11904051081990150454100645282030b40210703c081049009600410071825080c80b1300b5070140c080800380c0d80c4c0040d814034101d41c0e030550181199402d0300480c0c039000c0c041c1e000100d0f00307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 67369939 1250 67368689 67368727
    0xc0a030c110415050906030c03061f0b07061a0108090c01050f0f0a0207030501140105010801050103090f0b0a15080705010f050d0b0306130203010507020607140d0e100203010f0e010302150f 83
    0xe0050101054601021700035480c200409441c42030700b006000c142c1c2c035200030424642c043c0c0c1c00b02d282c090341c0c0303045003540b1541d800701e40140c0720284001c602541040700651004600450b660300740240200100011145400300312070401c050740005d032041c1400e5002c1c42c050080480c02c5141642014140c0ca0580095005403550034010f90107a42d040050150a1069401e42c43d2680f501c0e800a604000002e800c120061254a0405603240c92150601c0043c5200b4080036910132140b080c0c604085041d04090400103445c800d844542c0000005c080d600015000300719001070319005990b6103003078800d0b506038014400b9056020384815035003210741e400744071003403085410340b2400391a502e07180103060844030010000401d55102c44107005001c0e802c15121018284000701d039991f910188c4c0700c1e4401070038040c070303402c943c500c9a04050b002c606210b402440c143e5410171031403c142591a0700d0301c10030303500a1101035080313400031112503410f804840081c11031000030304480d460441c80110712100403031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 67371189 1250 67369939 67369961
    0x403080115050a0e0f060c07060e0f03010501050a060e01091721030709150302071e1a0c030402040c110d030c03180c090209031612030f050c0a030c1104 67
    0x210900060240030450224811000400c2c41c105040c015104005007402d21004a01841209444c031170501c00c1c0c0e40c0078212040c899280d0306641f901c65680c0b00103000c070b080f154411445070100c2c00d11500c2d1400c05109a5049031002840408158175203081036401c403d0002d901c41c1040003030304000c45e80811407480002c040302e226000b0101c4204143c2100d455110b050b5900400100400502c00c0c0554003a1018003030703c8425030400e6400707201810980080c4180e501c01001d1111a00303400d28030000241d18401c5e804e01540c2040c03600142440d4a82d07000604403101c2001030000e201003030260605600201c91104181007041f00314500d011164648014220300300c0010f41c070307003880c1c0703038420303454092a944020303d80b481d02d040c11120395a480e1044100e018102140358040b81002c42aa0100b01c1091440005000d02c11416210300c0c0c0420010b80c64081034000c03a12250000c40c6092160342110320314400341c07028220390b4803560740444a00128040a0b649100c524888480030783d00d910410710811 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 67372439 1250 67371189 67371197
    0x303040e060f0609010818160b03060321030c0309030f0f19020607050f0706060f15020d05070b160201060b030c09040b150712030905010c0c0303050f01080d0e12060403 74
    0x71404104000e000c400001c03201e80a0401400000744c181d030008050346c0c01002c0f800c85440c128070080070541c0707031551512034a110445c140388001003401c684d20045000d04820380035650340c2c08660031200442e183c0c240501c000642c04000150784041e0342e00c003031038001556805170781c07400d025000880e031150408440c050110400242901c01040507000c174407401360060001c1e118618040724054000d0140c03c0300d00e00d80e1400080c0590800005501800242005040603148107403513180032009440c1101e0400007503c41c11814046050180c400e9500c042c1e8030207038039103066541c5568409500340b04400d441c1999201d00010520300d0358107000c0c44c851202d06803e6920f841d02134080009030303407880107124010404030714030b1040c03250004211503d8130b420a0031204282e0350782c3c2045004103a6250041c00380c5d4138180c151105540c1c08800071a0031800703554103204a480721440c2950141c070038440c00c0110380c010042c05803510700481c100f5105050041044014180001d2100c3c201a0b080710210006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 67373689 1250 67372439 67372441
    0x621010501090c0329010309020d0209090d08010b0c0703060b03160b090f12031605070806010305010236130207021e09070c1a18010207060c11120301051c020303040e 73
    0x250390510914100c0c2140000d5103401242c000b205e0100030035020042c4c3c2c1095210740041081d52100742034283d01d140e0240991a681c50070b1800c13162218800e03a11840064000f50000030b581d94031406486a15030071001908089180d07a81b6040100040052550140100c907903a01445070b038103050400070258107201c5030303039890f003041007026902140e03421520a403541c1034003420b841000815122000c40c20309480b240c0d00d0081c20418940b510a0748080d09c244603910010013040410b4018290940c0c850029490340107409c1905262064201000b01c0380300088003c0545038a45a080001d40c0c8a40749401890070580360007191202d8480d200000100485003241b980500303204842e40d43c051030901d0a42c0b4400e03010368844a0600c0800b1210050f03c107071030042085201c0c4c0800400410704800004c541c0c030340c15031411002070011324042001040303e0601c00412410f0100f440f0a91004000589207140c2c01c0c103080010f102035041c5140343c40b680807480c110058500b04010006420800903c02503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 67374939 1250 67373689 67373711
    0x709170d030605060f1c06080f010b01020c040e030304020d3e04020a050706090201020c0d0501140705090a0317130605180a030209040303020a11070906050f0604030506062101050109 80
    0x5842c25980b015004403010810260740c402010182ca00c50319403081c24410109080070b0701d03009013075150803002960203144043d034482c60056100c0d04000c4820380a036200b400484080000315171070103000c149503030000c0000800500d07003014507000c000d2107588444146d140340ea100100d41c20700c600c44018922045031a007207035580e1902c000d410b40c2d2000c4505525190910100400c14020641c0080c401d03034aa040d003204580c02401603001c0680090172036843d954080c2880b41c0a050070040401c1e9002e1031f1001701c0c1806114030205ca425100c09020340851a00d95910300303580c14001d01601d0141a410b00222000a2420f62000000c0001d41c1c2c0305a165034802c10345040841003200158868107076440108010b0711442c1500e80e2160f0582001615088a0141074508045459007a2583d0056039404a40005a13034803010554400b5111300d280b4910b031600740030051069010181441c0d01c0140010207519103011400070350141180e0044130300d035042103000c3c20354034282c02a0f420b42e911036008040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 67376189 1250 67374939 67374941
    0xd030e07080a0f0c0308030a0501031a06030d050d0b0a08030712020a05150411130203010914040809040c0c080307031b03090b04020f0d0f21020a0c06080709170d03 72
    0x909084090192146018251030340c0d1400d50704000c1540740d4141d0041c0500c01d1100c41c4ca8000c540240040f5900e241c0600b441004102c02d000c211070711000c0c0d0280a039000b1a080241d031003600003500400803000d00ba40c054625800c01d5142100280d141c02c100110340d100d10440300014010302008544640c1b01e03182c00c03c8a64034031205a411907008407a0720707001c2000007442d5080c0f07141010310f001240e2640e090595081215880d5a80c01c071340143e400c501c04800070342c0254120b41c0413038001c122040c0b41c0e000d14003e00500342c0e009003011000f0b100800c4070340340c560b201c0892140309040151804200d40d88100c126002107c0240109030b440f046a0382464014443c0a544101490208801800c9075a4900c00140150004e4040c0c1e5000401c1807054807000003c02605410240981620003107141c000580c80d40312801002c65000384011460450000a0441e955984109103440b03850030400120381c800801000d00c010452040c1000400e40c040b548220300701224a07010f40020070f01494058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 67377439 1250 67376189 67376201
    0x1112011a090103150801090c03060510060e040e07030209070e0108060f010f0f0306090e010615030501050a290711100906050d0e0c060309030307030e010b090708130c080d03 76
    0x8180294039540c001001001034045909040382400c0c001044500500c8004210100307030450b0605601c1c181d80314050119100c2a60100d0348101e000b80126501c0340e08858542d80350744114004628400c0f150a15841c1541001100e40580022224903c2c4d4a40024a544809461403004502c5901c031101d0325590003280241d0001e81038445001c04001c07480003c3c0742801c3e81d80030f01c2c1008614071040c5241c2c1e11903040a0000c200b440300501151618129490007418070b4460807000c00b400141c21712825021b0b000d5981207460003081407200c02d1501055a10700f076400c0c4080151301a05c0f0100300790344960701d406004440d004080c2f50200c1082030081c841c2c4100c6210001c0e007480408103081214940c400c0c02c589501d008c48001154020004c4246483c0c0404081455809200482001302c415030000c06584140810b45e03040c03021164084145088600d0001d034290408002c1c400030322103500440249400440007122000e0616040e140d00d48210b00c140c009504940208001d0b0f0f140a51502031a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 67378689 1250 67377439 67377449
    0xc0c0901030803060105090312030903120a110708030405010603080d0e0c04050402100c0516060519030b0604031112070b0d0b09060904030f1202030c0a030f05130204050a090204111201 81
    0x181040e506584400080d800018070343e504000c000a03001249480c28041c4a05801c41484042d44070f08010300101e850f40c2004c402c1200780940440011081030702c500608030700d082001201c1d031804040b03884400c400e0340024001d480750342d00c800300080090b11410041252228907500029001c0e46c400c0102d00304801c100711148101d00701001d1001681da00450000c40c100c0c1410040165589c80c0b92443c01c14071904c500e8443c0345442040081c03e143c100f0000c00c00d150804064264400b800c00c0182e088072645910150080d50500007400041d1006005800e1200010a491300c0150032602c1c9520f40400c40c1c002c51500b19010400c0d89080410340622005080200d1308019203142c15004074811800041000c0c0030071100b038200c0b811a41c041c068482c00799602a00c29540ca1130141c1407a1081e51160854000080ca040ca0400e41e0281921515000c2c6241c8029241d40c00002c0e001c000c0a0311024081000301681c81c652400184d6540c0302e0440b04070a8000840d4407104a940401802281680700c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 67379939 1250 67378689 67378699
    0x4150e09090627010906050c0a0207050102160b0319021305040c030605152809031509030206130501150905100f1206020f040905190c03060807120f05060403050c0c 72
    0x500c84054900340d1007046a500403019042c10b6034055050f1030243c6005100582090f10b400140b1180c1e044c2003000709001c400603000c444200741e0301c03001207070f503200c80d03640c1100105d84050043c003050708104011a000004d1780e201002d00038441c0402012648a0f41c0d2812104280c400c0c01c00607400c182c0a048a100010b0400b041280c2c5840f0124a01c002520301034207510800082c801040d0010840741208480d400d4030b140d410220445010305809490701040d0744401052120003000882c600030303e00c8140e0303d0b601904075501c4140c004034901d182c803203003250f2654a90028140c2014088160001404150004159410a203084d00d50395039042c1c01900d006605c50350140302000c110381c0e8403503480380d10403c01a0f445105240756103160185070803150803c0d003010300707011900e0094070303000b81460b0108908011070010a181501120010303c00c0ca0010340184604010316175241c0030505546006254900d1032036010b541c0c86040501c100c0341180414400700301b03803046030401c120380b0a070100d017518 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 67381189 1250 67379939 67379941
    0x10503010c05123c010e0415050402030703021905010e0a0506040b0f070f0f0201030f2901050c0316120237020d03020c03010b09010e06100504150e090906 68
    0x2000400c030340318007011810030400d804003244a94210000410000b5a0701c0c0c60200b00804403803a649139201c1c038407040481c1800c0ca2001081017079280001e01d005070341c400000d0403800c070110360620140600420990b8940105d020020142e200d12050503500441c01c0b074800c150744c0c00c00300050321a0441400705401602e04580030300144d141c0d00c0c1102c09456020020a0301e455a40c4018840c0c1d200760b0b0350050024044219003c00c211400c40c207490094402d0300d0500660030b15109500c22103500e40240781c8121100a0301400c40400e0201845c01e401062604c9072900d4581c01482d4515030041c41d2040c1041156400802840f001e902e503074405448034806040380f42c210101841092201412908a1101c0005034450074032900c4414600c0716805884500c0143c01410080e407503070a200c800d14003950034940d50161503e41951014143c4020103100170558450000340196030801301c56402c00e1280800c00400d0034800080e503c2d00900c180d07520031a030fa184400c28004006070203019282654401c81c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 67382439 1250 67381189 67381211
    0x151f0e0118050c070501021801080606070507030303020903010b0901030c0305121c050c09100c0b0603010e060109020703020f1507021506010e010f05090a06090302090106020606090f090a1e050601050301 89
    0x41c0d1500001904080101e455200c21500e084280700303240c00104198400a0540000d1210381291800c0e0740090701c0d50146682c5031004d12841744140c040040030380e08080014000a400780e0301512444002800006541c1c00400105100c1c078000e81082d10310b688010420010084100312815181101001c4c0301e003499110000c445007103076903640925a07c1e445100151801c042402a6203412000400c0c0c2c0d0184110010003510307803002c0550a40b060050840020001d0a050243d04495103404008207100c0e071034819004001c2d00704030805c908500405080c003094003400c00844a05204100300c0c80580e042c10040645802d10354000404074400d54800c024190fa0401e5004c2142242801e11080d0318095450480782c52003903a01542d400b07090408040ba03060390004084040d07074805d4681043c180d8031517000b81d942c1c3c41c08450942c1d1000c0048005542c4880c403110a42e040001102203c2000c3c00e01e035507058003101080c109945010300c400148050100401805005000c00c0c1c1c000c0000c00245 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 67383689 1250 67382439 67382459
    0x1181205070305070909050a0b07021906020d0608030405010e060d060803031602012f070201030912021e0601050319050106080312070e0907080604020a1106040809180601050304020d0203151f0e01 86
    0x10b50015020380038072701c0010440f600038441810745140d030111202c40790000d4a0040020341001d85c29086280c50080003140301b40f8008126016105c05855565140c8080c408110190b84541c00d413001031922000c000602400c1000918000e0088034888140701e40c01c008001e003102c00f03030054901d0310f8500d040c0c5000c82082c1c4844411612400041e0995075001e9400142c0103007074a860000c10b10303a900310b001c418a9501144600b0040c0210141610b5410440c5c0280e075511401c1c081d19500d03070400d40011100190307069008602d01e01c44e8001040700b40da5450880e0454020b0345500c2e492030841002c1040f407513800760504008030710031900c1219034200018000c000174001400c05c1c0c05030b580003e170344100b14026400c21024400690440b07040e880c0529025a0310340018500600600d01c4090034101e060300444010302c26a0103039680d609566650f0200503080c6910801130307030540101c0300035800a0081c0c10805100307424078000315014100030301000122043c240e02c40199001123a005106070042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 67384939 1250 67383689 67383703
    0x705070f0201050d0207020a08070501020c19170a0510020d05010b070c0501080c09040e150c19031a0d0b0f0105030c03030702060d1103070801031a04050c0118120507030507090905 79
    0xa180803511016107130503200c005d20603038030040c1d8882d0080400207007030b1078009a10380541d1020383c00da505071148e9205000d0020064130f4551304054070000c040c04540c2e0404001841b0841c2403040303c40c00515a01c1c1c1c54103041109500910340750300060005081209806414010800c00805601d02003443d104d000403c40d560003070034108200000840d0408041c6801ea4541000082040004c1c03c031596074603640704504d04a801d03858507284e002980850002e0f0507071396103449c0c0c0ca5003e408401c1c0da10b0220005c16802c080000890b60890031921140c507400e041c40e8456105210800700d43c184000824000b50059220030711079800341024885907107000c0300b5240c0c050b0b4181d0707003607031070381200c80c4000081d001c0083d003000d02ca400402080603456000e09001d040b81c3c001d4843c0710a01110010550140c60110b502620903072000c0544607065100310781d882d8808102c2a00c05514035107441c01d810100301d030410b00b641c6991242c403007031060240c03c0c45424001c0c2041c10040100e540349903912501d9200d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 67386189 1250 67384939 67384943
    0x913061401092d1a0318012906040e090604030201060801110703030e01112817070804140601120201020105160903080a03060909140c03070b040b0d0b03010f0e060705070f 75
    0x10311460440f44500458081002030b007510a1012100341c00b000140c035058108942d1400e001c9400410070b40510810312600d616806440d0709412008001103000b035138803003a01c0426400140401c00024005400496a030088507004c0c0541103605190900a00391080d0360070100150345052043da0481c1c2e900d034215003500340e01d400c0100f80c06805110260041086100c0c403000c0440000b080001164180200300101d0101304d55480501040b40e0111580100708010000c44001c400c0866819405620090b42c800d01c07404840380010940346000341030082c20381c40303d41c0c0c003030b0b021054a003150380a02516a00508a01e81c44403000b01842c80200011414030010f04990800103114444a1007500028050030300c180d410b00c203081d50b43c64070000d441480c40b007010290145665083c45842d02081d004211058220014102818981514002c0d4000401c17401d106569040791000c548081c064801c4454140c07800207a4546148040c5040c01c0c002000081001001c002c03050000f1207481503c15203035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 67387439 1250 67386189 67386239
    0x1b030c020706140405040903091d060109060e0609040e06010801060e0c031602070f0605090a0e091b0a05090f0702070b0a02030d021303061404030e0d050303041205091306140109 78
    0x31000f01c014100b610031500543e4001d81041e04042c10701d07802540ca001240c00595150031301401d40c4645500d00e0905840742c038009401c00b42c5c00c009541c401e20010b00319460040455140c10310f00790004044644d0b41e800b2032411f81045004011810003841048c004001c0070854036110315092030000361030f00c03004040c5d480c0890300180b2039040c584204110310180031041d0301c2901a83d12010050855009002103d00c56480303918007064580e04600070340d0141c0b07a10701c000c01040d00407062601c030317210703080c04116000454828009000c0c0c0d07590545030300501007441c208489082603d0001d00341100740d002403020b584204808402a45c0c000f0494003074002c162801a19004c07400103900003032903558030181926041418100c42a04001381c00c5028900c26202d00c6c003403800d410107214540e0426031016007590028400240401c1c40b001c8025400030591814515010f01391000a0703807401100020001d056640000740510880c01da50f0a42108003400d0035407602e482c00c0f02d80d0b601c146c024040116a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 67388689 1250 67387439 67387457
    0x1020a02090405070e0903070c05060901080609040203120d051009090f0807052112220803130203330f0403050c07030210030207020102060109021305060f0c0706031b030c020706 78
    0x400004c0c00020007070180600c0c1e903111410320a000b41d0351780c0c1299009484041d013160001070340740350100450f822081c0603141d1007110b0352004104410504010026030309070151103100c4041c000380600400700d403481c2c104000b81c941442511800070b821a500200011442d0461610204104484481c950350344540015550400c070f00d0700e1410103c2185088a15214940801e840002840f000c0e106075048107082c2c4401d603585d62104169034400120b10b000441c1c07040c8100012079020b0004580c080d91800d10f01404018a50210389051460b1000f0303038503007460102900d2040360b0185080c40480146540c1541401c240e0a80b400d42d00002d0300003000c0c0180003409034070b00001804080020b64004000114a101c0150090069403000000b240103001d0b0300008100c0829610940d41010240146001c1b07440c184028400141c0c400c5800e44100078080c049074940910401145011701503a60700410301d1004d00c2c00024090001c414080145401d02c503011001d05d0380090928100c5406107090640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 67389939 1250 67388689 67388693
    0x806060d08070309053c01080109090323070b0906040203280b0405100c030204081e0312100501031d0d0f05070b0103050607020c0d0c030f02130f06030311030901020a020904 76
    0x80451030752003150081b50381d00207114480000c4902080c01407400d44209a85444031084e805040241803585000c10b08507001440501c4607544220800d40c4607041001c41241500d030480c40c5001e090441c020f5100c00080e40030104003800d00c00b250007010010051203542001c0e4002a121303980f1020140141120500038012102c40500701c1c1c0c9107030380048110295041a082c020740b01c03c241c00584070100c0c100514140c40ba40729208890071241814050030007561802008003075a031149500340071a00c420301a141c10a0300002e8294014500c0301c0c900c02d0442d14020014041c1e07000c13001c88001d02c00f801e0717810070380403400496254140c0034203103400a4508041007084e1344074000d9960140001c60200d00100402000290310703402100544c0803600741c08921410004c81408404d001044450607400400000c0e00d601c004022442c0b004044e400ca81c1c0e0250701010031a40f8581501c280562503400030030503d500994840800301c4030402031403070002c0c80c20010390364211443c0000e009124040000b42 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 67391189 1250 67389939 67389947
    0x40201080a091e050c030a03050706020d0204080303101d0609060d020301061a04050910030201091809060c02060a050c0c0c0603130c060206070912150e0703050303070f08010806060d080703 83
    0x4a010ba00c880300d80c000800704100d100c0fa036044040308403020301c11054400c85c0d600d00080c1035201d8039032583e00c4910b002e0040e5603074406500501d00c2d010405400344404203105005101440c03113a41030000440d059890b151111502d8039214081c0c20315448110240181c98450581c2c0547c400300036a800750300000ca03480801c1c01000d29500446004d40701d0304582e007060901030028002c0b55022904608030340c42c1c10340d00310070f581035030700c8002c0c00b10b00b104208001100024184061803412030400149000b1162210020348083d05401c00042c0c01880400828040c9886207640010781d1a1001e0b05001480c1c0750b00f541c5000d4035111910030b11000c0005042800c0c20000303009916444416940c1c0e03c0e0307944e540030b5503500c0103403295000320340d8101e40812865005c000100d00580c00510488400412400e1400140600100343c00603000d010804804154100000d5000c2c0740d5a60300c0c110900e82c0c04100501c042d0068210860b560082024044103035500031145403841e412152050741c8000a2400360307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 67392439 1250 67391189 67391201
    0x10b190c02010e06031003060f11121005060d0e15040507060309020d02180405071202090414030706090302161a030c13030b01030819050901091e17010903020f0d020303040201080a 79
    0x13a48401c0000400040c00799006000040328070504041c040360b841d03070302900107449000030181e003402c000f0712248040300404000c107500002d030110542ca12a46a40205445900c00401d442c42c268441001d100314080070400c451242c401d100a0503501d007040c2d9212900c40905104030810036807904039000c02d55440070b1a45d04000e83c010444154801040040680240119408d82c0d0318018039400190504041d010340031040d41c01041c030115551503540702030020700d02c3e00d0b0500440c441440500e0005403a41326200d6480e000350000c14400c0171625a0421400003504504041856200e0002c0c40000100680b9001044500440c3d147c4040000903540c03010341f030740080c0c040180302c00000240118540201109000d060044500b020380c9101514603115100141d1b0004240301e800b0400e031040030035a90041000c1c2c540148000c0d9444522144060401d00060f00596460082600f010b4040160051802020001d4034141802c800081c0d140c4c00300400c041d040c40507890014051803182e42c404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 67393689 1250 67392439 67392467
    0x90b0f090405100501030b0d0809090c07140a0204060b0408120901052109072c04150903020c09010807150503040606030204091b0504020f0406030209030c0d12020105010b190c0201 79
    0x1c200a141c040e480f0380c41060382c2d2041601182c50074040788900c1c00c003c81c5058480380c0090490303240c84003210501c4601c190050552419601c01d01101000030184400382c0c00712441640200030110003070041100305c0ea510f601a42c640d9208020800c1081004200303e1003a8144952558840f500c150040e01c076072044010b01c03090240c12007481c00410140c1e02000c1e008003224030840b11683c0d2110514403650807540210f441500f52401d0030784000840c0801550301521500284610309215124903056401c40e40045000d41c0084100c42540c0c1801e00c4654014004c4000070008180380016811031000095002010408000005070034480c458000400070755002e0001c05c038601081c1055003080c0e0309020071020560308988000744510740b81c000d441d03040600d4540d040c50945086801d5000b940903c81c0b40ba0103006408014107207503a40d1703941d07800b0240181e0b014410404041c2c402401c40364142c0101004c584c0070b002c010b0b50140c078940a450751704110301304190b12103424001622080c0d104820 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 67394939 1250 67393689 67393691
    0x4020a0b1603030614060d0c030f02031509060f06040e0c070f03050301081b010206060d020103090602040e060102060c0a080402060702041b05130803040b0706020906040f140112050601090b0f0904 86
    0x101c052864511101208054000e5030100440c680380d030882076403600741004075607000b2001c0c030030344201c6a01940400202001c600b0002800f046807000803060360421035807904244100d01800886050102039140d1010342150120840b10f65a00011410700a0740100d901d100441e07000030f0341c52400f04040f42d040640012058401c1d483d180b400500d070741d01c06d000303022543c0a2340322000700303240c00740c09242c100c0c420580203800701c0d56807801481103108038000140c2c100350322940303000045402440108013030041002081100d01e020000a0719040c0050641200f21004100072424241d20010036508241d0450380e01396501140c0c000a00038040b1f46080d03a0700d82005d0b9075031103d142e811800410b00d480074184a8024a41d0f21071403103031240070720f1081110741e075800c00640b400922140e00615612000070003003400c1a803601c0946a40c602e01e81c10107110041c090040311213640e0020102d201c4031811410620452800714002041c3c0884c922034104911408222719a800d07000d04165080300c000908 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 67396189 1250 67394939 67394947
    0x1030b15030c1605034b160602040e01060201290112110d09030e0d050c060309031303050a060b060301062c030a05100f110412020102030730020d140304020a0b 70
    0x82244540c0d090083c000f02c00c03a20001100403000e030b0b1b8030641041e22210300d0340c2c149015841d10004009500185140d0360b110140418000012481d01c090b0000c0c050300c01c41c2494560529002a0840f034404a90b140d041300b40c03080a00c044c1d80c0d0904c420009140070f2030611041c0c14403c88281c0604426a4298130241000c101b0001d05c003120348c4003020450081c0d940040e02c8a203a0284a030b03850445201400a400041854010b4100400195008411113040b00d1030010740000c1c03500c1144560304100d0705604003c07401c40030320105015900710380e40304586040c0345500d000000ba02c2214500b10321500c480000c00b1403140700c640141602d94181c0b000d001e40756204a14586542c4442c0c00b00d50070025185048980c140b110450312810700c05042e282d5506150905248071003484008001c02281148010070500c000154021304400302c440300382c440030320110b05484107001440c0d280500182150701c403203920300e90b103a401001500e225140c690740c1507a9403103a0001c919580340c590080c06101c04002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 67397439 1250 67396189 67396207
    0x1b090a1a0702031507020d080411090f090f0106051c02010c020909100f0606140c0703080d050103210905150405030a050a0b0a06050927010606020c01030b15030c160503 74
    0x4006020803407007242030307810600c18200e0003144c140068550340016400744c2e10f0388105500850245400c24092481e680d102075110700040c1040310301b1202500c48510200900080050400c440710101b00010001d10210b0300304008220001440e0503040140d0305d80407000c00a69006890342c118042d00034001e14142d00e0100b01d2150f0b40c1000c019050340b1070b803500742005c1c40002e003403240009846844c0d0780c01030b003d01050f004100d680c2088030101700d94090540000006640c0724020040e40d030072404041480e40c95401c203a00883d402e038081002c0351352925009440290710003008020b507103088411141e1891989141c3c00305004a82246d0b806120702030200043c820001210f0402c0391085191841c195a003140240c2528041d01c141030300300c0142c40c0440c103010090310030f106c104c540f940c007048404c0340c92007140c900f510281d51020001d03802440400405503854040c072001d414042c1c03404601c08071181e0002c1071510004103248030000b00882c1c4d000d900041d8080100100360032504232078441d4108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 67398689 1250 67397439 67397489
    0x6012007180504110f03100603050c010e01110606060a0c0507080303061c050705010305041505070e0405070f02070909051203010b040513050403021b011e0309050105060303031b090a 80
    0x15020780000100400c030381004001c81e41c082c0030310442e0302000f02d80310072410000388203180e2090114554580500031800c4507040c117074403840b4000c0d400b40f001440c001c411600094100450a14014100026208000d911004c006280c0b600114280d552a6546c03000324030480e940646642c008105002d00d110001d0318900000156001d00340440300440681d020b441c4d402d9480809040041c81508481b03000c110560090703001680c081c0c060b10b88a6600741c03420340e0120440300115200d8002c2041c1c0310b2140d0b51402d040c41140c0d4800c200342400b82c42c000c65001e0107565201c9602c01cad82c00450302d07890101d0800009002e070381040c60040950300d440356112201703814940c2040c05140d008424545a40c1c40782199030061900954040c0c0113000e1a12010b01d40d521000b038a0505141071001c0f0428900311b9000007911594400d40540d000107500f4203501c1e005080d00d4014008a109a109005201c00302c020050210912006a00c61907941c043d00004180b1846265110f5002c1c05000740503500001c1c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 67399939 1250 67398689 67398703
    0x6090b030705120a0303050a090c0306090501050a021305060d1b09090b03070f1415030703090b0609010510230403080421110d0501060302030a050c0109060203120a0203060120 77
    0xc80550310415115800d101003400b107010b2444040e0310030000b41020038025407050341c00411091008c1a030b224680c481034015041940121403450381d4026030000d0040a1003a2a0060202581540350488103018039504864500809101d07d0b030001d0540e030319076950f500c8a0b50741001d80d0883c40d085042c0c81b101425011072841100c00e00c80c200075410456280200750340702510305940d101c9406604082001040d001f03c0161642c01032084104582010428806580b01d91312994011130038600354a000f5505860191a1034041e0440342c00511003942d80714518083c402c030303510f4200a0200039408082d001345020090b6400e1303034800500403091240440060041d43d29030300610341041040c0c003c40400200b2000080d082031080c0194107960b1906107039224400d07000d103002080c116102d40000341000c3c5201070803143c03584000c900c0c03d04c550f04030084030002c0065001450a10500e03040541130990010700e48100030307600000003007150380110340e049492a01c6064021402c011901c3c49a66404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 67401189 1250 67399939 67399961
    0x140f09040b0f0112030512040204140423030f030a09210c140f0a020609060408011113050303040803070f03030905030a0314010b040b0d050c040b070803061003050f040f08040503010609 81
    0x8800000401e110008420315542240d040d1b5070306240181c005010070041e0800b0388102c0e0b010b0303102e180440181d4801d80c440c9002e940952603405102c404005904c1c10039110901c0120181c009000d07030703111400d101c0243c0c1d600588201012900c030790140b40022489012003154004c4080e51040344101a51107032211a0461003000300c14141c848482003a96558013020301603170725030f204808200c0141841000360200b14800351803941070603207900e030f2507081d14154180c4044108000c14000e00050003c401d44d0010041640078516003030400d41100d440e0300c0761060281a2500c121030002c2054841d031711000c0180e030000305403038171a181140020050444c440c01020244104000800c029558034210b4003202c628580081ca01050a1110809458000c04030401641b0500c0009000401100204a503d1040d0b520035500d183c075400f080a400903406440f400c041c0380004018072000d085400b5604250040c010040400240c0780c140d1080c4074540000303402d54285500010230044070741056864030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 67402439 1250 67401189 67401211
    0xf0309060705030f040f03050c011e0f020a090317041a18040b01090317040801020307020307050708120301090b0a08031c05010b07052104080d092c01140f09040b 71
    0x1c0c031501c10403501030000356080d9001d5074140b00800c1c0001c0c1c1141e00310651a20030304026040c9101d140c8803508491620b00390f03a003406154696100c0102c568850384006000582e0110708041160030010111402c6000040c00c0110032a2100d00101d00f00094070020407203045909a01079010030100010740007449000c500c0b01d2402102e04661400380928003603100b042e9940c00c042403550310b502422010a0503182005001004040756080d0280025071142c26035400555540e4107515050389040c4590f03105848c1c5401214051f403c072400c9008881c111184004007007aa1801c01000455030515a482503006100c0051544443d000d03014220420200a107002c1110340c0c0e0700c040030085442000002000360300500c8941c00302d00030101580b5400c110090702c0500382030700c1e01241361419858108010100e64400c13401c214454800d030700c4002c0c04411901c0762280480d400200c00c0a8003060142c1142c201c5002d01c1003210b925107038803410b0a0040200850b280d424541000980b40307070150f480030840 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 67403689 1250 67402439 67402441
    0x90e0103030f181a1b06091f090506040302070e07030c05180303090a090e010c08041104050403140d020d1b020703020126041b06020d02070306090f08130801050a090305040e060105040b0f030906 85
    0x120717170100e101d521903c1b030440a0010341c070810000101c0c4d41040a1032460b000c0d0b0b111011b4000c46c0c420410288168840d80060507c142019107905041000412650805090502e100241d030b900900392469903007004400e0402556140010741503009000b80a41c201c0c0e101e001c00656485990894542000c0d004003c00c0782d0300c085041101d1821003202d01a20054101c0006000c0d414650b01c069807040c028a0412000a04560040102d41c0074040210b00d040d004500700031400450320503000c1401214080e100c0c20000f20350069103d009522000e8184680308000416015520344101c4403034458802d61511340c502480d080f09507094001c07244600951214021600f0707800000c2800001c0030760b80050285500d140d50704000750900700d504035110903040e40c8646c0021081009003640952298208110a0401c142242180c00060540f07c10358140702e200c0b030120380c020040740e081d42c15441e01200070307946d42c40041c0c0b9280302e190301142d43e000c800100f96030001c4a04011314000c0800400f51011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 67404939 1250 67403689 67403737
    0x10c08190b0105040302060d0902030601080105101d1902040906030804090b0105030c0d09060b060307051801050405060f0d110c100605040207020a180905010c0906090e0103030f181a 80
    0x1201e089005860106408000a002500e041c4002c0c0401421800000c01c0403030043e0f010908200c3d0aa0101015030b46820501005904074412940034103448010803249941c80c400c081c0c00d4090285c036880010070700e6240c202603500a501250041c044081c002e0003101c0da00c0c03070155200c1c3e015200306603145161a8000f40c076036100d48120b80c002c03c0c10300d0302182020183e4074003200400b295182160b1059845450714000c3e1141c9019501c1001c40d40c41d00d54a4200072503041c1108690801400d0401408100c01c2c00669622001d0340c091401070030040b0b4440040a88400040c10341140b203000e403410100b600d2040c128009004074000304421800d1100035901d9080c0f00c160b00035000000d6104411802c240006060b1000310030b4001050300c0041103004007074641310b0031201401d00400c0004d40300c0342c081c02000e8022808000611301c5840101c010740c950340300102101001c0d40028100b1106443e09504042d010802c98050f0840170312060a04503400b0b4205100e901515600e800c2c0701603881c620780 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 67406189 1250 67404939 67404941
    0x60807060c03050a12110d0e0a031b1a0103050f0f0304050102070303030b040b0901140a05010212071b090e0105190e060a0c050c100f110406141605010c0819 69
    0x42110100e84510035503480740e80c1c040d03d941d080365108004000034880b0461070b100c054025004040d00410b49a6078070010f8411820960710031041d1580c0c5503102240c200000390780030104071000c0f0010f8000b0704143c442460484e005006001c103140105a10100100c244403005c51545542c03a00882181e800c07203030216803240c070382c09103108050250b0020601000131034003a4000f140084002000002c88803296400140d503420280c2104190005445100c01e9506100402c94090300d8240000c10b082e08e05050000001d20031b402d001081035025460841c4003100e082040e00c0a000c0c2100c0c140708400003410414000c0c8421a420600c40381c60410700303011300280d44596101510301401410365940c07a28106d00242c048984007508003c0d0810400d2560342c42400180038100c2401004940b01083c0d0607400c00b512651032040c02158400c000810403290030017000700f4003520f0508600d0311480d000340280c0c8103695040c03014180d0350910030300b0b58159074400c0d807461160900401c0f024200d80d210007424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 67407439 1250 67406189 67406203
    0x60906100609230907020c09090a0b0112020103110c0a0c060503010e0a0c02030c1b030106050f090403031812030902010807030501080304050d020307080f03030403031a090a020c01090203070b09040608 88
    0x41e0105460940500034501010032241140b034000c072441e40002c00e201e010421650302100c002c40141c110f50b0305040b0610340720b81c0c25500074040c80001d20541ca01929820f16500041c45241c001950f040e0300c00d030071a4000c3d003205e101c07500c0c2c85054075207d21004003004d449100b00703c41120461003101d40410401d02540650f4140e942d640c12000b1079950f80303d03428006000700b841a06c2588402d00c04a41c480d4001c201c400d0700b03120b05125030b0300e00d90501c40c241400e440d440d8000521440039205510840e40701d510040d136005030145404124000d0b040b40d056003000103040080e141c509102c500107007154254011070b42c128400e03030341c012840c0d580120440c21124207008140356074004020410441ca000000055068001000c2e1250b42e69a001c1e0f0610340301c40022150140e400c0842044241501846680c0b00b69041c0c0007440c4544a03050002285420010604480a40d010400f40303007016003540440000b0784c0c050100e654940d11844101c260b03401043d140e07403080d401c015001c0707400325000c9140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 67408689 1250 67407439 67407449
    0x4030803090c01140a030203060409080307090f0b070f030c03180905040308130b010504110c03040303020705210304150e040c0801170a02030d050a120212060411030702060c09040603050f06090610 86
    0x30342d05095030701710100d0207540080c0085600603102c01a410106400c6002580038101c80d0320303002c0c5070718642840034031040c5003a4850030b04042e0a100d000c01181607045824040c59261411000081107860141d600e201c03128420918500700190100c1c05408940c4003a000e5402a10f50340342c0c9a5601500318071198001a001b042c08105000403c40c5080c943c00000158060081e07440c10044030707041d09842c5801640c81034006a000503400c00980c00d000c08004080c01c3c011a20314110400070f030390241d0740e2180b840350102d090940f00546030304074400c0e841c80f9640c503002401405541032944006111750780a000d18004000140c40200049030000f80154296a019000d404c03805040754040e19207070840041c2d4000d00c0034082910740c07050b46910082c9100d141014585100c0c0c2020390502c003c80d800825010042e2404000703004c5e400343c0004079140d025070300100309951032400c0710110b4050519030344000c245214402e40010300d00303c0458171900c03442800c41195000e9548004d07038030125110b8856 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 67409939 1250 67408689 67408727
    0xc0c03031512061b092407020118060503010b0a12180204050c0c0703080306011107060c150504050c04150906030c0e1005130e0102040e0c1306090b0a0c061104030803090c01 76
    0x42d1345030318043c90024148112000301b05a011002d818054030419240b0090b4041c1c03a44001440021980c1000d625058401902121101142040e0010302503105c180120140e0802c0881c80b40d0f890b612440d0001403066444c0300a00240800e24101100800383d01000c03442507080100260000300c515003960020050310005001280c80d40d140c10302c50364070240c20b550400020f00c118400c004410445000100700c2543d07282c1047c142824002c055100c1c0024019a103802c007018080485c000040c012003e090841e4000790f00500400860000c60540e400410503901700312000080c0006c195a440442c1c0a980d0340300c070160364811002009441d240900c0384e2081c02000c0e45000c11245a01a00c60b80076000001072515407134941d88000944c04031440c544800e00042d041d904084165190002000b4034286950303c40c1c10040040701074002c1d141c40b00e041040050074030040c401550408200b4286410707042d940c3c1c2d522420301240f2540200c481201900c6800701425565100d034641c910400e2103084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 67411189 1250 67409939 67409971
    0x30b0301022a120310030302010606020a020901140d0210030f0e01020415050304150f06090f0b03061308070812010f080a02010e0904050c0a090b01092106050c0c0303151206 76
    0x14000450040306080c00c0304070b103d0041400a5070310b1060066000b04c80600509110310720b1032a0090a4030030755000391085401c004c41d00300040c0c0711400c01a05450180419500006c0c20101003000c2540c800701c0654480c880d400310100c1107030513910010070201c000e102840035507800c40304903080c0e20852288440240880c0581c00501d840764020b90f0b0018420ba002c80300c0c1c40d5240713135220282d448600c40b480c9010b644030420881000d1a2003245800164005c06120038540d03540081d4481a0003000302d0380c40e20040104004209829003101c0200c1d078068031a54555007a030707185000d641000d0181c8040410b11450105d031004001500c0c0360600e0313050b03581c650007034240c5040c4004540302400c11204c61059041100c42682d40b00215009000d9100000030f00c1c0c1c0500c4001406080b155200312205580014142e802c0380c480c104403c0903c0c0c00c00c074085129112550960550300c02c81c0801040d40c0408800d1060b09080d002460300903c50840f041816031040b5801c150711441c1c1a00c000501019a030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 67412439 1250 67411189 67411237
    0xe1b010e1207140303070c0305060105090a05090a020603090f0f01150617060105090103090204020c0c04150b1917010e040302070b0307020606150405180103050105010e010302030a11032b030b030102 87
    0x50000003c0751405401d4034103010540d901d208800e02250401c5420b41c003d50b00604c42400c0070079200da40614080800d000606055030415194140010041e0148000100013164500200210040038402d1411960140360950f00c2c1030007094101351820703101d02d50303d00c0003030030900c01c4204a41d00e01602d041000113440d02c100655030307a40403c213402c0c10316844070304280240c1d07514406030281021103400b400304900c0200c20042142c00c02c0101a0424244000038010000c0617001c0e00c40a82d9060390031145c0c008091415900381d900c10391010039a46501c000450100102d1000c1da0085d0b2180e001c40e511a0b40780c42a45085000440c0c1d9400141e00080000d1100d140c01800310b01c49200d40d0314200e00c1c00c1e495001065003034818110405100c80c03000010001c0000902c20307680181580584210a035046500003a156076200c035015020703000c4111001041d039028402c0d0310403500d0350842c0c010081d01003804113207510182103030803001c0703403910211080d5400d042c0200c030b5041e1030004d08084084091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 67413689 1250 67412439 67412459
    0x405010b060325090513020a0806060a020a0605041506170f0c090601081306020f090118060e0d05030408070905060102010b090118020715020c071a09150c010e1b010e1207 75
    0x20f019801c04105660702c001505480e07005103410a4a14244007603030b03852101d800070381942005400903015400410031400990750100c1c42601d83d0394440000b107a55110742c00c0c20140c00d400b0b140c07048095864a86d00280584010030841e103020107400503200c2c0c01100c011000c1c0c50380e0314514036a42000342c120000c5d03901d6100e50140360f0f108040f030800010801c155100c90007288c00034544103c0003a00020100310a607000940400006120b0307002d0b803110f5041c5a4003c00c0c08001a881c14056100480d2440400105000380c0d0060142c0f00119400203507542e4400303001d07003010745002c7e000d546841083d03081405c0c414030444c184c84a801000c030300858001c940760001c1d40314a10070b82e001820740c001000445180e0005022000703038280205501403d0041e242c251101d00e0401301404501000400d03090748401c041da04007120119041c50711000190400e601420300890108400d000d66984000ea61510090940084100383e1303c4861060040c8148010614000c80a50490b4482c0c0001c0140300c10b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 67414939 1250 67413689 67413751
    0x906080f040b130f060606090506040f05040207050f010c050406030b0f09070e0102070806130c0e0108060115050c01150e01061704080903010e0a0605150d03050706050903160b0405010b0603 83
    0x43d00d110703145910442e032102c0035400101102140d006413607a0080044130340c00043c15014101c01c030740b060f203403e240980042e6100000d21415004580100e100c0c414814240400c0c0c44900001000780f0402d010280c0080181d0f00a000e1080442d103050507616090500c1c803800d5440780c0000c0c0100959031100c3d80281c0310384000c080140d0440c8140342c0089103000c010303c9881c1c0100c00103003410781002d1403031400301d00c941c0c00ea821400c42d86a6500042003c12030004000d41111380c086550304490443c4081150303688075601c4120841d60030604103615080101907540115007031009560000d90701c840c4200e42100741c0603010448101560042008980c69100078202040018000158040641030322402c0070600c00050719165039450400c031030070b18800c03081d1101c12000c60b2603c016202070b0340d0250990240e0000a010280e5400c00541103240c10802c407908000d50f26022941803a441ca40341d450164102e81c100d5003542040301408403401c00d8000e49004100d042c000c000d04c4081d1440b00842c1d642c2c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 67416189 1250 67414939 67414951
    0x1308030a050a2003041104140103031b060c080402041d1b0406030f03020f010c030c051b01060b1b010b0f0d02061e070c0303030b0a05060f0c030903030a050304030906080f040b 77
    0x1560310349490f00e100d190502c003e51862a4800da58072840c19041c13101d00da101d1400414000c50901d02001c1c101c022080c080c0781540e40c1401c100f00c1103103007500c03e43d2043e40301800007030002d8a0581035103242030f00507400503ca14821101400060b11841c00240001c00c00c101710b130107590203912014417104481c2501642040003400006059680303484031001141044400e5000d42c00412640a07400c80a0140c201d42e0b0750b65080a01055840c0540103080d4410204140b00d22180c100b0f114100c03030400e4001c03030000c000e00701140d901c855952050b01d5081101a14003070082d03280c030300701ca81a0b00704a40c1000b01010000c080100010741d9800703003c8564010b0f0800c490610300c00c002071605050305405030901c80d000702c0c1584a400c0c114a07000c1e003101da4008000348250021001040705070795000454036a0049a03103182e45440c039035440c8a146008103040c4035818040130951703112166101019500c0b8078040d5540241a80d43e0b500c007a95050026070707282d0507042d603510014005c60320040c802074101c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 67417439 1250 67416189 67416191
    0x60c02011407030302041d06030c010f051b060a0e0f0607351009021602010e030a080d0c0e1c170715091511030a0513020d030e01081308030a050a 64
    0x52184200d40c1c05a0b4007609048020a41c081000d00c901c80d6040020b03140c4403070704040710780c5d1410800e0001c3c1c1d8610a18001d141000409461840703c2032003541940c0c854040080d003918020079440d18252581022582c4844070f03450000340543d0000f00040c2d818441050101070201611949011500c4c0c0c0d04400c07000c010901e44038a84510a1502c10300040100804140040c160414061200b40490140c2c230030103165005001e4403105403803a0f0544e00d03120381c7c2405c0540f03d80c07405201090504003009005004d400f00400c1801c1420269006102d940400791703610014042958100029071a290580826642c6104404000a00c500c0030070b2101400020440d0308105003030391826075420130480454251502e4104510030080405070ac1300c0d4900400006015000c450320200300140802003c0500381c64980003c074003031142c01c4a4111802c0e0700034044106002c410704000d44200c85802455000912080004244040e49403418182035449101c0900d580c4441d0102c1010740307130181c040c500c0300e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 67418689 1250 67417439 67417457
    0xe10020a0803090309190302100309051e1b03061012051006171204140d060e01050c180105090d0803090c1c020306010509060616060e0d0e0f040e07060c0201 69
    0x1c5003055019500c0341030400c0085655440e80e8051012160103905207601c1c141188105100503a03034541146001641071800048100d290f0070100d141c1511620180e0859040824120209001081c0d8000c080d80c40a0900003081c45003007819030304c00c1704891200c84800c00c0101070025802e48001e000d8100c0c0601c0856070440660030031103007181d0035a4000d80041003502400c01001d101800306a541c0200c1110040c2414a0600742e80c28926274440d03e540700e480540820b00401905601808440310240020881403070411380240361031340072031085403180141140a042540c42241100c0071108050211308100c680766950f1840d542000e00104068040d50124070038507112303d1b00c440d550141c410218000041c00d0b0041c503040c1001a01f1950003031400c0c004010311912940216801074480d804c80c4216400c0600f4201c1c002c00f2440000d40321400b80c0150b07a40c2e01e9601a10035514a9801ca440c60f0312501140c04100c22078440c54030f004943d030880d080c20041030380541180c0d14881d0040c1000303079031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 67419939 1250 67418689 67418693
    0x303050d0609110d050901110307030b010512010b030105030f010501060e10021905160b03040809190f080705130b0901060e0109090f0f061205060c03060604120302010603051b010e10020a 82
    0x107940f068a96051405000306a0414400e100e00507950407007603000c003c00c540f0015036400780e86480020300d100141a207540d07441d0b280c3c2e4802c100702c0b15000042000e801695850300c020740706652003031042d18481c1c0304012148020200c180300700c41c100d1302d032030300d803d2603080391402440001e00703549510300c00b90300440c5880c008030504210007001143c403590252200d504204c0107d158040355410100003000c050040000103010901203458101d8203c629004811000181d441d00003841d412058202a980d40c00090b1840000341c1202911070454210700c2d11306400c982281140d60b01458a80e002154000403c00940145858031004006140152880b43c0300c50640d0300391a152242c60b03503403946c0e860600d40b6204082c401d1b080030302580c11422054030b07156200d86607140005001c0000c3ea441c0000452a190340f02c074100c600805000004400019240c2000b0340206803910050303507240201000c2e404a01e50f14204150084416141d07c00c0b40b102c1e2609000502d5600d2124509510401c2c0e80080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 67421189 1250 67419939 67419941
    0x120f02060403021822020109090e0304050d150b01030b0f0918030f032202030706051c0c0201140105040506100c0807061b090905070504050108150a060507060e03030c03010303050d0609 81
    0x48000c0d1110045013a50510525005d00802108601403a49450311100360042c0c0c0d05c4001007040f11030009011907981e80c03440005085220f198030055200007035103145000c008c00710106109420110b00200714010303036640194140c40c41455800d40c013152201081174645000c0442c940c00c10400064810060002180d42d45103502a00f002012560b0110400c4440c20050b021026020418243c1d150290046d0b03006c42c4d601e00f480e00403482400303000f0075a006025454a40448214038074002403005030304c03072a4040d000b4024150100708003041180003080314186030050500699028014055402224800b100c118030311078001c4a20f40420049000031038010b002c1c1c07002c404d100d0094044540d5461038050050045a44682c00c60740c02c12007040041908101501c048030400e00740307104955075128510203541d1801111590044901501103007080d03111740078100b0107101d5041000b542400b140d00558901084410040d904000c200500010b40f20f440a0702d0000c140000104a030b0f40c031410703060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 67422439 1250 67421189 67421209
    0x908030307110c030109031b0302011b080106080a0c0f030917191b0b010312050d05180f12031617090102030402010e01081e1009050901061707120f0206040302 70
    0x40d08440340310b500300c0c03018000203c200d0821002040007421640d40a8000300241c3d01140c8101e040a002c14103050003034002c000c00000b4003240c6800d01101420103000600c00f802400c00140e01c4100141b0760396034602c680102007645072135001640240d840102d028103080d6100b00c0c0c000512b001c0c0421040040c3d00542900c10004c0c0212038803112090300100310300301c00008810204000800314021805400c0c1c8281580e412800709598a05502000e03a024442c810300108480e1420081003242ca00210f4080402a000c60950700c40381102604240c1d10003202c140c4034001c90003000402d015401d16015420500414103242207220304050300c1860101d030403558410165000000c10045690240b0020309040003420f0213041800c24081c0c041000d0500140107407003a580c00b002c0342070700c8001c003d040c009080c100400d004510341282c0c1c0b00c0c042d00c240d110301c84401c408a001c04203108008103054041d200c20307400380510007602d511401d02c01840b140382a0380000381004080b0158455400300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 67423689 1250 67422439 67422451
    0x1302042d02070203060c03011a07080403020907110111070317060a08030a020706020c010c081602010201110a0201200c1f0902130c11010608030919050d150507051303060c09080303 79
    0x1602d9506600500d420079000810329240c1d07007030400c014044500125091480012841115629807060340303801d41142c400c640000c1d500041c1035080106142d440f11008411000445c001d003c66441290400d07014012501c000b00820b00404440c451081c0c41c8a656510190051035144119651881181141c0c48003e42000580014009000182e010000c0740000380081c6800b064184198488610314001c14007205128a0904119415a8401d4200c1009032001c80c000641d5200203000180c0240030781700ca4150881500d40101000b01155010b45a00800240140024070007544803040d150303900b070003a805d01c0350303403040140c0160700c90f410a40401d0741e00c41000114014108409844020502d04000050381000f0041c821300b940401591080b100640d00404017480344100c40741d10300c6098003c160409420400c1005028101c40340c010b1070344105600b00881d031280d52088540740318100010001e400612001c20005034a41d1005050844a2915440781503c8030541c50440d4000c2d501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 67424939 1250 67423689 67423691
    0x40803090f1c1203060614040306020702010905090a06060806060a0c1403070606030305090319050c2205070906140c070e0a02071202010b01090b12011202030708010c0f08010e1302042d 81
    0x990b02c25054440c88003d0203050420001900c2c043d07501d502e2501c518007000744ac05030042500411640250035240207040d00409228042c40c0521501c40105128880d140000d44107202040c030321f09144040f1000d4800564403510680e00d91745a0a042e8629a105074100d44070402c40c041c04161a8441c00300554400e503209a9075486a030304040c60034500f131000343e06c02d20f1140050000518002403a15182c00180e030700d10703101203c1c0190f1541859412a4184002d400c00c010424400e030300092000c00d0360080d40b1541c401004072401c908680c000e150740c0114030341c0400b40511956211012060340008030440144c42c011303c40e59807450b0600a82031000141c3c1d11007490740703415a08107200801820741041348500307044605a980c0301482d418810100100d03950701c0241c0642d10144014409070001c4402440b00644800c001070039401003d685000140c2c6000c0040350841c0d80003602401000609403581001c130b081d4007080001c0400c0c1140213045002c01c1401d80002e401072194520220032020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 67426189 1250 67424939 67424963
    0xf01090503120f100e0604060902040308030105010201060b0c030a0c08070203010212060f2b02030c09150f0904030e1005090a0b1c140a0b0f090426040803090f1c 71
    0x4a11401880098210200c0c04a01c0040015001802a40780c044440102007200e02c4c0d01c0c2e030408540101552740190400364000a000300c00d0160520086040f80c500303a000300700c3c4590300c081201d424010140310f004660005c03c4040b01441c841c0112900c9180071b1391071145029a10f900280c00c9a1210700b030703213540704814420851207203000d084035a0301007820394403500a4010a1442400885540b40c1e40500c04000c85915080d0740701000103066041002d00000441c1c04c104d41414000130f50158aa485038054418100303203401d080c2c04550040c0d60545030341e90504003402c20800303e000b01c4035404041007018051120380c0d61796031050400801d50290314586c0c401d5042154055041c603010418841030424800e0480710325074840349540302a2405001912110042c00207074481c0341d0030015548188001c0034042071000f4045400030b000281d1030380c1d801d80c0406540d41041ca000d544900c40140d04140240406814800e054900090700100400d0203410303914501b441d00303500c080081d180501001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 67427439 1250 67426189 67426207
    0x60b040806090708060c070b09030403050a0c090c020c090c03041505070504061d0916050409020a0305070e040c08070c0510050f04051005010302130c0516110109060305060d080304050f01090503 85
    0x4040e542c007408405014205e02e29080081200078403445a000306068070450000e00781c0007003031094074007541d8003805480c010205401c3c508c02c2103183c0d01030401060b02e000c501450182c000103c11042d04005041040c1ca0b50703400a2501c02d94000030029100102003119405034807840b442074a11070001a1241501c60b420f04100030054a00d98100051516902c403018080c0d55503068200d40c4910210301e000001c145002c0d0458082c004d943c451380d4103500105054486641540006110300515070324a800d80002c1c030200000c3d1034514401e0000b007207281e4082620248242000441140030384100c42c2401c04410741c01c01250003c80c1c0140090004409000400c0001c0c000c1000c941c982c180c0c02d010550440e00064480345202c6501c00501741d80c0d120104030b040c003400681c3c03881d405990449056001d18244450303075031840f00c4824001101d503c0c0101da0540244110744c080ca102808401007800aa42c9039501540084e000f580e43d44152040a02c243e04240940019140710380040d68841c4040c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 67428689 1250 67427439 67427443
    0x90d06020301061709100e0f0a03030b0f03011506030507052b050903120a020304030e031606030e011a06070201020f06100e01150c200a030302010911100512040303060b04080609 78
    0x260f4000200c1a002d81d040c805e00410024a5003081c1c032000c83d000589502e8104060718009680d070000d003190068000c54070901d0b40650041855490a94040c0c81e101e0701c1c03d04045c00c80362032130b185090010140d44113200b0f140c40783d403003180c0c400000d090591900010228003030009100200d11000014110352118102c0c0d814040d20b074010120070300450034803004003000c56240030010107c905103039000c8000f90a141c810000e20400301400740c01c4e92480149603082404808483c01500d000c01c0c03c0c80e50041c45d00c8414410b10300310300340c06400d100001d64200b003003240c1d992080c1c000740d045101e940010803042c0410f1029500901030146d0a8401c103140001e12a40da04059111002602c0451314000d103003600081c1c1c45805550114141e4492100303483c110b0740c401390303191525030000031001011007016015440300c0741482c00743c3c1e1040c00702c0380440d0400000118030f0842c030300000c0303051108019040c20006825001480ad090114403070781c496003a85420382181e8000c86c00ca0380180188a034403001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 67429939 1250 67428689 67428707
    0x41a03090d0207121101090909050606030c03030301060c0809060d020c030d0f0915051905090a05100e03090904060e0105040c05010806030a080412020607060e060f0c070b07080c090d0602030106 85
    0x41800500743d043d180c400e060144081004c0094020440c03000511101ea10480c2d0400207041003050030411010035080140e580c840840d015802445880f251a0080c900007055904a41c1d1641d90b00801c842e441d03840310301d00d411100c010b6070481001d00000100c12224009050828862801103450355902079040061790130402540d040f851070002143c0220b20010b400003c8150001e00101c0d05803075200380700d9207072111040074510052500080c0800da410228598007402e001304212021343c8030103401030701110148806020607500030400944203003000702003940d1040c01a00c000071a05180305040342560402c40d0103d4003c04e110005005960b04807041a070400c405030001c00a070145e6aa452107107105500a10b4004800141150b0031035031484100d92000b0352010050024403920002c0d103581704002d4801c101100c3d0f02c00005007000e03e034a826100fa841d0803940402c41d5071608407081d54900009400c08038a1203041080507000c2d112078006860321403046a0050381c96240038001861150303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 67431189 1250 67429939 67429963
    0x2031f0e060702010e12070305030601050f070c2c15100c0c030b010306290f0307051e04050c0a08060f0a0305060709031202010608070302040e0115080102040504050c16110105041a0309 81
    0x6220347c034046540901620360024003800c05650314105800010220700445e840100b04003841400410704035880840541c1d04481d804500c0c145c48039005020303541200403035030300d003901c0e520070744070145403400c225503c0c03204074203042c0200c0087d01034440d03c0c1341035000c0d0015074484928500401c200845031280c00c501d04040100c0000c003946180b030151f081e0780c1d00350701c0724490205102e210a50b43c1e014003072040204001410013800f80c44103425a03650340300840b0304510452500c0009141ea40600044500f040c0a80c0e489803208d98030a0100014440709420703250700310100020200020340d0402849005090a89945100d9440c500e001c40700c1010100f400d4046904000080200c50740000703d035000c3d60750482e1b01250712015407010780d004109000c580c40d10403d030741a0008541c0810360041c025105c0c01e45c1c00340f0499031200d4540b0800d2080140005400180c08011030205046202c0703243d200c0d00500d0418a0300d5a203131880240c2c50281c0c5a0440d01000c00814401c00441c05c010540d1019 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 67432439 1250 67431189 67431223
    0x3170106020a030e01030e0d08160905060304030305090102071e020f0420030a32070201090206180a03150218032b030204090f091208010302031f0e060702010e 70
    0x260420000a480e40890355004041c0180d03002c0441c5640e000b5085801400e480008940b2680e90f6500010200502a44d80803e0044810070984007644940141026204080c6c65641707141c841369002c4004250007061600e45541c00d100040000d07844440a424408174881b0b64440d440242c01002040c181000c0e04030320492600500014009506c2801c040050103070386060b80729640c3c00030000107812003203010300c0780351202d20000c0d06885540c104040a0f00c41c83c218010959102d007010307070803921040d0000c0d501a03001e21440c00381051015402c0807178240a094490119584d035100d206191210140800c0a5000f10305003000300c440f40102e4208100c100d0003843e042c0c0c074498024907003c0d400d1200c004480795050208807001c1c00317a01140c1c0200b00c2140d0403c0408041041e0300001c0440da801150b46035200f95451111074030403211141030b250001d000c1c1c01c0166180c00042102c200c0801d28800b050346800d00e4540b002024440c2d0307480b81845030000704407002007110440c20803d480b100295070b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 67433689 1250 67432439 67432441
    0x403030903021c0507120201120507020f0d030c0c11040b09010e0a0e01020906030a05041a09030d06080f07150201140903090906090c03130221010c0f0219020402090402070c06020304030317 83
    0x2040c4006180000c0b11045a8072901c1b020143c00100c071901d81d031040e8240880e0906061089090f400150000703070000740c809079580880d0404c0d0807001e9401c055520000190300040603030104022084c41c001b0841c1c020000245400d040c0c001c140f51007800d9001ea05140f02001c01c122181d840e0340581c010709a044402186458001e00024803039010142c8501d4006940700c1c0001e0401031100404484443d1400e02000ca600d00754070020317035952045051240320703418544005404c4400007502a080000c240c080c220302e50401429004007881e45440104564a5114100858560b5400b0034028020040030b141c5c0e641180c82031150b005400390a0a0003842414204541c80240c0700c140e0350050075070307440700403c10118000281014000c4d07041c0c3c0c21000403648103008603401548801c9038605240c82d01ca03042c0c0d1440d075050361a81c00d100b03100c003c1c0082036141c0b21b00624150340144a00d4400900050a1504617203a078144008590002400760380000750600c01d00d500814090a6a40284001102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 67434939 1250 67433689 67433693
    0x150d1d161a0318030403200a0b0304060e07120809031c08010e040305070b240a0b0d0b060d0c05130504020418021b01230603010e06010605031302060403030903021c 72
    0x1052440e86100004a070000c0003186548085031501c1a41406100c200c0ba22941c40381440c0c030303400d0010211521241d07603140e4003525604081d0507403801c4941d041206402c59843da2141d1b40a0030b0000d292003020f0003450700c00b14811a8000800201501825243d500c03041341e001454070305100404011f0400001400c24840c980e84020000d043d01c03204200c90600e51281d24042d01c250040f848000c0440d1019820460502c00c03c0302d100d01e118212405807030080500c1c1c8148540d1540d42c0c01034100054041260618064254009000d00e600c040c0c112403508140c45003060403107031501205000110001511414904600036a00103400111000c625192810b2200500d03e02032171090083c0c1600816015011103a0b21008411120284000d1201a04002051a401c1d12107026182c01c0a0341d54041925820148120080c2640300001002c11741d007800300070790b440d41000f01601441200d691580c0c00580b210400b8000542c8039442d80d103020340c00c6104210b0f4480f40248180c07145103080d1403641c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 67436189 1250 67434939 67434959
    0x105030a030c0807051002030a0510030203030d1802030d08010807171009050a0b040c090c052106120d02060a0b010201020c0a020103020a05090d140c0a060e150d1d16 73
    0x2180740e1608101105402610340380701d85001c1e10b10050181d0084100300007880d0156001148640700c1b18004120342d50756480e0f000c403040040d02001e03406074030900201c40801c2055201ca10300000703d0511181d52440c0f60300184c5070003154140c103000141540010080d4041c2005600068688180e86c0c482000011003083d960300000404481d55546982c02003003806801e0160f241082d8000b0004c0b0400d01e09800d024000303100c540705004c40e05151040100b140c0b441030007130b140c582c640b88801526810754200c400303000200c0501440d40c0300d1014500ca410602d4108841c2c40003d0180c0c014010030f103000403840c1d0032a04289001815a4010800c80c0542480400e10181d91036090900580b9003211083c21100d03400389100d25a0030401140d10102030061503041c2c603100920f10703001c803034642d16030200340040e84502d1300c24000030070340c441d604511a140031440000706e0b038100c0c1078044c00c02c2c8a15000c68141c4041c03490010114410038100088005c01703021000d00034002d18406242c02d460008005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 67437439 1250 67436189 67436203
    0xc17060712060e040606080601120c030204050a06180605010206010b0901170702010609060608060307060e090c070201120203010e06030717070915050402030709060305090c1309020d0c0b070204050a05010503 91
    0x1008284811001c040305a80d1040026000490b00e05180c1d28007403400c040184140d02820324548075010002500c3d11a400f10565025071025190b1440c42c9140d00307110250a0203400b80118548841000c1080c00e00380b11200c404461000011500515080c006410494180c020040890b81004581c45598010048141c50622140a4001d942e2030302022401000d05411106145040c0400001e00c2c5900a8109000d1001102076030041c56580c031050320510721200c0c0e21900503880400244100705c904020349030003030040c1400c2e44001c01940611040ba8026049000301d0103c04d0107101240c281008000003400e900800410135048500c800ca0703640c200b40c416420482d407501014582c0400040061004040c083c10554407030420903400f500d42c034118014400001d15140018002103400203c420300d4030400313414294001d00107803115010b8000d00400f6a0014500303221a400141c400740c0620040c02c0100c885074035900e13070b44108001d8500141410000d242410300501983e036003c00d00c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 67438689 1250 67437439 67437451
    0xb0105180904140d0c05070506090a03080f0d02030414060a14150d0213020405011803030c0f020117070806010314010312111203010806071202070c0612020d09050a0c1706 75
    0x1c1c1400b940c41e46400303101484002c18541c02c0c1c0c0141820000c403580c210807190a0035100c1c5007660000e5445400707001031401000c01c0c044d8022000a030030004609640c1c014003655002e48402c0f4548107411003071400740c0c0c4c000d4a085412168100540325000c1c000e000507030f002203441f0018460036090180705203509202400111b039195049601e030b82c0556889214420980d40904480c0e003038240c108104000b03400c2403103001d012034419140021100042d00340c200603240e1540318071700c0307500d803035110601c1c50480c503c1d089046c024852000400d818a6500d4070b0b1003010140e852866900d0300f000018207440c040b0358404a00c055110041c00000c0c81549001e4060805107488000c1c4044210094604445d903000303214041000800492210000328200c0c1c8a003e4030707140d805803e150109424200d22503c2d5010304045034402080c44191f1140707200021140c0608809401c00040b241d101044454142d000c8038254854260141004001c180c668010103d24141400c10010500c200d500d40c0b03001414 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 67439939 1250 67438689 67438699
    0x5060315100203091f0f08160513090e0a05010b01090b0301030f02180717060d11041a04020a020a140f07060f090e0726060d03120f02030408030103060b010518 70
    0xc0d0303000c19100f00150340020030300518120340e4201c122070b450713080f0444221020000c2d4412078200740c84e9008000d02c50240e1050b4100b0342003103640c868102c030300750000208002104101d400c00218642e540c002d00400d03c1941d0007034a606600b86c50010b084841d500003181c180601c5460400c02810701c0d00a5a04583e0001d002441042491001036215840810140c2c2491081c005102400e03900000110741e40030041a00f400725100e0b40208500c01c418400011f15031004a10402c06a050540009800302c0204a40c040d8880101b000a03082c0d0b000031600000607840000f0030302c28445030b12058000044180041e00c543c1100d40d4a11b51103441500031002030103110086044000e219804040041c02003040140c103d08090100525051120641e103240d85480070035004410841c840d40c901800004205035800481554103980042609440c0110782d580e80c502c05555030a1400110310507442444032591301d46c150315001084621b8500d916041110a0041c00c04c00348800050684501c1d003150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 67441189 1250 67439939 67439959
    0x17011a0a05090a090f0f030906020c0f19080607110709091214040305070303030203090f0c010f0e030a0606080307031209020319140111090f030c030303010b0c070f060903030905060315 81
    0x2400050000f800e002801d603800a4072005c1441101c0c662959000c0c8241d54604282e603840320304130303914030012403440c3e1300454072403517054185060031414010003142001002002d42c2c0d4034407a418500c003114000007085240a203450701d04418800100070307085070a8100300c104459290700c60221013803110b10044c01981d002020800200303006540003180e21808a0740b25039100d281c000e019403c262243c01c5540300303c0401c54803425002c6a141c05290040c0d43e203203081b41c484403007101c4e040c204028464260281088100c00706085000b044003821040300116a5000307a45802001c01101d4071010410340c1c507020842d8016607011448a0440c0001004052418002d0800105c4100c22081c20328030b540c41d040f1040444100000900301c601c1d0704442d03140e8100c2c904020b240e00e900355a011240d054004200511144030248003502c04003000c00100c600c4280c640360084100b8040760000c5011603200c0c3d0040040541c42031050002d0070303056540c0c0b41103003040c2842141e00130001c0c9600b40303e80c1c0310007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 67442439 1250 67441189 67441201
    0x6090d1704151d030406050a03060e06031b0f030f06011a0304110103050402150304060b01080a06030c0b03040f1406060310020f07060c0e030a0605090c0619081b0417011a0a0509 78
    0x83d04800001d0f00c60181c2e40c0e00c2d80c0d0394102520950004400d071000c80e0405400150901520b000c0610030740025014004040d81030072004540710012040355406518403004c03201c140c0b41003000c0702d4480c0c01c44006101d0365040000c022041e42c05917040070000042001003000144880c442c00380925401e00300480e11f0f898520025400c0500701c9401140000c0200c104814890103401c569021002a290006c5544a41c14040266202c43c000034003000003807075040203d445120015507000380107207c0c28408488554981000010b102c0c81c0740450b91240c4107200c1e1038941403020251603403074402e04502d8011244840c0616000c0c3e040d003d4a01e0b50b0324610f00c4075a83c00303044105500d010080175500c0340a41440c10320000d15040c0c400902c41e10403064140b00600b495021600130f0000036801d0206000d5003a02202c201100500c4038603100a40080d540c45825094064030260159880381218030413900501401c445e003403141000901485d0411004c50b40720310b061841502c4003514080c000c0e41d103075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 67443689 1250 67442439 67442471
    0x1b0606010519020709051603050702120901050711030f0304030b06010207031212090501060f09110304020f2202030403050d14040b0610020f0601030c0503122b0e06090d170415 77
    0xb0b0380c044008035003406c0030040e4074440091218008081a01d081045480301042207075a400094070a50304050100601552580110013a0400034800c002003807401500001080c20084410000c0100e41d0000c113060041004c800c0249900050a2004200003490340e03c03040340d0002014504410701c02c0c1500000a10005a00310444030f540140090000303982d1038049151900507880380e50910383c49d0082a010f08640001144d00554000b8034a03007000390580f040081d24035003030011810082035902003030b09440700c0d4009144294080d03110b160712500b0790104001942c07080b00c1005802501101004002000300844d00d821410960745400c154181c450706034500b180704540c0c9140e52080358000030030040404075004c10380f54140d0a4a481400300004070f41c60307010300310361299085040c40500381e0642a840d490219410b0301140800c3d561280c4d8401c600b014403c2d2940001504540f10040c489604404c1d1907140780032075000d000c69460706132503001c0701c4814900200080c40e00d54241031046680 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 67444939 1250 67443689 67443703
    0x7050d090605091b06040e011401020a0f120e220e010222030c0b0a0503010303030c050909040c09050c040b091306030804062f030712050d0e01021b060601051902 71
    0x4440000c22060403c0e0035026952030400340070f00e00d841c00e41203009145042107000e40301260000a00c064499091440251b1000c0b840e013a0141141701d80e42041c4003190316000c60359200c9004004400c0451903000e0018000e425034440140070f0044e485014480c01c111807140c0c0c04907084500002440d510210042d0f000e44207100205401d00a54a100340030310042c43c280c80b089074070940c201c41d41240e50b884010f440f40281c40b51100424030074401040424081d03042506001110300d8403500c1c00d44400d000961001c0207880946114240c01d0007446411a075205290700304c0e003004001d5040a2800d030901c5a5840b845c800280100d88000f6801d60340242c0c0c1c0c000d8406147c2c0300940c0da1b1141e803140402000d030700c0d00c0b64103040c90180121010b02d0401142c000ca0340146001c2020f50314080d00e03030b21900c0083e0441640e20040003030400868413046ea0502c50b48000c04864400980d59545058081c085807000044091181d0008824012144e801804a400910341c102c031100e0501a034040590034075403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 67446045 1106 67444939 67444943
    0xb100807080c04030c06030c1d0d03030905030c070308030f010e040b010312020c0a12060605040506011713020409080702040c02060c0f18130903080a0902060307050d09 74
    0x22145041c25030101034000c1e00c91409a036941d036444008082c1d80304a0000b95100200c602155000001c50041d1002e159080c90b07001c01d40380050540000304d4401800c0c156262024802c0041c01e00c161441d0f1034480040d107882d0f40c0e5905049040c0c0d4030071a04240c0e030045a0002184e072408002415024030741020403040310b80e003990740c0e5250401e60f06100301c0c2540305041804020359260410300000c0d16824142d540c1591803482c042d0245c4009800c418421030a150801510341da000c0340303800501045400d080700d16140c0e1001d11104040201005c3d401070300340815981404480001040b0b40c82c801d69041141c0f00c4007200481e2500c606881c01c40a040041241070800140c00000c0c0801707a1034000e096803c4210172000900102103002c809201c1d540726010310040c0364009140507480b200c00032040c4808000c507400134525110003480c401c28090b02103020b90302c1c2d81c119403003282a65 = true := by decide +kernel

theorem cover : BRFrame.Cov 67266189 67446045 := by
  have h0 := BRFrame.cov_init 67266189
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67266189 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 67266189 ≤ n) (h2 : n < 67446045) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
