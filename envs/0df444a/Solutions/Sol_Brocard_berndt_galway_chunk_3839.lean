-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3839
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:48.501353+00:00
-- url     : https://prove2.me/submissions/01491d90-b5ca-4cc1-885f-e51067522e68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 690287769 ≤ n < 690467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 690289019 1250 690287769 690287779
    0x9141f0302180406060c02030705010201200f0712020a1106040e01032415080609010e030406140c150105030d0806300307050102070b0703110d0504110a0b09010f0c080306 75
    0x1020038441d103500710500d80b4120280081000944e681d00040860080050480c0300380141040001c4c0c0d5841401742c40d9000000320402880407000714a40320780740d40315000030008524180505800304405034240d59010080d50060100d242052400035110400e031647c551003030b4014007081c062400540c1b50300303041d2a0711041c22024022070340d011080100c903582400d4829802c01c3c0c0b01b09504e8001180182c01c6550860848080e511615817050a941085480e0f90740e681c014042003241d103201e100003140c2040c61074021460480851082400c08594058180710349214600400041c10304011241d00c80c00e0503d000c8070b04d41000d00c00a11910929508001d8100c071010003160100c1005007890082c0d06500c007182c1da941002d01c0e01a010b500410015101080400f000031a0b00c0d0003070240088910410400a141800b5402040001c110242050302c00e06030000a191841d118031f4101390142c24190b96064640708001c000618030090944080204031442d803064001480c10400d49801c0441120307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 690290269 1250 690289019 690289027
    0x303090319140a0f120c020106090e07140f010513061e171803120f04020102010b011e0f0e0910031106040609091d060705090a050d050a0b091c09141f0302 68
    0x1404450440960503241151860042860206ca070150300c004c00b241c01000b014040c1d00146401982c450031144640003280b0010341e490b00861420741c01c07988515a05040c100d0070201c3c0541d031203030300e04459000704021555030107500029800508010b4101c0210785001092144007221110402d0307005094034000c140300b5690840303c83c0061040c1c40b002822a0741940380ca241403c5055003840042e1004d90141d4a012082003242d40f24010901810a413002a044020f04c60b8008580c0545c0d4495a0380400501d50745040b6690b4864032041e002e01c01e00c1c0e907110b900d14154103050714080d46000009104040c10001048120340140c00c800403503608240010301c1c400300040e2807240c00600c1c0710050b003d00070081013120076500103002e011b4501c0d00741c4044c02a10780300c03002e005405400100c064641d5210411140000340802c03401640010303080180c503101003040301c564841500c2c0c002c142c1c1c00b1404529091111608540c4c2c03280f51044100c4d2096400004080311045040c0d04103840c2e000c040d0005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 690291519 1250 690290269 690290297
    0x215420d020a180b120f03031612110d0c0201060f090207140613050c010801210c030b0c18030616050a051c0b01110f06071b050303090319140a 63
    0x1402000b01148250f003103150110490018036891000d14410080030f1101641514000741da56000706e0328400440c51606e03240c02016003040d616104004220801d401e0f003040440c94003500c0000506004100d485142216041c400e4400c0c1c0003044045a1603d07101b00680c1030045400030455429920060f559600f03400c001c4100580034044854030b2003694244841c8030428030703007451064000c000b540c1c103100380a0011200c0380d10078802d0b8502d01c40c4100ea580f80401060301001303a080c0c8a15022800290380f81e480c2014564221898151400c1c042410107141d1504910107100c028204e02402d15490901680504814082d0945042010200d0400344041c0103008036004c101c101036034409404031700d49060001d055030040140c006a045004842c075502c00003a5090303400c038008090250380d50b0b0b00804a0b41c820b86108120342d4107659000040219400307100840c0526801d6021310f07a24041c00600260000540c1030700010088074040f000d050000200a40e0304200303103442c01c0305070b494040d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 690292769 1250 690291519 690291529
    0x1020d1b0803131505010b0307120f060e061c0b07080717010b0405100f2309090405070501020c01090b031b07050f062e090506010215420d02 62
    0x12030401007006800105010099400c582c5820140d0301c52250901110704014200c01550400c3c851143c8152062010a0205000e403002010902813071100080d04d07001751040c03409a61856200070800ba11550601c8060305108074160140c0c242010902c0b07107607940d50380d01030000c1c02c002c0510341048070301700114141034410b0703490304503412041491541035610b60064010581c010b02c0394500c07811421044103c21802180c041500c2c0b40301d51503400c800416a00366494003288441e0744541800c04102c00c201a65452007414001c0307000f50000c004ea40d00b060006464541d5080c00581803101e8044104400000803045a07881422245e0000114080700107582c0d15000301c1e4001411802441b012440c12000025102d02c00c03a0843d01a01d52044401001c0411403101e100c400d1001c40b40c5001440342d002d003074000c2c4d500000e0600c115652001d08125600c8444c00a80703944c240704071410400b0000744001015000010400c0c003c0083c082140703a1401c4500391031001c07460107400000c03607600a555030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 690294019 1250 690292769 690292817
    0x20702030a050f0304090c090e0a0c1e1206060e030d030905150a020c010506100f030e030f040e15010f1d030f01060b0c010e0106032f060712110c01020d 67
    0xb100040754550440c1811142d00d036001801900002440c094030300b10071a114801140072100742c103c0d0300e6510b45900b05801d01412506a052041c019040b051515103d094012034030b4040343c1359a5075480610006241d4240e824a50010003003160101080003240c0e00401c0c4200529507504001540c03050b14605141007030141820605030850540811010a06a4000700011160000200900d0360b030081004180d00821001d8400907604019086145d8041e501a4a2003a81c0a0440e400c040540c01880460b0388030b508800351001c40b403002e20803c1004403d071082d408009003002c0000254800d40140045181ea0301c0542c49100e42942c040113440c14060924071038040b1009110403512401050740542c024040c0400d1580b0300107815042c5074040c801d58003900c0d484006285240d00c0050000028154001c04200c0c0d100051190040344e5030b00401072002c1441885039800e10b12002c1000342c090324260a2590580c0c20200204201c0d0fa0f001c101c11300006540c1c00e000c01e107085003480d1500f000e50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 690295269 1250 690294019 690294023
    0x5100801210b0a020304020f0a030507091109131d031e1c050711070e09060c0306150d06140405100b03070507061d191a280c030e030405060706020702030a 68
    0x208180f212010054009500c12402642d41c0c3d40c0c1d410b0241c046c000c41502c1844090141e8100f18810304c0b02c9181900400c610007140b1550724248840c0000080c8a07840000381d2801441c2c1d50844480042d82680c40d41c0382400454000d942440ca005051021400b004986141c45901c0042c20f600d40d4000f0124000040d20180710130441880c1240c0064400850400b85034070b0341c420b411000030070b0000c0452440c41160900082d007031940718011401c4158101a0010360700a0140309014010301498000e8101032010020200342580303402d0b03183c4003003228180114000ca0a03e000c004524501c2004142100ca86020060f0750760b891071811280c9024000d0024421420140c201c03011414460700d00b02104040c0064030705070b501c80010480410310340c1100400c2c60603811050038141c2040102103070310900b0720240101a55601c0d503004107181404cd0f8078001280c0da0b0703517080240b40c3c1c948902c215288002004510300350508000070802d01603900020041c5400041c0142152810322944040039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 690296519 1250 690295269 690295283
    0xc0803040f092003040b0f090f0c040c030e060c030403030f0b010c0201270305010e060604020c1915090b0718051320040803030106020c01090e070503090a08030a09020a0510080121 79
    0x30030245840b01d84410b0030355418000301d40d00d402160100e640450070307141d003034a4640102b00705001d440500018100c010341c1d50081c50f560f034010085459081c40358038131402544400658034609803401508440390311441b00c0815240030041c0c0310036600700284070500c54090070304c903040c0700c4203002c03001c4441d08901d078802d291412824004101320f8150000d144842d0305005a07142d41d5079141c00d110890145964444296002c444c901d220101441c04200c0032a000c0c0c81c40341085000c1c4041c00301502c085d51002c90f0690540800c02c1203850f441200088560300074090141c2c005e203418001191032585c0130814035816030b41c101608040c101500c0c041c52081600307406c01c1e1999035918100d91a43c00910a00d005401801e60390041984074078a076205551a070045a0001e844140b0200ca83d9000100b0010b5144140640000800e15243c090751060300b0b080380c045642034452040c0a070241c2c89901203401140c8541c11a14501d0f049084103064500c88000d000e00141c14008080490f078054a01070107207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 690297769 1250 690296519 690296521
    0x80307020712230718090314030c041206110f030f060a0b0a0e010903050f03040812070b040f020402070c031209060201050f010b0906120109090201110d08010b0a111501030c0803040f092003 83
    0x3c0344846d00700940d068020f88403c06008100c1c488101d0310f10003141c0140360014100f00a101380c0550032154030f00c0c10301910740016589001c6060000540c8a19034645c00c0311000301c104181c0b08907180c482030f403025099860018041c6084034940c4540a10b2040d01d0602c405001c00000c640d10401c481001960001c003143d4500f000d0a2030962240d116009164142c0101d42c2102248030307c403c1103071500ca5020510482542e02d03601c941c611460441412648036400700500030200300b10549445c0654000c00210500b40002503028051018031340c030500645e41001c081080f1840f030400002e04440300b41240d503503a0b42c030340000142544034045d503001c0c03401306803400858030303050f2a0720101d4590710070380b140b503c40b0001001c00c81d51341e61920b0703072900021035150060250700e40e2032f8003078100f00c165400e11001c003125020215003004021344018051600c038500400074820b45000d060014804030b400b81d071606040c0321803919241806e00818040709c1d10394481c2403003184003180880400350124003041d12 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 690299019 1250 690297769 690297809
    0x2010c030503070c30110d051c050f0f070c0305030406150e04080a0807051204030f212003010302030a0b0705042105100606090608090106050d0803070207122307 71
    0xca41c1ca11491841d602c042e031500d04031068090710211322140c1888000303100c5902c0302201242c0d81c9d4840d880226024022038800e41c02e050b0b0f18018280161008803907410145880101c000c8140c0c80107194508002400b503204d00072a030440d0440e03400036080000826000025040038492904980c012001e108000042105022603080030b40b2014606644100305511466400c46060061496070145061000013040c00030b8042e04c0c40b218040030a050400f802188004101040d418142074010215141c1131401d0300380c854403101003400030b00148407038119411500440c0e43d0b000001001000032540030007049840703000d030003a075004041b00460880140243c0c1d400c40c200202100d000c580510454800304440d2082e80200f00c1030300c50030b907100c50800707141c60350441e9400405018140700f550380c0c0305c003c1000d071035800c04020004d005181c0ca036540c0c240360400a24102507913021802d00719a1180311000250702c0c0c02c8940311034020000381013920402c0c4104a04248440d0312904005caa41514045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 690300269 1250 690299019 690299063
    0x2060f0a0305090604082a0f010b01020c060c0d0c03120524030109030e0411090d0602211902030c0c0a11151c11070804030f150902010c030503070c 65
    0x2082646541d01444151100c412042d941d11041d54010300220003030001c920b2581100c86162203113480f40c3c280c0ca404c0d407146d0b1900c1342001006c400c90100c40c1d450b1a00c6002c2175804106e180d03001003080d40c1052030455614440d0b41c840c0400203e000c01c000e01145074030701341071260000c1012010103d00c200014105135a07100003000c811340c844110304406030801d17030302d614062203803c01c2c9580544032880c4400561041000606001d00e420b1920301c000d1002c0121619818110101c0c24800d000044c0d0304c88448980700c903d0204a0003a1f024000000c0170005403004a640040307640c0503840b8003503102c0d101c1c00782d140800d0140c0d8429410907c00d070076800061046480041d01064410345400c1114208030001d640036201e50320500c240041608101005a01150320001d801c160126440c0e0400180707640720806684a507009407041ea407030010001c2403110001f0f442640c484900c0041140004950001c0e21101590b8800b805110340480020749950054080c3c00320b05030f2000100300c1100c0d46181182d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 690301519 1250 690300269 690300277
    0x1a070308010b070302060403031112040b070305060a061d0a0801150905060409021c0c180204030203010c030b0d0f0809030a0312051501050d0c050f030103060b1e0d0b060a0302060f 79
    0x9000503054100004110303181908072101940c142e03014040c2c5c0d0755161410340c0501850000c0c8648100c040045100c03070340710100b60500480c0306240c0a046030038080f10060944c3c0340540131512640760a001001416009003c054051881011082007039a50314005a8810340540c40350034070313500b0048070141d442441140e00e4207440c1d403e81c0c100b00940780c1106100c11209580002500118000030140c0800e860340e01d055640380c460080500c9150305c0d4001c40710f001100e5114607a4254001c20240304600e000e0066100256840ca01000303a2820700c000910328402611000c2c02181080c41150280484a812245140c1c8041c046985009a0b490014003050314404100360360f03898000420302100c41840d00502c0550305030364142c20710601d4040d03003001703181c0c040410051040070403201c5054000000514003d40c0900c1001070140807141c180200c0c02c1c00c5031000240c0414180035074080da03540e00c0080e8405c68000d4070628240c0d417150003207407807502203401c007a50084011030045100c681400c020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 690302769 1250 690301519 690301523
    0x902040e0115270b042a0816170a14091b04020a02030a080a06030204050f1905090706180302092505090607121e02070602070602070b0d151a07 63
    0x4010003654410503005040764403810b2060706a06203c21910f11612038102580c2588024400140d00307105644800c0c5424032068145101101d02c40031001c8542c1100480d0b40c07003d481e00d645145021002070060072445000d0f00021080c0104000c99940e13803031640040c4d46003035042e13010742140c103151181a0742d800f5801031080c00301c060582d65a9260405000f035038000701c2c5a40055042c07181149040d42c9801c0001d1558034115500c600c000302580c0d850160b980901135000d004502070030101c1000b402d0f003507421206912181040240508002c00141c0407084072090b150145a2039030b1184002180004c55101039403120f060070601c1605480c803070220200310030040e141c4111217010b00c2c080c0c40500070140841d0b400750041c002040840c0c060041c0301c21800e0399242099412980860364981c3c0c0306502000001644603180074001c40b030f010040040501454001058242e2910780c44403d01c0c40f44e40c003038120403034981101605400340e1003400c42c0500032000d4207520360490001d024825400080c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 690304019 1250 690302769 690302801
    0x20c1305090d0e10030c0c0c030f061103060a030b07020304080f03220e01050402160227090703080d0c05091e010906030c080f04051f020405041a030706120902040e01 73
    0xa00c1c0d0241c0074a0b00e002c0d080201501c0d0580084079004c09a00803c14280404140b1200000440003e9002000d90300a10310442150303000403100d0804600701d5102503104400410104240034090380c400300207030304132580914101015900c0e6102203046003d20383c0045242d1082c1032940d811068040058502c000d0020318041800c080c010602180203854411440d40e0b0002000510460900750010040f0b100c40007a80a40302480d0760104002d50203891910300140e00c1880640c040301441120705401c0310b1244010708040c2c3c115101d940d001d20820b0b44122510f5034949440403000c2c0924240c9030801d40003442220307525200c2c4034201466400d44822030015903050000315100d0300910030415400056961562981d407040c140e8a50084007901c00e44051080382c881d1322032494032401001815007983ca000d07071941d26140030300040d503030120440040c0200c400d00003120b9840001d00102110340d02d00e42042d402d8051540c0b20700030091311002a42003070604110400341c01054200002884014503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 690305269 1250 690304019 690304033
    0x60303021b0a1805090102040b0c2104080c090901090209010e010627030f051005010603060824060d1103061017010b10032004090c110f100c020c130509 67
    0x401c000c04100a030051207581041c01456808501e400c1c2c0c41345a0000d1008001460709807a000300001c0382d00030b6140008254001c0c1007924002d13103000c80b0446590b5580c80010704050a02d20503544500e5206421030090f03170b281c070000703030301010035000450400c0c1c0291904510f56103c2c01e520410840900501000c00c845c40720003207070740d4041c420a104042c20028041c207c1410340d42c548048a040b04030a4a02c2c1c4030341044200d6400c0d140c81000e0003020503480c0014094503058000d802e2151302c0c02140c2804000c408050000c5552071a55030b0301042c11100308a04160a2804040010a1600305505803007100c040001440040c8525019100207a0303180301085244040d080c01c3c1c4146000440d0403103207000400d00c00c24002d07007112500448504c1038001ca110015140d43d402d03013141c1c0c80302c1172042d102c0c5000300710302d600701a2032100f17000c010028210030700b030a8440c41c0e50713060150340b00540a6074a200d440552442404103044140004041d02004401c5628510280ca429103218405000342c0b9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 690306519 1250 690305269 690305323
    0x1020307020d0f0207030f0f12030605240703081918021309111003020409020c211303081605030703020105011e0503072102061902010c050301030807020906060d06030302 75
    0x441c40f6107000080358020b044130f50031581c4801e2182c80c142021903100309806018000039400303e40980403e581c0344d5001031034614000c200141c2403281c1c05910480310f0a003200d001411824401c0307501c007039018181015aa00d4016484181c0d0303504481080220789459010405000d621400d08409402158699a092008422001250381d0008000c00f030304007603810840c040c203081e00c030500c00b07640d941001810706507603a940d00243d0340103044031803040d084104911003465810614121465030002420b0401e400c1e400c0082c1000001d001c050040d00010401c1f40d103140c20f4880319201e40d07522100360b0761074001c140b802074042d1000307001d203002c83c0c6105000c5102c0300000743d0a010403a4801801085514905095404038101800c151000e40d20f13408907020151b26000000c001410400c501c00c60140c440030002030855a40c0441c7d441004400c00040020401941c1038910042d012500034806d0b480b4040011418480c1c140c422031580d003440b8001040c5900403405003032003110880b0300c00c282c11000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 690307769 1250 690306519 690306527
    0x801141b120403050c0717060c0a1d0409150b0909011802040525050d0b01052803151403010b060313120908070e06030f0d12090c030c03030201020307020d 68
    0x660001145010103000d00c85040341101c04041d0024060300302140380840c8145001e081440c1500300a01148446003015902e041c00c02246900641010703041d0f00381180c150300100014620181c107004174400b9401c2c0b119079030356a4050000d80e0b0340700c1c00070002280d90901e407901511607912450302c504240300002e0b4070000180103160004d03070328019420303240d20700c0e5080200a002c0542042c000111242a850701c1800a1044204c0540c040d01c9a60b1100400c1d0180c00c140c41200000c281000014850710307a61200b40c400c1e0035013100c4104655114400c01c4034003240200380d0032500c0790fa1b0070b100d6400091401e18084200304007520507002130165400b24800e0001c2480152040c1a0300e5040d001d4080200b000d59030903660021031490702c2c0701c505640e507000a00e880c0154000b51005840d40c410b202c200d28080207504a0385100901801c0d0120200303601418003e040301100d4495a1030318580d03810407042810314405540d002c1c2044180075224203009000b90811900a000340c4209031680c0174007409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 690309019 1250 690307769 690307801
    0x1109371a0f150d0f0b19060210020c1005070f0e060708070f031101020c0c010e030f121e1201090606080906041709060c0f25090504110901080114 64
    0x101610380600c0018480902000b80300c0340c000016814424801240780d60200c0c014146501c6400001050144103c820015001050310005102e103003031b04400c00040390080380b0320408002c6101c00680f200612010340c2c0c10200c04c0d02140c21180d140000300000c170340c2c2207020b00c0040c58041d40d03807000030007000c4144060b510641c840640a20400d000c694006400900c02c0c0440b24403e10300010307262500543c050981e000b0380c03006102d0740c0002c0081e80895038000c036100f011303100031401003070000303049084141c951125450350241140009503208200a2082d0034a42404240800d40d070303114030304864030f048002e00380101d682e554240000010168400c2c1c625500a0300000081c0029448590319190050020114162001400e1050148980e14040609010603409000e880000c1c8180e13840c5050070001a40c0341505034440c0405101c1012240e0040103903800644000350780d40f1181461561105020754244e800b20320b090010a035100103400100341d038080c003070100702a41c403886148800544 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 690310269 1250 690309019 690309071
    0x2b05090f03040b090a08070e09010f05010b0739030b06010203091f020a0816110102010c0e091003020301020309030c010c09030206030c160c080d02120403110937 71
    0x4800e000a108103ca12030080c200c41800510701040e6981d50041a804c1001c41e034040900b100b02e480c100004002c0078050300030100803202c0c08010560400ba103144a074082e241d8003900841040340e01c48044401c009010490310198000018030329090b441d801c00f006168081150040c03525000309415500000c19540c0000c001061031072402e02c00078040e2010130145800b41e00314810559140003040c0190020460350005420f500b04100f100e0a0900307214016a030f03840e04580c0761003c1130034030341d9001303104000da0b02d01260402c46a840e59180c0401601c1c660300003135030551000003803082003c80040103084a111541c020300c49c81c80102000d5660710036510029401200400c00541031607040002010b50b01c110444c0c5112034203c5440c0c040c04480c0c1a04045540da0215024181c050340400c542175103a401e0889652401d41941d4500d0800c11681c2e0916005443d1a0701040700d080d601503004840d240e0134481c1d14040301980b00411480041d8400c0f0810107440c0c010030b040911100403004000341 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 690311519 1250 690310269 690310273
    0x40218011b0503030f1b030a09062301091d060f06011b080703050307030e0d03050603150c04060309080d020c01091a150f0310020403080706060b0406090510052b05090f 74
    0x5500d01010702d43c8200000c14848005410546001c2c1010030f03040918010123161500142c1c94000f813a0003821901c034111903031446c4020741e21241344d502c003401e07445c0e0540d00c400c1004a50044c5980e48242101c0c11102028041e00502c001c2050080c1c80400e007510408090703a80d0910100fa60701003148042c403075840605144005c0241e040400d001c0d07001590061920301d030001c0c0c0c1c104039111040c14407403010300c2003000a84410070700101c1d04d420402c0c01482e01a035201081c40e8100310660100d1ba1040384541c10a06458080402c140100e101c1138420b90a2241004e6584803a08240c4030300801c03500904460f09542004003c0440e600e04002d94415030030300a074400403124040400a514500e40c903002da0611800a085c1a400201d001410045220b85095a11348009140a4058541d20f40201d070303001a0900c020000280d10000f0003080f944282d9007142c29414807401100d1522a0035120b000c00d94545070380c8407034800e80380980807900400c1d5104000c0b41d15503080701030302d603801880141f50a03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 690312769 1250 690311519 690311521
    0x1110c15150d1a101202040b01090b040324020703080a15050a03140601080c011202070602041a09040b010e0a062001290f09190b040218011b050303 65
    0x11281000095003040c0c6481c1a0300780110184000703400300a6260b012a414002c00718201c01c5080100c40e05600201c40349038418100e41800c5261a04020b40c960113403242d51104908100c0780d0152000c0e902a10409104655072510b80c10848035076982c2201d40c2c003540328042541c94000000d072095aa004e64181d80e1180d080d190179403031202030f002c2d0555a00784041030040000d002d66460100d807004501c9904d0519121354544061801c0c01c005034424820b9401090001155a0340044203580083c555080183c5495841c24020002d01541d007100550f80e03402500b03103009215a102411900408540c1400001d0010004541694803070040303540108143d00103014960159400600c0d1962072044041c01c0d41b002420700d030035100c82c1c4103c0c002d4060110610701700000307455010035294070b007641c104800e080c2030320104901c294010708140781504042c0f0100301c605540d82000070f001100620664442900940c034500c80400e1b9001c03d0301040692003134050380d00071510103180d0755802c10055421 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 690314019 1250 690312769 690312793
    0xf1701110706150510020a0302070506162d03121d03030106030b040f09030c0203070906060f05031f0e1e0402030606090405030d0c050306130b0a150e03070b030901110c 74
    0x43c04842400075104103000e40003141d9916000036100b030805c40d6600506881100c1d050103400e00750301e6002a0300a0781e042000c010030780d4120004591580e800510700710940d01290550b20023804004003100c241035807010401c00e140e84880c1e08281e4110b0b080c0204078040070450f4000400d4002880060140c00902c01000140c0c0203502c04002541c01400100d586441c1601c0c16045030400301c4100e001c58210601c0d00700354141003280c00b01400c003c4400700103da0500c5000f0b0020400e41c00440100030340040010340458801441021b088001c046481070280c4450b4810140c2e038044603005081a100480d0f52202640765200301e0103650003401904594490070b041c05050741d00184141c41521080100080c42c4c440b85c03003641c5490056699140d00e0b03007000c00c01c100740c10a0342000b2080103810440b160405d035640039217100495076410010021003158600540301646809405941030040410005109039010025442916001e00070000401d1803240030003940075010884a66900400c60094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 690315269 1250 690314019 690314021
    0xa090b030403210f110711060f16030e0d0c05040e03091309020409081b010513030e0f03071505030406060906081207020418060b030106060813081809010f1701110706 73
    0x24041e101d081c004900d46081c100000107845c22000b882031680d100107034060901041003000701096404880d82481d00340300f514030101d00c0c02803101c007407031500b01c10b0201c01c1010300450b00244500d1024003110741194141c01c0104044040c0c3c800c40d40190304012254100040c04030403075001c401c2c0144080315030441001c525000304503448040360020f6a0383c1c41c00c4041a012400f402206110300300c22100511018005400c6d02c1000c0d011000400030030101800181d003001d0700140c011400e9564041c48898100002e1500b440350703015070045081142e20044455002001b144a036015040038412a0341da042d0600071565244540300158000701c82020f48107040b6802030103c2800100081a602c40705122046e2000319280704403201a9241964025070801b2300a60006002034201f081e503901e4040403030b41d403401501d000149015800200c11013180d408002c0d00c2c41604e4050521042076031900800030700480980944c46070b06142c42940111884140039120003c00d408280030300b050515030f9404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 690316519 1250 690315269 690315317
    0xf04020306011a0a2001060b040602100510060e040f1a010809030703051204030c170901110d09060f0c0b09030c0f07300b0a02040f06050c0a081b120a090b030403 71
    0x22000e46605d00c20903501a000d00860000e081040310030750740c4034501900642340ca480c07601040c000b5420481040401609c02c440402142d800d401e01d404101e0b00300000600034410303031404100140c0340c00d0791101c001c2041107000300011020303220315885e0f44403105d03482d60701d014900000340020410480c80c0003004411740c0c881d030828405d0501d80440d406a648110b84030f0418220809151808101081c6a42e0310031b49024092502c58043d18088003000401445030080e40a800300b0b024024648014540c40344c1296403480f5001034141030a410078030705880e100c0d4072124000119104000c025541c132403001c1100e1007200c014208607949207080038001c519908c01101118415040101044040780e21103102d01c1c81303140c0500300140d0740c030704160b42c01c410969990404420002c052101910f00c900020741c0664003508202056102d201c0700384c694201044001c14103083e4050754050120500c13548000e89061101078580c40c1301c03142c4030090300da4503000489019000580c80e004024151205407500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 690317769 1250 690316519 690316547
    0x4020d0302030d020f0306010e0402090a0504020913110d1b0206073f15030b06041104120b1012050a03030c050c16030203060604060e0c0c03040306050f04020306011a0a 74
    0x41c0f402c200311000c1c0c030401c0341c110107081101200d0000800c00e0700d40c0c0c0302e401c401014400301c804608203c40d070008030700003521501405000702d0780000e03a00030320380d18040c090301c00e608920010b100011480e80c0e4120f140d0446c01d0020f001c1810b0180398505084030f8020702e1000c182c3c640c01002070b6075a20700c01303d44145034400e07500c81400750f008400b200b030700703200c1110b401e0a81110345013904807000e48609821158900780d2042c411650020a1000803e00f2a000d900b0030000c580224a58070890302c1100688a036505c02210120b849ca00c0c8805c0142107882c80740b1a500842e640c040311690380321015a569004000103140380c00480e1414002030003a481480c4040203490414200301c0c0011285140094016403061a083c120304200b04600c3c01f005940e5000324203440910209107005159902e0b01e60150481c021818081840d007914101001560002c6030030010600c5541090442006044d000b80c400340d020f400f030310001069020851036100410509032060310718001c1c0c20182203940030014801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 690319019 1250 690317769 690317773
    0xe130f032006150105031006110f0d0903030815090c07030c020a06091e15050706020903071409090a08090613050613080d020613080a1704050624030604020d0302 71
    0x19104a440081c4010728051103400141024181100184010032006031503504000b030070000c015005030b4030f080c00c90859045040240d810000c4d43c650505004c1011000c040310301c2160700c0300100d5a4056044000c603400b94441c41c8058a451a0a09250540245a80d04100e02314045000072112400038070115004c1e140c40c16a001d00c1d540000d5042000f82d004c5c20004030041400d000f1401e079550030b03501030702c11030140321b100341d182203014108001c2c3d200d03d0005120300403a181050103420703011101010b100805445010303894a0900c0c111403400d010382800b03205044001a0600710025001640940044e580d504020460301040f00c103034020080d90841c4c86a58078000740540317a000c040d00b000c0320501c8900040034140a0b54030310b48031450030303030a01710f41c401c506010039000c07020001103d16402034901c950300c1000d1542611151500031019842c003600e00d007040309003e80419a5401011080d84010100c0c41c505403044050909940b01c90341034014001260040c504182260005882401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 690320269 1250 690319019 690319037
    0x2010c081311040905010e10020c06070503070504080601090516050a08060618031504050c0a0f0e1503100c140a0e0618061b06010e0403120e01020f04030503040e010e130f03 76
    0x2c082001d43e40c0450080741c1685d112141a82e140300280413018944a140104500b000c00165010ba40e8007400303400304e01482070000c0070030b4040e8420022980a800210121541941c0d03483d4480c000b0031040b84e01c840c03200e10810329145040e00c100100c40c0c00071866034030009151034030400c1250592000150441c000f00c40032440d003450307c2c2401500400081283c103410f01d0724290a045080000e1201c203140701d0070942d070092245049016120003034609001d0300703544d560f8811a410b650048103020496051080b414110031000300c03500a180345080b5a85c0d83c00704403004200d00340840c012142d008002c203051243d4000b0a04001000c1e02005d00c455a0300c8075484c000e100890b01503441050300750700b041000c0d2101d075000d500800c0305034010710b0726000c407216078502518001e06003104144d104201644480d0840c00070442501038650740f5075506103965a6969a01e08503640e64001d1064521036500103000041d8a5500c0152500c104540b0301000130042c103075902c0c00074111184d80102d06000b00382c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 690321519 1250 690320269 690320303
    0xb190e030a1a060901150e04020d0e03030a141b180d08031005030706080c09220c030506060717360102011a0307052e03060f0602010c0813 61
    0x10028070030b07001e4020a031400c0a021520800e1100091402d4026119180104400001d00d43c00d00481c500c2c0e49000e44c90b40c0325400008001c1d2046404003420241000c20806100501200460040380146410080f1342a403042c80c00407003404540038122250302000c0b507246226090000d120350380c10160300040001c410000940030b602c01d80f4065400704404000c012941c1d608840b600040c2c4030440041c08124a4904000c2094400400c4400e0441020408199980b0740484060102503901c0382500300b0481d00d880d0400600d4544400c0c0002414440480c2d07003418800116450305401820034880c007002c0c40f840c0c00142d4080b107a06a40425000c00c0c103650484840c110070109194100501741d5003845200090035074210f100300c0020301c207500c400c0e040240c3c1c00243e060700f292829545052126960341801c015030003510540080103030384171000425150b041d40460f007698204032080139400e480b00d01c202e00704c4942450050200f0300c481c0109062031948190403000e90710030313000058100411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 690322769 1250 690321519 690321523
    0x20a08060903030118051303030230070e01030501030f030810170106170318090612060406060512060f0a02030c040816030c0b071a040602090a121703010b190e03 71
    0x441d480c006641000c40180a80760604150031060f01c26520140070354101003201a50000c0e4018004007450b500069601811124030350814480c03d4080403894103008100c059888070400306c40000c0040c001e034442c407045601a01c50b86040c0c0342c0007e040e85207402070781d501341e480c1900a410b00144000640d4002199032442c1001040c8078644800490b40c1d5240c0b140740103401f401c0506c4d807501c9410038000c1c0c42202503034003e00c60295008880036801621010007003114121030084030302c1603005400420050040c19041042110020b5600340d29442903482c0c1142c03101c10580d018205202940041001c03088190051600101d9820b101494160b030f034020280352810084130303a07110380040311301001402030f00702c103080052111780b00301072a0036800d64410b581c040e0004409100d9400c550042024042c0d543d0503941800c5019040b13620058480c4001291460f514104450780001102d03c070b075490410f202901e040355000181d0b1410700070f80d00048100005500610350030011b469104421994003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 690324019 1250 690322769 690322771
    0x30a05070f180c0e1e030a031701050105030402060a030e011b230a020c190905011205010e030f16030c0203031909050a0503031c0e1209090f1b07020a0806 68
    0x300044070703941e6282ca001c21112031640101451050700e044030a002d4281c0104100040c0d51003280c400101c04948014402101c50311002990140b1540109208140c1c1040039200c218601d008141c1d0540c2e43e40f401180c0c14802150300940140040c0000c1c54814082c1c2c05c03082c018102c040c00441c02c60310701c0a0a00814840740080400950500816006a109082d01d08501e541c010388039460100700381070203940c0300021040580141d800c14030a4201ca124011208090b0490ba2001d02855035540c40c0201840302c03c0300e09582d43c0d4600513200e54442e800004903500903000c80d40550401d034007041e220b4040c416101055052210600c0b010006a40030310040050007000c940c030101880d00f112000b00b409107070307412440c0159a12070302841565000010b4401c1104901101c031100d9000d2040e0102611010346820558849e0300c0b10300b624107820b81c000d80888181540c001d40541c2c1d450b8040c5482c06000d4031410041d51803078440740c1002e00d8110051403c0e90010340100e418030380c0c0d480c2003854100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 690325269 1250 690324019 690324029
    0x40c090207031d0109050319050c03010207050d0215150405071e110f151803041a0904050a090b0714090a12051504050c1c02100305180a08070809030a0507 68
    0x15601c11010500450400e400003044000c0c600041700e2818240400d6450a54422194003002080800801c110b82080700f9050107002400039500d0303e0503032034013694480000f1403c0c070150084507298410301c0c0742000502e2062186c04001c0130521505400d1000802020b07003030b00200001d443c0003d940e60031301d45007010700030980d54441e02c1d195030342d18400d428a0020382040342540c2040d0a491140550b81400130f820031a21420501c02c042042146032a61250b40e02c6000e21605c20b1004e505007007000000740070303400c0c8280c84c113015903900e42d04008121503000100404000c040000f2034120380c801c2010007140b41c20403194034541b15100300021024005a4803081d00e05146800840400400b40300310003291103511404005810980d941548403a04500b1640c000c442d034030700c51319000d1003060407000c40700d8015000c400c408a0300c0c10000e0103800d045850101c4a1045203c4070001c0741f00282c055655130704100454140000c981e0341022640c40b41d084590f041c4036015411002c03130014058a00142 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 690326519 1250 690325269 690325277
    0x10c030327050705031b1c020a03050a0b06040501030210110313090504110913030c02010e0414070905031207020402031b0a0207080d091a090307180b1305091203040c09020703 77
    0x240c901e02d402441c0900641080b8007079045503940001d40600003103504280a01284c0000d8210301c1c0c171408100c0d034001620080e6102ca1a41c00000601c40e000c06c0342e0b46214000c400700010b036a079820510003580d40030720009400807100348905480c2e912510841c10040b5001e8256807802085500b500742c01c41150300240001a80c0d20144401c10008024041a000064429440d40d241c040000f1650031036020011f01445a03a1401c0021607115550209282c80010010041078825001031b0307010810850300d031000710701502404103440c170f40010300b9420100304862107442c0011a909000294001403c80c16907002440920344807903680e203018011200c0182e005000652415810a107040d0822202d0000d200741010b06000362800d0201e07520146180320300c015a540005004240f03060b8080c0d000c0e000e1001c10310381061240419401904102c00e04442402102034154012400c4800c10380c1c1c900000e034811540d500c1341c3c04010001d141c0c494040c0c0c0000000c240c1d9410000c06990044038214002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 690327769 1250 690326519 690326591
    0x1b0912150c030b011b030e090705120c0a0e0306040b07050f0c0a030309020a0b070b0105010c020105120a060f08010501080706111c030c080a0e0721140309210606010c0303 75
    0x2c1d42d1140440c02c41c1340e889001c2d00d8031701d05e441e18080d003040350321303508a800780d0040070002c0d60b800d000c0c1c4104e031030010b058501060720f46081a030094140d0040280800010606a810a20340c5000110b00d40119013040300c65105454410b8103071f40039485106d00001500042c4482c50b41440180070360b101d1a4040e07200420031052920402c0840714540e0011180354a00307010b044081082e80c2130f01130640c0c1003070901c0c203d0000300e400140c03024080d907004041b007000300804200c584c80c0e00da0850422502501410202a03407242d2545080c2c91b400d003e211078580c0540410040284500300c81d46003020300301c040d1421030540d0400318106420b10314402011035140d084030b40455070302030440740d03010401100402c296440d4280700ca4903400c080c416405c2e0010030950105802c20810390308551242e000000340960725142c510b080d201e80203240218031440410020b01c4003e4200c046598800382e078000500950b503506c20054070b010007910001c0c1e04059869140300b02d50a603004410241048002d160030759 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 690329019 1250 690327769 690327791
    0x10803030f2202030a2907140702040908070c03050706020309010203121e1005090c0405030c150903010f0f05090a0309030b1902180a06020f0304030605150a03151b0912150c03 77
    0x20014910503181b0000181c100000c0c5a8081040c03980901c0154041c0c0d030343c2d41d460001401510351b03e03502804450f00000c1c18070070003048034000e108603403040c401e40d016540d8a01080c2c0e22800b40c2000740d800b58104100402c8030080f01c0c1001a40010342c40720149561b50802c4c241c046540e400c46890306d040c0291a0140160302d001a402a446801c950500c0d00c6e050803e00403a403226110701450380540c0b01c1201c0b80c0f0f0040250b80c180c42c025000503000b004a000520f8200c000b8000740101155143d1820740070999480d004214490580c0c3c250316409107030ba2655651440c400401082040c0740c918414040c0f450b039050340028019540c4480d41c0074401d903a007030308010540079554841c07810b41d40102600001c105000c81540c00710b80e005100002d46691781c00b80c0b29082e00c004052981d000b01001008420051810451018100c100300b040008208018000504400303d500303400200e131410070200122002003461064491280141c29007640402d00c0510a68207010140400301c0c3e182c42007106 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 690330269 1250 690329019 690329063
    0x1a0706060825120c230418030e0609100818070e1e01030302060c071406010e100801020a200a120e01021216080a0c1b0e010803030f2202030a 62
    0x50203802c003894450b08102e83c1d65034124100340c4588178601c1e0403100004819485040c04045a40300030384140200c1e00410030740c110300c1316020011804030701d24803404013982c00e044c41619026100030f00904c0d450003051000f0394506400400031010070f40301ca400074100100c1480280e0041603502c40918441c00d081282c08010322441e4445141d45502100401c0840d60004090307801c0121201100d603240403078240030b2030740e03005081400150b01c652000025000301400a06208180c6e02d408610403589407203602d4241c0c0300320391280c2c00040c02003004204899080c40400400c0040500711042e01c075040c0c0c0e0341c804459070b1644030b101050b801c1c64040d50f81d5070180401c0c1040d5010411540c50080010304004001c0903180380500411004600c8855440c020724840b0040c0703800c005030030161440c07900000441c640c9030180c4401158244c0000031810400000c0d613005082600300200d1a0b42ea101c4802d0118100d030a1003005100c400c00c1500168a0078840041090700803641c5100d02101482c000b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 690331519 1250 690330269 690330343
    0x60911010f0203070c031b030804030507050307080f060a050c0706050906070e042703030905030c0601080c0909060403030504060240060503040f150e0114010f1a07060608 75
    0x1e40d0000c0081c030307000481611520060fa940300c000c410545500300441f141c50442504001d217115000a00441804000601e544c1181d100320101c5600d107480b203034001e488088a2004130682c1c4d2200c070201b06800300700d0700095408000c0002d86030900409468141c1951010385415046410020500c0101c650014001c840d0800541d02403005400d51240620b40c00c81c100111101d4201c6510a00d081600c030f500070000840d04001201c0d19007071388a00c02c0791141002e2050381143d100c0d02e440000542400c13018140300b10701c0c0e80050845943c0fa924150003500c0010411a29a6420080c06412904041080c409202d002c000e5001d0099400d5003029003245680c0c606840a10380c14080040a50190482c0e9010303510020322950004549421200c200030703850140340c200e04050011114a205602c01800080000c40c0e1038041c0c0d0b41c429052291140ca4000d0209190001c00e5851038500c0e00b9004002051045400051017983c4004142c140203000c0745840400e000e0018012841122400c61 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 690332769 1250 690331519 690331547
    0x1228050a090b030c070605040218011715040816020112020307030204060e12030415110a0f060c0e0108060d14030d05040c151d03010b03100c090e010f0306110706091101 74
    0x10307407960138440700052540c0607030540105007075144c4e0300080c11901c40590b000c110740c02c0700030a80b4103540c60309008070595084120410a41c402d5032420b04c44241122030440c00360b50021402c82c500100c4205229183d00702800c1681403100c200d2551031192264170046124140690b070050b1a07038101800100296011250540301c2c1c900141303c110400d0010040303404035903102001119075116500140c50751030200c51707004228040c150483c0c090000c01e8400c3c0c40300f03d115610404c03100c0c0701040140c500d4070045c0c0d40d06001941c1800000d40c18200040d180c2c10581c007031b8810b412003843c810358692071a0700c0a07064101c03591f100d01c2888104089009100d018200080f08003012500300d0700010643c41c0d4146250080f007903051b101000c3c50f1002c0d409800c0034640074017a1590000544006009070200d001e024000071000600040c0c0d0050705005141a110364040803002c81c0d00c2c68841c8401f078642d52140140a5004000c49000142c15111703156501c0d200d4580c00c800b5009010001d8000f4080441c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 690334019 1250 690332769 690332789
    0x6010c2a0e0a0e0f070902030619080109110603040c2c09100e0613030e0f130c0e01140904020703090e0702100f060501080f090f0a260403051228050a09 67
    0x81035252650108601d4282c4940c000d005849649c3d10000800401c0c940f03ca00385981c00c50400440c0c1500306400c0040401c4c018040b13000ca0341012414001a44803c5070058a01c110b80c200a0108800c50a20140024403040c080e422030b001c11205c081d080700c825640303210242d004165481c130012990040c1c8c500e44020001038202450880e150409103e440c03e0300908001050141202599598500d1084804007400c2c0121034241c00301001c1c01003500444c0e40c03001c22628202441190310404501001d0100070000904000720041400041c0d00240400c8003808450180416148103242c40d4510a4817254024500d01050b1200a000c843c03002d1503402406051240c2805141d81003c40c0c250002c4998070040310603030b03540038031904081882c09900a40c1c00303424852024040c4c0190b03a001d880300d03401c3d5848500f40c4a0110a10584194400201503400c4509a02e0500303004501800e40c0c0c100b261041840c041d56020010221100ca0000002203407000c140041102d0344040103001826907420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 690335269 1250 690334019 690334033
    0xe190e07060e120a0506131a090105061f0504170a0b16080a020405060a050c1f02040e0105090112020d050c10030e06060103060f0510020c060f1b0606010c2a0e0a0e 72
    0xf07469488140c020180e0a00103100107010080149000c40c00c100020440c07554070f0103040c12703d0014040c00003950203500c202c8443d10380e00c1c0d0807902407420f40700b0440d50780c840b14500340c42c0c400701d1542e0440f000d4050400340904265640803d110302101446601500c41d0b0810854910b880501104070103024012814070510052005480300811242000b1950602ca030715405d919448502d044010110305c00072501d02d465a280c200c0264019205075903900c500d040e89a80c071a014481c188a007482102d031403010b940602d801605101c405d95400900407016201ca00d00080b01140242c3e40c0040d500740081d03179507507024258043c180b00ca150441800d10f070070321030b907460001401c19018050084a200720407145240b020503008100ca9446404003030006174482d8403100814181c2d4005410441c0c20300400500100c20b0600842d00d14400c0905031100c10700100d480c0c4a05070300580d0000095004a00c640d000e140e1140464200c000800304101c0800c0ca505d001d146183c01d40f911254040fa55500c505 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 690336519 1250 690335269 690335273
    0x60118030b01051201150603020a030c14040909080f0a0c023f0304050a140a060c031205061c0f05161a030903090a080304030203070f0e190e07060e120a 67
    0x1076031581183d0302152080f680c052032220071401004103413401c0f040501070010020303105030550083e200000e082e07202008080c5e0101011758203681d413916482941d0100700010302114426074000c41016008810150030b0003c503190481181e4041070016000c640781d00c5404c42146041d440182543c0c6c000782da134442207101000c04944e001d0070026034400a0905408460003031004205580040100410f0990341380d50305c000420200558203582c4d070080300c101c140030400e40d0180301e06826543d4103031f45035240c1170740c0c0500500c0180303005040c15510103055031101205110564586c4280740c0030b1050761701d20b040c1c245001403600280f03115100d41c1c240686401c0001c940508941405421400d8400b903076a690030040313504507c41c043c00c40c0d91002103030002180320000000030f0300a0724400d404481485440d40c0142c11b001065101c0c0351a001044130001f00b4803642c001c00e504408006200228203041c408545500701181504200c00140d0903a18000103442c094074004824407405005c1d00c006000d40d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 690337769 1250 690336519 690336533
    0x114100b030f180109110a0e060a0311010903150b0a14010e01110109050304030f12030b061606060b0f1201090504030206070f02030903061015030b03030d1d0303070806011803 77
    0x524000100603404005010f003802e0419214002694000800c00e8110600d0318131203495903596007601822480c2c41c00708800c00845285130041034010182d4171510700d0f594880401c04e8074900b40328100a40c40500000080503003c010810740d00c103040200d032580b03145003880075403110359000031240b081c409140402071360802c82c3d070241e820b001c0c60300221602c0300940550141c0350b0781c0c0d03004050344000240003040c45007a40d144400e591090380302e000c070002d40e035500f181507801602080d5031009080021340c00505425040c2540c0300e20411010502c244c3d280004812a04400c00c002c071204000034841403910184401c00e400740c01a00e40c100100e08054600964400c0c0c010141c1c5c051004c0e0007013104100d40200281c0340b05050080c122070442c50005200c4240d11641c0c810040b00d040e000c001c800503107009000d8080001030182c010350070040640a00000b0f021900d08e103130740c8100c11117a00c07001544240015880f034207060301d4443c030608200c0d000511350b0100d07481240d003421000005100007000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 690339019 1250 690337769 690337771
    0x303050409091112030307090806010b030703023106020f0a1a040f06090303020712050c0607140408071202091008070603110d021204050c060a0504051c0c080114100b03 74
    0x85600c002880348994a00600f20480380e00d60154400180100140302c13000000c0254451002a80d440741b00d20b0303a9400a07a55141c0c2801110070320002032000640725403080d4043c0010b4070031800c1815403544000d05000d80d0f0840b441a202185481107400d012803601045a0420060b41c003000701400141f91711081505400c401621845450600110f42808281c401c0b9080c0c15030030210400803000903140260003503211103c211101d026442000302994000c8040d02c0d048d01e004c40c003904103950b5605040700c880360b1011403146480400c0c0030205100c2020003841000c1c1c81d0142c031550303d844082c01002400c1c100141998840d6003180c8090000c0720000c11107500b19111800e021440504582020403070f800b890203511251880494400309140c03002d20080c1c00b86000d41d0503030b505c94032404107100e45489850982c00100d80104002c000301d061074651b20f044402c40b1041040888069541c40341000455441520107030344400110303080d850074110244d044140580b241d0810740c0b820230f5194172404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 690340269 1250 690339019 690339029
    0x5041409120a08011404020408030f04030b0a141807082508120a030c17090d030f02030618090a050a081c0603030c0308100f060c050c0909060f2d1503060103030504 72
    0xc80c18845d00c04e95100d41d01500d01038640c94081da9220a01d0318000c80035034000c2d100035a911001400840d0000d18103101d008140d4404c01d54501c01540e8000d0a41d2610001c4000303805248546540001c03000c90a21000d44082d098890509070840c0d030000d03544403a981070700641c056810030b50340e00c0c80711707040e0b40b0032501094990f06000c5041440d414065511021030030305020070030302c41c000300400e00341302141c0f10480c00c502d500c08102e0132406d0861681240800c80d00150000c0700c402041700b04231240c008140c3d00c00320311800c0315168403180d45d03501d0a02d41d042100300c445c03000214002e152021982010700c02c4c000001e808201541c80c44d24014101c102c00040078061100e900c0208000890f1600b9a00c00b500300715000c0242107685250003400c1c2001000246c8550044200640c3c00e440c020914074001d6000400401c1c0e41d44502012091a0001030604006028414410200002e01c2c1c074907515014624031820749070b49803c4045102400721030035142d00c00c0d0403240040c40065000310039581650 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 690341519 1250 690340269 690340289
    0x14060a0c050718020405180f191812020f150a0f090c0b0301090f05040c05060f1207090e090a051b030c0d060f0b0303030f060f0a05041409120a0801 65
    0x14401d0901c1c0d414400181c01048500d10001c1119200e034005800803c22900191140a8480c4e0307030b40040400340d00103a5140c1c203182c08032001700c3e20b07150300382800d4582401b5400c0c000840181100541e0380c0c02e01c90590858106000b0b007116541a50144460040d43c110040986000400c503100c0003d00d02d0000c2c00410382030707130711403041d090a10b5aa00114000d68031501e20701d022621074529401c507820074401c0065150820140740d150103003a0081d036010b10780c49252048220b080404100f00c80c0c101c0a480040f6000500400510b03d944030703c9a40900c3c5151a0150221700389041502e51850040a0320301e02d5000200320400680006200300d0280075a0700146400c4400b440081e00780009514081d81c414a208040d005009481c1d0145290a964100800031404050141500c13400122940e240031441140081c1d40d50925199514080000802400d160340c0c84070009000c590b03640d030203608402d1680d0100985804100706080c4005071007902d403030800702d01d28001072402d04140034091a04c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 690342769 1250 690341519 690341537
    0x14010e04020103180212011d011e0203070509130b030709020a02060412090f030308010e0601032306061306021b040b100e0303070605010602030a020c0109050d110f03030a0e03010614060a 82
    0x1303004072603603016829500030711555514201b041014083c104d40020300100024041c01603180c20014490798404020480190407542c403401404002500700400180611000f00601500c0e90b4404244004400380d107400051410300351402d0514022440c2c12500c0b800b403040101d04001c0317400140c1c5650003a4008070300808180342038021a425800c40d0302000c0040503400d030101c00c040d04404100e068501c40050b14041d6070b2500f004406403005146100311510184003400e5101f13600320307195641300802a08040c0351211300e840c2e00780d40c000c0701d07405540180c01c031150100062611404007030042d4011141886641101000a2520303080400e400b0b060028100b00020f032a1014025030750500d8000400700615a52050040c0d141d6109100884c0180250150b1405640c040e0201c0400e0710b1010b0111201c0301802e54a052070452000d0080d6880f4a60040308800c0355410002001284850ba43d1081401e6900c000e150a6442903002002188405040d12049440742002d42d80345107054a410814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 690344019 1250 690342769 690342791
    0x6020702040e0f1b030715140403021005030601081e0c161e05070b04150c0206160606090e010b031902010c0f03090f15092c040605010914010e04020103 67
    0x4201e000c45429040c0103c80181c50444030228031105504100069600d0102d0380904254586c49680240b029104214006020148c17107079030203036003503000259220714103902c90700080c0c1303030071440003c0d2030000e100041004025648480c420350081c80020f0b000d00e0705041507060107034101009201d00c0340c81601107044025011140210a4080c0e0080d01100c000e2018020104602c41054020b8840b481000d500250320b501035000c0340e04903801100780b0055800c20f41d004a0710f510224000740c0e446102804240303030483c070a6589542503071203503600042d158a030010000680d0155420107125900d01031182040ea207001c00c26403522581116441c80d0020f10b88018ac1d8807555040c805040c180d14101000d04240d00711140005481c540c8440000d0a81c2d5115044044102d9154060000d410306404102004042d55840050fa00300c0742d6045501810761601d10b2000c40803036040e150991a8001040b4210a034842c1242e2480208001c4181c1d41c18200e0381c03940d183c3c1c040e20090426503034000b0029 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 690345269 1250 690344019 690344021
    0xa1b0c140907021005221a0c030c03011401360906050d0803040c0308070b0702010510050d0b060619030f140105061b031306050c0606122d121c0b06070602070204 71
    0x1b490101041245001c0390841c10100c80c0c0205d50103403410010495000705441208680c240c91081003040e12a40c07445e8200031040c4040c3c1884e0101605001035485110204246202d0b0300300e01d140030340a10390303100644013800c50320aa100d50002d84410701d007903014801a101d50005001140c3c00c00f807003a0383c907110352414291010302980068414140820084100070f100c41d11035002e80c80a40c02440551948882505c0000c4507104050f80090f24186031800910f101540300c0d8002c0300244158281040990803155011004541c000080c1e605d0b2241d004045040c4104106a00801d90942d025030500c4041000b500c2954020147c0d00e0166400000400c010011103030118441038400710b420b81d4030716020301150000000760842e4001d20b40020000d003401142c07201c11400050090070801a2032008018840354010f0740c01070f6060040440902120070007280310f1003042245d1443e90741c0312940c04180b2003003805001c0700400d400e080c8458410341c0c42c03c054485854000c5801603445801d440010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 690346519 1250 690345269 690345301
    0x603030711130c1d0910030b070c0602210c0316120e190b0a05040302070b1605010608070e0c03070f1407020904061508010b060f0a1b0c140907021005 66
    0x303442e0030f0500b040709400951001c0041114051240951340911082003000b0a0240460b007a0094240030b40c01000440c0c041240c2c0303a00301072103007420300e0005060b07118001664083d151507001c00307101c4800c036400c1060030601030740c0c4108444881802d500f082c1c0c80c007122402d0041421000c0150208000743c8601c190b41c89803a071100310300d044075207041c10141255905085010f0998029440310f00042500b0003a0060a00c03c1d64964041c000d0982410000d0707507190054070309405140e0b459608040025024420000074180140040181602c0e02e50050841c8600403d440c10040b01802070284094100b00c1040414126007407440078005165a50038941c02100b4000c0d500c110840c007404140f007550b50200c260842e11340300d00b2041584615030282a1403010043c00c1e000f00c030800c1407960245050001c1c11007400170746840c100e0000d00701c07841d10710400d000c0015180032060420420a94a01c0d84030b2074540e0307170306451088007840c281a020303403240006030b030000e245500c0c0e034002200c082d4140041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 690347769 1250 690346519 690346549
    0x9060311010f030903120213030209010f030b100f361a06070206090d05031605010b04050a05070503040303110f1606050708040c1502070302060d0507020d080603030711 74
    0x401105a9908009490149100480303010074102d00252400c1c0303100b40128100140c040c3c4030506d29203032480204000b0340c00320031280c10312200b800000c001030b03450402d894020300c101c040c1c14040c10b045d800c103a21400c20240044068a201840801c4180030340441c10007261562100244c0c40c42c05d4000200e40d41030640e09038400341c1d10f2402041c43c2080260301001c0c003619110080000a80000e05002c0188114140a0b500200c140312030529458000201010940b10f4400c0e01c4c02d20b0441c5c10a80208041800f01311003030307519011440d202e41094400ca9174032140b007100621075801c00c83c0010b011071002030f2010b02019140d0388200d292100510031542e1110401603030b2641d80c514080200241d95441d10b08441482c189800b0030800780c440c00046025036007054008040da0300c1d00c544001003050f14030500301907018255002000d40e07910009000403d00500010a2610b080d40c030007400c041150302a0018000e9000602c6516100003042c0c03101070343d0001107002c4440b180b138009641e0103015106 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 690349019 1250 690347769 690347771
    0x70507080a020d0906030c090b0d06080303040c140904080a0e0f030f030d2306060d0f09030e0f240a030b090106090317030108210912030307021e2509 66
    0x11a41c0865001500ca40680c403182e507003a10042d11003404905644016540741d00040f03510a0611020340c8600083c60094981c0e4400a0303081e0303131803901c00d00b15001210180d800501d90802001200c680031110656080125980c07580c42c40c0941c0c40306498004d096000e01000365540741d00d280d54a980c0e441c0d0306284001001c81d002003400380c4020f6540c0e07010f0222a031070303103050030038103407003000b208407107048141c6007404541305a6610f400b400503e41004207000d01003500c80302450b65000242c400c0390081c60081c4d6804034a420010148070344a841000818080c80491190300c407a100071140961484d01580b074815990702d20300070f04901030400c842c0000d0740300b911000000b0f0b4058101218200700c070321135040c0c041000b10008610b04540801d1041149a030400c050348100d4042d140c07403000980108d201d445082241600204211030001c150020385a4000014404110380400480791450707803107442017050782c244e80d01c0c541c2c5030144500c100100f0380c0600303003040d1040118422240a0540c900c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 690350269 1250 690349019 690349027
    0x1501150f18180e1209040c0c05120a120213151d0103050615031303020705031f020706181104150627030210030209010e0d020120011503030c02040b040b03120307050708 74
    0x15113885075134009015039209900d00300901c02d0150140d5070343c3c956a500180034101d00c812602d00e5044950081c1c0c01c40c02044545c68006103000e50034805011095446091a54003904140310030340c0c24608003508400380b0000010640888a100c40d0441640c0c1c82031a010a1a0b280e1310081240184400b8004030421804000c120040750031703a40115005019078211030782c85984d1001c0c9600c98104490303040746007002a907071070000c000a0b00103125041c45100c00062032403411080c1400710080381000c4403030600040241c0800d25003401500c0a0840c0041c1e2600341c98a80f00000c0c1c00f54104401d402d46850b0a910140c28000a00380d00345c009580152500c044070b444410010000d502c00100716011481d100300185140c240b0307103007030303511315606840704002080b0702804119900d219422590765503485021002c3d00d503616882c8480114400d44480f100c3e004288100720035250700041550045152001c071200a0303a00180c02e5140e1024400c1496583c0c540c00002c98540c401c1030006082020001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 690351519 1250 690350269 690350293
    0xb010f0c2a0b04230d050a030c020604030209190c020609101d030f1c0615030509010902120708010501090219080703091e0209070201110307111501150f18180e 70
    0x840c00d907890540520228038541d6984081004170300300c2d1400609181c1c0301c9501e1800290280c60404103181c00101a103040582c3c0307031700040d100e490071141ca805a24000c03001140d4000745004c4e4030f01b00705450005e452940303132100d54950746802c0343d980389010a44500241c0440c20350204580350300000703302643e640d07401c075032140c00042d407100401548003044e6852054004e0f01c240718850035208000c1218083c1c5400301401ca028180c090458501c03956100c10f15030040c2d55090621505580143c040c004051074002004d0031904164040c03d0918010002d1a4200800b0f558203020100141802085619440d80450045c00d0000b00100000c00c850f035004050011048401c20340d904c04c8a0401142d42e40403000c0303003601d1041e41120103084041c804240c0481c0034a41e100c2213100c100d07084868840a41801229044c001e074402017040651714030006c10540d020440d00004816030529044500c40b02214074404200c41c032074107841028101060080004540162101c10704600454901c20909 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 690352769 1250 690351519 690351539
    0xf13020a03020403050709090c03061e330302060703051e040308040e010605070b061c0503030f0601080906040f030e0411070516050a0b030c030c120a0b010f0c2a0b04 73
    0x244c042602c0c988070340480061126541d000b02c800040d40501c442000d00e285956100242050140b070380907010480d0a07031810b40c240c6119450b802c102c0342c0984c0075104144401c0c60404a4092801340344288240420310160304e4120807070300c4140c3d05140075503603001c41e41c5907841491003c091032480103100003070020900500002274801c0d07888041c00c0f242a41d90b1103105403254850000001c22501d20700000904034600402910f120000b60410f0700c1d0015583e50310a41182d00807221115804140d00c10700c0010b590003140198001002002000c085c10140c55a000400b14030800400700452030601c07500940f1950084404400b50301c0c1003c2d1603810a2510b1902d50b15640702c806003001c1100e4000420f0b02e84240328100300c812907921b1501d152200401d500f016030008001d000c5c0c4810801049404d00205001c061190110380c40001d902502c90700010603a840d00341e1902e0802001d81c0c4030002080104510200003011003d580c5d03e0310301c80b40d083e404805500e6228001010000c2000031b068613403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 690354019 1250 690352769 690352777
    0xc020a060f0212030603102a0302031b030702100509071a030a0e0619180b040c08060a1505010e030f030f0a2337120c0f0e0f13020a0302 60
    0x165001d45160903103c88020225000495015626501148610050b401d466002a9000c200320300c0c6841e107400b2003404c0440410750b0a65410020381d00104008903210110714a02d404d244d4407820a10318108020000e5403920700c0d4506c0c1c0c000c969584042910000c04100e56030040402082d06002071186003010326440d0011254800c51a081820009200300041410b500c1060100390380349070707180441007550040c802003101c10f0030341d00f04020300b5021641002c40a4425485000094521804d1041d0603084c148082c000d06205400c05140e40031160041c0244000d842c401c0c6410400d0241550000340382000c0a00c1c140801e0000042e03007450750403c24014100103890781c0711070b683c0600da0070110f0583c0d8401c04c2450150102407212001d600c4484d4400001c03201810541445600c40990400c101e90400d0350003404600c06441025203500a405000001d10850410713a4100840e0304002e0700c0c0e41c42d40300215124550301c41d900c1b11140e940e1071010181240d4440210345402c0c03410320240080d40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 690355269 1250 690354019 690354047
    0x411040b0102060f070309140f1e01060308090402032206050105010f1e0516060f0f0b011d010f0224010f0b03040519030e04051315200a0c020a06 64
    0x109240042649500010b01240100c0b0030a00c9a135031035485601c00c038002c156040084400c9038126041500000c800c101792007060b028207020b4a41c444c500b60b0303c0ac03903490a0300c0f4581c2e10769040c04802c00c0803400d04000e8922900e0705a80150360781c0d0380c2c9050009600c42c074070341d00400b0711881102030052100c1c0d9444141a81d80a898030820811280340955070a40c040c00e03400319148801e52115902c038401e0015020070050480c23401c3c640d0049640740026120940381c5080b2031607844800f1010005136010b195601d40c2e0a08014250420541614181a901400c05818000040340030141c0034800c011a610300c03280b0300203400940c159254401001c06c000e124202a0300b41c0746601082c5071140304226030065511800402010951080c58000b9450800043e42889948400c01d4aa41c4441c020a4450003282d5029841203400d4609041e601c145444503000040c68140e20310f515070a031400119010020381180b5498400046d4121003001c9120002904a262040e000460a80200023000018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 690356519 1250 690355269 690355271
    0x615090506030c030c040b04180818040218150f040b0c0d080903040e19230c041404020d0603050a08120a150b09180106020c13090203070e100e041104 66
    0x52100c1c0109503030781007550005075040d0804244210384d450140e005d60038450016101061100d0101d016441c40a0741150a54941d6000520410301403110460350321040400c0700c046080140c1c01401980010007646854015502e1b4480282c0e40c1c07006400395010291040d29142d5100e84440c82040d9a40140307401080e1403061a01034020a070041d0303520351040c40100001c5050a1410a103a803e01902404100c4000e801c110b1030402070300e05000781c510b0340140d030400041c05212201000b200000c01400710007001424031050020321400350548003c3c81e0101c6003d44c03609000240080202026032009181b88901c2080380108010b400103030000144c1038030400080d0b0b0301d0803caa41520b0813241d00444040c9580c100384261039090007c0e003080d0b2000341c0b103014904280181414410740a030424000341e400340004010624181d056040c15690044080c000f0914039400b2030342d02c03501750007000c000410280008081c000c0400e0301d00010b100d213890075021420b06081481c0400c5400390082d02803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 690357769 1250 690356519 690356521
    0x507060f062c0f0c030a0912030b0f030c011202090a09020d050702060c040f15111b03190b0a0203060102030c031c0e01090b011a07020414091e0d030c0c06150905 71
    0x110303611080302071051aa01103641140c2d83c807401c0c5045282c2c0002d0403149400c0e655402c0c900880c2d160401b4241188c03642d00c0002c0c1c0003986c0e101b04a9072584850045209030b100f6100441141da016401003150765010101580303416401000640591081d08100841440400e400040c0e48140d0001030254000d502995015201d140303c1d00d81c544264001e5030030740b02c5030103410845239080c0300800c41507842078a0451400c1203d61407413414500c000740d0304120170103c010030442e580740501c1039194909048450b01304800051366070f11103942c4010545402694040009011a402442142d100c0c03010303101030326030342c3d600c9a154241c100311503601c07104100e242440c401100c400512514a101f500486400100e82c130301403003000c00c2c85108000440c0e800c0280070b0356006071a240503980c140c50941c281421503150000e4807614004100c0745110701c0c10041c101c1603003204000305071009106840c1c42d01207601c0d407101d10107030740b036030b1025500610300d0745045a20b044001800000d00c0640715010301c14803107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 690359019 1250 690357769 690357839
    0x4050a0605010b03090705090a020f16050c010203090a0504050711060c121003020102100504030311070506041203150314031209010e010e0303060a170c10120c02120a0507060f06 78
    0x10f07900046421283c19480b02900307105071700d071542506902c107801c10790252404166504911a41c2c12000204a245001041c000304100b0180b00b0760f80241002c0c07000303604103413404000550340740381751080390b008640c0c0f90041220244104500c107001c103180c1c03048891031704101d183c0100c6540702491071442c40e41c40a0105803142d010140500880e07405070f0081c8501000807100900030300000d4030480501d03541c0c1d1203071154100030b10003402c0c0186c05140980b60929080c200045440082040700d402c061905a982643d420802c499809a0340c00c0b0b00640741580700300030301c1380ca180325138040d80c03001100300c20030000c141105400c040030104012000380a40c0703901490055490006a9a81c0e5002da01104240319800115603000010010304044458111000e40800e00d11010145103000042d0f200c910001030303002038002e8501c00c0740c044c0700a0040c0c0c1c1c2c21b0780c0a84c1c2c460003102129400c004e400203800b024040d0303a401402003e41c0c2c50724100b04181c0d8500011001c4d000e1419680710390f0140c00c03c0c500c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 690360269 1250 690359019 690359039
    0x80406050f130602090a081c0311040b1b0c0d060506010f0c031e02010f0501080a0b1003080307080603030c070b13061b0620040b09040609182904050a060501 69
    0x1020b03036507003035403040e0728020b541d121400380d00480700c0a600480c00200019980000304100341c606c0c901e406042d814028207010003019034400e4003650800c018100401c00c04591a2402ca0b030380c0d0000c100018800c5c3d5801081241040001c206040e0700281c808000703414441c0984c8290702591003601c45031044602c640c02910030314042140a1301180d011200384000d000380c0380c64003c0381840e9100014540f550340080508031003003a003201c8400d034413260380c1008016652036041d801481c2242c802204901c0c0d65100503c2e40b0008200e441000442070220310303951010401c1c0c42c600501d000958540b02d031924074020190700b1030448218234041801d030004886001e01d8070f140f030300c90400c0004a2003444648412000e03003180341007400601d20351200c48a1400a0002510180440c045619a81c07442041044103448860700044030903481c010342d0000c152002483c0c1c2613001da115901c0300f2000e6403080700760400b03002d0811761203400c035043c1e04000411a000c0f68980c0c1e2076126440800a59032136401d00f0f2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 690361519 1250 690360269 690360271
    0xa020315030105130212071a04080706210c0332070513050d080c030f0c01060b18010c05100603030519020d09030602070516140405010503011a0d02040b060a080406050f 74
    0x50054204615107902600307250100035003002030311086610840c1e13900c0560f0760390810b003295248d4181c1c0200b828090001c0601508008104520303115403200d09138803102c0f0750020810a00403030a50b6030b0640e000e1403400303078010818000b4005d0880b100c01200c1e00c0d2070000140250454003005101e400010b050701c0c000d9040d103c028407200c1c42214102d00b458148203d0041c04e41050311121401e02803440003160804c002d00c6076010015407940c58518544c180c0d0300b035410030341001581e40d600f40840340491040440032003801009280808042e803030303418402d062140761101c03075003005d0600310084141034000c0c0060903540c080500200281031801c504a031a58510b06085000031000501000400c01c141c01a0050324010000e860600d0b81c2d44407100703100c02c01c95100010740720b4082034086c100c0c9054481e807801010b080d070090124400e4801a414400c5003490014400d000940070081903488e01c1e40902041c0b400680300316a0b070b41e000310001d84044030890301203424a007803078001000f4501c481881 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 690362769 1250 690361519 690361531
    0x1090e07200102371209020a060f08070f050d020a0315060e0f03010e0309010807050408060717090705060d020c03041d060913020102030715140115030b0109120b0405150a020315030105 81
    0x10a04c46425600101da030030a00b91101c1e0240d0b80c84200703440240e600c11080c90006c10340c070b4840d042d0740c880d041005802141d0040c500350500076038004400350107400408660801102c5200181d403400960400d500403c030602032003a2a070b903100f0000c44c5080c0c21440e24440d208044401c0c072000219841010b09a030101d5800c000242c10900c030411480d4001c0f03020310340080f0319040c09030420b074849030680e01d0003e04403000e000081d0050f00780c102d4095244d03140c0c1d0b04960f40380e028080c602d040002082652284081c020202540041c03031101c1240d0500685000c0c0c50900c200040341c1c44440c200d05440e5200b92591441540381d200800e0350031442001c008078003a4103130041c500780025030316040640d40c81c00321000403071343d202c006400e40080c0004d07e06018003140001c03041d8500604000404542002441a051006407982440b8504207940101c20b41644840c00ca0555911440c0050414110b415221089030140301400010082a0055482207941c1007046da2200158000c06080c0d03a82500c1c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 690364019 1250 690362769 690362857
    0x31e070f0204110c1204050f1002061b0d062d1d0411100f090504061406030901020c0f0d020c01090308070f21020c0a05010e01090e07200102 62
    0xc0182015040b520070b0103003001510b0708000392000c10714100030310700300f0120301c40307000003030500c164038120b040051058015100200114042d50f8080d60350705015001d14202140285d03170300c2000f1649000c50b1650030404106001075a5901c80b500b075244248010071203d401684800542c0c280c9000b08001200c2c035140c4c40b600f0a41013440c855640c4400a042034460f45030381c40818045071541c004160b80c0004c550340352581031036003c00007882d0000c01d4100e41e1085041031001c01c9211521003881c1051081160b415969403035020100d40280300e0160b13110014000c2446420008601280c80104450f00b50203541c81e50000500448001d810350200800e410018000100422a681710340c1031b00d103200321030080c00150640c03440b0b502d091030020f020005a025034400c0b03445087c1030943c00b00901003824911702c41d110b00000a001545a800b481c240700390400d0000360850300c0391948040801402515141c490301080000e4080c2d400344400d40406038401800c0c5c11464201c0c40700752040841490 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 690365269 1250 690364019 690364043
    0x6030a1e15180504031e02070b03090312090601050a050405090f07030309060224010b160b0a060911030405060f090c0d030314090706050d021e0301080f06070e0904020907120c02031e07 81
    0x240580360011b400034100b0440c0300c4c00078003007501c50501d0300450168220600030b507154038607a403001d604242d00400404680d00002c00400c6180c031307002100c0090318400c880c0403c06944004140d46014104418000244a154070000505822014620540d103031507090301c02c4141c1d142c1c80d849020f002c2c034080b84000c0ba280b04c01000f6210a510240150f11400901420320f07500c640c441602c0882d003610446082d1303a407035204110300f43c02d511030380ca03100c50513030a914150700e8a519800e4440d200180780c2c1441014140015881490620080701d200300020080390348207606040060040801445000310780b801d02c4003040d101a40013410008446455807542c2c0341c40440d01200000e5001070700180f036029070b0210746a5040e40000040d6000c2c0c60b078500280702c001c1e5004a0faa00e080c1d0041d0415040c0440d04100031420f407540e40d841c0b54400d0701070b622003055446010080301c10000b00162142403500d44042401040da000c402803041450304054010b00c50b00d1640e0000003407084030b0009141f401604 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 690366519 1250 690365269 690365297
    0x15110a1509120807020706090b120402031018140f0a021504091e0b0108070e090c0c030a020a0506070908060a1508160510090506030a1e1518050403 65
    0xca00800346080000c02081600165868000d54a9003101d0320021034403500070801c07215810820200100241c0c50b2555945190000c544005d105a507134220040c000f64000805545080221b5000c403040da007010444129907034070003130b441040c507101107460205510800301419000580c540802403144054000c405c00e03036007000104a05501445e0910600b88000102c1035894071a00f45d11404035000c2d0350840e401403402c14101d400c52001c041c10b2104400038401c109a0159014608d1071082d110103050b515141c2d42c40d19207005900380704001d84000a13180c0003055012894a0005100b01f00310384c51611580c100340c1360030120740110b400030742c80a00011340b120404c2d0006110440540714480b030082e160300640e405d207100031186035035289030318104020504224038402462107880ca4161001410280050003174800640300f0858030392900100220603100e484500e40c1e1440c20b0104010356016003290110100d10b03072140d000200c0d1031101030f41041080c0d00807039100d40d50507034401030111005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 690367769 1250 690366519 690366533
    0x4110a081501030b1e030120041403011506030237030b0f0a03030207031704050a062105090c1311030601140c030304060615030b0f01031a090c0415110a 67
    0x500704281055210b02881c80c0e41d848040403001111440502400c0b121901d4080c542910340010750607450801107429030010310040300a4805551b8400700038005404250002409000c00440501002000580c0010f203690990700801501e502c240d07880d0407402865410381a1500e551b01e1030302d5a690ba841c206043d02d8482e0340f04c402208402488989d0359100f0700c0208002c00203a42049025a0101310b043c41072000c0d240c0b0025040c50015070303541c906418400410740c2c1e088184501701c21701008031030420340f2400209542c0d260b0451040d00300070b14034108051a0303440c45ea031410a0b000c0e00303c0c4c0040207101485406800c0c0300c8031aa804962468854200440e14116441c3d1120300074201840703030a40100083c070045004c0c1d4020800481c5444c10007401140c2000e503079007590141403a2800d00040d549407103c0c154240700090900041c0c86020360400080454440101940901d01004100100c111017024209488411554a4031b800070064244c4011140c9a41c8494030380c06400203000050b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 690369019 1250 690367769 690367801
    0x70e0108091b0402310e012114010920030303010b182e081612150b0705071505032208090306071e0311090904020a0f0905010504110a08 60
    0x54801407400603000580041c00382c0304915420f15001d00045c40100d40c80d8543c01002a10341130020b200207500d40750f005100703005502c807030340003d200b012040383c18051085001003c60192034000d0141c10014034000400407001000309201c1c1d43c0403917101c0035600b0000246d0f81a1000300704148d2420b45400d080700e04410060448550102135884010440d46001c1104500c1c92419040460200c0301c046000e401200700600d82c01100b218024109902540311110b282021103107100007840c0030905030340c0f80ca82d41450300516100000001c04204001c00021030f40112802440b0081501299580440301480f05984660941c0f0005005000b143c1140b524056440e01c00c041d440c0c642503044c0040b80c2000000c4078030714082041440c03c814185504034400d480c86e4518078041150a00421100c1e40c0b0b802002c000601501c407110008046488624490700a80340044419044c90359035800341001e01803d0044d28051424600040960052a01564100540c58071603040c0c968036440501c0300940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 690370269 1250 690369019 690369073
    0x120c080c0c120f04050405070806130b010e21010c0e0d15180b091b0d0f080702030f0d020f0d0503010504050a0b100c1e02031908040306050f070e010809 67
    0x590410b05202440180040140e14040c210803601c481c90403003040100d1740000c2129090114103020800c032541c8820015010740d141740800079640f148180101c0b0201039003800d803074202a8580018041460442c01d0b400007021440082c8810308480c10101c4429500244454009410b000310000054480c08020160101140000749004981e00f4001c2d441400c44015110300c00d2042c1407003050070f0144103d1020210b190044051043c1800220741d0030a2141406880410031880b01030800c40d00008454000c0d40042c12039851078040214680c075100c089205001501c582c445482d00d000b001710701c54030440c410762946800c41e8a0003081c880501030041a03175064a0f1781d00c0d501d030050759030b1800c0014000007664545000980628002c808124138944160301d001c1c0d0120f141d8016540012000030000700f40740c095040034160700e420765841c082e640004004e1800c00081100a00491804510401c0d1300d44e50381e40202c05a07001590b1580007612500e160ba0069013540d25180104901c2c200070b20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 690371519 1250 690370269 690370273
    0x607030509030303040c081605090a02090310050408040519061d0607050708071d01030503040504020703021903030c140304110919060b0318190318150e01120c080c0c 73
    0x12401d0000a403c551084a04592009200c1814410240d08200d080c140030304104000c20024200400540300e40701c01809038083e10f400240100c419201840394200c9210500c40900203400c11340380032101508140900d501805001d1070f54210f00401095001c200d03103054a0322411444555000031000307003045125a0005810814040091020421500146012009042414200030b1600c400e440c078180400c0c48010580014008a08044110b50483e481101c0c01a1340300928039050307080c04404d003ea200c000d4082100310051541641003008050410b544910307211840e03078000e08550205a90144c105012000b0820003401d0842d0001e0704600488100700070301d42030080d004156225500401c2e0094404818070000c2c4060440f60103210b592800500402e00c0070b22402c2850407001ca001070b040026048400c56448003038042030018160070040340200b4114618040e0822102203082c9001a425407100301500707215103e100b403d840c103640e664219841d6411a200181c20003c010b12040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 690372769 1250 690371519 690371527
    0x4030518030a0b040605060a03021f020705150d05060612070c0503040503010c030e06060312072409051507031b05030a060b191407030e13060f090b0a0504090f0206070305 75
    0x656030400201541d1407150307111815a1801d49420000d588016103c030b0b0180402c0542030006072f4500503010122010407441c40040060b01e00101d10308601070b48405d800200c1e18800b00519207005c0024018014060020300850326407806001c0c1c03900c5410000310a542000011404d070034452615102c02074041c0b800c40e410241c0701d900090031a00020342c11800b090f0340300041041c49409010082d84140101c2c090030103c00c4103000507001d0b1064803070007080001c0400b541e924143c0a8104242d46065480c0304010100303092a000341d030f0301c811301da907003d6a040240014050620a001e036a01001a41304000780c40410a0b50036202600040c0c0001030544e02c4000c04212540c420001d406403800d6071420842e0125000f6000c1c1c030000321300e428000328003820030020700801d0f0080680b5161400c01d81c1c1c0400c1002c10324484500804494011814416070340c2c2d0002030783c00d000c3e0030041c101d01c000c542003e03410b070740c44041000712850158000d10b425007501d052000741c601000580401406418100d00d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 690374019 1250 690372769 690372817
    0x10120605071403091b0312030414030f0d0e1506030319020f0a11010f0f090b0705010905060408031f08060f04140105010308030118020309071a09060711030d0512040305 74
    0x2c03a40044503103259550100d40d80e42d24114140082000c010300581c00b03070000345c14601140c1914800284007508502d040c4814240c00d00d0200121480003810a084980318404000200f000d003030701440000031485001048100f07141d04c050b03144d0052030001d008521b0300c1c0599183c0e1600010340c1541c03906500032143c0c2507a040209101480c1e03498420a161411b4090020014002d120f041010704104409004a0022a0303040400d010590b20815040c50f15542c4a180050141c648100e0003000740c0284d1040c401041128005540144091300c2101d00300c01e4250f04081031100248900390b00b5510140100303108520361402c40f60054082c01c0300305101c08a040002e070030b40d82c003030b4012078400d040000100000d060380e200c08000c252858400758a5030404607000c980c0e03404640289000605040780384500ea034200400c0b9000b500740a440701e07844500c58181408004104040d0f10f01a0080f07000d401e9445105401311250700302000341e001050744854508640ba45c001d5000c0c864400003100000103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 690375269 1250 690374019 690374057
    0x6190e0a03110c130b040c0c0f0201081b12010f1d1b0c0304120b061c1b08070b2203030234090203070201140114120c22051012060507 59
    0x42d0f52204c001000c41c200382800b050004650b819803100e01004a6210000d00040340b030342001d03c0d660b409103441452a295426107201c000e5860741c104e003c0d9000000c001441255410b0058104e50702e41e0681000c4683e112440032a803d000d168506400401000141201d1000c2c1c0b040005d59110b00205828002281001491640700d5002200e0f0451681d41c1d400c03c000b00103001c19805041078075400112034405415880c4880f42d1035006007009105500c00d58442c245940950040ca100c07000c031800680c1d10601203016510100d0720800381c4010f45240c0951320520040700e0202d0ba8581d00401d101a4030031105601000d04a6803801b00007907a00c41c4210f4600083c01c404c01422507044010780c3d0707081114020713084500320000f00c0e04440f40000100a1506d0060304400000000e4403800380c14801c030080a42802d03008140395921a403003286501842c02c44c0118030018203110841000036840e4111406d011103e1441001100c000f50303030102c8000b46aa401103038202240d8100800e0701c64807035074102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 690376519 1250 690375269 690375289
    0x305100b040b07051204030b06010302090102010e01060f06090510140d060305122109061501030e0105040506190b0a1505090405071d0105030c0f03090a050d0206190e0a03110c 77
    0x182c8001404140e00c003d01c42d040c800c08a21502c52421185000c0c61503941d845c444000400c0da5041c15408540d000441c1d0007034001900b8200c44a0003080700079216040700c5402d02ca540101c40c000b854041012520382042c00400590311410b840705240148200210f440380c2d48890354000600340c4483c80000003c00412040c10305c80d80b200416519031202b51424025003100488904100f506c00051002c1d852001c07911030340188803407003180300001034240180d01034a500164448250b28110401c410b00402080e6140a406144103c039154100101c1c8071003500c420381c3c2407030341c0000d458008200d04403844607100755014483c10001d0600c070f1444001022602c003191000c0110350b4000161300c8201c1030b035a10011a4009090440c01e5042940b082c07062070081410001c980103002010440c417480810114650b00d0344481114200381407094000e484120940360f120b6039401168484440803040e00501d54203c60703150050020201c141c8089030a070b601c0751900081c03400340b4030207a8800d0b20b89020070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 690377769 1250 690376519 690376529
    0x4031b0b040b1e070b010b030c13081c0906090b1b010509010e0706030903020a0f051204031505100503060f0a0e030d02120f01030c0905191d0111030c0a0305100b04 72
    0x8a440b10000c3c4401d12211800030121010b4107010400c03400026011151a81034901c2e02000944981ea0410380b0b0300944113085458410480c003c01c002040b4400140d02c400401c0c100c001007004601e00041600e4a80540c00b030080420628a014004241ca40e009004a000e50181050352441000700f15800c41d44151072242c0c00e070b51608109000c004080041800420041c40c1c200240000340c1c034000d4039064038440c002d003050510380040040c0f040c200041d0285c0150070180c141e4960f03403482c000d1030198170000d180e5152410040080c40240b1210094001c451001e4060001e43d074405801484100f8010209890160340c0c039060618200700700040d14094511103c0140d13900440600c50060403002022803640307508600c01400000c07a1189880104c40c031000000c60941c03648116444096040c0d0103200c400c41c984000d4201908040c5071000d004243c4000800650556100c6000d00307101c11076001c071280b03204002da4400710b407003540025030007000580d40a035400c4d126500781580358003d03800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 690379019 1250 690377769 690377789
    0xa09080301031a0f090718020f03100e0f01030c030f02030f0d180f060e0d03030908030c071e0305090f0d02120703230a080307020c09190b010201020f04031b0b04 71
    0x148058620f8091040368000714880320201052400180003030303407106d503400b500742042e0701a5241001c10700c443c1c0540e511502c00c000100d071689881d40810760700201030304c82e0048003221003011a503480d10009085060f242c0111006820034250303264004000001c24040b41c040c41812034a02190340c060100a07410f21890baa10b529403c0706503c41e000c424420341000070403010303480341009111f802502904d007809054821488001450609400601c2c03103142c060100d00e400401c04c0b2101d1011801030031903902c1401c0858461a103810020301c101020351000300465001c04c00800700b864440e120111084004100b0003034201c050340490010560140e040080d98060282071007004252200082f90404003035481e481000d15a040382d68940301070b6000350503903400002251685200b8020701442102c081c0c002001c0f400e0500c455200c00800d200741c0003807070346011441c0b000c0350b206000311820090310400d040c0c00d00b030964030323002a0842401d0b411080c81c071400340001281c20500000d00010629800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 690380269 1250 690379019 690379043
    0x80909010603020315030f0622140606040e15070e030a0501021c0b030d020c040c050c1c081003081206041d210702280b0c07080d030e0d03050a0908030103 68
    0x3210201e0402d03241c802c511030b0300000034031f2100440008410303600c05059645180c0054403800d40f07079640c0c03500c0c003005070010ba85131140d42040303980018268000c0d00161020010b01c0242007000d42c40743c524038014400a417110340400e01444c4560111034440600070240c95460055a40b49800caa0001e10704503049540300340f140c46a00c1c1a841142104e040c2500a0b0144c1001110025104c03031640c42020701c201e5a0b00c18080d1200c0c45501580d20744a1004204e0302c04442e4448046c00b00281c03040140002101c650024016404181c000c0c02140d034025251420b000d10202083d0440500408813030304a503440d4002d404442030301803200d0590b802e0342d014020408000d030003419a000c01c07842d18562400c0400c00040180c88207200440f08403002c220885140c04142c40000f41c02903070394414440d200e404030f50b100c6881030204607042218800310031981800407030741c0140d0507100c82c01c0d445c0189812a10414020758081d802c100c0c0d10281d0040300080d8020940e07504002c58000303800507100c0c6c003034040b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 690381519 1250 690380269 690380281
    0x150c01140105150f0a080a0b1804020406142110091a011a2502100203180d0f2904060507080a0b0616030c0f030302090108180c06070809090106030203 66
    0x3e00041c258030610521610701a000c94418600b48903820b083d41c10420440001044808541e010101860004100340c118001030203406210150a940c142d01c40c0b0701d0701800080041d00c0489941502c3c4000e400c178502064510b81221084400031100321841c00303004d804000c001c0644c41a4250544106c0041105180041c600d2900c810705801000385058201c12103400140c001080d18884005001a00601c41d13006a480305500541800290000320440c0c24692a1341c020006e0320300344e0901526030740001800402c04c6580880303020050104c2003c444000017154220111039903600c00300740c038203015805154100301c04d90001c440a41d03015940f2424800490b5210b4802904000c82a02c28031407200d00c000000e9052040000f51111400f22440101c200342c0070b16030030492650402001d4545945505004c0c2c00703984490b000500280080c030000d60b41e51028001e85528840700b400814000d401034060200c1e50744012020740740600c2c2400706c203803c0e82da9a10b407035021b4111f81d640503031241020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 690382769 1250 690381519 690381529
    0xb16180821040e040809040209030601060e03150c120c19030207030305010509101401030e011103010302030105090703050a151803090503011a1509010507050d03050f010501050a0e150c01140105 85
    0x156407000c0120410041000410400c0c1c100d6a007281c0c00881c0c16940d1081507000030000d106850401d90180503c000004510303030490a503440d110410780648209041c1e60091090300388084510540c501018070810924542c24140940c0c03043c5171682007450400703a154824000758a5629480009400150300030405d6494011a801048180c401d40e80505042140c409407111a0103005400040c00302e184140d40c3c4a600003000b01c101d050020802001c120302e80b01d81580c82400f050b806503090001181d1100400641e41c03048a400401401078000e007559040b1541c0d03040b841414609441d01094a036100c1b00240040c4158800d03101c0c00c1e180ba01e841c041c14207551170384400d880a606024030701100b90b2101c0c4d401074041c1d41c00c881050b41d1040340b1801a1100d0007201c2c1c0c040d060740b0805a0140101380c1561005005080e00210001c4581c0e903600110350780d02c114101c40c8000b6468000204940c286080940032000c01000c01c5820144100704c55402c4640c121818800c41c2d5412004100304c1c181 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 690384019 1250 690382769 690382813
    0xf100f0b03040c09050c27130905070b0f030a02070501150803030a0e030a0e010302030405030d090c06090801020702062502041e0e010209030304060f17100e0f040b161808 75
    0x180010502051402403600d10306e600524103419403204410719510310300181c52040050341c0760003c0c051800784149540c560003c2c07010354401c4400e84610321022a6825042041d070350705007409004240780d50748600700c3c140a50802c000840e51507480f41d8440b80081c1d00f152408005d480f03c81d00554a91511903011070507510540a0203403071350002c10a901d1240c0c3c3c818a03000d103040013824056901d840300d20306240396100707800c2c40300b120502c0c042e00003040080384a81c1400f1940f9071b13622481c043c1d45500c1d85508030310804400961122080003540802c03019103811490000e114010348030301d980300b40c000c03c0590b054610b945124080d08040e16144113403512601c56620704c01e5008508011000d00401c1d560300c1032f4050070003400100c01d0440a000d12640c2c0302d070b50350294010003040d80e08042a10440e2040705e8001c1c5103a204000000510012403005107611540e040001d8003c69122a054440c01c042d90702080c070304000e165030400a400c0d0101c0700220041107404010034551000c00c54501079146 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 690385269 1250 690384019 690384029
    0x705120a08190e0607200109050a170f180f040c09050415050a140a030516051c050a030509010e030106080f0601050a080d03020d060e09060708130b0f100f0b03040c 72
    0x45481079204040c800050015031104150900c144600301c8010340030070514148000ea651b40d805c0c041c00004201e0f000c80c44c8204144111100307440c1c00908984401a40942c100c80b40f08240107004c44005a0071103c40d0310b88100000d455401c1e51080c120104055450040d000c1c0007188185204100d03078142880f8960380b1a844802ea02c8495007010000b03100051180724008030000c1c0301d80c0d0700c0c8041d0341d44401000111342c403100306c5000d44682e1441403a41c0c4100d200b502c2c402ea903034040c00f580701c81941e40d0300c2c0b803d583c2c800003a02091780a036400b40c03480d801210040d410031204400c882c1c090f4500f40b240d2805055000c000786141030020b49070798030300030050300214060240440c0c1040110400164505070081c2410050f85444c01f601c0d40328018a07440d8803d04085008a081c07100388500419024081c208654a03001d07565600001c00300000d400c0c40c401440c940a000004550707070030241d2419000400240841c030302c141d41d2890340342d034000c0d141c10202c0c0f800b0000061008001c0b110b010704000708 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 690386519 1250 690385269 690385271
    0x60a0605030303150f0603160806090c0714160909050c1c06050618010311100f02070b0706111b0c010804030801030f050a051204030311060f0403050705120a0819 71
    0x2410000402d45034000603281c00030000800440090b43d54030144800200390020f48003030745070b01c2d211407861580c0188180d9107010034217400c0440d41c582814041144103c40b00e00c400740c0341010543e0741c104202e00040045600d4098402c240050350400c940c2c040c014440c1040109655509042413418040a04000ba03c1040c410140740740304610a4205400c003030700100b0001ea0f0340c0d58603021450740d64034002c00102c0b03e4620000031040040c441c3c1d40b00700c0740205035040035424132a24400e49080c071596450b4005030780300b00000c210000c4044014800103102d100041400101e407105c03010710b50444040c4107006040e0000005003804100a03a12240c9024603040106040c1510040c0074460306010143c0011b0341080c0350002d0202c100054922316602400b29607440e012202d401209400c603000480004204010520072981c3c0007949502504400250344502d4584c0c0c0c1c2c0641d01548500000c0320b1500601d90340c004e0104506000d4140038207142ca40b8034030307882c0c04078040f0030020020390315507c61 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 690387769 1250 690386519 690386531
    0xb0405010e06070c03170c0f120d0222090506240909150a06020d0f09080c04180602120a0501080609060412030603021c05060124210f050108060a 64
    0xa80e80c0312100c018084015602c80e40e80c0d05080c00c0c141c0c20905540c1000d400c114040d14402d8a01644200400c08010f1010541c0c00b5040282c000944540207078031403c2103084140601451035241d035004020181c02d074451521741c1c008411131001c500105900c0b00050307554600811505082c5a00205003001c01036200c80080d41036401d0742840345c0178445080b8020810200040c06124440c070220130b40c0304008180c2c0290035594040255074450f2007907558001070b030b006801c19070b1502605a0358140d0b0715041c0501012403542e8207102c000c0140070b80180c11544d4404005010403043c0c4010036103d401c0304074100c1540791095480c0c0582d403040c0d1003598194069010060181004124103410070f900c6607243c0d404000d180b400f18054916600040c2d400b051008615504068845526080038860790a0f81c559a907103c44400745504514a24100716600c0180c80682601c2150203545100c2d014050004070031441008504980c0e41071075403007103203036180010700100e20300700039055203e0500481403150b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 690389019 1250 690387769 690387779
    0xf070e0c0a1202070609140715031503120504050910140d080703030b0619091802070507030305090102011e0b010210180807080408060f040b01120201091215021804060b04 75
    0x903204034101002402c1d80c042603800c2000301d6900300341c0e03100c0e4025092041c400c040c0b500107510b949031071159100c00403800300403c2105000e800780c042c02c07001c4c0910280c1e40d1442c545580380b00c400b10b0328a90040090822010450360f4a50b44d8141c041c5585000e00300045080481c014040b2407810f00d02132061400c9044000000d000c0c20440e6105903040c98007085820b017601c0440c415000e8540c80c1300d040c03014034510070f2a5030b9100c0d10010031150518110050f0803010500174049110304940a411a00848018404240601d004003030309041031000081038180709110340e141e52910441200a562540002c1e44150381c100044600280004020403031044800c00e000460b000e03d620090152001040760002c0c400c400307041d200100f070041c040c3d034140d140c000107084440c3c00465041341c0c2c4c109e07101300108106031905071400c0301a50603181c0d801001e06103a0440040140c40008403070340b95501c5000c000e50380301400909804001d190345034481300c02030300c108020345095802100e0829414401000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 690390269 1250 690389019 690389027
    0x30f010905070206160e01030902100509090619032907170603151306180605040b0c0a0c0f0501201902011802010e01020709090803220b04120309050f070e0c0a 70
    0x4820f0014149614a0704401b40141d0103086801e502030b500c86941d00f1141e22954020008042510088a01501c655180c2040114000d843c07040750401880d80142400000c1654440c40581a2480f1009113800c0d541c420b000f890398000c03070342100001c01c4284000c86944032483e035150440d03022806809402c1c840c502d0f80c100004010b003149140e802195151060101c81c0d84081c22031842c2040d03040101816040c540701624059a04840c01014800058085125402500c0c443d454564171084502c42c603841786025440a510103446556840c072620403c018800686c05082004d0100c60b40c407014001010945880d5411201c030035039050000d183c1403600d1540c20310705203c1d42400d1003080502d050004030324088090300078540c41d601c0c042602060051800c0074501ca0b1100c6000c00182040a4801070040d0194602c010030b00b003545004100054040a80c600010540c0c0c540002d441a00749c4619113407008442040ca0746401852040c41140d0322070f0089a840006000703207074544258100010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 690391519 1250 690390269 690390301
    0xa06030b0f04050c04081507090815060d170c010e0d0203070c05150f03010b03010311012618030f030f010905060916090e0108030a03050a060b1b0c06030f010905070206 74
    0x1d48100d6840000032102c403480c00c2550f0281640704d0407034008079403d04125072070400c107030b07984030118450710300c0001c1e48040096085194948407141003943d0b251901030110440805104540d880004090328042c90480c07009441003a02e218000302d4054100c070802410403a9202c55101150010064000868030b065203240031140217998509041100005540480c0035101e4100b500704400400020111941c1005d181600c1c0118244075035006144010343d01e03040e880c500c11207540415498440d08654000a03250300102c00341e4200082c29a5103202070856004516951802d4008002d001c03442620307200403405000401c8042007030b401d0407000181c50110082202c40f04110100c41c04d0800c074420142c000040541c4174030b03a902075071030700d910035142d42107032450f1800030b840c0500140080300540507107030031282d00d881494907000c7d02a0089041c205c0138203101605e842101d1a60b074203074442d4002144140c4888140c040c0b0b80d41440f8652040e9100500f00008640c04001445100a281941c0c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 690392769 1250 690391519 690391549
    0x50901080c0c07060c020301020c25050d1518050102040b130902070302031605160e010512010506091302040b06070c170a02010f030522060c020d020a11090709180b0a06030b 76
    0xc2e100400e103803002034027910034110800c0f02e9002c0c0c0705098507100141d04107566006000150b185100b030311001809181840d149019000040c0406aa41229841e50000c0d01003040c40049141c12003450301d900b82a60b110340d00c1186642c1b40082d0051014220401000c0642040305040d4900b00301d03520b000396203009940303811400d400180008010011300300100200318120b03110b1980000e0342c0d1583c681164078240b1906002d1256a4500c51026074103104042c8210342c010b051241d1919000c810002046580740d0898105550707505030a00b507604c1b80e02034808a44a40034a0800c103092124103661000c161030700b42d0055212003c51001130380c000030420a00e000c54903000486944501404140d101400400812941c0343c280c00b405000c20740e00107a86548440e000c41f0b800e80900e54040382d684010450103840c1100c948075501700707882c0c02c00c4241c0d0001094503140240035144e43d04154004091a05d824255981c0c60342801d5604144c0300c0c0303000800950400700164001030000c12080c5102140c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 690394019 1250 690392769 690392777
    0x504180303020a17091b1c0b070903150c0201060b1e0d02040e13060b0f0d12090e090106150e060d090302070801020f0d050c0903120a031b050901080c0c0706 69
    0x184049910802c00c54418a07681286403140e810040845078483c03201180da02c101003101b452a8000d41018042c0c1d81c401038004440340701c2013921b5200e0460004018180e0400c000c8800b00000c04035050f20380c5005441c00c0e0940020b020341100e08041c0c01c54000c3c2d40130209a0703000744075801603921400c210344034902c201800140d403103410125a41c028440c0d40c00c86120781840c0b80a0101d000b001c0300c08002554400d2000304101d401710020024140200c1c078026511844180071000040c5540a85148110483c18403c850300d132a40846003015070304070303808500d83c1e540c1c1230104844084041e80340040c82d0301e41440d001d100046c90100f1110310420004100440d190285541014420401c0c0320081c038405000719100c0019421a80140d4400308203070000604000129044242c900d0071204141d03002130080048103150103140742690001e100d1682810b5540d82031816451241c814102c0c0e0300d260b5541c260342c8204a0002421403034016200c104942d8003406250100c000c000350304003d035041418 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 690395269 1250 690394019 690394027
    0xc030c07050705060301030318050a0b180303070c031b0e010b191e030905010608190f14030f04181b27030804030210020105070c0b06180405030310050418030302 71
    0x40c0340b45442243d610964210f50000300000134950300c4182e18010414502414034a9540c0d4010005c04c1001e500030942194403c20000102043c80c80c03d0303203040080642924100412500c48541c1c0303e0081d0f0040c7e468a0a030351601100b52100350301240540300c80d0f54801110350410610940e180103054280442c0d00010303000d030202d00c2c014140c450300d540310400812358a44043c24000c000c0d1241c0c03201200c1e15803c107200031805580204141d04c4200310560f8210b801992501d4100c02900c03028000c2d91040b420f0308000d02030350070038801014218055006076a0315454000000c02d00d0001851071002c151038000780b600840c01e03800140464010038a40b00d14cc084001d22001400d000c021005a20008100000410040307104003402c112802200c0c03103101c01004900c00c1e030a9038002c9a41e0300008450101c09030014460f803035419082440684060f40c0c0311040000d903410098280c5080d249039202100300120303100000903c0c80540019641405550724908003220403000c2d4040041c10715401007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 690396519 1250 690395269 690395273
    0x1060f0e03100501060f140403020913240c0e0f0108010303140f041508010807031505070522030215070c14031c1d010e0f09091006031a0106080c030c07 67
    0x210410b09110010801c003c0c80d656039001a0003044010204408600c0d41454034050340c101a0689040f0ba03000f9042c580035969182040c0c0d000d05032070100300d5114031039a1801c50040317100e50074450b0010013050005500041000050100040010030b01d200e40880000d42d1180d903481000c0d941182d0780f60624074a06040c10011070528010803808850207400030900048500300c40450018081858590a685036268664143c0f03c220900010b000e54141014460034910a03502c041d601c00540c0c58600d003401c1c8c5019000300c00c1010026482e0140e1000602801503182140b106241c01038a1810302c2c0c41c0140d070350f544c52407000341ca10036202d49140702c000c0020107403001e211800d0340701c014490b421024901c090f40a80460481510751250b92620068a0342c1540030f4a58a0500312000b0300004000c14843c0801404c618010040e40b0349006030200c8150400301c9000e05005548200d04c54040e40016501c409100d4205a109408100d1014244040c102c61402200c0c2c00298440b00380d07640d21964 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 690397769 1250 690396519 690396523
    0xd050c09060f15040f06050405030712021f180b03011d090705030303041b140a0302270c09040506040c170907030c062a0510180c030c061701060f0e03 66
    0x20b81d001c2c1e030300070300341103e42d50721a42040c0c01003060355400803200020580fa04022075050059008607605031b84030890605c11082e04140c0d440c81640300801c04e81c42058a000441c2c40701050100e00030106281d00345040035104000e000002034110a409141190314142c81c40075282e100000c4401000000b00c003090b1240000d01032071014140c064116036a038101071a003028247d02c84502003030440703100c2c100405d0078151101c00c1c9440040040c4403008035405c640800c807045c0054031801440d400214560f0001200e2601c025114036400c0c1e1841c1e031103003040d03070500058403401028140316a04d000d1440000039000703100503d07800072070f60728024156200b10313038103280840c81d801c0680b03100d07042c0500280031a4860150340c00d02c2594440c1c03e0a60700c410081131181e03200c2080040c115080024184102c6115500407403081d84224940c980031000c549840800340031941040c0c0360744506103014404d054100c1c258000140304121410340a62401070000c0600d8044013503403007080340491070442d01e5175007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 690399019 1250 690397769 690397789
    0xe040b03100501060503071206031a09010209090c0c07050d1a060d061e06330c060911190e130204020d050a06080c060408122a06040209060d050c0906 66
    0x7222020005541c48990140807500112903c43c0000c501d03c041c114403684c0c80c000d04003280d0b441254401c03044915010b0780e017604002881420299402d0090b00340302c0c1d446120840c0039281c842e40040d5581100c003129800c00005410650240a02c040004000356a03505185c41e1003d001a8800d941d0707d40710300058110840b41c13401b1304502e003003500b40074404d40d1510000342140443d417420007401c5c3d0344010341e1810030103c000b441411444419040007001c500007c100750b101940c90703c20b136082215656101100c1192900b940c203009039020340ca0301401d10192141c2000320360b008042d215840c0c0b018010b01c0d031000924507007144000106580c11902d8540503582055001c000600c0340385408801407004102d0707846200120320580c420781c8214100f1300110b40c1910b132400060a0012802800113480f03902c00ca24082d0949904d8415507501c1d40c0008242011442f020040c0901e4102401003181d01034000c0e1800c0d100386002d05003480021f40c0041d4000410700c055882000b582e03289000100c00100d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 690400269 1250 690399019 690399043
    0x32701030612110a090e03180406050d08030108062a0c0a060509010207021509100c020307030203011b0210272f1e0306280c0309030318030e040b03 65
    0xc0001d144200300303d86044a003110015a80700500950326030825060318030142d070800443e00104840960715440001d000c2e090703000a040401d1f95a900c80100c0c100141c0c1420640f040440400180030956080c010503401003030402d034034580d40d40384100001c4590078006080010910016440740446820702811151682103001042030f03207003034541503010398410341d0101c2c4212050500c0030080c603200019510926006001c042540c000d016068400149202d07080c0e9041c4540c44001005a5003401000034441d20f94071784455951080502034a00911650b8440c1c89608181f600340703916400c403011201031311000c0e590f02c2502c00c0f103007410011a010b464608842c40c80c05094070b40140c641b040d051800040070340b864541059040428104100d80342c0400d981604040c020400b507141041862a01c034201041550b610b0f1001c140d644202c43c10341212101003a1038880c00c409040e018400c180b14403200b141c1605840d031440d5002807c95035030031001481a035a034030f09030342552420403911008031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 690401519 1250 690400269 690400289
    0x102070612150f080c0306071b060b030609010207120e010804030e040221100909232401150513050108070e06160b06030f0304090b0f030604230327010306 68
    0xd80382c001c0a102c189044c00f0300000c5210344800c4000c1410001003440c41a00165202c204040c2ca8000c003034410703566035905032102d41d12145440500c1da0b040c02540c1c040e43c2e02400060b914000ba180036007141c1c13249800175081c000b118221321020398200400c0f85d030082d03040c9001c1c5030080380100080d0090007803038403030035086210048012120340441c0809000310241d407804d805607652401b0b10829200c8110f00145001c500380c0e01c0424103e5100101505160b086064a0b0b082078074503c4043c500294540035000f1110340001008440035204008110140500e0140e00c0c1008040c044151031003a0702c0307441d040281c400300003000c0611030041c8584100c0d00400c0a6a80c0000c0d160280360000100000e4500c0c2c400741d00822402c0c5000244200103203240b401450805180002d180000c1030844011500200078545084607542c0070301005101e00d21610840f1030381200401c0c0080190008544510503038010400c02c60ac210110320349a6500d880d50306043c05d81407201004801405850380a03441305 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 690402769 1250 690401519 690401561
    0x303050f13030b1003031d0303190212030a0209130504030f141b03180d0b160302070b010602011b081b1c0e0d120b0901030609240e1504020102070612 66
    0x1a1300000c103c6000c4034042c1d03443c4510a2800d122100e0700c01540070317115906620400100381c039016010301450060307410380140d8101c02030104000c0400d03401107446d081d40544c0018044030902c4d00c40d4401c41d07100250f500803c12881c059902400003081440c5020a0100280180c040100c1002c12120058a43e01101c20702800703440600e80c1d2500004110324100c0000b07101003102d810b200c040c602e245c0d50400040c0d00b040e2280030410710000032145005c070406808218490218803001c02003802845140e000150f1004140d112104540000c4480c104008440090000740e0440b01d001c1107040a901c40d0480c1d680b0f020150600500c02003e110201e03550900e00c089108450100d00702c044140e154441840305e080c018050700413224105529035000e01c4e50001480071560f21703880401d501e4407070941d0000d210b50550000c10303d4102c1800700900541c98003903011080600744025191a50300203411041d03410716074000b07502e9103c81e000701010040c074031209440c1c5c500150025000303902034955a03008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 690404019 1250 690402769 690402781
    0x6051c022b1e0905010513020a030308100308070803061306081b040f0c0201050f09150106030506030109050f01050712051311030733080702100e0a0b0c091008010303050f13030b 78
    0x2401c0c483c401038480d546020005072104900c01d032210100782d40200b84039000b0b81590b4058601070006044180306408202000c000200c1c00c9004241090103003c9054032464140108081c04201c104048040c0f810700e1010010301000061a405c6540d884020501002c200d4010600500c580481c584a160070400d80c3c00b00f0b03580642c091401418100401d00150766504209039031075158403003203405c0144034401040018031a5000b241c00c010000c1c004500b00c01c00f41c64082c40d21800130f4209041b65552002d20204940103000301c003103580151307028022450700400a582e0b00340717445000303886004103141200e2250340c28400113002c0c0c5040c0390b4849568075010a040340d006443c80c0700b0b400505514121a01c803c0c091050140f00320400d900070f0880d2018440c0c403201a261080d101c0c0001d00c600e00303405002130b1a24000611405164409076260301248041182c007480c66081942840070384030050001c60360000032900807207502a01b99941f02c0702510302c003010103180e601c060324410901081c000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 690405269 1250 690404019 690404021
    0x40b1305121c0c1a0114120c0103050c0f0309100507030c2109020a0b03060f01451211060405032e05090c03010605150901030905030c0102030106051c022b1e 69
    0x4140d4030310712540c0c2c141c2c4646c001803100305e07060b40004050a0b880b213649004250720a401281c1c1c0145c10307007540d03410012601c84c0c810342c94105544003c815006640e040d001c502040c132078641e01c00c50503e000e024920b01c00720081d191a0400100c100801140000d84400c81c070650406d18600d07501400403c256035550720005002d80090310312911030071592800c031b013456110307010480c3e0905182c02845a4604203a81200400d2135080d040da03090081034424010b80710000881000501ca1b00100400100040c94110054918014028032aa400707010500c12034a001620721940c000710390412000d1081205896079a41055460403100c030b0a240c1007141448010450701e002e00000d40c001d00c6003549410410010301c1201c03018080541003403105c05081e40c0309811064420b401030040d2440c01d1003040300242039078001d8100402050001541100f002c04000d10540d20800e2801d046080400b0030300100c2032588080200d5401140d0700e4440307000880359130711103e00d030f040040c040c1440340d1815003940 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 690406519 1250 690405269 690405271
    0xc040815010905060406030206030f04110405130201090b07030207061206081209121c03020f040504090b1906060903030f05090409030909360512040b1305121c0c1a 72
    0x1a50b50390400300441c80506081c00396000f500da00815107030452b0b0300d071500082040002407040c1c41c0e00c240c070020100c00e91503610030503001d50019243c05450200382e00014100c00c98940c03081421102c06c00900d00882e0307000c144803003540c040d8034000c9481c1049051540107041c4d16007240506005242c941c00d007440b290b0b40100101e40040e11b00100c0104140f50b031644641825081d40d660103558201608181d04c80c0d03004003810140240702d1410035442d8804101111480e0004403001070103030051081c000c6203d80107480e04100b00340c0034000340703082c000d00501070011340c0b00040c240808280c1d6501c000380544d0030740d00980b40c0a4400c008503070050400400f078204610512100b907140c04212240c02c0110b03c6526040c0148200380742e40c0180c28902000c41701d0102c00180c80e030340242d11040c000085400001c10040544032a141e403070340c803010505554800a035014030311030407400b5800d84240c4070105000c40440c910004203c040b00100b2001c0e580f90004910040c410b400c0c0010b42920f000c100c0c0541 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 690407769 1250 690406519 690406529
    0x2131e0501080c090f130c0909050c030d0c030c030c060c030501051c0c030b0402031509010207050105060a0e0703050403231b07030b0412023f130e0c04081501 70
    0xd01199070707201c44a5403520b1142c140103402158020024103a0803254444507005582440390b10400303801a2a14014074082e070b00403643e07140e118000f00040c400100304082e444002100906010341031010090098031602e4001828070084090b401c05150090100c503420700d40180080c480340303070307d0000200140802d0190301c1c45446590802c08903640c5509016a00980c0544414021801c2d601c4224201070010802c84c0d141c0f2030000400240401046014059501c80c000941c84181500d8031509503132000f01020300843c841d203c1003042a220700012500103c090800080644903410101c665032000e82c0351001915084150f52402010a00101a000421080c60741460300948400d500c03000180b1025110030740c0d200c0401e01081ca01400d6040004c4103004440100c44420f14004079055011a40c1038a802d0403000c2000100c0c418400455a28030302d0341443c03400a41d43c0020310030360001d015026500c0204000141124070100458015001c444100c4107041c034414048000345e2824011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 690409019 1250 690407769 690407771
    0x32040615080c0924131d0709230105060a030b030601060f140f1e040806240405160309030908060a05011706130609020105070b0c09120c0d0f02131e 65
    0x80e00c0c5640c128001c1202441546284070f07a010050100051707100240c4040c90110b69031030000142c1c0c0200d44a5480206030000640202c074640707100704003100e84c0f00c140d410b003c0241c42c02d455240811941418103407042103856645a5418290403401401040e02407034051040c6070000c2181508a1821000009503a42d890f0410b0380607614070a40c1c0c01172400c0059220814003d17806c0b80380e42640c001000341031001c4564103241e5641ca005150010594100b02801c1905031220040c150340700c682040d6031002d40c0c007401642091030280105541803015182056038400c0e038172007054400c07620b05000b0442c2004465690400041d035000821080c8114204d50616402544841402003000362040c2c3d840121100e00e150700d83c440f100a0602d465040f4104071041000c4400100c20a82d0540109507144070141c603089104103001c000354524040c0360b0715910005041c0c001e0b98400d0f020017a03840d40805030310030140c4035201048260b0202c0b10000c1500e4141500c01000030181c12600d03034600d40d4000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 690410269 1250 690409019 690409021
    0xc0f03020303220c0e06060d050f010312020105070f030b030c09010e0f07020a0807030305180a0c080d02160909051203070806041b020319120f0f32040615080c09 71
    0x82c005500d0024260010104c001181c3c0401551414400645d8007100143c4a149000031291014040f40c0d41221a8003614504000500512402180800203035926000800860030445000f40c662001e64906804254070b4a00c800303000d0320107121041c8060b50262190410b0750b10307080c1c041a03072442252820b1700e80c00c0500c0081c451500c00104100351a40000c4050700c0c02e100b5450403030140034010103c0034180010465082148170421200c14a81d0041c40c17440359050501d2415400c1002100303010f021540036072241031100c07c8840c40c0f0381c12950407210000d07590f10285096428031400c1c0c81d1080711900b0200401049076041200b15100358001ca5040001203102240418080640d00740000164001d00c09101d904940343d01d1020041000d04200000ca0942910b040c16614074508c6140019190041000d0403034130350041c441c00381002e400401544991002c8541d10f0006064400000c00d150008201030150325841904a046501315000500b9240e44855275a80c40d8201c1103402500508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 690411519 1250 690410269 690410311
    0xa1b061d030d1406060a2601061112042319170706020d0e01032013030c080703020102030a2604110f1e10050d0203010f05191a0a0c0f03020303 63
    0x500c2d00d920610004050302d04000036184c088a00344a454a040c03440024050514070002c147e614041c0208519503400041220000031076040041e0722071100b8500800784000d002031021460b80030959204c54098480000001c400035501041200c0041061f13001510045548910380c54101d010004640480d1806640d4500490355400d401481c1300029059841d0051158800d401100d07800414040c10300c40444220031806160b4808442c6825145e039140041081024800e02c0000034504d07507024014a03842e54001070348078400c41444408018004480b42e4069440012100130040b0b0155014080c1c600761400f40c181c055030b05d11807407141803021904500d91404000030f0701406542c0020b0020755448200748844039200307008803010710a06000707012402c100361020354001c0101d031142c101d5491801c81400f0300780382510101c00c0d40b1086007405000042c07039408004d094210f075944a42d41d402c80300000701c88449604030001c00240358110500b05143e4000080c5008002080304020117240322 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 690412769 1250 690411519 690411551
    0xf0e01030203070b090d0501110c0706090506070807080f0c07181e0e2104050a06080705070809041d010501060f0302040f0b070303111b0d050a1b061d030d 68
    0x9110080d85588052014440641404082c2c040c8000180c9003034176a14203980c480e030039109d000003040c2c007490000c10700304030100e400c004610060501d41409a0424180804615a4420755030081c0015100140c80c004020311003040b504207500448a40b030301c03003460b608455100d842620503090281c91030103d124619406e40702c0c1440d0750786405024080906042c0b10603000e0000d1100c180c507140203110843d088000e01083d1240411001c003061aa07890074941082041c400c0d03a0080c0c802c00c40441e00f003201c1070340c005045560035500441003503214485000024040c0042c03000b005204645510f800c0200901508070038141c0e041c2c0d4030b40c081d10051140088007280114801c0b045000007004c02002107030100b100800e01c1900a1801044c0d07800607a402d81c00540c4030404281c2401000d01d11881c17031060a001c02c0c40700743c40d04d19250740303405c4140c44020300902c0300ca21076984148100103514200005940101012008060748021075002c20120540fa500400304138135400d407d10b2038420508041c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 690414019 1250 690412769 690412771
    0x3070b0903100506010c060b0402190c150603080d020c0703120201090302011409030412060902090412030b030d0f200f010204180c05030f0c0f12060310090c12080714070f0e 76
    0x106941d90302c6c600c211501d9080c00380c0503007206e40c3c0d0072a0b4204070210b56520100d0f041a44040c2d143c450140e090b60f6494400c09a002104441400c07520380f400600019020710200c484026060300050385903034100807140d09083c4e095100600d0103d6040e0000c01c1c10303806401402d0200c0c042d8008010f50240003141d246000000c071000038071604100014011400c410400316110360040c400000c0310340455020662036101a40c041c0c0710854005050140c0c1540b60207001c138048420b40182c68801d58404001e411400034070400d600380031410014a903c2e48c01c941a00c5805094403007210441040905454000d601500810b8407011030351003c1c1c0d42100d10b40c01070000c2100300da42c55901d142d072031002c44400120043e00702d1440303403c01c00c140e0043c901c1d4007000d0441d02c400a440c054090600004051814545242d0081503a05240d4500c0c0428654880001142c40300d69012000784400c0c0b6241d00184a03a400060241e4901c403605040c190340080c522090310004980603088940350352200c240c2c414 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 690415269 1250 690414019 690414031
    0x301060c110315130515040c08191e06020c0604080406030b030309090106050f0c030d0c03050601081e06040e060a050f010503060c1602060d0c020c15071a0705070203070b09031005 79
    0x462080800c4030004c00841d2071100303c1c09141030321001c40040301218415482910140c030003800059041c01f8012040c0300b00b0030650911114145500429680e1713041c41c00d240740581c100c600440b110030301401035680403180d641611400303440303040c5420300e008000c9421a004043c00203190141800c04c1c4d003000400c89440d610012711229490b0300c1c12004441640c01406014010601445a01c80b1094100050051071140041c04120205405002021104020300700ca0403c20540e05000c01d282030030301201000e2440724050401a40c1329070104003d8034480300006420310810041040100342c0703a0025014018040c2d862006036620001c0581d550703c180c5200d9400e41301001265032081c00340f204189030610151107242000f11502d145001c95141da0500c001603005034140c01401d24065810a0901c031340148564103041071070302d40078081c401039080320036580550b00219940d58080c00036954030603401401c8400745501c031980320440d50840c1c400c050083c8203005a8090f0b80f0480e00030184503603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 690416519 1250 690415269 690415303
    0x20d0f05100803220b072402070f0f03090b0d05150d021c02010e060301091e020a0203090402030a110f0a0807020102210426070309092708090301020301060c1103 71
    0x6180101d40d0541a007044d40721103024000030001902c03003000c202500415005105210185616080c6074034020744956021000e11310420200001468411440404641041c442242c21071146000c0d40c00140c1600900d10b02140442d4410360b032089600107501c08c88041184c03550f50320300f0700706020381c600c41c8000003580b0501c3e41e1113018000e20010352130720000d40140361219141250f000030500c15070003a0408816540c4131000020780d10090000001241102e0a00b18503003640a5030094482c014100003601c100d0700000401d40f20000c5070401d1000d10306402e01d141e514050011002095840720394103201080b22100090311080c018400e4542034814824982d000d0400c940d101440d4980082c012100c03d039407d103802d0b0b00400c0072065080c040c900001c405a8074032007810094000e00c1c140c0c0c030013201030707042642484034500d03c480400868610244000b00001c0c0300d240c1000301d4000e4420141d0998404000015845c0d40311076038031100d41c01840d00c46520030300d020a16481d01e042403c92a1a2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 690417769 1250 690416519 690416527
    0x60b090601170c07060c09090b09010e0a02130807060c02151303020f010c2f06071106030c0d0c02100b030c0109150c06110318150406090c0306020d0f05100803 70
    0x440c9114210641c40001030f1101440c200350355032454100e07030140d04400d00080803500180324041e0240b107580800384d812103451080750300d0400c0074200420002c009505050300840e41f0b90421004040c00000b41210b001607a01c060744860f4010169020a80c0692044103100a100500100034089070102c8042000320029242540c090280b03903281040058100403103512540040346480380307001000a04000b120030300125580c03101c1008420134030418401c4004010703a000107082a8900c030162081136980980343d545089507082180a040301d000402030900300b0404502e81d000c0b42ca1124854001410000e402d280c0090641e14510f2807203d9020179074046d4140086050360803c102901130034030b8404907100345569000142c400302080300030003500110a11002c65403a6269101082c01a4010020030303090507205000403030090009041c1c1555005c840d020720410720b4080010f0354000c1429561030150340d20042c01001900000074000d864440400d081d00c42e80480311040300c0c00e0130000c40c14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 690419019 1250 690417769 690417797
    0x6011b0201030c2706030c0509010c02121c08190908120a06080d0302070b061002060f1003081206030f030f041e0e040f060c0e0109060324080a060b090601 68
    0x3c00807011842c007404208203800048000340c501c1111640008442294400e01e8030fa0050282c407001481c840902106102c3d40e9241d992140c52f900e0b1454048480f003103603100c04001c0d41e00f08107540c1e0024540c54181254070460f507030861095801303100c0840458502a00303000ca001704440aa00d0000d051100800c1032aa004103503844058002407190400150543d41e4440a4504502c940e4494040b0f80c0101d4404280502c1c1800e45601c90025182903101e442c1a900094682c40000c1c214a00426040041100c0d000b050203484080d5a12591290380d80c51b0404c1c5061451400702e814510900c5401104010000080300341d4100720a61f0340e68074106402e11340500d504007510b4410410403140349800086d1391342000d510030300450040302006080c54260410310309580901074114180030401ca0ba0200c1c6903805207502084507584d1400003800303174001140b54100c041c102c010034802413402c580859070b0407000c070340703056802e2103024204070101c1c21209119554404951550119040c040c041e10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 690420269 1250 690419019 690419021
    0xe0601050703110c0a0f0801140c0a0c11030a0c1e240e0310090b010f0602030414042306040e070b031303230301031e0f0809040b130f0506011b020103 66
    0x3000290100ba40d13031240070035000c00c200c1c1445a014400e000350310081040068800e214100341d40240c0c0c0041c24152814000341d80c060311072961104108040b102440d800e1069000a0f1241550001d054900d0101181007001141c407217030040794100131640039001303072004240b44000122510303c401c8403400c10301c807205540004203d009403800e011140d003003419250b03801c0c000240300f0000020f00054560351420882c0d04090141c00002010403004c0080c05403540002c2a2812212b0840981150b58061400300f4098100441d142408100d1052180c00c007042030300c07210388240e500b41c0d81000b202c0c0c40001a6a9940344c64820500402820000f0940c495401c8421041040c064207140110000c000c0b01442d140407001c1c055890040040018810042808880b08884041421004a10300c407070302c424448030903002d0700401c010360010b02c12085884640168918040041481d640510015030013000f81003c0c43c106c0083c540b401002442d01d602507030300945403107001076018031058040e0380150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 690421519 1250 690420269 690420287
    0x61002071419080102030a0c0215060d020f100c03020c0a0f1203032408010605010807050d0509070512100f090f0b09010b1c030207090c0c171b030a090e0601050703 72
    0x650000e80c00c0480e000740c40d840400c801c2c010300d400000165a464004803840c100c610b4020124115084001506a0880c141c1d4030207030025000c48041544103111308c009402c90743d100f0a86a00851510f45450440b504021082c0b1311a002e5001d489480c1550f034100300d0048401d0107034800c0c030444940c080c07110b403e9050340032081a2107800d000840e42c04e9600840c1c809503180c0d9030f401d21105555030901c112070080c0103a800a04d020700740115181000f0310b0240181c01540e280008059694002890703911080101c40c0013800301070000d8002d0784401c8403c0703450f0074241808050550a05c0c1e01b4040724202c905c1542c01d42504081a0807402c0816901d01c1ca003c030b00a00110029900e40030b100b1038960303804070740360000f040c1100c0f40e095006403403030042e0412120394070002120740352040310140540c1056140c88000d5002035441c40343e00740300000c1915400380b007440d40700b002d4a02e03c2000a00f480003000b400412459110f0300e00c80b558802c4040d0300820300700c40307150006000780101400240242100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 690422769 1250 690421519 690421559
    0xc0409111005031b071e200411040b0904060e010801020421030f080403030f18061415060d060305071217030601020d0e030c030d09140607021c050703151406100207 72
    0x120788504007103010045040b49158080e120208540080d00147e01061910f01d858030781503409000c4400c40d0891034085018611426421100000b00b100240d542c980c0010702502290410091558648c100349000350028011210f1200b1704c041c0300e140400e11202d448103211350640c0d9581c94200c82c03c404580980000d00708405042e118a0145800c6455008602082c1e0038646246038115080c2003800540d0140c0d0844a00710120500380045080710607a14a42c04006550700ca940c1d10190b4909001440194800b5220f80200c41000c00e2844022400500c660b010302c4014401005401503400f180c40f06440d0340380940d1000c0a0003c03150301030304481b440060000c068605028600e40845c2c1015280783d041d078000340c0203030b4080c800083d12803c065200c85094680a042151981c00b040d659511101d0480224170000c904000f0400c0410446002c0d503842104806000c0c13941745408058003400c40c1e03a168001403000043d4541c20850800250205c060f0700901c50149454403001500b4510446 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 690424019 1250 690422769 690422783
    0x200304031808010c080f0a050402090103032f0109060b120c010c080c0607030b091b0403151508011b051c050604020d02070c05040b01020601030218090c0409111005031b07 75
    0x203030b4036074284280b980001650b180c0e0400d528000d640d090b182c00c0004c2005184618081c14000941c481021080c15203030302d0304180b80c40007241c0ca0b800381014080f11100e19140554070000f2a6650190402c0207824420441441510540d80c20480c4241c10021040d006500c0110030100030b6128400e481c154900a0b41031514020042070140d04003101200d501c0b02191301ca464000700d6041502034a54004c1c501e200361048100c4036240541144254480030780303080032402107841003044a03031000000c00d0200e45c10744003031551400d42d503010701f05e405900322030b920340c4100012059000b841120303006003d00700550880e00300c440140c8000c0102420080d0015400e00c0f204a148482c0c0c8010a040b6004d150f0a003540d03440d041c00c02080e29031433042c081c11500524010001602c80400840941d40c514006025599070f003011545000480c1a0705640030b070810074141e00744188444d007a520791800b601d01b0a202e07140554282c1d050302c0305031140992442c010509620303111751580580700562042070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 690425269 1250 690424019 690424067
    0x30c12031b030b0109180b0108062202030903131509061b0816060c120f02070b1314071d1303021b0105070c080105180d0207120218040305090420030403 67
    0x41c8080000f1011b008414120b58034815105951f0b00000216440b480464010120710120f0113602100c01030f4106040985401101084c010802481501c0d008080701c01212802075803115115007820001d008440400e10f0b07168081800340c8100c003180540c000030309078106081d007156142c04007944085068080d00c1140300140000580318003071075102d100c9556030b03000e078100c2c0d480180044070411313006003103014410000b040c000f54009035015071000505c0c8441c03040050342e040031408c1320308401070303004180500c8501045c041c040d01e40134185c00000c001a10b80590301c00800c000c5100c118140600035070302c000e941c680e000c0c84080740044040012301d0700504108403070307903a60348145481c1c0012107540d4540302040b12141940382c0445800c4141c400520090503840e1020f912074090b8007420126146500d298400d54a41c0c424401c02e0301030f20403600b1420326080c203000708950082e155140c80f803401c0000200c0719640e4054503429a02c010400245161100c2d50203903441e400300f00d503080724508600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 690426519 1250 690425269 690425279
    0x302030c0f0c01020c041e09020604030b0a020d060e0f0412091a040314030a0c021507021002070302100224060a0308040303030c180b0307030c020316030c12031b030b0109 75
    0x31101001040c0750000a00e0190380c501c00290030b0002c610b03842e80c0528038000b89401914034494031590800408840000c0026140c00841c80920a941020302824040000d1080000060740100310300d180c0c0d00401c0006980310f010200440c4004e5402c103e6070a0b0950204000c070f0b0911480c0003405090f414003840c0681d0700e00120680e4521040f402c510004049810828444409100c004140141003c0d500c0c011090001400340d90a0b01400380c01414036500341810318000310100c5251940007051043d5800d081c100007583d440b4280000c07406080841d000c0342c0581c0c000113149120181c00c00304490304020010341100e0104000740320581c014101c2e05c0010104440c24010400b550003075802041d03000e100320001c2e190103910103042c89040c500c04000c00c8104002400c0da6005625490042100310180380100e10358050003540c2c48224503028040c008141e040400a10aa48990390320719080c0344102e420381c100c42004800030780c3d010500000b000c2d20b80c4240e000700e02c80101410071040560306c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 690427769 1250 690426519 690426523
    0x5061e0f01180f06051e0a080c03100b130501090b0f01091215140c0c1203011a0903070902040801060806091501031214070b06041a0f1c0506040606051206100e040302030c 75
    0x1400142024100c02c0b0040e1b81b41410400403016219101c0103100224000012030703560540c070358100c109155a00241c5045036148420340c5e405182c042010b0001e0350b16148030b0001004121900303072107544400c100d00784035406102c80e6407c540e259450108a4002d5442c2d070000140b040041c00c0c2c000380e46409000c0e2500313a41404034010f0710b00a03189601c82c0e0b000422645484d13441080302e41506024001003003403400444506640700450805292180c0000d00840d2030308080e5001801d020b8000b0a0100c0c0c8001e05604c050125100c0200300e40054440d480000e0f1148181c805404844400c0c1d0018030200e100300040c070420310305514064500250340340440c000c641226608980c9582e00b85c7c00d0003540e01d0705000b0b00d0300800b1461610340728400c0c0c0c540000c0b906040741107924010222035842403500403011b040030320040d810100b80c036000c0c81d16146c0b6100501140c06414403030084908a0280801e0028072244540c01242c6648440d604103140843d109200800c22021480104240c03041e400c41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 690429019 1250 690427769 690427789
    0x2031b03130e0610030b030613050f1e01060501030b0f060c0708030708070b060102030a091a09060c03220b030408070809030a05060105090106050c0606061605061e0f01180f0605 78
    0xe4015840b803904000040184401c1c281c1d030100c00305070030504080c00654010802d04e41020405032091039811251070300c00d0425410240f00d80260080d943c1440c03136900c0c80c1601d004082d0580008112003078640c00150125600e50703559941110078040000e0f40c0d81800360080c4510000310045a03e215500d0480310f04c1d40c0d00c2050110340c00c06021801c401004000640304c0e030880004d001071410310f1070b80e030401048140a03125600d5040380c410a041d901008a60485000d1040603050030360f80d100c605542a6641d218150504921a04060110b070740351210500109a0782c1e420102c40c5152580c0d1500328032904100c0007a10303824820014036005640801801940c44d00c1140070301450341c5007204101b602c1074142d0084007441401c102070006a030303000c00e52950102c02100d5807a115a40c0003108110300031000e000415520410b0217000207043d032002d85d080b51400049520030f0340c1d610b000040c41e804c01c080c401d544e0380c250340b140c15031005507040c0c1111101d4400701c0c5001480568500001e862601 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 690430269 1250 690429019 690429029
    0x40506030c0d0b041b200f0604050d0201020301150e03010b040905010b01081803160807051f0506010f0903020906041b0e01020c06040509010501120e030d0e010b1002031b0313 77
    0x40005200c2e00d42070110300404240e1102101c0c104412414030390303505030445214624004201e5412030703e074100204076101210200c0500102c5181c1000940c00943c1c0b07020907030b002c1c0e51034801e11070380f8050240b0500880b816241c20040a10844000500984200c1c1031610201d905540b55010600c80307071200d200c1d02640310b004100108000c04102c0024001a002a10041041070400d43c2c41031069030003c1190390060548040c00007031005418811001e0041c00e00051642c000c180b1400c0300003402e583c00e240001c8160302c3c10011520b42200550f8504552401040072404006042016141c9240041d034403100260001c40c00d80031a034586510462400c013900c0c04a03880d0900d1044a5038100810f074000f010a41c2d100e8542070500e4000307000240144034042c104448400c101e040c0418030780240c0005481c1c9c5084075250300601e001c1f01e0140c0000c0004200661903d8090b40c804d140c401291590920290080c40c40c2c8024005000a00200e1206140541c481004110042e1a10707100c2c40000381 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 690431519 1250 690430269 690430291
    0x8091005090f04060b0f0f040b0a050309070f0e04150e010f0e071d0a0c110d02010501031a0411061b070f0527010e06040b10110105010603060e040f0804050603 70
    0x341c14010045496980b0260303034002c81c50090144800102801204c080c428041c0c0c031076444210001c1c8524186c0b18680040140c010085803240c03113142c015002e14041c840101c15200541d485008101081c441ba10400801d0f00140d40803902041803510041944030081c1c10110b9455210308019007510301495035030580c285c0e2501c00c0c80081400303200311409011261a84a0701c152026000740c805c0c540035100c02407040d0b80e0090901c2c11405034010004040c40034040d0780001c1c41c2c48101a00a086c00d2200355036100b0046c0b10603840c50f200707900d078078400d942c40903e8552500b40314080c007202c3d802078000341141c0d02c070018841412080c2001080c0c014002e1101f1080744504150502208010005481e203450181d80301c0c3c0c02c444064444401d05507150140104001d550304000500030b40b9400c0c071f078650405290001480101d82c00303240c3d114601030a02c001d114590b03a0703200807000c83d89540708203000d0a1800e00460000381580c3c0081165030f0050043c40d00f06510780c00000e040d41d0040d41d54103400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 690432769 1250 690431519 690431527
    0x22030f0f0201020c0a060b010327031704020d0b0405031303060203010512010903050a0c02010e040c0201090b06030c0a1809140a0c120807020d060608030c0c04060f0305030a0c08091005 81
    0x45900c510502000800d5100a509251031401c1c4a6505c1c1d00308000200420b40344c00006001d640f09920079983c044070209500f0901007080c0c1c10b9a0708841803503060780058000003030508000710b0191242d0160380c2c0900480c2c40d000c2c16803240c0d401c058016100300c0700c9002c1040501105c2d4085d42c410310103035000340c5006a0704e5142c00c04016a900a480c4600c0b40b9904010760345000c00d4020090780e1000141e8144800d0b0417644d880122440c06d003130034440d50b019203442c1d600d400c1280e05501264140f44144da01c8a85c2e62509003c0560303a00c1d02c0c28400d40d209044040a1000003115141030101206403075000c035146605075280e4200356200172034412540d210408500c10321940c100e400d001001040d030b5aa0b407160140c0c40e11401c511890a029006211510000782003004a9100b20000c2c44002d0030b59488150700c1c030400c1d465a078008101c41c0b040341003580214541d900500028100d80e4000300543c9000e164500079690103da0440540f9601800c0c8010324190315030894184010400303584a680d9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 690434019 1250 690432769 690432797
    0x615021506030c032d1b030118080d0f0212070206040515040510180501150915050d30020303040b1f2601020715060506030f0f2203 58
    0xc820001c061038400c1d803102080160b07a40b07020401d4104110102e0406042c030a804880341c40c981070090f615041440707a100340b40c101c903045140c03001440400701e0081c040c1d0401e00c2c2d00d0303440f100c003070401c0500710300b0042101c8294238160303511507071003210004009401c00d01d6141c0500040c0a00311034610150300814104000c1050601c84c1144040420070907000c2400c0c5516150b03501c1781040300555600d56203c004c06c080902c104550500264888024060b0f0402a08c1032991b0840301d1040b64041070514401e02503001c150310b10002034801c0640180902c0040c0e07203612500108020104401120755403481100045003d035500aa640035001142e03a81001d24028414080081c8a9014035101100068041504002a10880f401d85070303800e00031203040b2078200c84070707041c1d040720344917980f00007030300d00400981c0050007040e10702c8580200640f40d0340c1c2c8244801c4c0d100440d000311007a00c4040c005104030741e050000d15085101c40b1854410502e15000e26240d4241d84c80c010340c00f08200c640c0200b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 690435269 1250 690434019 690434053
    0x30204060b04080d0513061d0d110f030a03080402040906110a031406040b010e01080c13090518010608191502040909050601050f060d0905120f1b0313030f0501061502 73
    0x40859107407151030400c0104607241020503a0168408006120300c031049048140d0366236110903c00204100c0d400c042d1072038050b622180e0400340c0c90185074460b1107016075190204124401d00d41641312005595140d82c00c200c001c02d03880c0c5c001c84010b640d4001d02007132040d1600c06490070003c7d5840004482c40200405c0d003030709900400107807141342803005480d003690b4041c1031102d4080080c00d0034142910b8450b822409070250390b0003201c3c0c03480e4040700051980000e4006a0080044051900038080134281c000d090385c40a0003641140e078850030021440e1960541251306607409100c52502c0d041f4040b4890081e607002d42e0107140f40c152580070041c180071081c0849801010221800c5172000840000b1550b24081c410746488165550909903060000900520004240c100d49096840da500724883d051a04182c00f02c0342c0010f41c10701500e22001000045490a481000303802a4403440c40c4d0795020b83ca11a007a044496540f11030001401ea0004c0110140c014640c2e00a00f41200c242d400f804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 690436519 1250 690435269 690435283
    0x301080705040204180c0c080a0201150f0b0f0a090803030a0902010336030e0d0b09210702060c0102090d08030108011119350a05010803070c090f06030204060b0408 72
    0x1602c2203104000402c41c4110a031246202181c00c0d040c040f03101d041940b015070344c3e1b81d040040a071803a80000390355404982d065104c4c949201c20104035010650300c030040460b8070003140c050140c5001c8200400c5185000e0b40010f4442c80d20755141c6147c14640f18112241190015640148a2070712940800115a01401841001c2d80d40c00c220510015200c4142000300000303032403c030300c1403070044100e009151051003072503680c4c0b0014188085801c0e0713505d40740328104011212144180560760411040107050f0a0301d000c980f80c090402400d1511a408100b40d03680551b40d0070315159400c01081c0026201c0c2c1450900480c05480e41c941c4030361410760700c282034070b10300c900144104038100100d0b0039125090506031450f07160342c80c250340b001c1402e15032841e0402a00100948d1179400980c10705191606010346441002111428004c990761140d18075030324051400c00070040c41401006111040c03c9500588019903924400305410b9540d4011904851294219040c1c840c000102400303c641c04100413 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 690437769 1250 690436519 690436529
    0xf0b0f13020312030a140c0c010b030a03021507030603051c030b0f0603010b03040611160c0501030c020a0f06060918020a15080a1109120f060f01050d11032103010807 73
    0x406400403580043d0701ea803144452405142d401002040040106610416002c1d504c600d50b8070460030a08802882a04501c000c120036608002110100f070030041002e814084d41500180b228041d48080082502c9005102104255445e200000428800c10070500c403022541070100780b8500c600002002c2d5994801c4080c05600c00300d2400e4540e45640d000c80303044079003811b44541c44e41c03254a8008087c00300210100c44025000c00c1a04468000e0404030070814451505204950340d55130054059400c180c8000c0e01503000100d08a01013140d00c0c28005900d03200340f00006449883e0a4024202d40e8102d4208403c513107002c1046d421400c0048025026150401e60b450801080c0c290003484104001c10f8200410f450361884010341410509550025600600900755102655081a030341d0b49880800c0d4003900c503940c085500c80d0042c22049060b680c014003c5c1d120740304113407618041111080b201c41c1d05840341c4005020641d8040311164070032000c801c8800d5070ba526161070240b44c0040b641007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 690439019 1250 690437769 690437791
    0x70f0311071d09160f14100503040204051806010b0c12090a03080f040302040f0f1a01082e12030221250204090501050a180812060a030f0b0f 62
    0x2484202120030300a600040c0c204120a510b65031403070454207240d02025818000a0040d10208440c51794001030b00540f41142202d0400040c28020004400b1500d5001c00121b01c0820204000d0b01b80b58109561107620b003800320340320344114030103a490310100360301c0115071003c04146149440000e0102da0365051409c0e0a040c00d011840c00040c40003140c40c88000c00d0620005542070421a00c0da069400950700140104101c04489a00300d000d0403040355000001031500600c2110302c600803000c02c40c080810b83d10010b00303540b241c0241003c0100071403294800f460310001100c04200540d51200604540307081182098042e02d4064607050010711410410304040e26503901948942d005d0301d403c40c2d40102c08c3c00d100701c046081d01010040c4d80c000a5005414000c0d604144481500098007030408441700f00325940300040f5442240001c4040105001d20070400c940408015490407600110005c00058405913655205d200060001400b19030111400c2c00b0843d0700078281e070140d544010f000031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 690440269 1250 690439019 690439033
    0x60b040605090d2f0f211212100509100911091e03010e0d0f05130503031602030712030e0d1406071805090112060e01060506070609050c0604150503060d08070f0311 72
    0x2c00100b229105980e41401e903440c01e10040c10461b420071500134101200442240d88020507400c0aa109104403041c4c1004450074500040e00c0c208200c502c0d1040c1c010b22280740e50350f030a140e1220040c00c0c0700300480e41014014485614203941c0c030341c0304007a285074140301c119040da007800c02c1c5800c1d100c501d4103480c15a04640c03440c060858001c07070041c03224203240ca0f000340d13103400c6d0030001c3c8503070384042e000150140300109200748998411032002005a008130308943c203032507603044411000c3e800d22400070f0010b0100c207503030041800c1500c001f44600f885980000c0b0848002030840340303000000c99200000828581d107545014001400b100b000e06400c3c0c403c40c1b090b6052400f44481e040d402103006010701d0303540d603040d6400b00007036000e40c3c0039000c000d003165034a003114100b000c003802d81d2010035680340c045c0d480410090320705401100d00311115006580c45000d041ca034250b031903030001081c86407c0900c55010034005403100008154039441a44803000e103080e01e050040802c04000742c89591648a09 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 690441519 1250 690440269 690440299
    0xa3506010b07030315060818030a0203090f0310090b100905060919061703180a1422020f1b06041e050c04090c0513060b040605090d2f 59
    0x45826030566020070103599944007186800c50003081d503d480e00b4103025074540c0102c0c0d41c1d64418162406064100c1491307200710100c003021501c9118100201016074810050a001420980c04009080c14020b041d112503039088800d6105685030702d00308882001ca00d404201100440c25207443c0a4818140204058682180400c00542010b0030a042c111040e01620300b449540742c02084c058144403444000c84444018907555941110903049541109000060403070308050316183d04440d44444440c0c18440c00c4018001c051001c034061641084a64034000a4061540020060f810311503035001d66a100d401903201040c02044458006900074000348408a29609005010a400b06100483c001c0c85450000c2c508003081c130402d50800d041c081c0c40320a101c3c170090342504851044c0d500e01502600d01c1d91403800c880081c001e20307180090138402401040d2169014101840c0c0141c004003500c81140c540444500010030300310b440d4010000c41c0c0354a00c8007000340c00050b402c1a5182d1800c1d968030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 690442769 1250 690441519 690441523
    0x41e05060a111603053f180f070303120911060315120705040c05032a071b0f05060702060d0c0c0f06062c060d0206090a35 54
    0xe01455010350300d0b141ea0302c8080720200100c48118800c1c50703442054a40600e0081c107160008960400c0356225103103041c445203e01c000642c81d808550340781c010001d500301070350682e00c100649446042c551614844c401008108062040d08001c8401401d031546140b42c0104640c080d00e0640d00382c1414020f40c1030000300c2040c0e2842200340d0032204582c6070350304c070405a01c06030042024507600080584d10200002c002007140b005480b400d4609215812441d0015581c0c0d11003940c405030204a010300b19a901031000c841c406103804454405450b0581c161900d59100c6c4a622403c0219140c2c84400c04c040c2c014184180c0080001740c0d055400c0812507000158030307008400c4c00300340441c0c90721f0506040e640310b9070f0511411b592004903000246820305000b0010300403805125006004071311081008a0f00044078001c3c20700340f41e80000990307070700001c2c800e0014070341500301c1c2c12200900501e0031039611401c04c50054a42c181c042e1aa1a03480c001c4400c036640c0d4000700001c684648003800b0010240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 690444019 1250 690442769 690442771
    0x30403060f110d0b011e09091107020108151507081201090e03040e040c03061107060e0c09130201020c0a08010b0913080901051804050705070201080601020106061d041b08041e0506 79
    0x182020015240101c4130040c1c0303440b02c2d0b9450408040786800001d030121504480c1c0c000c10340e040010704202c800c8007032005c1e40f6244900003001c0e010580a07030000b5680380c00039590760340110000d040400c0d2040800103420f059000040111070310380c00400c050001c20150072200703005120200060140d41c03020314016449106500514003030211010018050204400d41300e0011f40d400141006044280c1003145107640010104907240d5040c841ca85c01c2c4041d002a241541441c0280100010346030800400030905070f10310f0882c11340c09150b07a4041c1a60301c0804910041620000110303004c154001005085840184036650711110140c050300414148416039000f940e081c24559500c0b240c0c40385220038441c41549150340241444100b110300f96012000e0318296200303880c0c407542526184016401d9528900540f80050b1410401102c03072405400c05d07c0c91001d001e08005024011081c9030358080540b4092840450040f106120070070911803004032091a503100034008218080d81c0f21916010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 690445269 1250 690444019 690444037
    0x1d0715050a090509090309090a090312020c0a0516080106060c0507030b10080d2102160602090427031808060c0a050d020703080402040f0e033108030403060f11 70
    0x40800c0e149081e901802922000d0900145141d504c1d00e00280204ea07240d00c03054805000319507a80101daa070403450b010311455658141c071014006d05100e0a400b0094100e02050700c6944100540d041c0412001c5c0400f1a032201410200d040746410b1065031400c1d5107050313200004000740c2d6102c01d0007054004c103400c401da079404500b04000c0e4072030000008801c0c43c20741102d0960f01034201560802a0082101d0101101e40c006207195078103000c0782c140c01c900802900100c49401e2158900000741168000c0148100050000614290302000104c500b11806c16034100503001025250500d40c1021041601e042400f1034254464200140c517511914080e2800d00c180001089100c41d00740614190f409000180c102151101c0e003c0c24014480341d82a101070740a6807038214031400c5000c05000711445400f104e80251318280e80400120f0303580d80503240340f06c0d52000c0002502c00314610040304400604030070b4020741d00c0d242141452401c40d01c4c4a20001015803034840b03000861a000400d03180c04034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 690446519 1250 690445269 690445277
    0x501080106060e030a0605090c09070305071701050117060316090b12010c0f0c020102030d020705010f0c0212071e050610031104051326190207050d030905090a0204030b0a1d0715 78
    0x1031610b824049ca4171044012182d030003400f800130405007560540c0524400c0c0344607525413001c1a00c0c50a01c084010742805418001249240c080c4550203040d10425040078000d800c540d00c68000003030012000003241c02507620035803a09680c0c542441c0000c0c0c05092461800700070803413052070ad400500a0780410841c50b0030301c8242040c5c84190381c003e0040c0c43c0248620f000566580d03070741e4a800d500800300309a10050451070b012020031124400280201640091040c04d441d04144da2165540035404400d140301c1e251250f48500c00140083c441240035465114a0825680c19498007500c0d013a0803c000742e00440c80c180803c0300c4464071841e008442a0042c4010b13000b00015040e5248030707000d20380078110840d0700080c503d150242003003810040f403200d60b09540d0100c2d280c50811400004522002d0000341541d9014440362030151032494118020764001840c255aa07910610100012142c040f106556045008410410781030750248220300280901420307820300840010180b82070543e90100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 690447769 1250 690446519 690446521
    0x60801210212030f030f0f07020a03050409020c07150c0308010b12060411090d031d03030c0303010504180b090c04050121060c200a23070b070807150501080106060e030a0605 76
    0x851400c0c004c8585010f02e00110070307070f00e1800104405011000780c0d800d24158002d040010522440070907103c070000d42c10750f501c526041c0762002d0f100194208203442851401581000a003003089505900f5150030030380c07a1040d440c81a03007009024208142d200501c4410100804c80c150800c600341c082e44004220340010f00700d80c7c6101840c070103007e00d490041e0484442c03401d075010f140e0010406100c440d0100c448a01c03400450090649074001d009403038800758000e00050015180640203816041a080c0394102c0c07098035a140c40c280b0724426036400c00035801449151400e42803074000d650150150f00000c030360002084104081c14404c0c5080135201d65550300942280c0c510a202002050704400b130300c01d4510380001c56803500c424061504503a83d4048003510440c8617100d140d201e40e42e40340360018100ca14509401d2f19825400080f0840e9400b2003045510300142201c94640c105500366100020590f052419541c2105d001c1e81120090041030354504030075583c000f40403403209070700000204e25 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 690449019 1250 690447769 690447799
    0x3040509070909020304050c0901120206190c02060703030b09150d0609030e04090809270705030714030112051b060715060b070503030403170f0705071502130608012102 74
    0x140a0f0448a8010f000000317000621000180302c0c05241401c40d0b0000199a1b5800040e0002340f80b808003c6d080f0b10140a01e00c101d00d410b07030144008141c503041c24241c06580c0e07400640c6a92250008a011950b150188161400c01d4280f0a521440c244d42030061100407800080ba40413641400030185030321800400708040c400d608042018802520600a688141c68504980c0c4c00240038070f4000c2c0c0102840b25007001000c400c2e1140c0810500d0700341d04a0304c1e407401c121069440100b00074203108540342c0c2e0328070020890000b14000c1c030165408006113403552405509005c1e003c680221840c1c0c0c003003021b80c1241d882d0012540d216a2101448010b009400d045801500ca540e100b00154040400c44401748880840214400c602c41e960b031905101c00ca4901001191058172041c84200c104000180b5050140008005490144407020036045501d200d4005070781c4141000c0e00c403211454000c00007079820100b0309016180640d003030313500c0091600130b43c010f070300300c0c220060300c01d01e060040212 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 690450269 1250 690449019 690449027
    0x503160c081b060a05010f06080a0b090103030e030607021617010f020301030b18061005010305190e071508092d0a0326090c0f030c12070e0c0a020304050907 69
    0x450a98441c49240d12040881c46003080c0b40c12000407030300d60340200c4000031010401441014144c07a114518005030600748101100e4000005004038003865503240071000c2591030400041c02580f10340e607150401ca032030500741810304c640540b2200656001690309600c034540d0300d2120701901c80d00c003031003071032203c100702000d000d014802c00c4509010310000006c000e203c505d400c51481a4030318091481c40317101454005641e440c00315100005200c0074041440a5031080c0c100c4c40d045454941449070094001441c0760440e420305a2450381e0f50b01440040140301001e4903255000086402d00c01307042d01c1c0503000d080d1030304805014802c5031150200c00d080c007100d1008103403690303a51603012a8201d4646250241009503190148000f800d040070300710b504a007170011024480c1800c03101411040080d0018802440400c60400d075050040302c400da42a0b484800744038024482c284000c0c540d031031510018022454029102c0f07103c0e81c1013000442d10641e00041100d0480b402926440c800d980d40b03000490f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 690451519 1250 690450269 690450287
    0xb040b2119050d030506030d0e1005040518150307081e1c020115150c020d050f030a0201090c0618030f24020a1416110f03031201030501060510050316 66
    0x541d15250400c803441400310004103502c00d07010302d0b00e0800054440e0b0080650750802c200c01ca10024005903040e02d218180410600301c95420340c00d1007410552104c001500100140804080301a100d0b000c001c0351020b801c5044d05240001d501400d100e50a01e00c809446401d001008041c0004803070110084100400281d182d50720020030b4040201c0700c0d004001e0103003000d101419580038510101103081c00100e2510b0641d10060f886104000c00b8a5080c0003031068001016541400f85071011110460180300404d8040450703400042d51401d1880c01b0801000ba81c0c0100040003031840000f44002c85c0340840c00c00ba20b07000074202005210b9850b20042c004100360b10314084c041301d600e400f501210203802038264041341e600c5e00011003000d401049440d001d10780800801030983e00f21100811082907000e00100c402038440506042d0240203c1d242d94030208c2500403802c075440c010030a0100c2072154402a100403560001403030a0848000c15500025101c4032241c14959400680180901030700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 690452769 1250 690451519 690451543
    0xd090809060705070f0503150f06030f06010603061d07020303070c1b0b0d1416030e010f0c090e0109020c0d050d150303080711030903070b070201171302040b040b21 72
    0x825694241860a140c072800780e44a40144150031200c045507d1070085905403001450b4003c85200c0e9803800902d035110240902074541500981e52228800d6405010050282c501620089403003880d00040d840881a10000d0140008140c404e000c10035a0210072217401003190314003009980250b007000c9544903585030440840d01c800340c00004542c035101019100c00d01010004021040300c000050061510441da110021961002c2b0404074034000d130310164560305080000030f1f030a10b40060740001c90341c000b807a1002083c0c022004101141d01c50007042c1c05040000415800c0400ba0803032582d82e0381d1404240340505c000800c28000210700d5501252034400c0c005e88801c00e50f0303603a003070260a00300150350600004140c1459460074482c004105c07241d69001400400d0302c030f450455124919001401d04030b0420401448414420549100040c01134160140d03100181c1550720401c000c89954001180c025410868404811f40c1c94600081050855a140f040c003541c2c80d41c2c50380d08154000800d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 690454019 1250 690452769 690452779
    0x1b080d11030a05071419151a090903042303010b030f030409021b19030305010f06080115020c030307030f0e0f1305060103061d01030203070b04081b0630100b0d090809 73
    0x420705500c181b04154000340e000350706140c29800004079100c191140302600040e2001000484011410003189650313200da40700d810380303041030344a08403000030141500740f1400c500d1405040e10503070b03c2c0c284180000301030304400500840c00d2441106441e40030b1441481c15565000c47c10680580e00c1584416208842d40107032001c01440c00c1c031000090071001c41c06d5000178600800492543c4c0c00e0101d50060341c40c241c480785100e071719001101c803085d0f9000c3c0010045005640388400b05890400240070003030b10a442d26841c1515640c8020003e20003508a90b2141000c10300b040003640391b803a038031500d036103a0101c00b042d181d4070940180c2c0988082e81c0031111001e85940034401440d521030b905c9040e44d01c210291000303d030f030710014488640110f00548030031b50041d40d02211907101c03ca102850304000034041600388040000122050a5450f00034203451480c920301200031440e407842264040c00c10824140b007035040c401c0902007070284e101c001e0701d055030b11105e0100340654078065802030540182 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 690455269 1250 690454019 690454033
    0x1020a081f030f050d0e0a0501020c0411070639210e0318040b04090203120a091d01090e01060807140a0302040f1e0905030a08070c1b080d11030a050714 67
    0x2500d1175841007401c459900080f402940100981f4084500301c0460304141e00800c0002c140000708001400c040c4001c10442900308900f40000380b01d8081c080d0482294101010112214015002e00c0300402c45c0d400480814000c14860321a00246132600d000d004001e2019401006005c0d1401000341c40700b9445984801701d00b0341102d034400e10054030494015138081c09007001801c14001070700c0382410001e600d600903c48a45200c0b52030720140910880030720300b1080341c56a80301d00888940132038500e03940d00c40c1900014456040c041c0560f2051440c540020090b2030300d444003850300e481e400d00420002d896801d000032071595820107204091900284100041344000700d01200801c424100d00c60000d91509101c646c228403842440c8403203070400f000c4d40c640b01d5145011984000c004200c2c1f020300a01c01c080102150000d403e52141c0080a5024442141401085840d106911682c0810400180100780c009900403065400c980300c03034100f1544400300382c54188030410150349030300c1961007004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 690456519 1250 690455269 690455273
    0x10605030c12270601080a030c0f0822080a030905061c050c09032104031112030c0c0405011e1406040b0c03031014090708070315091a0301020a081f030f 67
    0x21080b100f1250141c02d0008444501c90009449590912501080e07400101401d40480d0089102140907403040c0500070280056903107000c10f6400101642c040d20444c21a8112102c1500600b80c2c040c010000040c800011070b55030041584e14280286c0e80210004220400c040b070304146241d00d0041000000c1c0300d107141280e0740095540001c4411442441a81c4004900d4449255840710b2240103812192802d410f40c6c4a1104030308030340c80565001103150740c54a002d030742d042c000317010026413141c050310800300701c107041100f13484045e0850b40c10420007480c440c0448070003004001c11125842c0e5919a13003030760407001403481d00a40e84101d541820005e0840c00d20080032000714450414800310841223030f15034044092040a50915903002040c11003c581907034040e0034003039440455841c2c003154000541c0c003c10304002c0c055004c4400b0a440705120713600d1070204440e0402061050340210704080f0442e80042c000c00300900310a0446d03603110030740f042901030441050b01460b00a410740d00045240c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 690457769 1250 690456519 690456541
    0x110c0a0303020c180705030403050f120a050f06010e03151b0307050a030e0102040b09012f01020c0c060304020f2b08040e0907050109140406181e14010605030c12 71
    0xb0b1200707600c07940c0c55030101c4c0000c1d5124040c40d40100e000d640e445040d691b6076601030360355910181c8041c001c0300081c031510101c2c00d6000704151041290240104036820090401805c110015003098180486400b943d242a00d0008401040c441685100c0c09a922890910340303089400d42203203090740b5000800c2003000b54002d002803203800d0542d0390402c200030400c503143d03080380038178040d40c11001800c019018940d032007610883c40c980b140c42c00098031482080303a007003200483c0c40500c010694011444041d00c0c1b000b17012100c50100300340d40340c0785586440da001914140a010045100304000401c40c0b8020180039620b882c041d22110b00302c4000183c6051901f5190003070310034400030028100000d1823111001c5071044c200e90041c1c6490b80801d04107802c0c000a203008441d83c079007283c1c1d00d9100094030550710405c504c1e4900000c0000410460300c0b080c5002e2908000010750400381007040c0d40218035120041c0904646241c03a0054803526203840440c201c0c4902e49803462814640014440304043c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 690459019 1250 690457769 690457783
    0x2100e191b1202100305040f020d1b0305010b0f03160e0c070b040818061c020922060312110c0f040b060c1b030109031b08090d11090606030610110c0a030302 69
    0x1311128210b080880504074156501150f00805a00040113540f0041c1005080f005402d0300c200186900c411626240e00d41003d2580d07c1070f1140e07919032a8400301410611901e84240c2020303005805031585840c0c01032096462403095040800703c040003d910314000b50160307031046a101c01e01141605150074482d441b6044400e5210384140172640006c4a49000c01c101ca1040180f07030b0841e10000b221030701d104004d4001c0489150010381705203a0034443d03030a0352401000180340000c0000c0e00e50660500035041407650110300309001104013401c032100c400084111000004940a683e00c0c0d5003013021501402d84081c0c840d4001102107900c3d00801c00108000c6480801a25142e220031003000405098900d540005000f0a10900c0094842c4500c0c0580102c141e01400080f460520b03000081a00060041425200c1d56207041e00056280fa10300040707900301100720307035003410343c28203000142c201d0700ca803500f00e0705000c4808202d10840600b40058056100d00800c25080c10341d40e0b043c00703511140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 690460269 1250 690459019 690459023
    0x1030203010510031e110d1a06040510030615090204080a020907020c0d1103030f0f030106080105041514010e1c020f040504030e2809060602100e191b12 67
    0x402c1500040da00318441010100300c0f90408042921070180c0e040d00d00c45807a0849050303440e200c600c1800f030507d40b02d2071040b00d072441c400c5980003810b05c2210010040c90300090103442c42181811300384a02d055154540c0030907250001c0000400c0640c000301c01c0008c80135940301c2c450003400410700083c0d0100c00300e12111420b0080d035140030107540d10391040b61100c100c05001c42e03003ea130010001000c0b4800002031303400c83c2030240442e454800c20390704201564121840c405042c0e140040180810f5a0250f41c441c010b0105490920840907240f5003000d08100e81d0107860b45d000124152843e07a41e02c500641103041c6000f5190b08000c4510f0001d0500700f042442d03007a8000d0717907001070000c890704080c820103200301c1d0148e54646079030400c0b0081040c28100e20072000007904400034240c9004000d0304448004019072080025041d16000c0302a080007444403003440882c2c070345072103100e200740045010a070300d440f940203208a00c041844d200c0d03015910510311140ca58511a008130303030120b19900c02a03a880c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 690461519 1250 690460269 690460271
    0x121215090e06010e01090c052208120a0f050a0c150b0f0f09010b1c060e01050111160b031b0d0b0f1215040201030212040f061a090c090a0308040b030103020301 70
    0x20704241c8005580780c6013031107030600b000304001c010000e003810790348a0042d003080c500c2e03e075280000440c48044044607510140b500211104c808200c5d0030000c11080e542080c25043c041d040c07032008007005c7c112039801c44c030b0300d8140803000920565075072003040c00410a17a803090300c400c4d5461000d8002d50007018541c0105000d46101c0c07100c0e603034502e0000c608001401c0010401c0c0d509070b00b0320303000000c15044540001e000d0306084154a0403c0381a000781c101034450454015020b61400c400185580d4059510564a0f0040425200100203042820301503902184480750759484407030303120038404105400000941c00100c1c0d00862a0761680060005550071141c100340010303440e00300180510064081c0c1ca10387d00c030710401804c0300c1d14400815400ad0050600600b01600101410103d0307204440844652070b00c552060200302c1640b00b80f12040c0700c081180310400101c400850240780028080a458000120b61a092543c0b040e000002850380010181d48403903444c890108250000e0000f24469 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 690462769 1250 690461519 690461531
    0x3090b04050115060216121a01120203010b01080405060402040c21060503010e0d050d050709050405090a03080c0a0e010e132901020a030509040e1219110609030712121509 75
    0x541c40051200143c8400d40c40300c0707039030718900b60200f45200000b0030220b4054096035407075a03407030048c401054001c0800c00e81c513060500310751041508440e9110b0006041c8501e00080c0320108000041c2140d225030f0694000483c150003150a540c1801c084052071100d42584544214420302c0c2d401003401c4038419002030207000b4960414640f111401e03810b4100189080c0070300f20261060b60001070700460319090030740d08540c82d000898103a84040710741c1c0740f00da0312100c01402010743c0a00302d203a01c0102c0300e521a00741045550010a005150a03500b070401401c503600c808180d0701d50032242028034000302d081100011a03260301403e404500d040c8000c0094054041e02a540003061814181d545640d40c58540038020007008010060501c00380130074461001d07288002403039140244001c08151401040d200d014500061000c100603020414640000f0144190307880f000064a0013998400081321106d940e03200201d61081848151201042c05c0c4140c070210110071115020586124090034032403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 690464019 1250 690462769 690462779
    0xa1d060a0b031219050d0f0207111003053d0f030b090d090b220b0d0b030106030803040b060303131d01090b1315050405010b040e13120e0103090b04050115 68
    0xd24040c4c200c02015000040480c0d60034940f0a070010990081071000003e0038031404d00010341241c0040404681d45c00440c58546668903000070a030600c0420b910b0184a0751078103410650301c2c1c0801c1d02c803600030b841d03040c0c112000210131801000d000101c401c012044180d80c401550801c0b81c110b21041c5c41d96404c4030f001c5a50302c50041050380207210703503441d0070302e521740790000c8040f031544400402e11031100c0548110ae2180c41a590000080a06c0300606844400c440c072507404550405a2044c072031b0b07241000400000e500712080d079600641013801e4060710360712480820f065101d0391404140e0b2111500380490b071407010044070f4800703161551004006a880705c0b0358108460400c0300c070503485008e4401810b452800e0703400903180ca1841c0740400e42c10b1543c45c0041000d4034020703000088180d0022809100f03408080c42603607440b40c010600b94010005076107c043c016100b59014400300410005020003590090b0016214903900030780f4120940380508156000341000b2901c4102414846800a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 690465269 1250 690464019 690464053
    0x908160c060f1e0e10120f0e0c2808070602161d0402010201150920090d200d0f02090601140a0503090f0307050a0311060f0a1d060a0b03 60
    0x1198400d40c03102c2e42000e00c91104552a00d4481403241c040100214401380c45890310920002c0103030b050744800e42d03442c4044500d54140c3e0b801e9007191200514000907501e811344001040c11040505651000300d0280420142012107400d009a03000092030386000a070030f01d00028003204503103040e420b44900081404451308800703107604c0b40c1c0c482c2c400707200e0228040d5241c00f5101904644140000180030074400d01103002211681e00c40c29084d5941e113501080001e81041c0c02c608c00b0200320220749043e88800004400800003c0c004d0103a000000c212518000b80031040d00f40c0700802069404a002c1506d0981100034104001701e0080c000e02e070100b107042d4000e111100e1503a030b22402550402e010100e04a50b513400040c000916881032044030a6500e0f000c0c001001c085005801a081400143c2006020710110b640810100e42c01001000045034801e80d03280c0d0440d180c001d000c2507660345150510790291320030245003218018201070150204031a403010107803140640988000031000300c0c03028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 690466519 1250 690465269 690465287
    0x709050c030402010503090c122503051903020709050a02030a1503082203230f03040b040512030d05010e0916030f03081f0306060f080d120209040908160c06 69
    0x140c00100c0c01d00201e00158061800f65a1000d064030880d020074821100003002d883c54100e240c1e0b5150040e5081c0900300100e00140030030031400b81801c25110340380d07a444541c0c9002c88803081403070f604907400243c1054424001c810040816520911441c1810114a4001c0d40103072003459a0707030700d8108a05a440d03080b816150860703030000b04c1182030074a104a044400c042011880c403c4010344a4040000782000740c1081402e00c003004400c1c0782c040d25010711484d150750030001d071046034020f0000300304160348501110b050742c400f41c8422112100d0661005d10314041c16041108070790802e0b0020504180044019110b004400b0440b090310040d02e918404031015070102802e00100d086410000c81d001c0e840b4140c114072071041d10f1140b020101240310740e0500c1e641048618030307101e45041080c8503052180502802c80c001c050b11400443c2c4402034000200c0d175210040003034010402c0544c9690742e6104244403508030303d03a19983c04200303108150100c0b1022040310884480c0354041440c0d0311031400a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 690467625 1106 690466519 690466531
    0x411040b0a2904030b0105010c02120f0d0905041509050c04080d030e060a050115030f181a070212040905130f03030b0a05030f0d3e070905 61
    0x2c0c003400d540c0a42ca001c41c1d94081c0014000701d1862403505044500074200446840c40a10119240711021094103949014400010388400008107610700c000c011a9070b06041c2644500c00c100860301114001c0d00d90030081c1d5402d028038a03842e03100680040483d1489801c1c90354400c055481e1240021001c80040c0e00c031001c0c483c1803402000140e41100e00c1d010140065814000e03544480c0300020421010980c59031f908001c109203640c030400a21254025513401c0c08002d081038041c0703c6003800508814504040040c40c528404182e84051105045d0520b00d041d20b0a41080c01628018000c203000b02d030503041c49c0c800900140c804002141c842d0300c010900e88a000304000c40310840364000c5000340c1000b00000a003030004100000b20200c241495001041818625000c08103840d5000c5907101031100d04402a41c0105080a03005038a030046441d2542c40740c0680003950b20590305 = true := by decide +kernel

theorem cover : BRFrame.Cov 690287769 690467625 := by
  have h0 := BRFrame.cov_init 690287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 690287769 ≤ n) (h2 : n < 690467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
