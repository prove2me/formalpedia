-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5415
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:47:45.50484+00:00
-- url     : https://prove2.me/submissions/73bc5a20-93aa-4972-9e92-35693848d75e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 973741007 ≤ n < 973920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 973742257 1250 973741007 973741037
    0x10608390c031c14010b1c02070b09070b1c0519140106090f05090a231315020a0807050d06032012062404090c0e010f08060702070e34 59
    0xd6041000c0155140c000b820042090103462070062000090101c1f040b882e42264009210032a000440b0170b4800301d0342030f4104800c240f0f050014a000e001160300d00b9040001c1e07408240c2c0c0d900748070f00500c82c0480c3e40d4804624000303401070415868000503c01440003005401440d030206400703100d5040810041d20001c61b030040c0002551064407009441c02040b0b6403240031080280c5000310b45450212000b08560fa20780e582003a041303100d440d022a51203840030042c98001010303010b80d00e0000c9001d20500c001c1c0050340e8064192a0000110f2800c0382e2600c080c455124024002d503407004101052594114040841001040f0f80455085a00050341d0002607440c0361100c004035485c812070002c0e1201c610000318581000441903030b0140c8001951046540c50100c0d02c0202d80140483c12000700042180e031241080030005802d11101070201410102400782d070b100c40a000300301503c1c90810003d160b07803415401c5000d811200501c625544440c141140f6022652140c0b80400244014100101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 973743507 1250 973742257 973742261
    0x5070807030513080c01120203071b03020c01450e162a0201080c04030b04200d42060f08070e06060d020c120d05010608390c031c 57
    0xc0c20383c10b031901f404003040244014020362006042a092210170741d1030258400022041d54101c9100e6002031040800c801c0025015003030941c0c3c030388114004443c9010100c40506040c0e0f40c4010309041002c0070740c0180d01000108182ca801018042e1030b81740c01c00100d071000f05a804a226429151412480c211000700361682444105c811604680d07080120300552080d4803032584051645526418651250340c0c48464010564042d114403080400d201107119561820352043c2000711500f40302d180540d501c50301c0e400d440320441d40c0c2d4200340c010011841110600f500140a40382003218000c80c64000b4035000070030450280010180c1054004200108001195425a61800a4982c1556540701003204c82da102d6481c0c4c25242d42c00b8451100145030400c00c844c1d0004e0b0319003009494140c46800a001c4860591101e020010b424081c84910070301ca0b003079484542074061250341801c1d0003143c00c903c9401e60060300d00003448002020b180442d00800a004145000031101350580c80c840340c13103c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 973744757 1250 973743507 973743523
    0xe0601030203040809010c0302070506070b15030616030207030509040e0f0d090b180301020403080325050307050909090a0503040f030618021005211311010206090d0c030507080703051308 82
    0x200e04d250800841906601500991484602c240704407a826501c9001240a640140000f12880d080e15000e103d0541c26202200d080c80c08290000e2005180100e88900ca00e0144d03032406080c9075001a0950901d8441e6088600b00b18019000744181e40c0780302c04090b696103400c0d01300328080c066128944201842604c108040320070107803072142040d103440c01002e01180c2c181401a41594200000030010300200301070752040e81d1031064080302840d0843c101d500705090200c80400c00008104006240f504041520402001500c40402c0c1d5658840b02c2407501c003161a0280c882d12001c2000102c0c8030480c0c00c4076064a101d12028410f00041103d000030303502c3e4140e0001d42c00016040c0c0b00c80300c10f115502130040700340c0d400d1001c8a4680d8960680880300340030340f002d03100c00001481060601c4001c4201c103001d24820302c01840383d440e209400c607481e0488080450100b01014850105051040c0151000c032030300500100c0d510302c0140f030090420b9100ca051044400340c0c00c01e0004952900ac20200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 973746007 1250 973744757 973744763
    0x30405011a01080712091401050612010501030201051606180503090102010b22091a09011d0a03090b031905151507030503040305031824131e17130e060103020304 71
    0x101303031240365003a00c2c1c41c130300d28041d918026a80d02e07440001c80c88600d0744e40d040b4010074000040c01d06182d0140100710203c00c402c0843d0382e043c4801040142d031300c0002c642c05060354240d2801e100d01145450400740003007094a051a114800300c81092040100040010510076002080080c50110030f1100004950240c40b000c60100707034400107070340115002440c41901c5107000d00f1182c0c241c4074159130008003c1c1c0301242c5a0390340c1c1d4105030890486030b82c5024032680c800b004010344002560010005601400b03610b68404c5c000c404200b0b0001d90408035440c20503511018820b514100c100d24000d00030100c5c3c00313880b40d540c03804403981c050700440464400365010340e0b80e00d2440c0d035191000c0e1003c0d070024115000010a03a006c010010000b884090894007131045040f01c1007811560030741e200324010300501c04803800c151440000410781030740d05070703490807454038544c0181c00c506201c400d01c0c46040a01846131030000700300c0b030b083d9600b042001c10713581c64031001304450310343c00011401c90104407401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 973747257 1250 973746007 973746017
    0x409030906180501020721120203040504061a0306191a12100602251206021908070c0f0f020402070f030201060801020a0c03030510090c020f100c21060506040605030405011a01 77
    0x1800380c1c82019064400e47c5200050310700301411a45c0d507100f50080030045500040e00082000d016524090003400010680e2614101c003aa030084c0c41041d583c4006800c0a220701000402c100f1441c4c4000385507001442600c60800400d841c0307244410741c036840940b44d000b0110707003400065540300141d0b4034482a1091a401040b102c21000e000c561441c01d098001500c950255000191003d20044034007400382c0324000168880311004108540d0741a120703a120b042c03104003420045515480943c0822080e040800540e81d0109800e001f600c484a4500281d046400010b8071018410b842c0c07070740052300e0300ca54020030035181e4551002d403c0f0b0082c800c06c0400500c0010507240407920171b401503600044101c249000b02559181c109080702c0048840c000580c00c02c410001281006000e1194403002c050700c188480303d195a8010201540941c50510b0000802c1d40c18844c1d4070141d201c0405400040c142555a80c2c840c00c3c0980182c00450f8221020740c244404c442c14400c149400c505d400c42d0684407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 973748507 1250 973747257 973747259
    0x10207031b0c05150f030703020711030a0b0a0c030b040c05040510031107080a1106040c090c021207081b03270f0a06030c020a08030f01081203280b04090309061805010207 75
    0x1013024401d10070088001280d030078444000710102c0a00194020801f50b14016a621002d1030904010484200313400c1c841d4000350562000f040d101608240d01000c4040d000034502e40c5000d043e401450801e4045401c10303d080c2101c1c8149030800002c02c1643c00448642400c0038600c0c1c8200c003900d040c8070300d10b15500c1c020b016400001d80c0030b4000e081003415900701002c0e00c0c0442d640030b07490400100d400792800e0540c40010861410303184162000d51389644042c00c10030460803074980e00380c45120002000c2e5503001a228072042e000500840c84102a03000752680c88460940010030031104603034602d18450603189021a510341031209840b2208081d1040e0341e00ca140020030b80003803462558650950084e0307070300100003403504002140301c0d051a543c103030210750400c80c00d50302e40303140c01350031200000f000c00034404072035100c882c0001c100c0700d040134403404c10003598501c1c0080c04188200355000350902d10744a04060704001707010141c5010b5a100900c10780e00e0744016150503424802c850160300000c2c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 973749757 1250 973748507 973748509
    0x120601140f0109181e020c060c0c070503060103140d09060c0f0c090f020c070602031c11070f051e01020a0e13021b030409050a0209210f060108010207031b0c05 70
    0x1034603200c120014100816940d80d92000182010740c030b010300303100e8180c0c0c40c04840078420070880c494054900c1750508500b0180001199507031041c000d011902c0050020507030201c5d1041c1080341101814003d02903600790f5075a850010803140b03030a00c5d406624001e0f02d4a10003014480c010304e004641450f560807010500302d440c1c0c40780174198000b080d9542a03105102145040d07580c060300c0f0205c9124800140e4550a5005081c24a0311503001030046401c03c01004082c0c80f035411041c1055001c80c0d80008a1a21002074090780d4031400030001c1400d60380701884824000042000e00008172203a00c0c1c9403440051545260807072003030289140120380300d58444000d9040c411081004d603004124014504a00c0c900355070061b1100c1c4001c07004c030798000241800b0a81e21800b07074640100306250194203090102c40052a0b2030544c3c20072031406c21468640d406244c4003040325400c0000701c80d0684071503507114150a4080e501c80c01c001c0c1d000c0b030103015891811400c01c1060f1014a5084080c1000060400c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 973751007 1250 973749757 973749769
    0x902010f03091b081b030d0e1c0f0602030f0907030201080a1a04020d023001090c17240303030103110103020c100f0c12020702030d08100801060e0612060114 69
    0x14140e40000398036a0312503000b0074010002c1c02130512400100102c40d0010440b4109800d0081000c1c081d4100148105809400100300088440121040c03010080685065144095500c80140c16501040e581000f401015402107000d0a403441c284456985c4038544190344803401d02c1f000b070009084030005011514035601c010244903004446041100c1c0c1200000d0607600a054095650760b40020640822400200e5410003044462031911720050000e0b100d0183c408144500c41c02c4a440700c001d950502e12484038003400c11044070022031141080001d129007811202008001e5001c80051001d142c83c3c0082664101d95014030480c8031507a40c07800460203504011260405440f82d5101704a07010500e01802c10b0322101c086000503e005051401007454042c400480e0a0910400c04d65000d0b80340810704180400341401e0420054840d1501500d0440a9920a503920352801201044017192101c40e2400790604454000c00b0309000c5503216150340c001c0c8940c1081c200c654404c2125030500b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 973752257 1250 973751007 973751021
    0x609070e06161703180703050c0f010909050901090507050301020f0702040e0c09090609010c030905030306010f120606090e0f0f150414130c08030f0726071506090902010f03 76
    0x306861480b401c076603696110500e90901c1c0c410a054401004108004c20b500c1c0040c1607501d45c107001001c403e841c2d603d80544501070514074a010300010f0201d4192640588176000c002c5c00e490204008500d05044d00b14020180420221841d000308200060349103414000c1c3c030110420000107a20340202c6900300f000070440c0c22401c00c0140946418071030306680b00d4045a1013408032501030861880c00d8841c250071190f8114206d400d04d4505990341340400c100005803503008a003070800d05d5100000901c280c0e100c500070384d82e2102480c18210046810f641c03008800703048860f190030b050910b8417581040036036200205c5403070358040300a2000807007550300100210b040e41c0e4090000201d490203210005450300044452018614100c0703142c008100784152005c0c02024040040e40c10b0002c12400f00ba10b9205002025211402032001d4400f049440005519142c842c5d1240c0303a42e64000b0719000740ea4001c0c040d0000200c03483c007000010010840e0050140140e4140d460511003030401c08190010401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 973753507 1250 973752257 973752277
    0x3206090102040528080a0f0c0501081b1602151c02160308180109030f170c1603030e0106080a02130e07030f061407020601051908060109020a02120f09090609070e06 72
    0x8204e0000401490030300c81c0d481c0103401380030100940c2c001c0341030640148103640d001c2c13070402c060002085031025030a00181d0b0140c1d50740ea0300ea0f58600080c180946005c41c441ca004e50701143c40c1c00f029018201e040010315425019076924140c07000d60f00e841c2e400701e01881404424182000e5001c2000a101d6030302c0551002d408200680c0c031a030501d81043c00c50b0032141c4118046103180300780189031500302c0f00008245c44400c2c02004140340014101b202c0e0b000b18072103803002400f0500040b081500907002403100000b041d0007004025900c001490340c1da420321405074013131015050001c030241d00310300a00580201610080000501e1540c0e41e4601703401070320042d1003c59880203040e40104c607201a45015030740300c0d4001c20042d41441c041280180540c018900350605480080151075030200b081411036041460050715468806000e1741890102030036500d04800c0019510100c0d0403001c0a00401d45d02070f10a000182d840d1828406103000030f403510f001180101841e60040e180440040c640581 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 973754757 1250 973753507 973753579
    0x3060c05040f0b030a0b0f01020a1106280906050a080f06010e0405040303050402010342150c050d05070803040204052a0c10060e1332060901020405 65
    0x2940750201000b65015812440c0700c1c0300004184510301140340036034010800119040b05088984c0340010b5035410322000c0c001c00070100d541c1511190340d5000c05840c810070448030030003020320200c03d100307e000807020200000704410180c04030b6441d00c1102502c05581d07441d26240929103c2d0300a484440e680105100d04010300f0001d02e8000d0b850310f0041c180a544280c030040b9090070103100140a5420b001d130f80c468802d0404220b00c0741c543c072200008612200b40c0801390403d403d109200600e17442140c101d400d14104401c040083c5960020716a94030601960686503c2000c0000460b52840703802c0780a8003003181440860007528041d40409d4020f02840f41e081c0100e288211000050050b005007000780312004180c0e8040524140801041c4014100042140da4242101c41203201d2001c2c0443c444840c07500e0f10a03040040d03504002c0c208032108044890024402e40300100c406c0700f00c00ca4480b0350701550b000f08049060500075a000e481004001525444101c944038444c41090400303054081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 973756007 1250 973754757 973754759
    0x809160605072006180f032e110d020c01060305060c130b03010501081902040815092b030c02070b03130b070f1403250206160c080403060c0504 63
    0x100064050002010251607950711010681002406410254070003501c48940c02c244015940c0c504007282c01c110082c559040103441e000713001c5100b02124082d866058826035040d6400104807030701e42079039000040b44130003080d0784408003201900c0400407100c0080100b40281c10a60a4a4010b801e01002d100000192950303030fa102c0030b16044c800c0d1401c0110b6003001560754407040c400005003000d0b100d00048a45903500d001c1c0003c14101e4010200441020001030200c45280d00342c044a0080c03a019044540c00e140c4400114800b40301540c1020541c0710708113044c081060450411210000001401060961354800603409021208030090031400354020103d4460f003c01c02440c0592242d81720808488164035281003441c0303000c2e104106000c0c1a41106006903485200800c0c07041c02e00b105e450301c075200d00d0102c00f052002400401003003200d05c0041054a940050894894a00f0038203005400008030010303034204140341c4c07014140b003c0c1003009002152180d0006c3c09040001d280043c942 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 973757257 1250 973756007 973756033
    0x609041109010e010510030e070303050f0d06080c130903020c0907020f060a020d1d0a0303090606030f1b0f030503092119060b090717041104020c100c020f07060809 72
    0x41c03409811407920510040010b00007410070555810900c0910b0804004000505501320b946608c80c0c40000d0411800080007c210040031056070103100441405000c19921080303859158920012003c1c024103d0f9201e0711585a8607003d110416500342d0054142040100140000300c1c10090841065100b1050032400611040001c98418a0100c80c01600e8100c01c0e03110000b514070003103c95104201d44070300c004900e1000303c3d020f200d103541230400150b40d80307985c41d000b0054002035001400c140941c001410902c0310460343c2c04508421045100d02c503540303075068414080a1070001500070360051000c040340e070421042032041c501a40760a041c005501d400b40c289440f50702003a801c0c2011501c00390004025150103080d44a100480307030b643d19448d20103c001d006104001050740311660302030201e4144030f08440c81d1220f501016000f90b689075102d80c02c06a980790f20150a80c862450300440d2400780e4070104581c18640591406040c03890b1a0030000c40b000e4002078104107843c0160010302d9a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 973758507 1250 973757257 973757269
    0x20f04060810050105071520040603022206091703160c030515150d02010e031023061f180906060206070f050405041109121e0a020906090411 62
    0x109659070300c01c0081e00e402c1d59880c61071800756000d0783c10f01500b8000840040c884074070074500c50760440c000182c1d0481e101e18405d0b4450400011500e1070000182c042503036940354000301902c0c0300c6810f205880b011440031610002865201700300000d0304a60b0280320f04903200d242c2840f403c225108980c103020000000b4075008048901c2280d0322044240f0800800030b01381b20035102c0038010302c0c4210051030011000790100622004062083e0a286d8442045a00038804250075910160848504441c8c000302a0000e002e207001c623001c5005000d105c1203074014241c0354a0700c241006006502d5a0f0403001d4a07090301c010000c0401e0602c00400f6103030000c450086410002860031110220b00c41c0e14058019040c80030140040b01082182d414100809810000312002c566042d00c000505107070a00580189018040b0500d0f80300550b100042011400000c100d002c00d65040801901c00700d065648541c2c40c01903001c02500407903000001189481c003030b148194040e020711006812410408001a9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 973759757 1250 973758507 973758509
    0x9270e060106021506010212030403020312010b0a031d0a1103030c0a06021305180712061806030501151421030304030804141609020d1d0c030d031b03050901020f04 72
    0x44180c0c00040100062541049014481c010080c000109400c1c1003000035100c07000c95100e800c40c030b5000004101058801c00131560302c04060920780087d075840e0702d900003140d8048070a803c0002d013000001c2c81c19841c0c1380c03440f4003030800e4000186044c2d4103d60761450703100036240110b54140010f01000f0b603100400e001e2114405d104a00050391614128480d080303454498200324010210304040141040c151b08069804c1082800c0054800c62036041a00140c0515002032854000000d480c81c40301100750001e0054a1141000740030880c0c0c010f10410300325842d88078455002c281c1c80e040c1409030403c5410a00416225000603d4444a13841100e14560055400304d002401c81e01c1003000744001515543c402d07010900142ca440da003141c0e0040c1c880c0035a80112210151700059131a400001a404003100200011000da980c0704550911911100c1c1d020300715001c1c1c0594242401c3c0c0500c24030511004442d480c8445000b100c0154080340100300c02044c0c105150340c01c218440902c0040b4006d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 973761007 1250 973759757 973759781
    0x2210412030e01080f011d09100e070e1f0306020c070e0f0f060f030c010305091e0303010801051005130209130f021b031206091b04030303020903010e0d0927 69
    0x4105001c2c400004040b20402001043c0203490500188032400606000640c0760220010f001143c1d125a5141c50800000c6592103034118900000d0b0001c2d0384020901100300c4608000780b69069641e040304608404880c00c6521400c0d031030080600010790203a0181000358411421244207988612120300c8a41d0252207a031a0200c15804201d41d1201c038101441c2e20081c00d4580c805c070055250042030740c030601c07420300c1818151940c00041d00e95400704403005400c5200e4500c1d0705030484031910070751a50700a000f594042e500300000520002400c03540e040c00c80d82c0140001c4000190000d00e98020b4100801030740c2c0c8004a00d00342c0740d22402e14041c250f52809091001651680c410801109a041071f01003c01681c01c288403000d4140c040f0880c169100307209072801e00391544c3c0c1483c0b03140300c20040c40601900000201d00171050642c103601500344000194000c00031604840829a62900081000d0b0005041100b003880080381c0003140e2210f9201c4561b03000a60760480300c00d4403e07103000300f00c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 973762257 1250 973761007 973761017
    0xb06041d042607020310141b09100c0b09060421030e010f0b0a09090f1101050f0705010506090903091f0507212a0224070b060a05010f0221041203 64
    0x281e0941c80c062100c3c4c6c1003030180100c10040a00c2c43d07007070013000d50001080d00035510b070020415100c5041c00d00032511010300007411002100076009012706001d81036034040e901140944000b4903051307800140c103070207643c1103541d00703011801000300e1906040504903030384e042507250444805c400700d00340913840207864400008940f500c0701c20240204880d03643c0c404440a800c00303c038030022500c0310b04440c00654103d001082e29100880042c0c86c50f2103030701901950403900142c140107000065000da8005c0c0f004449840180d26003198995407401080b00d03155110902c12102949000c0c640301e068100300d950b04015060800a448204441e046417408402c401110f051408a543d0302c040200902650b0140d0080d495901a18403604580350a400a0048041c90500f07403203000ea60307140c0b0702c40c180a00c0382c0640c3c540440c0340003e40b4070b900343c030414082c00c214800842d407503000d41d510750108500340d0300401544082000804c88140d1010088508000401c40490000317100b540290b030302d6000352a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 973763507 1250 973762257 973762267
    0x2104030921060c17130212031c0b1f030903030e0f030403380a0617030a030b0102030a23041d0f060a0f0e0a14070906030b06041d0426 59
    0x588200403101402c01c1078540c1c0c000402d81d00020300d0381c2c00c505145c80c0440012281d201007012068000d200c4001c903c004105c0c56521307140c21025206002282005000040070202030000700329a0100c07200c5030460308079074460141d200740d03c004841b40c001e183c082100110701000600b8041c105041d4021600001414028491040024910041b0706005982d04801c100111141103422a0002d050b404003800803c424650039001500605068400400414038003c2c03001d03a02d0344004c2000707010a0030145140415030001c0280c1e20b10f4642a181e042070101500c4008613030b000200d04030040000c5c2480003250b00d1400d14003010354213400c0140c00d5110300b07180101c0314079594001c01c0319115a68400003440500c4a01c0f101070100c50740302e000e030122605d400303107501d014040554070f418850010310100411140d026042c10300b1070743c0ca40c40801c40406c850b0b040c04940e1080d4051600038080c2c0c0f03060070340d40070401448150305c1401112040c02d00212145a14580c1510400303a084004021403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 973764757 1250 973763507 973763513
    0xa0c020901170a12020705150924030a09020402041e06090f03030c080c0a151b0801080303060f030a05030706050609070503070905010e060904052a2104030921 70
    0xa011400341880a005040b142d24503103541d9915840032000030030040c51101341e001054005c0203004003a2070001c1800119800401c0100066001401c02c0c1c0c0c0300d28041000d140036442244454004100c08096040c6036940710282500039040c454012070b00580d0801002501ca00e0361450000c1503842860300b5a00c440c501800100011620f80050000700700d100f40800020b90442d003c1200d55501c940320070340b1000e410701d0795802d04642846c0035101c80076038aa2400c00200d1640461132210110750b10004401c45500203c2e00c0d034009002d206602d0f40108085001442d05808800f40c40d20002c0840719121855504c40781103420000c0200c680c141c8803c04d0102d00e00c1c08103001d40c0e00c0300c1030b8030f0800d082d8030705070300c0080140400b031080c14180841511807028a440380001c54181500c040d10500150518030350011040300c1c1031502986003000c2645020a8030301c00303001c13900651010308644102130194050403d8a04001e0302c04c5092003002940001c1d200b800506580309400d05548641240c2c0c0142 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 973766007 1250 973764757 973764769
    0x1050f0414030f0304020f0409120306030302062a0d0902210c010c0b0f221a060105040f091e050717060105031e090a08040f0f080a11010c020f04020a0c02 68
    0x34803400c040c1c0c000740700000c3c00600e000140c0ea449501110118a28000840494010000a40041c1003403000203c0700e08215050340010088910aa00315003e9507540700d070600d51440c6c1c840303101c400107400028000f400e862050140401c0d4080350f0b400078440981d0381c0060916902000702c3e0828610b800c60600c4482c00a01441d0101d5000b8204502c5c2d00d141961004014200105000700e886c0342c81e40461040e990310300050007500c06104211101c0006403c003120079640212100d4044404540050495442a17013940e00701ca13541424041e006047c445040090401039242240940211288640080a5000351400b440031601d50a901880c0084c051505040090a0505110b000c00070f100200c26910882c40c082240c441000040b510307580c0701c8508014610602400340e0002060108400b9240c8400b034040350b181c26040784050742ea588195071200e940000c06005c00d15000c02001c000e500400c2115412480200a48a07080c0034400280407a04000201e0001510b5001003808500b880 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 973767257 1250 973766007 973766033
    0x30e07090c0f022a0d03030908161b03020d0803180a0309090f0b0307050402160f050606030607090602120a05160b060f0a0b0307140c0106120303050c281101050f04 72
    0x26000c0d07050600c9002544c1075180c0300b0b1010300c5000710a54071a110034588607601c1414220b50091f42a59100365000707103240d400b01d07101c40544505095042264400030036280f850b0440390701510100400c1455100d103496500020715134a5080c0c0040048103142505225220a0610944038440310320704010030303203003201c044100c84403595142001e038004a540001f030310812030b03204031401f503038405001000040e09603c034680180446010a100c20030040c0104011344288410b030b00321072003035407803560883d640340d1284203140258005000050401560304003c21180003541080c13850403800e02d000e040c800340c00c4070f02600c1c040302100521040d450800c40d090341c42e040807140140c00c2030402c1da244c4110700c4090407100501002c0c412a580c41e50079230040d07400c41d24411000300005950381e018101e0762808035000b03c0000340303410000b03070780340c031100703050381c80d40700070104590840daa1840480f10402c51844803601131110f0400b02050006090060074450300681080040c00d0401d898208108120303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 973768507 1250 973767257 973767283
    0x2030a0b0d1505060102010b120f0d080c03070e0a0e10050312130509040c051201050f0a09050a0b09033609061507240e1c0f030e07090c0f02 62
    0x34481054000ca0850b030340c41c1126590b03071400001c00740c0f1a1070041c0e0040c400c0c01c4049401030b200c80b40301581c40030302107100e000101200003034881c04034111404a419078004c5580c500318950900205241c240709032407801c0c003901c001c0c0c9241903454603020300c0811070100701c8180041c040c80107820702007820140410a01c0c0d46a14804604243c4080410482c2020b6405242e008185160000d01840502401d81006000c0503120003007104211000b10701803c0100e07952140127032240c021030402d1542d442962603164115008d0b100703000c02a5124840004090500c3d040f610051003840301949481e0703c2c551040c001650080c0704011100035440c0344140c00801e081c03103428148200000c607250708401c1861501c40003002a51072017580b0308010f9800c00040c0c1488104201000503000e15050360140522004007004c560345c41c12044200420623a09108040024100e821072020b44c3d0f0007a0000318845814009603089207803603c07444412100751083d0000000d14041740d094400340c0500c0814051030f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 973769757 1250 973768507 973768519
    0xb0115030b181015090612180807120c02060d0b0f0a14010909110a0804050106080a030c03080f190f1808090118060c142a0a060507050a0303021b070902030a0b 70
    0x20320040c0c0503080703284030700c1906c041c442c41340780c09210300542e40d000c0d00d94031400c9180b000c80440c1c10b0900700d0b500d0304100422503038500340c1c10b03c40321000d00030141000750383d40c0204410301d048041034080010300b46900c0b0b456000142041480c5a55591803207003c0030309001c0420501210a150004103101e13555400021000e1a2410040301c500d01d034000c0b2040000c8500749400720f81ca5030b00d4001d004009561090101d0b00845d1054001c066203e649125072900a946a41311600c17180e110a078911400d41d086412041a045492004031081e040441c0c0700309a00000180c1310b00c901408d1900c42d65004080b038009100040b20003040d0303085001d0242044200d220400c0107424000c0181c0105004000903200355008000c064903410b0030800c0c0c2d04d40b1010031006100c1d0b040300c20038508140c41c0303089000e480b03024158804501e180c030030390950b80003039085802050b03003943d00d840544c0254000c0c41450640070940c08140b20305001041002c2c010240c0300c2c00181d491030000a0002103c0000c251b151080b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 973771007 1250 973769757 973769789
    0xf12011b030911040b0102100c170108030a08011e0306060305060a050708091207020409050118031b02150318030f0901091401021f0b03011a09090a0b0115030b1810 72
    0x740403044400d03604034084e540040c020101d940180d240003903a030022484541003007600c000c0180d100410340540f4000001e11b0509980300e00d07130300d601e80c096102320100240300d80004111505400d109000c030340d40c00020480c0056120784034041a56030a40098a0f1340d8414418080880c00e14841da035480202ca19200121781081c2003000e444140e5624600d202507001300d202c80640d41c55a2100c0d8850768080000c02010450440c02d0540c003414071026804205000103591070700510008500801d50b000303220070000e004400740c40665400103005402e15a604003414448004100002d160341d81000b484142c80d030304005e0005000c07070510b405ca5000d0742c1e41c44100e12845d980000d41809080301c648000702c0d0031010740b420703000180491441b0680c10341c00d0082400c2c81046000100201900540e0040308955070b010585a030b46080c260002d0041c9140001007044030303103e49204503905514074010900c2c1442000288105210004140c000d44032001882030740d261180003440180450b4440449034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 973772257 1250 973771007 973771013
    0x41205060717040b041a01090c020c03010c050a0c0c030c0b04031511040603020a0c0b070f02010e0705010804140304050904230c030c04020c0a0b0916060e130b0f12011b0309 76
    0xf52000300911650070120307080040214040c400303040304000060344d941e900e8410713101070b100c13004a29003d030203558900781345400c0c180070790311020a0139150076140c0407003402c044507040041d0070150f915641104001c00024040050340008140d81d10b800c47e261401c60401401e08200030340c2c40701619160440b8000b40c003043d6015602142c000703050041c0c4809a10000391802103203200010150b1036032000b0400195003000c0c0324070362442705038001c004484002c3c03003070355607110580180360201e841c01000400081909010075464011041603a0400e5603860120316000c0c804c0e0390440744585d007006c40b84000149440140054243c0c1802060710303004603004640c50302200c01c189409142c002401e03d102d4541005060044c580c003004000c40ca1401c0805184c43d4540303020300000e800403403040000d07501d1040c5d0200490f000000c05880007110b4520140005002104280b070b04080d00068200c20340d0b0310704008400001484001060801d80200c0301d505055084442206061528a2207008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 973773507 1250 973772257 973772297
    0x11030f0c1f0209030d0e010c12020f010b03062e03080c1b03150105010311040b0c010b030d02070f09050a0b1e0406120305032205120c010c050f1207090504020412050607 74
    0x780c5ca5400d2801c09540c140e030040f20181d80d1344101514200c0000301079a0300b268002007900204104400030090900c00004150b1a07050542c0c601030441445020a988082e0311410324000e00300c02e440c03042075142d896a0340b0007d03800040d00f403031454000d40c1240f18448014a04000d01c654102c002e8641c03008503107100c206103041070190b68109540c840645c0b007421004c1c003c450250a4150f001c503180e10b0071446141c00382c40408400c5010f4000d130030201010700d00004020041d2004102c01c1c001c01424000c4210040c2070040068421541320b000b03111003525554500c004000c0d44507104860300c10007405020a6610340d5202c030b00e050074421074400c04a035214003600e4000c080c201442c43d021080551203040c1c0074040c41c0c0a02540a2841095080c1d0303022401401803500410081c04902103410301580c00303001d202d54284440c03604015004422910480c90b0358450313600d003130440a060b00c8202240498105800800700b580011102d0400d02800700040f41d030101c05071a00707010b4175909141544e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 973774757 1250 973773507 973773523
    0x92b120f0206150a0b0c030d0b040203072307061a01030507020f25260106080706120b0a0b0c07031703070f08070e091005180705090111030f0c1f020903 67
    0x5407036401c2c0000858943e448040004c004c00101401544902c0e200c0d103456101d5116518141c846840c00740d41199038180360082e40c3c843d0078030f62281e144110205461b070803418059034030343c00f100303808100050024409205050754400000341c41c1c075000c00300c41d002504903400a4032130410f42d4005070f01d0045152000800030600742038004540d0309541006c0c02c030b000411598104804081040041c042d485180d0031043c008018101c0c000e0254581e1012443d80fa5041402030310006a180703801c02c041c8850303540103031040740c2000d82051503d9640342c0c0c104a254001e0b41c180d024a0b0001a000c2080c42242050f100d10b00d0380e55001d252030740c1441e0070090404c189002c0b4240902001c4000950b669008141f004031414019005150518210708002c41e000600d01616100d01700034900000702c80c021484c0540708500301d0322004d10b4070f45e140d001034800e00400f030354803603081c807041081760b004080c3d01000c0c0c0f10b400074802c0200210072592800001d071110b034007800c01e031161061110070368076500042d02c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 973776007 1250 973774757 973774771
    0x20a03063210021011190c020a05041a03010609231006140c0d0c030f0c0b04020f13090f060e030a0804061503060e060f0709030503040308092b120f0206 67
    0x24400150440e00f40d0900000c0d60301d0b00707001c0386810130300c1c0d0005082d00028002d03407040369031500040400322030640d4149000e06e400303908003002100900140c10141c0c020214118500c2903145c40c1c40007030340041e0a50700c840c2c20050031151500d040008001c0c000500049401c0c406142c40318900d405600e032101440709103c2c5008024000100103c07000d0014221081c1e001d02304243c403800800b152000e4000031295004030009603104c020322400b50f2184400c003c804e540041340c660691926020000202281c13004a07502000f9003a00103c074106030b00c54041e41da03200c0d900c16070501c0030030b04081040302c402010301129a0030822507556000d521800390f0f5442036010702c00050b41d00f491001d0420803110794000815052038160354060940001030100e200e8140030042100a9441040882d041c503514400100a584240001e00c00928500c000d0800e13014094506070126000c24032002c114050468441054040b0500600910240300c0c07210380e80c0007050510580701180100000c1d5690300041c508 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 973777257 1250 973776007 973776019
    0x10512040812040b041203050906150f04021303060f05040f12030b090903030f0c041404051e01030c0f06020c18090f071d090a050c01050a050d020a030632 68
    0x4081200100640da4540002d000300c408610381031a00b003040c07071429241903803004454a0603844192190003110b1080c031030503000c0c160540341c444080119107500c042090703000000d0004201107864034806441514408054070005c0e03407450504d1800c54180c07001e105606400d19080002003140764030810003c0d5440303a0001e050010300c040c01c400500b42c1e0308000c0d80c0001c05005004000700000099400f6189044266003151200c2642e107020b480795204034610420056450070107860300781d0102d507201070200030341c03803089003080c07040010b04400b600210f0309000b0182d400c1c8000b05d210300911004c0c0100c0d00082400000382800500c800c00c01010030700c2c0aa0340040040d00490051000c024040422021580020348800340d520716403400d4026640301c48240000101013010006a8080041c0c005001e4032403140c039100110343d5036010910381000d1010800840c00c40030071501c010505030655581c00500c3d03130f06249075401c82443c41d101a0500a903141c81941d034980112164040c03010f021104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 973778507 1250 973777257 973777261
    0x14070b011a04031217060d0506011505040b0a02160f050d061116060b01030c020a02102a030f080f09100b010c0c080105040309060c03021f06080109050a0308100302010512 75
    0x3110700c0620a0f03402c01040200008803000d80d0310f4109901c00c9402e034502c548551240d42d01300920003045106c40c4041c1181e48150010451400281249480480b0304d2501030f160170340b03400781800d40d940b0240384180164001281c50003041782000f01100900752000001e4081841d03d00080d401d001c11240c080d0500b59260302c15405003682c0d00440b03c0a0309160690880b01e841400d0032001050302c841024003182c00c0c01c0010b40d200b807000c00c003107103402e9000b0142c14945c0c00d0320604648658002e0740039102e8201c40c0e06080d19a004012080d141c1c14400d9803071101690030a03000030b000160242100c000c1103400c50600c45502000305180300e0484031300600248942c0c019004840074014920050940d03416404003249415040d00071702d204d00e01075101d403d01595945812204480c0283d00a401600f054032050380c100076106075035208140082f00404e03241c0d29404071508540290900300d0b003a074800c0c00541c0801d6000303151141e001580b8021030795030318a59000a00030744180d807203d43d15900701d100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 973779757 1250 973778507 973778549
    0x1902090a08100509010b0d030c080d0b030708010911011b140309060403060204050a0e33041a0901170c010810090e1506041a0f04110c010204050114070b01 68
    0x20300030007100303085a80c6000c1c02d010071001858107580e600095400c02070f92a1080c14400c004440c2c1c41d6141ea145200340c080c40c4c0350704519401014202404617107070281e03180c8540e4108013202c06088090000160310303040e880d04c1500c48440851890500c1098901254a080100d02d600c01d15a0410412035141840f02c80e42e500314400e010600ea0300c10408180801445040e40c050025503205603440d960b4681c855809891f001d100303e95101150285419032003100d81c440d02100441990700324081981c40004c00040d0035501c050b9622010141e640085410390328180b0300050040000380d0002c540c2010900045445142040216050203090300105425034000c084600045c58000c07400c000c0c00d154420001d40701c2c00c2005409140100310310101d5100c0c038081c0324242c15100e2084841d400108039a041c0070070200d400c003441d80d00a56510083d880324261600600107207100c1400181d03240d00b06030024005185100b10b85840d1082030160780c00256180d0009415a4240f124402042e00700c02c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 973781007 1250 973779757 973779769
    0x50417100203010b1c05130f05012a0e010804022419110d050306060702041a10021e060405031815040b04031703101e031a0a0c08190209 60
    0x19515110350320010000400d15802c10150081c5002034680c0c0c60f100d0041c0e880720095400a5800c44000c8986006100014410a10a0740910700c20310000c0b40c1c0c1c48101210350500d4640d18601c1070f5032105120700b612074550100101c9007480f801d0034468041d0626402080b9880d80300c0c400b000d01102e40301c8600d500107040d0003e0f075506001c00c201c542501d400c401401030a0908010018600340b241d620090003841c0141c056901c24180601a503080c0b440580030480905101d0003005058180e1540d0003090b5140d1450310f003000d80090300200110040392a1a00c0e812140341c0d8615010b801c41420b12002507008012580903050503200d1300c4240aa0200180d2400c1d264030520308021030005000076a9002c4201420899015102c03000502e0701c1da041030840c034401120b000403001c2010009106490815401003000c200940b0780180b41920ba540e03643c0751031400710f1241c00306002c010800031705c3d4002d405242800140352800308802d081070200ca40e02c0342c03104620f8070704c111780209640490741ca0341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 973782257 1250 973781007 973781023
    0x603291c08043803060a031b080105010f24050d02030a05060102251520061605090f0918010e0105090d020109030f0c020d060c030b0f030102040b04031104110c061806040201050417 79
    0x507510400d030b402240241a48031140e1180e2742544d401c01e0000603404548126450458a0840f00d040084407842c121044140d8001c0440b01400400c0c41841c1c10300c4e9080c03000d5071141140882c0095541806000a4600340500059800440c4084000c1403540d1000176504100c2d5a8910000e801c030720311410590340b00958625016141100c13505601c4050000a165070003002c25002928008041050031150b500c42c0c2c3c0102508880c0c482d589007400e007030590009a102840b803208120292061100c44c1c00c0d10000c0304443d0315603441c2c4c005d10401042c14003c194802c2e2031800200b2240b04180d80c040c1510780500d45034400c0c0102e820600b000c0d51200180d0b00c090302c0d402042001a1141081c024008191076960103002c0c0704001d002c00800d050500c00c48095402c2c5100d15070516141d592801c01100300c2d07100301604203481d01c1a000304003100c407000e40012032001001e403d540ca000781170042c8542140c4603505180c0d020109010150f60403100b25801c1c2d8003d001c244070780d41103d1010383d1801d822 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 973783507 1250 973782257 973782263
    0x3140a02090a03150908070f0605090d1d0409241103090a03050a020c090a0905060717061003090c060207061205060d0b18070605030a060603291c08043803060a03 71
    0x10019428040123030051a0340354103031150742c0c100559285d201c80560b51b03084100010000c44e4120915042c00b40541c50700d18001c100051020692032080d41d02c40003082000340380100d045844958282069090740924002c254511070b05900318507200c07031510f560740710700c0c60040d042c40b00000e07501ca0110b10a0040384486140905001300500b06074802d000240b01100c0c0c15500ca004900c04604d4540c0b00c0d845d0081e50400303124441c0c00c103440340800c016400c0c02c040c507401c09041d696241100010000a0300030000c1c46c05030013518100b89040000381c0340580c80e518044801b450401042003d07a1450710b0400c003035030442440701c0309544114011041c040c0740b0b192a205885058000506154010000c41c0700c0e10420205114165907402c3c10740a90742c0350785100f14090b8440d00256101180320391400c0200a0017040b400000000c9840310307081e01d00d01f42d4162030a500c0010240841d03004500190840302904283d4902c82d03600800a400d960b5041140148805001020038240d5548152040155030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 973784757 1250 973783507 973783523
    0x1103090d08220306060608102c15030f030c280b250905010c1514010801023f0604060b2109010902030a080a050f0a03140a02090a031509 60
    0x80e03084480348202d0584003c0320300a04003039005c10300500c40ea40e03103800b9541c0c0030308403100b441c02c0440c0c50104071015202c1c040c568030034800382403044082000d00e9014410103c03e0030030104524007410700b881c14044203403107150310401400c91100300000700700f803003098500781c2c80209a070000070083c900e10a900c0b02529007031001c400e001034869220200503c070b03800b01540d0a4160905042600c00c024680b2850740420b02c00503025000c6080c02e0b01c0204102d9501744001000084840e204100380800c1c0c02c00c5120760740c042800c08900a042c00184010400322800c04000b401c2060b40c0000442d03050503142440c5038150105205494139000b04000d48640088940c65005840b03000404008d100002e50034042900c01040d140d110601c100130a544e0003a01404004009440744096540440002010880d04000d04c88440b010a8003400a41d00a07a070003080e1120101c5100d4a01030002c1c000c1000c0f98030411112080b5a21070b25007104513580304050301900ca0103107a003940101079980c40903107800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 973786007 1250 973784757 973784797
    0xa0308180109320108130809060d1815021207051b0f0d0e0a03030912110a0b0c060a1506030c0e04020f09100201050103030503040b060409171305011103090d08 70
    0xc000083c8100120460118540c0444840300044404810944070128081e0b113201440010407406030041c5079900001d043c0900d400d184601040c11107001d100b0030107840d6084642e030b200b00440340d03800c0346008440c490150301b402d99400c103184040401034442c10030b0150000c0c0f82e112210480c4042c1001c0c4880405485184201d24204c0c8c0e00d800d8038a0440c070000e65542e4452080745003800e0100d0a8940656940d00d40320706086981c1c09802c5c071004d0a80301c0650420005a6964840e040e00c0301900d0b20004a41d02c4401e00040c4514081014004d14140d90900e125000c080003440302c0403044a009103030100318110004000d842c0024213003c41a049400000c40040004030000100002002651841c448030031032081242240c03c01c0c0130050002e0010030200340440c808000301034003e000244002b41c1c06042d565a000c00c9448914002e40f190008074450702c00c0007850a0110042400f070074448e2046448144807501c9200d444141e51203503020652a03410310202c041034502d070003840203c00e1090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 973787257 1250 973786007 973786049
    0xa02030a060b01030b0a080303070509010c051048050403061d19150b060f0c010e06070903020a03060c021f06090b040b01230f0a0903060b0a0308180109 67
    0xe0103003600418042420014018146c3c208942800e0031604c504000c2e604588800000710b59a40c0a15a09410000d030701000e480420001d00108c81180c0a010303000540e1090024601c1c1403440108802c0500901c1c0c03041259101c220019040d400d8014202c13003101c105d640e83c0183c40340c2c0519000980954903091a0071200d11042640c2501034101740f044912a002c905050705000030440c1d002080e040010301c022084030f030f040c1c202c100542c200922081c00c00c808410401d2254008400c3d44402c1d81d150041072600350001e20280c1c1c0c01c842d06240c01c0703580504640100700c2c1c20646200051410396a02e00c07003070361030780f080c04520340c402d4102038190f100c00e2802c000840500250f008883d80940b03005611842c0c1d250521501040c00f174180c440d02c1020181a088070903002c0050311048030540100301c03810300c1c21004c500130482d10115803079906c00a800c5040403c00c6458007110907000307520020003400803030a00c006481540359401140514081d0035001200c070302c0859440741d84d80c170100c00801388203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 973788507 1250 973787257 973787261
    0x5060730030504110d05120d0207061802040b0f01170a091e03020d02030301061d12060c040314012a140409050403020c0103050c090f060403021201020301030b0906090616020a02030a06 81
    0xe6801901c4541d101301100d010042249298040181264800045d04008410310b10240962480700b110060504a00d40c03140002c2c0e58036400348001c00310b107003031408045107421b02c50300402a1098030700003583d010f040c00182804440075200b007009a002400a14240c50580262038155440074840540c564000c1211003102e072016403c81c0035000e0b844459413410b200006490481b5400d951703003040594515040c41001c11420400d80c0c0000910000c0d1030750300001c00007240145041e01c20320780d8840c1b85041c0004103d0392250711000a9040c05c1d1304128180b03010345e40004c0c02c5101542c1c82000ca14010040d40c400c29662003104885e00c010500040601843e13001038451400380d000d5880f5011110011401ca510841e0044850740b42482105c0d1142080d1007058015000507041c02e1030a42c4940020328040001d1541540580d0000018401c1000c0700a925400124440040025080103034440303880700f80040080b403681070100080003940d0305c20400652040d4018058410b805040d09110300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 973789757 1250 973788507 973788511
    0x10f152303030f1207081605030c13080c0f061c0b030a14030a032301031202030d0504050d02070609060e04050a11070507051c020603391c06050607300305 68
    0x14041404d0300084c1815020391002886010400c650360b01140d0103120a4070a5007000d40b907079180101c1032082c113074002000398000d00076000c81002441440c200744200584c00416100840c041d80081c02007214100c501080e012209481c4440031400c4e0b220a00400e02d00b24448a02910408048800c107a651002100400c15504199018090f0450341d01401d4240d20480e101e186201311030388010004550b940c00491050308292050301d140103209108481039543c260b4056030302c1c1c0c2144c00b41101c5550100460401000c0500704a0308851514401414402c0c2241d020fa00450322000044c05103e0b880c0c0c48901c1d041c4082812940301d240a00f061991420a0300443d8021202c0049100b640d001c03070007a003108503600510491541c1d40d00519a448441016102220282840c07211600b08540a15030b25154002440c019110a074003000405504030400d081c0d1034251401c5014001a10303040102d0720410307001400c01990108140301d60304246404200102c010501c0040c00000d40c1d8190040c034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 973791007 1250 973789757 973789777
    0xb040303050a061203080604021b2409100b011b0311070902091302070515041a07030b0117070909150302041103070905121006031103010f152303030f 66
    0x200903600e650b25881141e155018141c41030340e404011000191050182d954810301c003510140c1443c0a81840c2090449003482003412900168885030071440c0404180c00590011140d00c13040781881c0741c10b1901c0c0c0e0a41032042c0042900d03800c2c00445a4000c2d154070940740390845001031141c1041c03d0081c00025100b0803407205004560001a1014041c000d42e14190401020491448034964001c2c0007507014070390480e03441c0102010b0210f0070185419041c030840c02103082110b240e1020400c0c00b1082d600822420505241c80504c44c8541d92148243c00d020038010f420741c0b10ba4450910680341e8070034560000340494180721801c6055900350f4521001c8900c2950180140f440e1000c11034554003049650500003074070030004000c5458001020507031305100c0d40c04d40f030780c003024210a02c080c0d44a9030010359070302c0c140c01645020b41c1400d01c00c040207400303940020019003200c1032001a268130b1611803001843c41e4aa962031030b03004800c200c6001524000e0850f65a403070524201085a04065403071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 973792257 1250 973791007 973791011
    0x301081006030320070504050c0306011e0504050919050a0e0709050c09060310030b0f0114030f120307021e010f0b010c0b072313180618051509040b040303 68
    0x2108008041c041c82054907419100e690558200300c040c10942c3d088501601c4441c481d031703500013842e5110341c86800d004921050540d692450608000f62448510184c010002140d1034041031000fa481802d403025075200322043e400c1910f8251080ca03515045090440a070352400b014030080504580c001003031885658107a0b00041e41e0b801c0e04504483c011214460001010080c00fa010b2810000542e4410f05845e02c1d4803126850f602d51541d01e00040368401d180c2452400103000001c0321401d820a0000118000c000c00c00c03031100c2e99503c954820389011182030001c408150024000d0000144103000d080b6201d141e17021202c5294060b0a140c0c454080c1503241110100c081d5221300c2403000d40746d410007200e4807140c540c41c4085444010005419800b000090468000d04e140da074020007107448401e003002402400c1c5450310b07440ca9940c603514001240740c200100405c100c00c0c070382d0b4030701d0324101c040002e0503564850700ba9004c400c4601003250f2008a0008020400920803034003805079009540c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 973793507 1250 973792257 973792273
    0xf03050403270e100b030a240608040501060e0c0a181205030301140307060f180f080d0816020705120f030304030f0f030c080a0f060503300712260c030108 68
    0x40c0136010f0182d4003404642c51001c000050450b5a00d400580a802d0b510311140c4840d0110004000e203400e06410100c00034083c0b105200510000340299800f5000101103a070540c200074010b40351501c5070100f8a1b042c08844130120b84040d0603407108000404041d081340e103a0b03240c0392510703984951003402280c010015422403800b440c200060801cbc01d07540b440e00c1e0b800140d0960a425210100c06800294180c10941408503008088148140007805100000d0203201c40003040070f000c0c190020315001004010990060600b079000401c030341242d4094031003a02404129085d1070810b50302c0e1a180c2c0451000000340010540c0c40350701d41c4912001c99950814600400d0000c80c00d5901e88004400090010004110301c00303101c0e8014044000d08040000749a9a11001f0030b0410522060508034008001c0409180189810805000c1c0c051110164a0503829a880c00065042480203008000f8102815030441c81e841c044226407100302036000b1190700d007503c90000241c1c400d0285551754014850 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 973794757 1250 973793507 973793521
    0x60e1c08130c05090a110a030b040b031b060703030608030a0504080d0f020312090c130c021002031603110d050a0506010f0201231005040207050109020a0f03030f03050403270e 77
    0x214001c06540c058500b44400b4645001c11080800141021106554a0f4190b1040b46e03209402003002028503203000c0f600381214810001214110120b40f030080c0c000002c12218100031701e85040d00140c0486040e5154403040c18218002d208940041200340301c00554511034940107000303042202d0042e0101c4086001c0503504968202c81001030350003580c02071026070700148d0203194542d40010440b04640d0842003540010b1201a03400c960030b014141d0301d8600c2540b031603050003800000800c0a10544c43c509100c510140071806402501c070405960300c4140720550103038000ca4000e0600340205003c0c60425581e15001000142d89a41c04100164000c400180c0103014001d040d451050020021580d80180742c0101c0c04000e0441200342642d20780804c040c0d03100c0c4064140c4501a01c000a1400c110b841407110344031058112003c0000d400380100b0009500600e5a5481c0601d85008140b588a602e401d8502103c10300d2500d80102d00d0083d20201003030780004000468816034004403858813428 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 973796007 1250 973794757 973794781
    0x15210c0301030204050105150f0304020d0b041505070306030c2102060c0606100c02030303060409020109260106080a05031c0605090711010b1c030503060a0b031f1e12060e1c08 77
    0x1000f00302ca110750a200e00308031070301089d003d1640680054001c3c40c18110b41c0c2e4880080010403030b411200040a03042001c800c4a07140711301540901c0d07600b002c000280c1152240520103042d07100e0789441e4a86000c000841e45c4c00c400784c4881142d4040c00303080d250015140c5c46600c6000480742c10707000f0f58148902811462041d009600a00e40203000b940c91a100c40c01488040c0200840c11707814400e03100c50001e1810507120391401003428018a5409000641c2d01080c00e40e402e56024410b20703844111240c0102d4008412284484032032050742ca80c1c0410040c004d005096550b0040350b0106002e13080041f500c0e000448181501101d400800a0344203000400c030006021048020349840c00b600004002402040115003085000b44194a03643e80c0c4c1d072080da00c0390300444070001058401c9841d2006d90360900d400300007501c4552001900d107400c06040c013007d0400352040d050304101d4031a1001c14801c003a80211140070365003054915059900503420481d508030707155500014002400108020710034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 973797257 1250 973796007 973796029
    0x1413060b0108010e0c03151507050609030a08010b030a29100804110d05031204032703032313030c05131514060c070608011502060615210c0301030204050105 69
    0x5804c000c46644a02c4096542908010801814800340740c41190a6907100c001c10164800c101d070364281d40c3c2c800780c0f070018285500a04140e00d15070042c400110b4840d004180c503070640d0756501040340c8035900c3d4800d0300e000d410b00c500c02c0e440f0712503060110303119a0441c4621925440007612a0b03400191203030340031200704008840107840705a150300c1e4002c652604200310482980108126802c00301c0b047c101c00c204c04402c1e94100c1c003054011401c0c601400c200d028100c01041c600160750585880c688015003400c0d03060190024080c02220072444c100512025036031106080c1d050003130b000e901c030300d0581d10b17400e07190180a01c101018014400d403c0c45a00580d40071070107030000f900710545444a00d240c2c01400208542d4040410702c5013a0b10b50a0800107400100040d54950314294586a84402055044802c100840d007000e0100305241d110002c42141c101b132906403d544d1038280010f0101d2500383c480e2000032000d1030805000c550760000d0040c40c1030364000c440810060343e9440c01c000100e154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 973798507 1250 973797257 973797269
    0x240c17071d04060302060f0409050f0405100b0607060f060906050a1404020d0617010b10050307021c03060b0a020604140c220f0203010b0a110f1e011413060b010801 72
    0x1128210741c00744000c03a03541c1c12018050320219800d501e035800102141c108000c45801140d0200c1d04108500880c01101d400c01d41c0d001415456081640b1a41c0d203940649028407003464840c0c0090041d07480303841c104c4600942100701048414050001c4001400491040c51407560600c0400306d69031410075012001c0700d050b0b11849038065080d800b0b00000c0e4200359040506070b5919500090070f11120080c090f00d564000d4000100e8031020802c11848031036400b521010000700f4410004020780008020940400f1560704540e02220094228094100341d04500034400300841c8541c4281d4002424901842c8141a210152460002420780e42c2c130904100359032112141e2180e800c070785c02421031111a040744075808241d01d00518480d505a90003a0301c01030013007030000341200c07250703510114501507900100042d12003a03030350300da0356640d400b400c4076058980c14281d186608024000d5100c0e1000c14104101d6680700d140c15400d0110180f11081c055500c01d0030200780740140c0d03220f444154143d5075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 973799757 1250 973798507 973798517
    0x1412072f160b071511130806101805040203120d0c0207083409020a0e0f1806191706070224010b071b0b0c0c09060913240c1707 56
    0xc3c2c2c0e4641d40075260f00300e00c00c50320840d6103074102c1c8481c101c500010804401001d0750070b1005407512860300d29206e03004001c000307074501c1d61106103c04c01200c01807010140c85050082220344940c00044e0a00d0904031014940340000110001e0724503190300280507001150302949c0d5020350ba00010340d107644c4200c0c48200b850000d2a0700c0310380c40d01c0070705e07400d414041064405032015840300507400c100d9002c5010540851110720112640381381c00b1100003102001500d403400c4c032032110b21b80306080417400b03000c1c54030402407092501ca801402c003030f640008040c944074411182480030b007100d880d020309540490050285203c07800c5d2400326404030b02402a12001c1000d050381c81c10101c45683e8105d110101c0c0e0b010303409240d0010310a0902c020601803c2d00e003191907a1208582101c620301140d40036000c0c09110340c8c0d010814980c0d190110540d0140c160007051a88120501c1c2c841c1652a6059264040c0e510380c55130034090800310341c4014000002c9031540e0010320404105102404012145036000403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 973801007 1250 973799757 973799767
    0x60a060c05030d09080f0a02161401020a030806060d02030c0a030b030d1407171305031009080d0509070e090105070e090402061e0409060308070b071412072f160b 71
    0x89032a84100c0c4603502481170a418444d01d00e01304522503000e0303038402005910001e4480101010f00c5070081c018a8ad000a03491131003d00b50010303480301d21119016041c420ba210000b600d5803a813408540151000084c02c654078680109109000d4010b16904070020385007416015403401c000031080d40303480043c0c80b81405203510844031156a0711130b000032900c14030000c9e0f4050707d8100e140007424002a4a0b0307440c1101300c0c10842414a05078140c2060f220050901c60000c0200e4070801c00c50300e106102c1c03900410b1607681c0c810701c1ea1070110284e21a62840010b0700c2040307000e1006502040c0242010750341c2801c0001400c0800c503c400080e90041d40c080410880000c600809060b6070101401100c41a400c2558607001c103c2143d455901c00c3c0d40c4c444001a012041020402d410790384110a810030040022140e140e80041d400317000080300302d00e4140f40205c0e49160003101d050304000b00115100d40480c0300440c02400c1c0e10201a14032034a803003459484600d402801682006440e0200d00641c242 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 973802257 1250 973801007 973801027
    0xc1e07060506270705072924040207050304050a0b0a030b0f0109090b0a030b090718050108030f1b010501090905010c0e060f070201110d110f03070f0201081518060a060c0503 76
    0x380078007130210300034441d04000700303000155511030040340030300e040d030a441e90700019410003e0321450041600c102210350b4803299204621410110045e0507069400684500203032604602e544142c0d000540e000c64141000540300ca03521000304407144483d41c09000034869070042c0203040c0d42c120719060200b0000c24080c0058111944110705003907006001c00350b000e03602e03120720543e141c1c03e41d030554454101341c005000e40700c0b2000080c1c0441c251500100301c1c641c5080314040d200d0041410a0100b02c0002801915032010b020b0f1050324207000400070071a81d651450550020120020122481c2d401e00c207900d15000c0c02800d080040801c080e149500e800c411122080117580021000ca0600810b0880000007090070002c026039400b81e500d8005140200c0d0030304502e042038441008070706910400c9a05d001401040c480d00031254203091100d0980c69110302d100844c24200060380c3c00144c1a5a246c92000140c2010f0b0b009003c1610b15000054591000711190078a010018201c1c0d4001c000c01c2d00b007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 973803507 1250 973802257 973802329
    0xb1f0315020d020d09050102031f030512030601110f0105100527090123060415030c0e04150507120606230a111501090b120d080c1e07060506 62
    0x90080800001440c3c0344ca842d91850840e580841d0a480c20303035010080041a001070411041c441c941142a2891140f65558603a07485039000d0040c8219100270012403842d0340a00000144d4042c101c040d5405102030070f041078024181268800c1c00d00f60108130005560503c4500b150001c100c0500303140728150941c400303a02008010b405108207642c0c400d8822281c41880c8000221080d0580940d002418600204002c4d030b00304810600140d0a0940100001040c02d070400701128020300c4500d503265164204a1450540c41d183c80602c14101030404c91400c2d80a06825000100c10908001040d2555802c5401d0701c41c182101c010340c40d040000c000200304143c040c01c01c0143c14505000a01000c440403420400004114114807510b100144007a42c05405020207040003a140e000d041580c45620507070301c5844621b09024403090a02041e4140d00310030441e580c8030301120300380f02d80940e040594100b0b54019007050300d14a2600c00450b25514200d800c040c9110301c06031030104449189140880 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 973804757 1250 973803507 973803517
    0x4061d06190f11190c08061e04081207050702090f22020f04020406120506040902090403031503020627030f03120c090d140c101d060f070b1f031502 65
    0x100380500580c1802d03c265040203581048070040600074403008083c0341900485406400548054114100f004100552491000010b43c40f00781c0c00000c540b214101380c1218441c14000b0346016030b614041000c0d0982103001004002d01c2a14440c4041d43c642407907034900039059070b0010124001d4203601f0070704507001c000418014001421060580b0849001500700c0c7d01c581d2185010900c004103026046039144242c41e80039030243c600307100d5061160b00040f00d540c0010001000d240c0d84143e9003a6940c40031003100e02071a070107003007283c2d140c60088900342584551103412503010101c2820585c107003000b0820546c0904200025030074020b007100c29400c0038000070a052a00403080c4400e4046540300060300030500d00908011711a400c00f00c6520b0b0500d0b8000c10f810703000c3c0b02c054414036045603000340c41d6540d920813009821650b160141c0050300300d1080200740c500c0d03d031010501c0400c0c40104001d040c090b0303001045d20000409a601c281804511501c8060310b1188101201c550140151300200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 973806007 1250 973804757 973804787
    0x20a0215102603030106020a03090605030c07030507110301090506101202030a122304030c1508060906040612080903161a0a1e0306060905040b090411060f04061d0619 73
    0x10110340c1c0000c0403c0c038681099000c100103912490060b42415003114021024183c5881c02d1480d62405c800032292030300c1029002002c101c00016036100780900481989001c5030024003e010008442c10840d581d100103461883c11032020110009502c249402110710b180c0c0c0c0a03002d0400421a52075001e60141508402d6040c0440c0040701450300b41130501c3c03c0e61001c260008a501d650071404c00440d140d00a401c000e08a03400c02003058074440d001200545d01c04800c480c1d81086503103420204000d0003042e4440c48195449200ca0820000c0c110054503000600350b00301c5107407003503000040c01d140c0d406106d04011148a01a86408050118000c280c4545141440306038016070180000a00c1d007039400680c0025665541032003c0307980403810308000c141c02c45040c490a150000010b2003204090402810b8031520203101103a80c8400d42a034020744031803400c3c6038031595100d201030000444c2d60100c07058401d0300188101a442e001c415900e020050040040c00340000c10000c0d05c00d00c0010a402d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 973807257 1250 973806007 973806059
    0x1003060e0919150b0d0b04031e0e040b01140f0c0d0306050603160c0c060c17030c0d151214010e0303070806090403090e0a1a030c012c090a020a021510 66
    0x5003209480d0b042c1644100e074802d000507460b525081c20000d0454054204412032780c0f00c506040b01c12158000310610303a80e40e089400051050300c61005807a10345403040740e40c200e0400031500c1403850042d6030180842e4002030b0159070240446040803011500c486c003d03170b60300c84002c0c00881d107046401c403841002d0300058200045c4038074560301d40214074500c903030040c00040c0001404d0001c02941070041a1809000710205095090001c001c1e00d043c00768a605480c81d070380c0c500b1038020544124075010000c0581011400b400c14160401100c012420342c0440541c1d0309101000ba00680b001044a01c54201540c4000c000d8840b501048040c080161064003002005580810082c00c3c40820038010300c03241070000303071035140009400d4102824540c15440317a001036004070f5259800c2035404140c945040c18007100e91142c030084c401d14580e50070f140f40c0c00c100d24004211401c2d207140d006200c408000d8085030360203e80d0f00c840894044044440511117040d4600801c00350000c608018805803412004c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 973808507 1250 973807257 973807271
    0x80706091403060f09070e0f0621120726040e090a11060306010e130f0b0a03121110061202090606070c06210e01090209070c110616021003060e091915 66
    0x2147c5000360640b111800601488240324980c07400e2151044c10010402d0943c40303010780b00000c02d881d0700340350100805510300040c45c0010404580c5100702c00041d18984480348850241c40c0d10015081805840c10701f90010011480b000d500040c0b0312440d56010448071007480c1c40c101800050303000074001d50306216141100d84515a078a0030300100341c9224460000360b11a032030255030300751880303c56824010316450301d0501c0812031900201c0085052420300c200c1c0b80d2901540c2c0c138902403524070980a02441c0c02004511203484a0020000c40d0085070181c0300e940398030b0100030a034030400300c0080c9038104904040080600400c45000942c01c5c118440b0390b00c021411007241503c41020412207035955484c10b0030704501c1d04549031034114080c1c1c5082d070b0a450315940d5040c09004920200d07171003080080b404c00407410800e000000c4040d400751100b42c40d251210800b901811240c054240c2c4c3c13500a01c00a5031644002807040f0484201300441e500c00101502e44c645601c82006c4030111081c0c41d115 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 973809757 1250 973808507 973808519
    0x12051305060d092010050c060a0207030e0303070525060516060f091505071809180204020f19110312040c080613050d02032a1501080706091403060f0907 67
    0x407010b40c00c50007502144604d00051007005440800700101320306002d0280014403100d20002003140d4840b20f40034005030354148909017034903001c403001030a903818480054103c041041c0401c6a070851000c404614402d015205c0750b0501d02c000501070200001c109000551443d0098211107440d9401410f00165240300c44110340c05480c0195000c2e40c58440c10380198072102482d209050740300856142c140329104512800b0300c210301d420300c03441101d2512085110940044a00812000d550003801190355442c903070400c0506420101c2840c8044114048010038a07018181c1400011003100241d46000e0031944031017801c840141c025201c0208291010511400400000340614109030040328510810b180c02858111f401500c0350171504148080071008241410503c0958248440f00302c0603d00310050a1808100c0791440400400b660000a40500040381c020140c49195403010291511135403170413030385c92952582035015030148002074070b00525180030a401c030025205407000d01d03036914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 973811007 1250 973809757 973809773
    0x314040b311502040e0402060d020d09110108130506190608101512020d030e041404031107090212011511060a061820090406051c12051305060d09 64
    0x100c1400300304801d0700c51001d000480c415491980340820341507240ca41040d40075501204081c2009009a4000c2070124003881207805841d10040511003c0004c0d01345030034803822200002400340d0100d40c103a800b041803240700500350604290004000d0100c1e45400391003000e17800610300b060514590b580c0001c0b91049007030000041d0180e2565010a000100c0d01103200844205c0d0300250650012050309030058980810b400841ba80508160b40070364079100208000c0e01007030104182c000f009008000816401c192881110204c60003182c10881d19100032104a115039042401d400c3c0307804004101022030041e540c58488013526040d1001c00b03010b103107a031404e03c06031000350445865050510601603100380601d203403c130000c02803000c9103502c1c0b280030701c2012020b0001140b5400007026451a1590b40103000100b80181c00b4500a0300452014011406000c0381141c411141e8003a060400c0e10031410398048000c400d461046072494502044080c0e402813009070741d020b460350a0300300807616003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 973812257 1250 973811007 973811071
    0x21e0a03080f04170601060c060506012604030e0613051513060302030912043507031a090309011d13180c080d09060c0c080f1b010314040b 61
    0x302800c0e584503414980782d0070b40108000310b03610304c603404100104180c50b441100c0e1109280c100b0000640303a103a0b1030049906503694010404240c1940c6e04015032808000780003807081d0b010341d03911046d46450404100241c0310350410307020f840b0346c0c00f10700340110b1a081d50341c0c505d03402d0004d000c00d260810140804d001c11150f58402c00204e80d0100c208130446000748142040405803820040c9850300780300c001c2030f101800c4402400b05020140704d450185100c00808000550007600f02c510641e034070302d0b1031841c040145035400d0402d6403038004200312550000c190740364814144c40d050315024008042080910544070156405040d24455a42415443c070a02c00c1c0300a4920080b24070040501b4864030a030000d500000c00c651205222041c0716034010200c0c0150f034142d24280314404410f04205141506a81208240d03000d1201000c411040000350380c0742195014402040c001a090300540807191000305441e0f2854141001400164440c4c0041d584902441c0c6448045440e03009240440101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 973813507 1250 973812257 973812277
    0x616170309070602150a0b0f1f02101109100507060c0903050606100e1306080105011203110a0b060d02010c0b070503010612270f051005010e09010207021e0a0308 71
    0x4000240300e45901d09011140c09414540010318501c0464102400003000050210b510140da0302020a0b00c0c1d03941d030005840720200203021102c00c0906603100450101803500103030162080342000380719001280620040b6424240105080c09216014001043c91840d140010840e04010b61800143c5911401880c0b890035030301c0807855419403421710710b40480540201d01c90480100e02c251403982c40714608014240c26100301a1100c0740c2012940503040c00c1d0440d034200c1d400c007400070a010002480381c0710a103009075074115892002c5500c2584480c0d000c0c001414480c04007000961504040e030940c040c3e540306150802d03822000ea15004413517141078403a940001d1000004201c155805450100324100070720081204003401300802c1040b140e80d03500700b040301540900607014440b042070000e0f107180d004416100900d800060303210003000240180c078030300c280c03007004945c1200c8140b081d50600340d806019500f00c0700e803210aa07165011814039803a485000450040006a43c0c0006030000d200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 973814757 1250 973813507 973813553
    0x30c0f030303051f1a0d110d0b061312020604050904030c03030506010908250b0d1e0501080303180f0d020a0c1403060c03151f120c0e0616 61
    0x400c0d460014140d94018000000240020800500c9040002e880c0c500702c0d00355107198422012005054101401085114040246032802441e5035003404d60060500d0000014100b100303c40310001c0098034080d4104120804003c080107002c86000541c207091002d000805190410380e40701c002490b2885c0449040b00013a4007500c21104050300340c0aa590401c80900b0020f00983c180941c565440e000e8141300c000c540458035400708035000c1d51031400003420500b1040756540106410401c068040c60200881d010090103010b422404140b155038181c41e207507000386240d0703181e4034443c4c61401816403001009000e54041c02000c24410803071002c1703480c0039402418010f64581804141074600e5446040f54040d44045002281e0740441d00c40e031310249070b81d00e1944036100c00d00d40f480754622070040f040d0490707034180c0c01104410703589401c22080da0080d642d680104c85400740d42001e0b0f5410840213404291041d864001070b2502c807000d03048001d80b44000d51142603123a00c804104a10885030050410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 973816007 1250 973814757 973814759
    0x603030403080a0314060406080a17160c08060708010b0a050c0c120c1f050912070503060c0c0105071d010c030e04020f033408220803190506060904090c030c0f 70
    0x201ca50f03022154046c1003104c00700a00d40c40c1c00b22a070b4a238030701750f80d00034110f820380d2040700200c2c2040004d4840b022006400301070f500c0620700e803662018003140604a020720903500040c500502c641c880c80e043c0c5050012550802031020815250380d0860075441e249030141880004d001e07215541d0701600c0320802d40003400310058843c00e0150390308140c0c0d0380980c1c0022048a800303200346c10030101d6040c60010f4500c0741c03190309920b0046080094641142ea41405910f0038007000c00000c50180c100c502e401c2008010545030796400380d0382c0707031940400e401e1032640500460740c05602451144034500d019050802c401c0d05600009422a4400d00301640c07010070120a005c54182907a41c1d81031034a000c1c3c0303803441c4080a07031030074010f044050071018020041f410b40011148400c00079080000110110329840c0b01e0214503158985800c22110079480130014001500100030718011240101c0011b0115480c10469905020103021480001d8a1304407901c0d4000001801c4010600020614200c80361485 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 973817257 1250 973816007 973816031
    0x30504061b05011109040f111213050304080d0e0108040309350d1404060909050c0702040e060403030e0706080414150a060504060b09090610021e010e0d0915080603030403080a03 78
    0x44403008000d4025034500000344520184140448040300270039410003c4641e54003003414061122208020041e000119001401110000305864006c0440d01c610900c00c0e08200112241c0b00d0489024000468a620070440694030030f000101510035007060701001450364a81080036415019580802d50050200401255002e2006403000c81045442c5240c18071701403006007140b205000e41814180d03a078000c2255041038004480b04598061b206102c280c4130344c040583c58080444003940403908040c5810746c623060108280080d50b901d600e4400c0c480e1101e0310380a00400741c500d403021651044900d00c2c3d203203d1510480c5449501c51860128060741400d052100795411548260a03109051101c80966618001020351241d026500c006c000c40e017203501240303131444040e4a504101070010b820001104103400c00c0701c903010000100e420f4141c044008407510a0ba500ca4545112000d1503003500782446003030a940c000c0001800c40b410076450b9140c5174010ba028103031440c0429515060746400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 973818507 1250 973817257 973817261
    0x71104050402012c030f0a0b0f0919080702090c030121050f01090803180c13090516060302070204201c1b0305040b090d1d0102010f090b040519030504061b0501110904 73
    0x4181002c0d0191094410035550723100d0011011786078902801d406000076011714010130603d100d120403941c009a0603201c3c6d0a1010a591110340164002c4030030800090442c0d541c6000c0302e040310940303a0001c50030589001e00d1041804920021500c2e4022070a001c0b4404809005958880b0700400d05240d8034100a0070907405200303c04858281d0b508188030003103444d0341d0030480c0c0720303010905c0c1c1002c5842605898440c1c1010805440c4132210400d800000c150340c2c2e80b5501030121740d84207580c100030101581c0c030b165600010950324800c2c003102c01c0000c1c04c48030010601800803444048408203404d460322200c400000c6540c000080026540c104200c20f0100480501d5017251501000e40041418140014040154000d00300f4000034220700309aa164800d5104400c1050000780c00c020b0310300c0606d441904007106803000e64007403152020442d108510b500d00184d01035411788415180034503081d81681d41002140c00190003100c4041d2243c0480e20038042c0805031160b0072280c0791346003800740c10401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 973819757 1250 973818507 973818523
    0x1002011e0b031e10051503010b0603091009020a0b0a02030d1b0801030602130b071217070801231c0203070f1815120b060114071104050402012c03 64
    0x1041c0c00d041c00c25005440c04141010741e8000310564000b51034002500515201492103007495551400013001b0400100b0044101215803c400a2144e105441e007001709074002550512415040f401e40e01040038204e03070004015138070140100341e00d5a030310b10090405800010842c40542c10015104c8010b40c11446014080d1990208001055512440040126505000050280380c1c000780f40088058070004810003400c040b030b85a0303510300c15481c00b2507001461280060116988290101440904207000e51160707c03207644800d410b0f80781c0207050134019040744241c802d80911501c0c0700140e8440b54801c0114803602c008200c1d00861501c18149030040546c070500c1c050aa0f0b00c0300344840f60030804001480c4408501c0450701a54951120032241305950100302d85100900c00001005003400f0120700c204000d8031101c40394805020100005d10032300400a0054000103d030b041c00b4507155110942042c010b2610b031101840e00c401c150802d036100c2c280c40c4404000400300c90014901081428 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 973821007 1250 973819757 973819811
    0x2070b1b150c030f1b09040b0a0f031109010e010803032e091a0405093301080d0909050606160f171b0a02011b0807060207061a033009100201 62
    0x13104000402c9040f200c5d900070400b1080c41140c941c000550300741d4407060484090941066440c1151307a07a8034140e05100c58034100f2600811100300002030961100108504842e00304010314555030310120101c058410040380f036120f5064006c101007500d14013400c820003400703e40000068071400c00c5012806113000d1403801c0c2c40303503080000300200d1800104400c141e014100c884a0281c42007840c0c40780402884141000c02968407500001d50a04000f82034286001c45480d04000207840d01c84040694800312440c1e9000342c030400146406810f1101e5010b0400c2c00b8580c4400e00902569444054865800002c5c15046011070030700d10201e807000740402e00e19803001c002c2c50020340d50350028003040191004030300313140c005010083c1480030320740880318241d03404a01199225214508036004103008542c81100241d0b800310b0009034140000c0a4500c11040240755902c000c040000b40b0000007072800006500b181884640c2d443d8403207540c0384d2071b00b8555030004030f02e0741e00d07c0c16800c0d00d07400401d00390 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 973822257 1250 973821007 973821031
    0xf0306030f07030512070f0b0405011d010504020609010507050c13060501020f01200703090305060c030f18120c0118150b180604022b0e070602070b1b150c030f 70
    0xf0000100d001800c20810401c01c031440e6121141e600788120080100305000e000d103141d06003004200601035006500380b0350f01c5080120b04c0c0c0d003a904120b088450854000f504244108205041907002d400501460780c8211b04469240c44000302060f03103038034403100c2d003000035403641414011903030144241c00b1604071080003044803270f0b107413460120f0f401a140030001a034100000c0c14018944200303181c0022396081800c444060030500c01348800e5038801c03281c0502c02c1c00558041100341c0c0b5002d5411401c45030320b400030086000036802454140d0f102d00c45500d03142d9a1084104030000c591280021500e0081410010b000c00075a841d00540f410140001c3c8644d0103004010000d541103440550450004d541c0141c031740e40741c00001080044140051003040c00c0ca50713000c200314001c6811140201e0400800d5902c1c060780d4040c00c2c3e0b5907181c1030003141c0350040240302d926111000c04400c072000c0c1c16070b50111403003e03800a034000c2c92200b0a6440360f481c1840082000942c0440e030034001d401100b60000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 973823507 1250 973822257 973822259
    0x15071b03140115030807050307020a12061d0a12030b0d030c0606090506030703080a0c020409061a220b1504062c0d0f030905040219020606040c0f0f050f0f0306030f07 73
    0x245103003c0f0281e00004050301008500c60040c00001c1094810321030b0301400741c80c0b84070b0301c44078403030001c1990801c12a0503a05148240e008450b0b044060b10105080c50001d100340d044990b1061105400c0e16042410140e5410200c015651424000743ca000d01a8640c1b44420307406007006002c1d110320b500309404981c01c1c80e0900030f480e100000e20404598221004980360140d8580c125200d107014140030394000d060101c1da000f0f012080d0b10003140c24a0505561000403030480034840f02c6410640803005060941c060403011580325080506d91200c01403200394604005125810710b81c0164120700c000580c40300c05d0b00c2400840d0f05103800c040400041c1d1100352541c1e50005269070f1f606a00083c9843c1c8001c0b076110030540510000c03005450000c0095461b5a40a081c40c0240c0f9040380048005216801c08981c05080c503124075280f04043c0c1e9501504000203210036281c050351091440b080080401480012009034030240c002c5290800059540342411020545401d0008407280325640201c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 973824757 1250 973823507 973823531
    0x331030206010621091a06010309230a0506090d020d0507080414010e0a08011517060c072109150314010501120b0603010b030105150c030915071b031401 67
    0x380c4581158190329207401d044e00340301159550003403404551118141485080c60822800c60700318a88005800710b8400346903590340044095030311010018080d090740c22407030000340080741e940300d40c41d912800c100c5562501a65a040c9811400c0b5043c0341690003010b201000664144420800d41c500d91600c0703820030120351a00c04140c8034900c01c142c0b60010f0390344e08100c00e9004101e094542c00c002810550b030f00d42d447c50910301a010b12002a43c2c8411084408500201c14800741c1e0344e1010540020700081d580c010842e0000d07072160b07000380c850301d046060b6103013440000d1040305000001503403001441880c00902544c02005480c0743c0342450300b4605c1c0e0340c551554640c480b0341140c86c2482d080e1034214230100100024842901c920341c01c00b00000000c1b17001c0003144019412100c041d22800c0110501e5402503446016000d00c0307035400c3d0402c00a082d40740c501602c1d008200003000c0c5510b4035000c01c40da03c00c0000201100707400f02e802e0484504100f0301c0300700c2c1078040754010310100034810100890 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 973826007 1250 973824757 973824763
    0x13060e1602030a03020d0608030a090303020f0d02210f03010f060207091a0108041b030c0806182a0d03030504060506060301060f080c040b04060206090c061e0d0e010203310302 77
    0x8403c180c01c0550108141c440709000d5002103009103108400d03070307640c0c54010300001d2140509000542c007500c1007a42e244040c890000c0d60403aa90029400340c1001480032000d0070011200c7c1c10181004e00b0184007031011076201c480214000d00100004c0421a4035042020b42000701c01e500511b616450b0481c0300400c00d034203c440c50489042480c280c05c075680d031448d14508116821105000300c105030580841000719503001034054070740c04400c40d02e140e0b4594442e289018000e6001c407109800030204800c0c0040c645580e001858680d41000e5004c00340400400c40f81d1100742c10a40000c2d8807141800700f400054490250802d07400d98000e071546d8103201002e840c0010064201042180700e00001e0b4003401c0c01001e4a000d400e1340c003000ea41c4d41f5682e104c0250b1340c22058401176090700507908840c0c1180790010455a140d10884004500c0d034401c0c03d044105504036a0604e00416100d40740910310050a02c019841100000580e2003c4070b681681065000a01e00c0b42c00d0007143d40c0f001d141c021035000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 973827257 1250 973826007 973826017
    0x5030a0b0a08060c1803060105010207380a200d1407050609060f0a0207230a050106090f0b030c2b05070f180203132013060e160203 58
    0x80400440c9800402020402400465004030158021002404500743e6840020310020058000c40c184a046600416403030701003c1c4a00b0b40942d00881013004002d10060180304e000550030600c08615180100c0c45414503142101032a081d90000380400d420764000701c44a0060025000d0410364601c0b80f0240356546038046200801e014a020f0040c01b03020042c8202d03907215900c03906030f40c000d00f022942e0b1651060103445941c00d00031040001000341050f442501c0046802c54200720311341240c0354105018106c806021441405180b0481c40410703000d000740401410900000122100d0b4888040202e40040d041913220343c0210300302d0800b5607108648407050000011042460300940c00304544010802e100050450141c4680040e0800c5050341400403a00015400c0c01007050a04003642248002c031605901d107503410038110b000c1a4949815046007176a00700350703074503200c890f000904404000400811a00e40b16442880488500d60300c00780c014940310405015400c030a0301c041d41b03038055 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 973828507 1250 973827257 973827271
    0x501050a0c260a111314010c0507140109091a0901060e06031b09090705031605190809162403090807150b0a091a10090512010608010c1106060303030105010503 70
    0xc84000f203641c901595100b00e5181103d0400700e42e0300c1c21040720081104110b482010112210342c0107201a9500030103044104a03444000fa100c503a042840c0e00b0300780e0303003884019410411083ea02040c50f00803071180440720380000004240044c107070010030110301d105810041c01c000c075004284c05280c65080580390401c40c00c460784140044003050702ca089028101c10300354080b00c078400340204c0c141c01c50010750142c03142c114812040030721000190f640d481508650344002e040401c26001241c03050030800d40104004054902110203020801a1500310742c111080b40c48180305103504100b080b0804a0040307440303040c24482940d071a114603e4501039200041d010429031560107a40700c019600a45403050002c0c4058407490300c505001005028030080401c01c3c41200b0320210300d07445c00103000da8400021703076201040f1606001c144143e84201c5921081150f403508030115090201380681c511402c0140e40f5140507445045125242840141409009030000c00040c825030340e104040700d41c0001c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 973829757 1250 973828507 973828577
    0xb0d110d05090f0c130f020903010903091a0f0702040e01110310050901050d05060105060304050a050d0c02040b0301050402060f0f04031e1221020f1c0b153c0301030501050a0c 77
    0x500c6c01100340a0f1203000021549546040143d40815400141d15803d451600ca544074501000140c42c010b035200d04149201c2640d428401c410052501d43c01054641c2030450000c10100d80c0070000d078019810642e41001200c0702c41c7c8040c0300600388040e01e0781c01041c0032107a4aa14010759207400d521080c040c0191405084004005000e000007040719560b42c80d0312074101e620855000c907004240d06040281244100d0910386c0c6c804c503034901401241c1c0681d800415040c5804148446c1c00055071010210700340100d0203000000118921208403803c070004c1418800d030151080ca011125581030080c0c03202408588a110b000d220034042000ca0302e04c8882000507501d0040c00014501400303042038640c100c00e119000c0400c102c0c1d40ea002844050420746041c41307400c482e50120100741c011171080f03134020400c0300700381c400c4c1610540845900f000d015012040c031140b01d00c1142c410f50310980003502c080c3c1d101c5040c06940c807254070071021031346c40178684000c104000e00e413907044281d007040000030252 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 973831007 1250 973829757 973829771
    0x1020312060108100b0a051305010e01020c0f15040b0301210c050d0f15150f030308060d020402090d12020c090c070f1103030d14090d05040b0d110d05090f0c13 70
    0xc40c8030303400c24050200e008041d0b8550088046c0140340e513001061802c51030003145400a01c1e940a6440f034540ea40058025090054002003409411039150816590025010000b0840c2c417a50f4001000a0080d111107241e80c1d41c14401940030017032129415103040021100000b0214007403418142c252142110307194440001800e180c80c0c10082c400014200310713000c1051000304003055100401d662038a280303020030107640d80c42c45242e880581c803020b0041910840001e412b032400d140402c02d494402040141020640000304403803828030300d401c0b070300c04a00f4000540f100d0380400034039a99030382c1100d4180ba9840c0ca44010803260060890041510750703240340e007004000580401b205a81c402408603034441d24282c0c04000600b03c2e40317401c0110340803401c0c0031424544001c0783c401101c2c0b4450310781c2807405182120090042c0c1c44030b142880b510f80c0d0b5841c0d548948501c1d500818180c4600700e0003003064109503500c60b0400c0c600744030b146820703404035805552641340c0368425250300c04c400000203008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 973832257 1250 973831007 973831021
    0x303060918050d03091704060c03080106030c0203090909070e0115080609040f110301200706050109050702071e0e180105072a170708120c070f021005120a0c0e01020312060108 77
    0x3d03080e1b840b003120850300407401240c6103902000104019009640d00c030707c0c1e6680d444060b0200e03941003043c2001038108000240e142d080c01d4009039008900c100032944942d980300745505200400380c101c1d107010754180308012200c50f8880303240c85d0414011200c250315810995104000a00d04800007086030400200d04401603030f080d404201150000c80c1800c5080c88103100c0e10400303521501003215440e280c0800860642102d1003143d11448107500100202030810302984d0340300c403201480c07140e425484034000c50b803821841000c0e0b0040e510500304108121805034000d003507035030003000602048488000701d105115440a11101104290742c41c1030f010f006800c040140d08040810103080c0307540081d20380b04001d5024020216540e03a017144100c40d480e0400c040d0041c6c815080c000d840e50031312030840400352400e8070140140500380d04007a807910302d1103101c000f108001100c0c500348960380c410110508540201803054516024400703540b070541078455082c24000040c18080c10041d01e540001e540e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 973833507 1250 973832257 973832273
    0x20901082d0a0e1c1103070b0c0309160b0319021602091f080d0905010908070b18090403020d110102280219050307020415060c0b0907050d0303060918050d0309 70
    0xa50380e0a6410b44007002456113000d646400b805250030000f41443c884407000b0080841502c40d00d980c4450031302e510b41c58411112555800140c080f0101e401060305c004956400700d4282c20050000803070043d1a460540440c000802c419000124098010030000072800d11407401d0250791a030480301070303007251928201c40407801c007043c2080d04501e10003200440d14200020b4404030801c0aa030310030420a8a4000444400c4054031545106522100d0184010030700280581802361070b01400450312a07031440014440c12017907905034056086940480c0701aa4042c15091204090100031341c82d003c00b0541030902c540c507841701c4070120b245540b65512480d10a1100f5055041301a94407500004181051500c0743d0149504a10840c43d068820612208401844044071004d4482c041140101d40b238544200b040186086424040c2107404902c990b07a030f14811100d80c0c0280c3c2d000694908042c0356030102c0d1680d84814640f00701240c5c00c90001940050400b95044107490085207200c0e051a0501c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 973834757 1250 973833507 973833521
    0x40e061305240a050a0f0606020c040608071a0309010b100e100806010e1201020f2106040612110315071227020121110304230c0f06040509010306020901082d0a 70
    0x12114100034000235001e50009003049410012202000312566600c85203640384441d104a0001851920003000020020000703035a0020340c4900104110609000282c4c128408100b200e0201c0c441000c0c54110b070422a07040d4403141118101403c4a04002002801c0000703c0300741144528540c1c000c041800f070302901070b1407182111582c02070311030403001d001c2c0b0000001420900b05d11b0b4248030000d07065251078005c007411144481002c5c0b290134260342701c8102800008000c02d40500c921030700b400303040c402601a60700c00c6080e03a82e4485804810311100e01070700d80c0c9030025566060740000c000445071004503090095542420031500d0340d04641d111105081030a4010654a454840c0000a071585a00114031451040080e0080082c1d014040d5001c100d00014118041d4050b0b01300080c0c034240481c01426000004100070b08040e964400502d084009070412140e103034010503000355a581101e01039030007800d80c1c0909000300049030026101000a401510802d980420108004844640c0a11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 973836007 1250 973834757 973834781
    0x901020a150506010f0f09052e02060a0e1c08091e0a2901031202030d05040507080c061c18050f0c031006050906090402040e061305240a050a 62
    0x7210300401510108000c040482c0d6540c04aa039405c0118907451051a110414422070b4403001c04032424070082c000907480385c41032130101a1081d4100b040c202d140000e46003402e03d455001340140d01d024940b050503107450b12071940c190343c06405030441c41c40000b2920307400c9022501d40b40f08a56101140c051519000701e01420180c5c001403c50810300101091118107140504403442a800075000b4001c5860003070400162032900c69001400000c0c1e01003400d060020b16881204d040480f40c0c0e6120703086803c00e40d411221540605002c005205e4103010105805a0441c0c596040c004003400901d590a4410076140c0c1c4c00d562882d86106082c8210400201d440d00b00e001c44104500134030440d6611100500018403d2040d030940c4821421035001d81816600080d00041c1c2035140c4105200d000c22001d0000c990050b103e00c454400c0d01c8007007140724070841d070300300c19521116007600f0b045050080310302c0c21040d2240000c90300040b083e4018465500b25a050800080b40d035a00001e443c010000201e642c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 973837257 1250 973836007 973836023
    0x301112709150108100506030a09050f1603120242130c0504050601050405040e030930030304030e090403021e01060603050a0603020a0506030a20071a040b06060901020a 74
    0xc4000720107030280003403440501313803100d021680b2161702201d099001846110341c8940e040000a403d03809a4001d2a4403a2050086a0b842111440418203200894004040e140d0a004040043c06181c000b6404441c0766400640812405045140050708480c070091010611500b141120030f90300c254080900d14845110186500302002c000142034180c900a640d480400000440c2d2841c0038400c81f800341d035058603124501440c0100340000fa0000c48840f036050300061250301401e40f1444080401d811002402421403800c103c404a1000c558180c0420150300034010840080d4021103043c80710601218070b04483e0f075603450704a00c5c004560740741940c81946845031200001c2c4c150840381c2a951a9201130207256a480c2c808011901a0320000c1c1d407045504008101d2420b0180003035030092411440406e0b02e400b1480312070905030b141c101c2006040b80010f030703400512250074140300107a0248a18050181407139102c410b5000c0700541442e1281e40001100802a8000c0001039099540030f845 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 973838507 1250 973837257 973837261
    0x516122613020d2906011101050f0a110f070303021905070c09050415090c06020f03070503030411061312020414101a071e03090e0702030307030504030c0525050301112709 75
    0x48400558150394160101d0360309420b10b1f10104040c015903200e041841041d0308107545601c0c0c440702070a40d0040311003090608000001c3d210f20039000600d40c7d03c1c080d07103000d640e403016103410030381c0fa1907100c5803030b02002400d1001c00001858181060122540ea000c0811141c40f142048420b1007441072107030400780e20b05102c080810003428008412200c05030251100d145d112100d5a40740c4c40744030380043c155002000002c000401226107003041800c003500301ca041c5000109296110b4100e074103e0300742d281c0d4003d1034004529080c0900ba10301048580c2d0180d81c3d04006010050b034902c240125170085207003101c0307003d9099809090b1806240c020b03441341580402448034860f42a08900290001500c51070301140d040000c0620502030348083e07000354a940d039402c0c001c40080c08060300480c1041071103030301c80000c20b000b00701e03035021800d202c010030706413007000c1552500c0480716a000714002e0741018408042990080152001c03e0001401c200f1a400d07142a8a4010020035145a42c40290241 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 973839757 1250 973838507 973838573
    0x302090303180a0504022107090806010f0905060d0201120b0609060d1b020a0503070605090703120305060f0109080703020618041d100216030516122613020d 69
    0x25080640207001c3d90309441c0c80c0d855038144001d03880b0701c10703191191ba403d06c1240342e02407441140e03190740a601031908948854503000310504019080e40601c144054601c0c06200c002540e101e00340d00a102100c80950070f04944d40041c0c000442d2a05210361260340342e0604a00b13484400880e6241400103051030b03501d4040c008104024501c000110078040c030101900020680006014200260480000c6007880e582d6500d5801070032000f84006607038014201c0020000d030340c100550309080103a407008145403800c201408400d07445850400d0400070a041e04020300348020808105494040c1c0c0c8050b50f8896402c0749102c40e40c420141d140c1c1085c9082110007407a140e0600e80512940900241c404410100d004403040c1e000d0f0320404940c50b00070740141d40000380030700010410705003140d4108810802c41e454805c41d0024400c40c440214800700360301c0c0101c0a1038500c42e803940d88401524401402c0900c03404496491140740240941200441c3c507040c4000042c50403200407820100310004460b0038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 973841007 1250 973839757 973839787
    0x26040c05041112090a1a190c053703180f1b0e04020a0b0304030c0c0e0603070501090803040506091302030901090303181104020f0d0e0d02120a0c03050a0302090303 72
    0x22030a4203c881440031401c03000c40400d440ca0901d82103003c6000500c04860414110034026040c0c241000c4404050061070710703980159008031207151910b64644111154540c81c0500f14809040f451043d002c40042d802c001c024045007022032803600042019050340b4001c18202500781c081c00d41285041c0794030820110b82d440d00c441e5011102001c44c81d60307581d84802c411450507a00290321140101041c007000d0341c20000303142d01c180a45404036004041e41c9843d448080160407040c4d900302a901001004d0508100d414000c140030320380040440c0c909031109844c0d000da8000d251141c00009540c051541d1034004c2403401c0c41030f8400c11580d0381024150103009050036401100800c3c180286074503030400100c0e8414810382c002c01d41ca8000781810301040000c3d13022060b1600741413801e11840b8446049840346402180b41d90000301042d40c01c100010b40f801182e6030002c0c1d00c14404012003014154800c209a026a616003005030716040c3c00e06090703029008071020250148000308003418543d10b05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 973842257 1250 973841007 973841017
    0x7080a0620030c07030f26070e0d1e211206091e200c03041a030105010c0803040521070204110a0219060204090501080312010626040c050411 62
    0x1404008014120203207100c00c0703038001150451100c400900c512000329020344c50410048040b8504003030003000c62480c0200602140d5100d100c4020058104040030790400f48004660780104c5060550640680e56844a00c07201c0392010080d51b5844114000c02c0001071103003102c0f08041686a414891901c4018124000510401c1c605402e0503800518141c091180e40318030314450085c1c00d20b4900e01c02c034503c043d1070820f03114002004d0400e500300000104401820012642e0005150313a03c0c03914541503805001035840820140741000100f01980c2c000c8104254540d02044481e00c0c2d64523400c0c003909106082410518284c4002c5c180c12068000d00c0081010f640300f25801c0100f846224004000c6000348117419015a00c102c5074460050402a522013525200750400b610f000d494080c0306007654400c1c4e000c1a0341d43c4c004502102e00c1c111905105002d00410700d8201380198840d400e0382200c640307200c006889611420042400d1001c807a0041d00541f170302400c14030481c581c2820401c11540f00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 973843507 1250 973842257 973842281
    0x160503070302101107030f051605010e031830030d0603060b1810051e1504030213090308010303030506010c0b0f01080f011503020402250809090f0402010c080c07080a06 74
    0x78041800f86005074507003d1742c0400382c16a0702c59040c518114000d036040c1d401b1603012402e01107415003020000ba002d00a50615044803009075031074003100142c0c0f58101d01c0000c1154420f0104841e80c114861b18001c400031051034445030345280c041040c684606510545602c01c0c042401c001c404010b0100542003000021700a8960810301c2c007000d604028006015903001584040100041081d03103080704664504001d0307440002980d85202000400410040081d0000810003150410641c54412407275204004640404d0080240554008045c0703101400002d080c10340c1e40010032000e910035410100c0455000d55011002e051030b003a000e118071400d10808040c1c1c03244440c0c01302c01000c1806542c0c0502d071241c02030900f8030305560070000650000240e80680d0034070040383d410503034000f5100c0c86585000300c400d5552201d400060020307460b4000c010080004036a418840180d03030001c280411150001030b83da80360000301c44018141203065000c2e02c00352041e05103e1f003e01090b64400c48113500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 973844757 1250 973843507 973843511
    0x50702210102120a09031205070e1e01090503150103151e0e0d05120c0702030102070516140117190f020d0e0d080702070b0a0e10120b01050313020616050307030210 72
    0x184d46521401a078541910040c002071b045000ba13061100c0325008550032100501704001a26120804942c2606040240760403009003c0300090349541c1218842000c1c1c42c1c10381c05002106100d400320003405a06200041c01130380000d020044c4014a0391048800004082d4890900c00d200c40d032482c09420260f07080f02e0580140e6050124184c056411036513112a400c01202955807038032000d2450b50030500050360155000c000607070005105100031a500c01070443c1d0400e0490030109039041103015600c000381407101b501140d01c04071400c0640f465029003000307102c0c0b04201c100d903490400b07000003c14014400d4000b1444403407884058110550812444044954210700a0400c0f110b05809071100300241e004403105000d0b0149180040000b01c245050106045c8000301c0404e08441c00f13142c00d627000030140708981521094074003074800e038480300b46000c6085003001100e0308440940303540024812600096440507000b01e1164800c7d0550300318042c1e80e142c401780e040c0607444d02c0c43e0035102e0813518 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 973846007 1250 973844757 973844761
    0x308040209010e0907090b132d09081602040b3001020f1911070e0a15060203091003090605040308040b10060c0201031a030a05010204060e06041505070221010212 71
    0xd002c03c640c2e034414030304a4010541ca0b40340010501c0100505a03605400c020810030f2070181d40e07494000d5080d00c4441d200c0290303c0d207404031f0814414840003a008001941001100004900c0c0d00080d10402e41d460b4659081000040c40054010708034603801d036030005807050040080c0a101c0350500d0400c4c0c05c03d030505081d19030700394001e400c0344514038038401500f606108070203100c410201c5081a0302d0741410000f070810101c554461500030b403640003085045841d0300f04846c0c0190386c020000410b981100c0400f46a040ca00c01070346034098a0031680c0120005010070a02502c01d400c903110f0346400c08020021428076080c0100940011a0140c0d02481c900c004511580040303600c2c02e003100c45564038958920216801140078060b260038900c1c3d4041c80ba800c00e10315507000d00c4490b40ca148900001a81e8a10700440602184403603c2402d01c80d500a000800031012100501c032248085854042d43d0b031043e5100040344051070400400d01d46000c00a103001d5140d05500030040d09000a059108513 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 973847257 1250 973846007 973846019
    0xd0524010c15020a0c150b01030b03060601080c30010504060b03160513030b0f09010f06030308011e1503060e0c040324200415020606090115020a0c03030804020901 72
    0x40400304000401030900102d42d85000c156641c00740c031211902e03103800441e500560700d952116020030341100441a5803480f1a01c0d05603054424140c241c007017580034205074030b40100042c1084000504a209451000464050450042e0f0380e10428004143c02510340d542d2000409080d0b400034021a030155107403e40108040c1c4107081500d1140c4240e02100e01103038020f01049a158002c140c06400f000c1411401000051041c032a062007004003401c88044c034941b0030140da081d18200c00341a100240703098024008079074414001410b607000058034148031106850304200c6c44038580e00006029500620341410542e05401c0a02241c540822a0302c5940350a01c0800303a070302c901d00c801448905401e4140b03020b24009640b1491000e9003050000d01c8415594141c400e191117406250760101001a0521586103030180810515410340700600c21440c040021544400040c084c02c402c403101940c2c0305d08428804c00c2803c000d254030107954100c141d5245000342c131400c01503d04174420810b860010600c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 973848507 1250 973847257 973847267
    0x1050f0604060308190203041715010906050a05010813020909030703091a091311030106030209090a0e0607050d09150501090e0a0305091302161128090b060d052401 72
    0xd590700f00c1c090781d05e80390304003400002c10903180ca01001540002d2100280980800da100301c40e058200d8060003007080c14440d081c082d003805821000403d85030020170701480e10744c071230712805460080c200150079844140d08003281c00109030000703600011f980100a05064040040c010780751203600c43c1c031203440c2c480c688000c40da40780c41c1c3c40040341e00c402c1c0044d41035482c141809188071852040b000581107020712076500c045e4800d810000c08039800182003256420041c032000e80c0903003070fa035040141d10100705185444403800350400040100102e03421608000c4e55004003080c42d44148002c1001d50029001c1025000034442c2c5419a132605403900300540c03000c0745000c1481e916aa80510f0501c0700c2c400c100d501452034801802c0c080d400d021441c0500104400721114a0241203103075007070082e0004126540951052414900d2826500921170300058101c90066a05128004c182584100701040090103140c80031101c403810708041c00f8001611840e10315403108070945000c9001c0c0c0d10001511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 973849757 1250 973848507 973848509
    0xe13051e07031b12090b010803042603070b0903131d2505031f09020c070b1206040f0e010507090311060723030c030c071e0803030f0a02160501050f060406 68
    0x200c0140f81e61660840c1c0e0b4880c0440b8141c0c0740c1210400911030b0000e07242c3c8a4107107000d800400c0300350300004062102e1941c0c44007400708150115120850b03411030b080ba0540700d01410f00002c01c0100240c2c042503c4140a01c10b440c040417001070b08082043d030303821002002c403400c011101f1103081144013041e8803031070750104409907400249520104540ca18401c441c10342c4001e040503080d08040680902804501351414000c01c0004009a00c5943c045103003820003995920000100ca0704000340c1c005e0b9038202c03104543c0000c1c2250001908208070800402400ca170040718181540707004200130486030050611000d032070046070500310440c078410030302c041c622980c400038000e100803410009103d50f07942140d00a4090b00403c1da41803000304036200e4915080200c0801c1d142c2c00035034043c46041a10792251042c25010345030094010702d4000c200b0b4481c80064025880e282c400e00c0003500510b01c90301115212032007000c03030461401103401c1544c020001a0340c1c201541200401003865403415004100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 973851007 1250 973849757 973849781
    0x30319120b0411071103100e15150109061b08030118050603010b011d03010905031b060a20090a0f1205011d031b0a0b04030806120109030206070e13051e0703 69
    0x3c1d180008036124011180004e11405525101d03000100844a03c80c0c05001da504500304020500b160002000c058080002031584440c007815071041c048903a8021781840c115210303400d10040300c9040c01114021031100e13140c0039116a00000001404501400312410340c000f00c00400c001c10b0f1906000c03d401c3c0c4076004c5410b800900c105502d00002c80380041602c039422001000090b0580e85a610b890550b0400038202c5001ca24108034083c02200500c041039020242001c100308401000c5030003c000038a40b140c02c083c2d000049142502da071966094107000d805851101829181e80b540104003c41c03a60b10111125400c00c079410040214603805002c0c8200c0c000b01550600c850600e4459440c0764503005040e02e480343d00d101c0d0300400c1c010f81c0600c0c02503000396194111888c0c1582400b44600c0002520031150b85010007440c0460360110369140c009159140c0b1030111000540002c41d1000740702001030310545008148162082c0d5111808046000c0c0000342c1000d07034031544260212520000c00b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 973852257 1250 973851007 973851041
    0x32e1b050c070b0a0801181e0f020903011814010509030a0c150e01020d0e121e16031e111203060109030501061203020d0801121211030304050a030206010503031e09030319120b04 78
    0x10a523078205d5801141d402d0310502c0c8014140410013001a0945519400e419166914400e4400901c0b00c0d1080001c90648254028010780c00d001001c1c9a491080003083d0341044a0300e0801c40070480502000070350851800000d21000e02d200c045203000b0b500c01c1001080da035280c0399601c00c0c58000800c990300214905080740703081ca4078041101b00d080700f981d4202100140d0030032813050300030182c40d05251903e02070758440005a0304a01c0c13031041801c131124400140304a070588604c0c070110009051001c6004a80c40035100d46861005131880480c0f504010038030b500f401408a104040781c102c0781d14180c0139901f10741c0d807a6080c6d2015100f41000b0702407182041d152031154400701d4850944003a40c811075141000a007440c41110700c0c21a0801d845c200ca480d00540d40000a040e410482c103805400114069171278080300e10001c141c07480344444841c01c2c0000c0810305032100da0b410320644214404024070201c0031428a240100070032456204041024905861030149051501c20209241484586 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 973853507 1250 973852257 973852301
    0x1b081b0304110d0f080702030610050906010e01031e150b160303090203030906030f07020f0c0604060e031516030e01060303082202032e1b050c070b0a080118 69
    0x910702411440d4a201034000c1064030225001601c41541c0300d260b5402081c05641b114501c0c8105400c045014000d040d41c080400c10600c05035032041d25680d00104e09091400000400e2401a4041d010403000038005100d90618040811004c0d0808146800c6240f940000b50352104800c8500c1c0c00f45040c02120040c06042407800039000342d00071401607000400300c900300400980001ca1a52088844103c0d800c4103000348407140fa010000d2025103128400034194041480d000b09100340554400ca10400104007054000c81e10140800140c0041800301034032140341c01d1000343e602041494419000030304d003000400f50668184503000690344c0c540c0c0c2e41030160300c4001c0369036030941808a140700c070024030070b0240005070390400c68007102c020042c054511210302c50016501801e07420b02d1514646041c03c11100b0350f4400030109816010301802c0698960500603191450441f20340c00c400c01e5602e0008200300804d0300600300d0f904030703001148850503135111500847c054401c01a074102c2d4180203904 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 973854757 1250 973853507 973853513
    0xa0e090c120f030f180a03021c03050f07060c090b090102070603021b0d0e280b0307020f0d1805060a0f0e3606090f010e0a0f1b081b0304 60
    0x201d60344051020040701d2495140110603401d40e0700c81c1035000d201010014150312003018021100d041080c00301c5041011034915004075110000681002000000031030300300b01054000c8081e1400b10080c1680381361140202d02e0028000c020401204020421240d80024482c50a0303040b074800c0316042e40a865024907044013a00039400803042422040100041404425001c0100428001060f596208000300640c24044000400e00f0426540d07107605a41c2990b40f498600b07243c0c1126074088441e80d40c1d40d5400c0b03080f0300b0503500a040340d40a0080c2500244610f610a404161102c660340c40d40500741d50307c20410541e0710681030000c020840301107100074224059036802c0e000344406040c1d05100300036003c003a80629051020460300c1295800c1444003024421030782c5074001c3c425240b911b02c41c1004050210302410510a00711710035190000201030548a4001401d0380c00045414012a8150314107124840c01300420140000c075100002009980c01c1482c3c01c00f44181c000c035440c55601c030340d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 973856007 1250 973854757 973854769
    0x12010501300519110d0c181a130204030b04060618090201020a02041104081501090e0304060516110402071a151008040c170706140f0d09020307230a0e090c 68
    0x71a0a8a81c070703400c1c881040194403017a60800b4000d00c10301789600705a040040340d403c070440c0c0010404400746444a0314226159604200840c000111050b149050302401900040d1107981c000a10110401090004110407034000d5002d85210152240c554614000340340200c480f8000b0190041e4001e50305039001d4200713030740041d0409000ca0b500e249000d4441b10a140b0303081044021000c0c110365000100701c082c200c1d205940e80c180d00070020710310f498074010300188680a0300945084007226080648100319958244c285800e030082c0065466400034188007640b2a05070510074400c21401002840e0034508454402840c1c1005100c003885260000b01182c005030700400441d181c0d4030440c0c0c0890600003408080000c22071000044c60442d040100051029070444038000c6448c10038400d01c00d840f840e143c1a0b031000d0491460018049a8034000130b841c0c500564060744803201c1115903e400c10052528400c09210180d511402c100d54842090894030003c64221500d41c002d006140450702e800c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 973857257 1250 973856007 973856053
    0xc090105040e0423030901030510050607140a12050903100509070603090602130306060f0603020c03181801062c090f1e01060c020405070e0306060f120105013005 71
    0x42050b0307503402d40158007072a01266a131400a0b42a1300218035903506d0340c1d1500500340c0c060b504110320120680f4100105003140544c43c40185501c0c1541031a0380075213810044592515003000441d100840f40c0d503c0504941e00c4041c200380603029404c4030340700d502e200d4059940940d0441d0018005a4a404422002403030421070403950b85408110031a241050485140c01560084000003a41c600e81840312107031022640c820414140148407444076001d0110503620041019003000c900000140002650340c82e041e00d00322441002c2a0002c24081e601c0022a2400910404641200c031101c0052880702c022162b80c039544203a402000880d04882d001205410000078000306240210449100089030000d03040800026900c210003410b51400f40a016001109828102442000070b00841d4585e0001441c030360160380d2811035150a511203035202a03d440c2d08800800907961900d00000a02039850880000c005c1c6164102c0080e0f554021504145548100200208022140307011015218 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 973858507 1250 973857257 973857263
    0xc120b07081e15060d05070201060522052d0916050604031b0807090203060f0604080d2015090106080102160f0c0b18090a05132a0f030302060c090105040e04 69
    0x3510900e0a5941380d1070040d040b051140140070440c0d1900890082c01c6440707d174081c512500711000d0200b0185482c4c185c03008580d00c04000440d0f180d40700c2c801110042c10114910155040c81e20441c3c152041080307456018090150030707240700003441c1001c41c03070280329401000c1e80154100005c10001e0b0405800d00d812822001202c049560f8941c01c3c50309005060b449400d4844c2c00000308010f524000b509082c0f1054102c0b04141000d04200e0240c0c0d5403200102120180306802c0700302403a400300c5529404100303c64500f20303002c80321400c04c0170210300c1080c1d8231081150300300700000c280e89206009840400c10600f070300d0036014103561541c010700824034800f030b5441504020013007114070700100140f201001640307224000424000c2803241c0c4900081203910b0b15464002402826856021b034100c6482e000001481c014031a042003146c6107011561540041c2c000308030014a10aaa5101d00100ca01a4003620884c1ea2250040d0001c2d1250440003800280304210510245030340300c1010b900940 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 973859757 1250 973858507 973858531
    0xf0a2307140d171f0b0d2a080a140907030201080a0903020303070c0f020a0902180a0608160e0a15021e07061b051e010f020702031c0c0c120b07081e 65
    0x208420064100100d604403603505d04001444101d80e11480c003401d61144441d50300b40103034214090341c4016080550903281c04010220020803902d90260300308070300500840d1600d02560522100d070540c0c0b1840c43c4800c0f808111034800094070241c413403080380e417655055001b640c40c650750103108a0f404d41404104031445016407542c40c0c050380ba4176240f400603010403c030069903812140304010b0452050700c4c0442c85854030707042c144102a0b06c8a015500000c040350700c21084588440d0951304283c0e18084960020f1031030074009000c0070740c0e01c8440780c0068241c0984102c01c550040f0380c03100d10b03000e806415083d400f00000304007030340c8603556002d2884030083d03241c030031884d5580d200790030701d01810548400e0844902405281d82c1088c421115002d6030700c1003c52030046198042a20303140b80341d6603111000205440f01000a0140d150912143c5c1d114803003a002688400161500364403600781580e003100804c0000c2c001500444815000b8030a1032809041103001c8484010000002407410100700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 973861007 1250 973859757 973859791
    0x3070c0305121e130f0b100b0c010b010807021b010f0c060e0604020a14011413050306070302070b01210609050313090605041803050f0a2307140d17 65
    0x221034201094080c002da500980c810f429000450380b407404028080b01c502e900030003001e40006860401007a40541c3c005450041695407107540001c9207a164000d006654001074088075a01042d8003040030701c0c2c0240c1b03480503661103400080303980b21901216aa40e1245803074a1304072030340c0a041032101c01d040500d8140d4445903155a24005d4510f210350b6182a80d124109110840ca00302c0c640001520007000f2445450300301c4400209456100c60b00420b0488000586030021404141950040e1802608582d464140808024020340c00310400b5140740050200201c3d1a19800d449100d101403c0752204846c0d035466118003000f032890031021a420f100402041080140425400000b001d004600007001072a20b414002500e4403088500c048800c0c3c541d120380000d400500369021030302c01843c1503403644482e09040e20103842c20155580d81e4a0a14810140020550011b00e0514419000207a080901d115000d50b100326802c003250210b1b40c101e50b00b60480f01c003800d00584c023440c0111100e043e030f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 973862257 1250 973861007 973861027
    0x610050f0d180b09031c05100b07030f0e0d03080a0c270608010801050705042d03210807140a0c080304051e1609050405010209040608011a1503070c0305 67
    0x140c41d1410b07a14501090841d010061008480091390300815160145140030078a0501000181c1813040f10100240e440d0081035507500000c02e4031000d407c2c180b4103c4d581d51461304005e04400c0c90310b1404d04c0000c14081840f01503003800900b0640003030781610b030b00616032034000f4039101074005200c80404000341a2969060b206445040300000310508810719a40b6041207002800e4000c1600040a00da04003400d000100794400304640c1110010101d4209a8404090000700301018410b01051b9107988040030091040e480c08200d03000103080708107900152244000e0f01c0c0c0002c2292100b001c43c005e0120000043c1ca418002d000880c0d00d8078040140c1940e994030101160015501518103034051a180d200103500308405901c1d050861004080019907145500900f50040c0101109140c03190b010604116003501903c00d03292005000740301c41611541064000c06220684c0121643c110040d0502420311001e150300840d9810101c518507a0b82c11030903130341101c2d44c8100701c2c10000f00300594001e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 973863507 1250 973862257 973862261
    0x51012050117010f02090904081605070905161806080a020d0e06100501080f060d060b093c1b1e03040506010501090503150601050d0c03051006080610050f0d 69
    0x1a206990703403803070042000b400080c00c5a8410002100c81e5204200008a40d602c0c142c030641e000d6404456541d9070411854a170035414081980140300c1d02c60842d000c038a035486508a540300300c15a02019820070006102160407030f00d40455100282c545640a1100034442d40690b50310146121001d032800c054404900308076601e00c82d26441c81d4021600740448031542d0804c0a0041809203002c1e01030b401c015000c9a01300f60064000c40c850300d1344441c0b0404002d00e03a00a4511610018402422032031701052811000109a400d4440340001450817100c80d00540501d00000fa190760442602d0341d1480540000032141c0c4d01e25001014041c00142c0c0e00070f807401d0032504401e10aa0300940c5a06140c9842c03450140180c10890500090100071f0140343c4000404901407649952134800a40303800c0c5c0140c0e0144103491035110301d1400d1031002020184c06030440d9000d012444900c80b05907581e55000c07100342d032007607500742c2c1e02903050480c1034000c500c0b0300040d01441b18456441032178022198030501c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 973864757 1250 973863507 973863509
    0xa1e1a0a11071a0108030a022e0e100509070f09020711090c0705071211190803220f0602030f0c1002033c0610020304030f0c1a070c0510120501 63
    0x80466144001d10f03400402440414018400c3c0c2000754100202a10043e403680784000c44019440d488202c1001215404803c4a1a922400c0c804226000d0f101c20099150303e900d0402607946070401010030b80d00d22000514104440c0c680815502050904541c10007a5100400079910388059202c000c4440d520f01d0407e40c09086001d05190717903140149401420702515500400340440b0300c140b0003020517109510703004100b004850840e84940301c1d08003038406100680000708584404a98040c0d01c9050407448110400081d80ea4545503684801c50720102045005170310058005001c2c28008500b4500645000400102690350681e50201403c04980044400d0007103242c1505c0540d00c0a02242da20400440b16107a00e070f4030281030f0f8540340c0c8010001401c0d00340140c00311145400854401d0080d01d01841d0b004140180e0074580f400d1480e01100b090084820064003441e55000c80c06503002161041e640c13140085034644d25200800c80005402d01e850400d10030319a0514000c01c079103115840c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 973866007 1250 973864757 973864763
    0x60b0d2d0b16021603050a150e0604060e070e10090c3005070e010c0809040204080109060501060917120d0f0e0d14180f0409050f0a1e1a0a1107 63
    0x710ba030a00b9400024601256500c1d14070300101107031414400f09a01186010015030441e11103040c0e101c194160400401c901708021401d402030350203100405c621604150782c0409980c088400c401d448034844040c584090f284800e40c251442d0040105914580040405503498208040d00c4201d008004230302101c0c400c0c280c101514100d1042030610158415584c0041d460301c2c103c4150313040c000018241c1c014900002d046400d01003914079180d641d580455001e80340540c02444805803e2070280090b0a0030302604000c11700002021034400141c3c00b00e03035a011134007c0140189103a200d40003070640d00c595000f005031500e480d680c8508400c54004c0c081d080c019400140f8066040340c00050414009540d40f84e001c120800000c545840001014041407200b103071000c14103040b04000a0040c04542c4006140b80940c04071000c805402050001440b40900c540000009100c03540c0c41c8400c204210007880c0c02c26290100c090702e41d08180c0580d020f0710b00c0d01d000032014030ba00f519031a9600062011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 973867257 1250 973866007 973866031
    0xb04020910110d0f1b140718060e0601080a1a09070507260a030510091b030b0609090a05060a050316050f0a081c0c0602030c0304060b0d2d0b 62
    0x264203410020400f40780302c02c0c1c0754608402c8a006102c070040514501c10300060b803403034002c040081840402a0100c00c0c1800c0c0e00100e0b100243c3c0c6529880704003001e18680c0d513a41c0d04e0284006007442d000c100e0030b841810b050b941c00d04180d0354172242100a1500780109a26000c460280c45840d4550440c13560082c40c0d03035190b0f41d8490301b481c501000f90300481040703e010700d80c00042a03081219018141c0c2c0c0c26005a080101d11595201c4068502c007141d64001c042a500f4180850540707802001c1040c0e5000c800d99040c46141640c4e0706001d2140300703d45c110303500031a00b000042c4220301c481c0e00c80354100e82d0081003000000d58600c000380c0f40001141d003841c640001c001c001c02083c070b091081500e05c00000d56035800064a8203241c1c40e01d40045048040280d05541c40d03000c00035120300607490340309a002c0c00441d180d041030382e0081c0482c0c0007210215101c81c505804502c9510b041300c0f46031421548581590144116031150b0903840d00241c940d900b8402ca400e54a1000079025001d280c480c101c0c0c0221 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 973868507 1250 973867257 973867277
    0x1030308180c0402031e250f050c0d0c0302060f040b0a05070e1f1d09150a03060c02011523121204120c0e01060203220503100f2304060b04020910 64
    0x440e0121b82000d0304e0480c40b071242c0c0c800c40d040da0a0320183c0c07400d031300c005040c201c5103004d0820003510039118181c0680c0b140d003e0700684450380780e04119802d41c000d0113130b802c0700e12665400902d8a07482d4000e85001d0030783c04440c800500d618485d83c2000e0b038042ca01e881c054400003842d0300855031107460310f610341c0c1054116002c140303100c42c0e03c5061942c200a5103000c0381e01302640c91011814510020300002820041089500c41c00c1e26556540d80046511030b104000341030290b00020b00030841e0038802c4082005800300000d40310300048201139141c0c9068240810042076004000004600008500003809900322801c00a800305000c4c200411411045051580e107610702100c8801ea942c200054038030311040180302095001041e107050050000c1b40b800001000700d81e05012a41a520060b07152241c81007043c2495640d8208401c02e000e2402c040c4403442c41110b500c40d2648610201d08450602c10000501042c0150132110302018080d01c014a80407100c0041510f00304004841c1c0b01207002c21803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 973869757 1250 973868507 973868551
    0xf0405100801180c080f0604090b0a0e0106060806060a0e01180803071211031206010e130c02101a0103110f160b0606090a05131509060503120301030308180c040203 72
    0x103d2141a9000c65004000ca4585030002034507401313000c3c08112400018100003400340d10303681e00c0000c0e0a5000040092031789000c02140016047d0000c1c0c3c1040c0b5400c061000450900a0280c1c900401009014a0424070301c100d0441c5c4841c500084d05041128904450f004003c42d18050720141050ba00550b6031502039041551200c1d00c0c3c0b028070303c100600c0d42003503003204a001c403da03440c405254030000365039114500100c401d00307029855a507008040f06070903a124011540800d0003806039800744c5c0c40324192481c1100c111403840d010b260000c240d1061001c0380e036100c0da1001080900011b9010704207410b00003540419008200354640b680c20903400d10f030a01c42c0c0c829031107520038003c51300b01d07160440c0c000c049140b1300f6403446050b01850b154030504104006a800a94003100050100c1000b01d03910810b5030301030619482428068060015401428042481203e058a405445082041e141c84c10740102c02180544441e07001e002d49500c00c4c0003a40d4030300040d8050300844201000400c038541c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 973871007 1250 973869757 973869779
    0x40507020a02031c0507080a0201091a0106030c09060206010b0915041215020309030706020f360a24170712060506070f031409090c120f0702030f0f0405100801 70
    0x32200341c5000f00014000d01200b030384032081b40c0c55103a000c440c10380ca8001d0710005038058245128001e1500c04d08030040391001d0040c0e14172074101c1d001030b5010710450840744401d4404211a005002c01a007001005001d00d884030402442c100304040c00f01c402c110560004c030b84158025810034140701c001d00400303006200c01200301142d00404500110b1030b42c20b00e180c1d4140d4a21680100034269134002c01c80e8141090000c0580e10820301000b162081d2011404034119000c00b0b1403440500341260362605d00721801c1031980c010a449040301d104542e484603131404280d20550340100f4003042001e15480c8418844001081c1c001c81003501c8844017800c42c07945c10800d64091390000c9000d000d0502c0030002003603102d424003990079018200802e141c485903045d41114428902034a41050000c1c00b84000e01039000010205d010070a00e48504a4688444041c1e9590f4281c81c1030700103910074031882a07070300e40c514000c00007805084140ca14048d80d80c80072848070400c0d02d0414021031071140041201407109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 973872257 1250 973871007 973871023
    0x212031008191202062a0d05091006081f0911061309060902070302210d0e0604021003021e0904060e0f0a0f0605030304030303020c160806101a070f11040507020a0203 73
    0x250005d8100d40c80c042c66038040d188561408030850007034070320340d80c50454805021603c0c1020700307070010b100e103180550083da5100010350706030301c0e06447c03e40c00150400c2d001c1a007060b025481e66040350154400c10b074600c09010b010364165003850140030b210625555000c01002d90002c0240c08400344d0380340a07100d004481c8560304c03003982240100541c0c00040d41c08101394445806029a4103074080304032031044210300801403503a142a2510403030b2a01c0c0240010240e11841c03085402540111400a0231401c4e0302039650101c400c00300005180c0a01d00e85100a0400c5840192000030516552070403600f445d002507400d0740010307810b502400b15000103800307030b0600207408000510099140101003550b0344114880681055808509100017080511030b0005032050040711043c03c0b030329021816102d81c0181da402909120b800780001c0e0074020380c5440c40c201c2044400303a80c1056820380743e4401c0c1d0150341f54202e40358000001f40d031801da51a4800c050145606600070111544184181441d03c850 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 973873507 1250 973872257 973872293
    0x3090d03050c071212060315240b0301061119060c0f0206010e011202040b040905031c05060603040f0f0c0311040e0303100501030902011205070509150901021203100819 74
    0x100212404200c014452140382e04044c9007000f240e60140c5c041500915081d00004e111442582084007068415088406003400c2c4c42c01410709031031490390088450a0a228040e510601400104006401012040d00a51542e0169100400b80c4500d10031101c011820448d003481e40c4da00d117910450b0b8011208554443e040c0010211941010008000d0703240c14840d41880d00c10700c4410ba4115180c40d00306001e00c6001a105005010f100d25180d600c9170003045150307400840e1032000200e880000d0280f00e01410001d42203034550b841c0d68586e4050309080a5083e84c0e040300705a0404005070704210060019030103490078203603084c442810030050b121540140d403c80d61080c000e21441007416000380c0101c0342c0908001511035654130040e9000342000c01003a1945290900308030300d072038000000302a6554104e9080701024100b0f01c0620f034038011602140d0060b071001c0d002c4130103110100c0c000c61b0031030b005175030319211141d4481d02c107843e0681140e004224180052652000c000040083ca112801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 973874757 1250 973873507 973873531
    0xd09060305190b01020f0321160c08090a08030711010216051c2607050c090108060a0921180905010302031f0204150c03020d1b15020f03090d0305 64
    0x20102ca180c0400701840368101d0030305542d00354401c5079a00800102c003240b048502980d481d0810090812115450400200901c10507007002404061080f9011103009002c1d8481c010340d000a501c4500301c81c0c010240d115041140c0c1000890b07550000c1018040e5613201d00e2192034410741c824002810080303c0c1c0f40341500340d034808006024030f940d5030103118120340c40350940300600e200320300b0051390070354074061164034040d18410b142c0c83d43c40041c402807500c1c034050002c8400e02039124080c0a50043c0c00d10030700e50f46400182c0407540001e443c0d0041c89169005070001040c280745040300d40110791090b00180042001d6201d089800083e89107020000c0c044241c00308011740c51900800c0c0c0714034140e140070300060608140441d4145241c0d068a01404581c10021162100818060540c80151009502500c910480f800d0784ca4484d4101c0031080480b1099110340d08d15559800302041000c00e08003500d5a001d00c48640c20781100c80145100d04204c0b0300400d5100d40c0d0442c0a4121200a404100300031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 973876007 1250 973874757 973874761
    0x1507030e0402361e010c1b24020625170c0d060816050909010905070f030b0a060b0a030b01020a02100c1b060c02060c0c0a06120606030221190e0d09060305 68
    0x1c48034855031100030701c00e082010303005100f403910620400c00025401000300340383e00c0c0803c000054070800d001d6230424401d103651102c0041e800b66903032134003210000c40480d40e10603400701503031400e20700541500040c1031000a0303800719040d00c00e850f04100c5011040d80c1d4042070202a40c0628014070009142030700161291643c1900c446401403003e002d9640101c10f0070f80442d651b4038095104d00140c64021042d07c00c04e0b03072145500da0041c8205d11007542c2900d921000b003000c90302c8601ca10811102c40480003494808401c0c030940281118003000c5056015148110300075071242030303030041400c003141e503a440c414000e85080a142c0c03410848408071964100b100740146504545200c80c510340468080352a80903110145142105181303106030000301c001c04c000340302c903040345186d80d40b40e050620500100d92a05400c0301240554110b0180002d5401000c1002c0c00034030880c0c98000c2c4100e1710324002c28451070070800984400340260301855001d0040202d02a5001c5584805411580380a0100f4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 973877257 1250 973876007 973876039
    0x306060c02100f09120506070f030219120603080408062e03020d0c090c0c0c05040e060f07020c031204050103050c210c1603020105151507030e040236 66
    0x404441c001e0b110900c01e00b042c01c3d044050080d8159401444415010101c0902c10300c0c103a0b4032104107841c1c0c60081140e800c0b44510040c000d009542100c032070381c407411003081c0a00000f2a040b5408030569040300d5990030010011440780300080c009000781c0402085903060080a142405440c40e00400b0116800d100d254116000c4c4e203aa28200d03901110300e40d48070500303801c203000080107950084c8219454007241260158010600120590041c001d4610840c1d440c2c0600043d00e0300d083c0303241444d4028074000341d50401c8401c01203230401d0740340c412104010303c92400b0078a4002001001c1e581030f000860104090f60b03244c0120759201c8111201a03080c00800030800f4600b0941c82940d170103407443d60000074001707070410f810741d031248031200401c0d0a240f4080c10042d0090805580ba080c9400f099040c0d00f803103060065214074603c4c0c10051241c50b105007500c040301e0b80001455001d0b401071b002c000074030703c00441f040303c0c034186d6100b0084030001110001100c5400024000d0302401600403246610031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 973878507 1250 973877257 973877269
    0x7030b06010c05071401050d060e27120f1e0c010c140d0218090a0204050a0e01050603040f05150a020a1b3801080705010207082b0e120606010306060c02 67
    0x111000e0144040c401030305c0000580310b03801a81140f6814610300200065202c0c00b55051500881c01d03200920052000070002c0340d8401030045403204554003002403c228850180c0040000f411042503281c10040d0800740103c034000410f0b4160091140441c59043d448800e1081f400c20507824100004485140c0003c10841c1c0242a9440c4641d540412070f1080e070500355588060550b0010504e8a851400d00c0e0090029037081c05103902440d1243c001040351820105400c0c1600c400505c0c0c0303415980c1d65940e140352004050740880d031600803140456104012a669580100c00072140035880756065075009042200e44d81c00602c0140008010b400440d04280201441218880942c102420381004071410f944140110b00c0d03155400d14000610920b0204607541601c030241c0c01d50b40500d84d40e00019a0b9203d06c164540d005a0701d59101e01c01c0d01440f4440f1038941032680c05d101400110410014107400c4003e0303d084003980100c810001300e0342e854821040544124181001040c100303070045a1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 973879757 1250 973878507 973878509
    0x11d01051b07030c06050a060906060203040308220f033c03141606090303050c0418020928050f030d0503010e15130603111509010c0215070507030b06010c0507 70
    0x1480200000780074040c0740c400d01d9103156045d008081802a800d029243c3c0b00100b15521032620003e1600201007880351002c011074040740e4100703084030308150b090400c8040170802c2a43c046801c4060610010380c0000c11840f081c0114003500442c201c48000c0c2c580d1040e19080050318050345004010360400e004842958013000a0b0185440e0942d568000e581d50442d1240c01c4118100985102d401001c0008c41d400984075a482940d09001588031640d1040590085016880308003d441916401c1c006407503029000d05100101290790460111841c01f880543c801c081c1002400100c60600c82403c200e62041c1c82d040c82603000b400490380ea0f0000600b5400180101c544100c1071402040c1050310300300940300c0c080f00c01041a4001e00708405100010030107848101c0b40403240f200122030302d2410784482d409242c4c83c20380c50b9181000000046419026506c01203074030080003510070510800381c0016019640c0700320018441e8508604040310b690000800141c10031510043c1c0c0d100241c00810480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 973881007 1250 973879757 973879801
    0x12301051012020d06030c08070b04081906020d0515040c020c0102030702010c0212070609030317060d030309031418010e12030703080403110303160f020f030a0e060f0301030302011d0105 82
    0x10802e020110042c80280c4505010001201c1c03c102010062002c244002000c4541e41d900302d98070301b43d0301e003920611070059110b1440b480d004611860040040f403940b466000d03104140c01843d2600f407006900895030243c1e820840c10030f001c52260b0043c00c1c0b0b84540380c1e02d01c4080c001000303880740d441e00007940d03403048031802410006040c0c040c000319218a996aa0002406002d6660980d22004014605004c51000790300083c500e04603207000400f054411809003201a120507043c1480d0b45040d0081d00c0300c031b10110100084024040640361700500a440d40d0026070000c4404502a480010980000360710002c0c81190350300540001c501d800402c0b80d1031540d241c1800000c41e40d440c102502c40b1100703d0700c05c0b8400d01000040182d00300c0040c014509500346a114100c0c2c8040d0041c1c00c81e5107494940210f1030fa80c0c000c02002c0d08040c000d00c5444c0140c0c8004160501e0a0b030030a041c50075503002a80102d0140c0e440e4031800080480480821585640180080180d490100380007100c3c406841040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 973882257 1250 973881007 973881017
    0x203070501140708070807051605030307170c060c0406111b040e030d02132c0f060402040b07121b11011b0b0f10080f070506030a0902030703050123010510 68
    0x5140d04002c044281c4800640001c0469107441d820700f0003103050351140030212001d0080040b01c51a001c8000e10400c2a244080d0003503003032600315922032142d030042c442c09240d8450b05106814126400f04101440341541215098039180780007005414001a03004900641d00000141100822031499580c0904c0741128089000220007004900394420f00d1b0507031000a0000405583c3d4414045115003102c0e10a0f60203c04145003030944156125060a81072a1070403141c041101500041030a41e04114000c00040ca00340c0d803030b001c072502c40e408424203c9d1342c84012211040c250307400a9840f000021402c03405591500907541e0300c41a0002d903080c00f414030401c40241580c6180c0704409140c441e034051104610303424014405040c80c04100c5808074107060f1800c000c00d4464010581400158040e07005050342400d003410000d00c0d8000403c044080303a519a007900140e90f0810560307000314050b80c0001004403c0712111f0105501d018515071016510800400260f01c8a0042c480344607254645 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 973883507 1250 973882257 973882277
    0xd02090a0803040f050312090603042d1407120203030409050a0f0504050f0106060e0102072714070306051915120c050c010b041526011109100c0203070501 68
    0x14036850815001861103100215002c00d994100c800a134003500d01c2141100c201c0b40b00800d003204c040c4618401550062001d10100f0006007042c031030300042d4801c110441e075200c403004800b403201c4c20b4440381c02c3c1c501c101141001c0e808080f090081d18080d00b40140314181501c2d403500440e0b0380740726500c07e145d14030343d6850004203004a00d503c0b0104034400004140024109410311568030308a60040c0b40035540380400014903140541178895002d070060300600429460500c458141c071118000c4072809881d5043c0c40300a0403031912030050080070170380520300c01e42070402000b41104c400f504500c1c000d000da0400321030a4589084000100c03804d00c4618040c21408c180111200c441c04142c07014481d0426081001c0c0a4218001d40f14100801e402000405039250402040e01c08040c80e01031012081c403801e2100088000306503420301c20030030410400200451042d42120440c50000c4002800850b151005140ca01d0040f1b0b09500185003926105506400080d01c840c11803281c8e5050081c1d10318 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 973884757 1250 973883507 973883509
    0x4060509040f1a0a0b01030b01090f120302011b090f08060708181e0304051e09040624240305071d040f0e0102070c050316030b0c04080105130204051008030d0209 71
    0x103041e142e00d00c5100191241401c010384c03808050401c040311940403a0408100f464907505c6000071504075140d40000d03c030749a1516422401480c44224144d00b10354886840820300e02001020062040d419510400b026190413580b260400b610b4001d603441e0303040b100034001e9440c3d001600c2034105045425501020807500965842d1400410340c0b0221481c030002230500004020000d03004440d019520080352000070817000c4040c4283c0c5291a03408100032010a001c2481540010000c881550444d901030100841580607075145500c140030344024500c0c81940b000004046401c0740e070140c11700740181d0810020140080558038002440101a02c0741d61200740d5450308100000582428100a030f0f0221280c4940070f03601500c001d50301100c81850014090400003075002c012840c10041d150100c3c1142d17030315000c0f948081d05180c11460144008902800284030700790151400e08000301d1075448074814002a10b2005110610b01c0c400b9280400641102004403100d50081d10001039844104134 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 973886007 1250 973884757 973884773
    0x7020a0305091f0201090b1303021b061605030a140705060402040c14041409012403110904060e160f140705070801060b03100e10060503130512070c0504060509040f 72
    0x2007036541e034510f5040700c404501034042d44043c2c01c0783d01440b0f15040070344d1040103001e0548404400100140d000210811010004a020903001e01b0018403241c034015035003280c0402d011100c2c405079100e13000001c400040c0e41c1c20081c000304c2c15601c415a241414500d0700d40b0354031340c1e80c0104040d010301d441d4080e002ca56480b50041481d10340252660b5501c55403154071000c21500039410032409800480c0000c03440d05415188022800e00042422001000309102180503098200c0c03060400030050040f0941550303140502d501400400c60f902d2000e00c0d0080019642003280720f61202404403400c420b40a141e4046000052625000402c0390346030041d00c0c01c00d14041140d400180c180d46054400702d01000084011405105600210002c90752100740304c80380c0d540c060b01c4452000b0450001007005501440c05142c1c000c0249090504115458941d00e00b45003c411101511800002c0e08a08004102070360f400904000d13201001500d0401c1c011944012000d0000b8244007040300702081042681 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 973887257 1250 973886007 973886029
    0x507030b03030d1d06010506030106180807030303050603100e2a06030a0501050306010b0f1602130c0203030105011b0b0604050c0c0d05210f01060302181c0b060907020a030509 77
    0x140480303941e80d003240c51020040c510f0003800156165a80104800082c00280c00c40c1031f944003c0c030a40c5540d00e00081982c0e48011030302d07646034828400c0b40000302818184407000041d40203860218042c5826401c06051a81a05c00030800c1441c1401c4038144c2d140000304c8501201d2000d01d41145c42140030403160283c1060052540e0084000040010604441c4c008a0407141e0507000c8510300d980710584500207006028002400510500c054518146100c03101142c0074000303801481e46200e2082d6082c00d44810200c990056030000004000300e580c49002d5084890b48542c11401d4102c09903260480078201a0540d032080b5203c4021903070b00840041160020981c05003158540c2035984000750042d088521010514030b402441c0c50400340c0b9044105103d20b0041c03000c5209030303080a1043d07000703401c001400c050780103103010707e040350f61104941c1c440200f06455a2103001c0303503186040160700100424990240403c4420f0000554001407400c4065a050038144d840c0d00c074000210705e031084a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 973888507 1250 973887257 973887259
    0x30c0c0f150b090a0b151602100c120201051b04030804050402031b04060914040504050c09040303020d15051516080d091e0b0a0b03030a0818010510060f020105010311040507030b 78
    0x3c902440b0b1084407903841001c541c4415200c0110b01c03c40c1d032450b80c1700d41c00b0b5207030010304a0580e101e0020061415403085c20000103282070050301c045290700e594104800104801c00542c0d942c000748006041c4841c0f0031504040382400c400d00d098159580d0b02100d0040c0d201c0e0f54083d54000c030101d200781c86400d00d10300c2c100c084849402d4440380d8505000300760309254450306281c038003d180c05040e41e0416004151049400c80028a4143c01321810300940f044010015010141d0071321540311151818003036020000035035000c59004604203410001022452020000c081604200541c2507003403041d40b182a1070340001071035403507502c1d000311100600f002c0c01c1c001746491718000804140130f00d008803280b040e0740900c113080100c1d0f031200001400c40e102180940e80c035520600c1031025903842004601d5002d600f001c0c1101034a045200118203450007a07131000488442c100d406d000c030301c0c1e010032044c000b400c861009001a5141d070b21214103500c4603140c024060758895002a80c0c403030007034204032501c40c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 973889757 1250 973888507 973888519
    0xf05011a181c0f2a0608060d060c020c0111010c080105060309030d09080d0f06030b0c22120b150109140103090b010f050f010302460f030c0c0f150b 65
    0x40d0525040801d11600769088030329500040786001910358620104168010004041c04c8050525501742c5116038000e06840c2d000031703401d17180030024a080c0103640c0340340705039002810a01c40c40d000141c0032402c11051401c6070b0785403694080d002075014680034110f0340183c40066507500c92880f69070961240140c41ca14450400c0d04d04030810a01c84c3c002c010b82c3c84031000c200014241840303424255402d610000d40440110400b1941300c0d5603090043c00c9040001b850170498000d03e00c00d040c810505039021a5004c00c5802c0c100c0107100304801140d52200042c5204a0442d4030500080d2407542e480c091070100310782c0c94a0398a02a4020b42c4042000360b0071000000056035104c440b41d05c074040d1401a82e0184400341c3d440e000a500a00030b443c28081c20717404680854003ca000d040d54981001c3e203a4a15102d40752004001c910b80840e81440a07080d82d490f036000c0304c29502c024064030100c3e00c0743d03404c00114890000c0464002460501d41036400300d080341013000c07150010800307004d180124507031040e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 973891007 1250 973889757 973889809
    0x50c0d02030a1d0a140d1502220f030b060d0b090f0d0c03050306040b0609060f25020d020405042607060507231606050a0f05011a18 58
    0x6400001404004002e0b6840c2040c2c18401c0300b03054000103000ca80c0c3c6030031050581d418010400b00d0581d00f42c0c40c84001d00801080e56036611840020000e00307110703c42083d400298441d2103c0044a16080d00c2201041c0941c100d14250448816124521020741070a00400210700b0940e0390807551040300e508050b5030004c0b030800340c48050320b8030001e0060b012107206001c06418050700410501c11040d0701a2a1181542e07100006c0c04060110944450740c0482d003049100340c156202c5018059602d000000d0300e0311041502860404045c80015071070311000d00410f104010b0381c81441c0100140e5050345e0105540e2501d00d440c50618520b86c01c940391344902c407031000f40079280e40c0700501382c114010007040c0026201d08106580c4c02c43d255001e080344050450481d030512040f003005141544018900f00191911034a460049031010ba4112051170744504110350180d407503004d02e0f80074040907a45182107150788205610144505040000e220490311001340c034030350b2440e4802d41540c10342c0c20340060036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 973892257 1250 973891007 973891033
    0x307050c011d24010f0b0d09080307080a0501050a030803040f230a0c0e07080711030405091810050606091903020603040b0712020304200f130501140102030f07060b01050c 75
    0x80501c0301420301c5420b2501c000310810f4641c018120304803464a031480700c140342441d462008a40c01014804201ca803101c081c64001062500150301c10300c0f00780ea8a00301400e10410728020360310180d011901c1000f0891040c0042030ba000216a0440d0f8010300c4070050005a00c1c0c5031410555011981d140b18060b22003003a50220041122105130380304040301c4418a407180380d031080380d16050f83c1c4c0c0c400240600c0c4c00680c5090040208458202c041402c49013481d0f074400c001890807504661103a4264043c8801c1c105006041041500b0f030864200280300502d03000c0007080c41806000e11292145120108503c000648589400c0103036401a2420b50b981c80d1600301519070a900799404000107803180d001c04014107139442920b01035980311541044001251103030030802800151440e80c0440e00342700d010103d5480315480840e50019807008207803903241040004050090000880c10f54008002100c418502c03c02144c030b000d540100001030b11540d8000489a5001c0c22800c44074610405681001d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 973893507 1250 973892257 973892263
    0x702030c0915150c250b07020a080f07090e0a0302101a130207141506010302070611070302150601050723031608040e130201120b031903050d050703110307050c011d 72
    0x495a018001c0702c01c8002c240101c1e040c0101003090001040390b80c1c030006d001c08074482c0c00906983e400145082e100a403a10141824001160041c00d0b030795200d0201000080d1032801446aa005403a0252001110640f0065100d0340e003a0b5802c2441940c9170243d00b013404c0c810042c000304d0a400f5110303500704030a10052200a511140c0161400300d002c10780d90050900000b2400c4644229100740c24031501d4010054010350030440003181c100c0c1d1148d0140d0701c1e00b07442034060014a07000398000c0070300700203280d0780010100d4058a520304000c000c00c440760100c1c003410701c40300901c8407038022a050309900804c6c00303045015140248140c04032260401c4103002c850805031050f00e240448c1204607480384040d010340a21800c4009022811303110b914540703030326641e1004c4540c260142c107480b200482c0c0c6206903500803005004902041000c5510729910446200b495440803841c203081001c061003804400044c000101000c082102c0000d8040c2c0004080d003001165181c040c000d0b220f0001110f001d592 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 973894757 1250 973893507 973893517
    0x405090303280e0a06380a23090a060503030405120a0609032015040803040c05030d030c11010b030703290f01050102061b0d0c0e03032a030702030c091515 68
    0x10f12605204103c0e105800c5043c840c8580d601b0442030500300d101062400003000c646100c6950302c880c414a00043c01c0c204049030b164540041c02d002c03c004145c15003001146c03040604140311180c40d2040910441d03d00008503001d450703040b00c401d91036600f11101c49244c040e04000040413103007022614010141c000d03003254500400804800b80c084c98207000349581c0c0c080001c0101207250072030081004184400300564009008480004e0790035150004a85000c130244d040703074002a070703822207003012960008840714051143d000078802a0301c0c6400081e5121114040075141c2c80c441c1c51084201a6441c6480180e05a0070722101542d107021b04080c04898401d12841d80036004620004000980c009440415040722140046c00c100c29803407001c005000041040303092201122807200d1a0340d0410180a0602201d203114500c1000f460000c00003602c82001510a40c0c801d0109800503540442c240021040039100c02401c0d954070f00565117000203180416130020360030b0014103003500340d840c0101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 973896007 1250 973894757 973894763
    0x7020a051908190c0c0e0708040f020f0a03080a030e0a0c0627030318140d0b0604060503011503031701060210050709030f03021c09050315060d14010c09050405090303280e0a 76
    0x1040d041d41c0312503407800350b40100c1fa80800220f40c1000a00021b4500221910490014191211009910300800c100b20604d0308107640201012410030002c40e40760040500640605c4041d001001da9980c45040740c4402d4041c5c1c60a001d065503c004401c0451100d08840c40ca81602110410380e590901500e2080e0508000308034034950303940130403201c400b80e034482c02420340a86900000259a21003d03a4000c0103451251b106131200780c0080e80c0c1d81c0074010304103500c0480745421030b96495890080d042c0303451030f1002c1100e19802001040b181d900030070200702c844000c03840829642d41e0000100d590404540004008000785415101416400202c5244500100c0030080c40b03c40c04800030380d182c004c184100355143e403166410f0f504052400001136001040a880318050892594482c460600101100c02641c1c0d034500c0202d211613846012034004000031ba408003e103051000705580c6138800140210150b0340d4040710a031a0b004070700b40d4640c69038000e41c3c00f0482c0c401850303c0b9648039001c80d6029 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 973897257 1250 973896007 973896023
    0x120e090f060a0b04061209060e07030b090601050f091302150d0c230f0c0c040513150510120f0c0b04180c020d0f030e060703090b07020a051908190c 65
    0x854031400c900f00719000d0340c105807507900055981300f5816029094804003101c484e070700c074160490718003000c0003158055403051002058501e0001445071a01030140c1c80307113104406080410b00a40c03690741246422007440310034101300303580a0011804087d500189035031460340028140d039038042c00b5440180304480c80c1d03035454036032000c020004180e942100300c00f6084100400400400e1403103c402000112420025103160804850004045030000c0300d1810211041151080820135051081c4030482003900b81000141000c2428660403002c500070440443c00700c0c0030030818044608c1120b46460b81c056840401c0310f40b907940d0011183c2042c03040d41c05034002644c0c18900913070725020321801d40c2e1a0798000d0420340c103031003021580540310306045030a041d504e072050381c00b2080c00c0c0102d034441e802540b40400c68048502e4811105000203010904540200b85150005079001c10000e030030500c1541c00100c508040d0410b100c0c02c0c401d4210f5205100c01140308003174007036049440c66072030740d01403030078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 973898507 1250 973897257 973897259
    0x8030c0904200d0e0c04020d1e020301030f0b0603190c1e050607060b060c0307050c0109240e12031303030f02030a0807050f09060d2405060403120e090f060a 69
    0x145000c0000e000000b1031800240f2101486100c95806071440c818088101da018100d09800329080341d01c4040806d000c180c07034805802c2007805601030003800304000602180307107602d5038680b5042040042030041c013041180b80454080d03507042000c003035069128807100a0003869440c1c0700741f4030a032502c03859080c00681c0c0c0d40784c84244491090030701114030142100c1d03c0c0c80c40030703601c0700d00504202a46551156050080a81210b400c101070484188100020001c41503c0070001d050740d850f992142540107910091f100340c5c0d12104c6540b408207459818503590b021107020004501d6210b40c140c1c44468030012a0121400708454904003c4034020307141c0380d400d5484403c040f40c8a2048191b4200030414080210704054400d00c000e01c1c03100d4080441c181080d10ba1000140640d22000c40050190b44440d001660f078080c8011008600840b1044041c0e00c5142002048090041d4440908202d01200340080b00794094031181e103d4900051880301785251500c40a00d2485040c0d034254040e040b9888 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 973899757 1250 973898507 973898531
    0x20a031b1b0f02150c0708060a0506031015330c021804110907080f06012102030a0605090709031202011a060c0f0616030f1b0507050a08030c0904 64
    0x107614018120401c0300c80c0c020001e61500800d03038891100c01ca800103500704205405502010103030021020440180011515001100d854040c0190046022914003030900080b5500051103019000f1405000726040d55000e5465181e545a5880025600c2552a8001900031440006c01e41300312100103003c902d0700c040e8011505840032b0302d0001c0d080081150154030705042408099803083c42000c4422104030071070003042c15804142c5680340400c50150034412565401810f04e54032080a10703201e003142d41d040d0b1000e00804400c0c0c10119030340341c0c00030108000440e1a00000301524014048010320b0800d60380041041a90b4802035880c0b8841030100281daa106000342040c02003901094407401410300c0030464260b008104410040c81454100c1110315014407102c2c2c03244068294019200c5000c540150540741d01c0b0140281c0280b0b803a441900d840d040c11030140c3d806405180c040d40f01d5181e490800c0c54065071010241401f00c0201c02c0001c180714240003800c88a00941e014400108008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 973901007 1250 973899757 973899767
    0x406151403060d0f06060513090209070810091d1e100b090601111c02010c0e03010608070b070c030b01121106090f061617091f080402060f0d020a031b 66
    0x1845040d0300640c20403c81c0c1c00704000d0410b10702070f5070042100007501075842002035840e5205540c0c0440068135031a402d015860b140e00722540c05029030a00031024504103003204103282c114000d031514207a0f58147c00030300e8142c00c1d405c2d0b00c4a20100742252400000c240c000407211013840201a10361140c01c00240b100f18940c0030f01900420b029040c82d2164960200546186c2d540d820b14656038400d2030a601c80003410204841b840120030b40002a000710300010040c002d840420f0b06070b000c0e0381819410050250700041000071102c05007041910f0303040620b00100d01000070f60001c3d00c0741124034004141424070300c007140c0710103100e0410300407225490003e10005002c4c441d2440c1e408a914110704c0701d01e0500c42c0040c14000300700d541181c4c1c0700845555025070200304a03001c4840c00380100d000e03135603801c08016222280c0e0048180014164607910005c2090000038030090048074046a902145112501580d14a00e003000040d901d408840c2c074014006c1074605c1c0200110903040d8280c02d079841c015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 973902257 1250 973901007 973901011
    0x4181b12020904020706091b050301020705060411120609030a030f0b130b010912030206010e0c09030a080702060f0a020307060f051603051b0c0a05010c0f05030105120c0406151403 79
    0x5034558020310105200d108009400082c0e0700c0c2e400640804c078070702c0042c80d0781c454054a18402d00c02503403160040c090601503000c05030401402a071041007a0004100700281481e40306601000c50520704080e00c0200780015821004483c0911480050000c2200048041d0882c200c8982d41000f95400c418030440c1a0717896071010580081c21a9007007812075a01e50088094480103050641c1042c0d91100103010031a402c0106a0042c1c01c007070014851084600e80701354101d0304100c150fa040140d007900107501c0d142c00910040201d140001e1039011902c8081c10799108840c020f2805851b0364940401030f40381c1c2d1150390100c4001d03151540500c0c1c0748038288100340c01082044c11103600c2011450094001785805403016211940e042e4585034460740400050600942d203401030700a8400a160040c290385d060a559801d1080502d40f04000070750080941e411a00b08803000e20210283d5001e241c100500c1c41012a0050f00f00a03001c1a485442000d0a03c0c5030706541e600c081f100c6170069048150700003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 973903507 1250 973902257 973902311
    0xa0f150e0c070f060209040e030d0e0c0a030b07230d05010305060f01060210230903040501140a050f071137122613030c060806090a200418 61
    0x14940d10740004c00c91660207000384420107400045d0081500000c42d145400c81025407014640741c4002c07010b480c4081c000041c01100540340200658259039550380c2c0090010048410040404441d8126040b02e8a0140b82c9000400495030341c5c585041418000c0c0009010a07103261051502040e100c51411071a64105c40e123036405400725000404800c000341c441041d030b044040d07800c100c25a07000384607401c0c01800703000001d000f10350742c51426001601c1030032072440e082c202c80b03010321403001d00f96000000c48100c0511030a50607917030f21040c40d14140c4804102e201c01d03003005510345800400074103400c0c0c9440f00e00868651001c40c40440c01d2402c0a40c119014501c002d44807040c2580000d20800000d8041c0b10a0301183c1a81c0d0b11080c10b100120340201c52620319509007014108240034102c2846005800145401c0545251500220301c0441025142e101034a66a940c50808105d08080302c455032411480c0660381c4940c2d90b200303e41141d0640141c00c0d949803030035200407043e050045a440180344 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 973904757 1250 973903507 973903523
    0xe030a030f030515090c090415030809010c03032706290909032101030c090209060a110705031b030606030a0317040c09060b0a17010605070b0a0f150e0c07 68
    0x91001e100320058a005410340e106030960340702c0708800c2d40d20a40c64900c6130b9150510242c54110240800c1b0942d102403140c441200c22040e0705202040221040301c0c1a54400e08240800c59101c2c5400c0b0010601c54140d0640307030080d2400200c40502800b0341c0d2400a0007030300280114100340f038450841c0d00f078122010303950f00190700079200d090500010440e4000071704015a07080c1100008180091100705030006020450071006004220500b64450042c0450f11011400c000003000400c3c41c5105103a002c1090206c144401115078004000c0103001c1c04000d401d442c0d0352440d0000006028520307032282440303801010000b400ca4200007847c1d03008250542c0e507040800d00a14084240c405001d041034600200340b060104100256025000060400790300c42039642548400050140c4800d5103001d1301031034040300412065038804249c5000503005640e95034103840d041080d00042ca24035140c14050f60401c10340c41e030101c505103454811244100e4066106603211003080e15a44103032800280301071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 973906007 1250 973904757 973904777
    0xc0e0a0b040b0d110c0312370207110a090f1d0307030507031124100e24030109141905030a0e0f1f110316030f090e040f030e030a03 58
    0x18450380128203011013030f6181350310304880f41c1c4520742940c1c00202d4107a15255800b0038014081024407460865542654888480c007021003460080402c2a80c4002038203600440c81c03409201c55802c01001d881130003000070005558948214014125403c15000d10078505001c0308480c141c03070101011400700315009181741005669003528990048030303040e810440e84000088046a041140e162041501118001e1003041114a04d010031001802c0340184202442e040080409402c640c42d0030050705021706120740d4008040382e407511400d240c1164150301380001941488000c0320810b06801c4d03810181d6229a549200d00d0b8241001c0f1240103156500412100302d050380f080401d00300461000300800d4292032400006070a507100c00d18071450003246000034050071500507041030986081c1c000a142020446185814a079081041c045d051140568074040390a11a00782007024080340d40700b4484500b0503092081b01b400d2010800c80100706444426192440c002a40c450419419078540d07d0f90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 973907257 1250 973906007 973906027
    0x20f010e070e0c04090207030816110c01260109060518010b090d11060c010b0310060b04031b0e040305041e03021e011110020306090114011e120c0e0a0b040b 69
    0x140d80101003c1079000c00303000c0800c00b0f0509000034442c650207030b0f4580d40c03241400074541200840c103d0724241484401182004203480200d20b04400c2c0d00700b4241110041a25065607280c0e210014100c01d00004810001c0f07405001ba070f200034180c0b201901c10140108108240301e08a040a00a081070302d401402204620b2a1409400d00414031403c3c0d101039941e114000700300c85810200101e040c17a512002051240d0038208002210140c0a000c1482503605d42040001e43c0d100ea0b010140140481c01c84100c12401900c00d41c500070079a000c2ca220061515060041c4960086d008184800d14410950400800304817201800c3d41d800408180018400d645064030824400b0403035414420b9160034600310310002c1c844404c04410510300503030b4034a0180200481514160010000040e9141803544241d078011000768000115041c0d20440c024420410354043c940c0000305119941424074110706140d0203d000c01107003c040e80c10718030150b100c0f00590080d0103107004035145a00240001400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 973908507 1250 973907257 973907279
    0xe070510080a050402010c020907020c01030b060a0e01030e031e190810050d030e0a06030f0b0901030b182b0318030527040e3a03050606091f020f010e07 67
    0x345c8141007041b4250116030104902c1c400888103203000d41c100d200f680b00c5a50305130058030180a002c40b2071600e0b20f45080340180c400c2d00d24142241c10551703100309000c00301c1d0703007001100e54000003001d42c650014940012645668081800130b50031040c01452502d6190180381032034026242140341c0c0c8030700ca0500f070038482c00705006c080a40c100454a02c1e008007545406040601505e0b2b160390104208a85110403010b83d080c0311125405181c290340100081030348000b0395900000411101051206101c00d10703854804610801d00844100d2414081c03401c0701004e408034281101e850030f1050b9520446e290341190449503000d0b000c91420898800580203c04100100c6070820386001e021440750008203003100d4030350345410800e6100000b010030803d0b01840c01c801c500100c0c0d44140e2000031000049840c3c5460902d02000d1580300c80c04038103a59034600589444407800303416000b924021200a110310b07514000c0b08005030041596814018406000f40d60401e103000b8000c0c104207103000440e241d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 973909757 1250 973908507 973908511
    0x1141b0a1b080d0509030903070e090c0108040c090e06041505040f080f0408031305150f19091502100c0e010503011811131409130b0a020c010606030e070510080a05 72
    0x1507940041022a80d6440f0501c11240102001700042d41c480509000741403030007455400c686603400c01b403800c000c0e1f004070004140000d44828130300a403554039946040107019841c0e400c0040701d203091140d5006c07111400504039100314042c500a0900c495840800782c1100c01c16600500700c0940c5510390030210300038800805440c0c4075070a0076072500d40e41c1c0195504540111484000300c0d6281d120070001403030041501840403d000c24614504121225000f20038403480404007007a1a0003030300902010f004040c2d2000030400d5810043d62508240b9009460f0000b10b107148001030726101c200c10b401031103200340007003110040c4c50712031444e42088100101003500c507178121511038452a420320384203c11006880036103642c00c441108142004811111007810348000c81c05500d0510400c15016042c802c00b11075a500040ca40d030b5144c80b003030038010203442140000d0100391308103800010a143e050380402d9620701c40c1c40603140a42d440f0410130a1500c00e04501500040800000c2080010260311182d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 973911007 1250 973909757 973909763
    0x2202030c0406030b2d0a09020a090c051c290409080a0203030702060a1a100201200405090a0506031e0708010906020903061b22050301141b0a1b 63
    0x100d2814051001505480450300129013000044060140302845030074071902e10040321039a1226010380c0d052101c16810000c000c90301d030a4480d201c6100b55250000c07400043c1c0049001444004101d2a000d0801d50050041b518025810003480490781c2480c46543c22082402ca101030600804407000144121141549035020b40d5441d210380004181c4401448070f0180782e005141c40e4901034902a0400e035005022801c00d0307040a0030340e1080064800792452420044841c181c1014603480c0c1280107043c0180c03c10804480e2800e030b0120841c1c800d0183c41150760454017601d590b0703240f02464003a03800c103881c0e007501540322002145041c200a03810414035030809003201d501542d40c0b54480d00350748100c4415508280d00040d026120304040c8141c9601444542c212854104103c48031416480b40011600b1002d280c503d0100e41c641c0280b44210040c000140213121006210620b00b030880000c0e1507296064142300624502c22080c481500e04007100c0d500c8031650301e603000f1440008a03000d10011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 973912257 1250 973911007 973911013
    0xa0b0c0d14011418061005031f0807080f0a020d02091e1617100e06010302040512030405181006050d020702040504060504140327011b0503130e220203 66
    0x701d14480c0340301402802261034250700001c1c00000d010226a071412404140c0003100300300001d9454244207031040000701c0c0340c2280e490360f41c0801d4046918040c0d883c03444440290b030b000600d20300001012401e1f9032944027695030500000411540c0c40034140c1d4000d4002e0341d084400303405841c0488030594812190300074440c180d61007803491070f0400c0c0d088174140f8000e080e055101c2544d41e03000607510075500314410620220f0070007a5001000c030b1454480c10014400c0c040010f20284d110340c0544000307102c0036080000c540240305017551242c20030301031107008902108601d06440015104a809141d008010500b06814040202d81ca6440310035001a002d400b0050b410051300c0d64400c05200b68000c0310005404c2c10319243c04e1507150b118100c003030f0140c1e0040c415403100e02c1302007856071540c210000b20b10b1a4244000016610085802c401c030303031020001500f42047c440d0202c000c1c1100040c03403940c030212039105c3e500b5001c0c440041c5c0d07000c0301510f500b040110164604a0f0305080b03441c001012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 973913507 1250 973912257 973912271
    0x6190918182901090e070e0601360803071101020106180c0c1707050c030c0f0405040212032b020a05071b080111070308060307052b1a0412020a0b0c0d 66
    0x80721142c1d6020303800058240d40c0e500a50115140134058a0040c06d0700180310074503400c00b1800288800980700c0555103c05041900018504240540d0f00000034000b80c11020183d89141460303d0781c010304000d4846240004221b5580c2d841846030304256000443c1003148005103056640040102c54402820300a40c070b070420003c900340002401e071400c00d0025965903143c41e407803c0e07800c29080d80c42c03c6000364407869420005540c0d19500c145031b0501a1800031b42a074542c000640c49203401309182d6a80c0c0400509144a9400e0b00145030780c005030ad0000300420782e01c5d840d8079004c0b0701c80c603450f580c0080d00c24001a0002002c291000f141c00e01e4540c104800c1303a40300d002c01801c50307080e0440110421000107c4404240c0c2208485a0080d0114054041d076481c2c040800c100b44214400140501e4650941d00449405035118524154122041881c1141100c818001d0035000380d41c02da074000c42c1c0c41d440d0602c0910000d40045001e900c0100b9102540311603d06d034459802c1440320840090301c54107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 973914757 1250 973913507 973913573
    0x301180e12040501030c09061e051b030403030f02030a020307080c100c081006030b03100225060933020c03090d0b061804051b0619091818 61
    0x40308500189a0341e56a44038036140016080f076189000c0c0c3d100f480f41c0c0d600100f09440e0002071041804c2400110342c00c240d0315a280446551080841014400ea41c150381030071090740000c080c1095911035207800d261513140443c00e0740c4da03000c4d140080005920400c01e078800a01500f014000381c1c416402111310090499030150180d07503c1b40a0103002076916010041c80c803520b40c0e01d6100510541c241048100d6860002c203403102c612002c01803c194002403034010450344c00d41603a0406000206410940e00a440d02502a110301c44050b100d40024400440300d5103406124481000740d40301960242c42000c01018020350800c961002c9a40020300c2035081c42e48075003d450030717580d105e04132200051401e041001a8020b42d24a000d20f6035840c001003000207040004c6442c1e00f44171441c0b40c0050802c1100c000b402510803040c41100e90b20300e40d032100181d59000265542560103e1001c40d61099460007404119043e21b41248009511002c403003020a07d9a102ea40b0610300400075a841c01c2e091003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 973916007 1250 973914757 973914763
    0x270b1906080d03090b06010914060307050418061d131403040807060909180203030406030b0d1509020103052a07021813050c01020d0804020402090d170903010615050301180e 76
    0x125825011035110f10b813100411455220156018009080c0301e0006402d2041d202441403240852600882c030010101d0b80141c0500c00303507001040c0d031420701d604070079030001e103c40585082d105030010045504044000d01120040c0d8520680e0300b8100401c565a460300d0f286103500540501c000240420880820241d6003441000058130080c0c903a0a4410b03d02008901155803030040d445585066840600050f40c011044070100d4520b07140c0416520003841c00660900d45401008100804491421080401c0c030b810008129000f40c03410402951951400c40550130040c0110844200060703400d441503050401500110b4005001e09030000080e403030b803074080d8005440103034440081b00c00b0300e82045020401d54600c541c0c284041e2034600c24054000d08450300c0508000e205a40202d60103000743c0780c17400008410f5410818044c0440c100c14400d00c21680700010300c6010f9400c0a40100c1c07940031521085008a0940d0354080c60f50b0303c8c3c03034002e98040040050080d81c1988640000004907410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 973917257 1250 973916007 973916023
    0xf21061d01020c071e180b0a0905190614060715092109080309060d0e0105040c1d090303180a06051005010908010e0607030e010b0310270b190608 64
    0x16100041c0d07034001040199161012a90100d0385071803010345c45c1300c0714012900e081022500c0172080301d9130506c00002c5007000340140035007070707a00645045000100b007d480e800c01c50248020742c1f807440f100000403162000340c6140d80240b000212107018107080c0b901344040208061400740c1c2c6913010030b0106500712015940c3c540c070251000901c00d10071120740042400d040980c1e1901d41003404c0194540641c1c1b64980c0280d280403031055a0125614103100c0c245c0d000a4030741e02e0702c04002c00030b40c580b038500308034012103502642d003280800e40720294605182e1b105450141c0702160007142143d907003100140f040e040300302090803a0b0094005000c0011200d000c1d00b40108011640000e50f6030603c40010a48501c0c0d50050f0ba09030304040007110866000719025800818900d4049410749040c00c1140c09080d50b003200c0c6406208001803646564a6a400820382d00c802a22082d9440201c01c08020400d090f00400b402c000782c1500407811141e881051422080400107011540956035040d46040c6504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 973918507 1250 973917257 973917311
    0x17010b0306030c061309110708071203060b0a090b0318191b03031b0206040f08010e0f01090206220f0801090b070f0203040306051008030301030302030c070f2106 71
    0x4048144041c0b458240a41402c812082d24802d0505c9905003103030740d489505115080c2050b0342c0e40d5004170300c140101d00311b90a0035044040c0f00d59030703035007807610050005099412200083c6019008928030308008100c0f030b030322501070352130342c3d2454146004843c5c60b520290420420342d406020750441c920381800803420100000f0003031181a801c60a207044440400616400c807290402e800784006a0019031281d1100d032407000000440301240701042203440b4a41000c1090000000300140144054103c1c03020345d291f680580c5c0c0e80d00c00703002e8003500740d403000c42c0001d40c8034405110380d006560403d042224106244103400c0c1c00c176a034600d03005241020316002614680d440340c880ba0140004101fa480d08401c3c80e14120b03555000c003040c0203440e4019400f005200326101c1e004625005002415000035024540960359a07503500d190280d5298000714800e011409a50780c0021551540e81c03400702160b0042d03003200580403644141030410522808101e513482c0d501c94806201000000a001d08480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 973919757 1250 973918507 973918529
    0x60f20071706040501110f0a08040f140a020f190501110109060218010305060f100c0609050717070e0601050f0c0a0b010314100209130c1b0b010f050621071701 70
    0x615060541c21b5400c05030702100d004804000e0040350f4840d8200300c13608030003945055250b5403641c0c50f201520100f860805442154058600d218040303011400900d407510880c0e221f10710a010100b03201c21003440803142000f4404000003000194020281e8200010008000045202e0b0f03a6807120100d030000750740351000a42800982084c1c0d41c043c440e00b50042c0c1d088818a0f00c2c2000caa00041210700702d4101c000030424480050010401c0c039402c5011417683c440700380d0300015202c03401c80314904800080d10443d071140398000100790804901c80d40c044d10303040c0e503001c1c07601c2c503064500e048a0380501951441c0d13214100000e40407a00040c4003501039071041303050322003205080701550301d0081001008822a48108210001d954035440d4443c038003100b884003c509444400001c0e20051071500c05001c0440186003000100b1406005190580c0c1d12801400c500c182c0720001d001050090100c02c8502070144061800003c05008885a11083c2490201c070007825101c1001e00e1400c3c281d0041511003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 973920863 1106 973919757 973919761
    0x610031817070b010e06090709060206043f0906020c0f0915030a05060601031b05090904080c030a02030c0f03030417070201020c060c1501060f20071706 67
    0x1a4014000050f10340c0d44030100c2d089a0000c4940318440c815110001e05058080d100102c00e590080d8010105a504c960754041d50088a10280281907514012040000135052f0401e04500800300360031103041800101030040080c4d42c0002c0e043d074001940c1000030380ca544071710b080c10100450f01d0a41c2911409012604e43c13202030003180e014080c3c5000c0809004002600300c2c004c0c0c0c000e9a081100c500a844004a0803401303e070500001a020480e80c45d00345451040950000d0052020f40d1400090f4210b10303143d68802c1c10980c01503000880c9000c00300a05105940056948030051480c51401d55610030308205148004441d13030401089002c15a4801c00c9951305031400a00340c00d940391240420301d0b40c3c030072081c0c4260200c1907503200081101d521821050b0f0014000d9110700c2c0380c0c1244403a0950b8035000c0d500d484141481408400242d055075000b411410710314000c043c040c98 = true := by decide +kernel

theorem cover : BRFrame.Cov 973741007 973920863 := by
  have h0 := BRFrame.cov_init 973741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 973741007 ≤ n) (h2 : n < 973920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
