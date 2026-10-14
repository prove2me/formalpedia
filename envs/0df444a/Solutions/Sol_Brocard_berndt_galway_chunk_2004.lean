-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:37.6103+00:00
-- url     : https://prove2.me/submissions/05d80566-24f7-4a7b-9262-1394a455dc04

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 360251798 ≤ n < 360431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 360253048 1250 360251798 360251813
    0xe030307141b0d030905010b040608030d0506220c1b02300a050c0f01020d0206010909020a15110d05160f020303070c0b04090c030b09040f020a08060c0c0705090103 72
    0x41c03400d654103000091a00780c40000700c80031511054000068403481520300c800100541a005402d075425820030140c13003107510303081c403c440c101c5003068000c41c9400c98251000d130252a008104da5404581c2d000c0002c50000404028110200514400611014140c0300a48030b0340405480c00e841c80c01c1204000300607220542e204181310209050044201c00002c80810300d07041e0400000b011b406440d141c00108540010420200e01c0704591a1011440d80801240c1d40c0041d08030004c0164882030042207440710580c01414030034000b41010340e42c5502e5440c0c1a42c544519007400c4002801040c0039101a4414400c040d0701004074508603140015080310764002d50001c0e00082c004451601c1004210358040044690703032076001d6030720b42c0407503915960101544c04c1440341042d00e904bc0710f03000040d42c0c401e125680c42c0890007004022a031715161641050300c14a0704040743c001c03000f09e0001c0b07010101004000d11818030303113070756994680d541504282025400c1e4007480c010f0010700014000034450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 360254298 1250 360253048 360253067
    0x41071e0306051c11030d0c0605010843060e090a1103070e010e04180515010f0b03150d1b050904050a0204020a121a18060d02060a020102040513020705010e030307 71
    0x1c81284000035000e410400a500303070480c50713280d0502c110f8140c1e00481c1d4000d01c4404055004a5081140ba0303681c040054681940c6940403803008910012151014100414a88601c00009480e0018042000300c0b48007021640c010340089813080f04180500d160042c01c0d01c0e48101c1940c003e11254582c3c011080c1c0710b002c0a0194002e00c49100c186420691043c64130003a2608002c2c000d110025204100146a42010301c05841c10f00400d04100005142c110340385040302c000e034101030003042c07814002840c1a0009406043c0c03200f07010240030301c0c0b82d40b43c0c9100c11026004122621748861804541010350a0b141e014500403460b490810001c144c3c0401c9a55550380c050f1800b40e601c8000c243d003240e64a0644582d01030706882d200721003003540701e0000c0f0001c00340410784a8551004002403d04000c0300100c480d1580a42401024001800c24001401c0d9541c0070b1300015040944500c00240c0150324010381c160b0003503000ca901d40a00c4824000c40d58036090707140103113107503051240f0f00030300c80c101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 360255548 1250 360254298 360254329
    0x40306024914040807120206040308040b0c090303030f07110111041a070c080c190e04021003021c230c0403060e15090a03030b010341071e030605 64
    0x20701c8881109014442d00241441d0000008a80c81407916207442c58954000752000d0b00e0408150400b0b09585000180c901c0c01140c241d22502e9982c1e0b6240c0d11003100c040000c1c11900c207414203000c0f140ca80e0714104013941c000c042d01c21507820949050340006200350014450700f80182c2c100110205142290011a07050b2912500f106900e9083d0022030800751040030b400400c1c44070b100c4000900c1210100d141e1104107c00c9031606005d180d541ca14140340d0030380d070081c40140c11140000c240146001c0d4010090030155040243c1040c0e00d0412206041107014100b00c4410f03219051125103000d01700d42c14800b81d2100e1480a4641004040c400c414011404010082c43c0c0d2010041c2c6040c10810401c001c03241c0501c01d507401860130b136130100e0f00e5145080080340401d003011060105917029009020444074105500c0c80c50f8200c1c0040b041e03e00340916080805032924000d0b0b80806513a5020003031060410362182e6200003616548060654268100d03d02010f2400e507050000340d58032003000f801c600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 360256798 1250 360255548 360255667
    0xd050a0c1d060f1e070b07021005011809032015310615061715101202121305100612030507050f06010e190e0d050c1204030602 56
    0x400c012490004c00107010151440d2010916000308102058154818401035007078035156914441c0f10016980d0a000e00449441c95003150132031600e403580450100c038080e00c0c0210041404001901c40d00f500e0525048560700900b0482e140d44250510542d00224507602074001c1d000008191410b80d005924500602c0c001da901680c103102007034001c6d14100300c0e80c036805200c0641e204d1010301504600300d602d440c03150f00c0c18000344d042406003c0a506031030010b80300343d0550011100440c1c1c0c2100d00da41c607080c800c0d401e009c481c0002c0f2035080f81611031102c031101d48116403200c3c103008d031400c21518413108890b400c2907018051940f4000d108002142d05040c86519514a4075005040c81e5204803072110034401c405c00041d09180044085014110768814901c2c000890480701040e101e90210401d115404044580c8840c6e2280c0001e080840985c8192414814202e04803640c80d80140e10940e405600400c0c4404031540b407e2044c280140703000c0d0b40c0f1000a182d68070610303a005411b0185103441 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 360258048 1250 360256798 360256807
    0x9151014030a080a02030405040b01030e0606131107080a021213060509010917010f0605040c020a0b0a0e1902030d030b100f090801020a09140306010e1602030d050a0c1d060f 76
    0x5032020860b0038041a80095040d450f0044241e0003562a0000d10850f44a503080006100d00365000784101400b00150001034840769445400303020304241961190851603030b03149900140d0b401d00c000036002403846140110740e144407692000b840c0000300000c0300b002903410030240a203520250000c000302d82c1c03107003441030329640c0850042e40c101025074007000d8600c10f045a40100c403e0194850010381c0750a480c204001c0b621042400103c404444241015900002000c000300e100a00341a40c001c844910110b10351080a04160401090b4800445490400e510840c114030341880045101021407604105410400001403032006102c510601401400d070346151802d489900c5080141003560300079559601040e1009207603451a03c00d02d00e81c0e19110880c0102840c0106107107040f80c1010820002a0b1907016200c0314016080441c1001d500c002c0111541903074981c0a0030340325408020300000c182c0680c07000030b0103540e6580d00e2000361005070f003619200c0780c2c1c3d0b002c1580c60841d01c10b94420f488 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 360259298 1250 360258048 360258089
    0x10e0c041205030d020c0609210a0c02120d0210061505041202011806020304062c1207030501051302031c050d0b1203030103060c09090b010905041a0a0e091510 70
    0x42d440b0f24424401110700014221000c06c1000074145d0040f01804111110490440718081d064005204a0201340c6010040111014810041840a04c1c0010452113740a80c03075421490300c0c0280080d24050380110802c0340700e1000d0740c401c140060440e07020040c003400464000030801c1c4114064070b1680c1c1610b1058006591041612600b074090194440f84003a0b1101c00c080d6803034100e80700b9800000c10661180d00003c070346076407071640e0f0744002c01c1c0d081c540c142400c100514801d2940713502c42c1d58401c100001000c284240a054040c141d40c84404e401854203006050400b40801d02451110007842c8181c10021b030b00004a800000c400c130710028030100240e0018101d0402a0b0380c138007040c0b00c003000102c140801e980c000c2c1111010ba480c0d240030300356550945803c1d0b945c1c034144a4007080258404000f0760409800ca00c03802c1c401c03403c2c2010741130042c40000c0c1d1a0862500400035010082c010001c18940400090020015001e0200036502d408000003400741c050740906c2e000f61820a064030103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 360260548 1250 360259298 360259303
    0x50105150a0906120f0e060612011a060a020f07060915170a020f04090603110102061303020d0c0c050d0c03030e041401031115070305030f010614070b060604081506030105010e0c041205 81
    0x504e8042e40e800f4081e04540d03114851f65004160f0b0050300c20050640d06c000020340510403040c1405070508a40303d0f000040b400c10405403c041030300b00c20350082002c011807240301070120501500554070359820303c60400004c001006c03100241c071b005110741c643c100c6002140c401c818a90000ca42c500140c0c2d20740388048104410301440d03012442c042e04060f008010400c0c08414905415001e030708480d4980c0d90031090140503540c1c0080680540c0103030003100320161080e000031045600401c440f105841d030341d0010405401054209441c002e207c18420b108156104d1490041c01a08403014000088404001c500d040e6061000130308404211101c0c00f45900d40c600420243c0d46000411900c0343c00310306002c0d00e198811034400b018202290b00124090303000e00710091106400e051424201804e5903144c1c61b100c5c4010f8085648000c05110011304030070b08000d143d1210000c0e001d100224140704041c1802d460041c0c11034202e11303c0f41010800500c3d844002c0d1400c4a024022040d40e01a407070030a2030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 360261798 1250 360260548 360260561
    0x140106080c19140c0a140105040b040b061f0206060301110f04090f0b040203270319260a0c09080c1c0807020d0b060310050925080d03050105150a090612 67
    0x124107040c04031381038980e510003003902c055150054a03620030681c4540909800c80d61b04440003090300701810080744c0401d6035402000d60100700a455a80540c45840c2e1300c540c101d01d00300e00380006034811020410f0b00d0600703001e40c10550043c44141401c00210199100e1a8001c0e8040c64030784554545040320100c0654000103140d19015204640e05d00304a115046000d2a070340c1305801142c9000e21039240c1c00c100108541c0201140185070000c00002101190704418804940b000010824551040304c101c1c880120302800c1e056100140501d02010702a064608550182e413064100008030f04c10fa071103005414120900600a502c1200701d1454524140e001d907440280d0001b509000b00301c10805079a202e98018107080707088503150050419000c1c1a19000c4074120451342104010b4400700041804481090303002c000c12080f582d480d100d460389001c1c034010111000a844000410481c01c00c0d00361690305001032010b0525119890f40041c122004038801c1008110300315401c841040d00552004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 360263048 1250 360261798 360261827
    0xc04031203150b0d090606090b0a0e010501050a0c08130602030316180314070b0a030903110129180415060509040b010b0313081305041527020f040801140106080c19 72
    0x40010303a0722000250002c0c20483c2403a401892b0007100400ea03205500d01281c100e0303005944446c601400e49004940d0b281e0f440f817040307035000814403c6ca00f007105a1800c01c806004298011030b00c902c2c100c00c000584191641031074050000f014a00900300012280403001d8135001030100e031104010035031881c60020551300a519400f00420103d144544c150400c52105029940311030070b00700362007810b50894611140c2c10035035894010285041036024888c0010100c0011321407442c90000300807882ca8203d049400b2954008408455041c04003d841420046d10060780e441c4000c0c603050b980e001c0c4e040e0703047c05100d10078030f000f00002d154202e031018400b05041c0e1141d541c44d00c49040c5c48007101d4410351406228803940c1440c0c1080785d86003410240300704032122199000d400c1d00084510710101e4042c1100306480356020082c201e43e00300c04900410042110070000174095110b005070400420068005400700401042071001865420b01541c90306038401c1d080704240d0750440420b6074a4a10840705 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 360264298 1250 360263048 360263051
    0x12050a0b060403060b01051902150c03070c12030e1504022b030318080c011509020c07060e0307050901080307110402090f010305060d020406090213080a02030607080c04030b0c04031203150b0d0906 86
    0x4808d01c4d0340c041141e41000d440382c006210141c4410035020100d0101712003550014851718580303804904402c00850f4090840d00740044c0c03103d40c101410f410b01d24100761180302110503106000843c00c041c0d42c0c0d584400c20303d0880420303100c503a4000020700090311801404054440000e11030b1105601c1103800c42961040240d559400b40030046c501a210580e044210010b001000050400c5207008a405204020b4050400982010000e54000303001e100c0d0640c16106000c1301090315150059124042c1c410b0100031900c960541c9451525200e426092034000e034014030103054240c07140902c0d070800040c00d080104442c3d507402d000c950418103140000e94001c1c2130110000f070040d610f0b40100310b00c480741a084010f0300c5d220410f003540c910081000a405511820015001070301c1394040a0300034101001c1c40d4a81992515008200e11007512071480c00c00c40001c0800802200d0218070844001c942800d00000d511080b091882d58080c1c441d00900c048006040003c8024a500c11441d66901000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 360265548 1250 360264298 360264337
    0x11060f120a0f0506010807020309060a120501091d0a150f0212040303061502070e010b09011404030813350a1e0c05010804080405010e0d0602070312050a0b060403060b0105 75
    0x78220250a2031120441098648030200b0754652081c50010320620341c5400451400c40c0d8003080c80b110354000e80601c420400c54022449600d4041d008090092007a08000708649001d0450300c43c0d10445010300c410242d00803081d80c0009003500c0100d0003002c0501c2e0380022070300c01464070310001e445045040007124400704108400c05030541d1005096640700818030b01c0c01086200141d903141e0f001c0c0110941c0b102100010000e8810602c000c0000d180180b43c250143c40d46215805205e8000d500100c40703a00c4080303010380001e4040c1d2060002045a00100c040030014460995101c2034802c00d0a550003071400c14603091482c00300803040c04241c0c0030741c1448000c08454286995449105000c80b4007100d6000c0004156104c0c3d001c0364001c1c0e4105804c03601d8035103000300540d402e604902d141074101c502000c81d2004100b0610142c10045c2c081d84408540c4103054141c1403c0f128020b008200d01c1e41340c151b4003051500d0703600c00e850541b64000c20000300c090841006a43e240100b002140620b0000417 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 360266798 1250 360265548 360265561
    0x6080d09080601120803150a0b0313060c0504123203040906080319080714030a050708071d0f0402041a040303020c01080609130f12050a020f0a11060f12 67
    0x15100485244506681407a62110744910500700c2c0040040c14014040c4041000140c034021f40100d00381000741140c042d1035840c890104107800840c1c1803c880401390850b84148143e03409840340500c0d2a2030002d01d09410461041d03034241c5031f0000540094a00c003402000c40d2070480c812400081440524410101c0d51281e080d0b5a40c001c6c055858503038144640020804000410b43d641601f2104005c664541600030480300c0c0100280070004100801c6040e00c2e4420f1588015800317400080c42c086154a090900075010341400350090007000802103c60270341141d6003c0400707581c10101c600e200c059107444005806400340343c100700401c219074019402d91180c1c41c801001164031a07000e03a801c00441c0c60064032880411212960091001800580c8403d10100c1d020700151040c10110181890758403038618035080410000b001c0342c0002760566020f83c0400140b0f0702c802c5100014107510000d80c0d600718420b041c403c1c2450103a10042030130b17529640d480f81628008060440c42c8070701441c001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 360268048 1250 360266798 360266807
    0xb03070f05030f070f030f05030d0c030f0b2202181e0306010b13060e0607050708012403050d05131707061d030618010921023d06080d 59
    0x1d2061500c01d201c0c41c0707921400c06102294101c121181c10910400311407958482503c103032141942103030280001c01c40501c4c00880e5101c0c0c0f00b0107442e1603900007a0203540901d40300440d00800314541c07148156120944800c480c40c046504100410b440150b1965058480a81c080103e8407656501004107940c11300f0791032425600904458086041b501c02c1e0740c0e07503481d00610344503070001c5155440c0803c0f02800002d0240c00005035901c0080c0034075103001d4294407640c0c28080c0603002111342c0d945888403076145048010301144000c04d6a03400390122851581c515903103030580040c00007808408100318184d14035101d50000203206070701d0f8490441016084540d00d4816902801010404029000121848525003101c00c0350003c1c00a00007074032810900e40c0005d00501c003000aa648076039070040080c0b40503000c070281101c8803100f00010620544040d080c8a12610b00c0e45d04c0803141210000c08041000e0541030b0200c1d0b0302e424002c807001d2290405c0c0070f05441e0b00440040d200742040000d21070ba02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 360269298 1250 360268048 360268079
    0x120f1c0e060412050c0d0312050c210f070e1f0e100819020c03070201030b0418080910050c06130219080a020f01080106140d0e070e09070e040c0e07030b0307 69
    0x4c60568146088420800081300d0030410082c0014002400741e00301860194400c41e000f19111f4102d5081a020141350404500d007a521114a41e810605100300c2c200156502e5410044d10305000203145803000210b60301e8100d10301000110159002c03a2900180141d06004d42c2c0343c0080e003120507a03103103040040d14112064031490f621680d414046404012584213442040701010095854080030740c0044014210080070a540260340703101d8a540107000440c10001d80b0b104188954842001c2406c200a402c00700400c0d10900030104544020745d040801c84592141c82940c84034078421460000c20003d00e08035035014a00c5c015a180407500000004241d00030070b200b200d800450300348007001140d21041c01e200e0381b00490400b0488800c00b12030440500740120b11640700242c151945d13000745241c100c03203510410010312058240036034030006100250203090801c51082107400c0c2540d4081c2142440c0c441c810381840c20301c0100d031f4498420f03008220034060080c2250200740e205c6208103410307080c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 360270548 1250 360269298 360269303
    0x19110d09050a0506010519060e0301150906260604080f16030903020f0d0b070e04020c06010b1c050603121c061707080105010b031315021206120f1c0e060412 69
    0x904e000000d25282c0192841020240b00b20401881490309800380e4500f4003d2200c95070654031540e500d0b0a100c42400381c3c40080894840203d0b6651410808041d00c02c401a010040780c6021104044100380000c4c5560b0003540c8180015914041d0007440c008500070345010a02e00c0d001070308408141988500c011059900844808100000d040c04110344030300709110040011a0344800515410700440001440c42409400549084480140e0341d0500c00260040c0e03410031408580b44900301825841400004600e9000b00007504040340000d41c0c842d4405442c00900d100001c040709a050b02c9a81c5488404440800f80446502d82003c41d4a400014816902c5846105000544c0703081c140504c504a40d1050036151664590612803181906041025500b651140c1c0b8060b0411003d48000c2003000c3d50b201201d211414032100300098001d0740d5103889800e03403018101c090341110101c0c400328403081c0b031841d01c92402c40c0954189c41c0c40840d80c440315030003140424001040c2c0c4001000b1032081c1d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 360271798 1250 360270548 360270553
    0x708030f0105120607020c040c0210020318010605010203180d02060c0d0207062703080703170c091e100c02040617010203040c0e071202070503120406020c1519110d09050a05 76
    0x5416003603a55a1380411a18100160f1100007803500d24140f59120001d80b4a482c03041c1c42c00d80d020581d0a0042c0e030f100340c0c1d02804032503400380c4001e40d100c002c0c030440020b081d007480554a4280d21400d406000d181841506108400e90140030045555081c100c0d1032500c13801301910326100720032034003940316080c0c2d1080101141010040750642d00001001b9402903101d801e400035440c1c10b40d00d0b5803080383c0100000710f05201c4110040c1c00440706a034600d0b03100c2c501c1440b00c145d072204060180804031007940003441a404840c65002c009540d05200001c3c420814649440c5503010360000402500503030b440140740c2000c3e400f1481002c507044d001076214500424040b80b60382d07910761500c09540c10803240080014804440c3c0200010160000d200c1070f4002c804903800c2003507003408044001d5081c0d1b411500b07160b00050845104e64140088a140c901500c1c17044a0383c548050801203441010102c4988640c0c0c590701c1601d2096240c00342c0707500c00c036040820066028140b0340142d48000c040819035191 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 360273048 1250 360271798 360271819
    0x90504180c06140a080a020706060e011502030406050a0806041103090c0103060e1003030f09030605010e010806070306060207180f1a1c1a06120d0f0e0406121101050708030f0105 78
    0xa0b40907240c061400c00710385043d50f20304a0028811581c806010f40380c0f045054080048502003001c034002c09024005100140280e07500d0800c044054a1503003041e0025500180001c0084680050540d46100c0207800d001c441c6564900021b40145071104007000a02c4000c0309010120340001245088040203032000c12507581c4501242c030340428202c54000c124080028240002031140c40c4810002c0301900300988003d07107a554080540d02c09030070084e90201c034403004010b140000c0100075000002820208483c60601d0802910b81e00385000d01c65a82d0042d004240f03030700480c0d40c00080c0a0100c0e880400c200030180c6495041000b44c0c1e8100c81c0f21321040700d6110011800c022004c3d40c800c0c0e20401e540c00d20507200e1440301030b01000911042d442800c420801001d500284080d685a400300e60380e07404801c03030842015001c2856800c505000314074041d0144540b00c4500b104262603a008800282152505401240c0600c582c50004086880100500c05210200018681038840841349403009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 360274298 1250 360273048 360273059
    0x180b0105070b010504240e0708060607120509011416030e090702100b06120f2719060204080307050c090c03061815030f060a15030503031501090504180c 67
    0x1034001c1d00406044140b802c00100701c50700d40359008941c010205c860b0b55800b011130304002c0102c0e08142d80f164020600d1001002402c0b0b90102500303038440c0e000c840840c00c0c07070a5510f0f2205004428084602884000140c440d0183e010302e482490101c2840030083d07a8040c0020361800002d002c4404901080b03924401d41c41c0d9250032a4150720a102c2540106080182107011030098802d4904054001d0010043c801c2d58100b100152031041302015a102c0080c00c00340100c03041040c261034001c1522000c001c6c580038020010680100101d4030701400d0b0344440c12800c020300248110342c00202d291200184c20810440003080900700848101c1e5091401d540301c1d50703429010311080b00c04035808900000d07092a0b06c1003240601740c110140320705540f035240000c000700b0300d40320031030b010701c50550302c004100000b0801500491082d040c860030810165860350741d803103940e4080a421a200c50b541003100c00981d0340b1400d4418001e1030002c1050280b4101e82200445c8042e10110a858000004102240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 360275548 1250 360274298 360274307
    0x21c0b102105130c080a0201091e06050d060503010603120201050a0228030e100f0501050303040e0f0403020a050a0b0f060904110607020d020a0801020a1b03020601120809040501180b01 81
    0xa41c00d5070184900d4101140700d48030001054020b002442c9042e0000c0f4210100e000124140050000c2800810918400340005455590b4544c0080340504a58240340003010b203041810b02140c40b1420302c2500c420404490780040c0910b038200c660950318000c0000284040b130f0382c02418021045e00208459129955483d040e0301c60150802c280c004c010100303440c000c0200f40c00103256480c2d40380c00520708000d04d046074200042c180707100d01041d0301d03480301b07549110483c4286401400304400551800745448940c00740d0340401484200180598000502414028481080a03550003001c1d10b010000340d15010700c03442403d0360100c18182e40d000002d1010b00741601034500594004160b803016150700c00800416a0001100301c0e080b07007001c42d0500050f204c842c2803001501c07604001503200c07490001f000309142240c898140400602c0c001c0000400e03004500c1b50305481984050740b4105103981024a00f51054030740300c0360020718103400011464814115440d4810b01c1820030312104420600446 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 360276798 1250 360275548 360275567
    0x40213061d04030c050609010c030c03020903120f0d051e060f0102100e070b21130c14010309120801090e24060a05030a030c020a05120a060b0103021c0b10 68
    0x8001024814000d07500c00d85540c800d5038031500c01c0c074062101107100c0e0ba0f081d042c42800c2d94003881580d1242e948050310b907010f0103410000c004c58503045007400c40c5600000d60b58408190000c210400010300e651044101c84129601800805014407040c10081c1c0195403482d0701c101c140032003014440102c0c80c1440c00c0c080520748004140d00502e164041710411300d0003400f2648104001d4401c080c0d0002304e000540000e0f290310a0010b68050402201e10b02c84402d440d0024820411850010060000110741e19588000c0d9092040f0b04061041c0a00c0160001c1c1134025018001c521120030b0603d0b415400143c05040c3c81c0611401d000a00504007003c0d65000b0b0401190341400e40c68941c2441c4111042d291a44058000c05031021305a8802c0801d09003056448181d00042404440c5800d50074001e140300002c05058409032103c5240f001040d03212009140020009030b26940c01190f03d80c481d40668000c0540d5100d05648215600301000041a02111490041c140e1f003a03d820450b0041d504071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 360278048 1250 360276798 360276809
    0xa0b040509010e090a0b0903130609090e0118060902130203243001180c0806070915110c04150503100902030a1b150906110d2109050102030c0304021306 67
    0x2441d190380d441d46c42480e0164000c0c0f401701984018420181800c80456040c401004182c5907040740a060503031100a544101c20514030980c10300596042c0c0c0c0d040c0702940382e00d60b03070012000a40120350b80f0009a406208100d0078a5040c004028017000d984c0c10344415102a840341450381d8682c0240050001d540b580f82e15408120300b04a4a00104245451140c1d20301070380040002031224240c05034000100d401802500d044070104020301030312000304820307a0040c646040c040d50507403818580b005041c107113500c01d008100c0720030300710450380004100392040d2000040042c81280d02040304840b0046d0b2602c50644240725103600540101e809101e400308583c0c0190250011100b90b0311400943c0b0000044440c00d60603142c000a000c883c10007042d4000650780c1e07106c0880c903203401d0005204101d8074a449d407071a003040058103078050300a1000d03018020100010085031000211081c001c214111019007154000010000b280154000940c0309510071164207010007112543c09044034410b0252 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 360279298 1250 360278048 360278053
    0xc0d081f18021308060c1b070b04171f151a070f0302030409020d0603030e01050310091a0301020d060302030115030c0e040f02180415110f030a06050a0b040509010e09 73
    0x40080e00050b0003c081894030a110b40c03400b00d6841d007405140c04000c54550304a0341e80411341c0000d901001218001550600300182103203410b10640042c14810b5100c1d001c400c505040d81300060450901c000610700303066240003402c1a03291201c11010301034a02002042c841c0d1280b0100d200d40450f08580840180c210000f03061140741d0780c410600b142c94130000c4d41035100505c8006a5030030b041c0010403030010b01042c0850240d00d5172074050b0042c140c03e04040c1c1404000e1041000d00b5403000d4801d42110041c1d6004a03464051040303242d0420000c415440d059400000d28620351000e42e004482100d20a0700200a01901164031004108050200908800305400100540000540041c1d0058050340c22441d40d10400da000410000c4079044c604442c0306018100024015890030020020740040720030b002449001380c0e41ca10754490034200c802082c1c80800843c031501c049030303c2503010701009030030540301e140c0ba0302c401c440c036400c9441070300e2255940600116244a1603400c0341e0007500380000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 360280548 1250 360279298 360279329
    0x106140405060d090b011701060603020c060f07140f18040603021c03020313120302010506010509010f030e030405180a06090b0607060209120106060504140f011b080c0d081f 76
    0x8200c610b6021240f5044019180c940300c40100389203500b00380c02402c0e84100e1610035020003002c0f030b0946100340d01c02c60515106000c0c9000170400862510750090f807600324518159600c060503920a2888014460314031000300343c518100c02d040c0b0007040c4900c000e42000f40ca050700364003044251002404000e402c0321001041e4602c044800750908020342c42401900c0c10600034080c40196948154441926121280c100ca002e0680a11849401c040286002c91420301c4e0b640c0040c10350401201000c0030155140c00e40a002c9200f401074030098203005185981070949016000708858003a241484083c2c5400030000c0d0742c0c0c409100f03035103680030050921401d200c480d48407035000390441c03074846802560510401c04001c80030b102e04030140100303171900e0382ca036403c181801e12210342503400b05000340040409007540e6a000754a020240d40000c0e50701140f640c1515007503000340142c4071500300d07038400e800c45a41403c0d002501c480c8070700c90f88103450b0040100d980e008020f10360130384691442550b4201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 360281798 1250 360280548 360280559
    0x60c1804090f02060c10020a050901030c09140d0309051003020306100503040f031224150c051506060c0102120f070810060f021905012307020c0904060f15060801061404 74
    0x34041c0417980b03240b005075011080f40803010300503680b000f50008000b030740c0020030418940c2c040c0310344803043d001d924100c1c3e02c5a05040540728142c68060450b803103903070010602d104051140303101134042c04000c0d148000040315460058065042540c4151195800e041e140400c5071141055a100c1d98002c1c204500720851510f094074024481d0303007030050054441c50031031940c40d4040c0745441860201c0c46421b0300300f40341c8a04a00c0744002c3c4010354040103101880280400c200080710a40c070554014075208036201c0d9400500d807407140300d26801e41ca500101e0b452030380550516907140b181201801251817581c4072a01110a2501100c0c90200803c00c042c0c04e0054610034500c5e00b820358114011a0a1605100030348103101d40960b00440e03540c0e445038160035030000c040c51007a0007603000001045050602030b03030103903c0d07041400c040c40c013170007031071000405000268000242c0c2c004000c4040101e41c405001c41d80795140380f8000e80010070300110000404500c12700340c13101e82c07000000312941840d0030030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 360283048 1250 360281798 360281809
    0x1701140a050a0f1a070b071d031f05070c0812070917071a09030d03091b090b120a030801060f12060e1b03010602073b0a060b070c050103021b060c1804090f02 69
    0x1302523469404d04804180301d90b92030821141008c4440c2a580130410422401c450064440003031420301040500c503800c4002501d20001e0b20b2403a0144404418580c3d11144200da9074021640141226002c000542c0031b0110045a0308050300c00f07180d0042e54580904a0011040c46a503e440340c1560190107a517107601d220340c0c08520301074842c01c0207010360544100f061205404c0c98000d00010760b81c540d921105460329040c0c0b410850044030140c6a20000c50700d0241c08010148900014032042100d807009181c455132220a0750071850104100403611581040c3c00c002c0c048511010004488420b01d008001200680341201d040c1e03801003080b0f40c10600e5036446407588521044180c650041412886c6c121400e4004c00001c0c20014000b4901d080f80d4601d0030b6400c44e030300145a0380410490900400c0c940b01c7c4003400e4400a0030090303a17032001c58100e052a01c0c1740c140c4180301401403c0a004400900d440100360715000c1604a03a071000030082004100c40a010006104d903038030f01001401420b09 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 360284298 1250 360283048 360283067
    0x1180206070f02031e010b120d09170a05010c0f0f170112020d0f050a05120a082e0305100b1f080c0408060f040308071701140a050a0f1a070b07 63
    0x40c0c02e840040304031048040001c5400e920f17450890b512483c030300d10305083c00e60051400e0f04000300284803a80401038064030103441c50043c1c03809400043c400400055081201380d111642c010000c10801d0035201000303001c10124880d42d8000b543e4000c9004046200d801034854110901d480b40403e82d03e003614403450394030b100c001240c028008121000c0454060341c809240b00c1d000c3c0c8043c01c0c2c02103851800504000d020003a50444010a100060074240d000300031990021303008010180070000d090803da03500f075840030045280d1070380308808070400601040d015403002d0340c1d40040c0284c040384c60420205004480d0364002e40c4200c100000c1d0000c2c0724480ea40d40003040401b0315441c050321030b0115070901008440c1200c0d211911401d100405034041c84a075800081498101c140c842c241150340800001845807001070702c02c0b15030504507036458505403001041e00030700e0b52400c1543c42c2d8001c5803a40d40c6208518181040451007550b04084d5012103505681c405079056843c4d99103c8251101c461 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 360285548 1250 360284298 360284303
    0x3140105091e09010b09010806012103050a1b080a020f0d051c090f1b032d030819020c06100f05060f0c0a06021b0c0f060702090a110a0c0501180206070f 67
    0x102c1750501da000d41c44200d40b990103411190040c1c8099070404800001d081d00700c201d1403044520043e079100110f5442003d4030360004152501841c1c5900416219034610a00500540011000280050301070380028000034000c200b14107481c012541e500d001d442c0c5000c0c803990105828a0184040000ba0140e486240014801d40264030414403580f5071b10043d80d00e101d0302003e59000c2d00c0e010300901204054800e2004040c807010350b4a540c0e2840030342c82d0110706490007000e208140340454a5005002e050445c00451500110348a0700c03407401c4180e41d031005403032092181c44990300104045030242c0c1003070f00395640909101d290100101d0b0f0302c40c0d03640c03084903180258087c8800100002e20300740003c1100c0100364075603805250001c004181080c8189410314803400004013045125107540040d15a09034045440c0d0080781c3d202c216a0025102d50796a40800e5840012061043c5030407154001e1682d004000030484004284140c1c1816041d00744040e500c8002442568000f8865a81c2c00d0900361 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 360286798 1250 360285548 360285551
    0x6011206180602040815060d1a1b221e051e090703061806081e0102163915030e060711010c020105061005030615030703140105091e0901 60
    0x62441d01d800c01282c004d50400c160980000c81403483c940a1001601d8014400721108040510607545170316207039495642e03500c480007101c4005200d0440a11002c03280c17017024020541d80c0d11400124038a0945410f15901d6030386198100440d5618219120403d0803c0003030104c03140500307100420580c0068007504132090369070380741c4140b030940312448118015520380d14081502401c00710f4228810741c1280e0305120251a1100801409000042c0c0b520300798442c103140303401034030b00000d0340d4064800e0980341480819408503102c101700401020002c0204055141c801c20a5180403041c4d008007128109120074030001000e01c07112503842e100d46145400340c00d00080950810202c10304008044942c04042440c1c203400b40074201c820b01403562804124030003040075141a10001c1c3c11700074150340040401c480800080c04a807254140c880107400d84000091b124540044020080c2204041ca000100d41c0440005032605290b03201034068040090201195512000354900d9004024007040703156 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 360288048 1250 360286798 360286841
    0x60b030a0804060801051e0d0b0c0708040e0a1107051c0921020310020a080a02030c0403020d06051609080d03050411220c02030a0818010b120102070b0906011206 71
    0x20207140040009040c0f603140c4980662600c4100101070030090b400c20411103500362409596542d02014610065004454036000d4940901001041c007800d44020181e0b41c3c00a0041044505404054400c1205120078480c468203505080c0c0d9038002c1d40002465584240030814a94103000382030051000545413034284150f880c0c644503041c030840114025401f51000080041d8201170180c080040c1200d40254a425040c0c0802004504020080c5218030390100c003203000d81e801c590481d0002e6400520802013000b041c28018002c080039139034800e400100c3d80d0400100c6004203c0c1e40100d4000c840030342440c0303041c42016409440c00074000c4560b1150499450304954440300c400b003614010070140340035000c18195030b404a0314580505425544240701e2900a580d2014800d40d01c0004903503004803410329100c806002d4902000501e60004009002c0c04000c04158041e01000780280f86044158403505641034a8107000e000b1410504090007100340403400707a40101408426641000e0101c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 360289298 1250 360288048 360288053
    0x303140109090f060b030c060d0c110303070f03050405011401030c0f0f06080a0216120e01021e0309011b300804020310090f0c08071806050f130f0603061d1603060b030a 74
    0x23690240e510101c0340c50350303191411314103540712140009561242000b58990300b040940a40b0811058084804240d145d41c0001c00b005030a400c031340400b40880d1000925961285440e640800603401542141d030410800081c03000f0303005d4000c9044400300d44501c592074440b440020040d51041c01c451070401107505003500000c01d0100d05581d4192036503542503141520000080c2401200504626040c0303400014031100303040441218408002424003e08280b0a074400703079540340b5800000f81001094502e040781c82e000304419002004a401c48106909440d40c109460f41002a200030350140c0c065134000c01015019405000150700884003680810f40b00c0c0d58000c840c521a4004400a4100ca081080705141410086c056482900b00c14800e180c00c0c000840c410140d45001d0603c10814610440840b40c0c0b0360344840748500061000f804010745030704001014025030340c584080401c508140b44003814000c2031140003010ba03c01200c0c4024550b442d0f19010300581e4080c242d1600502204100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 360290548 1250 360289298 360289309
    0x30a090203101b090f05010c050f030d0f0b01050309070320130b040501060801080a080f0c0f0109021f0c0b06060f120604201b010209030304030303140109090f060b030c 74
    0xc00301c60404000c2a445032038103040e080081c03c884501d09000c02c0103010721030604036a010390140c1c0c00031701c1c04107a04030250900500d01040310a80e18254040040c10b807007100e507150840c1449209400301445550060b20044445110844884c00f041d00000c00a10004040000f039040e043d0041503614040070b0000c000030b000014080300317121015990060000581428021301c0d0041144d401c1c4514158508289181c6500a041009011040000c0e42c0b0311011030304415948000d0403981150001c0ca054207ca81c02050b44400c280d12031700340d0b4080024403007049003200d04012000e55030004e4000040d500c02c000303208050100d69115406001009002001c030000c1e0155802054954034182007603000e01080302c4000c0c2d4214912010030320001c822501ea1000c40760540e640c52110900341d408c00d0382e0b9a009005050b5a2645408000781c00001e05502d6000310244070b05038180c4001d0399985240301011035070000b0000f0001c0d900e00203404082450b59104507101d000203000c3c3c4a050090070300141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 360291798 1250 360290548 360290563
    0x5060a0b2109010902090703020702060d060e2a04050d020406030605040c0f060503010b0a05031321110102130b0a120609020a02010b040b0f0d0f0c060503070f050f090105030a090203 80
    0x361010074408040c0712450380420516040304041c0001c000c6000c1d6600481c0740721034000c04102c14141c0001c1c3c00811915550b08454480000d140204411600d0b25144100e8640584d6190401041c0c0e6003140244940340036540c1020581081607403920307141c4028021400c054030826a803040d5110300000c08541c2501420384103500c1403041415550505500c406801c203036030080700812200380010300c0240c108074121031080d0700c03c1c1032142e2256241c200440b04103d003a40f0040511a02003046641c0c4407000000da150416503480c0c0c1c0d4400f04421100c0ba00301d01852404881d504482c450400c4544032140c0100002e483d81d24000540210b110071820603607a442c0d0100075503d500095001c03400786d081c440c3c080c0313180086038148400d0040d280000c1c008640380364858441e000315402502003200c00710050030b00302e43c010072551080c1c2c0e84040191452304129560700126411481d560046403150044509001c52100e0303450400c1894801110b55410090402ca40745581d1048100541d0b0200f242c1c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 360293048 1250 360291798 360291817
    0x11010e030f04060f2a140a03110d1b0201031d061e0f19050601020106091b02010b01170114300c0a081902061306030510050a0303021005060a0b 63
    0x759403640b522000400c8244988407440400c400131340f2810b5101d15480700300d0021102640498003044e1103003070102034104100f40d20085842040c488204061700008440f031100c5030a8259024900381314404e40391311427540c03e10704400c1e506100c980700641c041d50141c04400401c01982121440448a0034541401903601c0c40a000741c00b00082d042101030030b0107983c00501783c1232604e49170800401c0d02103240031006ea00d0300c200341c0307031000910144d200b507029000402070034805004000304031000404030465180b80000550030714010801c5035002d624560704000d03088281d681c03140e20f00600c81407a500c11144459103c030180110041c0500e095000300c90031071156080000030f2a280c2412441c000d01041440e008009890003001700f8440407440701109116503480480032000ea1002501e02d100e6000c4801c8404003285d00402e4069041d880181304019030480c0d1040c0079240c3c400c0000c4c003c0544030080050307005141103580360010b9000160040c101800c000e003aa41c507000040856007200005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 360294298 1250 360293048 360293077
    0xb040c03060f0e031b0309030307080d0e060103080715090212030a020601050907050717041208041d130201180302150d06091b080c09030a0b0a0c031b11010e03 70
    0x38800d00415100304050b41e1007100081110380044001d0980b40d005805000001491000700140c5212060045620425004081c2e03590b41c806407030302281e550000d05e900000701c0d2070000c07540018040000d406045c0d9800004d8103040400540c0c600006243e010416503802c1d485856000041e101c004c448c0c060306640c440034607181c003241da400070310307011059000a105107500001d11082507080000c40b4941a04012050120000c01c00c62045604c038903403240c80c0c0300b01c5d6030305400f051010000c040c0054512201014a400c3d080d10901c400e20042a01d111001e45000e0800b08010f42c01a201c1e03c115000003010310303043d25907940000e60b400d0a007403044d0b0601d100000386004180101d00c50b80c4d025201c0d400c03040103d001c080502c030141d0780c000c02802090060f0900410182c000546c1600c6050400400b02c4101c8032075480c00885c0558240d4440200c40d0401c030003040303014041c3c007500125428071411201100786056080759484a0801c242e8030555031141098400c40080c8010032400321034412 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 360295548 1250 360294298 360294323
    0x41703040b030c1206010309030918020f0f1b060c250605190b150f0313060e0c010306140d02010f0309210f05040303020c1e03011a0103060504020405090a05130b04 72
    0x41e20138050000402c00d604140c6815540c000090300300340c0410544075142d001c0d15a02c2c00c1c40c45481e0003442030958902e0341c40c4001c111080000b003208004d2250104114088180c050440702c0165248000e66041c9504c2c5424007000e16882204014490208460300c48030503001241c3e113403141240c10070340b603078149180042c0c100400d058840c01030b00d1038880140c51201c4441c0e005d1801d003000340240c90605d0081e4000002140da06404018a010880e822000801c4900c1151030781035560408590a180800d080400010361250803003030340c240f200c0000d08510703210401940119420301030002503109050381c03060380d0008070707a1103044105103807441c01e5140d450390029500501940c070038407821000c00000700010700c00a940440c10160414040e00c000004d09a4489400100300010844c942c0540c60120400a0001d8100c40c000415000780c804211071501d41c81404140c0c0b0886c0955070b08890141d010803014005548001c0c0c0c4542c10a01200c2c6040302962821840301c0c00743c40c243d4440c6017450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 360296798 1250 360295548 360295567
    0x2090708010f1d0f0a0605060a0507060501050a031e0602130e0105041a031504080904090305030a0b0a2312030a0908101404030e0117070504061403040305041703040b030c 75
    0x614019040d00303c20b90300b907001c0d40020b06808400007842c0c56070701e52500f030114003451480d4110101070600200810344864040c04000c106410a2001752005418030340001840e04100807500140c07a04210144600603803940d0a0105c0400c0032001c461842d0308002e00001d503040160914040d000190104105501d40700030041994108040c141e40c0105940021015640020324240381050342904992280e50b41e050620b00e45c004e07080915003083c00c040b450020154804029440b40880c0c01c402c11412051409201100d080c2d40900a13986904042c030000c00c0b03107801442c5c200302a0080441840c1340c54042c0140c01c1d034010103040c001041c07150206100001040c4000e00b02042028800c1140300400b4112840e26030000d44041c0512202030b110041c0c6911540100188142c068145065401d00030740050040d803080c8507038400120b00c00044403130f40011404aa0169030503640d00b505207810400c2c0d0402124000740000058441080002800700320b02d000b40d4800da54400f155a01c804034503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 360298048 1250 360296798 360296819
    0xc01020c030106050f1309051b241e070f06020306090714030705090d0614180703080409050705120a0b011205040506190b1f0207080304120f0602070209070801 70
    0x800c4064401d90500900740240c3d00c4050100c0501e2070100e41100d011a0440f100f90700400301c26802400030f000e010452929005c81c010b0500c0e0380300007502e5660424402e8008003100c04503024861702c40003c20401c215000103004030001d02c404045801c40d11b0103032250340d442c01d1600300d9031003140c065401100304410740c5005140c465018181d4146000b407038500c20000e00c0c862000409440c18002c010448030340030388540144204d001c0d0301800c10003608818403802081c11104881140c80340340c80c26007620b040341d4085121307400c59a2001c00c40c2c1c2040d0505450344090040203200030200700d030a02443c221543c1c5030003640c0c05201c2000e800500f40f5107070f00004104018036007648804030709040c284030005000041b40b5501016500d00c08040020b130513a0540502541d078034542e40490034032001c400d084c1c0541c0e200d0750501e480d6000c84020503a0396120300d803a40180d110300d039600c00342e803200c403c00309201c900216000303803003000010b02d00b284681c009040500140c3d8245c0004408000600103130320074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 360299298 1250 360298048 360298063
    0x50d0f1202160302150729070c02010206060913050d0503060139110a032405010806130501060308220602010e03160512030106021005100501051207090807080c0102 72
    0x35440504450b039101a100544419940300083c060038a502401c0704a11200d0107554242d54030102000079044019842c0b42c64a0b050b8540c1d82800b0054008101082e0080e56001c43c1d00e070341130300038140070f6540504000305e155000740286032010b00b0003006000a601404030114242254851586a0a1610006001c0c180a003043d40039540b83c1100500301d03603e40c195240107010101050307186100c0502d400a08160003078403140d04180f001d00e02204000e00d88440300420800024202202509041e84606446d828400d5407020f401000200c0c0d1440c4080218810703d5000b580082083d81d03583d5a0244240d0154400c10600c0f180b542c5161184582c05420a00074480e501c02405000c1020312550342b681b14500d04002c904c6012080b640c100181848a00c2d9030b0075051554a84940e540c5a010307448031700410307501801d80c0c0f4050000300c88424216164040e21070680d0385e142444640f000c03103085050b001e0141001c6c032402440005103501c0401001c000303064140050510b95100038006032803d0310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 360300548 1250 360299298 360299333
    0xe0d1706010f0903060c0c12020d08060d020d02100c050312011805043c0f02011b0302070e0601020a320106050d02040b0111030d02040e0106021f020a09050d0f 70
    0xc2c1529855806507200c680041529040381000900c901e4049050300e4650300c004005010000c84c0c040d10880d26000702e9800e09075092605c505d15a03680301c10800001d0f005500000b5805050400e41790050b040c150340c0f00212544504152501c42c80d81d031070301d6145821010080c5145071000380103010440d130308080c081220103801414031080c1081e03502c808409441140d14040b8101071500340341c1035002290040340a541490158807290740300d0030120004030000e0402da0218018403804800701c694401100d42203500740d03019040ca40c0c10005c800450f424003170182ca0451085c4e0500c400403450705c0011415040c26582c402140c185d440c4032000c603c8140041c2c0c500540d141080400c010f480313001d1003100703040c0e04030b82c0081d19510340e82c01600c01003658208a0b1a920022039115680301059008005640304002940030981e66044100d03034542e02e0b11256694a803c540a107071100c034054000d800898041c0c24140324041d210000310300210241c180a680380c5e0007040f8180b0605c802c48a1000c240d40c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 360301798 1250 360300548 360300557
    0x3070c0c180f051306270606080705010c080901080a090210200a110f060403080c0a1704030809040e0c060d1a01022e06050607050c040b03070f09050a0e0d170601 71
    0x191180725503044201c10713000682019141c1c2c40042200703680d00c00d000ca60410000449000c0c40041c10b2002c0200014000c0b5001071103105008145980144204290306a100300071900d040500c0b0011605c20f030014000c001c415480d50b41c0600103981b003207601116400c20b40c0d1403d1009a50a095560342c030b004044694454001465000100c0d010722000901000700f174a03a54445681803001c901c43e80300f03651025201c9000070583c400c2150001c0b45141400d80900d036520880706402480c0000391090740710003003220301b00308640500d034189608041524810707801035500707402c1c007100455003e5021a0748400d101d41d4a911205100d005110605070080d030a1008000124481502d81384045501d2203d882c0c1b01006580c1c0c80600b0429044540940005803055464001e0352401036a640c0c0c401c2481441707103042c041c0a541506000810100721051940008100b17403810a1440043c040604042e0b95151520103004200108001101207403c240d030301c480101181514503a03480102400150401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 360303048 1250 360301798 360301801
    0x506010504020c1002071104050403020a1101050406080f06031002031501120e07030206030921090310110405040c05120106050301150f0e060a0215010b030115030203011a03070c0c180f05 82
    0x10100090030703401381d00c01c54801a0344030002d0628001d0411220000756009041000b0001010303404100f001c101c2c0e2155406146d9106900c0041d2502d00433030041d000001d10181c002040b504a10300c140d5003040d000380542e950006000c825200742d900031611840e03960140342000d001941d201e14481030500fa290340030032103002e03540700c03403078072481e0a01c0003901c201d9000c400315040d0359050200c814170544130140c0ea5500c0785412051030780c0c1d401058030325200b40a240100741102e2040c2c0504000c0c2c0d0104c1c411240350909100800000b44a0100e140040000038070050b0040201c10341070340d001e072001c0d464080d102c0d89810803270078030b404880402c0c2c41007000b42d0748075011241c4c1200740b040421004990040d15002910303000c0b4a004070b01c500c00d9440541c2c0000001d0b46904010045042e07500501194070b07240b0b00140c080d000c0e80b00a114044685841c0c000000c599242540903641200c50703446c149906c0c3c81c041d00e40740c0d0015035540003201000240c07021759010b0401e0f44901864074054031800c0c01203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 360304298 1250 360303048 360303067
    0x12f160f0b070f080c0a0c0e0c030702060c0a09031b05030c060f0301060518270105030109020d2003030304030f0e010c110d021c0b010302151207180902070807050601050402 76
    0x45000b0300304010704500140c4120300c100500541952109408074086403690301060803d111810640c0c0304030300f120419076000c25510702d070141c120f9200d40020380003404103445081924201342d10000762801004030082000c0006840d0003001041d070504d0540750b0401904040415040401c6035058600c07a103410407841d802600d8000a890455003103003003460701e844c0a8000903402d0250351500c80e50005540f01d18402900000406c1520400403450007a030f2603032114249800c980c02400003070340c48a1000074200010300c0039a00c010703e540e01001c43d8046280d035100401d2440c3c0054804401091200bc82c0c5940160701010030205480240382070705030300030720791182e0410b03642c0c111701c03e400342d6401d80301081075444241c01d141d00d0b86900c0011032074161213401d0200a982084c08100c0c03080619002803d459500c1c0ea00744d5131900c0254058850300d0301d030680c00b035850303030650300302c0651950b0303c0403000491146520161405901804bd00c90341e40750b40b858180e041a2058214a10580c07050100610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 360305548 1250 360304298 360304319
    0x241106010605030919080d060b0a020c130213080d020114010e0703020a0309121101050c0304020102060c0c1501090504060e010614040209010c020931030509012f160f 73
    0x444034281016652a140c20070a18100360017107414150142d0030304141c00c100300c1000d001342005810407004102c0031340c135110303550b403a80719100021006911105400c1000d191076076501d4500314003000010703d0f252455580d0320150b030840d800007500f50041c0c0c002450464089c081c59500400c03409008031903605201d00000b2a24000d03000c00c2c1003643c0883c620f051a030280c0d200080d0307150005070300520585580c400030040e10040440241e194242008680c00301c861030283c0c0d00459050700500b065036520790107620103802a904001c210300c104840080c90040424400d4040c000e0820041010300d4141000b80a4888580384594240e16180041010f20307a60707507a0a070201011603015030342d036601000403103041c20310060295001a051040c455550404811301c80b554207880d401e00105006001134810940d040c07000503010450400490010b0361052a09041200c007800c03c41c00000c44200141c4510702c1502e40c41c65583d84101c120381000c501054a00c0300a00102d0020394206007841c00d20309 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 360306798 1250 360305548 360305551
    0x120d140c0d0e1e100f11070b0a09050409050307032601062a0b072106081509030703080c030a02070b1311031f0b060c120301140406050603060d080d0204241106 70
    0x7041040c3d8181030032a03036111b00200300c951840441118002912080c51042a5115110b40d1001c2404204006020b081c54060b6580154101000d90b08080b01d6031803d98142a118980035112080018556039102405410714042c01007036442202c3c404800c01d03203000c241c2840406103400325030501d0940001d0400b80c08035500421a1411381c0034000c511881e0742d600004907035200300c8941003210200b0054400106000c101b4600841860161550441242c513445907000c05000640041c0c00a07a00503d04801903401c0501c0c940010b107401d415481e04103000c0070079946201c503c414070741d59800f4000e110180f0022440c08070003400000041c186040d801c1c11580d90354110040d280e076a08102e940d2500203881a861603002900c400007007d41882d9030a5000340103204154040c0a51b001460900744234040545030083c0480e0b00e103031901c0c0200030b0b5808141300d0442e1294400c102a030072503812400600002d00341001040c0c84081600465140381c0032450100d0100250300582c0e900284001803447d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 360308048 1250 360306798 360306829
    0x20f070b03070801170c0120010908030f0a0e0703110f10120e07051c05010e0703050601031505060f0105030a06090f0618330911030114120d140c0d0e1e 67
    0x405624007000c0d07418a020041d20f100e188e01d03501e01140c3e10140310000c0001c5105080c1e01c500581d090740c1da42015011640300c501600300c1c030340c85038009000081c88194001110100200001070440c0c21400090b4110f403a820300000045510100443e5906640100c0b1880e503041e00207094402d040102161070005001c5291000c01c5801c100303001881000c5d03010702c1500320584180e580703041d02c908000c1e80e00d807001e2000300c135800c16a4030402d1000c80c01d482007901a0400604094140020b0001110b454102900441020341d446070006600d422521600386529a03400002c14070703900e417500c281c0e44540c4a11010760f00c01d040c001110801698400c1044501e11040c0d610780c400c900c04600c80c40700f2034090b040138548600e0044601d00c408031420103903040f0f6204116107681c40305d000b000d114203c1c6038008010381a50202103e20900c41c0500080c1e040d84415481450a084401c40541e01c3d001680c90a1400f150b6074030030030390560030800030a89021502d01982006211007c0100d1100c0ca10035011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 360309298 1250 360308048 360308057
    0xb190b0f0f040306020304030e0306090109050c10020f07060f0f1d04021606090f200114160501110702090105090c0f0a050c1c08090a05071401020f070b03070801170c01 74
    0x981c881c4204400e540c0519001201103440e0315140c81c0c0a0820001102200e00c00e2240000044d107456050007090340780fa0740072029101100542c0107118045104003140c20030360181e086180c07100d01c01040104003c112a581e21400c41d901c0e150068500e09128540c82e041104040320ac03400708460030801082d07144281c4005076941048405408240a03482c8010451410036510300c0a01c00302401e4065078034040d05205c200f642030b07402c2450000028081c1c541c00309251a410720340752121640601005081c0340c5103010481099a40c16007103036190034882c2d01820b000300f5160290b050030141d05024000c107a031180120308080c080c0780024080d010242040746000501003014910481c00c1c0c940050041088415450410400300040c1c0d4070046ca0000190010b000a07651070000079040d1845a04080501015402e0042c080440003410615505500c81c40c8074460300041d0801181d0020011000e1080d100e06203103000802d0303108180e00140b4181000d490b080501d0740040b625109680007406c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 360310548 1250 360309298 360309307
    0x110d021b030c030a14060c090f010305060f190311010203040b0f21010b030a050a0b1c0203070e1609091406041e0216021201090c060c1506090b190b0f 66
    0x7a18101d1044002e54041c0211059141004400300108000200034410784441d9603403003443c1c0959004514500d42e10010305807180403103501aa10540c0c20000c0034081600c02010200420802c84cd50942044000d40b201c1041091102c51040070244080910103545401e24011f00914140114180421074241c0019620040c0c030703410f80c000c2d43c4104800d0b154504c0f0344c0d56001c012507030742080b101c0307078203660400c40085d031a4411072091620b200030041c5040c10b180102c81040c82407660440d01242c0621403007a02041c0d40a02c0c5c60a144100406003480419076401c0500802010003079015891070390520607800e00d92104126080d900c0700080d00c00007000d14018440b80c1074421060070f0540d40c076100060310501840019501c601c5540240c6a0641d01700200d0041c900304c0b2007648000d00a891128010b001a911400e099003500f4000c000315941018032608140c00c644840d03014441d03803030340d80d11306410380c1c1020700d40050008a1007040c541c07242d1820a103030360548602100b10000305400035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 360311798 1250 360310548 360310603
    0x1a0c091c2303040513020a02010e0105010605190201060b0d02090307060c0515131b0503150f01060522090603031b030e010503090a051203060a080604150203040c090e0601030201110d02 81
    0xb080c0d4004041c0101051810341c510b804400c004d51101c80e07604015420b1410310058070740d05009141c101e038683d036165803800c42070b41003c050085621035940115501d8150004071200440c0203060081d55401c00141c4c2c50f0401c42c00c0514000880e840403042c800e4075180301c0c1c086038011502c101107481c000b400e10265a10310700c070146e0800406200510308480c203030b412191080d070400c0c44070581e46d00381d0403200259541074901e0341c240411543c51031381c07542c65801030041ca8441d4001e400c110540920320304829001035141411402030b81c0000085940c0c1d102c0030070038158040200125030007000c0007071100310001d0310001c0203a01001c0e081814460000080303402030074108049102182c00c2000e0303c0b83c1804800c40341d1003d910944040c0c0c070520042501040099002c00c1180c0100c0c0e0018800c1c10b00c81c210b00d481800303900020310641d10440c0b801c8001403060014000c40001c0040714002e0302039981144005800c0840419054005070302440b0710824454002400003581480ca800d85c810040084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 360313048 1250 360311798 360311803
    0x7141c0206040f061d101104081e070509091c0314070c0c0b0d0203090601090209130b06070c030302100e010b032104030501110c07050102060403080a091a0c091c23 72
    0xc65440621401c0c0d24030704140d4172004101c000d000580d5007000e018200c1000c9107009240600d00481c4000c0d005403044141698102080d22505032030030307041e07507080c40e40c0d04002208014126140c0f42250000078560f200c4440c115902e03560039400e42410050310000d607850515140b4003c0c500c0c000d12410f030340607805000000c0c903100c1c01003440203460395075a8001d541050183d00103944011a600c00c140011841c10007900079661090400b4080c0c0400c07940d5404c2c0c4c0c0003c1c00e555000207410000412120020030f0010000f45c000c0c40c020703002012070b00141c022907411900044580030041c0d1428003019025034001c152201c0f4030300010159070b01c0d0006844521210300c82d039800246258a03143e10ad000040410000e020505010000c3d18066542e50005903201c0e2000c907001400103584500140300c52107280d00c048407440c0101c074003042c043e0327200d005424240c0060703911103480d010200d04a450ba03d0240801c10005d98101070a0285900d10b64500786202c04d5607218018011681611000342c1004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 360314298 1250 360313048 360313061
    0x1050307050d1d24220b070302070804031a1b0a030b031e01060f290a0219030818011104030f021815090c0c0705041107050307141c0206040f06 63
    0x3c0d1030550b55010340f04c1202c241200d5000c03104042e10201d1030300081003141c0344845c244201a00d85100c0c10000c01c0382e80c4080f03403100300602c003a00b8140e0038000c4002003400000600041c62150b8143c158036a0310300c043c030f650100010140c0802201c030304c0040c60600700d00c100b41c907180b200508001c81c4203004000043e0030540d41d01c0c2c140307959800484001442c40015040b400855640d0210004083d448124601180c2e449000e00c074046100003c0e1400ca58260b0340050400c1200c43c410344180c40604500414107050100040e400207403410140b1802c03070b4050031a09040043e04008010045c202001030107070380210f200250908880951030340540d00d45100c4003404541448822080f17140c08805e1036150406407000354000c1410400103100c11034000c0480702103407100300080005034078000c208406440c0254020010703031070070311086000810401c0502426031081d1114110814002100b0345000c00c40320141c6040000e04031030400203a0085401904a90030207000183d8644c0e40c1400c03006000d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 360315548 1250 360314298 360314351
    0x2030a08090f040516030b06070f12140d061a04030b040204091a10080606181323030711100504060c060b0d030c020315060a0501032307050c060601050307050d 70
    0x9190070409101d030448110400c5c0c4505032010001c5240c000140074242c010b110b0020030503034424030a10b0115a0200701c0100341d101900e019842400b10007103104040d00f101d44004241a00c0d200d040c0105030403580d41d2500d1021403000d481c2070a01d0742d29900540c0c50040d0010303016540d40c0c55001c09000c00c4580c00e400c02c51051041e91218201212009490300e818429900c6031301800d00480c3c820310744502074824607c1e640d00341c01d060f40c0f96011550b0b03010b01450000c50340005441100200342072240305018010040002640d1591014180b24450040c2d0032029845841c5e00c0340c810703041642103004c0d41c065036a149000e800d40c401c0c40c41c00c90003c00040754050307031091010141000b05984150a82c81142c4203800341c0300c1e02d00c1c0141c0003070b40740c10042c0e60b059031080c6c0005c0c00348407651080c0d11103144416004440c403094030b242801486da52100b0b0303c80400103240011451000081085420f0f0404401e04e80325140d13180500c4020414040d103d00c002c0301540325440011902c0c03482c10400c17050507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 360316798 1250 360315548 360315551
    0x30303110d0c05040807091407050a020c03010c0e090c0708042c04081b0105040b011806090905160b0406020619200d060603060506120405070b03161b02030a08090f04 73
    0x84103244043e2a0b07070860710524205114424002c58866000e00805005821440d00c40425440f048400d4680350010b40170082184903402c0c0300ba5440d43c0034000c84d5580c104c00d03211a10380b0344014062150720300006061948114040183c0342c0000c1c1c1c010112421210121400c000960076074100003400b00011500710b4101c18000c00380014400084010f01d0402d44903481c065084902c00615426074400300c40c0030300080318603401044aa1440b50501d2004030494000164464030f40c5110307802c94007201d2003942cac56840012001500d54034881004080c145869070039080510f01034000f035481600038030f09036641200c005d14600c03800c09a0000746803540407c400700c051130140155000b950304110124503c981c104040058407601a103d0141910b00190525160010010080e566018003030003c50f4680308802000805071001d40185006210450035510b0718015044001e0113108445024594605208420001a500018220300a40e0300c50001915864070400203140fa0110001e070b01d0b08035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 360318048 1250 360316798 360316811
    0x60a0f0203041e0509070e0a0b0d02041703030a05070c0b040f02150313020a051e061803070611100e0a02040e0c0d031e08011208090a1d1519030303110d 67
    0x2400350071248810b0350340685d400000350341e174480c013103403402454000326822003114102072160222070f13401844401080d040c01340c41d0566850b440030344d9403001507050b480c0350030100c00d0107441611030182d560018154501402c2440954482005404000d071000304803283d004811001c41d140d100001a1150020481503241e14100c40084158100360710304a00c203088a10b000301c1c25103020186a5071a4800400405440155a062007000e610220b0604140084240c3d0341c01c180d03800700040c00c050031469481c0703030f000d1704020b1803e4500202415000005820100310480c1c007000003ca9402090701218081400001400c54034102151b42140700d0b004030a54a454007855000b440030a240c0e145a04104062981040c040340e40d0242802101c81c5004944164000300f0402d01c0134002d0010024031927002c240d40c1d000403030214002141126171541e0802d0801041d422400c0c0c00240722a01270310b00350a546e0050f01c0080d0019054080102030641d1924004180e00300f00d4196044031102c2c40301000758 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 360319298 1250 360318048 360318089
    0xa0b04020a08090609010e0c0103020906040302040905030a09051008063a15050c09100201020c0a030305011e0509180f070f0e1012060507020307210f02030306060a0f020304 76
    0x200c060488004980d48104000b00d1002e2030141f15070640110060040d140e6040e070342e030044020798040c20006030300c10700074400440940e84500c030b03a2002c103114a00a40d9142f2040c200540b501c0419031003240305140391a03200002c6900228126400f00307040b03405120300350b09403102100b00384c203040501c0400b0203a1200c0011100540360200300c028000d80c8810903498400e140c0c0c1003510310861b03082c42d0041c0c0c04e22112483d414403410035024541c66000240c00c207842c008002e07241c440700ca0026800252a035004015070040c200b050001842080e81e48110281082c000ca00c6850001d0f10320020b9041b401e200d200350040c00e010800014041078141c0e00300781d83e00d0b90010800300540c041c0c0b000380c0010501061055070200415411541310b204104c1c00120300341c40c1c01004200081c142400d60008003c2d100000d14004420944111000104100d032841100014084002d44201c0c8081d94820024402d003a83d5010995011918600c0c01011070648401c0481c1035016941c40081e44402c00800f13140c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 360320548 1250 360319298 360319307
    0x191802070f0b2e030c030b0603100c0207050f01030c080105210a05030306030d0906020a02090703020903030703172a16020d050309040506060703051e040b0408010e190b010e0a0b04020a 81
    0x7442c1d420042e043c407080c500e031070b00700078402c0e5440001d00e00903200c901000001c4e0306012103a80090020141d4840c2030007880c0b44ae083e07400c445d445d04c0c01604070142c24031261400e03e079400700f880c80a00c0c00300485071014401810080301030050b244506d11840f50107509450041c0803d200d8400181642e27034641840c5032050752500306a0340c5901c13a004000e40c8100781c80c03168a80d98100c40082e0b009200141494082c00340720100908840c04142d0200082459070302d003000107248540c440d07518000190715200b8580c00c14040981041c040c510182401641d4416145070821b0b218107200c01241e64015280d60b05101c0f03584600300a42251401d4020414820080301521008d5400d440c1070200381d652031708220721446034280040c0800c0041c80880340c0203000589804041c0341c0c29180c01d14080c0c84209080003071300640c1c80708110fa9151740e080d0460b100309000c02d00b4004000d0340a800c01ea0718aa07984c200b090414041c4c045040b0403040001cac1d861074250800b440c4000094021561180c0c0000001d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 360321798 1250 360320548 360320581
    0xd0c050f0d032906070f02040219110d030c0f0e2403010e06010503160807020a1e030e04020a1b05010902060403061a030d02071e08010c0e191802070f0b 67
    0x1c2c83c0c4000c2c0070050510f906044040300a401d00a01d4a442c00c58a955080b82c0302c84180360503a001503083c01030780e078100880108030413498619182c0a00c00107c804071380d440c20300500c401004142c204000800702c0e1360008203401e40c0d03d541b8144254424400004200301e9907010008001060076407242c0914074882c14010f5058900e1a100d2000d2607591000542d072074441554101002c142151151078024481e204d0141c00c211f2030303c1030b282101c0070b64813075244005461b21802d80380b4042c4118001010f400095400c0003581c20b40c0c0c01d600b490340580019002100f04000091521040420141088020f43c4454a201d84c000c00710380c0c0711612030904000801703540e8100050b1204000082d192072070002040030f000301d00c540c010100300e0304042411940c2e80c5041039010114181c4107012520700c50a002d29011800d050360740800c102100e0381040780048107200741c0201100c0c0761074207010745036030980d031902c20100300350000d030362035500d464185400783d05514094103040e20082070055461030000143c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 360323048 1250 360321798 360321821
    0x1719090602040b0c0723060f0d050c0310140607061e0501080703020f04050f010302060903010b0909010c0905060a050712110a0c03020103050105060f030115020111180901060305090d0c050f0d03 85
    0x128050741e10742001c10f00798900c500c524441b200184c0c06c2a240e0f0300e070490081c5003402000400380c1c01d10000c00c0800b41520b005aa0181c25008040304100b25030741d070210280c0003459542030102040940102259552064620107070030507481e0744421400000c0c0d00106102c010b02d8107800c0161b580e656003400d17200c8025010480c800e040c2d84c115111180f81501590303001d04000c41d002031036a407940d03013088a0755000d28251303074065481d00c80c100740640c2e8100203948070b030f0060350020880e07000b4604014418007031600700d244526800d0180800c000d501405807810160301c44141030b280e40101c2404c2d540f03140d01e8245c180311446210f0800c41007001c0c007102c2c0021603100382c07000d1003e40d8803041046420b0051903210607640f1f4050004100c100031090074200130303003101d000004031085501000c00f950380c00a80003000030303c001c0705c10001500303045001a004001901c0c00f0401402e00380e4400b1303143e044813046070007000320400d410b105102040c0200c200140c9040111864000001d00142c06440d5070b4840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 360324298 1250 360323048 360323053
    0x3190c0603050f062d0d0804050a090603200109030807060e16120b04230303010e0c0306090103030e01110d0f031107020d080a0e2e1719090602040b0c 66
    0x10030210f541c0180010f002d20300c02403403465004c540c01042100010018958941031500180480954540d05034010905025071a150380d2a41080c0074419444044e0b03000e0141030707280c40700410114014440c40720704a0f1400a6031a1810b64401c0101d41211160300054080040000c000e010050154810846030040c03c5c1a40d0412040d02002864441d0794819407910030300d003601900004254414890384544150040d240c1c400c40901c00600712032044998441030b03480003005000182c140b484090b0b0095039035031034500e5860440c011414481042c88000e00f4448240d0b50105181e02415900c00802e0440b8225045440c1010006100c1a4405136010100f80740251800090194104031441ea0342c0103810007019200d507a40e02da4241c1d008890a104110610600d1031a1f0713075030003000d040b4103107070200c10001c250391501b035044010603034040400c2840301c5c00c01e00045031440000d40682c0b04030703d5a00d03811071211030000c1401500b0003104c002c0c61140b0009011075400c3c615000f424088094608 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 360325548 1250 360324298 360324301
    0x90218040b040e061306270c0e0c070204021813060501030c050c0a14070f0b070b0708040b0103030807020a02040f05090c0603071d121020070305070602070203190c060305 75
    0x340710031107001d40010100c41e0801c900090105400181002046101b10400124410712010301134147c16046550a141c150701a41e11040c42600d00e90400904401c0d01800c040c2c1c106110450b1080c400c2480c020f004030f401081c1c0001143c015074404d0318420002d040104114190100c0b50000d050300d00545000c02d15003910b407106c26100d034041d07420011401e070042064281c0fa0b240c0752070f20000404807880c1d078031030502c001c16502e60844c4148024101051403540b601803500e00040254001800382040000c502704100100b800d429050b8112501814041c4454030303204401c90034070301d500a001e50454100b2045013a500300035400244201988000d44840418010420405100940d1444009101c2511404024110b400ca6165480c0001e041c592000001d4050f07600703021000e41400c58243c2e4460a100f502032040c800502a2680d16410514249442d41c014040c1d02981030040c158544c0440d600b400c64a04001001a0509040d20703070300c038080546000d84a43c0d10314019080001c0c00e04c4d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 360326798 1250 360325548 360325571
    0xc051204180504020f0a0f18020c1504060f0905151e161704060b0f0a080a03050f040e10140108100513060b0f07110d080a0507050709021804 62
    0x10980382611500303a51002204101d5250700080d200c003800507a40101100c4050405507600c081d6200200890640000c0161510540015640089800b03c180d02d004029960f40b040000c645c2020801e60440d07042215191070030800c00610310115050780640c6404441d00520000181c03042c611140c01c42401d000d03541d88507810b540d80300600590301103065210080b50361100144e42d08040b40ca41480c01c10146120702a05802d282070076101556895a20302c040c050900703146029070035412003a01c0c548082c900d04000b0746c0d541c004210b0060208440422403c105452441c115030040942d40b071803200d80d080044200c1e50f11285803095210328030f5000c03061102c95018030f840070303c582d00705000341c40c0003450181800707030002084030114641c503a074840100744031680c00e002d800f442d008080c28503111070191500c0c0301d090b58143d0004e8862104180100e0000314084200c404e614800c2c130b403660300c4041e6843c207c1c1c5040e8036034000c190347c2400410513002da0140749041c0142d04401700c03030074820300241c80c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 360328048 1250 360326798 360326833
    0xf070b04140301090c05270f0603010b030609061807050d05070501080a0605030c010e0414040b01050a0602011509020a0c050a031214090a0209100302030f15010b040b04050d0309090504030c05 84
    0x180000c01c0c5c148100700070001482c050740582031440000a008a90070422007448409080444000600703901003c00d2110600382445262030400d4142c00524090401541c1e170f940c0c82000820030380985400d0042e8a811242c03c2c084603000740800340c41880c10010320320b00241c07182080e000e454001804400020500c69190180d41e045a00c090041e001ea4400302004540c0c010030315001310781042d1644081342a03050001d00461140b4081c09201c402c41d41440100800c070042c660043d004c584c10030f0182500300e42d0660301601214003403c0d005a55607014982624070342e50300200544140940c0801d142816080901e40301c05580c0e010080282c09010080e140b00850141c903e042c40392b0018001c01c0c01400c14500d2507402c11404500000c80d07a41d0390f80083d00c3d00c0d81404110410b034222402c1c150704500c02e184918050100081d62608090800c4c0f03010310b16010320b00c2100d1103002010340d0b1405040c000d81d1484080e1034800b50612280c50700d428007400c04c004c992001c444510940c1411030902e070302c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 360329298 1250 360328048 360328061
    0x40210090803120f131a220507031202010e031b070312030c020601050d08030402130b030d0905030c10210f0507050c0c0603070e13020c030304050f011a090f0403020f070b04140301 79
    0x10424030201c043d540f81b03d0740c2c42918001c001d545696800110707080c03603515260101080d584140c0c0100a154290f19201008201c00702c0700e03a06680c10107158110050b000b0007500d112046105801c0003050042140078070303007440c9138806011242044503603001594141c11000000d2100e808640950b42e84500340030b8039110036a0b001d00310310f0080c008540140350100b4680c1410a40070340210f1407540d4a0f001904198141840401103541c135581008a800e01344101d50031a1001c4501c901c003084556405410307055503c0c86030f090000a030707d4403511541140c3c00707244002009a01004546032420019240f607010524a218520828111601c80d1800500301c031300c00c403000e07a00d440c0c20300c461a041c040c3e10002c07040c0034860150213000380c0c850030100b04080c0d0302c103d006500409084104541c080d00710746124040101914000d1101596900c460002a4010b03e50410701c1000d5a110300f000c0b820452000001c0c0c5190240c84000a03203021904080c10035543c40f802540303031801c4d91400b007508032402c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 360330548 1250 360329298 360329303
    0x2070608071e0e0a08010c0f0e04020304080304020d290106110706120c0c0b1f210f0203031209160602060f070c02010210020a0c0c061106040210090803120f13 70
    0x10403074402c100c0180309951140514002030682025151038003446030039039011400060014102425100d0320503440380c00038010700303015141186142000e48594040b48070082002e409501580d40d5402000b1000c140c1e4030008501c040605003200c2400d9505002c28001c1c07041c80c00140006012001e424004038400c403c441681c2c88a0b8460001b000000001e85505500e035014050100c400030b0120300c0c8408003c0c4211860540c1c202c1103003440d400d0400c4548142c101840c0c0320601008205076051024803001e040340c00c00d170060071143c51840024a50b100d03d881e203031460f0400000f030040f400c01c0009e4990300d0300c0251041a8000341ca908003280d49503800c0704c52000d07001181010640960045030300d2402d260061040c1c0b030031a0700d2230020303405903800080403c0c002404140c45406021707128481101800403843c0c01c180e541107400c1803666a4070042c00103413040c00024158034015000300c00b80001807581c0d17001d0300d8030380c2c5d01038048840202c41111492087c0100b90000b82044203130403101c40c403c2c0da = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 360331798 1250 360330548 360330587
    0x30402060f21010801051e19060906051207061209080c01180b090309011d0d080301080604021318030810170c0a051203120705040f03050115050406050a14030a080a0207060807 77
    0xa2a0a4001f9a080c0301610012204402d92102a180c1c10103008402c05003001ca800492500c2c0307041c0901043d203103500700c4000f45400c10340c02400000c2d031041220480c0c1c2d0b8074140200c0ca022860811a0040c03085c80300c0c0151662900410204003418100ca5024007801200e40c0d04c0d10b85d0780c07240071b00d452303100340288a800600c85c0980540603010340c039004c11f180c030806040c290410f28241d0319691540d100781c04c00c030825442081004218a000000d0844003644a401032108d40022a0809001d0a01050040a01c0210000030f03204078144194900107020844c13441d09045400280380b41c43c0c041c9022018040c0d4001c0380b011625041094038000d10b10540300041d8545042000042e81140340601490200030040000040520428076504061800740d000014507078080061a0002001d9611183c01241030050070012583c0d0038541c08211107045450101144d05080001c0c00c0811503e40101102001f2641100c1c0c3c690005480c006d440068541341c0e025141e40c0d40a031140500702041c1d070ba008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 360333048 1250 360331798 360331831
    0xe04060518090a1a012c0f13020a0f05180108070b030a06270f0b0321041203051209010b0f0d03110706030e01060e150105030402060f2101080105 64
    0x401c040416503201400d0010703115011440d40c1c42d0000ca81524002e92208000310006200c0b184050601405240250314071082d2103592840f4003503000300c001c00701e02c461030707002d400194070014031640018503540c001c0005c91034640381c59884030340140754010f082c02211038001d90030149140242250685074a24014542603103000c5112005600041050200580310603000030320b07101e4200c240310f0307640b10014480e10310036940340d80030f08540c68440300808540c1007040f16502d40d1400718000f010610380200c14070b101c282400c0d00380c8191186902c04031044c1c0a0002d10302c1410717844406048100c1029580c1e4140d0b0301ca20301464260b801134078240d50303c050307068180515490308000c1e442d00180f21741042940002150b10041c03e001140d0300003c0401d4681c2804400244e080c0300b07200c05854001c1d030340f900c542010348200c90b5564240031041e0520030004007103030555031041c0584400151020a0580c0c802c1c0c84000d04038034442c6440741c03019524103500003169806060003860300c51800303002540800c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 360334298 1250 360333048 360333079
    0x20f01150f140d05070312080901050402011403130b090604021c080322060f05090706230307090e01060f140708220503010e06040b09120a0f0311190e040605 69
    0x18a038240300a954460500c103443c10020320244841d00c010344c09482c1030310a40c2441500613110550007403083d00980d14103400c0000503a01f00c800c01c0071b0a08641c3e04192203035142c181c2101c020000e40406400c01e40100b082041c03240303000481a114a10a1380c16103078900e1150301c900302810003042e00070500c103005d2001528403044488240818404c0c040107518400c1c10381c0305d5030103d51b42c80324a22030464907041001503041040002e440140741601d00a1071000b03608903000309404500030721106460000000c254041e1140012030003410a00a52000550b9038000207000500d8400fa020042004001d0701c81828442c030003510000741e0030116030351516140b03000c0d0070700e4500002444907521117241804106500c0074440e00d050100750760000c15003424103040580c3c030810002c00400440d44114413000c03d400311207040e03c9114a030380c1400c026035107654909130702820010464600c90000071900c400c0800002c0c1000c010120a0384501e803c040030041444155051130040b03542080340c1040e28000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 360335548 1250 360334298 360334319
    0x3030301180e100207030221090d020d080c0f070e070f0806010c03090f09020903010b1002030f0d140a02120921220905090f0d020606010c1a07020f01150f 68
    0x2500034010035500b00101d0780c80c2d0f00040360841c01d8140e0041c0d04c800d0001800c0381e202400001c451055408480c2416403e00c000382c0d1a90303142c80000e00502c000d102c0d03c420440301d001030b201160103650658807081d0070302c200b050782d5150911409100401c00390208224074040d031810300c1e00038010b5442500a40d1500010b40f80b16503009008c508111704680e001801182140041340036005070800503a80d012404d0416003520030002e40c80f44215107142103a41c24a400004644003000321b400e42c503403035503000340541004000013261090ba0403c0101001408441c03135004103402801d40282c0502900d0f00d0340d1841c1d68454181c60504034000c580c4c030b1040101d0342c010151000024114201040c038400060040001c0c00030341c402400e9a4642e0306100382018180000c010340182c6070001d2032803e05c13026000396140303000b03084181844000300201080c005001c0800c000500c83c1500310040341455400250785112070408400b0300e5203000c0e1606c06980f90340b140c0318120740a016050710703018201a403040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 360336798 1250 360335548 360335561
    0x901031e020304031805091512010501180b0103050c070204090507090903020a020a3501021b03040e09030f22051f02010501060c02031b06160c031208012103260402030c0303030118 79
    0x22752000750650000c0d64000d0034000d0340d01030400c48401d00e8140209905003416510039091142c141400e0070204030501c0015002c2d94800303901101d001c60070030001d05006003042101d41100e60031504002c600d41c2416000981580018400d807503500e156565410480d1030f609214401466808c803a80301490464400203041140d41040d400051030203441c5501c0d40c40109011070b0311041500003003801c100c044036034a03a00d603001d032500010314070f800c5000071800e00324070801c0c013144d6010320403080c40103698654603000310280001509888481c14542c9500220152030740070301d0019800d2400209000d841520b5508040341e02800400c0054100e1941c20f80882407040c1294000c1c2d001c0c0810b030188a44000030124450085000109039411414258901580c0b0b030203050510070050010800212050b071589940b154000c1107406207500c0d46411141c503848107982030340040c5500c200141d8000784c640007d020754800c80403107589031907000030b143d00c0c2e0200340304002130f80705c071039142e03646a025079082003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 360338048 1250 360336798 360336841
    0x1503030a030c0e030714150306130f0b0a06030e010c0e030312090a02061b060604052509050a09060f3305040e01031202010507090b0307050901031e02030403180509 72
    0x112040d00f508000f017813814007607522489106d1802800450b05042c031511610340703032070361406e11031440c42c021000c03624600180d49403158807552a044103a0304e40b85a0300c203034820b840040c040c5130b041e9a5404005c024080040c0081c03929444c0403e5501d4860040b84420341c00c200c040c0186080c014000c1c612070304c0e907600070040603683c081ca18800005907140001007400e00454582000b1071043c403a81c441c5401e90050031310340075910f0b000034882d4807102130b0402040707102e15a0084001f4001005c084803d0840713030707000a4100d100d8050100e001c61032500180f0550f40f600d112140700b02c2d038504030300e070410380641014a0840310b0346000004103103601c100305244002034186185001c4c2d45030740c69140d00d4401d070710a85841c10060031032210254207008868001c4854900500014104072010b00c103844050a61010301900103242c0300d09902a8000129a43c15905585851803821aa8501070b60044070700f00d000074550114082030f602800c000300d00350741e4080c03e142034568034540150032516448115 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 360339298 1250 360338048 360338057
    0x70b0c010b09060f01230c03031611060109020315191a091302030402061c05063c190e1501050408060609061503040c06080901022106011707080106081503030a030c 72
    0x20102a400000c00901103004c20000455580c58844c124059122890a442b0100a0a180c480b1740001001410328151000240300595075250b4110078031400801c070010640280c2a191102c0490500c40030040c21698421200002452442001c1200b8440c4055442d408200a1088481e070078082d4080d682c458805881d252800c400800f8000c0c600c0c01d0503000c114070030f07150301c2000a68217200700111841922090082c01c01101d1026400701c903001c1070450509488000443c682c2a43c48259980000a241120000300c3c0e45614454040c00000c0f1403c5200714800c1e211000194421401c880440d0361400c0030340030941380c034010480301c043c001c0c204c61b6010380007001714072101d50510300441c05144108216841c0618041d009042180d00038120304442e48140034040788903090124451648075a454140030a81d030303180c0103880d41800b40e000030741141124002c103c0345c6038014805074185d49031619040840e0341ea03078100200b00000c404800c0d40541042c071250190070302030b4001501d2000315040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 360340548 1250 360339298 360339347
    0x50601050a0602030a020307081e030424060b0a0f0201150b03010806090a03021015032f040b0d03030b030f01050403110f070b04030f030c1506030b1e07140c070b0c010b09060f01 78
    0x140307610ad6400948041c2d851302c20583e41210700454210100c0404146c1d4242441a1858040c042450340150714904c0c0c18042c0a15500040034401e500602c142c0d40c2d40c6c54001c1906881d0070013512560424000c80029100b01c03c04110714070360000e110b681c4540c2c16401400032440c007035102005441c0c1c03524585e1210010030b00101c000381c14544101c41502400100a0350084a0251202c032008d0150025014902d8200e07465600e0720f034000010111030b0581004a4000740d0440400d1a1400c50702501829510780400e000c10554000d0600300d406c61007004031084162410702d26500e0303140ca0300c02c60402c128100070070030005000b81d48120b410343c001d08126100d42e07503c1d03c0300c00c0300c10410400420800c4d03a60030180200400302e1951600030300b4820540d40248508841101900c8024010805000904034006441c540f10310480f50240c4510098801c455600c0311004a00e0f0080356003180b10b5402c0c040c0301841414560340c0944a010010f0144200210280c01568076000300fa03901580941101d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 360341798 1250 360340548 360340597
    0x3070506061206061216150810140d0c030b0a060509070809072106091b0e10030803130c06080f0a0905100c05070615090e0703081c06030f050601050a0602030a02030708 74
    0xd882d80c000c110700c0c81c0355251f00001e904010b01010004041a01ca02183c2106114a42d0380038880305c246d40e020f542d03500c804c000a04010074141a01d031710040c0b00035030103010030080c041a078101404850068a542c203554031100c0c01680c40341e204481e0101e00e44d01250042144105e213450760058205190003100d214241c0d91202c1c0141c0e4003546d0117407401c18480d030614a25881c00140f180c0205130380c03a03000344141042050700307401d40c217684000340c502070f000700106005000001d079081005070305c828a80c10b01075032100c01401100c8111204103000e50340d840081d1035520117004017806980e005000e0f200b1011640170b07030303002001525030be40200101404100d001414522494940c00c1146000b484014641b20f2aa0709540501e0701603100740d0040750301000042c3c0004c2c20340b8144043d0140842c01c6000e841014001450550300243c034802048061400b4014081912414bc540580d00000c01700d4882c081a82d0b28407038500c181d00140e00411041c40441c134140b015008424450001110000102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 360343048 1250 360341798 360341833
    0x8070507030f0323040302072c09160305060f070e010c0b270102090901080c0904060f020910051b01060f063203011502191506051002030705060612060612 68
    0x641e01e01c0d140148135014002850380400001d0014002080107100701009141740c40101450782421950445040b004203004500500410400c1404010028106a0b503800e1003a80e07a00103a85006904070f0b048040b40529108a81e58010b580040e16102d00d1840700c1c0da10607541c01d400900031400440440c3c0c00040155a00707001030b5500d6100000561110181c004200d02c008069106607819808603503440e8503500d880000641c0146c00c4140050310600071600407010707220394180c05074010150850500000e801902402501031500c0c8105181c107400c0c481d090803544280109110260030766010040d0a1240030503511042082031403924184c18005400c500b10f442110b09408544040018403181808900680d26841688010b0a5a107003c02000951811075100509492050769140c50300b040d0765001400140030103045c60700d98003007800009440350014a0100d82d40d00a41c40810703611700c0c1080c6103d1f902c01c1072502519858a07100f040011203695004004658052400480e07000480d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 360344298 1250 360343048 360343091
    0x605090c01031506270b0f0a0f0305011809050f06130510050709060c050c09090714040e030301171501080703211d06070b1801050708070507030f03 65
    0x260041511440110000d01680c1c019140c801d0210325141c4200001d40c0c1c052a45100c104010b04000d00e180803407280d007014801581c016040202002840c0205000740400610081c821a90ba1100f0b4100444045041d03030303c203102e180100b2103d80c030b443c1c0c20640d10781e01544515109004883c1e07190354400140d03007001000c45030241084141c028240a11100b0300400451080c400c804201628001c00060f2417424035001c0d240c200103800d42000c041080c00c02c21554655030041102d00c03a8035007068110ba0f180418003d2a40d11610000c20b185242400d014600344003601c0006107017036a0034034007650740c0c41151030341c1c50410b0301c2122410140b11380300c3c00300f10b4040c100881c0030f45003a608500f80060440f4510b501911808014500c03031451942c0241311000c2e140c0d0b10301c2608064410000000c0d454007802d80090282102d030414004142e4403a9003604811000b20000e0103607540380801611250001c60740440401c400300000d400081c816040c0411840aa0a001480740d10000521101510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 360345548 1250 360344298 360344311
    0x4050a03300906050c13030b06130923010b030a06020a14030405010905060f0105030c010e06040b0409020c07120c12060f020d02221208031027240b0d090605 69
    0x50700c002d058180071a5002e40350340503160a008915100e80b905c0e001002016074440035141d0500b03480071428980e10410301790310003920300f202030140310003505040384038104042011442080082400802d51b00600890fa54500c0080141070214813545505000e517022000f07800070048101c00c24103001c240032020314002c9008500000c1c14a0071707450064034154000e8801039441508070010041980d00081c0819602c03420700e0142c40141038000421401e010f16084003400b80320125000c580d152a640c00362091000031803c64100e03d0352a9200d80c120105002c1c0030384030540d104818800048070b00c002500d89442803000190313030014100d1103022600244207000c58a0380000301c1c038040002039103000c8200c045d46d074041c41d034462074200100c13900302c80b034140100703021800f20000300244c0202c0f038910014410060350000300004200d0000a6000154500c0201403a000881c40710006162842c0264517280040305810f50412602d4035140e04070501d140040d40c4c44401d0784000506a00a4034003445 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 360346798 1250 360345548 360345551
    0x7120b0403030501120b01120201140301120c0504020f161e06240806010501031107060903020a0213050f010911090d0b0a1d030901050703021608060103140604050a0330 74
    0x105441e0080664070181e00c0620807400d181d0f20100462100b02009044688148803020034812074401070320088009114038040760804030001885071864001754800600c034100c070010860304c031070400007240190310107031254002c18468151808c540c4c4148403c0140500c5400155602451002581c68480702003241c0b800d840302e07190000c0185041c6c180088080f18441c1c4114282003065041c0e9504051255504054490542c003400c0200d080840d21410703005103040c4103007181f505010b942c640c1000350403405144071141011950341140700c0c03c0d000328412210300c8940d9107010032540c054004600c10303090040c020002c0b2600c6a035802d1031041c5042c42401c0080e400d14041d0140001c41e4a02e03404041584030728000342030810000300c03c803068101c0c2400d0407030b100e00ca01e00f0128581198600b071110401260321000c5421480014918122031013420f2400145030100322003034440f10152001019544003500000c0080c0c060720960748842225030700c0c0006200030b030602001d05400d00440c0c1e8040e6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 360348048 1250 360346798 360346801
    0x30804060905040b090705221202030606061204032610050f1002071e0503060c0c1c12110903160302040c02011509050712050c0901110f07090e07120b 66
    0x10760040c150301c0007000304640802011803090045180c000e00204003404020340010314054040e088101c031020082c40407001c982030b81c0c68101c0b4050fa09a41c45099200e44039407400074405261000448400b019440706150701a26a69001e4425088981c540c0b0900070412681000c01e00c1310100c1244a40e21010021442c249880d01f808844659049010300072100c80082c1c05c0d0349a000502c2d281240c0b485050080240290025940280402d411003980340c018503050091f01101131001c0c0803407500c20130580e02c80c211640c0340c41300341c0c80c10307140000302050103030f00600b0000340c042d40b050400c80c003144a15440d201e0354400080c00d0043d803012204079400945c0c000d10940c103151058140c2140075000030042c03102180b041d04d42e2445c10f486481c840c6038648000030b09984c03140a072070780210300d4604144564140301d0b00d118860b07000142c00c54001a07400c603000a64102c0042c80b01d10022200300944190790900c6000800b8008541a0070b900c0d20602c5000100c0100340320052a586d409501411201d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 360349298 1250 360348048 360348059
    0x70f0f032d060504030e090f070f05030603010f020a08010905090307030906200d17010e010e04080703050d02030709031203110306041a0306040506090d080402060a0c0f140d02011404050a121404030804 88
    0x280341f4003602064000000100304100c1030342040651000740c2213403c0007512541d501d00068054800a1141c80314580003158074619250000c4900703060b00c480c0ae40c00e1107184d0301d43c0031003560703401400c1024000803015581042010f02074807422603130030580301c8240b044441d004005031406072509904030020341c0d2400c4070010b070701e00000c480e4050654411107a503254503100f200b003025200600007409005002408208143c001c0c0110346030380c11066020b548038034005070041c000000c80c1c401562a4120782c0c0321091b07200c1c4130f8424141039000c00b8904500303503254103051200801c680c00401aa00417058a82c0080b80e0701084424800ea2140c002400549811f078072250410003000d90a0003480368010a100042e507178507050300d0881710103107010f20243c5101d0030616a034540005001c0d00e8411241c4c604140c032030002c201c8000801c0960001c3c23001c00700340b41000114000441c0c018010781c10410150f00026064402201c3d21151890f0161021000480b150980d921a0313004540c0780714000790400c0f0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 360350548 1250 360349298 360349309
    0x60902031606020d030b0d0803130b07030605010318030c03081503031909170709051e0907090e0a020f060a05070515010e01140618010212070302070f0f032d060504030e 74
    0x204007000340782c2401504030846c04580c1c4500c40d40c60003446014048001103000441c00a401c100b545c20100b9144907080c079010203402010070380185400203040c20100d581c00340d200d1045508603581030383d5409007003059403011100c00101601c0070308800c51054800c48181d6040028002c4400200c860f8802c06420305005440c041c100d40c023902410705420908818548045204400c40d00b4600012880307503600109401c030f0343d91001c02c008080000708240800044005010b40a682c4030f940200b0101a03501050395542c0d08040c0020760040c1d114441a4280c10140040e107035600d5a41016030600d1400c0c0d0b47d440c10045500305014485100f40c0c01004541481540a40100100305201c0000210800400d01d07601c181846807043e20501005500300c1d1b442080080c0d034684162100c10340341c210b42c1c0703802511910603110700080000c4100340070882d550360001131400c4a501c800c04c0b4004110100040c43c400c4228011500f1070b00c418401000130035883e002e1740784a244260f95a40312001e40c00200a17 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 360351798 1250 360350548 360350563
    0x100912180506120a200f0715180c0e010503070b071704030818060909040b100b21090303010b0403030c050703021c060c1d0d1e05010c090902131206090203160602 71
    0x9484504070302030708420b414074001c40b080700d461b41c0340903a5110014144080503005103095001258174100240c5035820b81080041055072040007076010441d690440140120402e006e0746a058001c18020017100d91040010300e9800e00c02d02c000f441940880d00c20602a070800e41c003c3d030309400c00042c452100025051003c2586500301c90403401c200c0300e0b2000c1031400a008000074140005140458249440034981000030000103c00640e110101400890b070107000215480071000c1a00c0803404050006c42038174180c4403c0506030f0700700b9256843c1110b881903080c100340c2c2d05005412010000d030710b44900451070403116104c1340d049040907140200448411084540802c00c15080d10445c15a4402c10700b8640e02c41160b4150750703c80c181c1007548008001c50039440c00c0002c030000d244100001904602c0c40c10741140c0322111400e0745c5554a00c164400d0902c3d55089810a082c02d00250070031447c5004172600800000401c664550b01180c5001495201c00c5a00d42c1016801c0001507810094007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 360353048 1250 360351798 360351821
    0x2011b0206040b04030507020f0301051915030f300306060e061c0e100203043903170c01020c061f080303130201020a051e100912180506120a 62
    0x140320900d01038541083c84030000d0002010010000b400800750740d10460084603a100040c002c10003414507070300c8542243c0d040c2c12800e1401c2e0800714042003892180102e401200e4004117625450f03181503881c04010340e00c00e00602c8513040c00c000022514413a080c002c04030358070603441c001081820500050300500e2980700241c030030754040141060050350000b0f00d50b42030408600220300e505001c40c04a08140d507500700031140c0c80c40801040244404a00e0441003d0303148035400000c1030351500c0c080202c1408a2194030000c203032030030400001d030741180c21400308242ca14550b03041c8090402841d081e62305c21030803540290300c41e00074011001c1520145030022640c01800303440b041d240c00c2241e901d030300004045440d200d40504111040d640248028906981c0c003c080d00c08180740c50790005c80048242e140c0501900c1078070000d0604d280742c0e20519801030b40102d12145000c02100342140c10343c45d091074441003c8003100c400645604c40f50701821321100a5200b20400b45000b08588040303400c1c080c130300c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 360354298 1250 360353048 360353053
    0xf0a380435030f0910080601050708030a06030f0b10050306091009020d0b190513110907120f020904050c18091806010b030103020310090c170f0d02011b02 68
    0x41103010248401e0102840c0c1942000036107014462496821800380e0041070031500002400c50b454111000042c8002201124100788980d6651000c0311b24440413900c05003c03ca0401551010460090180d40e00501c0c010340801c0e0301d40c40307503100343c3d501d01d2580084070b03100070300020303c000708030b00c0710103100900350582c0180028580b2143d665034070065600c1c0100d0283d40c45228000395214103482010181e000381010b90f850800305001c038440e045420340424603e1034207011035001000000c200740304503049040d60140a584000f000804100a84190140100142d103148481c1503070117020801c100b02c03030005031038a410b2018030050351070080c4642c401a0007042049039517030300c40d210300482110a84a0000594400c0309410008011030399109041c86108000160f0000180c0114141c85c400d0b0103a44007940c0c03442e5580d054441124008060700075100080c448000e4038459170301c400c0418811600010020240e04d402c0141003095180180d445101d03820030401c1c030150007210503410380700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 360355548 1250 360354298 360354307
    0x30f021b0a060c051207050a020a1a340506070908030309151f0b030720060601080a0213080a17040b0a030902010509040c0906080a02180f0a38 63
    0xc0e05501c003030040a062104501850381480b8003080a0007001d50071588599480a980c28000d40c0c80030079040c100c1c071a003041e500100780c6c080f0700c003c4042c8100d141a1001d041640601c0101680342038481c00c1114203101d244150303041d4040400c0b0022041c003a07000f42c01a41407200c00241004d006e40c02100700e5078030410920428030070010b4112200001e081c2070381002d44882d90103080c400300081c1c880e00901c900c5103010504511800055008060a841e104c002050340560400c407009030704040bd031250811000921113500a60309107900c0803640034018540303907017101c15094008032038100750420752181003100104688845180d0403070340b00010032410b0a1401069022510582550300e0415032150004011640240151400c13000d00400600c903e0000710070041c24210300e4450080040c51107030208146280d40e2007180c00c1c504c0001e0440200e101a5000d005003c1c0a01c0c113031070341018641c0c5001030609a04103d41c00e11521440c00034079507030640e124204011000a08440d10301302d00300f1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 360356798 1250 360355548 360355603
    0x112090b0f090d12020a2619180219051e100c020d0f0f080301032f030c090613020f1b0d08061003060e0a090c120803042a03030f02 58
    0x581c04898014000581d03124103d1900b280c00c0f147e01c0704c2c42e03094000c0490821414898908285100d484020b141c00d107041070004030441511035082e80074100c40c0c05901d0803805400d042c02c54042846101705e01d100380c0395651011425085500c2064072196540b0700d01041c00c2d25103050034000e4100240f034400e9903a00c0c283c0000d13405105000b030041502d01224020f4080100c00801d10359004e400040254403580d513405c1ca22411044441105000490b5a00002200a0800d40d6000404c000b81c018804481680e0900041c49000340081c0d07032010041c104501e00401c0390000b41515400c40c0d800c280c65014000d910340c2001d00d004280300007500f00c48c1201440316800509281d100030103e80b08050343d05000021f40040905800c8421072120300c0c820010607100a40000c0c030703294070850059060a64070000d500c482440e0300380041034140c00f00702007004500d08030b001c1d8080b00c0c0794011031544221448030340804c07100340c0e40c800c07008116078003825204680c040c0241850b42c6007100e00c2c01c0a00c0382c0314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 360358048 1250 360356798 360356807
    0xa0c06110c01150f0506161e06091109011a0c07030606120210080c07030309080702120c0109050402210c0c03030a1409031303030f3c0207080613020112090b0f090d 72
    0x2010700200d4030012034980c7c003880301c280c255170300d0442c100c5c1800010b001c00d0300300000540904541507902022165034512030b03082c00321185048500c01651200d901550042c083d05035400b1448603030181c41909000b002007800c6108407001005064140d60380d103111032050212030581c5820000038130540c07804200c6140404030840c0c8000c1c0d0b05150001d2941c9051522050034001d012001c0c2d04004901c0414400b440c2c0010000c803d548240c030303a450301e560360300c00300020783c854500d40000e030741001400321007040c0d48600c11580011300429007604048122103004d10f55001121a03501c0c19880784a446502054a0240c035080111000030b9881c10b08030101100001500e8800281000003c61000c0d51040c801ca6440b584200e000ca50040d403011551010a40200080800e03100c4d126800301011180740001403c00c101d5903180301038111582c0c1c20760481a05840114103a05100744084008203160f8288078640c445881800c00709514100782000e600a85d42c0204201c400f41d0201d80e4002261303400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 360359298 1250 360358048 360358057
    0x1180314030703110c070512010b061603111506010905010507030819020d1a030f07050a1505120c0c070501020d020a0609140303040f060e010c050a0c06110c01150f0506 74
    0x103405581d0392030700c6080049005000d04008410300d04008203144804284c007040c0c4404446045a640c2c82251819100900b21200301003800d41c00130040107002e000756032101c00420111302070305000c805a090074500c5403c000c1446110031124214000b00080ca40c0c1210218000c2c2100b0318046090560710b540140655101400711014284201c0021908175420740444000044800050041c0881c245482120095540300c05109001e142d00c139440402000541e4070480380000e1111403264940880b0b4110f01100c0d144e507008000c82000040400546500f00c1c0d1700400c542484255500040340032141000010b0b00154115004600f140381c0721940011001d46003908864000344c083c5c600d00d0900164004208109100c0c003011040000740310a03001003400550107088184014a20f03200c0e043d0884520b941540d011543c140720424000d845a00c944141c18401e400c00200190556110400c6810802e905032041c1c0d111202c2c0c0108030141c0f15543e00400c0c0700260b112800d410500040c40d00d004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 360360548 1250 360359298 360359327
    0x1006050301050a231f1409090612030c0a0b0106120e1b01050c010e01020a1205070206010b090d0b010b0904151229010303031d0a12050c0c0604090e011803 68
    0x20321002c5003188500d40c984c059030f00c110052a220144400382c1000041070b460b0103290b0049480c80c1444194400310500f200d100c10001040120f15503920801c009a0410b811402d1180384000d0041c41c031030502c100804c0907421b0284441445541c0340030f034002c1009803105013032450103051103144030030300700001404e0045210030380904031000f4090004a417103001c1c540d4080d201e0740c200760409001c024194010203c03040720340d4600f0324036600706d0010026203030190b50000c0103030b001d43c0c010004d01140303401034015070300014442e070703145103080c4c8075109450400e8011203030401001036211110f19251203004068404000a47c1110345020700c00740345c17403d11840c00b0340080c07145056011031403084418508034141c50070418200d540c407810014000d04003c0c01c81254500034044800c417010300008c0e80041941c3c85850301444040f2840d0441e0340340c201e502c0005952195200c03440c0c00d03580e60cc000d00081c0c03082c410b000440a0302c001425094450740ca000310181281d1038510004240d00c1040b840000c01c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 360361798 1250 360360548 360360569
    0xa0507060e03150c0d0e150703050c07120206070206061e060a140406050705010c0516031409030d17060f030a06050705130303050a0207140a0e041a0702061006050301050a 75
    0x7a656011904124888449040c0c81c0520000c11180c00544c1000e41500c80c2c014000b080944991500645d40350078030032110041890714800501d03654880e400007030f4404540810281009010794070301083c2522800c900015030004410041c01d00d9041000c5540f140b4210760452a2141c1802d140c091800c0006201e8000d004c0043c98100700d9010f49c0408401542000c0b0341507032185e8804000340550030011003107400d54280424803104600ca001a130700c0f03101c841d03101111030201550b800d07142d08603081d544050b9100144540d040f9030781e041c0700202c1002003544824542d1410a800300b000780c00018801d40c8034814800000c440c40d1800944250540d601901c000307480d4407010700030789090051030041c0c501e0026002c004004c040d0f200024080030015038080b22202034031a018809050000c1e4840d5030003605d140f104210800300c500e0440d40003030154030070f909600b0b1507074080304041034121011070141c0d0280c001c1c4900946400b80300c5008000c80c0c40c1c464219410440011940c02c0c1e5481651f0340003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 360363048 1250 360361798 360361817
    0x6050a05040b1801030507030c060906050a0f030603050106080c13061526011412061506090a1203091502060609311506240309051e0309040501080a050706 68
    0x6880e4014615503c0b14030002d241160b6959190666665406000c1240d05403410b402c00961980180f072108180c41c41d07031315110b042c0441c00c00704841c2c0c3d40b14050000101a22014004042a401c2c803a21016243c2e000280c8040e02c6480c1c1403090038200462032099981c80c104040190001300b0709100e840e0720051030031540b414482041d00d05116512122081140d80ca0000001c4241440540c084188070950701c41d85044102d4644036140c013001c0340d201001554407513006850303240810080c01e0f1074100230000d00c921078039110020240340c0b02c0c4504401144016506216a000081c95070032900c20b5807006100394076040001c143d403c0400b030311361002440940c48030b00b40409981d801103003030040c808443c4100f4441d420042032034189400040044c51404a02040e0b130011041e6503802e115416000e0690707144000e50880040034040c50580705802120243c000c0c0014818a5a04c104a40d000135600d44a4130ad00300703c03c8410690246000c1e51002003a0400104040b035801c0403100c035070803d20481c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 360364298 1250 360363048 360363071
    0x30807020f0a0e0f04030e030307020d0b13151d2e0204080102070b07080601030c020a1209170a05060606070201080a1116030309050105091f020a0c060c0f02060a06050a0504 76
    0x2c0d00c190040b50702203007994200444091510745041c403a40c020340c6d076020381c0c0d52400c1c241034070f80c403038013902940002c1e03203800d145c000c580000403090300042c074240c03a450782400580310712031003c0410100030700c020388031580000e150461548022169004070043c11080e09000604101c41c120400c520040900080480d000d45a0b16815a001858254001d550b221401e290a08403074038125105000f107000d2001080180d4803a110340004030806030020070003020b1030f454210107582e01d600350404112200340007060000307444480140d0320b690384005260f80030003480c00c1403d01400070021401a601440a000940c2c1e11203202d41d007140b40b41100184214078196114494450400010b0f102100c0c11584400c0560590007118943c0c0500006c1110b603d50424041e1952001072a69211619009540940c0c411f5503005080500141c10103100d000d54590b191425114507040d502c0100712840349200040342c0501c01158014082c00013000410b0070300001500c03400603405164021556000200170 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 360365548 1250 360364298 360364309
    0x311040c020303220804140114030112030507140f0708061506190306051e03010b0402120f0a06050d0f03020c03070602030a0e010203090603010306150603020a1707020a02040f2004030807020f 84
    0x2801d4101c0d03240c46d61103880740c418000318440c5001c12400288102030904074219083c1c01d89042c1d40d407110843d00d94081985088400d0780090307c06136600b29003810740d010900c204200e40c0040c1c04442000d000340301d00c1d0a0000d030801c3c000070540078102900b00c5000c1c91a40da01e60413268000300303080c00207c030041d01400480040903287c0203190010807000c1c4c0c000c01034085080000b2039180880c0248040c1c61404d00340300603030068020404416a4060201e9a000c1120844907071005007488005500b079a213000064640d00280070640301c0c00c0c00f00c2031403414998184900c64001e0400e80081c0582c0c0e142a900070741d00d12462040d0420840900e103007401c160f20a004a40b2210b0b0000c18540e101e5849007018001003c215903006402c40c10144005038030307802802551070061054880350f8041d91300810111100360001c0a2200f14060103900e080180d4461151017502607140400280d0326440c001c10312480303010120703014841681071000708001240c1c101140c04180d0f0603a68003001e20311503c007098 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 360366798 1250 360365548 360365611
    0x31006022a09420409020a140d05060c070b071107031407080307061506080f06130b04020a180b040803040915050307230f060306011d06040f0311040c020303 69
    0x42c0311000070001d00c0c2901d40b014140d074802110f95003c09800380c0c084020003048600c801c0c030082d0822001c540c204502c02c004080804282d502814084880ea0595a01402c0403000c590000012502003201740074808000522540400d49040c501040c020f0030040564911641c84000e0400007180d1410307000d150144244c0d0010000001220f440390100d02d45500500900604404028050900040e1407482912100c3c040c88500308802c0c1180c50703400c1405a1a03000c031814403811522098110103d4407148001c0440c0515551040c04030507864000303140020540d0702c142a071440601c014030080d24084221803c4a41941001413407201c00700300401c3c3e1500e0741e4403a580c10f00601c040004c24a81c24520390801d208940304c41104286040e080100c02002c2252298002c101480091010350042c1c540054014240100031608444000000c0041e405500034108030307a81d80c0001c10421030701001c01d000d641c0e000c49003072200c0c01d06503100950341e01000b4140e140100000a000c1c0e0b413080440880e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 360368048 1250 360366798 360366841
    0x4081c060f0b190f090b0703050f0a08060306060a05011b0203120304050a03030b06072004110c0703030206011a030f07120c050301081b0f0103091106031006022a09 72
    0x1141d681c078442c000c00340d0443d0000f040c104515107541540c1c1441111000ca04045540b214450b06090042404103a00000421810300c82d08001c09071070b04007144090009051190b948800d07518110052508140010703021502400350080c05010340d07a04541c0d00c200c1c0310b0080c1c000300c0c098411400040d1030b200100700f0100041c0800001e110a0110100e032080d0b1040c020789050140c0c07010b0303205110b054450b404014000410b0054440030a1101070444203441c80700500208c3c81042c11100d1031200d41c81001c00e1403959000b900108101901441054010032052100c0744c5e07580403400741c0901c81c1c80010108402684200c001590360b030700481c131281c0d007810542c0041040d8207a003c03010702203500a0082401a105255052103070f0b107105250452242c0c0c02915142d141c407a004015400703480c010b1801c40da20000c00c1901901a21a10081d510405100b0305030703910f641c80d019010741844801c00710001c1c2608120b0500c9484c0000980c11005014141c40d1120340f55180e00701c11041d00b002030b0b9403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 360369298 1250 360368048 360368069
    0x30f0f0d0c11161404021b07090f0b09012303030706020f1e2701030b03100903031401080a080a030b030607092c011404021603020604150504081c06 65
    0x712140036510070010710002c6512000c07900901200080c1c40b5a001a5204100c2a008120058912414540c000c0c1600c40c03d814a401021555070b40103608000c1280c010401560f5036a00240e42500c0c940540c540010007580c1070300d2103504007018800321205c4407840b04160082803c410310170351400c000310342e5143d4205904544424589d40b90480c16400482068030081c03e00f800b8203d6401480121611220000000121141c48420b901d0342c10b01107800080c14599034620601c1f503500e050001d6001441d1081c2c001500c2c14141c900035040301d40c45d0701003a20041c00c0f60010700880f0000100b0302c0d4000d40100b00d071a02c4414074031081300684041c0010700c1d010300803039040c0800030b50002d00280941d0002880c3e404032002c4031400c0ca81009111001440a0b0102c10040281113582001c1403d582c3d070151016140c10310b090b000e1602c0b4421846c0480060b4000410001032044110404203126403c036414099403c20b074482400c180a4481e40d5208101e00e0801000c0700c4005510080007480c06240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 360370548 1250 360369298 360369311
    0xf090d03030e071d0f0612070602011b02060103050316050102210f060411250b0403021c0201090f1212060611010f0b03060f0a021324030509030f0f0d 66
    0x240100038080d0041140650300c0f0396007012400c00d8440c54102d0350709940e80440310a6903075000c02c01c0481e00703000e80842d400c20025418101144010721960014007002c0d00040741c46140381e004104c00d001c01300300035000c40d0000e6005100041c4080b0458481c0300110800041e440a03c0c00c143e4020305c11009501e07010407039000c50140e60184074020324400c49a20500c0328803070382c2e03000500064945580c0c1c0451080c40811410b80712550103400c50b090344085080c0072160602640e40c66600742016a82640543c0c0a411401e485a50f80360009010345128802802400040d0b511110f201c40b1807807004007900c0c9071306c10015965201d912011080045800240b2016640710005040c00c00c8441c0511203550810340000910046070240502c00340d4060024a00d994038280006540302000d0800c20102da002c011030383c180341001041a0107011000a0802c0c105a1000031861054020ba18041410308201c104410306401005440c080f0f40410b1002d90358640d00f070540d0710640320740c0310f0700c0e00403d20300380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 360371798 1250 360370548 360370553
    0x30703060e01090b030d030c051603090312090806160207140102100f20120601050703050c010e01061d1005040218060c0a06061205030a050f04080a0b061005040b0409020f090d 77
    0x204215120113041e01943c0c070f41a1100c8044043e1151100c491020680410102812982c12455803603540c0c02480d08100d01030702c0303954146061003500f03049400100c035640c090280240520602d6084505a542071007002c00964010352900300368803a41c2000d80d083e401150190f40240305078003121050220400040307141e484a54000c2c0400c0e0720a85c0c1e45181200925041002d01c0d0440d500b01d00010011441503481400440d801c3d40103440480412009204030054144240110000d2843c02000455003d040018054008208400c18103642f020a401d01c2204200c1c04200c01c20b90b00306481c00745e995404140702ca840249010310080c1c003c030340003c40400c54000821802c2030144620024003495030f0716110075007009a502030141c80391308100a5010558000d00c0204480f1168010312030500d640c680400e81400b040c801c06035469078081e01049107601d030040310014501002c4c03e200b81481c0c1810884149800349000b841c07062a40040e41002c0c101451050703524031301c0c0c028100c004070300192 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 360373048 1250 360371798 360371801
    0xb0307080a1e020d05010f11040602070e130c0b0a021902060d0b030309030a051c0203090306010605210702100f022110090c090911070f060f0e0d030c09080f06010b030703060e0109 79
    0x12030050049450308e0b2008014801d100101c0d003c4800c181d008218107410609412401c0b04060503405a00511100050000b690441c1c0c1000078003250f160280c55401c00b542c081d003030a8518605948803144029000010313941d21041d14032f0101d03490b03c0040c078100e282011900d10b11480741c4135980352013101d40080030000006030310310b0403c0300d04200e1b40c01c10460120a03652405000340040d4140c01400050016500c1000a083d2182d0281d005100c441c02e8030021000514007a80d0f1080141c1040c40078000461482c012220742045407070b01145065101114001d01080003545800602e00038004101010b035146d01181c06406410b0080099070800c910103030407410a031103800d04040c244110000d810004a0a4824480c0c0002490049816a548182c010b19003c0704041ba03142d5110800c040c0f283e000c001e1510000600c4e14001480e030400100074210f03585503480b005243e8050b4400203030302c0340003040c69030440d2003e826064803900d6015094000d850940c0080110201e00d100004110f483c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 360374298 1250 360373048 360373061
    0x30c0f240605031207240b13020a030b0f0603010611010912030501170609060a0b190b0409060504050c09100504031b0f0b0a091e0b070f0203010b0307080a1e020d0501 73
    0x460840b80c0c558000f440d107020900503010f018000300c5408041601b03103a400d02560340c084d0500340c000200d80c40f240000420203414078048140c816800700d46200010b03014490150625402c03a20042581c820034006922440140240400c0281180500c03244074000d40003060507942c016020007200d07204000c0100200401d208102002c00c15800300000c003040030428501a01c1000007034a07050355451a03600240c0b40e00200c1a800440d10310049083e0302001848601504101e94070f5680c40c4d03c0d0610f42003c1d180d8a405c0742d071003286800c00f480030105031881200d0000d0003d03032761883c108101c00400da4060250740e0014040000c030f4004402070b50f5a513080700094611071003440f030328031b034031110504900c2c0948040701e00410a0310b1403d201680c0061705144600c480d40ca6900920307074451280032001d821038401200e002408008600131132800380500c2860240c20b50060540307900e04a96075031399104085000c0c000c44503001d0102c0305a2426500001482d4000d403c8808008107441d01d940240702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 360375548 1250 360374298 360374309
    0x1306140f030430022a090a05070f030c050715060b07060e120a0c11030708010f020306150a02070e0c0909190b0a0f031b05030f1501050d030c0f2406 65
    0x9200e4010003d80c48501001c03102925035030050850394072480b6011010020700f84088100d5030400c038402c0444e5200c0301c03054480d01e111080800c2c01d0070f28030381c0903154124480603e000d05041084102d80d10394020150398109810666501040003008649030080416820108010310700007810010b010968000d0820a100302040703034140c00d1248440c02c00341c0111361607880022041440342010544800107042d000d800107055412581e0758081c4242100c04295880321182d0f00031003089030b146417401e01041c140c41c040f001645031444507d0000d44030041401a0340c0a006604045200c0002c02c05c1591030001010b4851101418401408201901001041c40c480c03414030f100c00b4464100000d504007201c000400107128941540d90750b9001c01c4072604641c5140e0511100060296000c228940c2025500d00c054011074107540341003806a201608124001e0070190080320000790b0104551100310f0300001c0908852899280c442c81e080f034044800c40841e19203c0019004d68482d40c02030003140c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 360376798 1250 360375548 360375593
    0x3050f0f07050d0c050402180603070e030c18010e1005090709090b04270201050d05040b01031203061212050702042c0a050c12070803031603060b1306140f0304 70
    0x203a0300e008008004034903c0340240701c0c4c0307640241040281000d4000d0502044055800e9250f050b0719000300d0b8640c0c0046030030f0f000140202800e0440c906050240c40440c0005482150100b01210012080b0030011710410b1469903001c0300150080500007040005032400a001d4001800c0030000146010814029050001e242c601d800d600c45ca841e200b885c24488224241103400d42045450300200d0b201a80141e042c0030b010400c80042541c20303c07a0701c0c403d601ca045000c406504604012485400c0718100c04281842e140060080c0402030305084603560b40710f104c0034140c0f46140d004035658020204025080707030401c010324a42e801d078256048840115080300a01034241100d84a54901400e21b001e4501d421405d51000d031070901100b041440101c3c2c9007102d61083d40d40c10b44600d5580225a1400c0070340f89513522000d032130381c90300031900241544c0c8072a50401c2c6115003030700c010080e20311805052091850345004490440e07029944540c0148040c192245490300780304226110380040c0c600c480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 360378048 1250 360376798 360376813
    0x8270109050301150e18030c0102030f060d0b0a050c04081203090d02031806130b0309010f0b01030606050d051e01061107240c050106080a06020d0506012102030a0216030f03150b0f090a03050f0f 85
    0x1e00388034400340841d9030803580c0fc11054443c0c082c1180100b4001e00000184003081101081c6501c04111580c490b20741d6180651792031400d15441c908100c8603151043c110740013004203210308100c0700402c2915580851b0040e664011000b4580c1e0100d10641c41110544004000c1013401007041d44a01c9410310b20800510402d040440114100d0301140181c0c0c001c1744c0c1c2800307087c10f4105142d001700e52003564144003c0515502c0c200d07000c5030490991040c40094044880501c681100303212442c0140700e2803d05114001420800041e482c2030200360f41c040000f01d0030340070288603094000400810000d0185c070035050480c10240c000e03601c030710340240103141414082030301540729089100c03000012622420b400752442c001380e006540007601011103283c091015500c0d00401c10400c0032501c1c42512840350010072000051b00b07964680c1c000601c00d080e00d80b010050183c08604480c1c20810360f00b05155144085030018544000a41000e40700f44280ca50010420742c0014a0b181204031031021602c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 360379298 1250 360378048 360378061
    0x2c0a02091b0f0f04050607081c05010f030f030c2108150a0b0a051e03090607020c010e10031407050423010f030908270109050301150e18030c0102030f 66
    0x110403074154007a1095504002d203801002c000e0b0050702c0280b4404080c0c1c0c0c80c16a8450005060b03410003030064601045c0003600340b9200a424103044003898803804c0601040d8500f0241c141d158180e880090840b140c243c58050425201d100e4015001d5400300321a51000080f0900c4540203801c071110703c0c040740d40700d004a00e00c0205100090300d01c9200801001c0e1641c21300150010f81d0708408504001c2c483c091282c0c5156502c0c5130558005c12203900c00c3d0b6503c0381790030500c2d203241000103441d48095401c0b600540082d83d0780300712050482c00c002d4808510001c10b00138100c00411460080046802e4508240702c4150b031b000c4010012075040a40c980240c07201d08030000d50b103404a0584601180d625031441c40ea450094004c90700c1c05014803c101d051030030580c3e4110a642a000610003c00c8104031145050b42e006412000649402e0f00200310540e01c0122035141c141d0725000c0e9812001f020f0340011070403030804014013402d45c1c64409880d00c0b41d25030740c0e10078040d4105072130b055049120315001480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 360380548 1250 360379298 360379321
    0x606030f0b0f0d020a03062d0212061c05121306110601050d0c090207030f080a0204180b0607051209150c100b1f2105010b0d2c0a0209 59
    0x4803407a00502c040c1c42c0003080c10401c038001d02850800c07a0402a5958000081600d510560568034600a030039108241d810101300008404020300d400302502c14022525503d403000c0c04290f118205442d0028401410300303c6450b518140080185144150840708611060b040d016003040c440384500d5401443d00c9940c15501e054404102104c1948079000410682c0340200b80c40000d240600561035405803140c2500c0141d034441031043c4c3c0407030b0300901c05d061303407980c8920b225604c440e060408605203030130300e103240e0750b40349032071a20941103901d07041150302c260b40c3c8804480000e9841812500948c900c2c0d00c8004039608580300c100c1c420000f209419030041c41202c2150719031a900005030904c248062800c81c0148034000c0c11540041940380e0b01c2511000e0780c07050030380c01d420507100c50342c0c41000720755041d6809400c42c00c00c40e0760908040c010045107802c10143c804036580c80c0000f2810015090f22610b040303924505495513101340e6615500706440c00f1a6000e03615000b501c14000980d2041030684 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 360381798 1250 360380548 360380561
    0x140304030b040b0a1508060f0108011803030b270f07020601121401110a0201021201090204080c091b0403140c0f03031918060327020603010b03070c02090a0606030f 72
    0x9201d03045207000100028441800580c1c0500c3d8940300140202ca4005420002402034102007043e921403001c2c8841a00289074260040c502c0340000c2c00321104d01016803442042c0310400405064960001d20415540d550041e0038000768000d18481e816003109034006144025110541030030104008a40800e201052143c103888c0007081e080e12402c1a90780f4102c000c001524120429583e803034082c1d0003504002c000380340c0f000c2942c2c000740e02d680780c22075084500c01c81070f0320850b0414410401080f4811006c02c44107203401c1c08440c803880c02d036200c01101c0e03548110031140707480042c0c0004000c8100f01d500c125009400340704074115040d55070800103101c3e402c050401d004c1d61607842402480c090030303064044c078012844507240003203030400810009210380700e103034100340082500c4075080b21340d400442130f0366040720b030040600503601000c54010400d144010301803882c0740d500002c001884180561480d00304241e0150801055190070201f001c018210b600440300000d04014040c00061440c5c001c03503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 360383048 1250 360381798 360381803
    0x3100803120f0604090501050903220f051203041203120e0c01080f1017061506120c090409021003201804050702010b062d040608071d060403050a14030403 68
    0x140215100d140141ca1403070b50091655502c02c4d02c07076240d80c002030300a01803207002d01510001180c03101c00c03904030f52081d000500d004140d001da5042080100f26a58001c1000312030059174582c00414588007080e0840c0300d0ba4024454480301e12490714101039200d600b600100f030500404100e00e405041806460f110300ba15101d001904143c08141a10300c1c0c00102c41e0000046400041020342d55400189a484000a058842d0300020b08204076180200100c2805070383c11943e403464018207a0303046d034281001034030f404020100441c1350010340e2540d42c03006900382d4004086500d00c086900004001c0c1030107040d5510031420010a04000d180d101c01911018608440c0b007010b8a241241030100400000f81004219034070341044a0403a00c42c400140032801c2402c800c44103d800341d11703480c65940f0842d00b074080c440404003c10010264040886604405030b80350070445d12190840111911007109086a0312000c00500001003010000c1c00f05003030741c8103109100c000b400c07a1030329548130f00652101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 360384298 1250 360383048 360383077
    0x9020a0203091201150b040509010b03010812031003140105091203010807091e0612111512040f0204050c040602010b0301140c07032303070806092401090b0c0303100803 74
    0x42802450083c0f84011480700c9031000041c0b0440d6464440846603031984418013000e0001024840d07810720003c200d015180c0700060f54519450699455990362000d10000481e07840440030550311890200c1090040d0303080259069030031480001c00d4020001a1101880da209007414050441c41d08000d5038100c40342c0710042c0002c2494041c5002c00341c10403880c1180012141c80341001c2d000654440e0720060118031148a170200c21502d803860500000c0303800f162103171100403048a040d0240c14221440c00003640c500c0501038031035140c812400c500c2d0803002548941840c040180d865030b8903024000301d410660082c828820f500c810300d400c8610300341249182e40340c4400040c8010200800502030365201c1e152141c103c0700c8800a101c14081600c031a060741c06000814018201d60008103240c004070111020269070070451400410709480f0203000101c0c0c6015038031b05405e41e00a05400c0014040241025510b900700240e042d241d038421521491200b000079408100d0060000c1a120107100d4a0700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 360385548 1250 360384298 360384307
    0xc010807031119020f060c120c1b0f01051f03051506010c120f171e0c22061806090501050306120327030d090e0411150408010609020a0203 61
    0x48000d482c400e1111007020004109a00b0b0480c550000c00141100d180d014100318800c91350900d0901c20050b080306003410f024031042401410050361a9040407022200c2c90791101148080c5200d102c80b9509007a8a000d101800c4134100c0040d0040c2d4895560701c42c04800c2500781011034100000306020207400d544c0520350002c0f8150800311540d0300310205040101d403000d129070360200030001100c40000042e50001c4007131540303908680d4411000101c404152030741c0c81c11010000300c054440c00101e4194030340c800855072500c0000211041c071001440c110040c2c1401c4085440107035074910603000000c101c00c40070b8000a0b80340408000703a0380d0300d82c0c607151941d1070701c401104c642e04007810003a400a141040110172502c10030007800440e081550907111803d400c52680c00080c0300c1c0c00d081c0d00940080803421800b60340000781c0001d03252000b094a0450300d80e4100b44410031000d1640d19085025024183e0700502180003803c1100c030954001d0014644654048050740209541c98015074004d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 360386798 1250 360385548 360385561
    0x606020d02100209030a050f100b04060621180b0612010203060a090902061603030e01050705090d061a0d200f09180f031b161412010b0402030705030a0b01020c0108 72
    0xf001041d07400e10040032030355020030315110703541422032180185105a0201c070340d039030004000c0e0040c0320600404903020080c0614101c000781c88144420b10407002041d500c20785500d01e1000741e0105030300c2e4400c010b0030b010310400d905e840c4002c1074056548a00c5003000c136111600c00c03501402103a00c034103400b80c208800706107410701d00310107842e0141d412070b4400c20900480c209501100321080f0023038000d5801103040c0f21190800382c01c41d5000f420400403c5410009101a61910128105880c0d4404000103901800508e09040c1c1440c070700d00140d000000038811010310045452806140c01010300c81110f48c2154002c000c0001c6a00d00da4076000312505000a44544407204100d00007101003080e00c0f40d10100094050450348040001c800e0108401401060311404204150340a07200010305903403541031041405a01e107040f14580e00c42c642c0c2d1440d0f8006030200790000441d030503000d00250b44a082c280009807440d081121031040b4149070000d159050362001442c018080410307109c001d1181c6824 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 360388048 1250 360386798 360386801
    0x803130807051e0d030207051824220b041a0a091404030509030c0306010e0739030908060109050601031a0f1003060f03080c060f090d2a060f0606020d0210 68
    0x184801d17820750203021f4000500c2d480307505c20080c0d503001c1d00840c0c100610300041d00d21400a012140541d1011400c0e480b4601c5498070401502484050032480d81c00c020820f0002c000703058640356013604181884801c1090085584070300742d0503d0b049034402d00154458107a00708944043d0488071500302c0c01e60114001c03034040c00003003080c03000c01340988903c01400400300c4e24280c42030b48141d0050b0070010410654a51026003130b45e03049140c2740008942042468160301c0e048402d00d07000d194580300e180b00010180204924001000d0443c242d81c10b41d0f0b502c1300c0307d4008040c126602400310341000035402c88007126480700346000c5401014486200d155a00b8800c1110401403c2000e140e80c41d40041082484c941c030703210065205007180f0b40e94800100c050ba0916101905000c072040b1510b0a000d03400c20301044051103540c070b52810007440151100681c4084600205003001c0c0301c0c00f11229401c0c0901c0d41c0240c1c43c03410f0448006c1c000c203a40e4400890b5609400000383d00160483c148180c4c0031100b6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 360389298 1250 360388048 360388069
    0x60503072c06180301061220061201030606180207081602040605040207050304080c060a020a0b04021908010c031413020603090c0402120708150603070f090803130807051e 75
    0x9200042020010a00880c1c0c4540c0030304800c180c50402d102000c0d003d442c2c01d0103100060107a07103d407808010129030760001d107204c00b00d5003200045000b1840007026180d410a0303801c2200155180000c03540d40c1d0500d440100f4490198080c402c0385601a40c80d001428000c40350351a502c100711500c2d0110300303800071880e40350591049078004d8403500e000455648900140c91400c1c010009542e403589400100c030300e005107011045008080c10310440003210340200e0107c44041e0051200d03002940c035072000031091120b01c1c500c400d2400000802142403030055000ba800e032000c0d61801c2003406031481b81040b0700304084803d01000d0700e020b0220001820007070080c5401030070050844485503550800501660040c138458110070f40150308200001350b0001040703410050440070301e4410500100824514800101000d09029510072007411240c07003200054020903200090b2903c0d000040c0f0342e2034031852680b0804c0e607a44940c407800f040b1403030220030b4407450401d40080c225100502e00d01f84800c4681 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 360390548 1250 360389298 360389357
    0x9010207170102130915170c042c07140f0102011d0a150203100626070509030709270f0503040f0e0a09120305090106031e05010606050307 61
    0x145240014007041014480c4860080c8a030000d82c8134014403803080322801166000034011410021000710580d0000c210304203480035806096000904140850300e003100c0b035031110b90440e2400e4020603070521402c2282c02400c8101c01c8042a28403412041d07940c80000b8007031141141003045005840740b41428040c05118010b000205007100c50030600160101200c10481c0117405c801483c5040215040b410030109100600440c1542004048895098905d014030740a0202d044500e0551102e035100300d0700502c00c1c80407000c41e20310305048000e100e074000d40042d9006e40318070030740410508528001d2507000d100c0e00103804903044103411050555130030110103907103c1c980c0e0080240410ba0070b02c0100040c01d03011400c0480c0906e051200010f5030001020b1070f00321498020303c1000500c0415600b04808c0b501d190200752074580300541030040c44298002411445400d000c0c1080202100300030701260702420003000840e40e660410341345440b0490b101e8000400c00c513259a018003c0c162004580f00b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 360391798 1250 360390548 360390553
    0x1030b0a0902041d06030a030203030106050901140703020c0f0a03110d030306080f03090a1a03040f14030412021008011802031f08030919140d0503160f0b1b030c090102 74
    0x141d99400344022603006411136114007150701210402211060380c0d26030040025801403040742842c0d2002034a038081030080748100f03c000146209140e01c25492450488040c0d034840350b0358240c40c0f80c040d40d501008107803036005200345602c03405245070049060088036040480c0c6d4242100c6c9400304219540c4442080f803d2550b903281c046016501007100070201da01d4500295550178601d03041060140c11503110103013200901b030901800c00c2c110380a5039002540301040c410f5501903880e00142604103220541c01c24800402c0004045a0070301c1e407918605e00036a1040d500300080003003103550230001d003d8843c640903ca55495043c083c070364000c65000d0620b80d00b105500303400408890311041c540d40403280c03560000c240e03c100d515002c02100c5204100c52408109279151004140c00c044000c1c0030b1030f21808802100e902801030500031907103032018003000c42c581102207181c041c03201c190030001503810a0f03003000014003a4a804407105140c4004604440c21661522000c18590340014520750450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 360393048 1250 360391798 360391819
    0x50d0e060702060d14100e100b040905070207081002180f0102070605030c0903070608010320010801050609010207030501090807050706080403080408070f0c15030c08040c0b070816050c090606090f01030b 89
    0x1c444500d2054080c406c0d11a94500f45440c01d4545803c8020251440e8038045d4407043c10414045104110f43c2294400c003000715884da01d8103030980c10440e240d4002685402134089070f0907100c560354010a0300f9403040c140d02c100040c01d81e00b4000110302c812001d070f0269014410500085000347c0140da400b00c0c2002c0c040b1300e01040000440d003040642e40c00030012038059030060040041d2030700342003403513540e032044015070b0104d410008213412030600c41c0c5030081100003500c042e1039109001d50f00c003a40e0424028405240c89250403182540492001e560034002d0030000700380c5621032141ea90090ba056601c1d14069140d580380c0303035541e60068508850031403402d0390274400120945200c0c0004c264050240340a00c4582401500b942d0f602c0d0a0a0100b0105504100002d24408080001d458881c2c04180e11943c242c500700c451442000006955076184601e49410043e001a202410202c240c40384820b07903d40c6c00502810303000c0c00080c2c030340c402100400c04026520070346c80107c2c0031034010000c2c10030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 360394298 1250 360393048 360393071
    0x204050f090421090302120604030c2616110d05060106050d020c100c1d0d0b15090a02041409041a0901181b0b040b070b0703111204050d0e060702060d 66
    0x1c3e86200c4485008103814150070815032800c4118401100311800c0038011714689a47d000f00ba9590004000704120074216909801c070b15100d40c00d071281003405032407960360599000400d12994010b0001c5408240301c0d80c003082d1307c0c1003541c0b840ca9040c0d8040020403e84e4201001524540c05c2603940c00907240c0d080c000d415529408100b41d00d511280d4040010f403c0e4030507103004080032182c030545001b40c02e402080110036142c8040544105401c04104032190b00e03500741c2000c0c0002004192540480392405003e06450164020301c12075000c0c42c01c0c000c19081c0b0710709000390020111005860f40a2206040d00030291940b05598030400c10400091000108284840350000301c000546410a5042d0850840740b0361085000290500514a0b800c05203003003442503c500c10083c3c02404039804e500030407400da0181e01b111104a402c02191906d5000c00494514204400c0703034103458920800c2c0000c4110b0b8080c0b102068252805480985010210740901c091075104040c070040c05555080c0903081d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 360395548 1250 360394298 360394343
    0x8040809040c050a030f1a040213080706050a1101050601081302180a0b1306050904023322030201050a0e0d020406030501050714030708013305030702100204050f0904 73
    0x90340100e484444c2c58149210b0001c00300c459940c0001020740c03901d45c0318810100c05800e4a154840e04a81c0565035072030020380769081710712a030b11480580c803a106000c0751586c0c000000e00600c3c40c0541d600c014110005070f219003030301c0f01901c034140481c0c14a00420611000da822500699002414060b18080d000e2401825298220381c40c2c81d03206d03514280400d40345402c403c0d0030303404800d5500920a860501d40024040080540001e1141d0541d4000d00c00344221495013552103030401c3d89500240c9002600c2942540c01220742014450b4640d402c1034030b07103060f904030000352901a0341c1c05007020b0041c0c4003542c2425003000500c0e80800c8645503034006a0750390044402652042c000491242844203014044c3c0ca1009141c490b030f03c60910400c00520384c021191811142201801301c504e8847c04c807040c0181507040341c40b034200004410310496043c0c004005500a5445500300d944940050745000d04900030790041d554818440100f13021240303400c91080d5009030007082c090700c040c40c601c00f0086 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 360396798 1250 360395548 360395561
    0x60102150a06170307020609010c1b0e180f0a03050c0f03070f1109010315050a0e0d020a050601080706050301031506050a09050703050a060e2710140a0c0206070804080904 75
    0x1e00c11625004240200b0b01c03001416844000350500842c00c0040b10750010f015030062030415410000d52203071050901a60010b04905000c104000308182c41d1121403440103080121000f41e0030680b400a8480300210000704140d001b103051015019520084e942210f050b0301210384c0480c07a02ca103500104501000340b001b445c206204406e00c0c05d18016074a407c401903813204a042d44503c500400420114050098036180c002c054100001c4a69a00f0310030002020308070801c2a1a11071000030b11440340d00041c00d55013850050007101c0b010707a40c80300c00715618035113801084001002400100000b9200c3c400041175000c2900d00821003d07204d0010039800741d80ea80c00007001c00e4540050100454051090640080b00e0003800d210703080c1040141d08880001410a0f000e4031590384c258140c0a200c80c105124108140050b02d001000062003000030780070190310b281a0300b07030030340210300e28100e10300c61200210f5550300a040d05a5525809039070220740180255400c1d10b082100c400d541e5164480e04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 360398048 1250 360396798 360396811
    0x2060c010c08100b040602030307140f070f050601090b0607080c0a08031003060f0603021c03030609060f0f090c081b040302031516020115051903060501031a0705030f0c0306010215 79
    0x140710314036100c041c2009a004a070b200e9113100c0005c100c140b28013070b404411a81d00c4201c0e42020300c1c0500b04505440c4803072041504852001d039002c6444d1040140501d84000784a000702e00b1140982d0302d80780b607070701214404412158058010808100094034160140001003040000d540c40d940054485004941c802c4400c0c6001c003ca00303c0620800c10300e40315440d40d2a40d11041005071509540c0414852052032400c56004400c4d445003000b0144039801c05005084001c6061051580c0e4009440c01c4541d5401a400d154940032070100e00d1007a244503041c40080c1581d1482c07060346400c1081c46440b2a54210068025010040400583c0b001c101000c00c101b01c00f410100d00d0b24141c1c00d502d0b42c180d0020340c41811a410034400d40410b40341c510b070004c16110101c60340702c1010110786071200302004a9000074041800d241c00041402031041040c200c44032440340712205641c4041c0102d9441c03104440500c4a8440c609c042010781c0f0030720010b0341d8861018011200401c04040c0d041d00c01c2c140c1262070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 360399298 1250 360398048 360398057
    0x1e09090607021b01050d0f0b040f0f0e0c090f06150c0601030b011205070b090d0215032a0f09040b030a0b010501020709090302061323010906110703021902060c010c 72
    0x7400707405075040144034840701d9042075040100c40d0400c0020141e1141c41640303001c180d120f40b0010408015648030220030400100304204001c1c1c070340d0340710340a448014031103224680780110304a038a02021a0b400070b8104014030700039140e40c03100f07414184141c0143c41c9680280004040407250381502e001010348061420042c101136140d0720f8020318000058002d80c0b030002c0152112400148001030250541e000303032501540315600140821801c0c0040200650301c4140b02e080c1c046185c1c0c807000114000c2ca29800703081d80010140c009480850008100201841c0007000b40213104c041d40b40140820000041c1701003070364521540000e01e413071001081665050f070407000400841d07030100302080040034114818402034504d40c40107511000001e15402c0c00b51004260b1070200005408810951700641d02890920307010000e040d40200720542084408518110001842d5040782d4240c410030b175819402032540044003892554a1040400101d030030150a001c0091100030a01601c0c03041c076400d42d20b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 360400548 1250 360399298 360399301
    0x6071a07050910110a140f1608060a020f040603020309100911040507020c060702191d0108190c03240c0e04050c030402150a0c0c0b0307032003061e090906 68
    0x400c149603c007900681c0900c000310342000000400481d8075440c45401a810740054400110032904000c102c0060a00c00c1c00b030031039101032411040614106442d03000040b10110784d100301281d01288a0f03070a034541c000c54140000c1180c603101c0d400455214943c502611803c0e01004243c4c0103807400b0160484980708445034400a50825218542d400350303d41c40209615400e03580407509031b00c161000640607160980d40801c6501c038240070000117002040280c610508003500c8850381c01428000c03110b060080b00312520940202040d22801d143d000101c0640d036a1840e038401d00300c81c0030b103022104443c84c1842c00c0c004882592084008030007164980c070703492852000400c8100e9100805c1c60309103040c240103103c05078541d43e0a21070302e51001c032400c640e10b143c118415079568142d5040201500c80201002c21650340c0700c0c02840c011900c50703c051103102d000b0110002c1c0c0012130704004142d0441400000d403207242880004001d01c880000c40e2925000e0f40000c201c0c01d410807240c002d4294444070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 360401798 1250 360400548 360400567
    0x30e0a080a0e032a0a030b0906060a33030b12070501090b03160c03020f01050915010b0307140a170a230103080301030b0402010905030619060f0e0606071a0705 70
    0x450800b80300101d02416400c0701c0c46564409005007994112580702491070b0410243d180d0145241c081c41d00300904030014075058400b1980c8190403035200740075070008840019850040d610040000070441d12846080d130181c2600d20000c2601e4204408140d10307410900a5601c441000c1c9800e85010005010a0740c1464009411540244e01124005004000300304e044d41d5403074610f83c0310200518202e0840d80032810201c1c600040007000e108a94608002d0001381100051201c184090b15140494582c0e620b020005860104459000100310761400b82c00b00a44e400c4003d25900362203003000035008143c101e03103c685590449400b4015a40c95104800e0f903080742c001c20300200f5940d01000203640c1142e0702d0f8002404181b000030840706000380840d0440e03004851400240002030203c0300103117031000c2100704010741040420072007440e0160200e48840c4108455080c0d62980110351001d40b11501489480c2e84210002e0307031205c0201241544100580d1000c900901c030319910300b51586401e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 360403048 1250 360401798 360401807
    0x501050a1208160618060e16061409061c0b03010507111e1c0203090f0f06040605090103061203020a110306010518040c08070b072f040506030c040f0c09080c01140703030e0a080a 78
    0x2028403aa2420303401420443d270355114401800c8444041e4809882c2c2e0810b1021036610b00458507200c42181080444c0300c82c0c0d071448c0c1d001e541c0c03180301100280142d4649440540e4003405d11078100c4025009419891294451240e440b030344110070740200d583c00048404048449201040b443c0c0058100059141c524a080e1200068618040b100020003124620000d1014800d61103410309120380400d000000c2d80c065070045008180c08500724056407001d1400070345490081004681c2100d81201c40c04060500145d002d041e20b1001d420020381c11607036400003049460042c002c6a440e40c1015010908034800c4c01302500600f07504540584039501840d000264042007040300d541290604081c01b4040c0340349200541c0071324150f50000d02500c410fc0401d0800c11001449a001401c0c140302c507000c00e809070302c10080041c495880c00001511046e18544401000010600080c00c00c401840007450b41e800920169129050001d01d4a124010441c01c081c08860305640b401c00c0800d800c220135412 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 360404298 1250 360403048 360403063
    0x1a0415060e0a0e3d061701050a0902090415060216060215060f040209030610051809030d05060a0807030b0703140f07110f07090501050a1208160618060e 67
    0x40350704000c11401c0001c3c44002c1100204550010b00c0342c011454001c0c05002d04140e0820201e240424503000d018151642148062080400045d2120307030321400d485450000c5030580f04c00a20010600f0b14103042240070f500480c0895500550f111920018410241425401846030750041c000015090030f02a0450003103900180070364000c40c400c9044c0c211061043d0b603000504031250f904121890340480e00901421070800d07094442c89080c0801621803201590880702d041344c281750040c81c1c095100841403011b07220700042d0f501c2404403140c04211034004640c4520302401c0710250780d0395407003100e24148585d8419266120084144000160706000312070a41c0903444030100390341480803d00e03040c1e176002400e01c41001b540c3d04403088030309414040015500b500f5011608441e40390700c4032400401c0217128285c450000140c00040a400b100b140c506c00a07005008a410000424510319081903440e204840c441c0d034031000000003441e400c5100303003020301071103000400071180082c240c0b40051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 360405548 1250 360404298 360404327
    0xd260309010e1e060609150402030a0b04050a0204081c0e1503190c0f080a021b0705040c030e0d0302030901090212010c0305090606030c19050a270203070903061a041506 74
    0x504043c40c554040c0090a103800110039034044d042c47da9102095a510000081d015501c14000070603c800c56034183c10988810748205d034100013546502c8210001c030310541c807440c032040c2c00c5207007000107041c140e0211810030801c40c201103002d8500c000c005690800303030b581c0c880e0011002205028030b0320048082c40000c0402e208041140d919640c0b006030004a1142c648810400c0034000141c0f81d007005c0e01600c801020482109004602480d03440780c41d061180112802640360a02c03045000c1e100380180444a844400501000e60b06160308801035880280810595034aa880000050321218245a8142c5c07004000140751301d0440b0005080c1c84002e4a0102030b6800b0400340801a5800310785900c1c00c240842c0d070308400c2a541c0041e03d000004580c405c40d840b0310700352800500f01c2c0d10501c8412441c0742800c4e42c1080301540c2000d0400303d001c1522101c1c0051205981400041e50030350240703444c51005100204040b86503c001010b803501c0094100058940303900c04c108298002c50714403030191 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 360406798 1250 360405548 360405583
    0x102160c050a0e060603090a02040e1b06130501050a090e0703240806060111100501030f02031c0806150c06010f05130603050a0b07170c1806090d260309010e 69
    0x145010502c1c0c8003c074014044c50300c1010b0000100341c859400b04003410009030302400a011010810056a0701c0c0c04070480341680994040c018040c403403404404079121035000100f0720707000506101c01102e05810041c03840d024000095070101c3e1442c3d86103a503520074400d550300440d02c1716940320080070300e81059034851071035000c200c0b040c84040f101080703259000b6400e01c0c00102007140c99200a141c01c1110300c420031040d24090001c0305201c24441c580035070314000e404842c02050350340c018414141416070301000045902010078107501d4154916410b000081d18030302e040c00001d40c00c80303080510030307401500d501f020401c08200a00b003450b4503c0c2d040d84001c0040084a00e95100c03503481d052080d00040c40d11201c0e0340003c5e00e060103190103c101058132108050549800c1c4031000559000b02600d1002806540c06001145410800c5960031140a000d1400c550415580d0000c69810300100007440544040841e414110303200245214002c06c00010582501002483e4103143c02c2181600042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 360408048 1250 360406798 360406819
    0x31b06010f080f10050601031d01060e070801030b01050d15050a0b010f020102090105030411060417011a040b030a030f050c010c090e01060302030709030b0a06090513030f0f021b040e0102160c05 85
    0x201c1c01304180b9440b000e0100041419502d0341d004038000c02514030301c06401d11000043c40c22594055110905aa00307181a0000c0c90f200d4180c240e803800000d10000344982c44140060000d410200d0815030050702ca000503054103507000d1200341c1031383c41c1150311103100e558a213030320800e96a10500c00103059034140021490000b5803800240309110060002e41691a80d803051074154580c1c0049400402104544841260041c800a400b8001c1d074040d00b2440700c2d0f09000760030b05181911480d1120b00000307008080340e68450340c0950390f0300b214a01d0241440420300602c01415800e01442c50740241030340d5003080c12070030203050b0510300c44181c03c070004041c410300400c003800e40c2003500c00091b00d4010307032a448240d88507290800580f406030044844241001f041c010603481d076003101340105100303494036284103104200483f9903c00b00c120080c0144e0102c0080700325030320508103600e490040074101140291070203460b142a80e11040308803550a040320400000d10869184030310140008440e00900c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 360409298 1250 360408048 360408073
    0x30102070f06090b010e070e271e360c0307060c0302011b0503010b0f16030305041e03080705071109040506011e080c101209060f0b01082502031b06010f08 68
    0x3e26880c400a140900442c1441150b1078090403000000c411070300c4109d03111850000e0010610141c1c0500030340301c05d400c48001c0b502d0710702e0004000410099840240313620200c0300001d901c0c00d14003510502410300847c0840f4810f600c00b840b2010103060607031a210540381c00c910b0024215100b40c20354802800115140f52ba605e54000100c81c111007000c07559980707880710303003140d03211a10130a50b4401d0035002e006401400c05406030820b038444c6000c1d98841191300c1c4842c40079810050070b0203009000600c1040008d08550044002d021554041c40000c4030b4007040d24003050b034025056609460a41c8100010400800c544c0009072070200d00401810701c4501d01300c101995010400c1c00548909203806602c410248500c01c601b101080c0c00c030381800301269500300800141144c94440e1441f504007000304220354000d0f424070b0300800c41c4100d4401c22582e1440d8500100d2501c0c18400c08500082003c0c10003c0032003e240c4184c040346201030002d5500d4031001e182d445006a021701d025421240c280d104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 360410548 1250 360409298 360409307
    0x7050a0f17040201140f0c161409010905100f0305030904060f0b090409110904030c1b0515030c120a0c1805061c021306030b0a0f081b030102070f06090b010e07 70
    0x100b10f81c0c28209224900000035009103140200507000c0c490ba640401c41d504c21510015469600b000c000010580f070b5521078010a4250034124046a000b019010042186030143ea000f5544000d689540414403074403100d2280c040282940103030780a610100700c2e400c452400c2d12800c0000c00414616038402c500d08040c0b62158094210a240729650315a42d450500181e24a9580300200052500ea5130f271615103005000300a5040003a80d4082000300228684180d5817500e0302030301c6006200c1170700c01200a0351b0710896030005000c0800d130039042c40045210584d4150f0175004101c50000841c08401700c040c000e114804e03124070405d5103e1400c1042107552140f00444a55040403030504800b8084d1510500180c420440d840403452101b42000800c6903140e80441c0b9983ca003146d103c10303840c0d074817407908169850701d009034813051700030b101d4140c8900c551010810116002400141c10b22941742c845040b00c2150010960380141c580c2c25500402c40e255601c0341c05042a00c0f0040c80034109440000c1c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 360411798 1250 360410548 360410551
    0x50c0306090c0f04030c120311030405010207090908040302100c0b090c060703050a020c030304060c03120506100c030e090f01090e1c110a0609080406090603090213110c0607050a0f17 80
    0x520302c140009407400003035058811100a15005100c544845544540100f4101000e49060300007a4049080a060000c0401200c08031a0143d004118907400d12014500415241d00c085403205030400000005072104814003004400340d4681e9180306215040000380d0b490024850f02c0c03540c100e00400c160540e140c0382035a14280d01407514641318012030000f0f81c40c0c8020303081c1c450b40c9448046030000b01c0070380c04503c800b0080d120b680d40b0407000c44041d07068002c0d42e00c1964455405000752668442030740c41541e10600c0f260003440d100c18801c08150105138401000c1c3c4000422007904001440f00c3e6100d8003c0014406040e402007680c0070007041000785902c00001c040c010400440c1b402c11610004005400c0303040e401030020000030019107800c03192a4030520400b40410881140010428028071401e002c0e60380103000518007141c0c01201000030106032036204021001072091107103495040102c0c034031071b0341e480e104c150f51280190406804070000100180030051806168040c41e03041c4100c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 360413048 1250 360411798 360411811
    0x5040306020f120103050616030501030c06080702030f0708040e073b031b03010b0a08030304060f060b0c010e0c060f1204080708131d09061605040b070605010504050c030609 76
    0x16110900c0b90030380d404034031605800c0ba03407801d2000004828044041035841c010200225421464400e4003c15402e5a00910010307008400e9280c04009460040340b05030740c094001d04c1131b0ba00e041802614a282c80d004100251207001c4049401e104850101c924180c00503018140103000c40001e144d00e6804404c102a00c00c003800c1450803141d201c40000c1d40b019041c1c00000c0a80300110921003200103140f9880100c03074800e600b00f90100300c8509010a541c41036070842c1c4051455641d030f0362a1040039000d6280c00c04495660342c0000550714800c0390213804a02001c0002160003030801c1c00c0705240540780300e8064400c00c0100003003184200c000007191450a513403032000d2802d40e00ca0800c50700741d01403208090031900e000580c1180c9000021042015110001007440c80700198011440c020982150004504c1c1c1c400c0000c1042d0380c400f100030302d804400c240f42c81840c2036261078580a036900400300032100d86071510010701c02c6140034003400e80d10500808100b401d502c0d08000140040c000275000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 360414298 1250 360413048 360413051
    0x509031e03180a2105011a0924090405030a09050603072016120507060503162706030f180203031c061221170106050a0c050118140a0305040306 63
    0x101c4102d0b40700d0188200003803041142080207091004800703d0100c030001d0b4229002d5281c155007150260b5084519003e500c409004082150b4a41c0c555042000764034000b099542d14800c1010758581e07034042400c1c03090740319034007954403460160005054031607960801e0b445003000f0b1007000382840d4404520841d04d4650088810044030155200d8144100454414012507800501285643d0701983c1124854880c0044a000039a81d0104940c80d020a80c4e120f8030542408000492a5108280c840d20115842ca04100107000c404048a081c0c42e40703a000d4170119413105032014010780244140c5034148045107404c2d018007240e82c000b90f142c0c4120040c5a0901010340c21040442d1595441305020300155954800000c289040203003110207100100d0b0341c1c03d090344083c81c10042c406d4041d442d02e0744808810b48150f074202041696180c101516003000c000300c9450b1080810000d008280003603004d51040b440209041c14215200d03100c4071741074401a4040560080083d03480300840b012290400ca0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 360415548 1250 360414298 360414337
    0x20f0d05100e16140310062307060903020c09090115080a0b07030507120903030f1a0d12020f100603020906031203010b0307090e070806010806030a08031504090b070509031e03 77
    0x201035401c00104c65111680307034004010810450b01204104095803017a0b1070301100f10815440e079004042124081420a40c001c1c41101c0018440340c101c0903c4031b210740107548410a14101080a555084500760216034654816805610030601c00340003030030221000c2e014821858071072400405015080004140d038460003d000c0301d20490047c1001388107250148046002401c1c014040c08061030b05059042c68080152000c0710b00d55406802810003130800c0145982c0380e10b68600051044034048150301900300314080d041d100388903207004150040c0300011058154014416031700c02c010a15400b0360b01001184441d418084282c904542e00b02c0340303c541d05c3d03407210400c45481d141507120755103210058091002558020a40c144180002c0c2e0b00c07010141e848104155640103602e4014008020800100b100040440006003072440c0181000c00c40e00860303030716900048000c070381c0c04000440114801c203407483d051207106040c0001c0c80c01c5072210040e0076802e5440b80f04220311810304242144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 360416798 1250 360415548 360415591
    0x703020309101e050a0206060907120b04021b01151707140a050d03050d0c0f0e270c030714041a0d09060c0513080601080613050304030204020f0d05100e 67
    0x3c4010001080180c1c3d83d040140d642200601140c0000e05400d0142c080c201c00110242002d55400c1e125a0090b44c0b601000c40710224802d00170015001c4154200e50204107415102260151041c1d87c50b403c00300000340085d690130f1040c0c0c41030041d0040c2546036541d03010100000000070302d000c00e80361202444910586044001080d205440c0d104e50307040450070038400240364201020300215140404148801c02c20039000700d81d01c001202640300403407105007840d2003034141660280b413031004103440c1000f032106003207500304002d2084803040c83e440380000800944c181e10240c2c100c026919420481c1c105030501521380105091807085503080080494588124040d90b00046800c0c1d030000c0041080c8511039500614607030001100070140450800009521003000a5590407100e004c17000e007120340c50f0304019000017003003854161a9444140004005070b03440303200520000b090a038100395590b610600410070b651004181e509540000b0008009001903003240591105034680c81d22600005130707 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 360418048 1250 360416798 360416807
    0x1d0a02040b100905150c06070906110604020307091113090912050310170c04050709051c08090103050c0409020c030301031e1703090a05120405210c190b0a08010302090a02070302030910 81
    0x408804146d4440d1505110165030080c0450b01900c24030303580c2810f101c1001c91895603500c01030f41d0094256100d0401008008505c1d4800e505441d040d0040030f1900440c4403620400d0355540e0091342c1580d9507101c410007040090390005c00700c02d50314101141035240c40e20549200105621426003101c0301c550700d50a0016090002020040d030040040007141000080108082c0d850701030303d8045c121104000c20409015548200e8180e449030210b40380500301d10044000d050090030440614005210103c1c2010032800070300a0541079600464030796145050207552000280d0240c00d11011450140012408446034240d10500c003a500c3c541d070740c882054a51a11a04041c040c000b4016580e1584107140c01a0040007120400c03510740c000d09143d0b4440021b08502c2501c410703002c1d8000480d80206d81403405030001441a0403001031095a0f442d00c00c0245a0b0184681000041021006004500c0c1100b02c20703402070599182142411a60b507006503480c4542d00783c041c85074a02845881203c0c1c0b04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 360419298 1250 360418048 360418057
    0x60906050d060b270f060304020d0812090c19030201020d0c020f040f1409010605030d080723092b02040506060d1b2307080d1d0a02040b10090515 64
    0x2e0f1a142c580c2c0c1c1c0706046401d541c25402000003080c140e80703240740740d07120710f000c803001e0b0124039000344820701c0c5841d140d0030059090081c2c5411a41c0000500c407048260300b12103143c80c4110003490151104d00307200717000c00c001081c040780d40c0c21400c6150b600c2440541d80c000340b49406401103090043c070101d941d00002c0e0b0300c03061107100c441d441801c10b4100341000049403c00340c0c6207070081e8051403064032412801400ea4081d4014030f501680080f9080c2c0e40d0030710500b035031500405075080c000c1030b0701e03a80000d81603510501d1000c10000cd40c005141800e0b410050400f181c4070040072180302d03a40c2121580b5501c000c00494000e880b45440f4400303c0c1050781e910045418a1421540c10090951003281c2c2ca00318408041103000030a0107102d6404043c4c4040400006044808003442c0c501410340c7d4502d402a049888074944441d0b45000b60112090b28204192a200c650802002c503400c00c0d10401c41564154a122409060704c0316000d06c01c0c9402404110645004035000c2900401c2c282c8240114010b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 360420548 1250 360419298 360419309
    0xf0b1306050c070b0c1c0f060302030705040e0309010f11030315010f112d01020301080a0b010b0c0715030f06060806030d020102040503070b1b0a1b080312040b060a0b0f0c0705030601060906050d06 86
    0x47e145000c840001e440c0c1c0894202d9100368180d6142c20b03560307410070003103e176012078a0000742c004202420166116542242d641400c9043c24000303181210358446c5141c1040759611124400d40321003184039a0490201e681487c4c00345485110f4a00308071400e034a42c0d0302100b4251200200b03006040702c2031b00103e140b103880082000219103030742c0c1d2600340903600e00d85030b107060781c40031103017400440c600f01c281007168000e0f46910003c0003854a456008060303105100110810590340710074a802d0751007039004e400010030301ca0340c607401c0e1418a01e080504091918900300207580c41044200302c0d5440c0070031400206c50741c4800c02174603a10003201c5009610741c080603406c41c074000d82c440207041100401d8080038500703400c400c10700c049855800190352171048542c281d98030601100001c00107100c06101c0e50f48800003500c1c003900142e07240c00c0b01c0000e400c010351004440790b0128101071022800c20240c4010b0008900401d0954501140906015054000e02041100000d02c1c8202c000072500100c00600c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 360421798 1250 360420548 360420551
    0xb093003030a0510120803010608071e0815041a12011104080106091424040b03030d09060b0901060909050702120a0f08060103020f0d090f0b1306050c070b0c1c 70
    0x203051803000000f0032084a00100c4840b60003004118007007468800018160b200c45aa0f04c0e503420103000741c900500080c04d020030030020341c180c2c00b0704d0465922050f005c06000e890700c3c0743c0c500b46600040041d03003c080180d4011031400a86109081401c4079002070020140c4040391024003007642d40b8094401e40300c4007603000d080007400240c00030701580144103e4254103002c1155841d6200c0441111509072001a40c03054642581c1a04001c0b0079080410b0303c000030000521400d40501290a5030854902809455611402181884454000d000c40d100b000c0310030341d001d58100140588207a00901465440565540000b01340300d000300100d4030007040d40c1b1405d90305c0b9900b288000303000000f0903200b60005008580031550715400780c000d0340c0070800740e03004007410110b00c80d0000c401440c10700d0042e2085005074803081d001c05c503144070460103070b0212a1f0007481d15a103414400e0603204058840000309204000303410206141c0211641c0102c1d00b0065259224000b4940000c500100301c40e0b0440da6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 360423048 1250 360421798 360421801
    0xe180c0405093d080114010e0a143301140a0e0d080306010f08190f0b0a061106070504030b040201112e060b0304080714030f041503060b09300303 64
    0xf184510940ca9400012010030706015128151142030b500b034500c800131400281401885003030600315603154050050140040ea521820044074030300c0e0010740320044c1c000101d40c007103c0d1111038004008a00803c045049206248000000b8050008011003542c0c0c6440421080725480c40703207006050780340004001d0b1125070740c20f0411a10030307030003a6403013804196200c140d01e46480c06030000502c100c044d55680642c2020002c1490054049910302e081320559660039601c1c0c81e41c506041d50050542640d0f0420906e0308800386510b0301c1b0014001c1000d115044c041000050325200b94540e1042d82860301158a0032100080c518100d0350090f482da2030035560202101040c0820300007a41e86d00020401d003c0b03d039498046140034130040d10050224001002060045221004081c2500704c021044900c0d00c01c4140200f11250000d4000010030354070f0303001c65940e695240c06510702030b094205040b8907182e0618005104410000381307042e507081c840100b5107581c0d000c2c410a1141e03588080240da035603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 360424298 1250 360423048 360423121
    0x7120b13060905060a0506120615190f0f0501050412060f020c1c1d03070512071a0904050c1c0509071208030a05011212050d0b0a060e180c040509 64
    0x4504c0e0490310101e01d14640400241d59280c40902c0e6a214081c40300500995124000c003200503084402d0380f140c020118210315120300e82103019150003000c91985070709045050030340c422081c010076400103040000c00e21042c051107050072100c407400381e0b00801c0022406401603644000c0e015030104c906040c080c04c0038841441c18900b032842c00c6004076030b0307902280007900030000f00d00c60010301207580c01d0352003810240001d00b0300003041072a40a12200702e61159598240c00107250010201d03003450b160000c1440c035010705003401425000f402c2100c0c0241484940408144008801250810302c1134a41020400c107810a01240018207180c1d04082044c90300c5003007803100c0d5401507883d40c030302034646000080e55441c20080400e907180d111003c65001c10000c42e04688070b812240101041c169074440c28803c2c0c0d690941050010900e9440b45c40c0d0090310141000b905510100d10190008000420082d0070040f582c01c0341c007540d2044808401580b1442100c022580703204020b8440f104d94003209108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 360425548 1250 360424298 360424303
    0x15050709150e01080604060b1e16031e0203190e040e030d06030b010504020f0714070506042409030c050d080912060f0108160608090f0d0e03070807120b13060905 71
    0x2c0e20902a02e0b2030845844d003900380b1081764080d208412540c81e00b0b020740c403500d00f01c6281900240136440807460070f20650140191111503d00c2045020030710160390341c3e0350303d04441602142c1000c0c0e800a035092560f0302010806001c135542c4207004202820200322003940c0c4aa2100c4110090a0101c0e51141c20080748840181418001503896007900300000075540b07858004c0f02c091600c5450203030b0500b80ca40c1c0c0d90301d03100189101c600000740550300000c509a21101c01400003403408480c0708a0b40302d09c5447c401100c0c08080f903038604000e240036060000c41d5104204c0780c00c80e101900c001400301101c4c117000d1060301646226039408000000406440c40c0c000803420701849001d0800d240d96640c40c070300301d076945600140e44030104002c0701c42080454025007074145d01081d05001d5481b10b440c0360704601e041908050303004000c81c0c0520002400c50404001860140c4040e1006080c62420b01c1c01d1000c1c250000c801c0140018184000241b0040484500315034440e403280d8140211481071a0498 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 360426798 1250 360425548 360425567
    0x821011403070803041406210c091003050411013902010e0307030f150b120a03030507020a0305030a1d10090b28110c10050405060606071505070915 65
    0x10710900c00c900c00032a401d44003000321000c4420858000107001e074500d05122860700200101c00c0300610b00051413010b0141031010740e101e4003038400c5007641d610300e40342048880c00d1440c403890b00b098581410003000506544000d01d031040b003401c1c480417410282f04011590002c00003480322800c5601e00c04a08400c8103040652110300c00d884006100025600380355462010f44401b414020310840d9450201d090a12949c4000c48141804a000b61440b07020604100a0443c9014241e000d11251002e165051041541200d100e101030020300015032801401800058003042c1d0b0b46039904441581c200c0c941450030007030600c40b02507412901c20035445100401e520901a03985aa2032000a14010b011070031881001c1f50146d1700c07131501e00441440400401d12403d9045080004016064502d0802c100c100329a0045c50404280b600d024074200c1d0910700003400e200d00454040c441500094441111100281070b10280010741d90759080c821592415103a21200320144280e0801b80900d91001055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 360428048 1250 360426798 360426839
    0x801150503011b122a200106060e01030f0615171501050703081b0f040501170403020a020d05150a050603190305030a0c030204030210080702060c030f04082101 70
    0x700000042c0160755010740380000100703000581070750402c1107130b00c006901c9840c0d2451004580040880845240c200d4459102c1d03504003c204400d820b00308005580d09003003e04100340000f80704a524015000d800620071194440c145911807425001d40d04040d480f40c00108a0401d8030046001000300103090340104d03000d191010300018001070118a01000098041001a980c0a1410000741c504070f50f0000050030081d0400e0154070304000c1d840012001d000f02c0d40825a18603030b00e906c7c050014041c0c000800640c002d4041080400c00417a402050501189806460f010649044c51030000c0c1461180790500c41c6154258045c0044141207500c05880303020150200c4200c4010303c2e018109101d4104001030000390100005606030860343c0203070480307010500f405403d254813580000c607002205000c83c0d0000c0c0b120b2080180d40c43d410014207400006a540f03503407031400c0a00c078240158100401c05005083d00141e00d000c44501503e94a413240762080302404107507110f41000c0c140003006400c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 360429298 1250 360428048 360428051
    0x521120f0f0414010e0607020c0a0f05150a05070b0403020c010e0102030702090c0d0905011e05070503040c060302090f030a050c030705062503020c060309030307031b08071206080115050301 83
    0x11001242564a5401940da030300e071400d40ca80d5141d82d00d840c800e03400c07402052203540700c0d0440611200304000c2e072802100c0c0c1e90083c16400c00312005004001c0c0d19607000c111050100002000300340c0711103409003141100101c0c01c2c0d6070b40308521810398945c418000c0080c500e2544001300403d2550100f80710751103e100b6a2260261203d400049940e0302411f00b01950200d030082c045140f154120000b8a0800c0c01e4902c00b00d454201a254a8215101184008060941300c204d5030100308440c46002d42c80b807841c0c04c20909505142d1591a400c000a004410915500084e00c0d21a42e4810303400c10412900101190b980707540501c0e00603154000b9039102c600920a0b8503000c680da2400c0302c240c03034103866810a441c1d901c103460484c10150743d0700d03540c00780c05500810742c80d40c0a5465000095216045a200455590a20480c01001c0342c4041500d0b07070302036038071542003103c1d02c0d480200c2070340100312031a25014a04550300444003d000d140d000441d03562918400e0b82150703e109000100f1104202c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 360430548 1250 360429298 360429301
    0xb04080c0d09030b060108070917011a0907140f0403080d0207020f03030a020c1c050a0803070909060b0306061809090d03050603032b0f0203070c11041406010309052112 74
    0x10b4580500b6400000e128003031a000041065200b0007c083c0d00c202c4034a41144102e940c1c1e0f1210f80e04000e02c07a001400c0d83d4451071404e0799039001540c180a032400035100840c8030703c0c080c07000501c1d025910404000c43c000015294550b007440d0426540550380200e6401e030758000c0184810020f51003204128041e0100f80181c2500d4a004000d8458042050f0080e10360f2030030380010080c000c0007030902c1001203440c032000c81c4c0116108201d441012441038800b0781d41e80c148540041c1c080c91250780100000c1d400c1100174041c01490b042502c0e04090140c0340d9070717103132505804890600400962901c1c0c1042512080088000001a00b190041e1654800300000c0e1540001c3c5500e03481020703081103015150080000641385060026000c0000c03405001582071609100c400c103a80c0300707036076080009181109034000e00a48500e400003244c0115800c001c180c0c4418a82610381c0f20041c0700f281419035401c514001d020003441399401e0050310b4501561118070204100d000c5400001810300b12561400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 360431654 1106 360430548 360430573
    0x6121d01090c060206010e130b09030c0109050619020c1207051507020a0b2a091c0c062007091a031e06102304090b04080c 54
    0x1200c0d602541e160240017807510f04103070070002800300350806001402080003030030a07005500105001a0356541c4600600314010369402c800a5400c10b100388040200200d4254421103000f5100d04120484071038200890140000c000352a80c0207510000c0c55602c01ca003d800d101d84200201d80301d031140782c5807140e0000010b61703640000d03901a88008040206011a6992040d00e00e2a40031020540719015010001040c41580c0020360014040381161144441d00e035400002500100301810700340b41c81d80d5400c2039441003c0c00903501c400342a106a03840d50901980240020007040e040741070400c4e001c0103100038410360302048800c403420081c0e51000c0c8030603030080701000c00c408010b0910760012800d00718028000083d01032525424440380450b5140d110540c00d0822484800c007540d800483d0042110010192041510304100003c0003804401010898401c00c05d03210403c20b00b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 360251798 360431654 := by
  have h0 := BRFrame.cov_init 360251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 360251798 ≤ n) (h2 : n < 360431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
