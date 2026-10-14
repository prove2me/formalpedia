-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3696
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:24:38.347398+00:00
-- url     : https://prove2.me/submissions/13fbcb5b-68eb-4ce7-a5a4-474581864240

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 664568345 ≤ n < 664748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 664569595 1250 664568345 664568347
    0xf1002030906281107180b06030f070e04270c0e10060201060b0405090106110f0d18140d03050307092112030c051803010603021201090c0b0a020d0c0f050d0203 70
    0x51840f03604890075500200e5003400048041e111103414002a01e0040350010040071001000880e011b10103807030b40040440e00301d04040113000068080d01041481502140e07030b202b4405030410104001d80d00d2800281c011071031001141c804d0528440e910380d410900480b103030522280c1d2030301502c0c0d08980881d0350022040800c0000d122295080c01001d000b8403c0c103804901302410840001c0c40c0c0d070010320580301801071140c0d41580411060000030040800c90064034010300f181d9001910907005148030fa054807441c02c501180e01010a034000c0f0300002d02401c217500481091350103490302c0e032000d040d100c00e01644000014030030795280031014401d9110454035079200c0782072400d208a110111098400d00d810301c0b50205500d60300006550b001c03940c1c0d0b241d111110980702d010900410840c0c00c007a4100381031076881803101c54150042c8034a28814500b0043c2165030305450500e0340100c120080058200c00320a4607002d104003418820316008588a0342c11f0200355171030fa4078100903a1030000150300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 664570845 1250 664569595 664569637
    0x50423340c15061e142806020606010e061c05060a120f0b181f200c0d170402040b0a12030905010e010c08030a02160f0803040b060409020f1002030906 66
    0x1622070413100d0ba400c0c0608803561140c10300024420618602c100140640102032018105000701d01074265a814003610b0804240c3c0c42e110001c0d00c1e064200c8a01d404104136604030102070030448200e5452030020151070b440c0c4050070780400b015040107800c281e400307059404080341048138003118010007403041c0c2100e0908140c5d8980210f2248008004c00302000c1e500d15402403140f0b01051400f06610304014401005200c5640d510050a8050300064001102d5009001a46026009080420841341251112490007000321181d0b10707000d15907000c5903019004200141429040b1300c1c07105000902148025032508040d44204000c2841580068580c03581081a03582105440005d40b0003882c108850404980345c4640c1c601c0f002d41255a8240d0010b031620800d00d00c3c0c802c088a00c1e030b1002c00b0a20303600241c02c10030802d8005a4085c0e03501d80b140da0106000c0e19062082c0740c1c0e451750103020216545103030340400c0200742010003c1e6080d80010440501280e480200904a074802045044501a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 664572095 1250 664570845 664570859
    0xd0302030420030604060509010f1802040e070b1b0a0b041a0603010605030a0b0a06080a03020607080a200a031401170705040e0a021504050423340c1506 67
    0x181101500824200c1c100074015030341c40129010354050b1b04040c02007002e4854107031a50040c95200c03080480711303240c00a03508a06140301045c8040b44d000302c0e01400a03901e005180c40e26104a44038100001130100807a08450501580b20401c50507450b0583d051400700c1c1e20b032641d0607001110200c13071100c404621580c445261520322500700001b070300200700b82c606060200c0e96500400d10042e160600c4480080d844002036040b600103040c82c90260f0b14066820f2501a6642006035101d0000c1103a01001480580452084061107695100c0814000024400f00c0f45241c1c8030729600300030541c4075001008130f60b0481078268020108241c0604098041008e110704010143c3c01282c0314030b0800d540c854440300c00103201500d981d01195003d290140d4154120b080d4810ba6200d182c20074200040d07100c0c034009203a080c40c1c1c1440c2c0703802c0040f07030f0740e03036010300ca860030443c00465224420955100b444031014081a45400340c0041c1008805128a501c030381000c4d4000d0014031101c9900c500c0103100721 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 664573345 1250 664572095 664572113
    0x30106120c0c05070902070c09020a0525320f0f010e030717030c070f0308010609080d0f031e110414151204020d0605090c0a0b04060e040b010201020403050d03020304 73
    0x320340c40e00d2100b05010b607850544542c0648a5054000d8001c10700e90203102141c40303054000d0083c40e01c01c40d5190700c1590702a003550007401694041805042060701c4d01680000d503070f038801350701085440340c0b503d500c580d01c2110303841c00c1c00741d07520740701e140d00050542101001030004603c1f60000401c0e45600f458095401d5480305010280a90801c0c800080082e1500360320264454106600702d4076a56002411290307400b465402a01c1c1c040c44054100c203050308074503960705890160355242c40903911060344580d2242c0d0004403400250400b42c508901510070392000c00d5a820a030304084000480e013600b07009070758480000600842001408000a1041c04842e0760b10358401e40b0107941c42008550200e01d20b01440c20740040c2025510009402c41d9224040c0641070740e4041d8041210f402c2400015130303518080b207204d0340039199017180483c3c00281301c0f080e14200c56450b940c81107500c0d0441c00380310243c0b8104403c0750541d9000d010110001348207001c140301c60281e60740c0060700e9103002c0c10603600c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 664574595 1250 664573345 664573361
    0x30a0f14160e0109030f241401050a0b03180c03150901060608070c080304051f0509120316140d1d0c01030204030c0e0619060e010e1e011803060203010612 68
    0xa0000d02c0c5005841079801006a80c100c80e0030030382482d80030099007030001120b4a4400001c0144140b1030307030200c0c4003060380c0c0510000c480310a4111400d030b0305d40c418021100058041c2d82c100300c4013440060198840c45400b660313030030444019a0512500200803900d80011085450300c442a50010800400b800f442248000e0485180a6506040424025000c54200d0b007014284820020020b800d0290400c04002c2c08024540c240441405124040008007020754405020340610340c00d2410102c0340c282524054503000640030001c08400304181c6d481c840315900740d00c0400342484482840d444a105070252202076200d5030f00900c0325406600d00f080455030101d03062500c180b106101141c04a040031054400c0380307054120035240c800c00a10303c1d01891b01c0d00034081c1c1e00c01d400801c500794041100a12040c0030380307852450010032000c02c0184130b401d04040d240d0345904060480b0662041100201802046c3ca080741c00c1a2691100c106030381c0240c0100001c01c2a11200000745642ca106180f6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 664575845 1250 664574595 664574597
    0x306040902120a0b0915070c050f070914060102010506130903020718090b180607050309032701091406070602030408160516060503070f0e01050f030a140907060e06030a0f1416 77
    0xb41ba1a1030340302203050381d040a461a0104a610080c5400b04007081003124000600c000441d800079030b83d280480003500d0200e4228005805070408901954014002c803801050b004200410052804070243d00810240c50203400310712a1040c001104e0100ca000da80e05203c5044001c113002c400c600382081c40c4040500082e03101404007000c1d240581c40454003075000b16091a10590b030b61101009035256000341990006806d0041d508001103200022074024500403e88800386c640b655010742c071700b020400054050704403504000c81400662541d004561081c80341000d542042618a403d05040c2da255100701d40940c03140b1000c00420b40031081c6480144218a020351440c5000304005051a1052450030700784444c1c1200071039180c0c003170b50696080280c0b5041c21500d9190000d03000024041001e140302d10009104080b4283c043c0c045140d1040e00c80c980c6550600c03c01c003606001d09584020618491156203021060310080300d13010f10702a0090480c4681070741c0c2891b290032981b940358665520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 664577095 1250 664575845 664575853
    0x3060b09061c08130b030a050f010603020a020c1020011e02030c160507121a06060c1504021f0302030403030b0f220905030c06100515030a020306040902120a0b09 71
    0x540c004181d07a04507441d40080c03c10f4842452610080802c41d20f6005545850b40200400c801c0c00d41c540e00080c89244184a140e20a0f642c0b418154102c0c880c1c0c11485005801104205c10030307042c1204200e20302c803101c1c9003900203a170101c0c0141c4d408601e00c034007094286c0d44900700101c0c0b8942c45880c000048900c1d040461560400106011841c420003140a0003003030158032010a114086c01142e004101660140e094051f2604c0d000b8014034080e0580d442c1d110494020441c0c42c10103205566003551507500600601186108600041c00003c000702e80c846800440c040707003004000c0e501c02070401c20303132000750722803c107441d019054034444a0180c0c0625225444804250f841ca4a07142d191640202d10402010602c0000c1e0040c0c10f1642c4080e0541c440001c921542c2c02000460b207100d0a415031515088584035010002c803480000740c0303400611420306c04940134044a90003190003082c0207000050540055020443c5e210803a030a202d9140c014081040c144403000407500d50040d0000e010b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 664578345 1250 664577095 664577119
    0x30b0105031513060806070207170319080a11070b191104050609010c080a090608090a050309090c070213020301090f140703090c0e041104061502060703150306020403060b0906 77
    0x11503007502c2e040a05601c1140d14010440304905039a000d5009884090f080d56207038941048060356402582c07084402c814200e036112032844801006581920070080b518018162500d0800c4601e15005800405240c0d5943e20301c4403007200e003030001c0002902c1070410300424039054506071100028181d040066504050408154040f80300c11281075500803209603841d0040d403801250150309603d801814020009240c0d1041d41d0000700c2481110309903600c085299940852068407040c0e402401020b50b40140544250b038508080350551090b40050081d0904800e40c00192401c04a2120215410381c004014803c40380a4021005070114400083c0305946a40d503030401820380c020898000c0590707a61015040108090306080140607002401c2082d0070b1a06045402c0817450590740d00c600d140240010301c05031450b44040002501c2d4002d0100c0380e5644900307401400d00b10400d0345000b0141040800010b421f4405080614003408001a0b07503040c60062000c07001010b8241ca11078400500700d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 664579595 1250 664578345 664578361
    0x3181805130f02100306120f110105070507091a1008010f06030e100902040216080406120612030c08130602031306080115050f0f0403150f18060203090f0616030b010503 74
    0x42d2030340e8680d040d5030301440106241d00032002411242c00004114444800c42814400c1190740c101015001d46500924840c40900546040c4551400200143c03c00403040206100315800b445500c1c0e01c0c0d81d00c07040410348110005407030342c8030705002e42d01103061000140700c81c924005144d0043d03d0700d170030304002680c40c00d459281d030f40519101c85400e0310740310a003800854460b5015251002401131805a003070f010744c84c00e1031003500140150400204804202440e04005c1e001c3c83d4101ca44151904a44041544080b26211007100017910300319010081074101000ba8001500100000d41c0590b03143d102c040d0354264915940d40c0981d003040b01100c0184520200400300a110820702e0401c80d40d28400036100390031900480240007003290700490000107000c4c08000140310000401410810320300414080400c07200800414589a01c0c0d003c0e02e500010780e55801941c20070800e1045505a1070740a145618100040702d13030300000c0802d42c0d402110355030540140c200d44402400c015041d8900015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 664580845 1250 664579595 664579613
    0x602090a0504051305010b0f24070501230a1107140f06241009061d030a060c03150308030105012703050f0d0f0203070807020402130b0c150402060a08040318180513 72
    0x2c09e03140402d442206440c03203840d5003c03540c0e920703032000c028007054001c070801840325405140c1e44d9401d83e040000140300d01e865481101c0601d40004ca645042041584502e0703814180c0485c00e9465224003001d1b4103103403600f005828860300352100d03500340035440c8401c110002a50101081e008040425050500d140c000c500a0180c4a540c60300c519054206544d07540081e8060500c243c0500580c1c2d0b95805002d11a0000718054449440c01d1001c40004617001a050700700744806400e41e1010f10050100703600c10199041071400031a840b400702d01d01b004500c600e0f108140d10403541540619542500310100303001650480d201c50800c05101e100007031010792207115148008110f05800a010011503946605440f00d461282500c1d1034070742c3e201c0c0c1c1d084500e680520010840c0b0311401b11810702d154510b600c00d520480e8007824450401c20144000d07200740038050011018003928100304140c0341c1000d02c0c25002130180700d4840c0d40b92401e840ca08030460354050408209088404800004116041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 664582095 1250 664580845 664580869
    0x1110403030c0f08130501030c1d010305100902030f04023c06280e03010b130b0406051008041a0106050304240606021e030301120602090a0504051305010b0f 69
    0x2040142c8a111140703400b80440510341c070003e00c0b0fa0400f00d41d00480341480c0482c9402d4540a8800b0410000d400d1410742c0c0c6a071240e2440c1c952101080032507a040c3d44a07400803034000f2420110b800345141c5400c42002a40c100b21400d00041829008110035454404000c00314082003061107000040c10040100f0501100c005864100c0030300041c00006031202c4080300c07900c1d841000b2400c481540d403440700d46200c0d55181c9600020302e521a00d5a810f184c1031090380d2882100410003181c124414803268044c10034409003a0307004d55140c1c0c0008107502d4540c04203800505a0381d80340407914251519204601440c42290a40b0f551a4014011160400c086980240d04019100030714415169900e040c822001c002c09031070b900304a00017030020b0700091700c2034005040ca036015410440c8070768115560f0000341302e54030300d90b203000e034002000c1552503006140b1380c440a8840b001050315000418281c1e06c00b511004450801d080c501001c5c00402c0c4252440b850b0100e0f590075034120110009400d0311280 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 664583345 1250 664582095 664582097
    0x30608060109180210021501061e03110f0412210503131b0b040306060b0a0c1202030f030708040506060904050d030c031b0507050f060702100207020102151501030b030111040303 78
    0x3c5000d82981c412001e00440942c1e4000c0c035801755065a000c00a4903032403132100c1034480600510010030424068400f0108c41002444c5200b4100002e0404601802c007840c2940c82d85102040302000034032080c001040034051895064112941c035142414004e18507800d081e9132041624040b44031183d100048a030410041000250ba0028900b0105454003c05821400482e4042400201c1c101101c01500840b1b000e04010024507903540340261540c03160484100000e035a40150b40c000400d540d0b18082d42032400d00c1124100342d604c0d1100c00055209441c0c000100d03641740f080200b0064200310540e882001560070440504003987c1d29940e503092145010300b410303201c043c5405c456119034020a040c81c00307820010b0010200c1c0304050041d601401003942c05006000038240d40b41000180c440c01540e0a9008080003109035910800070740040034128110700030110014440d07450058480d00918080e4640d68941514500140407507520003804d9020780d05110012106036240c40c281c030220703601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 664584595 1250 664583345 664583351
    0xa061e0f03030c3e01110c010810090c030b0f010c020a0501110109021e09011a040e1b070501060e09070302210a1202060604050c04240e0a0608040210030608060109 72
    0xc0e150403104c6800b500e1010601071a11a0000031880341c60850001000010510304401030981e001100e01ca2440414494141d109a00c1100607503c6040da85a0042113001401252a10781c5a500d069444280090b070001e910350b60a08150300d030407405640c4d0b1820034200300b11216660790106000c0c0e542d41c810b1300d060050f15103070034180010031b40004004507070080504440d01200c160080248014050b41402085c40c403001144002c03810b13200c0d030a9940d05800c003d080c1460b00c09002c0c0e00200007000c078100f042048210402110318840075121940c820000131604d1820151054038010000f44801d481d903200e030700c1c00c20258561950200324440125104031880c4000d010040c60221160401002e20110540a44aa07503002c01c0c001d0103404121800e00030794030398010640c2c050040e0301a945042c0440c016034002ca41c0c0d4509529412484c1d420444100110200007030910340d4070790302240100300c1c00c1042000714a48030381c3c0012101301c0c50a0401c441810080802d507100b10500604250980d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 664585845 1250 664584595 664584617
    0x807080601090b040816050303030f0a090f0f0305120c160206092803110105030103151802060301290412020d030201061809060b010212090d02010e03060a061e0f0303 73
    0x40300d1103080300036191820f8a0780d070721030f0b0340c18074076030750340c1e0740d40059180410076540c0410185004801c0368000c252082c005401901e030304001800519400b02e0444142e02c0c01c03030240000070040700b20117005074081c0e00c6450316850710f0030800741c440b14001d201002415003001221206080003800f0910240c060f100e6a485800140104034151072000f52695000a8004c0803401134070504090000c0d01d2003000c03811004c01c2c2400c01501c1c540401e000003012515001ca1080318003410340c0c091006104280c2401d44000030300d4011035019802a0007000140708905103e900100800540741301c0c00b03540e90111b91415281a034004031805010400038410040310030380c2001e1600c01d4000b18040c100034454061007240700045a0010960035504035001814014100030540c00440c0645d03600c401c103e8003074505070f00401040342d13008106204906000c141c22104546880400c1300503c07448130b103200090032034140701c1100054031450341c022a400300124424411440074036071100032294036040c440e0740c40c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 664587095 1250 664585845 664585847
    0x121e0c03050f01030201320c03031b0a0e1c06050f090d0e030a0b090709050108011b0813060f09060f0c03061a07061e020705011a1c082a0106080606100807080601 71
    0x41c0c7c0b600454054901082420302d24001100a600890f038500d2415001d01d82a038604040d40a500c0c1c40d0804901c00780b01203041c6041c8200e0711428240d503100c10091506c0c241c0d440c0e0086540c180c03194a0109030000400040c01010841001981c1c228100840d441310b00c0c000080d03440303940340e40040c09486650301040c0c00541c1001244003822a074003081c800c03903031aa0310132802490302c41204100c4201480c1e000054078001c003400c40c00b4000240d25080900358588401024055103401c4009041d0b440000d03901082e0030740710702003c1114540000c01d41c040414401001c1d1045a04030030b01c801203500034401e031003e640046520300b276802040401d00d444032a8800e850314803804c810307018030740c00040c4210402c4010351000b601c204901d066604000246400e001c0d03100516031003100052100c1c2060000300703500c880507160641d801c00507042c0140410000c01d80c0024400440d0364169103c200070300240307505005843d800f21041d10040c500c809940001400203102500c05000e10041c90003141c050f03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 664588345 1250 664587095 664587167
    0x301050d1a0702061e0606031305070f0b03060307050a0608150a030f05030a0215070e0f04090602070813091a101e020f01150b030403121e0c03050f01030201 69
    0x4140741c01c0760400c00d440d010001030740314542114091090342c1d1554581c600c0d240c240d09064082e14025160a0840d61100964250341c03244030002d0711745200e0070500140710981e8803586809003811310702c620b8490411b1003c3c180307000782d0b0341c00c11031003420902001d0040c3d41c2d1040115600002e8459040c50a21030500070581e00c80d01508058460a0341d03c40c8034043c000000000e100c511456403c6034480130640c0041901c803841510443c2c0001c1200e071100016140003e0021011140240000707040d031620380d211001c82e0f211007422211904086142e0742c4030900c241020000782804482030014a0321090215070500501004c248510391810000881c01c0c0310b0801001e20f040e07010029218000542c1c00a955a4100b01380211198240130304201c0500c0050900e60881e1200d00740ca0f400c6854039074007030b0327044540305190101140c0e0300d031b5200c0006000400000e03000303d403014000503070300040321000b800e90744020120700d820400c41c401007005176808420504800c5848041d21108d0841129056039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 664589595 1250 664588345 664588373
    0xd08031b0403080c0d020c0102060c070606121a070201020f0301030b0c09030105150a170a0828090303080c13030314070f0b0f130309050f1507110406050301060b0301050d 75
    0x12900c085404410060028028030810030b480302200c5614481420490741d03a000074403220300580200005c209a01b40079400b41090300c3c13084601060140e11480b40c0661005500b0054903080511501c0e10603181034080c0282d0428828030080d0f1914884070760b0030821340b00c1031200411004040c03000a849424400540b52095002402407000e03080610303504011800305c942061041d842104005901d644010848880140c1100541781004803516a040d00390044172420341030b01d05001401205581080300e2111102450301c40c1c03800c1600f5030800404000c4010b01c94071042c142040140c4030600242403810840c1d91510b010608000340c244180c0b07050089075030082c000300a0060076810041d502032003a1249442e45921103050b80e4010f00450403405c58107015003c1400e04505002606000030035095018004d841d002c640b200f46200e0030040d500600042e00d140c0300e40c0428245610b03040c0590002031074110000d00015050016002080c0b0040c400d1900c1015885d101d182088500021804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 664590845 1250 664589595 664589641
    0x70807030903080a08062110180203061006020d09180f0204050616060b010e090a050709050a032301020408070501052d07120801260a05011d1005060d0803 68
    0x3841c3d00082c500a443c2000550b0418404c10050b000a4015405140340b03003084c4008900130400f0a40606030388c0f004107001c0940c45a4a90304607402c3c00941c0b020411a406140c105818403c4145462002410314090400e00c0c010014075035400c0208514030400a403501403090400561410a240040c000340700f65408103800101c08240320405071003100417400e03200e000d20002e010348106480110f41003603406203040d511051380d41c003043d1251090340c000e5500107410b0905004040e240c9001904c0003c00b54000c49210060044030a51001c00740003490030148120020742c240b07810010a82d03107407036403030050318104480454108008200321b800200c0c0071900501050200301c07025503804071940404010b554034103a0540700b0303131441d1207080b081b4100c0c0d9030550000c00204140391035a100000001341000d440c0720b0104808045602807199628030108411418008100d034a00c00b0308200070140d00b4000702e8600b000b086070301c0e29034440e14030750258003005256482d540c0540b030751510103141e11040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 664592095 1250 664590845 664590847
    0x3021e0a12020111030406050f0c0c0d0f0201020f060106050a11010b040c0519052b0905070e10060215070305091e07030209010e060f060c030405121c080c07080703090308 75
    0x28510206a034a0705146000380d88a076103c0451020031a0f9a10452240c00000340302040508110440000501482d0317004005584030391074400d00041515961020945510f0744c5407810808540e01000303103c40b01d4161001400301513141400181040c000c00840354103100741c803141c81d88141029800013170401c1c0001c1080000c000540d200170300d503030070207680600c0030f1846d243c10255035801801138410100c04990401040c02c3d99614565101d0112989100840c0c0c40d00040c0300040d5080c4036071005006000080e03441881c185500320740b6004164403207810341d000194661441403400110350b07842184d42c10046030540782c6031919840c000c1c1564410070a01303545a004d1058600100d6100100e07802160340003801d03600d0320741b4440700d40303000d840581e480008030010b0b8400381803040140982105c3c40303060f42d003010b68800218849181e06071004016810041e150044210b506002c5950710029140441c160315140e1100d2403944102c60026120520204007441010300c04c1c0040400385602001031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 664593345 1250 664592095 664592099
    0x117040b1509100303030b0d0507060e01120504050d0818100b0a05030f01150b0c0c01182105060f0601090e27010b041b230c0a0807050708010b060403021e0a 69
    0x2485100740d4041100087c1c00c1c103901240314500000e44980060f000809014040d240c03004c10341d0780800b090303852814044055130f10303040400f0302e12941e841a40607001610726611001402040004010561036031b0b10500e00018081200004101c0c508000d25500080d1f5102054002809416550b1200303515100c3d0345002d40070090103411441411514481c2c80c0c45031506e520412843e07002d332214803030307140c0d00c140e003992184c2d0b12810007840c0150560041c1c42072aa100d0914440311100c41c0c00c40c2c0140800c0c0d1100c80d00700320f0200072403980101a044408400e0138020002020301c0690b00c90382d81080b440d00d0120701d146955108842c01c00c010b52602648684c820700c50107018111040405100da40742c1440841c0f00000c6101031080320030b00d42c0c1ca910007000302c05400c0100f10280202155601c1b81440780d1a040c043c00c220412540d4003c00420f074944440d40340040c505045c1c1d03008019981d041c60400542515200240c0c1e058950480e012a42c003502803800c0c10340720007c1c07410503a02c81c21720040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 664594595 1250 664593345 664593361
    0x907090e072c070e01091502011406060301080601230a060309030e040606080112140105090303060a123305040b0601031401120f02060f13140117040b1509 68
    0x4260440c0c41c1c0800388081400d4890614110440c001010b400711003241e00040c049621503800036071682e10504150308165210040b10004644004a20780581c3d0b540c0c88400c03d100701001400d5000b801228030a203550705100c800798071011b040c440e503101031111800c1c1140c03849060081b4203582034040e020070315042d903d202c010003600d202601a40400c0490310031400d45d05203801080103030b070755a88134a06140d10300020340c202c901500c03030181d440d810120300460000070207000c3e1310b0050f1501c00065840e41080c404004000300d0729404940c489507424140c0c40051443c0300d141508069000c0c1024a104d00a030742803425070b006200c0802101e1814007000704108501d05c09500514007aa410094940d45400c2103040043c01c0c002c42c101584098039020014000401000c40544060702103410459695920b182c682c1261651800301030801c0400d1003041c4c0710661541601e14240303000f480c080319103074070220381c250042c20180101325440b001a1200072800e003c1021100e0151800c50140b03801a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 664595845 1250 664594595 664594603
    0x2060c0a0f050703031202070b04110f030102040e070329010305181009050c0402270d170705010f06030b0604111b030315030115120c050402070602070510020301060e06030907090e 79
    0x400c601140b07000b0101b61062210b4820344001a90000030351285e510b030b07501c59105804120105c41d6100744490b1200b0910f44003800500002d00c1c0b80a01d0240a040c0b4950180c00c0d180c0d104441110210309100340c04508100138a00ca228072401c2c24001019201d00040c4642c00890344504c030f60314851044404224112980711f00fa5050080c0d040d0f856804c2034008202c20381c86605000d803103c3e0014285900d800340003511001445d10000e2042c0042550b55840c1108440c03203a0403101541e001040c0a414070600b80200507d85200780800c2200d6811540d90750b12011010781110300581c2d0700c4a01c903a242c0720310b6040b84c1c4070912851090102e01c80801200b5035035401258440403502d030b00203c80c82d0605050207803c614002100308422421700b00070710100c0d00e1503080300075901c0c40d5551000080a44a07440103100b45802100f01503911810f90518516212102e03000c65481c61042004002c40c0b9804445624400000c0781c05940e00d4484481681c0340680940148007150f207000441c11101c50001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 664597095 1250 664595845 664595849
    0x5030313091509060e090106242610031712070c1a090c1e03060c03070306120b160f0e010c0807050d08090d080c0a05211f0803090d02060c0a0f0507 65
    0x80c0800749d04c86d11196524504100c1c24030148581012074004035006100785184d09207040a0348001c0c80100f05941984081030350f4450013480969410300c1405000592564140e1304074401d5890401c65020a090100b4024016020001c00c2484001000060703582c0c0304081c0020001c80f565030825071882511a0125100c45100c2d14000e0107854141402d003031a21548c0f6402005070505030340d0107035158503e0b44002d2021703040554030140441c40c0b500e0f10924055090043c1070200251800d50007064200e0515203009040c810302c03c00300700030b4a52015003085034140a29120f01d06500c5071900c0704440c019031000134850f0050540c032010196020b10580d10401500302101c0700310000d4103040d80e42d07501c182c03070034070100908020600c4502d000e0030040c0340400c0300383d802c88484050004d2501c5140010784100c0102400410808880130851041c10043c140c414042c6241c81191000a103084c080c10000034080d800101c0d0a0010701011b20103213901c50340040e00364400700b50300d1508544980c518 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 664598345 1250 664597095 664597111
    0x2010e0706180608070c12080106031406031209010309140303042d08033102040c0f05090d060b060a09051804020d0611270a05030313091509060e 64
    0x28000010308030311803865003032000040941c40e15040e09080080320200d00045c0000107010320800b64000150b01040c44182c401910341d5070000d254140b140c000c064410840c034000441d844d49017444410303034001c81da8034182c44190142541e1410720b0320050b4042e200b8100050001d01589044614048001c4000c40c070580c418028840303255420180100c034002040c80f101d074058040c401f040e0006c1e5401c130046400c0b0300000001942d005400f00c00c2604401c40001483c4202c00c0c0d01452401c5051030b02541e24190303002d08140054002c400001421800348045552240c800000c04006005165000481c0904064036060742d5821809024080502a12401d070103811001c08400d80f450f41c1c2ca03001c6024542c01400303028410720302e40740c4d10701070442c503041c403003101c0800c1060b001040c112007000301c11a13800c6003c9040385200c003010450001240d07809540680c108014071060451003003d01002d56545040c0045c0090700040602c03054001a0008080c00385400800304010240003107140c880c84070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 664599595 1250 664598345 664598353
    0x9060b0a1d0727330507111f090e0606070204020d0e011410090507051b150709030212030c0303041b050603040b040b130321021c050103050d03051012020f09010602010e 74
    0x4000c0d00c00c0584c8401c01007885065041c2070045950910402c002d1480c14090050b600d412521500095402c000701c40003000043d012240d6450702ca6004103280006100c0000104640d1902c64013049483c400c1b508024131403940010000590280c80c1d2003990000094802040507602441780369054040503219000a150000c1001400120b41d0007494841c0712250780c0c20f41841320034101414001d507850200001c0303010f500011051000c88440440c4200060703642c0b08103a85c9140103110035890400d000742816001000000342c0000700100300c3c1d03041940b01700001400712400d841e803089044c2c1a04000c0c0c1c84180001840144404042c1c00b0f4000da01034051030361a600c41002c0305030701202d588070003804908c0c1000c803007900003000d040740c080f030000c000d40151800000d109400e8000422503401c0c540c0c20341d22f000500c18000b00f080043c11400080c2000c10103420080c1d03100c0079561051196225410090040383c0c01c544402d0f01584150b07002030003241855845510180c080d1644041e122100d2007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 664600845 1250 664599595 664599629
    0xe040c0303111902010c0639090509180a0f05030304030305011e0504020c012c070803040e0109091406130209090a03080408090406050a060309060b0a1d0727 69
    0x1801043c44490390341c201c0c01088100c003503a401500c6003803440d81c06031541c07a0359203960304070036200320600c04910603040178912a803a2484060321034424030889031810080a01e00c14481e03501c1d0107581c0c3d90800384000044d40e0041da164802e030319100d01c0f04e0009004840c441c011034204000000a5030160b4442e0310b05111507030b00c1d84030700c6004580188012600142c40c000412031420154002e00019242200104801c2030107100b40c03415201070308104180094012a040d64010140860000fa08405028500e021310340b40d208005040e040c0a41000f55aa690902c800c0144110612200070002d40070750701d01380380402e002244d07280c054409038018656a000581201004220907541c9549034865041548441d242e02140c0d4000c2009907400c16590500440c144d640c050010005100c2550040781c022082d03d401d00070766070b5068026008100c0c0400501c958071003464220341803080340358111401e945070b0310120340004c500060200c245600031141601406450501800d0720f06110404071707401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 664602095 1250 664600845 664600877
    0x10e2a030420031507020c031203010e01060f02030403031101200909010f0614130f031b0e04200a0f090204030201090b0c0616020a0506010b03010501030509010c050906130e040c0303 80
    0x1140b414034141d0540243d507030120f4080b4015505a040242e510454040f0409100468a00300d900140d4160588000c401041019110282940500511300d455030800702030100103552030065000090500c150b449820542600942c4100085510011a81405040c0588101d1264000d03194640240300c40b00000c15203a08085100c404ca1b42d055548044495080703500f80400d1b041268400925884200c000841104844082d4043e5015070707011464014521100b85d41c1234060f80c0303c1d583e040608402c02010401c0021150000600880c64002ca10100c0c0b0015400e6111900050100c00c0404008201c0108039805402030364400e8032074030007603511004107040704c0c0248125244a54044c03800982c541072015011002d2b04071a0040707035800c0d0416650307203003028400d0b0050400c0f0030340400104110341c0d01d8001c0c16040b00824008112500b907000c030092181c451110b41a0145200003030000c2040604608240107040d61111b0b2041800d0910709002d01010f10710007a0009130202c1702e44da01d42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 664603345 1250 664602095 664602143
    0x1061116080c01120f050c0a02190f06090812070f090b070b0117031606050f010e090703030509010c061a03010c0503092a090a0903020f03040806010e2a0304 69
    0x5079480c00024101c004480004490300c0309030034118260141c40d600000c0300c4114501405001d81d0181c005183c9510f240000249441170141680c40c85e0b818000311100842c000d85405082e29030031402c0031421a003a400e1640140c45030b60806d154603071600080000c59640300d100980100b40b035644581c180c3d990b866644040703008450010300841c50407030042180703500c0810b00442c20321031340003a241028012006404e407030380d05210a2b51910b48942c04c0100c00c440a8036980d02401c0400008541c905209000a42c2c03401240401014041d00294040c0c40b80c1c055070008214903031080d01441011440321a06200641c4404110301940c00c00d01520301140c015401e5031b10402d0f200005001c21150081000c013219800e0711428148070744000c01e44010348880d04c440e4440c13145044003080012541c038000340b80003c0560383c04410b03002030000b800701c914041850b83c1110080f100c3d422040d180e080e001e41c12030012003d0081000790cc442036031070408011000c0c42c41a409555600010b100c080c03880890 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 664604595 1250 664603345 664603349
    0x2010e0f0309100320090a060302121512190605090d0f0c02210a050d050313060e0709020c100e070f0e04030e1201090209150f060a140301061116 64
    0x380750410302507040d960600070300f0150040d20b1490086812a03410011100c038921015590320740010018081303105003009030340100281101d20b001c40c50070390804401c2e000c0800140c81841d003141d0340403401007555500151220203800420507503c0168001081034ac031a00c101c0000c4034820700303240010345c805802180a4025072215120301140100000b006c413100c2614403c06c0340d0040107100c1019402c00305944110380041014024440c100301800c182d45020941c0c0b101d5410490308108004441501d01e80c1d0125403a400b6001180c401501c200207414045140c005080162000c545031620840000d4564052842030070308121400541c010180c90700702c6400344001c4811130710020003410792800d054541c00380c06031410101e11040c00c4006400540411000d20f4969110fa5400e0194689040c0f80c5403c001c5417440c02407801615000b0508856034031015600c102000f044d6103840c0ca0148200c81d54105c0c490025990740e68440e50044d0522a4000802c08035124582030102526585c00030802 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 664605845 1250 664604595 664604623
    0x130203161b0506010501080a060902030c040303081014060a02031b1c05090a0b0d091b05040c0305090d1b1e03080a0e071814040c14030a1104230f0702010e 68
    0x51303800e010040da440740d800350131900210b40e00c01c0000348403c0140701543c058038500c0407507aa51407840c18010b01d07101000d89600b1028010002c00c00280500b9008210144002d482e000d13114005510141d0a60041201110449080d03070351040c03051202103101c881617402e814a0300a0b1040031071044076a40580c030384840d08810f0b1148244813056044025041240c1215000724850800341e0781c00c82012081540040682030031002030045d4a0b05000d0b182040d54107190402c140e281061985a44582e074240507000e2100304d42c080c400407440c240300c40e2400b68012500b00e140b41500715504800501084069002070445800304001c10581d004109483c41c02d68001c2c18501d04190584040089018000440ba680caa18a207040003070400058406c50091303405852503450100c501d00f1100e1441d00107031007600030110b6031000990040211403184d009031400030741c28400b0f02d003a204400c446800020303644100010030565540401651b4450102c90303000b03001c0e1017103141c40c0958511034850400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 664607095 1250 664605845 664605853
    0x7080f060a09020a03020d060905010b060a023c0705041404111513090b0f060403081c090807080a0314101406070c0602030403050d0203091c02130203161b05 69
    0x1442101c003604001080c50008084034800703903884c1d0010754440c00040d01141c581e5100e0703001109000c1c0070b21420030031910030389810340741490f1090000d40303c114000e400c46107007090361803c14030000101010310960348440c0c11182041560044140d86952a10466101b1420704102c0701040c0b900d102c00174003c55101a00d801e4184550007003204084640c014490b800d4018400040f00310038401da12401030031201c4002505444003000d0060100300702e05403e000c1c1200708020800101c1441c202e03041c6540c0c2407283c482100e030740e4080134054211814060f140303603408603281c003d108100d0300170844600261002c100c103000702a50700710700d64001c5a50011010700130754100300070010840e2410000100405441c40c2404ca5034400f40c44c01d88542081c2c005a02c00300301030080004c04c1000503100341c0180000c608000901c4000340c28150300d00d00742c41c0c401d41b4007401c030804c548840341c0d441441e00c3c64400c150f48902e03011403c01e030f00b083d483c01c18800140548400c400b641d010f5102d41170415810034050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 664608345 1250 664607095 664607101
    0x220f0501020d17040609061805060c0f07120c200112050c0904180b010801091b030b06041116050d1409090403080c130308041d10031b0e1807080f06 65
    0xd43c0030400000c205030341e4141c541d002000001c80c540b103284c1f440214000440098052030400ca4585800204000c0014104000001e00b0381a04010b8459030759016540140c80c4603030302e50407603038540440001408010b0700e00c251252008200a540c1c092502a03882c4441c011741e1801900076600292441c00fa075070410041d503001c905103a0040384400c21118600f0103d0005590ba08000701400d80c0444082d95482e1031040c20015680494070f40300500c3c02c109600141940c88a0400f102c001d043d203486180c6c0c44805030003e00c0d2510544000c0110b02d40c0402402c0018100301e501c4a46101da845c00080455120f549001d604500b5688000700190120905a43e260b5040c2c0d202c8401030160a2103480c140070038203296441000c0003020f035108026132900c8a2800e1803110038074640c040244031801805003000390602a8003003690481c2d8104031a9104110b01d80c0c5040d503641c020340c011854a40400c810491030b00700d600300c7c1d05919040101216034a03541c0d601002e44840010945558a40016000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 664609595 1250 664608345 664608377
    0x507030f181a0f0c030d05061f0f090e07080f011d01030605041a0106110606090906070e01030204080706030227060304030e150304050606040c08010524220f0501020d 73
    0x1d000c0e921070006111510304290000300100e19040b40c4d504145507071000440d10f0070005c460086c103401c890f0640d42401c0052064070114030785408800c0e04002c02180c2c40b0360310500780c854007400c03005007140c00284207141041c1c880100742010888100354040c0e048000094081da481c603410400e400c1d40c4508070a96404c642e2100054480500306940505500002560607412402540d0003030000380c4030407003c030300034007241030400b07000600e00b511070b02c0a1400c00c2080c0074040740c0c170342d4022894548211019400c00040e030090107944c111500b42e00c560349000c542680c150340180251500403c42080380354046000640840200d00c5081e00b02c90184003190029004540136598940010940014007821001074400b9420440c4c090310035901c410240000303410300d482841d0b48000b441c0341400096042c05c000c10125100c82101e41c401541c1007005095010f15042900d5000180c900d020080c0031440e141c012000b007290180900284061400040035800020407540d4407000d51140803000d10300900c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 664610845 1250 664609595 664609619
    0x1050a0f050306190821090a030201030b040e01060603061419150201060801020703050a030e0a02090705070609061a01021605010906110f0a060f060e041e0309080d0507030f18 77
    0x58116981c0f100d203501c031845603026003000d440d0540086c00d407212101c800c5400600c11212118100c0340c02c110643c46d40c0c0382c40c4c81c105c05032602800d000c1004440a4040f0f4000c00c3c0003854034040794030f041000318815a044d00700008444c5070040c4911039810460030032803542050440c04a0150300c3c86410000302c600c00c5003c2c0380e83c02c0385000004a01c0e0b0b841c8841402e9a10091041b000a4030010360300381711a030076110b00c00ba11203820000b010b902c00968042a401c0310050540000e12038045081401c001c00d94000d0500c642d404901400303440c8084c01c0a0310180d001d040054054080d24032801c245107580b1040104442c016502c00e04011b28000c0191074274000d0044c0b440d0a0b00518005c0868001c0410409151500c201c42c0000c149100d28044401c44100d600840d801141c3c5c0c00500c008941c0340d0041c1e549410501c01c9850050655203425201c40c0c0039070b8800e9401d8051240c1a5820580240103403410340d0003611a480c140361000c1088462202482006e018004040030500911805803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 664612095 1250 664610845 664610851
    0xe0309060405100c052b020f0c1509060c0a0b0708090606130f1e0e07060e060f0c071502071205031c02041a07020316180c0905040f0c080601050a0f0503 67
    0x201340003014465a4607103d0804018134001140b01c100384680c0e1120214200e043c950721403091010b05526a240b84845403198000c0b9002c503c0764400780018945c040d140c3c403c6400440e4000c0c10544d80b00c80e5004107a8a61443d045c0a948590382000000d4040340540c6900d44180080f40c082c01c80790391100104081a81600c01005500380e0b80c16801884255901c11642141d907505601d0804040ea05404010f942d0f01800d00e4480e6040340e070080114a0f000010104404000c070b6070541c50341d80700c101c48a1640500001d540f0709210340f44000480c00315600e0100c10b4540c86a003915060750725000311041c0b021038000c00525030303131082182c1e4060b14096500c1a10400341d0410151a156039100d0320102100e00c1d90812048400000b0041c0c11840d01b00324002e941c2c1800f9801c7e01d0140e00d40f009052175480c1c6c860220380c000c0d8039490003051142c443c20302600601401441045011805400d400060540c500b01e0000310748848080b42c0c1a41c090416141c2101155644502c004060325044440750005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 664613345 1250 664612095 664612097
    0x190f06022107031e0204150e030c09040305180301060b07020f0a08011a01080a050709030f1109010306021207090509130609051213061409100e21010e030906040510 72
    0x4000104166101d100074501a211541d070100c1c00e8120300c43e203c010100c1c0348481c0111213104000c104840d14070782c6022021a000343c107101e1100100070300400c2c10205140d501e0740c0c3c031507010410031017055008005803582190b080c2e01d144450703070300904bc142256090301550340c10507802d000c03600c0149080d4407224106240a0580d00845035240d807080d0940742c00c03810003d060314114030241e8080d41c0c0070282507404844124140960b06003144080e122410b42d000160600614240071801d000c0514150309a0a0001e00700d0700c4c4542e56403d00000a41000f0a03000542d4000e1020807840380c0f1400c010401d03510020300c0040765407200c460000900c5801c58044a60300d4482d41c20303e010440c10b001e00c00c0c030114520201c968894000d0b0b0511800c007000d8000605015001448540c0350030780710155a45a60151502035084034000c50903a2941c400782c04055000100511442650300312101c0c48001401c3e0a000340b065141d00c060007074480c050b00b042d1503000f440a01c0200824a0034003807054442d401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 664614595 1250 664613345 664613377
    0x90303200f040b03180f07090f0501150810030b07081b18060319051302010201141b13170a021e01080606090105190203181c11030f07090608190f0602 66
    0x60488506d04103041028003120325002800200042c054502600104003079041e003c002640c1071142a88000300d195040204100c1030034005003000346000c4205c0042c50700680310045030b02d82610020b021900489a5600000e0301464607650b00b0303104030584034021180c1503100d0200e0301400070701c000342d0001000c2100200e80e080406190071020300c03415000307892000450304414028000642514180d031442928034041400300010b001241c040c0341113080c8880641559403d0619204140c1009a086a2041c00140a1a90b54000000b41044050784240e5001841107440ba0018403600e042d0060940400c3c071040004149113042d0000b1300098805042450401a003650039098a10011449202580c00007030155908140e018114217204000c4541000200405484044d00035100f9001001d00a824010804550741405200c40d00340310070303040f901c0081e13840c1040d002030455489160041d001c3d0140e10300a8980b031f07059000865810003a016078070b05842d641c441c02541f01c0303d444121888 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 664615845 1250 664614595 664614631
    0x100e06130c050a06051206060403080d0c2a200102070603092904051204180c0c022809050c0703050d02070b010906080606010c26040801090303200f040b03 68
    0xa030f0002502d01030b0849075038054551103250103000c507001d0050300e00b601c00e140038001000011150422900385086101d80860450f0110a003a43d81c42c003a450194400301908075006503914091500c0385000b4042e0a002c882c50702d41c03158400c440b41c4003c040ca801030300582010703c603081c025000304c3c4c80a441480720348500320142480c805184000041041c2e0318035000184001e11004010744400c00c000c00040514040c940701858a14038019508005405d45030340c10b40103d280103000c0ca02926401804010100c044414210740014a1180c40d00e005c15148038003140c1c24140e44a61485620b00841c0546002c506860550300c0c1d030002c1c0e0b4008a0980c00304100000a80d820300705500a00368864040350803402c1c04012070038140020007041c10800d91003510804510322096211030111281c5030240303001c40c1d0180002a070b1081c2e800294156007461948000c0692585c070400000d1024500054020f4044400403041e20601c0019060400b06100903c600c0c10b14500a542043c441c1011f148900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 664617095 1250 664615845 664615849
    0xd0b03160608070e1f081b1201270e0105070f08040c030206130b0c030901030614090604050901020c0f06010f0f060f1206090e060604150315050403050c030408070503100e06130c05 79
    0xc040b031290000041c2110140301180d540384003007203242503030089032509080c6c030540783d03034440c150501c2600b4030314810614811001d0022b03805031405050510040c081c0030f080c01d0b01c5030302a2005461400002c2c9121880000403403140e83c071240070b258002e0728100c290b0b10316000c000c4607412202510340c46992000c0006a5800d040c00207212915403003018684640b045d80c009011a8481da2140c915126500c03490320140c2c2d1290040c1780d001070300b1100014143c43d080030081c024040c4a26003461441000200501d4201c0026014100d5007589140750000d9100c10300f00840c0812480b4440104c0e401d1400c4e8a5170340d0103921000d6521105d00300004001d40c2d1a0080d005641b1070b40d082160741e82009040c030005080c50f02441071400b03080c012034030125285039507070369995803507080851130b865607000810105482041100d00d00030704a000c40e5259070b229155580c55040e00d104d041d02ca4400c4144901c642d03642402040c0840c0c12000241400c2e07581c2d01e9411800c6402403400300da08402046000c01c1c4c079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 664618345 1250 664617095 664617139
    0x30c1e0c0901050d03031d0a061a030d0c060219030e1606120c020a080703080a060603051003140a06230a0b0612100515090405010b04050d0305070809060d0b03160608070e 75
    0x802914002020845040d05080c0708035000b601c014940101c0c0200ac004294800007032034403203c016403424843d80102800e00c44001e004070503000b2582410300406030304c800d0b03240c0c03c0000c090300b4072010b4075850802502144003000251194801040790050b01069241c3d2603804420000f0075401074034440041c66135014031552004008070080780c00d000a218a543c010b2003550050001c2d404d0400403420710307088211240d062844024140f038501d068800348841c081c09410241c03544204140041e01003000b44200d101050810444130300702c000005503a00ca564020754000541c042c01c0285400500200c407107100350f0040c190407080d101141d00141c1c6071200b4026801c04803030146040d403541010802c00c401d961040c0d00c0741c2d945040c11b0105022035030b91115600c484503814244542c2d82d41041c64142410301a110000303034844008130b141002c1c0c0c01180c00464104004900707403010108074220030034081e6814022140000d00a03000107061900940d842404035900901c5581040303400d1842c0008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 664619595 1250 664618345 664618391
    0x10e1203091924050a0c020703030504180e030a020a051b0603040b0403030b090702060a18081b07031b0f240807030b030304030c0e01060203070321020705030c1e0c0901050d0303 78
    0xf60f07503104108444012140300301041d100542c40a042140c1ca0754a00802d60b000380e004100c0a00107203520101000301550083c2c0c82d020361070040d00d8903001010006500c46400f508207540710301403400121000e441c01c031230420f10390b680100103900315200c507190303454802c000910480a040e564203004160b9611603189920902880e4002e1a031454400401415141800900b20a42d2228108500042d40040a032140c152810541501d0102104699807514826a0014083c0449400000c0e000c2c00d480c1146416078229139050140181d44200f00300d5904001180d03d2000701c4840e8401e0203d91207881e0864102d085803402188802020700060b096501c40c2e0300c101c0b4002d24040d410420702025040d03090040c50507001a50902d0001e0701d0152460070b203404841c04005514604030303444100c9034151200d00350440c08580c5c480d6180a4065903031000d4034403c3c0c0390041d00b160980140400003600903641d40ac00b0b001c4484076480c2030f0600585c4422100708405041e214508081410552008091 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 664620845 1250 664619595 664619663
    0x2e111204020a050f010c020f010c0812090d081e0702160906080c0607021008040804030c09050f0c1303020f150316080702011505010e04091202010e12030919 69
    0x4000d062910400100c14440ea20050181030207142d180d40c503070303088801c40a0300394064801c109050f050500480b400c4842003401030041d031012402d2880d800e1804192803007954240d048440788aa500740503103403020210b03030802d2845580d2a4002e00c0c0344541c00f00c3c5070880d0350f42c01210741e01d4006442900081e080e542007014181d940340070030000c06a080100c0f100c000307410f0311600d141043c40c0d000f00b907010410250041c240110740000c94100001c2e001207400864110707081c4500680c880c100c4001504c0d0507141326080c8540d61020544680b0100e0442e04e47c144840c124080003490f603801d119003108410a240c0e400340f90400700712050780d0b030403009522031306904071480f50395400110041c00809024000d2411685002c004002c807200c0c0340781940603542d090812410601c2031b0070004000e04082107008102c0221085600f40c03c80d015000600c9940b524016541a001001001d00e00380c0002c8640e80607030342c4254589100141c1802401c404580200c4264450550320541a5040712114410b13107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 664622095 1250 664620845 664620877
    0x3010603090614010b130e01061b05070312053a0f02160305091806060f0309160609140d050601090b0111010204030b0a0f020a0f05030916262e11 64
    0x2c46d03424500406c840036000c900c2c0c05e4a443e50420000800101c103c010455080913001d08540601100308000c2004582c002402641c1011104009040c2c0d0000c0c1c805510f451070280700d9584106030000200c0340c0c40385105108460341c900c041c10801425001000d0040664200104074000ca030045805101e18081d0726040d43d2040d425003800303055658000140d10300394200061183c0781e56254119902600440401c6850f074075134507002c0d41030942843d0342c2442c1040060001070010f400240102c121100c080601203110180300c1448036085410340c00400c00c1e0815001803214402aa02c5940b8180c818504035038446101d10b000390032607200d5013058850540d12010028161907500541130883d02c07640003982003c0b1a41c00280078550101002014000c02100141c8801c0042080848940010b03d0390020a940e42c181884941401420041c0900040071842903041001420217071400310030150b00d084040411042c44e00c10548640194200c3d10b502c11102c00403485030103400c01d01e45142c0c8070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 664623345 1250 664622095 664622107
    0x41b1701020301080c1507060f020909090c01120c054f170a02150904020708041a0a090b0313060c11010e010606050904050a0e150708130803010603090614010b 70
    0x524054245c022548a440c0006000070507441c0701d0243e07200568810000300c0c0d03024400f5000c1c0003a00403e06a6500021401d0400c00800b100081d040c00801c001c9e2a81130801702d000c24500280c03180c0b64001404620100140c42140cd0403400d21031003a4111a07013800c949000d0180910b03140305e0b10781d00d0780200c010212180190500788441400134010001c42c030b101c8009148400b51203060f038407400707481008030104c10189150100c04803400c000d00200110750369007407031403c044290444e0050940486a070b801c0c0c6110902c039942150307244c1d803040e01c50280952400c21201640d50008040320703144421044c0c503000051300c601800302080c0c0079480380002c41e0310b444911405c49004070302c00d08007030781012400c21925800004561980800b500c0110f100e50702e291440c4080d02a95209031514428040c010040d9071080240c507004030210b540c0c41206840345410041524030060001c2c1104c8030400040104502039806401c020b0320840c030101c0c60000300104070074170f810700340e00410a600e000218 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 664624595 1250 664623345 664623359
    0x4060503012c070515030a0b030f01022521020a02041406030609070f0506070c1707051503010308090d150603120906141b0a0f0303020909060108060108041b1701020301 74
    0x88144400380034000c3c401545040000345070b40502a18191212800201055030840141c1013031800b008041d0441e5201c2c2000b0188a0003903200c00756142c0d2507682c1c5440c5408111101c000c00c0f0743d080d0419015071390508500142840394054400c80825445603c41c0f11006843c0c42c082c500c898011108018034500e030402c14503040550080c8146115004110140f00409100304a441505d1044d2a01500c0f84018504007a0000054200c44070100c2e501444c80410100040e8100941e8401d03500c0d841d058001d042004200d020a0200508641090010348040d080005080b00340d81e0082d9003680085c046c8600300d0742119200c0e0010b40304603880485483c04c5030f800041d140028102c2c2c0c50301d8001c105080c003000e032243c0030380f401008100601c47d102c0300d00d00f101003010389007283e084541480710010510b0050000c0d071101500c14001d16104000070050b6001d005c84c0751103000103840b19891540d41d0764072096120510341c10b04055a00800c004074010206c0460707695400050400140d0340d50400740 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 664625845 1250 664624595 664624661
    0x2d0e07090e06012606220b1f05010f020705100309210e0612040f0614180c0a060c26070311100c0f0c0812150f010e1e0406050301 57
    0x8038860791080c03c442490000d54000624070b500030140d00400ca1080c1c50400c101902d0480194054007c000070403c0c00b0981c161500081d28142007a102806040e0341c4000641c0d0901c103013542c076000340e003108004010310708150182c0c52100b0484e00c2c0000b111209595007180c41100000400f40d03902c2003038400b6150030f410484119203038104660351428103941c12000005240b00030401401030002550150400099805c103040a544000c150140c51624032080c8204003103803400c03400d46200e11030030b00c0310f40e0802d4550a0180d0304146d6919015445645403010781c0440b00d5040710b8400c01c00070118a00c02d0300c00c4c02a1180c14400c0e42c07480142e5408418961600c0c442c1ca00300d145e6580381c03010b84035996030450441c0c10440c0d564109141c11050908140c61030307019460760413660101d24410024204a40301d01001242c404548181690703150340700440d03035101070480301504440300b004040090780c00b003001400f0032940100042401601d031000302e0b00751000100e507488408402403080030450380d981 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 664627095 1250 664625845 664625879
    0x7030f030632090c070f08070209070c05100507140c0a08040f0f080606030715030b041802010f080f010b0f0c0d0315080c061207030e06010b0a032d0e07090e0601 71
    0x848140c0141820380f2059445d1140703100013024600440303010b10403c0300075419150a540c005084901600e40920082c003d40b03050b09044600d40644404100002c245108041c06000e4a1f0358210040ba083d4115500c942c1c0850307040701c0203103d01e0441c3c0d00090070b1400104060301c6035010340ca1b00d0740c0c90a0714800c045801d07038000d4141038202c40104181ea171400141c801c112005440380d48407410200109500414441c1000390308141400f00c114015644d08290050061003a60b032452041c0b20480100c07a030314000c4c5c1b4144800700c0170000400145405c40b01a0503100d11070000345140408905030b2514042c1142c3c81c2d04046502c41204003191103440c4203410041181c0b00151207900101c070700141e11841040b280f00f19800c404000b007080c0c94070075802015010300d040d00300d400a5844e4020714503141c0042c0c0480700001d080c00905089420410603030300b106a0050b401036840f413080c140c040043c1803c0c00c5181014444c10600190802d131902a0301204140b200140c04513505001c1030b01d400a07034030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 664628345 1250 664627095 664627099
    0xf020901031d03161b0603050402100219031101110c010b1c0c090207140307050c1002070b0304061d0d0e0103050f040201050d0908041d090106050d050307030f030632 73
    0x10401900c1500b0003c802c07101c0540b481c01c84002c1001e003034038008902210000c2150001710b100c171404244c0940503800315000d01e000b200c40483d158840308049960308030314200c05020380f900e5100d19000074040c5000c60041c8521400215204525032018190303034115444100281e91140c83c5615903040c6103500446402d011340c1c13200d10014054581c80c02c180524440c030440c059000444405100d03055000c00400c4240809403603644807241445565502c0110000303204450030340414118600004881e000c42e801d00c03050038150b96a980701e0100401c07601007502d00b0326040b0340d208010b4000900c0070440074800c0361125580455801d00040c200c4070003c01001c2c422101d10709020260ba000400e51f0803040c4500d001189561051404c44000e004550040c003a800c5446101c20403104218a118804d2030641d00800c0525610010020300c1c10400201809a80080002c040840c0c4206a15a803508440c140402d516542d511817000043c0307611501d00459803d10440d00c611724107803160500c0700d402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 664629595 1250 664628345 664628381
    0x10150311121b031e150a0507021e0304050306010b040e090d090306230c0918150d110d030507060c020c0a060302070f0f0c03021212091e03010f02090103 67
    0x19010160703540c0d01c601c140d600c00114000e110914956420007824940e03503141203251030b55540850300c1d140c0c1c0c5c00320a4a507010103d09507000410720314003480380a124030301c1a03009285a09041800704941c000d542031125a0340004c22001c50b8a0700c04102843c000d158648445a13036510f0b10500948a02019100c0300380c40d04120700442d1515440708008050303030b41080000452000032410b1040105101102404071401001003141d004403032009401034960584000c06a0100c0200c00050010100e035201000c5c0080c81080c103131030600400911080303206412005146c914000014015000c2c00310840008000141d00b404008072809022400380e076500091800254480000d40b000000303000742401c041e4049494030900a03c00307209800107402c0000d4641d4032455040c403e1901d582408280d006a00d900300c3d10401c0400091001111014600e450741850740b00002c2002225440c1c4140e5190f481c84170706962240d80a1040c62140300c1c0e02d800c01039541400c01c00160549044251241e540c407030b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 664630845 1250 664629595 664629619
    0x2071a22030818161e08060408120603030c03040801091514010b0c03120a0608010c050a080c030613020a0e03010b1503150a120b1902030114040e10150311 68
    0x142002400340c20141143d03218a0707a08012910700d2900d042c1d0f018a4010b041c910900044014400c58054004541142c14180180d00c07011025951201503800803c0101c0801003414500030114029400070f00040a40b850400d298104516542140e04900866596010420708000320800350101c01060b60800780042203a41c201c094034480144191005c60000294485501d001402111400c03214072607010010b082c50796046000380403c1c00f03091030541c41c0090300501c990048081d05d000701d04a036502c040950b1003484442d40703a040a0181c43d044000e600c00b4007100011030001d400450100d9550320f42c04940c100801d070a503200e5542890040208171403241811f03500b2412242d0101c1100c0315210b01d468000c012035a0301e030940c0c3c09481c845964001e20020040d030140024000e803056000b14200c5030410049030f04901c401e01c10b44540c400c1410032041503007400e4214a143d40000410f56202c00b4030300b21600159045859914031410046c0414801c008403502004c1101405903600c0300c0c011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 664632095 1250 664630845 664630847
    0xd021b0d1b08030402040b2d0a0603270812150a06050a0e0405090a05070807230a03030c060b0a0f180504121d040606050408100b1003020d02071a2203 66
    0x110000c4c3c006401107499500c075107160340784e034075418200300384c00b10200c41a0310704824aa60703d03640101405200d240750301c000040451080c02071a42031041c0300300317410211840410420110303028a030204c4400b02d0910030b0700c1813108815201c0344070742e40200052042c0e5460104221540c10550080305c184001409603540990344403d03032808400c010f40c2d0008183d111000c049141240010f0002e02510640b04085a1042c0115014048074400388035682244c0c0014402e07151303c60b44002c01c1c2d8100c1d0401004202280c40341c240d03200d5003030080c1000a41c2d07001100200c0d14008180c2c000c5020300342c030342204000700301000b45640c13001c6088440400189c1001e40c0d0711050032030400400002c112681840e04a4003100151503245450010001c1010380d030380780341c0030744035410134400d0b0401c500500c107003c0341240b01340c0102d18100f0002022008850800c40083e0020341009140701002642070080c070000034000c008041061710350b40200c1d0b0040c5440c00000d4a500c208121034644000f8240e40f042c002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 664633345 1250 664632095 664632097
    0x1b04090f0e0736050c09100309020d0f2303041707180b060408190303111318060911130b19121404060b0901090c02120d021b0d1b08 58
    0x246618240743c0c0d03c010030003030204070740303501c800e00c1c6016240ca401c0c240003034010700c0401000b01d40002d0390020300b00300c05071000f43d04541340ea80f0061b400c016610700000001e40716145180720644500310720078600da400ca200f090310080300102d4281da0361000074140305182e400f40740400f40828180040c406581080d08111300450448100b50040f41c882010481d140c0d644415140a4000a02241d020102d91500c030003004100d030030207030046031070728090501d0f40b00c55008603500c005840c102588800c1c580804070207a010422481c004007982e03004089401c0649004400003442c5900000d40c0701d550035000d40f000fa40c169032142d0442c510411030008001f0008200321581480d85c104803403205a072100c140050031001005200c0000250104403c0207181d911072003401c1d106440800040c0e03201c22a040494141140d0b04001da4020780351102e84445000040a20810400d405410300220351080c20440136010055031135904050860740da140c0c0c0c09410400c500104a000c407150b2401611340343e2031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 664634595 1250 664633345 664633379
    0x20c03060a1503260310240c030f1e05030114091e0c040b0c0109060605090606070605041a0709180903080c03130c060e0112051e1b04090f0e07 63
    0x91032038200b98040e840c020034504e61043d820a200d0b425075a140a050398000184a8091005031081005c2458020f4540c0c50b00d4240741070301c68540c1494840161001e440c415100f40c44201009000c040304403600c10351003000c488822039515069129410035400c40582c1006000d1031707000d4140f5004019159041c85100b000140d40605080f200c1d45400b4264080c2d4403a640008000210003d4400056030f4150710070300c03815001d500c0401442e0745a0003008804141903800582c0880107100f0040452050747c032040d01301d03109554407040b20f10b6031840054000421503050300030030f151007001c0000d40f5580b2192825401c00d0b0f8010019204141d40260100c04040d010000c503600100004841d03182d80c100c000c0c01c66800c01070111031190744040003014841ea5040e1540006c40721581c42c9041c882a00416000c0c0794080c503140c0d400740070490003419030b00303006003d00c64400b440304240300c0804c0c41c040104060803081c0c0c80403a6006a074881801903c46011175003085600881041042e40141c000c0d00745 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 664635845 1250 664634595 664634603
    0x5040b181b190809150a0e031207080711030a020d080a020c0a060e0d0c020904020d1502040f0314060412050f1c020301090b03120f0901110d020c03060a1503 69
    0x3800d803070307910107021001e00d03150820324822800902d514885400000d41e03940008550780d503180e5550b0710f0900c20707242c4146883c0039161941840100b0071811658001c1c2001d2502d42040b030307040030361203001400c20150603603a0b04041021381c000e008266031b1214020f00340a28a2008526107a80c0e00402517541110000d50800c01082c0e03070100f040b426841c1c04903108140700c0c5044130141166030034000c0080691003100c442a11450400005950103006070f40b01303254005201ca0015030700c980901c1402c0c2030144003101d06840d005284403e2401500c0a000a8905415043c140c83d04520342041080848074940840e40c1c40602000001103c00b40260102d120301c0c40c200c4e494401c1c01c00209864000d400e8076610f401101d10750f1a0305006a03a000d18100c41407104244008124003041c141c07503440a00030800c1e5401c04005011003491443c5c014001c00c001850b0801d00d444000d900c0c103041c0300c0c43c0c640140050b081603020003a1403030100803494006800390307070800c424001100982100b146c40d100080c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 664637095 1250 664635845 664635889
    0x3012c0f120a0c080c010606030b041a061e1308060609090c011d060409020d1b08012c0c1e0903070513200a02071208030403052215020705040b 63
    0x242d02c1040940c0690368491159516080203a4100b1b001c0c029500580c40001d01c0c1481c2c0d1043c2d8600750007998684080300801641b503142c48004d204030303903200c04000040604180f080c1000314001c00010000c1d60720030746010000b075003000d848d40c0c01c0c4003010301840c0c07107000180e040c0300745201d010880c258042d80900b4050740d01000c5503aa0989850803070f4030140d02c070340040b07400107200c1003035001098402d82c01a0104600c100503015040741c1c1030b070345003041c00007107800c3c0062080a64030fa003c2905c581041d04410b241101e0038090381701000e41101e10102c400000302e10003034154003000368050a42548050303241000b0442003ca6525081c51042500c1401c1d01501e00128a00395404685e080c96504807609c08003120301c500c100c0aa0140c0120301c0184901c03040010610004082400142e034444121491a1070b142c40844041d0000612501010a0a011500c40c0c0c8042600c4400900c1803a03805070319135040440103810300307005501042c0074506060081c040d5688450020007041c0a001c6c1c18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 664638345 1250 664637095 664637107
    0x606031212071e030e120703021e071503060302040c030b031c2a03020d0f0918020c01090302060a1103010503100e030d060323030c1b0f03012c0f12 65
    0x1183e91014440c0e01d000408950f8200c50728655054200b100c0f9460b405088a000480890070902e062185070000740041e00312103402003452030f428180c803440c42c3c8114116a5102c0d1548100b81c01d0700321020800002c40d6950004004600b09030040303c901d8030300350408021044641c0003080d1907103100c5040d40e6444250540c409006802070380c640c54503245214404400600d00e00510030080c040e131409030007503c502c14178100c0c03071b5120f510070310600d0041d41c0d11a0000c6141403142d0a0101142c505500466000d20000581c07860900c05c00ca4014000d500030708050525452005c2115405610031070030110400041c009510009540003030075914050001e07138249080c0909055001d002601c40e4100d060100020600100503d03000c4490001e1081100c015480c102031940ca208100f08041c541e00001490307041c50305c1c410314581076500c000e03002c080b880e02c07101c0010f03003110750850040160310141d840a0001807501c004520f00d0031030220080c080c030b8450400d0380f641e03944e141040e004084000030304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 664639595 1250 664638345 664638347
    0xe1507030c300b13020418060b0a02032710020106050f0d050a080711060a0504060f09140111030409180c0b0304030c140102070b0f0405010509010515041a031e060603121207 76
    0x100510743c00d1305030030841d140c42e11402034400706107a640030210801d0070040c011400c0c00151007116074101581d001149000c40446050030070300d0341e18200c41c81e61508034400f800caa03150340c080207110903000d07400021802d003030504000c42e2501d41100b82d400b40d0f50010380354000500011300c0d880c0b0203030040071705a182c2e0b416191005441d49030784040c94001201255140070305800c03d01500030b813202503d0307001401c00c0a440855242015219080031030204640c2e414182d401080800002d103808025207191079200d101500c180c0d00c02070203480f980008450604180030b03100c2d84e007602034900c5030744c0d851940c14143c50007810f00b50200f074040d140b50b8020362100d511f0002581207804027030b400706010700d06142410740c454030104c040710141d8155080900081040d80103102d00d030310a503150040034100300c826000340070017400f04030700002e4030540700228610540d900304141005001600c15681031100951140d034100030000d8511030107540030522200c8500c0e4118283c40d40c0343c000100b4004542d0720080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 664640845 1250 664639595 664639609
    0x150f0105330c030c0c010e0d110d050105012c0c190509090c03041b180905030903060c07121d040207020f1018080c0303030a0e1507030c300b 62
    0xc00046010380064400b0040c1c42c080041d120307803070070711003034500052407440103481e05225034807020351051180c0060400640d03000c3c0fa60501280280c0150b40080c02c81c0c0c0e606003102d1081e003000381102010710a2201c3d4110000c5012600300100752502a14104103602c0d0110340580d02c3d094480c0d035528078445400340d105006407400504010f14960007800c1402169074550b009860039286042011000c589810f10307504004200c9020040021130103071400c04d4280184020841214a800308200c14a015a01002000d0003104c0d07035144550380e880940b0700a2158035520104400b1300aa140d91510583c0d0510070074000c42c0c4007510050390f41d465910010701010400c60149910100c81c1d4031040b10300340d1203e048600d08a00c8043d000c011506c40034020303039178110f0a10309649a40100f0000f400a4100d03040300400c0d0005e8000c603440007507180d50103c0000400c642402c0042d0751510140c02c91a0b100b01d400301e000300b10f0124404207880d02d51000340c0d40902841048020341e01d4a104520b140c540d45 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 664642095 1250 664640845 664640929
    0x705190e07020f250501030c020726011d010522020609060d05100f0f0b04180207142b0e0d030e04020f07050106150c0f23150f0105 58
    0x400f41c4003581300c4982c0103c0c503214403040c01d400c1d1003039880e404103c55009105e00342c4400d08540050007444e1a188904050123000c5403502240b401140c03006038407210900685003104850307101c070300918080c2c004160843c0c1c001459000650061402c0820315044000104c0b42950151181e42d914200b03440800c40b641700d0354098101c154940010015a0b0051400d032100380e03aa001c045004d0a0fa0301c8410740188802405509041c080c1040f0800649040a61000e45400c04100c054200b01e000d4460300b01d1541000040b1060350400c0030710400e40c004087c4c00440d4900300b03101c10200c04607003000003043e1180c0301d07400c180038822911200c01450b0086603a0301d5180303c010400d65440d421170540e00c00b10b4224003002c4480d5030038903502051042055505a00d01404c0390380301c041414094842c0524040d0040054520420148070400c0720317080400b880c16030701d0f034a000030040480d107001c0e4803a4540d00280018828000380d00184080d42e144d01402c124400d008581c50705481c8104008011100f4903 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 664643345 1250 664642095 664642123
    0xa14060d140a1a06010e1509010c140d0203180307150806040b09011805011a0306060a0c0804091b0212090f0316060206070f0207030507090e0c04090c080705190e0702 73
    0x10380450f558208505018511070a400e076211000000e0306800c0c055507280791107000105034400e010190403035110302070018120340035001ea92100216005003a0800d602088441d005800029010b1071220345106660f20740702d020f50052a45515001a041003801d011400800700462900860055511a046602c0d4000000c040f08100c0d40c1d9500710504101c070f00c2440c1908142408000282d080c54021101445c040c2c00e00380ca851552400100f1800d0382c400c00201040c405480080702c08507400102820240c00b00410000b4003e20b602c22401c01611011403400c1107501c5040300c4019900c2982c15100440419500c4660000050000a040140040c0588082c101550002811907800500369009500d16110303007120315458401241c540700365000103462648034107010041e0309070f642c0c080302c00308208500744c0d008150514006410b46142e1324055588103c4000c081c404036034140328140040000316442e40f490354091784000c00d44080e5118081c0c4050916000403600341c02801b08140b600d0038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 664644595 1250 664643345 664643363
    0x2060f0d1509020c0114010305070b091302030c25030e150702130b18040c15121d0d020304120b0603070305030304080a03050f060d11030309120102030a14060d140a 72
    0x4a0788410002d400c13107010f030f542c95070030680c052401e0344c40180a613050725009070180103810b0814052040036884a500c0036009220f20030400460700d05440a140182c1040c110550350300300085040b206e0261a290780401800003a0b058400a90040c08001915400399200f0707a011070714410360182d500501c14080d4200040c0315102d8502c08040d40f00201d0254100d0b04ca80d142038490441900991044034020842d5011003028841400c20000c4e550408034189402c03003008d000d41140c5170070380b4500e82d440c40e12616410b4002070052001d2180301d03145103891008500300f034900f00d201202c2444005000d402c0e1a008404201252424403c1d40040c1d80c1000072660341c0c1c2054940303900307680d0007101c00b00e000a1070907000c00c11000c90350847d54041c13a0002c11000c3d000080d91075000303962441c0b040d80395140c4410007111441e61104031070b841c44180d2030303000141ca910341162000d0654a81210840700340d020130007040403981d201d0500324405500a88040c8161003200d001600c0c140c9405d1001c0e0901a03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 664645845 1250 664644595 664644599
    0x60525020f0d110a0e1003030e1c03020303060102060901020c0304140609041104180b0d0b090718060f0801060303020a081c090c21120c020604050402030906101202060f0d15 76
    0x41c0c90f046440044410f0301c520898640c0c5000400d03081d03009864410713100740c1d080020404a84203a1107020b2000c1c00030301c00b40424031451420420080c1d00c0c0c10480c09030304080108482503030140f15459124400c2d070025898407207141000368481c416809101d550f103038004240d00490326428282c1e181d0043c043e00c01c00409007030031609031580d0040d00c101d040c031100300300c2c08d0345804100d4040d411100a01031f02c00b1481454656560807112001010600b2902c60254005150841d120820f0310b17005d6036040000d281410700741d0a005640d03c03600049860380c108081080041da0005001c19019041700c0110b885c1d00c8040842141c0007246c480f6404a241070041450500c034684501c8000c8a1803076501d4030041d80c000c0d00d1305d400b01c0680940980006114000020013600400310103802d070380700400e414070702900c85c0300003030403600180d0b0318040320b910050400003102c0c6200c1c4901d003e0881c0b00c12441c007110f07240e40041c00c03a206540743c0050300c2d03a01244500122140390000311106000d0040303408055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 664647095 1250 664645845 664645853
    0x15010f110625030e1b040902040c120605180610090b0309070e01060f090902030c041e0306140907030602090a03080a11160b090603060102120301031b060525020f0d 72
    0x10081c2101120620602c1004109402031244202d04100138010744541880c8141d01e40380004040c1c403131604592500c96020050b65680b040f0801c070406503d0700c44e40c0300c010101410031200743d40c1101d801500c0c02098140c0c403615102803650300000403503501e0b0160009240440b01082203600c0141800004014404103d20208410007610004c04003500560390300d100403924501700c0107095020170040401400380007d680c00850707024000c210000d141682d035100131400f050100200e1040200b402009000b000454010300c0000707c11b000f20780c4464100510a11707115110351000411a55001480006070348400011500440d0850b101a031211402c1202410f50710141c69102c00d540a100c0d2034407503d518641e0030800b555100701d18030742000b800e1001e100091780b014000b43d055203e1901c10240705004100114007035403007140041c2e4070f08500100441030400981106040c08810b0201c1c02c088403440750801080008a074400d00c100c0094008103c0440c10751000075001030707041d2000c4082c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 664648345 1250 664647095 664647121
    0x1509040f050607140a0c06020412150c050301050117220807030905091509060616050a03030f02030705030a0c0e100906080c07020603040f06060803120403030e0615010f1106 76
    0x910300440a9a80c15034071002d04480c40450801450342045043c00300307074140351140c4209404180314920062908ae02c2d005100f001e460012012519184403c1d440710801c503460043d40360701205400c080c1d0440d410306002809180d1a111720510070402800060101c0002c0320807602c160410040e10348410a041c2000810b40c0e105080039800300f103041c4030000d050b007000c101c0340d88182c2039051412142a00d550801c081c56034013900d030310750100703080c8001483c40e1160441000e00c4c912480061840441601e0064290355a1420607502d0b2031041c810014450b82250450360300c00003090000070310240154090b9000070141e84010f40010364030800c0c44a441e08940110252070381601c40011907514107069014500c60364100a402900500c049000965074442e001d034010301c2210b0216210791980e85d8245950071851240c54015228010301041c1601441603040502840c0c010304081e1030101c0302c12010480c10184a410090a50068083e583c0700301d40100902d403500c029034070503080800702c071070113 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 664649595 1250 664648345 664648373
    0x52b09080c0c030c150a03020904062c04030c02060304030507050a080a27090513050a03050a080618060f030114010806040309060c1115070b0f220c090203150904 71
    0x282c1c4201e0482002c0b80c6400138101090b060020152103020049943c0d100741034009940c08010705400b8040b10800c1c0d521401000e0103000700030207111070640d4011604100900c1c00001c6400428440144404240d0041c0031095440e01900c07282da0300c0d02d55140403035070303442083d1016105000f000424420060b0b00340040c14441e4050785c2d82540c484401e07104c020790011001000c070725440807039003c100d040f505411903540702200c442c5156004203580c0301d0a00703048180030110b00082c4d00240d240813090300b202c05135800c58400c4c0e64070310785064030740a03000b220100942032522610321101c07003190503a82504240003030401400700b500c040d6910703140c059544e141954110b000c100c00740004900c8034410041d200505820480300e00b503e244540c103100d991000c50340907240120007000040085030760641243d010303c60320344c1030302c845e8500405c0240004008840c2451003402441181011507030405002040e0b42072003c00603034a88400788640c41d02d0b51000381e940e41001c1004200001d00c0342040350000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 664650845 1250 664649595 664649617
    0x31b1109071b020d030207050a090510090b03150603010f1a03061803070b060303120916062c120604030c1208061f0309063801052b0908 60
    0x20954403080d1042d55030340403070084544480305454109025180021104140381c2c0603005850302c40d034441000c20090b500756040030002a0700c510a101d880c0c0c0501d51000000c0c00f12480c20064609048006602d0b505000040004c0000714400f0030069502980300000c9224126020003000c00c81c0c0040c44005030900310341d81e100e80100e00c0041d090702c2005854019110f07504010b1454184a82d42d080841c80c2d018041c280c0520082c410000c03801340380c4092030700912041008151107588003540105620b86034000300d04004c1004000f00004038009120300d20f1010981e200e1001c0102072020591a2080c4a520301e4240305030002d020500d034004004810190003006148106d01e4004015208050306030341d0309400c008a002502c1c407643e941c1285111524045c640450510403e0f2102e01c02d8a40c104009943c10070060702c00e09a02c08000c020181106540c11040c0b282415107002810f0360141080003040d480040300141c0c1034a0202d0200c5000070404002084031081d50304052032603070400603000e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 664652095 1250 664650845 664650859
    0x171818180f0d11190c030206160501050c04051e010518130f0b1503060d12020f070602011a030a0c050918060c03060a08010506030d050f070c12060510060503040807031b11 75
    0x1c0c0c4c5603001044030b54007054101240031358807450340d400c3c440554455061420201e100c0d644140c0001ca080c080c1501841d90080c9040d20389081c078082285802511098185848942c50041c075140d81120075921800102c0c2490701003068180c021407085481c807444005031a2401200d10034030b00e83d0364040c00e441c40003650a08040810828040e180348001c0d5035040e8092488401900000c942d03a00c850f800140500c140c82c0315200100a46140080a82007500540d4488080310a04240d00781c0301c45141c402180140a04195503c44a185007690b0065900a922000c00110701c000c2c0d10328960015280310307080b21050715000c07501100300e070015121709104075290f000c0095107103814090940101130090152a100c07071061026610341d484030005200c0c1074001e00143d40825400118040101411450801c007001d003480c100301100d000815182d206503128405200032984142942d502c2540031a00c180d82e0760090806845040c104e8105440362514005154100500280030410b0400155041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 664653345 1250 664652095 664652113
    0x60203090f06041e03030b1f030b010e130903020f07030b0106120207020609101812140a0c061b0b0901091a0c0a030f0207171818180f0d11 61
    0x4151100d40907103002c0c280700601210b0000e061613481d8481d500c0e6200382000680310048201003011020300c842d102046400c9045030403142c41e01030150100a00091a103485000c0030040094450010500e04a1005039241034080400d402003001c0c2c4034041e6001c2c100d0705410b03528580b401d40f1500034014140024000c18030360401d000c40d030090b548076a41c0240400e00305000a0203004418401c1036082c01005211400f00034a1900d841260000e17080305550514480002c0c00c104040540311a010710040e84421003150205202c60320704016070b01c0c240361040200c0e444200803044810080409411204000180208900c05502c003094191207480b9803218200c1c14580004c200b64121140c103506242000417800c00d80c4258061030380340c21188401410100952640900d8480160a60594483c0014031b2190b5450a5030825014070040703078506107001030042040204c600240c643c0c101407007a450070b080030741414010310170b00c060101c04440c5885285400100840b025031001312017070050341e000b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 664654595 1250 664653345 664653373
    0xd0e06060d0305030604060f0f03020117060603010302010c08091003090b07112815090309211101020c09092424032a090601170a0510050d06020309 65
    0x6104030402401c03084841101c0e101560182e00c0103101c198860b03910840481c804000c20348642c0540308642c049200941184005481d0181c6d03030258480d501400c40400016580f9242181d05495080c44c1c485101d645030b01c0c2c06172a9008028400d9030200308082d90200300d581c958090310340707580208800495a281c2c4c1c08103075014202c40180101070341181078110300a08040000113020f0341d000f4000300c00038000c1d03294012403803003110540c5469510303900000300340b650000004000d070414003041492464802c00c14140004402c00c01440c046182c0080c030b16582c02442040e10b00c000c0a4810003003440e0000785151111000d0184034500d2441506401c134004128424502c5003c1c0f14001c0140b0780715000131000001c08030300c10a40e0520a00c00b0000400c41030780900e40c076440181030342462030b81c0b020042040c48003008004604008040740003100c10b02c2d607085001d4202c80d030010005100c0d22001d0030350300001c0e503a4002c250400c2919a44808201d00d9a00031407085440d081590710104202070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 664655845 1250 664654595 664654603
    0x70b0903090f0f03210d1104050f0102070609050f040b060c010b1e0108010e1003050d0e1302070b04021210060e090c030706210b040507021b04151205070306110d0e 72
    0x11942d8055000d00010317000445a114415100e841131861142045644000d40c000c2e03640015600107120030100b01041035043c000e0a4801041003400a00b4106041a600406d09140c0c2e104803403186401011500d20344c0c503503034440c9005c1324000c0c00541e03803281d041403074a010340380b400b130f980340205040c40c0110b048810712400c00e03120960595650000780d10700301e400c000481d0064847c80000c1000100080007400c10001c0c16820b0b0350949521035800310314401c001801160491045405004001220001e90666000e560140e4100c4031500750344000c400c1345141c800440c3e008101a49011408604001c03070416041c0b091550504440c1e003090190705040d12000b29101e00300214071814020401001c50300c42c80f629040048000080c1507404400040580383d06071000d40c050380001d2004029100b51a200c1003020ba000e0f101407003200650198000c2c00c00b03080c4981c0320070070543c8000c1d204014081c45090010f41d002102880485085a040354450340b00c00301510000b0725001d074821000d40081 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 664657095 1250 664655845 664655869
    0x8070605100504020f2b021204111905120705130209040515010e13090203070617250c0303090503071a1006021e0a0510020a02010c050f0405060906070b0903090f 71
    0xc0e0098100346e04c52031404074031031121041540c51001140e008581c411030380302805400e600d602500c00e0600b0581010341584510719607250041109544070300d240030542c10100c0480701c0a4850f80d071001c2040d07044034240300d140e03001141d00404030030202c80700c550160003502d071001c4125001c000319100e500b0012421b009500416010034101003452607585840b02d1642062100a0f0003c600b8010990000742094901d400c44400b01388002d04581c0385215070641140d11090f1401c0481d01400d401c40b8941d0580344800906042100c00c1100f80101482a04029039040e0300c001160b07210303052071909030442c21010740c682c46410030101c00101d0300c15001d042241100c031b00e46c01a0950310003409c940400300e0701005519000d03105065500300011800c00400c3e03061400541c0060b21640b8140c0c009007901d800c51141400c01c00d052004a11004050040b10700729181100c0460340c0742000030101c0d41d40d014203080070b4450050181027241c40c07c8084000d0010110480d900d00100345a0000c0001840e40c10b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 664658345 1250 664657095 664657117
    0x10090e06010807170103081803030a080f09030c060c0d0b100503072f06040605060a050306130c0825050402030c19050c0d020705031b031f0204030807060510050402 72
    0x901180c00c9500038103032950000c01034504201894400074a2503100b280c00e80c02203562860009090b080548d10300041e90f61503208074090341c07501c0c0304000002d00e80e2030041c100380100c00c010800f14116400420440d04003111213016906a45440c00c400500c42d0002e0110302c43d414140000c05181d4540039600c2c8880c00f00c01d444044c10740c0c1302d8140840d010440c05000d001054055520001840c100c0e11003906650716a000518003807600f46072500c150344000d0b003000d000303101825051001d5a8042601c82d40000c003107400b40400201c0342061140c02d0126030000800e0b001311883d600020240c2d880c440101c00c02800c28855482e915014070040303201c102c03068010a0024005d18007143c21321100304204011900d02603050030146001a0f050106002c48203003d07a201140c03c000a0505000c201904140c1101035801e100c04400441d46484174400c0e01c121003505005140103002c1c8c607505076809140c04c4840c850b120074007803404800400b01940c51401c13400d005000003600d49842e0003261142200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 664659595 1250 664658345 664658369
    0xa0305012f0a030f150806071805010906080a021204030804121803060902032109030c0406030b130611070821010819020103272607110d05100b1009 65
    0x400100e00a244c0541d20503521131700e80300c00302d1044045498400190001c03d0203041242400e641c0541035403c1c680b510f1459003003a103401c000c2a0303048840042103c10508125280d9654002c0250080c85105201c0003840d151b2018041031651261107544568414095040c1004640c141500e44a5004071241d08001c0c0c0000c0500014140e500403000061001d03084400c0c04800031003282c2202c502d8800b40c0032942000c20403c60503c0d0800a81080c1082502c00300140d60864440140b42c483c000c5c200991042521000070400003640e1141e24102c0c811005903072206018a0240c10300e610450b00d4008546001e02464078295240d21040d0480c0c458500400e42c03c503034801d02d41c050081ca4402607050642e26243e01c58030301462094400030500600f41c580501c5010300d00300740e03031050b8038440840141c04c22607040400c8990f042101e01507a00011214840761101d0f001404444280c20010628050400600044000c581000c000404125150004208000b108072211030319885000c101c405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 664660845 1250 664659595 664659607
    0xf030106060c020108090f1c0513081f0e10021b150601121803030c03020d060f0f120b150d051903081b0f030c040f12030f030203150405150a0305012f 66
    0x1180e02100c034905d025a0034414100352902b0890a2045c43c1640806010781001700f000410007501d034010344000c80c40034000c00117088115042581d4140e10596a8480c5070f001645034090410340c0c2d000900458200d04039011004406400c08110b141958414040317100c0c10601a01d41c081c9000f148890020168210b40b0000241c4040340509003010b19281419400c01c00c3e5207000049000d0356014001c00002007024910301010034025000076804212614000e4201074001450021040d81210309040c0302e00500800400143d000d00c5d1740c0a0041c190310611038a25000c21050001450035030103a103811000e030352001801c4102c0c6100c550030201c0c41c5410404a5500c2200001541e00000405845414aa1191941e100c140c9198000350701001300c9203000c02c2051f50202072000345161501c0d055046041007084040c103641010340003813241c4e8498002900c030112040a0910280c401019856125070b641010380c000d00711802049208075218480c0e458041240502c012120000e000721490300b8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 664662095 1250 664660845 664660873
    0x9150a1508012709062306130b130c121a090a0606021504050a0b0c03010f05030106050f1e0622080f060609100305030d0507020f070807140f030106060c020108090f 72
    0x841035a8080704d170369640f558041010313101c0244142d440f9070401402d0807141010810003007810300c0072168940c100d06009d42c1840070346031109032035003030141c03410040f4409061000944216031699080104185008840100700c00e08000410043c0c00640e840b00701034035003514070001d079070107030007034001680c4a0403440c010603000041007540a802981078603118491551249414030041d103607003070344000220041c000c00f0200301d03100c0d0041800328004c000c2e0901c2c0c9404628082145150184680c12101ca200e10010341d4418241001000604560b43c560304083c080c2c0b0150100e80c02c40d228540d08010129087d5000110581d03045c100400800c116034420041060000b4014002030b0004040311000001450400103802001203100c00400c651501c2c038070007403810310b40708008042c0d0b40c0108010088910046a082c0548141c100d101404500541c0030550b6000c44d4150f03590036610300b500025059600c0541044254400d0361100482d0b00d50890302503842d4400011920590402103d811801c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 664663345 1250 664662095 664662101
    0x204150b09010525061b0801080c09041a1f0602070b03160219050606010e030a0c0314030f0c03030405160b04140f04020d050105030d03060305030909150a15080127 72
    0x1007605011044e0302c1d540820b4410310382082281c0b040365450749075070100d1107043c0a0781c420110340030309203031200f199850680d20035611924070840741d0295600d08046418040014128940007000300310321861f40c105400301c5510f1044502001c2d0728009001d80104010740301007641e030111880b00d40303420309548030595003422902c00c041120307096201e8030342145800c80c0040110900d0f54000c00c003519081c5411030000d0141d400c1c4203081171190b000440c07030310009100740001109503600070310211240080400740ca4514070480307829180c500c1000c5070542104000000452265104105079895107a142d000000026100d0041c1140a0707001e01c000d002040b14441074640c007140048c44080004200e8011030201e901101c21044195100c00050019040070001e0f08a901c24a140401c502c91461700c51580743c0c050915158030450850000c42c0748174640f145488200301c03006090399449940c81d2148900240e8100307201340820407410000514401c0c080c401030487c01130300288000445484250402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 664664595 1250 664663345 664663357
    0x11416170c0d0209091003150b06030727030f050c010e061b0304120b0a060501141204080903060f01060801050307120320070b0408010b0f011704031e09030204150b090105 75
    0x101d80d801e00070041c041d1741d803009403030092054a0f24905100e06500b0102071030b00c01c08100551031401c00211030038580b1000f0860758844001d2411000c10561107c031200c0000307400c401400c040d6815140481448141e803101c1c80d11038030030030031210301c5004d000055810030f03074180b01d0b26400201400010354007094043c05c808002180c200742c80c0b034a1b8440b0202c4000155083d010755084030b4140070000d40c0c42240c801c241c050142400c00741e5246808441c00002c6100d00480c014102002d940850100105801070320f01c2410010309550042c54005058541c00d00700b403003540300007248000006198207000c91b64170140c612084800b04440f140303440075180f80d40d48085e00982644009000d0302032280600019000c3d00b0800f0740240c0d154501002203003035a0310203515600c41c46003000702191580c0c004456029513240280034420990360b03410240c840410f0015222030034114070100703140d615070090b441c9040e2031003250104121080300d900040c182c00f4600629412000c10070030100365602804c09804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 664665845 1250 664664595 664664617
    0xb0a030b1e0705070203061308030a020702040f0e06040302120418020c1c0908071d071116090b01080c03100b1602130621051902060c011416170c 64
    0x11010302000c0c10000340441c11900c6600040c8003168050841c030b01808500c1d0000024816010203c00c5a201c102d990322000d0480403401e40c2c00100c200840d110b80d0044201c040702007600300640985281482e46a10b0112011001806001004581c08452805903400d68800500f9107000c410105083d030025844070301400340600c00e11440c1005009601d202e030580c850715642ea0034610740781800c028070701b52541d000100e00c64202041c2e00c2c0070402000034541c3c4400c09140054403034104802460819030413031a000204201700201084e40c5031940c001c01d105032420b030f884818035500d00b06110704a00007a201512034002400341080280b6401001e010301c2c1000341080c416001e85580000c0f0140122501101d4460711900100000c1003016040003141000c4142030840180586c2c51589641a0800b42062841d0307040307801d0255111031083c0d0742603004030720003004151440c9a421200b80c2c401c440d60070141425a448485442c4584c280b2000c0c00040e20140695440781031040ca030380d4024150000e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 664667095 1250 664665845 664665871
    0x307030f060503030a0309140d020a0f0c0e01080601080c060a1d0616210f05041a071406090d0906021209031204060c05010c050406050702040504020d05011a040f0b0a030b 75
    0x208003a0340c140011702d04c1c0311443d140000e0205072071502d2031035084540c0c020145508602010030b60036802082240151b0b5005814182022a03807030010f0701c01c0101d811440c0741840000000c5140e180004500e4107842480080b075010f0301412041000601c104041c50000844004010007032000341c400b454008100102840e0400e0341c1c10b051510070b00e90400d004d03500d503000300d03602c03041002c02c052600050348010310b0321b400d101001c0340024205204501c074600031040705100c0009144072107000d41300f4150340501c03030000ca40c41075013007d0751301c51040c0c84050690040d20790152450b402605010100c40390f940103000200a0251340c000d85030816100507806004070105003010038003400080000d0191919004108450350502c9402c40300404494070512400700000d0000d181c001c0241d501d0954111000b02e030070340e52403022950501886000070007660038440040114000004161560b25050700c1c00c00c91070340306070181130544d04042482d83d001100381c0018000304402012159210b6a9200c9403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 664668345 1250 664667095 664667099
    0x6010903080d0204090e03040e0c030a090609030309021009150f050f040801050403110f12180301062c010302211e0a02010801060e13020c010b060f090f150307030f06 73
    0x1d400030b500c07000e002c4a60340e90000d0f050001418500c03e0035080c040c3e03a4000c3d4101420700803d080180740250005660100100000d0f983e5461a00408150703070b0f0200d0144000307072440c0b5019018041041c012886042c22100b11405d8a00c03408620085924909021600c00030f51403041d24401000b070684d0f4100001080180c20030a0300700e00400003042c07043c000281616090070028011010604120781c19000110031501076400014070211020100141e1aa02e00000080e001000c1c06d543c2e49903015420041d00086005100303c1012240b81c032085a40c607401d03500c0540e440480c0c02400000d62000a00c00d0414035092907100300201c5042903002c0301c102544030280148900010510b110300f90340b2040d80c030821542e101a03100e004004504142d00300502803400620140c44180c8812502640440d010740410b509400a0410320b101074001591110104118619584030b10401ca004060100c0341a0481c10000034282500ba0100381082c110f44131650102c000d0005500690702c0c0b41d03180c0b000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 664669595 1250 664668345 664668353
    0x50a111302070809040e0a080405100e12060a0b0402071a10031e11040605100c0c0b0a02030d06080a03050a050c0309090f040b06010e060a030f150f03030207080109020d060506010903 80
    0x800e02d0341d000303255203500c0c0c088150810013600c2c208014a151074000c9503100c1d0000344110143e03400d0314400c0344c40a040c0340c1405c8045a100c1030046801d5400f104002410351680404220305000b0441d80d602030010004080c00e0009074456110014450f46066821034840c0009060700c80d0800c140c4484601c203d070392900c4484104500c007030345011002d054450a000c205000b0010800e01006481c02d00000f454400010010100e0552107014403801e1801c4d603003000300401d1038001529030507002c1c944071a08030034000e5480c1c100003506207000e440e000300440ca4040018a404029a159a419182140442040303580380c00107a1a102544018001c0708000d035543c02c012403298a18242039900d61906042c1001c5071b11001d4000340c1400406a00050f19444290841d01d03404070700e0a01040070605080000c2c01480c0f070011480400101160102e015108581f420040301d001e1350844030800c3c1c4034801507080b90b03201a002984044e1212217140000c80d25004158400014100040b20946d40d480e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 664670845 1250 664669595 664669597
    0x3120903190b010914010e0112060e160806091c0f1106070e01201009020a1e170d0e040c031829061e03120703051213050a111302 57
    0x4101e5249041c6001846001c1191007007221510400d0b0044203d540f610921911f0031106015540210040e0941b5609000f025000b41c4034a1a04034121038658004111a952808040c0505469801400040f481400c400039035a01603a40990345042c00c890a08401d84403080009a104140000b001801e90140414402c1780c2c8900b205448415002c14000001081d051003040f0640c119024504401d104080c00610702125034080c03403001030440e25074000100c20080d00d9001000040201d074010000c0a003021550b01100d42c41c09042040d40010581d0584804182511034002010b14040840d1864182c004881e0603040c0d040009020b1a030841c2e041055565041c15194961440440c0f242c01c0d0100c04440300d029103d541d920154241a00000c080130b04010002056500e40030015007542c1c1c050003120079440400400b00c3c0d5501c018600038007503402102c851242d0707240880c00a41601d101082481ea400c0d40600602400381080c3e8581c071000c1c2c810105c980d00034405503655204103240d44 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 664672095 1250 664670845 664670893
    0x10e010c15020a090603140a0b0609042f2704020d2a02010e1011161505010603090506040f0804080a08040302030c0109050a0e070e1302090a080c03120903 68
    0x44009603451510343c0000e0850561a80800d04161816804c0c90091082128444c1c0007200d05401281d89191140010028001c001281f80e2042c9050040a003281ea0300d401c1407610080c03107605001500c51480f0320042c40c00b40020391401000000304148040c80840642181000000c01c01403c2100d1100100226800b12403100b90f032002054105081c03038903d803009502000315100030700c08041001d01494407440308180110900d5143c5202510003000358042d50040d017000f0b00004030841c1542419a48140c0e100101311300c9a25000000c50268424020541019040001000c00e038442e683c2d0f0710340342c1007144419500c00b0f200f030102081205092101058041c0115611600e590450040600306040b00745410b05110150f0020040c5c1c2d121944000200d44549a5924055072190703c150f50032500104010f900c22550300802400944507405805000015500d080358682c55888550707a4503500e1401641c194011002051412200001401402c0014040d91642c41590f802080d490400c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 664673345 1250 664672095 664672133
    0x130807050c03060c03070e06090f060a21050f180c0306011205010e0102030f0c0703030204150c050c09060303090622170f01020403020f01030c05090901030b1006020307080306010e010c 81
    0x300c003104500c0c2c204200c94000c03d0149405140d0308004201030000d0181b1b40c1d03524021500450004016907881040c8a1420000b0b00000e684500c0c20000420704c1c501c49001030403c3c400c0705081442210300d03124851103000c2040003002651960030f0300c0b10707000d140b030ba00c008500d100718a0300200302e444c01d000043c0200034010085a080d0040d240c035030700f0f5803601194005141c0c0305104210582d000142c0003604079402c030440542d80c04460030201d0203445650060040711180000d10400554801c2d50050102c0c003801c252002401032a0030031403d600140c1c0c403568103a0090001c0031203858140010300c01c44d00700c501004200d6003414401e0202e44020341c031038003035180d00501402d1680c031305000c80c1400419001c0214136150540d80020194070400d0441b84c10140d40303050f410b00c01350181d412030b180c410000b0b040080c01d42c0d4070f14194420751800c486604150004000c0016a14000019116403d9024070001e0541d660032004560035140742c0f070706d10304100c91105800040b4542d038088131518207207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 664674595 1250 664673345 664673353
    0x606020708010b0d120f020f06101706040c03020f130f02030f09060106230c011811030705060405060904060e090307120912140f1203010e010e0c040306020313080705 73
    0x64200102d0071608180c0c2d800b40200100c0c41c1980000b80000b004080c0e51440b0b080c4542e64100c003000172440c1070319800d88520140710312024000e5140c59410800704171550000d581e281d070701d1860641c1ea218035003640c00600c0348014920500041c03a108144c003400207809000d035188401c072902c80d4401e80b0b4841c030400c01101e40c004280800468413020003030388144a00000d205a5240503070003462280c0056609181851a0f00c40d0401c442117182141d81448282d0001c0c03022000003600c0c6000604940402c4484e48105450100507040200c0d1000c210350f0001d2006042030714150038001e0302e034003e60b003042d845941d44d04081003e014a614050203100710500940d04c9035482e02d0315006001440c0c0c50f074010310407070840400555902811545501381c0c042c101c002094566a01e03c0e2402035605030140150060180c1041d20020b46406507040f00c5501c6502005a40d80c3e0a0f10320003a501510154200c5008000034030105100380c0081d508081c010580c0f250005541e1540281a004072500304c0b81500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 664675845 1250 664674595 664674599
    0x20c0a032003070b030a02090f3705030c040b06070b04150506010507111c0b0c0c01060902091005180a140f2d03030405040c1e030c09141306060207 65
    0x440e0003a2481c0720398054000f003150342d050003100500b03800010035010748035800043e401840e03110700c030464810050103071540300004007103010400c03005403a005240401c002d905405045198606802c01201e0002c0c0143c824010144d043c00003915080000d90380000040000500090b02e0320a01c41c4694050316040c11601c440802041c140c1e1000b4006a041000078030444020031807440d480700515404844211002d40400b040c81010562a00040c000303802100800c8040048100100810001840204501ca8940c0030400c01c82c0950400141c000c1941e9140c0d4000c103010314000c00c54440056603642c40400440b0008841e442e040c0c0083d42425114845c0e0311a42c2050f41021020020031942d0040c00c020485016101c52118501a43c41c181000f00d8000316441c14400c44024000c003500900000b0340c001030141c05426901d5500d081003445468a01c00240300e845a040c00c1c0440da640e80701100d29101d5a0445c503280080342c641c1c00325542c55480c01c0341d0b41e94480c020003410141c014080c058 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 664677095 1250 664675845 664675883
    0x3070804020a0f031a04020d0c0314011d0a020114040801050a1e0203130206031911090a120308190b03011407020d030915020a0512011e0b0708120601020c0a03 70
    0xc20a81c0701c061501602d43c424800240002d2000000300b02416406a080e80c441c00081d2503010300060113400b0060b00100807050011081d242d081c400c900000a00403c200b0105203d129104040a2120790b00710380a540011740c81000320f44000d1500c0000700c0e041c1034a03143c040b42110819500c4803291079482501ca500343c0071030380d24104240c62228085046180c1034a0300303000e541d41114000c0c0325500000000740b5000269400e503043c062211020004c88545041c556910741c403072080d107846030b54003400001f10240040030001ca000ea140d0389d17641c11a224031540000701c00900640d040c4207615002104113540f8244070b1001c0c807103198445000b583c244020b000c4c3c201490460040200b506044a82011419034507a5a204c0030480b000160f45141c0c89904a4842c001c8503480c2140c4041e9900004a0508c41c2400700090b1488803000080c0303503a28200080240f081d103100078078114083c030824103010200d5031050740c842011700644610ba409200007030b0001c103d03504103c6102d000031444103e55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 664678345 1250 664677095 664677109
    0x111506010810060e0d1506060801030c0e040302100e0a0f052109060703050304060b120307170a08040209040515090318030f030f0d020405130c031b141b030307080402 73
    0x8410341118070041c2d02e003442c034020710341c1205041c07482c0200f00880b0300340304200c010040d0707103a84d07001c89a00f08442d0741c0b1810003d0580c1d50a100548800380024000309200a440d5030641c007881d81600102195030345c040203e0040d01000c900c0000c240201c0c0c1c480030100f9400402145c641d445000600000d200d602c44081078001d842000c484031a205122039600327038548004444000d030301400c0075506d2f542c0e1445c0c01c1c1c02601004418a400400401184560386000809065444e2140450020800882143c450340780504480900098030140108015050403c1e850703800ca801036040c0c0d800c04244a40300c24204605591011041c0c0c00001d11114000c2414405041d00c0b03000c034080c1605c5400000c030300ea60707802006109022000e0000b01101c102003076a04840003080e02600313901c2c0118805217100000c040075095038020a0070061640021006460304050384400c1d5102c444c01480c0d101800002a00442c680a00a1119921010080300c081015500c690310566500d4000e250520600c154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 664679595 1250 664678345 664678351
    0x70e040510060206180f03070c05010f02120f0f19052a3d0b040501050f03100c0c0c2c010605040e130807200d020d02040c1115060108 59
    0x901d1038625014042964007240907500055586554116202c0380c0fa074407814407411507420b10051000054003010000120302420446400341c0720420043e240350700598841408a00120721b220702001000d21800303a010140603c5007843c903100c0e0030080d0090101c80c540e1100d44122020802c0814001c01203c0c10305200e048000d13556406451000600c42490395070011801c0400900c5480354004401c1c40a81d82c45458030340700300842c00300520441000c0001061600011401581000008151420001804114544080c006040e42e18032a003c074801400c02509034000c102e0502844004aa960200180604401842c98003800300030940b12920500041184050004560040054540240a407030032100d0f4440d200401d5911104602030040030008028902c00c0046441403d00840c0130840460f003c512134540c41c40028402046201c0311120b40c020352007418441040e006052070303001080141040d05081e00c1d24514607480500f81900c1442c1c140e81c8007000c000700103c56a000307000a030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 664680845 1250 664679595 664679611
    0xc05060109110f0a031104091401050d1104093906030504020d0f020d0602040b1c152d06020a031b1a130503030108010902031014131406070e0405 64
    0x11000b00c1015604100d0300603400d41009104001c40c02072801c50207a004401c400350400c0b0806e58481c1c440001400500380080540c03010b550410020170103003000c0c6c14811840c0e0704984810031224000042001501042030304030f602545480d62200d0943c855000852407040004103616085014402d00043c0c4000e03900c21401c060404041c0000750f00c1d44030b00080038540000307088000305518004030340d540b1041e00b002800b0a01c00200010144400405080704201080410038401a0b05452038141c40c0ca41070020f42080c44001d041200400c0c0b8408104036046030f00030b48034a603d02d0501c030044c0321200e901540240c1c1103801000100b40e03003d41040d04c6070813422005025404c040d00c500f41e00a800d000496080300ba40004a10301000f04c429607802c01307900500704c9940f5a15001024064200100100e0081c41032049205980c8528002e022585101400d10030712a592100c00404035100e2080035204a0120f4a46400740c001c14040c00d0b01c04e113443c3c0c452004d004c0f08030f0280001c441e00202018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 664682095 1250 664680845 664680851
    0x262413110303044a15060304111e060a050d06050316051005130306050903070f0318050901230607170909010b070b0a051008060114030f07061b0c030f030c05060109 72
    0x4c48183d0003450000c041c05003801e1400041e030396400141c1450a109440d040e0700c00b1000c8100303c20420054041c0302c030140243c6144080104202a5008111f144959264400010301c80704540c0d612800103060a11910400410030580d60b402090801e101d060300800e803c4051042030100b0304140800c081d80c0315041c6403140c40c10b0140c51040f0b6402e01c4c28000100219125008900300320303000c00940700754540011403c032a024803441c001e05005024602d0000201841c01c4c0040c0c0c5207403a81d00c89040f5480c0c0d00e2165982c500d940c00e010648418094a15400b0105001040116091880b0a0007030409062001d5603514072100308800010141c0c04140c401a08110500000d02504c01e0310ba00100000800f1450b51201140001111055003000440344074a80000518510f0b4101c207004400e026000c0c1c6080c15840f07005240c541c00c2a02814010802c0c1d0307541a44075642d03480b072240d00d503402030703050210154903a41c5d14103090b01008000d0b00000c0c07404c2d01c410705000080c0182c0e801400c2e022020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 664683345 1250 664682095 664682189
    0xc0206010602030a0f27060801120f021002031333023d050406050c0403051902030a062405031b0906030726241311030304 54
    0x2d50f284100040e080400c480707030030780c101841e0003030383c1011448444c403400700c40d0811174001d0340a000c00e040c490100020142400082d081404e0f031150402242c01116460220070301f9003c0c062540e035100c2c0c5c030408501c410044c0000d44054028008080c1074900700d4180e0650b8075000d400612062891740c460030060301c442050001da000100c0c015011502d400a0911107050304030740b610143e0400e8030b80d042d03400880c59900748001c290b120501c5a4400c080800c4035446911481c0b003680201c0c0001012030788080f07060800d00032801c1109040318402400c8540c2c610300350741da18040e50201c0442c91610038542d211342103440421100e01c03024010a80040418072071000b6404448924551468007806e240340216046880500104000d0300302c00f02461119112405d1300182c201e49a00c0c2d002c032a006441c80f040350000d01503603000c5907001c0f850302801691100389104040600a2008032054903020060300c2c080c0d202440070300700901c0c0d2920842060103105008100407003102241e40f2a055510602e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 664684595 1250 664683345 664683347
    0x405071d03120d0513020a15021204120b0a09061401060e010f050a031503051b130203070c02040506240405011403010f2c01120c05010c020d11041104030b0106030c02060106 76
    0x7a10304283d070490000c03903d525401020080c2079043c0d54040d4100084680114480c502c4100c80454403035641c0c00c0b52a41d84d00c5403230400050190f030003510000c004000182000c5401501c1440d0031031551007001030039030b0a59030b80340c0859400c03426032070740c904007a401042031035001100300d03840302c60a0915513041342c414400103205100d03040c011418107a036070b44107161034141107508002030b6600000316007030101c040c60105c11484024003158401d8200f00c03100d4203240024000d681c003406107030b220074503900c02a608000c00342100500c819003100082c545001c02e12502900071182e0780e50b94605585e80c505040004004000c02c1c003245580e8a000c01c01004006a42000141158281d00b5244080041b080142d21400e80482c0b0600401c0d00c404004210180201e40101d0482d1003a81416149592600191000e01c03c1c900040c0d4810201040300d0003103601e0341080924510000c00001d8002c0302e03003411041c5038015400543c0c07510445001400041d4040c80341600b411983c0c00240388640c90028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 664685845 1250 664684595 664684597
    0xf0306090d0809070308070c090b011701030627110f030703031d03070f0905010501020d210f0e07090510080601050a031b091d0606090c04140f0405071d0312 69
    0x1600030700b001042d500040c0c00500501c04036001e10703440344110382c0e42c0b1841d003003681d004103075030160541c00341c5446094642507009414aa001e52101c040c0003195070300c0c1d030321580020130002040c216100d42e0b00c01400048a51a0803084005218408290b44010020240040c6100c00803a080c003c0e4404503003840402d030424144859409007003d079402c010300050119003400300b44d1340600408043d41c03d02003003000840d00814166042a803c0707680c2d845014600711003071040c8620750f000d00350a404650f40b6a40990308018020482850f0200b40b554040904600d42031803948000c0c1001e55950620102403a80207030040280304020003030140d9414800010000b941c1880001d062007401095024082c2d40c402d071074801800301c0c01d02002218601800d03000342520031405215503004480c00100c240c90201c24660003408403011460526081650340d000100070021901e510185a600c0b680040d42c89005040c42120240d650484142c140c41c95a030742100a0b000c41e620070380042c84008583c0522710 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 664687095 1250 664685845 664685863
    0x60e10090b0409050607020a290a050901060b030114040510082802150702190f15020709050a06170106050d02010e0d022d01020a080708070c090204030f020f030609 72
    0xe0000100c0c001a40c0008005060400d0700803d5030080c82d04200503c0e4000c41e140d641c0703070f010f405004140300080e100640c810302560b000c400d04440c62030104407007030610760002d548808880c0000405a464050079262070308242c1c0180c0b0840c21702403d410060915015045c0c2000210141400c050300f0300c42c0e101e4403003401c5d03039004540414148070840b96055440402c2e050940207450071a00005034095000540d100d01000d0740641030000345141a86447d11a404c21030b0011001140035501f0b1112400c0004005088801140300f2054045013100d010f1054900800c88004d0004071503203003c01003015110407200100309649040e20400ca40c0d210b0f100315181d1258240b0300158800240800640d024880010181d04003600706081d2840300f110410003500024a100280d004003030007001240d41b40000e09006041d01000d010001c00101400d0240004602c503103030081d01c807911040741e01c08980042d40103440d0000c5910310351055007420340c46803001c0304040d4041d108601d00550b01c20f0382d810443c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 664688345 1250 664687095 664687109
    0x20c0d09030b161b0b0714270604030c150f020a11090c070b070c0c080f0a0803090c060304050106050901050423070212130e0112021809010912030c03060e10 69
    0x1030150f05030580c480c00310305603091078007404c03002d04503c0c03400d02a03e040c03011611480810f86000c0001600c862203015941d02c103805410381280c0c0e03c1364500419028004a0115411170028400800015074000c000c4015281a60841e9410300611308001c0280c000c020010080d03410100044000c2a0419071400305139800392200c00380d64407200e4100c0088e214100c0302030183c0810105001209501022541496001c0c1e88000201a00d40008540342c000c00c4000d45c85c240c0c00381c0d200400007554070b000b95034000324030020785207840444c1021440d03d82c401c0320203c5490b5540c0c01d050015290035410940903100070340302004101c1d10103c410010320b0001c030001c40e10030350400028690501c200f1030204000801d959090b1140c2281040f204000707024000d2090030424180046050000a501210000e400a0854160711800d000000c102d800181c42d4002c29502c54036100049800720401181d01403155a0010381c008010100608a03a02500400103400e461700c02e01c903540030044007001c140c0f001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 664689595 1250 664688345 664688371
    0x70e01030c15020a0804082a0d062406080702071d01050f0d0203120702040e030304050d0c111804060b030d020705151c06170a0206070b071101090501020c0d09030b 72
    0x50030780913460b0400d030700001400c07140000340c0802c03819004100d64003030410301071003a4614554080f000c0010440d000e009038212030b071400800003248003504200104084403030522850080052005494009038110002081e041c0f4103000b070441c2d040085074024400390320b42000e06001d003680c0c0d585c41c017030603c0b03403d1081d60540c40e10140c60362030514501050340c2c0101120402e01504034030b09040d0f00080c0741030707108a24001440c0015640070044130b215a03403040c05042d03241c148240c140e400140c1e01c04152a89200c00190b0409038035100042030b4500520f083c8845031385050320381a82500c1508441031f001e90441011001d5140d00040c244058071021078003204d2011520621015602681000c02c030040b50310203080b440c0c3c50082c1d0003001a45c031007040000c44044403c18441d510805c3c8ac83c003d410410800030303030002c9050000781e190020310300e20b400d08404854110303203402c1d644800f80c159270595001542c50b01e8108200103000c1012640d040c004407540c5581c940d040700e01001071a06140c805 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 664690845 1250 664689595 664689629
    0xb0d0311011401150f03090f021513081006090b220f0203010f060206100e0a0903050f1201241d1908030309011527110a030b03070e01030c 61
    0x403080d04540581c00599490042c10b69403040401c0319070f16441900c40200319000500c0b54010721034000c500c9a2500400ba0200e030b10750981c240b0038412810025880907450501400c01c0c03000c1c0d0305168070000c101b50401403280800052400d8220343e03803540402000351134040512485d40f15000b40450409084262600b0b0200c8152188041c04da08405400d04900c00030011800340c114101e02003d603810b80d4200d40840d070f00c410700c0040b01c0c0700a02821984c0001c5c0780000f0140095500f21041252003480c2c010b041682d404064401e07500025a100768030001d24006200f1100c0d6070020340c07234088014100501d516101c2c1000380c1486148206405418103080c5600d0007a1114484080c1003240034481d4801c01d591030300810340725001a11013910075420800700307000c0e41024480b03400583c2c49280485942e00b1401c000d20030414116140300f40420f1300c414050382240b01160240c0095551a1004030f09540090109818400c054000e911186030300da0040c400300381d140c80300c8001d0ba80c1458420009507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 664692095 1250 664690845 664690877
    0x204051f031b05031f0b07080906040509010b18060901140d09020607080d0f0b011d01031d0102040f05090705030105010f020f0a140105060d1e0c08011505090a0b0d03 73
    0x4182c224600d00324141841c480c0942e031090055201d1003040c40450603843c181d40c000d48001314103228012054106114460105500c580105082c1c90010011803800380c0c0c1e0804981010400d90201c5244500072800108600c5484605a1b884034111603062070110a20006000341040f0041c3ca640c0039000f03d0a80e40420103607101983c02c640040099031210b03000c1c942095140d1114041e003c000342490300300340c0e10600d2400307801c00c488016142e404049021110081d550100080c06504141e10307103c0d04e0040301c52a0315142210701440c0000341e626801d2804070440540e00c0c1e4845401141158100200389074818141c9054070424605480d1030304241c54100d141c0030b4240a81203182c090b004002e8104544a66000c03c0a41c1c41c0e002070040d42e60319400c0040301d101c65100504000520704061228054a903801c0f01c80d10312840140e45250380751506582165008260700b000b03000780410900c43d51500d1348402d6440028610103022141d516008100e0b020394000c0b00074148600301100d40040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 664693345 1250 664692095 664692101
    0x140f163006032003070801050603070608040510052418011a0705031314030c0d0305090118030f23030403061112070c230606061e0304050105070e040204051f03 70
    0x116008040c1c8080c8840600d0301d115468103d0030614441e10440400062002040c09114410a00100900308a501d404000e0310f05800062040b21140588400394440a5aa02c103d50140d1038117103010f403080c0039401c00caa24000b22962998819180b161003007518002c1000414151074807034442c070310012503024610140c3d000c1d58000410710302000c60070044d610466105801191280002521a900c00b407082c1030310b0f010b100c00515042180400c40901081c000d500504501c001890034403c0180d650280c1c0d0450580c6030000c0752183c00c1800458103102c6040ba2645008032201c182c0d0319101e0b078250b0200e40d07911943c40004c16446e21144201030601c100c40c291100c0c0078248445c0e80f00d9140c150002064601110310485500710482d5100349c041c032290010030700d1b05075000300400316a03c4e50000c101c900d4110900c203403400c00e00c2a00c0b500e0f10f0746a9001460090384030300d0011449061000015184107245079489002e140f050004004941e1032104100098192619410318040b00c21011405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 664694595 1250 664693345 664693349
    0x80c010b0d0303051014180709080d0c05060c2502010306030212010e0d0f091703071a070e0f09070309060e0319140705061801140f163006 61
    0x12101100000509058164110301d200c0d1761401100c2c800c4c191a50340d8038416640c605c80d940d4000b0310501500c2e803451030181c07101d5000652030130700b600302c2a9030700041480d107030520b9400e40004402a01d0f100030040708001a03500b2080712000c0c981009101c4050303040d8111880c03150340f80005000040029640641e01a4001d3354000d044004941e0074144868040c2c41104c01c0c14009200f5841a4007840b0320413094241c04075065580c6800300c46c5800504528940380d1100a401c60004000400000c1d17800000407481d142087c03001c0025103012071000e07005200801d0542d0085265a180d81d205540f00407104c0d500034800c1c10b000030619141c1c180000202420150602d180c4030008901c80c90030040c1410a84001182c0d8948500780c030700e00404401030181e240c00a14903400003020424003000100740c141c01d800c0313403000000c4229019250988500042d219949450740704000e102200b407412690441070800e509011b1400d2150074032017446490101c089010241d01340b4044200b20405812800c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 664695845 1250 664694595 664694599
    0xe160314130201081e0c070203011d210c03033c0105040b010c020607020105071b030b180114060105090a0e01080102040611071401080406021b25080703080c010b 71
    0x5528644034505618585800000b42e0200d8a09000603140d00c0c59480c006884404400148026440f124642c040c90341140e10101e03415500e038a1640f4107040320400c1e4a9800c113842008040d91503007001640c061151507000700503c00e000b0008440703801ca0010840b5081142182d000010b0180303030308105111a40c003d40c0d00c0550010f0280d044844071040d840700d040e98000c5904000410007407006417140404054000d41005080c02040c02641c005d9002d8a03140303009247c15020120b80642c800240d20054104603070b00750700e1005001c000b80c0810140d0201c90ba400d002001a8070408448241d001d40051029040010005d5100b113140c6680004000070200341c48850082e584814101d4080e4115016480c0040c090010054211350000340000c01c0b5000c141c0440b00e0014200011210047c0061064032655002c011150307004003203909401180c2d4125014042001c0410031880040048002159400c655440709014941c000b081c2041240c0c0d02ca00010f58490180005601428a689000d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 664697095 1250 664695845 664695881
    0x20706151d0601050d1116030e040c1b0201052203050c060c0c100219051e15040b1321031406030c0111150c041a070c12050c090c071b0e1603 62
    0x47d44403041d40500c09000d82c0300c0e1703c0c0ca0141203140340c00d0108451010440700c00086c400b041415901c80c0300420503040074018907002d480c3c000e03440f0f241e1000c0e001e804404600440424005c105125080c440b080035014111042d51500f511b030b48050340d5440d002101948200c410303030540c5010354002c003c1d110b81346c000400946401d02d900d0030140d840c3c1c0741000d01da07140c03284000c03204048000c01080c00003043e070b60100c6c02142600c0f135460750740145038000c103d0041c4003c0b9248003004140c001c010000d80d00101500640e0701c011004000302a60071803403007090700c2c0b0142c1e014810255004110a40e2094007071800b81100c070f0b00000d115282c014000320088120261509121180c100c480041041c0c0f60944c6800c00f8123600d248030b03052a441008005002c144a50005001c28181201541c2520307015600301c404da0f800100000320400e10a40d0310750184000018210200f080d9880c0c00c804da03060f078100e42c04005144c008241a1000000d014070300d404003562000b800a03009074000711103071075542280 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 664698345 1250 664697095 664697107
    0x406031b08060c040b0a0f0c0507030b01080d09050306060d210e0a1e0506090420030a1d10090804030507030b0717071e1101020706151d0601050d11 65
    0x45069450300070800c450140c030000074041030f0a4003c64089800340d00c041840d21040da001241c0e18841805a0805c01540e160302c50017042d010000403002c0e6000d2521b0320615498890716519208046a0308818840c90000c00c1042e590003259441e800078090340c16a034003001c1450141028603c214035100345407040100408603c0d4008840c6040580c2074804103401905c07019581c1d013113482c2e01d058901d0403071549000d011a007003460142c82d00c1c1c1005440841c003040000d2649070b00f84d000513140c3c94084030200c100504603240e809820f4440d00201b10103809070001460301070301d58440e130000907100781c0c507000c2110800041c81c0403180159041400c3d2000940c5a11f4038207103402c070588442c0700290303144411807000081484450300603e069207034113561004c100c61504c07401e00048500c0c1e041c4030344243d0314402c06100380005d22140c2d20904002034000e0704500c500030305000726040424002203004030b0350b40c103242c19450543c11050900303219032070340762503542880034151130b0b04111403414002c00c070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 664699595 1250 664698345 664698383
    0xf0809031615030608061909031103031e010f0b0702040203070c0203030f0306011218020f190603050105190e0a15150804030e03011a210d0c0b0105090105060711040603 74
    0x100880480060340c0c24402542d88042440d030354001950b88000e07840103210b00e0b8641030110740c03216800324481d0a001031807144020ac0c031030442c2c008448100d03005004524804000504d0300405024208041201d045141030a0040c0084d00914074001e014650000104d0055030040485640c000e0307008048940e030702c1c1c4900f103058882d0002d031011404610303014138880704900c29006842c1042e411303044840d150904c5800f0085a500340d0500b15412445011400c9207514035115418042e0040362004201c81d4581401d0140703404040008088150719884c082c4070b1000c0503140c068010b1080c1d14040380d0091181b803042c6590f0900c1e44454024100c04502d0210301e07800260b9030748141d000c0c0d00d40d030844514240501d03099681042103180c482c500f070401100a4640580300c04015440c568000d00c11034a01c82c0c0d4607142c8540070111034085100f00144100300800344070a14090042942c0d00e00c8a5458200864158041c10600402240c400500c901b0140c40310f6000c0d01c010354000d41000f001252100c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 664700845 1250 664699595 664699619
    0x3092a04090c1811030703020d0b0a080f12190804080910030c110708120a02070e040c1505120c1b0a0303051806160309380906040f08090316 62
    0xc6410548075608100d020f0308409449502c4050182c1d12085207541d5890200701c000758010760602e40002d94034110002c440d1503d00400010700240d800030052034141402e132078a803240741071200c12a80b5041000e0683c91508603168503181303005091950150f26035107007241c290b006401040c0e030050740040e861803a85034180c10034030001031551144500078040030041600ca004034000e208950348040210038103514484000d09a0111901c15600142d40780e4105804104040da42965910403503e03051006403180740345034500c0c0c402804d1051820000c0302425000440041c0000ba90007001b090100d001c65040080e40c400401080035070311040c0e907a2070090000d200a5501e014418070101e820540701c00c0c006403030f9002e84084949145040d0603814102e024249414003101e0a07000c9181c00c0e0043c000c410b501500c13264852412600030454403084c0c91102a00a1030441554401c0c010312011070703201520110a1070b080103105a0f5282024082031908038446051240d40d41110300014400c515a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 664702095 1250 664700845 664700849
    0x150308070b10080a03081b0d020c010501081e0712060f1b0f0302090607150e070b12070c08030402040c09081608010609150b0307030917070308060603092a04090c 71
    0x216a6900c8180c8416126903500000d41004021890046c04950080d60403a17005c20591707219807000d0f02e0b20703c040500c40242d0300142012180340c5c0d11400180601c0000303004d0940e24818028007400d403541030310642c80d0303218460710541846d18041e44043c0180401ea0f0000c03010074110b010203112200740040e006241900c0040400e0000d6483d00d400881c03648203000f100c0a5100c02040d860415105440740c125541c00c80600021841d03640e00c2d50350f00c0400c00d104500050441024a9032a00c400c400000c8030100003c0031041000f02c104004030001f0040d80540b50848e07010789002400d840c5600e07040e40c1ca410302e0b400c501001d00c50200260110600300e80100c00790341c02440284111380ea60031034641a1001800001800704003030b5000c0c01190f10007000b455015034180b81c04600b009060315280ca4840003051200b8440e04009070b05000d0507044001700c2c0d0025010344240d4914681a8281c1c0e403140e0510020341d240007106100e80c002e420301c0b24403449481400420400844000c1d240440340d00d2054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 664703345 1250 664702095 664702111
    0x70c2903011e0b030108121b0f03130b09090f18010e0a14070b030417091518010f020318010e1309140106051806031504060c120209060d150308070b 65
    0x781408140883c005007500c0c102e40c001002018100750007803140840b508a43c003118040e00d0f01e245500b000300070401004400d020341d003026550340c503100d4a42d0b20b00401d2503000340702d140c81c3c00c01c0b9400c41915040300c41e56200305140080186038441c070560008e19161032900e115507608105403410900408921420020f1040c02004003c0001105107500c03501141310f409000d08092000401058060846148403c510b80088c6e00d82451800010401c924040440110340c001241c0050040009209c3c00002d51007420300c1ca00b9002e1302100255648500150100300003000e1034040c500764003074141c2e098900070041500c200304955521950042c01942d90949001b4140020b80c1c80002040c4507a00964070302419007d686015200b404007404800344c081ea40507c1401e1190108000801505000300d210b0000441c0d05902140300a090070b800080201c1c001e4030402c0138404039070b1200101e07003003880c8841c40410012040d41c05d50a0002c80359001510001000868008010031190703a240b1902c4c41c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 664704595 1250 664703345 664703399
    0x20d0e06070806330f0c06090703030324090e12030f10060c0506070822030c0303060518150d02060f1306090803030a05061f020c0411070c290301 64
    0x1110719101c09034028001c00c400f201da1405071080041610790010001700868080d100d180c000d00c00002480c0140888104a01e0b40205400b4800c140d454003078081c02581f54144401c28989280d01e6015881c0c29110700e044182da203100c80c1c00a9070003402005002001c240702035440345488280f400c640d400840c2d65209108074010042602030043d40810015a080b10003001103554060b820350701d40a01610380c0242d21102c01c4032415842c100400304903250f2290b81c0303072449044d40d4039010302501c2d01074002503c5071110303006c0e84140b003007000b5800d6404089030b40c420600e122518040b581c00110400040c2d0051000128642c01003c100020046070f10304010018070559114000c4800c00340d603004d94612604100007042004005030003c0d40c120000400401c514000c540402d000b4001469070500540c200030800150786c40c03e40704200942c640c05d0801840d024281e41c0b04040ca18243c001c03071b48103120180d40c08007100c1d1440c510003141c2110407101d076070b03075611209400341401c0300c040d400c0700f050720b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 664705845 1250 664704595 664704619
    0x6041104060e0103030f021e15070e030c010c0c080106120c1d1f080f1608070f06050309010b1e04231b0708030703050712060602030d020d0e06070806 66
    0x9081c03040c081200c0c20002c144501e0f9081d50790840321084c2241d5407000b1446107021141c4102544503d00e40069640c4004003550311280748402c00e4200010240c07400c4c00800c074050800f9407804a1040b0011409182c4181c1c0940303245481d81104409030000c03c0c0c558a48000402c8100c0e01004014403070b40a10f5148400da1341d1403c414040c5c510503184030488130285800b00d0380400c0700b072414081410103c11030180047e2126680d034540081401d0702c440741c5e400f181110f852000d090601da005400440b000d0040d00307040101e080c4920803248604401c2050010000714401070a5108080e089801021055440350111070112610300b80743d0028411480e003003030501a0309040000711034481c80410740c1c8a40c0d54030100c10401e40403030703480c0c65801120108505000550100b00461042085450016032414030380c0006001d001608541030381a49800028005960008140c41c4070301c4a0040250384d4400c0440303504003410803429003d040d840740109025a1a07003000c03666110700b009a500f05d48640e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 664707095 1250 664705845 664705849
    0xe0d080403020f0a050c090408370c0f0308071e05120705030f01050907110a0b090105010e010b120703020c03070525230315070323010b0313060f020408060411 70
    0x50584d5100a1103907100044140150509130182c941c03240c0175591113410308100010a290041842c0d2600c00140c0084420881482c01095202d080705407501d00701400100941d10900074603001c0b0005001d01c40e54100168080c5e100b05641d0801e100440c807000e440090828002e040c0e900700110301410541c8960014058520800030b070380c4200010030808038142d20308424001c00040281c800020018501c1d40c55642e48005c00600003202c2c03203024000503620301208078608546041e0806440a481c0000421039460042c00303503041c10010540f04541c50310350741d005500074420580c24040300d00001c2007010500038081020151243d1641c2d220082e100008510070041140d8050003a05c03a82d1940400200703080103030f1111404001808032682c2143c4141c820398004e000b21040b100180d01e8204082a1008030101760705803030310b4010121f9143d41012040544e900008003003a00110b00141d21000340320007500410502c58074003104640d10f64070751714034648460048a09032044619a00144424 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 664708345 1250 664707095 664707103
    0x1d0402040f08070f1d0a0f020c01060b04050301050a0b0310052d070f0302031909110a0b0301080c0f0108010302040b1809030a030510051c031101050709050f30010e0d080403020f 78
    0xd2201505c0c0c404181d0f407403615000c0104440061194aa0703404d10103082e184401340303d0300c13001e04007000d0415210781c0707410101820b6400c010030070319000d4100f41c0100f46d40d48000507a0310320304c100420041a10b9030380c60002804960740300f0715000450f541d01c0580c030001c09800c1110380154003643d54189042c2c400d48040d0242e1103381d441030909150003001001e141015440703030400e14800d200301191311800c240024000052600800505480080104003042d000c004100000340103880c0d450810b041c3c80000382c403d420511000e4082c42e103c03090100540c0d0f40c030054619891144450700054140700d01150303900d400c06408000400d1034480401c5014140a140d2401c5410040010410346048940c4d1400150301c10011010b00107080480742c900c01080c0030780c074851104d555403034210b6071a1404021888810540c6640110111180301902200d1000341c1d100040f03a2846103c00d1180c2c0000b01c03070040807042c4c03000309107004545c90703002026844104c0700d00035030003503084a8070702c9195000b440d12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 664709595 1250 664708345 664708379
    0x3120b010305090613060f06080304050108370912020601080d0c0507062012030a0506010c020a14010e0904110307081222090c02012702011d0402040f08070f 69
    0x1241c0c803c5000491032210305e03201c504d1181c840d80000c5001d14403c07017100c0070b580543c4c0280380b0f10340000c1424403065a00c0000342d03a110005440d6640300401100c680c4100c49868460075031a500000d29802e11503241e6006803140d1944042841510400c07813000035290302081c01900c581d40a002c03844d55200c8c2c410752110051580140242800e50b2410006a0302d85070b1803226000c0b84440c642020007201e105122608110f41c1440b074aa542e80303842da2091041720002803c0c681848030a84900000d03032100042c0d801900d00881d1990a543c0b28000140c5408201c03045c40303a44000c1704c004000030041c9501036407184d003800740e0494254580b00d11550b80c07a480207d5112040c0d075428406420654003549043d1151481c3c0200e06c119031340c9590441701a6084100d0510141c1c0d11900c1c061403191111042c403400955250701108030451542c002041908880c60b42032070407090740c52404072551a541118020100900c41c0029181d540810729152000e6205000f05a158000c001039a280c103006200a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 664710845 1250 664709595 664709611
    0x40b0a05130506030124030c05011e1101060f0b040812030405030a0e0a05040608011b0f0207050d02041103090a060e0c011407140f070f0503010606050301062a03120b010305 76
    0x605aa940000000078140280f80e103038159201c030490b072048040300300019800700c4946d100d42009411410b11010003070303942c0e01c060304020070031101c0c14070402681840d030601d61081c80c0280c5044201044103024080a8010000ca0a01e000000a510311040010000c0740d6100091322501000c00302c040c0681d010485d00500207400030005154503a108002225000000800410a094581d00418200c40036504146500ea541e10740102100200300e18164a51009141c1030611a0100b40001d4461000f40b207040e00521075502100d0440d0b440c0d4100c40c1108880281c060b40381d151124440d03648180d81e0000381c03001850140c071302940d8a004900e00a1070300c8182c680c025901084007500950741c0c4204000e0f2034600c10524450004501480000782500c000f00c001c0070580e040ca140f000d401c0d4110340c05148283e2400d241040216080420749044400a040010110030190381d621800d11110300d4802d00c1403120320312502015000500a82c80e401300c0340c1c00300480c81100006404580342036079840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 664712095 1250 664710845 664710859
    0x2103010506030a090f0f1a040201140a02010f181703010e0f0a09060912090914010621060b0304031b0b160c020306100501020105091c0c14030d060302040b0a05 70
    0xc440e038204100250f40140e4400d40014040320a9124404103d9003a003013141d10b4903101300360384c042c03061041c001c140d250610f100366085424103500280c103c0500001ca982e01c0d1401180c6095110300030750009e0400444090103010006800e0f41c40c0e09001130320b200450354a01a441105010200441034030705807000d40c0015803040c2c071101284c04030180c1c01000a0720068640c01100c0008259014500846100d000c3d08600703103000a0020b80041e02e03036040b0b850424900800b81100071100d02c540c45c1140e0b040d090418900c04040810615215400d0040258605007000041d11540c00f400035480365001355101c10f00314140000281d031300320305550003800b055200c40200e8a000c0e003c0440b00c1031110103040a02894140380c2c0840c0c2000e000300c3e04107042d803c4040040155580a0040a0748109003001030b00000800380001070100951001000c00c1260b0480e00030100140c0341d14400e03c0c11980d02c2103d0b203681d4900c019002070132443c001240164100108c011181c24051458015104000c00c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 664713345 1250 664712095 664712099
    0x30807020402032d091209030c0409111e03010f0b181f0305012316050702060f03011403150c0d051302100503070801060c0308010510020f100e210301 66
    0x10019403c00344c4107280c404c2ca8408103610b5409440c2c00f08805000c40000c9030080c0c0b034002c0f0410304101111380c1c1406d00384d4003005030100a9070081104c0c00b0a0404441c0000c04200b207007042c0c0d881144901020303401034160350300034a624003000360340c001c1104210700034030400d42c12000041c19203441a00043e0811003c8101d1480c00c8412000c4603440340359501400c07440e400b4802c0080d003160b0179500c10346041c0d560314280380030350504c500714801c0042603501c100d01506101080480d0000e0318281c0303100b005008503400c011036582c6402c0b80e180705c1c8480d40b00ca48a58491842041c032a0550042c280f1034458002d04082030742c491040184111114418581440c160b0300d10302000d458003c1140c51941c42c11403200c070059480400c8505480c2d146d0707440d01d84a02e401c22029081140603040340c030500100410400000b070b480340450781520b00540e032603c640b02d4610010703813406070020081841d40c061420340d200540d59079842400d0047c0d02d00d0858840d48444c134004104024605094880b000d410001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 664714595 1250 664713345 664713349
    0x60307030c21170c0705090112030f0513030605070807020a0309061101020c06010308071a1b0a0e030a110406170a11150f03010914070e01082e1e03080702 68
    0x12280c0207a10303400010704000d80b6503454030b00c1c01d0495120910038400104208020781c408000450281000340c40149455040103c1031021240c8203000800f0894444241001d042c440c40c26214030310610801c5980d078580b00d1600c1000b802046601c1c0c000900280b0004100c2d40c8000b96400030290103032242c0709814109230302294441e880034107080740703503408005aa075548d0013003240700c1c0211f0051009585454040c0f07031000750000c009115410b100900e2091004601c48034151a43d0445002e540300c2e55240c2004d42035a0450b00d020055a05000d540324050502c43c80c0c002e03051140c5411901003040d2511056501c080400b517090100207a40070800401c0040d00c40d400110114400910001044031140d8000391583e00946041061020120042100e1400ca015240114689070341d4050107142208006169022155805040003005400b0500351074158140c440b401071202c0d0a1b65941800d414217a115115030b201740500510113001d4950305907800140c54045e281d12071200c1e442d1040b1502 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 664715845 1250 664714595 664714619
    0x3050916060e1503090f0f160b070f0b0403020d1103070c051c2103110702030613060b0303040e160e06030115030b06040801140f0717090c0d1406060307030c 69
    0x4290001c403907143d030700450b00140015522912081d00108002d10185129a052851400f0b0340c210030f51006c041c4800e41c4c88881c0895040d03508103800c054984c02e80d4103029124400010010780448107100c02c8c0300034554003207284080101d01c1d84542942401d01c0f62030030b90f41d110704040945150814030b0140268035000f940100c1c417a010248001c0488815141c120040740174440884950000c5005841c50740d8150280710300c200c907072805042c244041a0046610f40400501c08510022280545400c010480e445501c0d074103c0a4100c03074440780c840140d00304400e0244c65280500c40032a03d2003000070703c00c0148040c0100301504071811a481d022a030f40485e812040760000f4161184d080c100291190000303400189000800811a00902000380c0380c241000350540304805a00400c100c0c00d150041985080f00300064020b40c0103990310081d50707062440c45003280343d004a90900c0c0790140702044030f460765100141c02c185c0300700f52124010107585404c584401411070210100c200701c00141e42e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 664717095 1250 664715845 664715867
    0x50601023c0a1b1508040b13050709051e06040501080a0212010212130209070e0a0612060f0b0418180204090204180503031909050c090606120c0a0305091606 69
    0x12048808848950f5184990315660140601c1000d40164080003a110824a40c580060060400034090300302034441940340f00000b490500701a400002d0314003089410400300c002464404d00410050601c9075852021a40107080d01852400700d0001c5995850036209460480364860010503c4194035424485605103200c00e174400d655080c4a1041c07407010003e841d51003400b05001019120040d407041100c0b1f4034000e4100c400b00139110b585154192902d02c1c0d2501540c0d040d051a0b00a107080d1405040a4941c0e9000040b184c000c580000590802da00c01070300c03e4900e0b0070786050440184410007000c944051200191002400307141101506140e03200b00c2da00c07400500003007002c03082c1c0e034040020350b00041001c4809500c00003c10240b1481011020a180b450755028042d404050f11400e94401018203840e00c601101e10119455075924401c543c2e03c41069082d4455510340501c0000013504450310201c0400d00301400910b0360740e0042039010035030040c0120454200d0130044126065122a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 664718345 1250 664717095 664717213
    0x108160b09012a05010903030c020105090a020f060418060611031306050d11180109090e100f0b0907090504050f0c160c0b0f030a06060f02060c0c0c060c0105060102 72
    0x2a01e14191031010320000581c0343d40a0b20020840c507800346401421034100f4216075045915190900285020201d02c00320b41603011114403410608001c0001e24030320440e40301d480f84811342d4920225070f0200c1d401070404c03a0120384640d003961f03071412583c0381c50f8418203522003141250400c0510099029002410340307052182d000040344e030311614218200340d00001181111b0381240446100c1580c0c0403000c900608840c0100b407295092400c9607969600c101442405450346908050030300500c1513114a04030000101140d00a003403019010f4500180713030080b40e01072400c1c140001c041410520000c0e0041c0b0300d518601349002c1c03022178000d14500243e60110f82d5940854000186003c0c80b0000d409040c400100c61b540d01c0c20a42311081c11120103034016410f02c03400200701c2c00c400e500800c40315400700034034508942c0e64070f0b2079910328100080e2000d044c0e440311700402d00301d40e0010150300151040c2000e80031603120b11207510100031207071401c0030909007802c2c0d4500090700200d8030342d0f0588404801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 664719595 1250 664718345 664718387
    0xb130903031b170118020909012601020c0a0b0910060b030f070e0d15110301090b0a090e1203130512041401030615050f0d0203040524160c0201020c030607080108160b0901 75
    0x20740e03000200c6549007a800079a1aa030008100070b000840c4080401c4c07904002c0000f1072a10400b40c03400b6403146d44ec00b0303000c0e0480c03084070005030800030180000c1d0282040003008202454650440790002e800584900740302690850003d0200742c041c001101c0301d42030003440b041b000348055aa8044032851401c860140544560b084c0000340000400345019005004004c00c4038a41030091000064180e0b001c1e00c1c010f0701380144800d51580c0401c25003c2513050038001d41d070380d559051484129840c0d50000500c10310600105244969024004e0000c1d15001c2c1c0304040400405001141a1200c0d4041c242d00d1040b08081c4405c010300a10003030a46603550420281400107500306041243c00403a02610540c11513098600c1d4441c01042000c16211002802d240c28100340850382c0c00015414590801c0c4441c501d0305009680c001c00c1840b011820003002c90b103051500b808010242c0c3d40a00c581c1e412446014008034019841141c004180c5031401022814542c039200111190500e240ca019201c0c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 664720845 1250 664719595 664719607
    0x30f0206070801081504230105150a050604090b031c0503040c05011827050c0901020d05070f0206070c090906060303030e0c18061f031b1707030b130903031b17011802 73
    0xe08015401d6a4241f480000a4186003130010400c3c0108203443d928414096030806020b02c0e542c0105580c1600c040fa86d001a22259410100b0315050301481d0320b400340300381002140700c0d09510070011481503100d9107c403003d55580310010742d45442c4a014000010b0210402130180c90a9078001c00d0f110101c03191103c03c8540300708002030884100341d90b81c85007454000303400c0e240340d42c04100c50080055145421480c1621584603100f5420030020024802c007000504103061204128155015181c0c040c41000b4001a51810300001d109a00c0100c0201341442001d032042c01c404508808204000b9100210804107c2c1c091003070f1070300040c20150b00184418075624070030084245103480341100d0301c0010b00ca400c802c8030341d076034828440a05020001504c00802c80300c0307403504042d40c20818509002c03c0c01c0030f4020010b44900300c00000020814a0030001c4000d040e456040006101486006080d0300303031410341d08807005a004050541c03042098001040b210280440008050001d0000181401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 664722095 1250 664720845 664720883
    0xc14030d0c020709050c03010f1703120a09020310020306030a060b0301090813060e040b0a0b1e0315010909020304020603160504081203090c0a29090409030f0206070801081504 77
    0x5016541e0041c01039100e020248650011803140b59004891000958159807406042c0c032030414a9000340c10551988050300403111a007002554150510100e10001914099030000e009084084d400e910034070407090203032000840c0d442280c1c080e11000c0e02401100d1025210b0700c002c0d1500c0001160590350b5000380402007220f0002900070b041d08040d00c0d107042403030b1510051004100083c0c0d03030301c550300e0111940c0c210b0750f8080c00340c0100ca91040e540c07034446203966003642804140c0607142c259a08000101704000c080c4c8424141003250980f0f40040d0300f070304c40310710008900049070002c0d0002c1c4c0c200042280038581caa000d45161240d0700d00140b42c1521002170034100822101a440103603404002c0c001141403e024580411105440018110307140c09588085900310104c0d03504824100030203c11181e0343e8a0441e100c100000e0800c0c012020325140082510b030385000460014007902004c40c010511900f8054100c0e14024020800b84e031141c890300c1d003000000341c02190b540c000e03901030240f40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 664723345 1250 664722095 664722101
    0x15110a05010c081e070c02040e03120103030f09090218060714030d020a0905310f0e1c080c0405100e030a0c15020106240309150504030e0d030c14030d 66
    0x48440d0b58103e203900f810100d8841d030414100c076110845042800300824103601060306401c0640444000c1044482c01901030300f107100d0105216109070f180000031041c186c2011490f041160a60703658031480b070ba02c2a03190100d0080706100c901c820503100441d80c003840c1001c094016180980c0b08c5040d1406802d60450be50340c8000320160000c0d40100e0710211241d000143c1c040204030544802040e00244505241a240617130f02440c00d0268165503030114080c44e80c0440e0265807041000c10400d5200307c21581d0781d0240d40e684600c031680c480c80d014255449544000d02070b0318606a034038102801d003420401058075910000003000300000c2c000043d03942c01c02051005a00600c42d50011358240786410041000400410040d03a0610608020002d0042c440c01c425881000700c580e009802507004801a1160380c401820b0100b41d0440c1040103243d076840180220320036254202c0071000a400e000d80f604100801601048202c402c42011901580100c0450814001602c0c0b5142e11745140c8022 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 664724595 1250 664723345 664723361
    0x20f04030f031b0c1a0315040f180b0415020f0403120e04060e040605090d0e0d050a120f080907030f060f0f0e0a03080c1219291915110a0501 62
    0x2c4180118020000310340004000080302d84075211880c5185001040c0e8501d0307080072450302e4015580c0300049c00540c4041e600600e001045242c5810244501e4144140f05500a4030300382c60f00b00c541e1000798030a00940c42128002001440e80d14100707803840d126090584a482c00d420103215481c10f544400e60380da4800c0002a0001a0341986941040d04080d001c0750310080141c2c030039500c1041061062504003c2d0b200705840c0c08c8a003249092030782d14216040981704c54008040c41e842d10495000c00740c1083c1c0400c4180e076541d54002c078660b40d131001503540f00c0091101416000c520015440030030004c0e0031488544030115004515108107849200c00c54038040c10b0584a03420403100101019408040560003400095809081082400c50055280c50182054a000d01014403007803100b0b1580e041901404420102c45440c40b001d84d030844500c5440c4d00116201d010f180d2040440d0846d0000c8210a5805581d0804450711110100369030100120a079102603120f440341c900e0001d003090045c81d034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 664725845 1250 664724595 664724603
    0x7120506011502121c1e0b0a0501080a020705010b060a110d0c03050403030305060d1a0a0b011d0603280615020114011a0403050601090b12030a0c1e1e02090901020f04030f031b 77
    0x1c51144121b44420403191400a20f501c5540c4ca01d60412150380e00000d09900088180030044c0e481100b8600f050043c03441a15160300500003040b06040140c2101c98644400305c1401582c1c00140c0540b021507088241c5e20700200171440501c41440400d01c2a40455030105000d01445282c641c6601c0c0d16103c22100f00680f007086084a003002100c81907805410482c440c01c0c24041c0502d040c40c00050403855081c01d0380ba00490300800085d01d4030303078211044846040030071803035403100e2402001040a85100d001d00c50000c2c400250706901c540c8144264504030000a40421880e420b20528900d07492640010a50482040c0000300c041401842214000c1c01ca00c4070003e00034544905000c140d42883c100c0a4060700309122040c4d6203604202200f0020b0307441007034184401c1c0c1021813a1341c5082c48940c0601501c111640c00010300d8040346886a00900071180302c00140d640c0b5400314240c1c400c2400310b495800e0180010400140042e501001c1e8500c642054501c2000c510f003903c20b92851404151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 664727095 1250 664725845 664725881
    0x20304030506040308280531080d0b0604080a0b070c0503090f0609130b1f0912020a030602120912180906041103070804060b03070303050a081003020307120506011502121c 75
    0x2000428401988150b507230405003141d0030202503118844440340030300d028102000000d2041820740955220288492006180c581c1740d68450040f50b503904003950080f104030741d00c480443c401c1400350510781c4003507034000015481c1c88440e80178407180c000345c0789041350070540501489140340e64411520580007044180003d000d1a030900b04400c080b032003142c21100d001682c040403065a4001c060800392050304c0c10038035280341c25202040341c05d01254070240603548085405100c0700400542036004010090489060803903000c0525040c3c03155070010034a0010135540194075045c9220f4142c0d200034010400a070f14401c1034160041030340200c03a507400107141c0e00200000c21141e4840c5140d841001e40050045e141150b030017810600c54806944144141c030b000003511481280c45a4000e0341e80a4180d44d04196070322b080024031000600222424003480d400030a05001102545000b03040950080c0703400301824064824a81c4101c0e00c01d07180380c1c0d180e140300300d8011a501403403009421500c900707 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 664728345 1250 664727095 664727101
    0x60402090a05090723031e09032502011808060114060d0905011409010c0801050409061b020102040512150406020304020a08060c0a14090a03031b0b010b07060c0203040305060403082805 81
    0x200024003d40b910030000c40140203100c102c030613204240c01c410301400000c40c048d854000d80ca900e90701403281e000c0451084801c0c6008002040000d130581d0030b1003130302d45804220707201d1a904000302d101d0182e04125800302c4010000303070b103061070300315504000030706098502203105040c44141c900fa01010baa25a4582c2c8107115820b1440000303035031040b2004002c000342041ca000041c8030b440e0612032680304907110700314a01402515480b5000e480103110f691800c000c070000c400f0b0302030340140c07103018444e46e07407400e5401100e13401081202c2000c3c0e00300c0004009a40d607a6071840290000780c0b080e60400c0d0038400118214004008041c014601e02c107d0315101ea000d40c0004110484215080d10b086109020500850300ca02026900f501e0b410308001c0004503d224a840890803460b00141141c031010000107103002260f402800c2c03060080c8410700c000124010300f40c0e039078800c512008202e54446000540401c0c80384040d59001022000001100414000070181c0700d9681e480c4a200d00355141c0078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 664729595 1250 664728345 664728377
    0x19120b0d0f0203071a0a030b12030309060109050601051c09080705070b040801050717191b1d01090503030307110705040207030e030c030d050703230403120201060806040209060402090a050907 84
    0x8644c0145100410141d0b50403e04e00644000c0c041d83c6c0f00c070418940c4406000e0103581d1901c0344400c41111443c1165101e00c0d060000315903c0400f0711504c6489480e1001087d103a5214000b202c40710300010480103182e0094000403c010720000c0300c155020341e0b060100000155050122000404c1595802c40c0c88038107140504e402c5a074080c003050144400c000a034410800e01030801c0b9880945640001112481071084501404440c000a0300e104150182d101d20503820000d0040003006070440c010aa11203e001034886510070300074a40c2c960310520008480078400c00c01c114081c5112025160196034075808142607801892040340442c500101c3c1800e5030404201000c00782904a00612040f41003130740180a0f4490004085d04210800d0700440ba1818030030443d0051a0b0317204807141d51180d0741d0809446241c841c200560065003440303400a5070440c006201400359400900c401c0355620780c8400c02c13001b5408694a80d07080641d000c400103059540c0044c052040c141074036145034605c3c3c4408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 664730845 1250 664729595 664729603
    0x103030e0a05130507120204060f181a0a0302070618022e120605310c0f0e0418031d060c0307020d03140301090c0f0519120b0d0f0203 59
    0x204207004407810a401c1000303950b16a0000010740c10f241c0000303110349451000f19014291034101011060001400050007a40180c1103070398541641c0c1c43d280300740c00d011110381403000f4038407541c2501c1083c0c2c0c203907a400081c84402404501f209007401440c01d521542c40300252102d000d001d0200300a8024484254101551031140d0604140066400b1201e0004c000c405407107289440b0b41045840001c5884801040e0f00c240c5c00340800a00340404011401e95035912103121078401074040188960154624641e07014a640c0da034100e0b01e41c41c042c400802002c80700c101c4840703d400d80c4980c6410118503014200094088514043c0c0c9e241101164442c1291411013180d4684074041c01c8104101c14a8000c0841942d500075412100340c16042801c2c10b0840d90702c25250a116500b50000000181318440703640030414101258507454808105d070b42080d200c80c05940c1075038245140c0002441c810512800d466501181e55030000030300550b810f80811010041c10a080b6201d501480c211405e51038200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 664732095 1250 664730845 664730867
    0x7090b010905040e151e010e0a0b09010312180b12010512070e010521030c01230708040312110a031a04050709091505120c010e060c120d020d1103010303 67
    0xd20180861200002c0c659a07681c0c40d542e59680000c684000300700c0f10b0001b001c0402074441101600305032035854400b0f40031444400c1d1825402d0b0ba15021401a4500700010301d43d040700d401690400c100e408002e0b041d1803041c0f80c0700e51042d81f000c0b50940401c20300c00190281c010340300c1c2c04500710391960400051102002400c441503250381d100c1c0100700300482c42c0c2d03400641940d034140d41b0600004a82a45d0201c3e25501450030055404003060a6000c680c0551042d03521907030014410103e800908200e9007030302c20039070b00d03400003801c50000900842d00403817000b40178901d105400074058042d03640903c0c0c10741080c14000000383d10390b017140f01e60404015a884611f102103a0400540c1403246002e004001da0384681004191103182d00700645a650740300300d00404002e0038012240100310b00b056285c011580300030380459294100700703175142480c4042d0b81400c0f51000007840c12a00b1900e024034240c00100004035000d0b001c104013200320195004814004109a18454980d411442c024141c04440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 664733345 1250 664732095 664732099
    0x3020c040218280602060a050109140a02090f04050c0d0e0111071e1b1e050622171501090b0a0b030613051f0b0906030a05060d0507090b010905 63
    0x1406102207942482602c42d00c80e8000311003103401e030708100caa100c94011240e1070300b2441c0f0703101020000d0000c2d00481c00c3d91081000400c00c000903a200c0c1c103240e080724140121200303c4034503d40001d0381444560300400b55100b006001040001030280040c0c15240c0455200c120060003041015200f409070040d42055400b50b4024010110129490071043c00350b5080504449886512801c000c581044a003955540090b0f03903500d1841802c5c1c0081d10a505032103040c41040b480700b541d19490414542c010f040e640300400b440e140c030652015601d540c0c11054443c202c0c40c422041c00280c41000d00034010000e20186000e41104460340d03800c840c010b0300585c081d004541c10b0440541280c2c0d80c0f120400140c0c1c04118003103440b0384404011079041e11a01c03010b900740b14a02014044400ca04000c031610100200e064405100d4940a5045181c011005400d4000e00f0900118070100010340010b503100700044c242c01e010342083c2d120a443c0002c035500a0030390650b80c645450003944d00c2414080a4442 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 664734595 1250 664733345 664733347
    0x90b0306041a100b0d05190b15030612100e150714030c04050301020a090807060c0308010302060c0c090411040615023708030f060d020a09020702011803030c03020c0402 74
    0x7615402d4011007094505601e00c288500010150641c18403a03002900712003034069250015401c42c03400402c0306450300204010840c1d41d008414405004504195902800b08800146e408003418001d420117000e01d40d002c0409038490a07d04002c01032500e24203030031080490180041d0018030705190345006500e050305a10400c010040d80c0100800c9491100504040e951b59660a80c2d9286401143c010aa055000280c60a541513001505409a41070041035074070380b540e501c41c02d43e905250b00b0b01c0140410441d00c010005858854098489901100c0c00e0701c228480700000210041c10841d802c440c100510040303001241814451300340901040319081c18100c50002c0042d60b00d1240443c0503440c0181d071901d689100c0701c048078490315420101080280c0e0700c50387c0751006642d0402c03540501560013140004900b032824040445007540c0242400c81c9485c20700104202a500c040c400343c0c1406040d014581208411502500043d4003d0b035a0390014051403030000e05141072252002d01c0b580c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 664735845 1250 664734595 664734601
    0x4060801051b0310260f03090d08090a08060709030c060203070305071217010609033503040f0c15080a1119090302060d0203090616020a1707021207090b0306 69
    0x114041e10010b04200111855141d5642061942845680340c03c4015190525030710203605903085950000c60071000710039214842000340240b03035a0700603050410b5000b000f0f02402404151175100074083e00002404a103071058440510901e450340503181000003c0149104005005107100400090000351003e18504001c540b00103140c2c0c0100c4001600d9903c841c100d10300035034059070604040c40840039130650107694601c0042c24641e80780c4000d540c1c0124008407041c64416034540380d40c4501413083d00703600800d8140311080040e04001d008640110f15000c0020201e4600850f4000a051101000c000f030407540b20002c1035000c001d89803280860802c0d1041080082d61016280c1d11071005100d514409107a080448000d01168406900100001100790841005070002d40c4511400b4049501584401040c150b8000642d0302e400010303040806808000b6000181b07500034143c03148030329410058181c0003e50151210b0030034603142da06c2079108014204041c040c80c1e60042046025003024a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 664737095 1250 664735845 664735861
    0x9060309150b040b09180106090506060426030c0d090902161103030904180c060824010c050114041205120f040203011d011a0607210504230406080105 66
    0x148088140c0e981c6031201d807603081c1070701c440d8060240c421004104a091b424900c41a50700078101601d450055401c00b940070035044018001d99000700b00c06011949080d1603c13120b00381c54820001c152100c01c04035915646008c00070800381c161065020003808441451400140290b40e0035440b1161050040c040911144400707162110010b0b04400b14060820b401c0000a0861140c00c030388a502610b003080d0440c2e2381010f6035030300392002e100d9000c0181c400e440b501c090740c0001c1d0440f0704440395400607540781401e200043d130120302c1d903506051001e6504410b40d103c90a40d490001e0f1102c141c00340341c080005201c0b20104c2c10004628909090740f4001500d01c01c1c1822940041c00101003061803000b0030f0454a00354000015040c0d000c108803100000c0b690420701810042e808003a5000c0140302c19003440c5030040c03ca4840c1503005058207540168040c04e0401d26131009544010312800b808000740400c0341264540922684000300c0054062010410088a185411082e01e6a16003070400000e2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 664738345 1250 664737095 664737113
    0x1092f1b15061f050d0c0203090301090b09280807050c0907110d09080c040b06120f04050c030111091c05010c03061a070b0c0f130303090501021005040201140904060f0b090109060309 80
    0x103000108400711b140b941c8840280c3c41d5201d0302049940540c40c00756000c045c090050201c5002e5411a41940c500501d02140b05501e44d81c0c1003c1c149a02c0060425140051480707001407501c10300c00c0c000d6615001494001840c0b04608644e840081600142c07540058003051150700c00110881c00d101e40b0681c01d110030113507160103e241d01030056030307120455502c50384c0d03180c203503880352030281c12115492130711752040501e980c42650119a41c0c424124013000c1441c040c000d2040150f00078601c14100300d000c50030007410185c0c20007070480520306100c1d141c001c20001c1c018400e07203a416407008103060381b03010341300c00110041c0840300012802c18082d07440041c1078141005e4000c540450126220030481c001607140344508000e8000c9485406400030805801441d4441100d40980994084e030300c102040500b903c00440f00280043c018000510303070410074070041d001109004c3c000040c00c90311040c02d0417010046402001480c100407800b01480c8d80d0103610b48014204070b103030600103100580d64402e68 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 664739595 1250 664738345 664738357
    0x1302180f0c0f0904020705030705060109053c0a15170a06051015090302040b0f130c030b040f15050d0b07030207020607150501092f1b15061f05 63
    0x2006001030009000c00000d0140d584643c401003046503900411b00d40030344d0b264020b03c800c07500ca020f99800020805460301c5000d00c6842901a920403120344801d000e1b640c20402080c81200307a00840d00780400d2584011303071520a40881000064072070b40025a540c40e02c646600034a00e04031034440048401300c000c100540c00e00d5200c040071074203071030700d5400c01503001843d009518101101c4600d660840e901170b20340404c0741c0c000c3d82c080007025010000e100205000c03014498000c0942e040b00c01d01c1041036444070700b00b9a50351074000f41403080800081e040c3c5044400f01810240c86a0000030100c0c80c00d82ca40f00140b100f100c03680a21445680d030000610f800410101c28180d001c1088000c2d521030f070782202c8003203502c078140c0d280d0445184d0070749004050078014080121700d4208a10b40c440e03804003101400314514130300004581140070180c2141e038000d501125000e07194044040b10620100585402c801c0e82c0d1048070303003904d070180911424490000c0c01004241d4501840300540e034201c01181c40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 664740845 1250 664739595 664739611
    0xf010e0c0405030a140703020d05030d1b1e0323061002010519090f0804170f120d050a0b0d05060f0705180f01020703230c03161e09051302180f 63
    0x280c507901c17102040d081264a44c800794100c05c80c0d20b0b108040100100c024110078078a60380410800b016442ca420010b441c0142c80c20106a0401070040e040703252400100c200c041502c1d0110700c0c11244408500f40034a0711045e5070107800070a0030f001580c980104540140042440204040d150040c05a01c0d014640400c00402c030359aa0344000a200050000b0261290400c00c0c3c0d650301c0340d45002024000c8222003891107980192044103010860200f01b60b02000202c802d802e0800000d0102d03000202000b03070141c204190388480200041e201c020a03016850300481c0a0003c500c0d0007a090b0420140080003001048410413070003464001001011074103041c2941e198101070540c0340145d00c3d02c5810340020704040c1c01410b000c0d1003003545042a466428100c2c4c1911400b004803030616a0310340300b12000f00c421001f402424042c07141307100795103600020001c00392400d8561f03031106442203800540313104002d41d261140b582c00f5810040890359004194950030503003480c02078191a0a11009010a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 664742095 1250 664740845 664740863
    0x81b060f09130e0d050c060609101511070605071203020906070303050604240807050607051c0203070804060906090e10030209060325090c050c100207020604030b0f010e0c0405030a 79
    0xc10b000d50554402418a100041203030114028001c010b4515000500710891074410880001c80703d007454006103004401c0401250441070401000d80342c144014043d0030300b041078080b00c250035842c040140e00300402c00303502c031070740d0320309040c2458000c85c003044504c2401d041c010440251281c4840c4201c500c81501031500184603126480010046c0c4102c1100851641d62200507110034017080c10000c007218907650032106034980e11400d000b8a4050000041c00d10703041015002c0f051190800c80003c450510700c143d91501a540e0b4031403055410030342080700021140c0708240f0140d500700e0020703405080d01d000f485190707180a035030049119116000c000e02a422560100e603941c1c0701007041d03841c1d901030600c81d41c030100403156920401cad00c9503125038500141002c8005468030b0080e021100b000e8a024040c10003031546044400c00b03540003c4040ba0051030030403000000c20f0281c0c20ba94000e810103000d5180b2540f400701046c1082e0000f50241ca4100c000304000c006607035000842c1440c080c0c0c000074030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 664743345 1250 664742095 664742119
    0x60603061e0403170f01140d050a060914030307030609050c121506040b041d0601080912130b030a020c010608031602010809030408030a0c0b07090537081b060f09 71
    0x129120780440283c1c24010340200140030009000d950601d040e60f400c7c0030011100440c0c0010040d00820500c0d024119030802941d410100391140c11229025001d11031643d5021503020b207484c9513510841e0342c0d40000e079441d04188220315050060503000341003400c5040c00e150582c84105807809003e0240c65051804e08100b0b036071501d8010680e4000c0c004980001d842e140e580000102c80c03107024100c40660034038040020200c1d801807407024003500310100142040561407071559020b5005000102ca03150161000041c40100340e00150b110b005107410150301c500d01491441d0a507503040d0803801d6a500184503104610301171034011008190240b81819a5171509080e441c190701c52600101c003103000001e518000340d6004030000144903c5442c0c403441da5581c104080f02c0c0305000c1c2c022142c0c014100c038503003401980b5540080c91400310b100d58060b41142c08504600b0707540300f10342c011001a00003004007481c550101010061a2405036a62864591f482614100a115160005100310008819 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 664744595 1250 664743345 664743347
    0x22030503070f030f1d070b0f0702090415061212020708060a020a0c0503030c09120706021c0e2112122a1305100203180f0420040602060603061e0403 65
    0x8408814061300c100501203050700a001ca01520043c000a00c2c42800b40000d50381011408481e043d200a15249003803050b1030b420480c000e080500251a5164a6600040c1c1070507036100340c2c001081021188c0b02c500c0c4a0340352180d200171107880d400c1c09640000070b08104080c07021030003681c401d403824001039565a0020041e80e081e40c144102034894071000c000c1000420040004040e0110b08880c900455680300752610b9981200b0b005000c0141c11481c2c031444024000320706a4148602e07810f040c3c0800801c072010840d80c82a00c840000d04ca400c0003c80c41d210f000902030040d0754680c9a83c044e1030040000030a001400740a000e0882d84141a0007815000a070f0000e0240c0040c441112165a00a0007009050140170b601132184a27103d06d008800b5000c3c000003c450009005203140143c40019100b08001c02503400c100d03070b4016031200840fa00c600890211401ca0104140416440301e052441c001d00d0101e000b81300034001d91150090111102000d40c0c0c49810f00400314064480790307104e1030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 664745845 1250 664744595 664744601
    0x209060105071704080124060318060903030c030f0e07051908120702010f0302070b0a0f1104170705030c0a033509130510030605041a0c0322030503070f03 68
    0x806402c0c80310601079480f0300500e9900900c1158059002480050408104d40000762a5403016185940d0b11800400155010303800c240c000d1a0f03600d52941c1c022255460b4001030350f0300070900314002a541c10282c0011034151055a403016220391007081215950b2402691b00c4081e4003d070b510411410040301020340001384130fa40942000350544150303130a003070749400c1070342c10400040707020505551006801c80e00c43c0c030944021641003030340d45c0c10545580c2c0e0200c0c020840804141e807450784a5812194016601c1d0082c40103000944103800c1104100f40c070107017050802e0b0400f502c25081035171400c9255031402145015030f50403080f425070001310202c0c056289102ca1180c82c1c1800c02c20f1241503101c0341d022014060b01a41580c885180c900000041c00c100c43d01202c213001d49079125070301803002c82d031a07600c01503210f841071140e10741d403456843c5540440002154021000c01e0000104003112102c003c94003500a1200b40301080d1066030f580141103400000c200d802001456082c000f1240e200360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 664747095 1250 664745845 664745857
    0x1050307031403070c0e07020c060f1b010902030105090d03150b070201050d02071209030b070f021b030102130306091403090f090601300b03030705100c090902030a15120b01030209060105 82
    0x4101c52686d5446659041c031250031202071000d400750140f181d4850610404131401d86c0340203041d8a04d09001100d601089100040f905102517503035142e882c0040e00d003445814000c600d500002c0c40c00d40d012801c02000c1e02c1b11159458034080610b08100190b240d00001d41d0b4043c0c2d070900b0815240c90000382000e0090049a40c05001620114240301807503401040d010140c0b400368800c083d00d89c0d00c0b654207440901004005000583c401629068119959031501c501520010300251515036860604030b0200ca481d041591440c1e0346000c804104094103e07048202040130380174501701070213000041c8080c0c1011505501403000040002c001d42e10810b410700f02e98480f0511411000c18402c2040100242000c994100e075140c000546950720b0004140e4100c107178050000c2110a003001e6003040580304d000c2c0201d050240002001c1400001400030714400c0c03d49403000a4010181402074503298100d1f40441c41d100f104015450214a9601c2030382e042d40d40565a46115494000049800d84910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 664748201 1106 664747095 664747103
    0x705010e03030a3005190504021f020f010f0b0a15020c01050306040b03061602010501080a021c030e030a03030c18052107210515070203071401090c031a0c030105030703140307 77
    0x72804a2521403140e205503005030070700333030511030030b4502c80340c0344000441e00c0b40c20940701230625100d904003d00702109031690030780b070343d0601035180c4402d0100281041000000915240c07201d40100f50840005004c0312132600c2c12044522005009884220041d400c00000046000d00018400c01c1c50b90005e0064503070f442405003540341b001d41da0100318103100c2c001481c00e07040c0d42c051206001e0140681c030042101c6040e040000d246080c6401c10301000143e86c00288080e85903076040c40c010b55040e40c1c4003c42d145000003c0361800001d540186515071104004000060030309204101c070b5481402100c04600d440c107142c1601c0c200c200d8414005900a001400115001411001c0300c11a07800000400310400d0312141c100348110b0300155590141d80c041d003840d044141c03014542c4003902180c80c034219410000025102c018600c00640710f00315651500b414150240211014a944 = true := by decide +kernel

theorem cover : BRFrame.Cov 664568345 664748201 := by
  have h0 := BRFrame.cov_init 664568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 664568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 664568345 ≤ n) (h2 : n < 664748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
