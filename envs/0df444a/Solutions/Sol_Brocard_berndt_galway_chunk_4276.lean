-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4276
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:05:35.131028+00:00
-- url     : https://prove2.me/submissions/00911c23-a34f-48c9-a4d7-980c2489b300

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 768884892 ≤ n < 769064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 768886142 1250 768884892 768884927
    0x405010e1003080307020a020d060f180507090e1e0102030603060f0405030d0203090102071a07090f031709060403081809090d14030603030c01050f01290717120f1006050901 76
    0x408150074034800e210f010b102c00d230020980d400da5091402c2100c0103100070303508006114038184000e148058490400511035401c4005006200d141c1055400940420711105425016a08001c148405021487d0084101c2e0400040e160301e4894181440c240015200d400408031880c10000050b6001085a07120200e0b40310240c1c4071380790891000d002e4001d4030f40c020700c000480c169a1000e405141c084500c034545a580f6240d540d60703500c47d621079000482c0405441c1150107844a00340800e072200821344584040c001a280c590740781c0399074240350003580703a0078001715090005400358034180c40010f4001e4800c001410881c0e135004000f408404030015255200d410100001e04655802e000340c032070140001c030081c0070519140200d0000c901003400340440d8210401c1d007004190080340d004c03861850090f40c00c149081c4182d11002c07840042003109200d002c80410004120140990368180900020460000c2c0e5061819040b50640401d81082040100511404074660b9000c45001c04070903104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 768887392 1250 768886142 768886147
    0x7050a2309041e110618040c18050415030b0c0405040f0b09160e0a090e06090a020a0b340203070b09310501030f030806090103020d300504050405010e100308 69
    0x2131519030481500903400d40c1e400400820700d581041c81c1c1400400e50700c0d800b03c60800010707a601c070080c1c42c0303e0361102401e40400703000300d003c0c441d074280b0703604c140b02000364a14620341f5540e1b2980c5d28040d1030011190341c0c4044d0f001050400080c1001d00443c20050344003103003032015548010116650030f600030501580241c81f03003c50781600c0d0250060360580540504201001c98030340402101800d41034010207594408c0300c0003d140401c020500b6604103038020b00300c010041c40c115491200d5000890b400c403d09000c8040c40c0c03201103c1110001400607400301c150340c49965401014101611940a1a0b40d00740400c05109507960700440034003410004000014070b05c1146103803080c5003441c952201c0081e8035110020060040c1381c10100419842981c6114036580c1d50b006210b000300d401e01c4020341111240000714006411040705516204c2c11580802e041082001c0500c0010515918078022410020702803019042a000c0c0e034cc05044805400303e11400e20780d01d03004110072244005051324502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 768888642 1250 768887392 768887453
    0x1050901121a040c0324080601030308090f06040308090f07081207060b030a05060613061a07030e0a0609050415050607060c050f0706051e0402090402010e0307050a230904 75
    0x55441141581402038020403405820841c0500202480c2c8030400300324600d401450306d44590f1103c51004e4501c004007404841e4a181e9040d81d01040c043c1c00080c45005007418114900b400708130403882207009580f01685424a501443c1c1000d140f1030b10881300f80c00041742800b84200c00035819000d214205a15a541c400d6420500010320f2500c008a5041c0200c1904ca410b20000207401c40c0281011240600c520000040100445003540f1074038040d04200341003003001c50340001c0034180042c041c4c10310300000111030002424000d0346400070300203d9881082400b031400c092050456821400c0800d619207801c05002901a0007006401840c5a0b2255400414644100141e0740381e80201d403041c984030b50303292170700d81c010b040c04136182400c070070b54484044005c2d50410388141c0a40c0c0c001c0e240144944542c2c004642900890800d1500f62181ca240094107480c0d0f691120024007111600700c40c03d0045078484a0b00d00c01200c40c2a210700407071402c2c00040b0b01240d820101c4103615011101d0348010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 768889892 1250 768888642 768888671
    0x10b151303031b080309011d0a0f0201120f0207060615020a030e09070207030c0b03060310050105010f03050901110c0c040506030a03020d032a0c0b010608010605070b061809030705010b0105090112 86
    0x208a203000344071305804014002000b0713054206c1c3c8150701030101520503035000e6000c03103a52110612005005030406807154000b55009602c12080345070b20000c04a90102d00035204401e0741e04c4010100d5003241e84080c20000d100c00240c15504c010981d2010302281000ca4400605412114103001e00c0f8030310702c1f000301d81800e000b00001c400039903110120081c1c0c1503460040c0e0480750402c9911901034001c0e40e10340b40a90f545403286505a0f501611401140203030104100e00a11000307285050030340d41c80b02e2440001d01c00d20068085024004001c0c18001e110006000036143c014010a009a01c0185080e00280e00400e034617010701c001e4079002a10a1485e00c00328294002c4520341c04031805140b040e8040c2544c030150102901e401460744505913603aa040440e0400401d106000029109204d4200042d02485207031b60800c800802c01449141d54801000100354140ca03060320503400081d0078070400c60300b03000d004510f41e42400c1880c03c10a503000003801c030301440d071540300381b0300c3da140000350600c034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 768891142 1250 768889892 768889937
    0x70302181e030114011e031a07090302092404200309070906240906120b060702131b020102030402090402010e12060103081804060b09040e070b0705010b15130303 71
    0x800080081c48450b00012103000041001c1c019803c038102482046c01e030305040c0c5000603045036444100856000c0341c64101c0042d902d0083c040c0d1007080301000e00000560b840e90b881501840d4911211085103000802050740c079041c2400d41030080382020034050680205800c5200c404c4c480c090250b50326540c01c01500d00f03003409034000c015918500200421003500b10b0501148804654100302442e82d41c1c128182c882c0c4601e0712604000840000c90015400403a0b00104a80300b0041c0115050a0302039000644454194074104d402c0c50b07032003000101c9140710502171403ea5a641c0021855810150007003410303500014000703030601c15003401044040c1c490700303180942400450140c038982d5031a03141c00580c60b1321412a45203040c50310006071050745080d00c1000c00300e0b5200342d01c15250200d00d4080c8000390564a40c0d001c41409881d0380081c815244500800b00d19114400016281c02d1040c10010340544040d00203905100c01e10140364270520750310103070040d6901400c0c64802c446c00e100e181c01504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 768892392 1250 768891142 768891199
    0x31a060a090e240603090c101107350d0e120303070c0c0602150412140301080304061b02010509040f060909080c0d0c05061b1b031207030218 62
    0x14007031841003003032410b8540e0710f06a160520844111180240a04212250009844000040d0000c505a017054540744c03802d508803c1c0319050025258071511041424210207070310040420740102122903900f0f5507c110b407c450703100041409039814030b8042080c0e540b055000d03200700380075000c2242086692100030b240c207454003180440e5924034101c48020041c1c40d4040040b181000580e04c081030440c008a000005a4a402d040301000d984a89405c0e52018005034440140301c0704c40d04058102d485d1000640c081e100311801142c1d546d24080c0020201510046a6481c000d80490703080700507a40501110b440c060700722004584007500808110080a45a0002258525014241081218010240030a40340d500c080d10b6900d0b100c40801e0310025034500380200142c02c2030f40020300c2c040c00c0305903103980480c1c1410700074141060045c4d1b040c004d41d40300c03000843c99400400d4548000345800d01c060b17406425480c095040440001c01150b0041205c24910b00c5070030204200382e064104503580d28180b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 768893642 1250 768892392 768892409
    0x3050a060e0112060b0307060e06091305040506240a0504020d0b0307090e0c0a0303020c09090a0203060403030504050c010c110f0d1505010515180126070816031a060a09 74
    0x25560740783e0702c609810203070850481d40d05042140074074541c40e02040c04030885442d6140c414160646800b000442e5200c05489070f0701011010900103110401e205241c426481403004007550704200440f40b0340300b481e89140101c1083c0ca080c05d6021500d4144d0404100d5000740c40250f11a46824041405484869403458040c46100e40c00a580f6081790000d40c920b601c0d0106854601d030190040c0a5004c0d1980800f03009030307100c1c5c494010365041c1002000d9100d00000140e40945440e9400a400c0c050113031070980c0001e45500600081c08010302040d0b11092090a2018140c01a903450000d5095981001e501c01c5000c14030080054a0340c201c600583d9900020000c0d070324040d03081501c0240300078042c8038001d081000482001091240445228510b0141c0d07025007500b1407001100d0648a54088516030248142c20f110b1166482804c0d5014211980b00c40c29036151500714440390300d005e24403040c20542002ca1013500020104012032803400305035086170b5126003102040d07500c0002c55201010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 768894892 1250 768893642 768893669
    0x304080d11150903030604060f03020904322b020a02041e0e010e1501180c030b030d0207090b061c020d02130303030501060807030203160f0311280207060f03050a06 72
    0x110f100d00400103510500088404004154036642c0156056166000080d040080342002c05c000c43d0000c1c200085603448450002a2480035030f07810b101c40c2c010101c10b00c0b000d61003419500c0d19000c40d510b04900041000160495148080c0c100964a00390007101a004036591202803020100709000203c0d421100c140a01c1402d500030300d00f900a1035500c0720f45006004031004085c5080d25401824101d9418a0000280302c1c40200b000000f00405100781d003d0603030310302c104035664506004081c070122094014151803450070500c00b0070388803555101c0d031155100708a030040b039500409a001d00c1d0513441d900181c036009240503580c001d2152010103243d61548040010030181d00d50010742c141c0303075983e0310540b1a840e11a4140d00381d010903a00c2080300b5446c4001d01c0c1312948a02000080d02d5001d00d404100801582c0341080a03a0090100702034a507400d2055110f00000d0b40085d00e060f030316078801040c549242040041c440744404408208041c1c0b210007060f090300b016000300e00074280360720300601c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 768896142 1250 768894892 768894901
    0x105040c05070210182c07080a0b030c0a0e0417160f1a0408031801021822060b09090906251e080702010c020d14070807080f1b0304080d1115 62
    0x3040c1506c611300d003641c41d55560010800400380c1c1e55900d07000d00c030f094498450381c3c1c9540780240003030513941807000c4c2c00d41710f0341180d41d4282da6007400007001400241000e2085003020b04100080d200d243e40b90348420541000700c100b0500034400c4e6021a590000199000c20b509498804400d88040e00600c848440310b90500060204860066011b207600040741d81d40b40416170b011900341d00901d1207074908188514042e568509207002a8184920401403036481c00c81f01c0c0301d201084403c00d40007203001c1d600c00304400105043c11401d40c0c0d0070103d414010203151400c03030006c0d00c03003504207031f1000c07003108298000c26001405070f00e4051148420000c000d10560b130300b0100030301c202c4d401c6610310010b40c203090415690780c0c002b080941010190b581d411b1400b144d03040d40e901c130310303440044121007080c0100810004188454080c05003101070007034032035407180781d00381d5255050011809103403641c008010800000b100016900d80c0c2070310700d0a00c103075084e080e6006107007083c0311480d420207541061360400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 768897392 1250 768896142 768896159
    0x60203090d02120f0a030f0903030605010f0c020d020d051915140f0103081309110309071a04211401050105031009030503220c0e07080105040c0507021018 68
    0x190321508400044071a04440a0710403a0740d1580500c0c0c5102116081041c4048464114014088540b10b4140450307007071402016841240c1442c1e005030002640c821041c0b21540c0c2c4000d1041c20090a454412812040790700090703040c800500001784900c5404c0c501800300141881100b43c40007880611451140d083c4c00d042003014180a0601422841d0184010b58001040d0043d07000350504255880141e0942c0c0d520b1101c0e602c44941000294400d1600140c00000c42c01903640320000192516260304010040901e808001d800071226200740130542c0c2d0101d4500300503201107803040f0300d404c180128000c8911007001107281d0040d241e222030202000e04010705400c8941211025022185c000f041c0154020440d0308180e0018006a01080840e407100364400055000001c01d004034100f2010700e0b5501d42c030440d11640680384410b040c004121201c0d402020440c01480256800d00182000b108001d02521030b521000348220701384a00318052a1003841c0701038039405410603164940d912400765 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 768898642 1250 768897392 768897397
    0x1103060f01050a271d030705070e01080607050a0309020d021c12031a0d1103031308011802090705130b0f0403060f0e0a0305030a020f1b1011180a0f030602 68
    0x71603008000300d240000e2504910280364014280400c078100303120582c1c584c1c544c0a0040c1400703e084452000c801158588070500041100358070a90041c444030340703040302032940b03000140e0041c00710b6000041044500c3c0c3e01b1104695001d0403034a40004d00c9005440054812103035460040d4100c0b070045d02004180b03a00004411006009901c00b0481410801d400c4050b60150a1200c41d4943d0300c400041c6075060007201c9a14280c8604104202e0030750754004280756400c08603d0101c4400211010840400280314032000541c00c6030000041c50070b550003080c03007200b02400c013004004002079107040ba000d08441e804041c042c00c5000c195038815441011034150031500050300c0162a04c4651100302c180da100f541070410b400302c00340c520000c1d1500d05031040d4000415070120141c08000e9034a212459500604840b40c2c0000040080815644018901205000f21840b210300d0480d902c50012541401c0d0b40a1804000c0e080380c02c3c4d100c40340820361202d84c3c3e5002550104c0d815101000f048480d401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 768899892 1250 768898642 768898649
    0x1b0a1110110409200307020c01081015050f130b1c0b0904081b0616140a1d0111060a050a0e0a0c0b3601090f0b0f071103060f01 56
    0x455000c480c03505000300c100c072030409119920141c200400c009841c00f0b80c1140c459032000070800460040c0040704241c2c254000c440000040c0c11410888104d5a0002e88941d0030140c0c9019114949040400121045c901130010f1410300c200401d08802c4a8140c100710740440c413405c105402003076510380745403055411021400c00c0040c00c1400e0458511403900c90700740b1054004150310400d4445884000b526408800c07000c02c581c840707510f5481440030410500740681180e00020490b4100f030107004000d4080b189070b030320790400108031445500c2d03130004221103444141000d0340b0004841c40c0060703441a071130341254019400382004128400804ac0e20052241052000c00d029041d0600c00031a00c0f151001c02c0103002c0030380800140000c443c890045c2c100b1a507000c4003070b520743c401d0b24000031003901241c555110143e4005240e5002c2e581c029070004c0100380c5008408085402e041c58001c5034018402003000081c000300e83d400c180318429815000101000c0d040d110315080c5280b85180e404400d02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 768901142 1250 768899892 768899927
    0x30d0f09020607030918020a090306020d09020a12030e0f01230c0f0c1005040e0a2304050607120c2a2a0806040c090b3f15040305031b0a 60
    0x142030391141c84e00c82c021210002300c15543d504071141903a0f40c030742c0250004c0410f0010660745850030303c01601e445000324040c4c0045581d22a4050240c500209003420000140d802050410780650b03044e40c110540611003402d1003615441c603c00351001d01180d0040e042c1e405018800c0000000807041c0101da03440718034409582480c1c2014503040151441d1140b0301c525821114000f000446151503907002da24075011100342c176440030b121549000b0705548142d4060b60359800a02c01e00240710341004244c801c0040200342801070400c0c01502821250140d45010090000c0d46540341c01014101c6c138102002c0da0000b0380241c503402c0045009206c01c450b40500012000c0302a01013800300001514030321035035100024031142411b00070082d025160000406820605d141c402c90901803280b00480c5a0030807600c50940c5900305805002c80a0381c600f89200c0890b0045242c10250181e5a281d643d8030a40506120b542c984810a4003079400300c0036020544800c1000c10203c610542c0039108003004038064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 768902392 1250 768901142 768901169
    0x5030604050a0e0102030c2106031e030f0403030e13050609062704210309050d0e040e010618060f1d04020d0f080301090e150103120c020406170607050c030d0f090206070309 76
    0x32340c111311203000300303030f03109981750344002188281c0c0c409400d041901c0b1141c450a890400c1a40700303448020b5001504101d010800e0780151009a06104400e0440100c040324141715509003100807510760300c000360a00d4004c1a13040d44445820000110701c40c6e03103030100d64070040a480e07c0d00780314128900d81c0d0004000569849180c0c40414031030700810346001e8010700900703507020301c1c0d42d03090b12845503c01c1b0158000d52950b004800c480c17028802c0400805002084110759455400031400316240e40d041001c4284820000b4061488000118902c942d40c070200c1450b241c440d800000d28071501c51400915801924440030b00300402500518126072214005201e0600084040e42e12051100300030b92040c07081500420210b040d6000a0442103040c1c00c000340404015000314040d038020b5081120307103070008440c850003420304000a0b644a441490500e04003040b28042c19141e00c00c01100690341c94031000e65062400c920381c41440440d5000380000d90f94000d925001d001291503224127034008500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 768903642 1250 768902392 768902437
    0x120c0306090609060619051002010501050a05030111040b0a05041e03020108070f02300f0306130603021c081902010e06010e070c20151b010c05030604050a0e0102030c 73
    0x501c142c060a050005413015644003030902c001c101c400003890140c0c06282e400012540c45034428410320400756800070543e1340c1000240308807d9440d030b201c6802a89080c0d044502c0700d034581d0640d03081e03c0c1500c65507696511400350417075280c0036642019030605090b40b85402600011340c0e0385000c40b0b00c00e80300d0090710f5403041c00a4801280003c4c810015030004004c04681c444600308200141c040042613104401c2c6242220005801010030014929000010311085182c0520781d06030030304c0308103000d03c240340c01c2da401300e9141403001030200c0c5540c016401200800c0340b141e041c0c5182d4460302110542e0ba01c95010028007a02a009554050b405401e001060f41c2d4098640c83d031041c0c0840e15503014500d11562015000c6000030b421402c03140104048030001c0d034500d40f13850710482c1868561505d40c200c111040e517088402c0903d02480c3da02d804c1211840035042020b8951040040350002141ea41d005407041c0078010010b1089101d500c000200421074059030050003031b8200c94032070215994031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 768904892 1250 768903642 768903661
    0xf0807030c0b03060d030302070f150c0e0907090b030703060e0a2408190201030609050c0702090907050a0909020102010905100203150405040b0a09021c0309031203180b1302120c0306 80
    0x2040c0d134a642c105407042c1410020900236001403e00a10502d20300c40da0031541d40700c40404528160720449080d49403003030f54208a910449003000071200b2030704150581040c5101902210740c505c18881d0000d40400005d01c03244c020b62044d0700410880c1d4840b6414903008980d6002440c60899442005401c1101000b19560380201c98040d078000740014610a00440301c0846804040c0074200d04064440201007009c003d00d0280fa0302400c9003d40c1c86444130080d204203c1006001402021a540440c07420445130391011020812030f600c41c00300042040386400102e01515155001420700d00c2901440190141590700031031160109400c4181c208908500b0041559400e44014003154020000b0a1800c00b56034001103041e84000d100c0c59541a0f040d95490f00b10002040690201e4480403042081c000c10002155101c89180340410080410b11442c9458a50010014040040f4103001071503949040203007045458000341018070380030424011940d0341d0069182c0a000c2d000b40000f1172903218 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 768906142 1250 768904892 768904897
    0xd03060605181323070f020a11060304170a0e1c23010b1507030e09010e0415020f0f0c010b040b0109030611040302040e0c03010b0f0312030903040f0807030c0b 70
    0x1d0031603502c025501a100800800032030b000c8502215980c0c81e010840c50f80c0c1159010b000090040454041c50300e4803220280118040100f0241550054240c030b200182004603404420102281c01548a880d94101804913202061102048c10300010342101c80725000902c0004001e001c444409400e00c0e00d010b90016060a000700911031201d84454070264440d0a14007031890800f100002a0700080300300254a9510070080300d102d203400021a101450ba01c030141d804105400e46041d101075240542e004014003000304040d0070b8507000e000510248401c4d070105c0ba202a001d03016a0780307070290b4110714001036224015180c0d01e58038000001c0024200b602802020010503110303144c0c41c0e80b450b20b500c0c001d000c1d05c641c440221041044040010f0741c171845080c0501001000508112003804280350071034034074483c4944242c40c0c86c0c11416031558009841d12018426028003a1240c172018280c030700d103001c5c9800120027501502001304840000040d10022280220817809070203549190b01642031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 768907392 1250 768906142 768906157
    0x607030f0e0a1424091c02030712140303040305030406050406060509150a08010b030304060f020a0f1406070c11100318240c0c200901030c0501091d010e090f0f0d03060605 75
    0x313400601403c80c03140303001060191184040040c1c0c200c01e416690029082c40d40701c2d04000503017402a801c080034000724116240011b001d03040254910704158a02500c1800020401040c031a1180001420014941c001c07000620000e0007185050801d0002d15000704103280c2003e019492035034002400c20703014010b81103610f002601861800d800c00e00b040f00e2a0440c440c0540c2036100d2009840002058607202e090f20304e02942404080c0c1048210060800300040c107000c00b004010300841c4085201540c103280c02c100100d03498580311100b02c5040d000303400c1160800700e0340c0e88440c50101c14001492003800410032201603015003401140c50030000c40d1a01164240020b4422210500081041a00c10f00004000c505101203514000000f403042a013600110b8100304842d400701b01c99604078071044060083d0500c0710403000d0300700c010320008075414401c00a6000039440400c1c0340d100d0501070b51400708189000d41d100000301c1001955a65403980e50314001918008000600c01c2c40b58090714003030b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 768908642 1250 768907392 768907459
    0x601051605063103081e0709031109090706030506040e03030906180a0f0605150d12020d230901090b0a09150819050903210a06090b0607030f0e0a14 65
    0xf0b005191002c0304c080d20700800081090369601c062280f00d01c080903401d407040f02542d40701c551403825850000c2c40e5248000340036000c6d1180c0e000784403088401140d440f003603846030302e40000c9669903500010003601448680c88264000041401030648010030070343d2040f00381c01401490b040d07030002c51654546061502600c655000a8404000340f078070380103e900007640302015890000920002141810300c010304407403000c1800110040c0e6901804a8048880d05080c20503c0240c5003a00c0004003114a0701800c2c0150300261046c0c8070380c0503001443c0079000c4040819202c10b000d21028001803024010700c3c15040d01c1000f6007150034410340e11b651107006402c45c920914011003007580090540604a6003441c00203009515119140c0f041d15070106030268289040d0b81850007030780d0116500e94010311040d904040c9007045648640701191040303541494405000001000c040b10712202d01c07400302e0380c4260f51440000e1543d0301861441c2c184501195840019141483e140c14028804050b1010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 768909892 1250 768908642 768908731
    0x100b04050a1211040c0203030403020601080615040b0a0e0709031520070c03052e09050c01080a0f0614010314070f030903020c0901080f0d02070501090905060105160506 74
    0x6592000c2d00000c080c030030691000b602e010000090107886422501300d0050b40302000300002d1550403ca001d00600c3d41702d014000740d040c0340c6842d1a4510300720400c0360065442e80010f00706038403040136480050150000c01c130ba039400d01c08002040c04000388016120824801030f401014030b007038818002440840b4680b10310700003580140350b80c1500085400e80c9d0444001d900040812028030500591030754000180c41d52404444001184161078007103502814607144520000a070006800311403500d090030318084136070320304188070007a2011100e07e00e446030814500181c06120038000b00d0484401340c0b070501a04000518256003a0400c941407400107611a500088090090f44444041802481945e400382c8082000c0741e8410000c1c1d01090456124242c5603070700c4c2105206402076051248090140d541c80d0800080400e00b00d40528001745580d00d001c600d280e8016021903401d50b41c40c9029940451a5040560f01c6000c1100d4000241400036800301c07040c2c80f0007080122014054403000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 768911142 1250 768909892 768909899
    0x16170705161d13050a050102030703060611030a050c070f03060209041b210f0510030302120a05120a092009060a03080d0c0c0c0306050103020f0a0b0306010f2105100b04050a 76
    0xc0d402c180203802c0e10350107107401c1e0094010920900c50a0394483c051400980e50b0b0030003540080440300160711101c200070f041d401c0c03040071241c040304079911455a07140c402d4135401402308842c01d04009038002076110049031000020041a60041c000300c03001144e08200b0b0030525416881c0c514104409800002c603201d254007640ca0706101e615540301002c8500082c1400b411040c1c00889400ba10001c0d03e103507c54500700105981088010050026464200c2c01c04c4400300000e8218001c1071440440c0a0700e1000188003662240d110411454000018999803200c00c0e0000241d0002e5410f003e004901c0000094402e0400f080714904590380114444e00d003c42d10030441c4000c003a00c02c400c0c41045003900742840814803000310000654011100011300d94503602c10080112142e00025010f00e0841c501004018201d2098030b60211003030030b101300c0c0c801c04148100c60313980c5d61214060034208a803036000001c60196010350700c070720300501d008404d0035280d0f00d08020714040c0d072041580c0306c0105441030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 768912392 1250 768911142 768911189
    0x200d02071a0712091e150203070506041103012a0f02010506010f030b03190b07030b0d0b1501020703230705040b100c03120501092a090b1617070516 65
    0x240301c00741e051400b01320340381c0c8072490103d00c1c40c01e80510300800317007010030144940c201c0d11036006100885400207628020340b95a0380c42d00d41900500140810040c01e04041d070585003074000b50044002084100c100c051588001d801000c1d401c03003000c0000b20507400f262011801480b034680103540c140c40d0b52000003481d400031005010868606509801515000400c0440915400700c0280c40f4000c040c4a61505507001411280e8161071284a0032417045450701181d1000b01c6071760008140000c0410012034000141d2800265500c0146160030416041c2c60305090544006ca003142024103841c0d907555a8010801030b12840055998800e401420400629006e0b400340e6096600c641810f00b003003040c00940d070302159800d9106000f050342701e8078111000452060b0b0b04107480d01c1c008607184105040240206904154040e015071490002014a00201d80c0215210300320792002c0c00d4042d0344440007941d100c6030090f1108546c603101e0801c0354044d40c1c0d0380a000000366a084c00c030b56a021072290700d88 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 768913642 1250 768912392 768912413
    0x60a020a140d021908041a090a14010b0319050322080d020c1503090c060a1407120807020a12030f1d010b010909020405030c10200d02071a07 62
    0x4003803060881060140d440d00a02420710180b10710030041c1c5600f180107480d201c8080141c148410801c01104101c0046c0851820602d04041040901560f0b81d0343c4000030702c1d141000c00090042c0404050f40820004150020000400180e0650f8901c000003007008141a6a2000003003054000707021000b80441200800d5100c4128001000281d903658001d0900307292032100d624005070807802c0719012a045c07074201109215290741185107036180562a1b95160b4044202d0035200b50000104400c01a00c600b03141c241c1d0491030061141d0701c02c031500d07046200080388100000880c6610f400900400d00101d8660b61094008101801c0400194400c41c018080d80caa45108203070f03601103c04200c141240703a907005500300c000002d04800c0e03040024000360101d030f00c0082d00e03900420091240f81c03004504100d0401080d6080c45c5514924103041c0e685c4003d00000c040c6808850b040c40c0032640c4001a0301d4040982c035000c0e1400541c81c1d60900348d00515540b252100c92070104041800a48030700d54 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 768914892 1250 768913642 768913657
    0x341205060319080705070f06051c020904020414090601020607050a0e1801080d0216060e0409021503190c020706080727060c020a050306011406030a02040b28030509060a02 75
    0x196402e022940341084414001510107882e010000b080300010800100205d0001d00844039501b15801d15184004103140325030391125590780d50a80c3d07551442c0c03025406440072100010015922140ca5103035100e9005038400a0038421380310381e00480d00c954004504180608500c0e80d50b1032800450080c1030300c400740b03013054044d0049042c0ea201c1b20003504a45043e80601181400340c42401150403009140500e1802c0841e01c60b03806a8007000029000307104103403118070644010803488018000180c040d8100c9100000d151000010400e01581041501005044e950010085015000401caa99a809000340c4020441200c0401d4245000321000509078400c5850000a00d08810800b1038035803441d445440407d40e00c038900011403600c0f80141002d4081900104000d43c9441480404100a041c0c0e076402503a0001c080f4200080c6601181e01605422140d40c0d941c5089901c20f1411110744000e40d1031002c02060f044904621038026527000b000144000d05094440000610081d80b02d00c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 768916142 1250 768914892 768914899
    0x806060f19050409051e071101091502040302010207171005040203100e0d26070c020a080610180515060f0426010501060801121104060e34120506 64
    0x80d290269680e0459511441c4640c1d281038481c0d1901d49941c003500c1024094003245d101c2c8102800307001d61607075491503029469140001c074250881d5141c900400002c0e0002d050b4403506e0580220001c99a00200116032003a401c503050942d0312656801c1c6010307050452259030f044501c20680291842c0c1059410038002404d44034100700e02c00241d0111014004200071941000113001c180e240c00a0034104940c0400c1005440780d880070b850800d82001c02040741c0d00340181082d044042d900e41090301005460f94508540c4503041140d20807050101030301ca1040c11002042084452010340d00920703020ba10015824045121541c007004040c0d0004010f00100306010b0100007419613181f5203060201401c52404403c0300d0708a00d03958250b41c0141c1100702401008001004030390514201803040035088404500000c81c00c60004000c3c103c40e500010310b07080d002c000d00c501c01a252122124034480103420705243c2542c00d000b070a0410001c20300300d0110b01900f03d2000c1254643e000b00e644030a004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 768917392 1250 768916142 768916147
    0x21c020a030507030e3d05120c040803070308060415080303060f0112060e090607050403020d0f03030f1d3d09140a06050601080433020c0c0418030806060f 68
    0x4041500c00c4042024001194403410380c100020805003c4121111030f580c10b1b0703900e1050114000f03012440383c0d050080b907035000701c000078072a90136000945000d0003030042540d40d60700c040d04004000f854180c2d40240b156141c0301d074080c0010140342d0040e04440d890b402a6007580d40388020480aa031104000038103002080b07a03e45494022403003101c01a004186c2c040520341007064089140000013031911050050400091001d030350307406482c5040b40e500c034141c030700c1c2e806140c075007100a44560071559408900349240401445803c011400c500500c003000c880c40401c51440c50418000c0070790340790174000011168032200c02400a003050102f00041c0d00481d6481955495070303550b072118070408510b40c1060100d003080060b24051550800024039040c21281844e807240342d02006241c40060101c3e011400485120070304e13002ca015107400202c0119102d120076008291900c51201550788520300c2c0600c40040600705403411500250951b40f00c4500b03645103070521034160700071101482ca42d10207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 768918642 1250 768917392 768917417
    0x60a050a121106040e01120501020702131d0a031b08070213020301170601030b010b160c060f02010e011103070e060f04062118020112180f03021c020a03050703 70
    0x440a4000040040550710000310586082200c080324881e103100e4821a0100400c01503010b98030384190550780400503010b003400c1e480c68170390b0080c4100c3c1e4000b5007050041414000c0110700e41e0201510b0802c4070310b40005101c0c5480348a84034661004002c8c080303010b08402c50050040840c0511159201e2890306240c103456400281051031030000448041c3d40020040c00500466600303003003103e04c00c100402c0503505550f2145455103050082c1c1c80040000302c0c4031224002c85503050000c0300c1d04000d01054064a5510003050412020515030143d070034403492a0301e5040512490104005640126045840c0e85031f00b1580080340502c0d0542c4414140a101c0c0241305090086c0001c049540340c43e180a814240c20b00c02901522008104061504584560ad00641098411100c1d42480c0904103e0381d80d0002038020000d0004038800201c1203002c2104002d00407900c002e0303c034007030740856a00041c620b05911913069060b000f44016040320340c0b407200107070040c1d002e0300100c4d2090600016000c038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 768919892 1250 768918642 768918649
    0x20d110c04110d150308030a090c150201050703051f140411180f04091220010204141e01090909170c0d09050102210304051507050304060e0607120203060a05 69
    0x1107222410b0902c00c00a1402a4800740d032260790303a80505010803480345132441d140c20f070190000420340e50750f0b541c0f101c12150411a440088038080c20130a21a800034505140c4020700a100445051001c03c3c5001c01007800c56207500e90702030a000301e052104044d1070030501410001911421596045a22a051242a80e10507406041500c41040d2144400001d000400c00c000c1041c00c03845010301d150640d8440071030081c0190701021140740c10101c2d21481d041c400521501c1c91f0b50b4110320359510102d00443c191303d0002004070994030441e2030b042d45020130301d0910600744110070128040340031144104040c1c0383d550032500010b8010184000800d945070f046011031390229555400e583c2204c40c0038235046802005041c0585402c0c8000c103007400368514030104401408000b074450910110020741082400c01c014641049070340300707819550403e030102800c540c01c00d5504440007420401c6015403a000060301511030a08e5035188122840c2940c0400c009610242075643c00100100b008221501c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 768921142 1250 768919892 768919901
    0x20090f030313081b0d11011b0506070504031a01050102031b070f030b1602010527010915090c14060f03060d0f050f0f010605060906030c04120b010513050601020d110c04 74
    0x9100001d050420000c00c0d80d2a44402a050001d11170700300350302100b011580c1c0c1d81c507401d1440390a0030503242001c06051181c02180000b00e0085c010303c00c000410a000745d00501070130441c2d22070112005e0100c1c900703030b98000d1607000f40110b5006900c1404011221035492541790f01d8015090180d03851a030301d94800040002142d0015100000d140051100c3c482c10a149202840d8030ba00c005c0020b810540507100c5031505c250405020010b6001c00c1e8100c0010070352141c103025038420220328800e00c1003c640c0003e0720804400303440701c012000380015041a01c904c07803110130340000c140307500e00f0650a880c0403a03170304042e01c0e071900044807680020000f00d005440004190040c0300034846088074500c128940910000006640d1741058000c0180361070328003e0702e0400c501114016229030300c0c00101c070b2140c011a441001806a8030003554180038140c24940d0507a5000c2d50384a40321652108140b007503c0301601c910780140c0c42481085806841076200050341d10804054a050740747c40b200041c1944c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 768922392 1250 768921142 768921149
    0x480c0f1305010906060e0d030c1722030c050904050a061d0a060e0c0a03020a0e0c1c020d0605010305220c050d050f060f01060c15290420090f030313 65
    0x9070303204d40500285e504010551a07502044030b05440c50b11256134000c14099000d00b0042c1054151807011a040728500b0a541180250003500da000d00c8036002c605a0b008602c0c44180c4e0403200268002c00c3da8180a082a489160000000d05409007241d031410014580c0002004a444800300c2000d1503800c10b02142ca0041d0245101055040e121090f540c100140e41184600c152003c078410070042e107940c06028120740c1d00c032403900e480390348a207412700c000d10454260151204c0c0c0702401c01d007854096070182000b214010010801c0507101d8005408a5109842c5a81e038004a1403154a42d050301d0700c965070005110340c115851541c1c2d0352000ca240542c801c003003102d858006844c1c2114204081003047e501000840680c1c003254034201c000b81c86010314040183c4110754018110b41803142d290490380d1000c40e0380f042d803586c840c1e000b01c2200221a0030040c1c1da03ca2410800c0301c00411201711400e24024814600c9140340402d9041000a02c2020105281c0c050100748944100c140c1916241c4009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 768923642 1250 768922392 768922409
    0x12150f10051c060e010204120f05031e130819081b0706050403052103130c0509100e061509040c03060e1303090b12040314480c0f130501 60
    0xc082c091414200ba1456441c0d01070b0350341c1c4148000c04c41d081d50404da08038041c1d006840c9000315041e40c1410303803c0d4800c2c0d103d40381d40081ea492500420142c040010691401c0c2406071030103941d11b6803800f41d100c11038100c81102580840d90110b01113856000145100301400d40642c08821620300c00c2d6060500700d501c44004204003140804c03c2c09024000382000400200c5100f040c02c1080f1400d2000b400094648a0000c071101046010403151445d00e1014010040482c500ba20700624000228015402200c285c5501140812840d050210140500c110201041401d021f0024240002000d00c00c00000815450742400500c051040c0b04050048404417140303154515682030140400d000b0780d00408110b03004204500c85400042909500140d0618041300306603862501d1707031058040d001282101d47c41c0042140607290240d0b0a5107101d00001086131260b042115100040c083c150100c0140c9801090000f42c1c1c0d442c0c584802c24406000904010315503080c10141e100b1100244c0020b42e2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 768924892 1250 768923642 768923689
    0x15190f0c110c0904110a09020f03041104050f041b0b0c030405090105012c0a08030a0206091b0603011404091406100b071e021f0c0212150f1005 63
    0x102194803003415007a20005100034071484406401050b11508002d101030010000006021180e0740c5582a000040429580a640365050110030181d1603206030341c1100c000d804c01040c40c45500b000d0041034401c6002100c0001e007956281c6889416024440c6507605840400c0d4000ca03060035114007a0108001c0c070401113407600d0600007800754404043c0c0005060051520b2400c281002c600e60a0407900c0030706401c4800e45010802040760141950007440072400007041e002000d65001542601c1903403a50200c039401d10002c0a40d01150b40c1101b07000b9000201040180710035405509000381041014000058442140c0c80340290300c0c21900c100da0054220000b0b01c006041000d00142c05002060915442e00d500c9560388400704800300c03080c810301c240e07501c05d182c03d540d155486840c1c5114846501c034601c0c2a501002050241107920480c8140c000b46a00e44041c08002120302040a401034201c05d0ba48501c10b003040c10140c01000d54008456001c0c0105990f00d5213071900e035030110060b82161 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 768926142 1250 768924892 768924911
    0xd090905071b080c1605130e060a02070501020f0406080415111210150801030605010e070e101719050c0708090d11040f140702120f0919060c021305060315190f 70
    0x3c00250f100c40381000803820234000003442c00c004149581c0142e05908010b0f941c545038600700c2d0190103802c10300b00a81c1400b140000c0c0b25604034040c03920451203417902c0c001403075941c034510301120385240ca9491a10360501c841122180010840c4c2d030440d4130491850402d654883c00100e420784015039420004800c1d4004208100c0c00303003d07044c003504116228a00074070708500c3c003d092440146020748a50303410203280d0445d500a02d202241e112144e030940c1c9c590700c1c0004901d40401c1d050540892fa403858200003810501d54041030310301d826440a1141d00e03040081c0c00304445c20b40481016942d20800884c80e01e0f456580e0f10440b141640640c0b0003080c10b4080071480f40d07044900901c24bc041d500108031103244020854101d03851503101680a9442d503464501082c80f500070368002c0102030b00d1060300481c01c0f40d0459840c0c44128400c82d40c402910804510300e100750f920175203159405a0006450603103102210f01c80c1030b40803010b8200e0303032540d0410308812015a00d50702c0211603034076074904018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 768927392 1250 768926142 768926149
    0x40f0605070203071403060606030403030b040e030a1409130507090b0c2d0d03020c07180f05060105181309050a1a010501031a0922050d090905071b080c1605 69
    0xc00007172021a070200090344c203e00c04030340ca40d540140650704c00c40c0004002020103001e5840841344000280040240d805108072182d44c9501004103240803590301b1014010000c0c0305400c82e001c1000c0070b0420070300085901c00d582c014100141580d02880030141c0081400f4030b080020b440401070328001080064814080c0ca00c4c40c000b0075244440394558909110715001c00001c2c02c41d032910b140d280050b40c41c9000c1148900380581e5810460060000001000c1c2d9800f1907085140000707080d0100300500c0d194a0010b4030756109a0030907401e0a2200e1400c1c960b0f61521030b150303030f0358805c0512020491414656800d07081040d00f020032540c2c412050700d40b01228054495043c003514003070030304002045041a603510106420400306120320b41050005a81d924512141400424201900400c003882494000d4507030004c030610000003010401d0020b140b45003402042c5c001e018603102c80d5851310700e101103070b480101c108009690f234120030410399841c1c0200304550000b02c110101009407035428030082 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 768928642 1250 768927392 768927403
    0x30902131a010c05011e060f270c020a0b04081908060d0209061c0b0901150f12060e030d1e05072012040b0c0f01151a040f0605070203 59
    0x80344a10715003407440a84480407292000d030010242080d41045065244c0036002d00002c4c480e00581c2100d8113042c040300411900401d05540b510340c103401082c1d17111506880f0840c120014540b50404d8000c400c80c0005c20340c2c0c0149071686040c0305a0304a0071007521032086d40c10055030100c070040c20004951000c03000d10030501302c1e141d940f40f501900c00c1c140000001c0303861000c000013a04c2600581e02280d250340d031340424160030310061182440100e8160902010340f18080391041150f509103400142038004048130300b02034690001080401905004480803949e43c1140d0440714913a90f21401e8031160000c0000d000d900000303007000305503211062200320030b0300707080211540003500380780074007804640103a041c140891150110506181c1e9100c40740e840d2000661881411100c00140440c4801401c3c0040409108481c2129108201254400d00300c55580c42a4109110b840d003043c814000e43c01c4020141c001401c42c080d080940784c220440b03842550f50f01010101e040003d2190441c1402e004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 768929892 1250 768928642 768928669
    0xc040806070e09011502070e0717090f0307141906020901091a0901080408160606030b0105030f0d031a031f150608060f21060720030d0207020d050d030902 68
    0x148070324102c0085000c162140f106018440148500760703011800c0c0741c4200601001000c4160744e030325950501d1a400b800005c580725414000b43c3d0300c2c4000034032203000060202043ca8940300154a44451600c0f9406507520752000c0e2001c0f800f0382d100710303052100c03100300c035042d42070241000503642d011801c0050248040b07980020980d900142007504201c0700503080da5005402828906030765902e81c6403960245c4541808800b0401d1840c18007411301811b44e000c0c0064034800e008903500750b6220300406950354425040c140707203075021030b6a44281a200b074110083c41101c103102801c2421050340060b081203100d040803420558403055400c0c0c00c4540380651031f041019055000d94a504017070740200240300c01404180645008908014161120303014070201003648043d0b1800c103c803008402303071a001e05442290001e0048030401901160860481041c644108011403502c0810a0500003a400c059070590b48450403044c204045641404100c9100010380c0d000034000e00140704212030100c410380b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 768931142 1250 768929892 768929897
    0x3030f0403050a034a1002070201051204120e04140a150503071d13021513090207050303150f0f011103040801020c0a12030501061719020a02010903030608010b090601050c150c04080607 81
    0x14041755124408607015100d4845900c0243e0703112003d0005a4481c454000610b49400c1a4010002408441c0d135218010310310300d40d86d1040200301c81040200361007140804140381804400030410000c1503900214100c088010100340031540e413030000b0b0074000c0e00c1e40300a040c80c050f940380c1707100d0240c0a03103e90760010b0070005010039525140c01240e02441460889024071200040c1c600c01780700e1800e500c400800780342805551f00ca00303619125840750070566195020498440c640900d626015114007011f007009080003680c00811401100da0704c8600c2c2e4000d295000c01c11000c150000280018400c10042c000104bd440a446c5000480e05103034040d05002c0600c1c2034010301200e80d0011043d40300603148890700382140c03500628890009841281c034100e540c80010015101c4d40c064000c0303900c01d0300075101082003595030101d060a0301c040d4882c1c164000049800100740798019005054507500103021103c0e4808842d0050b4585501078881120b404004241000300034030800c20346501c01c5192 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 768932392 1250 768931142 768931271
    0x20a0201060f0f06082208040302010f09051c02040908041509233618120403120203070507060c0b0c130303030c030f051e0903030f0403050a03 63
    0x24581c0b9916604600807a020400c801001c2412032103043e000d5090701104c0c05501c40340c96007d140c031460b664050f20080b40440d40105070781192034002e00c4e0702421940f019051683d05801c017a004951100c5059049a116507144440b40114040c00d002d08050607004a1b4601e003c0c2180c0e401428050550f801401c602c0c07007c2c3d4020a1000c210074100d18400002ea0701080ca401c048000c10085803420a01501c0b03501c0030040903005002200750503800781c90001041a80861182d550507200e502d4000300c400021401c010400000300c480c0c0c1802d06031401f9104ae0303418042155689030600c3d0a541c000e0b40041c0e0001122400e1005102d001604281c0b115001c524081019002d5100040301d0310014080c1a96a070750307608224026044028003010104080200c1d103821005a0003520a8030754020284841c5000103091140c00001c5902500006003000d9283d6030f29035044401d030b44040d90100816865514040c0000300000c00290f4240c8141440c1c0300300c1a0450004c0340c03000710407181c1082810345 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 768933642 1250 768932392 768932399
    0xd022101050d2a050d11040c050c1506011803030207030506160e101e09150305011206020c031303060905010b0f1309140a03020f0f01050712050709030213020a0201060f 74
    0x325803001c00c3d68410541c40c00c400d01c1c1c03180c1e1403000e10b07082c80d4442c0350000c0c0b07913000ca60b0401c140305c00c201700c2000c401c40d01001303030b03607960380d400c8500c5d01910180ca00154040782001e040320204200b895400601490310701d0701000c14504000d4081d80c942d00c200c0c0580d12981c3c0c00d0040150038010107a10940f0001c59040040b0f010038010114901d2032030046c01900c0340b109645045208040300503858941407039091044550010007021503001d80b02e04420f20664090301d240c514402e0290504032106414400700d90740250311890000c0d80708810320305544c401048070f562000b0725007401000440c0241c90001325080c060030080d0035a02c03503203d2244034075003842003840c1c04d9561080c0301c90344220703c002c00148903003a8034010a100071803041c7c1d0141032080c00d00070b1080690001e20050a104040300b900c0c8540c420a544509881d0156903a0307007c604e4495090410945c1039100c1e42e4031044518141d05841d54039000300d08504c064100140a503078001074000701a68090160304024a1501c1302019250314 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 768934892 1250 768933642 768933653
    0x20417070605132c1e1605190504050a03080403150c02071e0305070b090a061e0c060f050f0a0b030f060a0e071a0a11062404020d022101050d 62
    0x8030b001c2d503005121880c09200c83c200c0c1102600620b880103205400d00717400c240c141e240c81c2e058025101c2c0f40622400001540c0e180b0702103201303c1070031040c1d110203050803000b880c20814070b40b1780c00019040103c2404001760030355844104074002e50040c155295100c0c01c604082e0148082c004450400394280400c28220a6001404004440ba0040e0807145402d0610103c6e025410302d0388007402c98401c00c1e01c0415000f807030f50000c0001d401c0464050b802c0380c1d61a00251813011035000d011030200a8411045e1801b8080c0c2c4c110984d00c0d00c90207001480340101f00e03045040b41c2041d600b86180490000410035003981c21f11906400400490050498210290380e9a5540d200140103081e202e484181e102d2400c2c2c010012100500854050201c4124000000d035402d6048003075008005003128140700d04ea0180850541e008003001011060a020069200440b42042c4095282c11960070881e4001607180380c03020b45038042c103500c03114201c240c94080e03074a036801040c1c1015200700a1680750b171000a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 768936142 1250 768934892 768934927
    0x1501151e090513181a090f0c0d0c3206040b0f130b0c0c190506031807090f0209030d08060a1a0d021803060c0a020304031401020d020417070605 63
    0xc004480c502c08100f80d040d05200540607004071500300321510442c0c0030070041074001c0b52415500344c00c02c000c0d035645d42c880d04582d144d0400b48942025080704250560504140d645040c042d40602d15160009503107803402401e1620715a40050004c00c0c00c090495500c81c80b041105002c1000c40d40c0c2403d05003003903260380d80c3e481400498482e02000041c14010101214243d00062900b004919154100107a2051700c4c1d9429041c03252180241d502e444550030204141c0078243d95000d0003680c2103540c0c07804500d00b100442043d00009119403030001070410002d0040000042c1c050a0140e00c07504070310103140c0f8102c0f0034038884091200301030030450961603240905040b5042005400c1202c2c2002c0d071184400e12440050388015400001c4030325100076011440100020305501305e80550791000072500f203074010400c0e080c0050304100420004100e00d00041405e840015000505e00107076080c141c0c089034801c0e07000b82e21800c0c42c0181c01400c0c5030144031250081000c0d0038000d00c0e06a20880b901d0454 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 768937392 1250 768936142 768936149
    0x601051812101e050108120904020c011b020c031209010f2a0b1e0601050a030b01030e100524030a0210020c04092006090904060903021501151e09 64
    0x600048240031401c0404000540480c0e002d00020040d50b0b00c09500c1620000c40195411001c0741070a000241c000d000044c106200c0c4200c0d489030b03003844009001c100c040d45c1301c5900310300c00350b407116140948046481c40d03021043c000c81d001401d8851003071082c9806c100420f0043e0b0078101c1c2c00d110240c21a604040d4072401b0011614201780ba090103010810015607411060302c0081c8507070702c40d60342001404000f05015004103e440c0b43c041101003546090080100ca105000580500c80e99800e14007a42061103001c40504020400004060314141b414618165a103141501e500522022094241040c40c040c815403078003081e418150004240d45640b80c8500074081e0078003000c500c10f014804c1c0700a5101c0fa000500603c442e03242d07030a0043e40f140d40e1021400c440145203074541c40718506201103408800f809040742811340c1e0303035881c3c0320002c125544e4250250b0060715190442010100701d44c0e4040e0a1440b5202e01400114200030000e00081c0030001c80f5510030f0604845c5560007d0000c03044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 768938642 1250 768937392 768937399
    0x260604093513060f27170105131401060e0c070c0503060106020c0d03030209030109050709180b0a05041103031c0c05030606071103010b0432011203030902010e06041d06010518 77
    0x12002090494080408501900c0d40403421480c1011882030705c00381004403035052404001c0101c5003d091822108140d41c0141c4541041300c800001a1040c20400074a200144c00091400d643e441c0041400000b111684100c05000030558200700d24525110702800c4198002c1180b50305100e8041e550310300f61390350680b21380000f0608c801058840d8040f18170924001e4000d0007100540d1030225a00d220f1801030740300c41800c1103a420050b01e0401403c900c5c0581229402c609500c42d640e0100c000c04001e0400c5e034161216011407019a01d04000420340d00d85604900382c9041d0f00081310030104c5100042200c02c0090400c103105290752a142500c3e085034100d10100d0003e16208006401000c0e034903d440c0d0041d040044003400c941c5c06980000000d1103004c031265014024913001e40010f8024018500e8181c1520300c100c010038443e5200c181141d2060400015520307040e0001030490700640d121010106960101784c20001c55402c84d107800180a080040c103213468034444280c111701c8244020302 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 768939892 1250 768938642 768938657
    0xc0c09091501030609081e0c100216080c0c04060605030a0b0409030806120f0609012003091f0b0a090c120b1f050f03090c1026060409351306 62
    0x6014429044418289a0340120415100007d0792101a13800a8841d240300b07005804052030000c2c550b008490108144000002d51118256140016504002e4a8001078400c510072103036503880781c0c80f8800c050142919600c0d05c0e483c1c0f160300c400607104058401400345044c120b241c1c001a4020304219081790049035240d2000c1000380019240009000168905103d01c0c8180902d56a040d4040d82011a042c02d00420b0b4480072040680e080c4000d03945500f06a00c403000740700000504c0441000e40e0310840d4400724414000318002034140728140c0000c22078950b502002403005402007003811012955840038800400c071140003400c43c415075607224404203401d0424401d442d200c4c01c1140d000000d02c09202ea00c90605c4201140d803004403040c2103000d5110f55030300190305409010765010b502031041c5001c02c04001e02076202200e000240c040d542064403161848001103403a5540b1007076048d030680000501d14010505450072050740c0500e400f481007041420300100528213020f003600c00b00d040001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 768941142 1250 768939892 768939911
    0x90312090607120816170a0504050f03071a06030a020d0b1509040804060f0212030114040605060c0c09070c0f02091b1215041e050604060b0c0c090915010306 69
    0xc2082c800c03004000c002d050006059400325400102840c0240150b120030350710100380f600f00795800b80080b05290745800c8200c00040842c10f01d60000d43d440351045064686007020800d0071403454210003012940c042c407000c00c50780d968a000034442e40c0803001f00c00902d85540c20380c020034030010380c884015100804520000319210508070b059040008060001d900394a424148005a034200d802118009204160b034185001d2000540680c89100e09500c40d00d180d00c1c000e0040d440c034011294054025840741d200107038943c2c0d908090840c1c00c20f8207000d0100c84080e5010001c0d048802420307102071021800c180d0b400301c0c03203000c01d41d14466816104690240c031480d0703505076000000449400c013035100003460413464540c00300c030600840740c03010701161180144040000362000c94100c0d45060003108030740340880c28a0340085421203005800041c0440e02c03243d081000d0303403000c5014060346d4001c0317004280c90b0400c2c491290b4440c00d81c001802c5084450540308400c50410310010b08110340f03410110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 768942392 1250 768941142 768941149
    0x1e140f0303040503030a0903060f09031b0501140f0703060b040b0a0c05070e01120501060515030406051003080307030b0a080d020309060a03020d02030106080f0717180a0503040b130b09031209 84
    0xb940074060080c2125254000c0e0304008214a03064001142c0d4103050a02d4810725154901036585030b1035060321604031607690034051b8000c2c1c108980c030a0700c3e10364032600018440403d602456001342d00c5c802191541d49042c40001d4196041c9500401e81042c04020030401c0b00108015a000c1070f009140030300300c3c0d614a00b04140b50005603000040e240205100000d03280c0040350030415864031800082c003041c1c2e90307002004044500e80580042c0d1240402c0081c0000d6000d504c110342c13100e0301e0901c3c10380043c0c80e9111410550411520000429a0380103403008610744220404002c1c03000000074003d90b810440025101d0049840d1a030042c0c401103203da1046010381c056440305105450119207030342e0340306001461403030143e60741c0e072248060f84041440b1034801c40c2820203403541c0c41076085081e00c903225001044801d840c2240024010000039400007242480200028005c94031415100c0c2115032950107607000d030303a0258005100403c110070858401284541c032881680001503102d403505c9021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 768943642 1250 768942392 768942397
    0x50a09090204060315210807080d05040503180603060a0b1c0c0c02090c03090601061b0c120215070b0c16060906140c0901271e1e140f0303 61
    0x305803a8004100411020307416402202d450030403503c03510503260780e50702c1d078144040010345084100d00851480c0000c21140d2000b40030541c400c40b191032400841071418012a041036034100d41e41c0c0c10028060b412101c42414518400f001240c25074550304001000500c03041082c441c0c041c0104000c200a0006000390407105194070002a041c450b654400c40020b00070101a04124820340401c00400d58400b407250550f071040b03803182e0081600e642050030503100b0500c03406507144000d4540307100c6400107110000c00d00c001c014610a140c0c2c00c180a20400c03980c110b00c0000b400e0002c405106c40c8010134404103469070000b110f92000c81e0703141207440b81c610f420030700300038050915810804594108040c6912803401188002c070441d20544400c5119211840345008190014007003103203071000306a09000c020081030000c03002e684040d50322240d85030b012041d060500000c080411040018101350800e0740400c556110340c01055a003010740d6902c400d0751201180740564400081c40006480030002c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 768944892 1250 768943642 768943649
    0xf0102120f090a15060e01060c02011d06130b0706060902091f20060f060a0803090918010c0c03030b01030203061e0d0c08070611031305011d040c030f180302030406050a09 75
    0x904900380b5100044e5400580b00903c128110b0480002c0001403081c8a540c50b07902035541656410070b10940c1c0c030082a844000f100300796901100401c00241c0f040d801000900c000c041034180e664a6031602e0524900f154400e5024002c043c4c010000d8101d276a40e1354401c1c140101f05804003100c505203800f812640e4101030f030120744400241d008800b5100000107500c80c465400d907024880740e95954000e01801030403a1250100701c2d48103102e1007110b464400943ea40c89640f5903c6000250140100c46080d9040b54002748045070560b0107c1c2c0503d40d15001307096070000c007801c06510b581010380c00710f1012603006c8800060400c0c083e50200c2503a42c0c1e00083c0344d0080c0c100909504040d02c3c3c40000361a14107034407030200402d10401307900060f0403002c0140c51240b2a98400150006c4c0340ca80199003240c115a04104421000c1200300c241d9502e40c8105a500c440c0e55500040d0030350300c580e050084800c1780c456203d84074410000200001da00000b190240c3d11140703070594407600e00c0003007540ca030100d540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 768946142 1250 768944892 768944903
    0x3090b040605160e010207090e030c030706090b0c040e0c0714061008070611120c15012709051b0f042a0908280203010213080f0102120f090a 62
    0x1028401440481d030011805070303e0b1240b0402c0c081040c0390040c2d0305003500d03483c41400358200100400c0581e0b49036100f00e40c04c884603425170b13103001d041345055411a0311070300080b81d0f41a41c403003018080c0000c844996510281c0c900000740b5060811080603160300e0014140314502d0000aa8039003042483c4d645103e41e2009c1408030f03602410410344200c281d0119010302c1d9030900c101c2000081951161140c4406a6088400b03410081ca8030740041c442540848012040c91281d40c045613400c640000b11306009082e01c01d0480740ca101110781d224901d60152800c40079840c109100c0c07001003040805c41d401070a01400d2a081800040c501250101085110080d449442e14503a460341404040191110926040300b0340c00f0090b090805440511250042001aa02aa8011034043c0380301001c0c01d0b844658071a0700d0000101c0c4d600090990380013001c1d180903000080c80c20044003204200b09085082010000d6081c088004400b80c081100184428100480c46021500d05138090007041000c0381c010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 768947392 1250 768946142 768946163
    0x11060d020d0902030c0303070804050d0314030406020a0f0908060703050a15030b1b0720040603060c050901030b01080114010509190e0f0a0c0503010611010605120c01030f1a09070309 80
    0x160840000b04081d003000e038024003e0303140d810480e00c0c01000326034580d54041d50541c1498205000c0c1308901402140440034080791207006483e0b020580003540c070a0b40b0400000da40c03101d041f03100038800300d03040d130900042c49200c03581400103000221720181d014485242c00983c40e51040c0c448409840070004030860340440341000700500080d1070405201d00b02c501b5810240070342002d207074142482517182c05018041070303925a4100101b2203442d0382000100a1001c41d0103a07c036210002162007550b020740202d00001030500095030580200c1c2c95020302420251034940c90980b19081451094800a040003c00500c101c5a5650b0a90804c13034401001c68400140751902c14910003d24155689100c2d90010000541d004503103003c1c4080110b00d541c1c40f00c1c116464040c003581e0070019088549899500c1d02c0020803561030703070321071800d051158400401c800c000e260700140c101c2348181030705030300c1c40c0c20001102003400d00c088440c1e00d011001d6841014595810b48120002c00b0043c10081130120310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 768948642 1250 768947392 768947407
    0xd0f0914030c01110f0a050d0b031009020117220c0e0702151305100911040c02030a030e0303090c010c0201020f01061206111204030f2a1406040f11060d02 68
    0x10103450310350410701c000c010000e1304441c000b2203401084030790428803c4c10440103810a1044015100201800d0b0010a0009000c0c00003801e0442d02c1c08071103543c0d99610744203010f43d81d100951007103a020146600c2d2850034010004401a207140751913084010303040500d102081415030b6400001d262200020440c0d052203003000b905da0100c440703d50382c4004a80003040311104d4020711400a158401c00a2242d002a0000d0380064124448140c6482035a140041b98a032124080d040010f41c19034051a682c1c00e001a02030100c0e9000080c50303100d40e0051040090010000482100d8070009080601d078042e40c03440103e14220a41413184255402c0801c0003a0310b0746071402002119200746014001d00040d04120001e9005003003607084521103410114012034054048000c3e181040e19082d075580ac15079040c0c078003c02c01c0320400d5500ca2200d890f00c0c018060105001c902080e140000b40c583c0d41031a844411a020140344040c1080d501940b5039400783ea23031001114200c50000d00190f40ba83c02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 768949892 1250 768948642 768948683
    0xe120301030c050f0303180120101d0703020d020f043306050c0d0806190e180616050a0306170d0305060307060504091517100b090403050d0f09 63
    0x1e0511a03d80aa241c41c031000701c140c5804010b560508441c08410301d40701d00c0d004011107103684a0358402d010405100903400d2010310920801d08401c01008010882006c0561090241e8412480061031600306560510040c1d456400b8002e80e140c04603245410344080000040040040080b00c9000c0138161903600360500302c008041031a2028170300300e440082d96822081e20316124408ca0380400c1e82209401003402d501811119411a1000d4260201c1c0700e86070484c4280c02c18903400411315440a40104044014000c10f01c01c1e07800602c41c050070f4141020303c0d03010741c18004641d03c18207000c3d0200d122020188241d21040080010817500002420010310040d118501003444c000028184070001d0300900300004c400c2c2c2180c60540d80d027443d051030102a00000c105000da0781002c48401c41f000981000ca0415956030440030302e0241600c8121580362074210750081000b02c1c001d24164040102007a00902070700c600900302140801c01c8506600e526000b84124200146003c0c0010030303031400d290 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 768951142 1250 768949892 768949913
    0x6020c15070207081506010f020a06054206030c0d140a2d091a0f060a0f030b0708150a0303030f0606030e190213050f150907080402040e12030103 64
    0x140182c007903508440e22091000d85a03008100508800440140401ea05500c04c401c82800103490344140d42c031054560352054283c0c1c200b0f9820001a000d000039000e040701d002180d4039503031071110b1015101010000240b04100c2040c000045c440e5801000240411039008210f400140c1c25920030040321881c14000f4802200a840f0164128501402c00008441e000701c0820383c4601c100340c06d210000b16171700c401c000d0300420300203c41d01d10a524143c000038404a00d45402075900051005851800340e040c021a101d056204a41000b0541c1c010008039801c2240c05070000101d280402c029a00d201040080480710000c03541c125200000010a159240d0310051480b501e000d0300340072595881d0f10131410307100710144140079034100c2d1955140034803621040d00c104900c00781c000740cac028620a082d101100c108407403004101605000308000d40d211503c1c503400000007141c0c00151400d01000041c8440402003000b07004a075680010724440904001003000341400c0941e1a6896849150813801039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 768952392 1250 768951142 768951151
    0xc080105131e020312031008031206040b0924120a050d030b03010b1309140319080115081602031902010204091103040f03050901090b07210e0d030c06020c15 69
    0x2c8402c1002d0800d0001981c400403915600180245812081001c3e44c0c00e075640040d100d000541c0494600040c030071750600c00351402c4420f660001c045840c01c41c080c0020f031380300f41c2d50040c0b02d4441c1d00200001d88071062a40300700f01d048042c003905100c612001246000c0d50f01c120b100316038400c19030100b08100c1c000070302c841c51100c696810710403100c0003420b042c02e0350041000300742c0c0140c20a000b102d400e4450b074810000940110b500c0c44c0d1903019041c17082d08651120501c1c40710300700c0940800380d406401205141c014950b03a180c03d810154403050081c0102e0001e045160095510034034841c10600c00c0013690001c0403038200d5003c4881c1a04000ba000354041c0c03203040303d01b5042080001034a200303801980d00c981d03040211960300040c0c65604880550184101e2410701040b40303000304505150b8009001b01500c40c070325008183c02111003245840b00800320142c104440b400341500191100ca000d0090f0340c2c0e05041c8160720700114075280b0081d0003607410b82800b40c881c013031000f4240000d2074046c5009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 768953642 1250 768952392 768952403
    0x403020c120a02180601021e03040f120606080304060815040e010f020702090609070c020603090106030524060d0302030405060d0207020402210f25170702010b010e12190c08010513 79
    0x544000440130480744202c03416400341e04101e140c0704811150100b21498892400c042e00c0c41c0c00d450b4121040404120f4100c285c542194171807840400115100300c4016009050085082c50301c1c0040040034210001d01c000035104c071901c0107108584440e00405200144880244041c10282100000940221900ba440746080c2400301c5c41c81d0800b103055074001e60032503481800f54a25602840030503480a0f01d112809d6588074030000c085407040c03001500c0c050200c4040d0300c1120092403010304545010304014892050254038200080c0c0000484044031416a400b0341c44000410700c2070001d00800401035005800001c0c03c02011200a440303003c1c0c0c44c2c51303c401400680320300107003c0951104079540c0b0031400644d81c031803d4115560085080c4106c1e580390101c030310240d040e0100c2901800b03403104800f50703440d290603840b0b81da001410000525000d440402d03064030301c0003c1a554400308150b146220011007200030912022141d00c5c0050544180288803908041e0031110820003071407401d0300c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 768954892 1250 768953642 768953659
    0x8070f05100219031e020906070f030f0e0f0d1b08010204141207141306090c031401080a020a031211030408030403060b0a0e0601110c0a06030923070603050403020c120a02 75
    0xc2c00c0d1300038401c0b501d4144a4071804a8428201149103009500604c80d081d03003c2c42c00d2090030001030000038660031244c0310707595010701100c2c038550140c40c0e00050500303144984d040840c1241941c030348100f07807450550011581c4490141080200d40300314426000600ca43d40001400b0625006840c030030216501c1c1652410301d03034050b0b50741c0390341c50741407502845071400b020000103403061404c0c2e541c2031480700c40050006500b03542d641080701117a080c0c00c00d210100b501c0b45010440b051390743c2c203807500400140000d001807025981c0000c10590f19400018002003000c88100045072040c07044035108400003040341c0c1e42b40d4480d070101c1c0e687d401c54481180c80300d0070200c01d0280c03420881104e20845000351850511511202c00640d6035040c03002e00d101051142c4011151035a40e0604d0800080649440001d110142414003260030b560510b0001c00c901c4d54454041e2030760400049040c1100c0007072030300240300c0d19940ba0407410b01c5945410194802c4402c030702c0340100140800d40d03641403882120310786d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 768956142 1250 768954892 768954937
    0xd0203041e12030e45091009060204091d0706020304180e01090b070503100f260a1b14040e0601063f0c0f0203030105010c0c0e04030207051e0d08070f051002 69
    0x6417405011a8502080d070800c01e0340d01c40c6a00d80d074000380881d6102c1d4002500703060310744107060b00310b0311042d80c80514006c5070000c0301c0f410a000d1004501900c1d1620180d8682803c01d040303c41c58000305800300b26529551030014842413001e501141c86581d00c18809266414420fa0041140d08182c48003680b903d07051400050611a0015200c03c032107810602c1c0740842141405448401d28100c03000180e40100204d107000600c0c0500b844a26603001d0011092541c240210442c181d40601c007160300840c98a141c80d0350440c8002440d0381110160714040701e03110720071002d40ca41e801600c2c00048400001c4004100e580c88218000004640c44140070444041d004c90101c0d4030780f00683c000c0016030810801405154841e01e18050418043d40b103844005a40b81003c940c0f142c0201c41c241c2c010713084103500b40000d180c440121900901240d84d42d401758000030000900103071041500038100c1c007000a45504000e502e0050402c103907001070a0742c0c50700c1c2ca4070320840c001c0c4d407140d4031403104800c2806145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 768957392 1250 768956142 768956269
    0x1020306010f0807020c0907050d0c03020d1401050a091e020a0906080702150114030304080312040b070c0b06040b01140c070f051e210d0203041e12030e 67
    0x113840740c48650700600b8032000400a018581c44054004002c2000401c898148c41d030b00c500440c0500400c60350016510380c104141b4208603100e1000c2a410001c2610041040d980c5a07541c22003560120500042c1c1031000300c040842e1030b40103030a004045070002c1907198025801c4680001220303019245e0030302c103a6840004a803554a122018000a082030b0014010425074100c3c01d8884d1602800312840c0c00c0c3c40f40c05940c517540140c2041c100503c000020001003118281c40c0c19040791060500354000405a600d4110000005008601840c0d40e1030418507540e11440c0511030344041c075542140d07102d011401c01134880040d0301400080741e16503640050316040690401041c10300041e06030641002070010848508800d013646803c030a084c000d4560080c2c41803260303043c1014640c008507074441c5002402100c8010888200c3d480110011042101c42d00b4050142100c0380c1c540f8040b105560b100740007070320705442c0e0b58407560b48800020208030480d02c080c05200400150030440f410010201410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 768958642 1250 768957392 768957407
    0x100302210402130902030f1002040f080d02030d050402150403060b030705030309011b140601060f08060415092f0a02060f01030c05011209061104090f0b0603071d040603030201020306010f 82
    0xc3d001040f1802025010300c2940c884d2801d00d1004042d10701a2220340b011394505036071a081d0001c00c0f540001e04000c040c2500c0310820051007907901605050061a50180d124001c0462400159032500d0018003159104411600a0100c900290b07031550340324100840141401d1054500a11a402000c5401d01d000030694403c24016036803000304500c0008a81000644500219110182c041001c2021001031080b00c0c0a0401559081d000100290004208003070140c0100c0c0150324201b0714903c581001d40038003054038003a8030042030031035a01c030541c0300b24100e6882060000700c9a11088038409a00c0005050603915942204c400c4d868140074507840d52020310005000c8051100204070950151104030103140103074000260044c3c0c0358442c20b040c1c6030071403010002e003803000070144809450340c0300d40035001044141c00c11468183d0f0022500030712000c0c0420092200d241401b2000d41c5441b042004419009801800300c00c1d42c034034029001c0e400580d03040307011032120400c184a00c0e10500c1c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 768959892 1250 768958642 768958651
    0x1e050f0f0d05090c2107030605040602031b0435070311040f063606030b18010507120515030f06180f030a12020d150e011a091002070510030221 63
    0x24942561010a4001c40305c82008103101e40c0154040000414a070384200c0e0f11440c000c42c03000d6540d24102502d20380c1e2401410346035000c1c5c0814042031207480607980a01c04d041440d4442d0f000079900c2c440340c0d081c803000740d84440406881b40800c00300800602020850b01d640e002e4500b030003c103c110084005446041c01810b4070400c0748111140d039070b040d003020400b0050344c1c004902c00080c2007084113425240941c10559142861000f4068120021a0091031001e121002000a41000c000080000d62040c50000005403030b000403030b03071000ca0076400f0304d03496000404480f05084603485003501e500c01102d1400440422038015054000c1c0840c120100d070a03800d02542c03814100300815990b0559205200403220f030f080c0100d0103c0421072051030240800d000d617000003c0e180401c0071803d500c0580150078a450700307910810f070490003c4140c655898007250040c00102c01034004902d030408541c00a580415141c13103140c00c280d0580c1c010710403c0000060010150010541c16005820548 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 768961142 1250 768959892 768959899
    0x70302152716052e0c02060c060f0a020a0c02090c0d1d010e0d09030308040c03082a030a02072702030f100f18020c100203010b0909010e0105011e050f0f0d05090c 71
    0x303100140380300d40c04d10800c80b240c085042c080d808401c25004180550440f420104260f0712260620141c1592003420035841b0710004404e604d000b8551b440104440c071035007402030180c0d607860081411a007035a011b403103401f88100300c1082200001840105001100c1c106c03080603520b88456690840408212050320121503150b20020074a95170302203030303441b5000b04244d4100444590100016480305c0040038110180d488403040d200b4a00108a800c0d410445c504129a10400c4000b00598002c101d601c101c3d800c5000c15220f03540e5008100703e10010300306401011510000401800800b0103030030a00940a0310a100078180e1030302c002800300c02860003011001111b4641d030804d202c0541d002041c000c1c1e0b10300306a40c1d4811450900400b43e8100fa00032400d1020086000c81c454103010308020700501c40346103050001d5252000192549808060b03c0011001010040b031200b800b990850f194540c4c9040310540d1400382980c1034840b41c11008601524908040124104a1f0700240c620640c00000307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 768962392 1250 768961142 768961189
    0x8010e0402060703120e010c0e030105060f0f010c0302010905010c03141602100c020c0306090c041103040c03060b12071203031a0f2209060209030d020307030215271605 74
    0x94400703542040c00c9294544907031b03464100134421030780280290b41408005490790303075001e09078a04241c29540003c080900a40c04010300c42c10591f1403001c0b20307031210820300b000c00314601503040490140521540c050825030030302a10400182e8140d10071000c0d626030030403007806910f442c070032034140464403903004005038040580400b03807400f158021500c4203003500440705554904070100c3e091880c115801240360f008545580707081e06150042c030500e4034000162514602c0d141c0c0d126940040c0c03500004d031138995586079003a4207843d00e0421840c13480b01c80c000c0f10a42d6984401c902103012142c0000c1b400281032050343e1100603980560340702c011800a0154845840c0001404071100803050103100c011240e180c6007524810510515800601401e000351b82e4841d484141894030850300c40c02400c541c0104074040100c0c0c0c3c0440c04900b0b0034105c0485440d180c43d00c403110031a42c0b011810910907009414160800301c0c100141c0042113100266501c400c0e2985c0d101003150b4081d000424144001c480c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 768963642 1250 768962392 768962407
    0x624030507050405120c09010807060c080703090f030803071d0d02150d06060527060a14040512030d0e0d0203161518140303010b04030206090d021c0308010e040206 72
    0x3508125400039103031505900b000d540b540064070f1015418440c40c07041c1c00071560440c80d400c05d5030309180034120100082524034a08500201081e03030a0101420401002ca00c0c40101441070800e40002c041e007a41d409801903c81c1841c1b021075009496120200304001032800309104035002820081c0401010010080d45a07024000000007400c3c0219401d441040009184d5040e442036101600c000e903106500caa000c0802c9060401e06400c00c54a000d0143c1e10f03150031542c800302140c494001038644003405030703035015426a080c043d036045035038400e0f541501542014400409003000c060f00c80030900038880ca0712034013078880d90700e401e603500182c00403c00c01c004140102c42c0400407500c554040b00c00032403040001400c42e01540410701045845202050030b100e602414080ca041c0044051450341d4034040316443c0600c03c070b120080c001e2502091440c031565072504001070203a000352084028424070040315544400b046000c4010a41090010503038405110042e4492940030304040d162849 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 768964892 1250 768963642 768963647
    0x100e0a09050a0503030a090c0f0e2a04121112330c040503060705160204110d2406020a0203120c0a080f0a090e040201090b030c040e10090624 62
    0xd0203906942600c155081c000c00240704000a501c100c8400310b000908049070b1818140c1c1184da41d10980504200b18000c0c4140c5042c01c2c1c0c4903401c51200051181d0040c8030a410180d14281024801840030300824001100d0001f01c000c803100781e201d00c1002842c041c200007013086041843d282c44146501800c0601418224951202c40300080c22400345864035124660851020f8200c51072a0954004107040210381001c00c01c56812a225050080c1400b00b203441480903140070300710191090f078031000d003036083c50240b604840d18034401e0070007401800131091011003140908852a1000d0810010000c0c03414808112103c155600401414a4000c0f12004d05d007990000500411035000300b10440002802401c010b1483c26041c0300502c0e01c951320124060701c4400d003640010079080703000c020000142c1c0d100380c4000c16110700407440e80e129258030701e46d040d05000796007050121b2516542400100c80742c10520000f124031042040c4545519002405010399041a04c5142000d040d80049201e50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 768966142 1250 768964892 768964901
    0xd0e0d0906030c0c020909010906110711010c0804080f0a050d020106050d0807020a0e1608010501090e130303021b011406031207080901020a1a0412081306020d060b041706100e0a 78
    0x2842c1c4d01e80440e8100040e0000740c026002500c243d1000d82d902c0140c8030400072680100030000c0ca441c1d40341c5080c40a00d032180710b071110300741c00f00b40e04000c0600055400c00c2440d0058602801d03600302190311003100707862015500c803400002601d05204511124450a10502815041e100060400c84140505664032240f40d0007000e022070b40030403c00c02c0410389450180085118002c07880303100c1c0c48581c00100142c00501c040c0c01540c1000344a00050000505c002803998000c015091340c0e8030807500340d0608900900030b102c00603d8000d54101410681101500100c9042864241d007050640340d032000c040e5103c61905100703005240c18003400010907410000350040d880180140d034500f01460b524100c11a445000320003001d501c200506c03060010b4003038640551407060034040281d091948a20014400349600103200790303000100844541c050760403a900030318403804550348894607031001480c80e03081038104028510a840c00200801030029500d0104c03404165203003803d4480000480140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 768967392 1250 768966142 768966161
    0x2030a0e1c0f0b010504090b0103030804031e0509040e0304080705130609391407060b03070e0702100603080415020313030506071d1c050a05010608030d0e0d090603 72
    0x18000001e490754424000c500040c580d44201c0450203030803450302d0719545842d81a00300034000d51400c102440000c4600001c181540e405040015039035503545011180b02c0540c00c0340903d041c1c0008004003c0c00c0d003000180c07982c00700480d002e0190f0303d1400541541c9002d60b103d01740d40355001030410401d80c10320315806620400310443c0890300d5a04c038aa0391003580c0d040080d04c2c10030203080395280d0458a840070881400701d880071401001091020380100790601c04d1b8600c1600e4500000c205040100301c2c0e026030001c030700203420348580707aa41c0c3c03403070076131404c8100d41d410054041c1c500304084040081c892502982e620070130407801c0508100c45180154821500c9806603c020412000144c2441c50b07400b0080d031103207006122501e45440003d141c500300d041d00380b60181400002d07203065903c1a09508050108171031540c2c25494a08100c0d02d0088402800b9085500c0c0020105a0080100080540390481d841c1800f20a0460300b107943c2d685180581c400010702030700e0f81407105a200e5000300c02d0f407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 768968642 1250 768967392 768967399
    0x8270d080901050d1e0b012f190803090105011d010303080a021b0a0507050607031d03030405120102030105040c05040e07030b031c0c02030d03020c121606050a140a050702030a0e 78
    0x3c18108013944012107400455200d41313580364489500b40151a4001c40700c0ea02c80a1a1180c650108541d42c81c510003a401c503690364007810b8460381e840540e81040010325031081903468950501860401c24900d610035118003019500308800440c03815951807414016100c4480820416841d40c1c50440da5190050400c1c42030540801400051a001d02c41029008544001030842d0000602c0c20303a10702a155800b0601950081c0840f002180d00040e0210804060b42c1400b50304c044004001b034214840ca8011590080e00c010700b4540c540340543c0a14181d86094800704945064048103a80701d004601c00d820181641100043c40700d44203402c0b405580308040c04440c0e1200304040c1e4155a41000f10303d900014401c1c9041c141907290400004031409200d0a0440c03a01c00503025150305e415441011010402001510050700020f004d01c680d04960031020030001030400c45413000103010a4071140110a06400c080390034110944661030040c51113400071440c1890000040d0303990040000703516031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 768969892 1250 768968642 768968647
    0x50a05030405030915030711010e0304210c170f070e16021f020c01061a04060c0305090a090218030c0a060311040e040c0e220b04110a0308270d08090105 67
    0x46603181d40109800405040c84041d1b200e240c80d1800411401018680090981c10075161080000c00030085505440305030300c0024507500d0000311b03c42504405900208030500c040c80001c0c018480c0c80c3c200c1d0055110005690041d501c00b18a030f076950700940950304802048902044000c0c02c0c114141c0e101c100640185d411064502e1400100c40030201e90400a458000640b403916007000c1c4078000142007010a1030000804100d022501360240d4025002841003041d0410103160180e400d6640c0914000c1c119a6425201c0030248041d40040d1558408030b504440c4d001380d0b5203030100700013a0301c407006480c600041d8030307051080f40641480040042e1007c2c0c02c02c408074149100040c0148528011240c2000c9d1070300d41190303884d0245006040c10108001d00c480c9135003001b00001c4805c40c15800c40c100f1401d07500c407820f288074a20850b82c0c0d0b440e8000011080042088008000f8022070312007051501d800c007003c00e6405284000d1500382c035903c02104407864000440442c083c00b20303c40189070260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 768971142 1250 768969892 768969907
    0x601140702030d05031321020d02010504080403171e070605280b040b03100b0913030f0513080d0230031314070603090c0506070b0a0c0210090b010e16050a0503040503 73
    0x11f00910703083c0d50611310388100c040182d040c40d0b010400d4001000c01c6100801c440d19083d182c0c41520300903070000400a401101d03000d0700c800c90301000e031040c1e9000d42030482c540111010503158164010b5404031580383c1440006599102443e131000b00742184072403803480c1c1c004024a404014104020000d070b00541e501030703034035098408000003205511000c200080240f45002003007141c030402089221040b01003c48000000d600c00c0500360a1081e60a000380c1310307801c1d404081004442604100c0851055503840c1c0d40c880d80c00600500500000304a103070050b02d103069000301026010b001d160180b0320030001326540784e188050340c03140680681c0a800300340c0140b81107942032004650014000944400d000c105015182040f040144030850710b00d031804841d551000e03c0c003040106034001003952084a01c010a0090007001401e0402d0380f4100400d20451900c1d000c01c41e020700034000c8207010304001603001140b50300c0181303082c8106d844441c2070488650003142e440c0d000030000c4403140070910502 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 768972392 1250 768971142 768971153
    0x60f120e0c1912030914060702180402150a0807030b0a050f060d0b060403050d09050613091d030d020d0e1603080307090f0e0108010f140711150703050601140702030d050313 76
    0x204030b221310942d5420b500c1494041d0340c40d0182840c049182c890b00040081c0001a6604601180030358003901d141c00c81c50b40c07035000080c14508400c0800070604400640400c0c81a0702918242c0315500e02d0b03d0412201c0840020301003201e80c00d0107034581040d41e03000b0300c00151038040b0107400030007c6100003251000b00310001c2140c0b60000e610807038180d402180580151034215400388050401995014241074544103407841d0f40446119101c2c140b96039000c0000510308001030300590598507002c8070b60303400041d01424020340c00803901d0f0b0b41151a1050141c02c500000c41c4c00d000ca403007002031b1103e6250031510f50040d69032000e084101404000f07240001c000f03c40303103140002080c403a8444201507240070004c81c03d4550070f1200b01038441ca00030551042440100c4415007081891030701400b50091135100600d0911810946080411520100300c00240d01d0780100c0d200d03200a1340c441d0740c442841014074105014201000b941a002030300f0310441c891042020715072141200000c80c16070a4182c0701e2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 768973642 1250 768972392 768972419
    0x2030606061b16080d031e05040f0f05160f0f2601110418182004140612160b03070302090402030907031b0f0b03070507020a060f120e0c19 61
    0x4420003c2088401000344c81303020310007690404483c0c1424090a01c940c51031256011b43d154000390160ba0700c5000c0360500140c0c20004441d940d201e0b000114145160910540d00c42020b2140c5548105024000c141d0000854020007100c086c600d80500003800c0400c400f00c0142c4045200b000c9002da21400c4614240900070078282500b203a0130305907242e0600000030060380c00c00381040b000500349075403290030702000c6001d2015140c010700780c0040c82503038000b500705403841806c03001c0c2d02a0415050410080700b1100e11070007004215464807880c1360112040342c4600500c0514020050012010042c04d9515801503500146500c0c006242449442c0010201d03001582c0e103c1d070a52100c0e03014010080c041050034809115262500d0546281140712103800c0d101c1d000d801010300c000301c0072540541c0261700350f0755401d5004004103200303502d6007401003052826054240000d07415038019108110346114556410006001810000c661a4144160802c80c061900c0c005404401c0c00248041d07031110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 768974892 1250 768973642 768973663
    0x9062003040b10030305090f0301061a120a0b0d0b0910050406290a031506030204060810050a020a080105090402120d0203090117070c0b25050705010f060302030606061b 74
    0x481030380300c1c105030420020480004110020642d562181400446d4001d0291002d0190840d1541901120180402d0250405900c601886c41c1014a031100c000c2c034603006070091301c820714501012959a010540305592040138515009040e082c2c01d900480c00d04000c01d40d1240c2d4150864400b00c404101203000c58900f1902034504c2565002e440d007211040403c03204242c50007090004982006c0c074005801c1084a201c010031a031070386041181e244c104d58120b00000d60f00180100880b86d070381c00a40d80c1fa0014900741450461a180003d4050412482940e225000a84d0b0b1115680e08210500c410100c0280003aa8002d100c94180815218200085141414581e02568441c10000000750120050311051804807940c6420428910303801049801d10503007000c0712100d240c4070914020200c0ca500041340801f10000c1e2030210f501e5401400405003540710300001c002d001010507460003141c0307041c00003d5242c1c000030b0104600b8a004809800d0206209901050240c6048066071801d000d40c80d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 768976142 1250 768974892 768974951
    0x604231905361e160f0f02060a020c0c0301060314100e0a021e030d0306080f15070c1b0902180910260114061002031312242f030a0906 59
    0x4213120302c02e9601802000d62070060342802d8040c00070307045000e51103200c01010b040300c0d01d901041901c070044040154031020203005d4001c1003d00d86074106103041084030340308030907540720328902d003400d0503054443c8840d020720b68405021201d10b16070800c005010143d084803a1101d62220207880e0f654280050020341c526614000381d920b240a80c03150411220100880302500100c10403943c3c00f150401240c1c1c0a1070500c2c000e0b400f4030b00c41c5003526002d904c0301480f10075000206000704204c410b5600501d000118401056a07856071710003004440d40d4100c4041507000341d01c034000c0001c1d8855a500005070207101ca407114007011400c0c3d02500f103c1402c03a401031034040880c00e0050508120391409842031261000e9440d04000340c0b4454a50401e910901c1e00340300390f0715008002c0c801501c030200c408020120800c81040500c0d0142e5002d000c004051240d6810154400c1c0c0070082d50703035415404509580040382c1190790f10010301d00144410074050785d0258484808994000f82060001e10846046 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 768977392 1250 768976142 768976171
    0x1a130603110303071a2a040e1b07030305100512060a0c2c0a1a1306091d0a020403050604050303160e0604231905361e 52
    0x60800191141034150124040e400400441c1e002c1920300a16045c50240303a2135002c41c58a41da290890a5103201c40f0102d4101c50400341c50844000c52002001205d81107410031415440304003d1580c404649100b0000201040003001d0009000c0d0300074960003000f41204001d201e40d07500102d135007400c484d8080440c2d504240204000c400d03c0d403013244600510340c80c000342c580d9030460103003a1824100c003941d0020f00b04802040c00642c1c070020741074043d119030034000450040401d03021946400007502604c011940002c04600c0c0c0b40b06000040c02c94210140b039416040600928039040315002e40780c000c481d0b400300b102001089082083c1ea00581c490001140d5900d4202010302c0d071500c0308030403141040303240101c440043d034440d025101580c90340001c1c86483c0c151000c0407020401b00015940d0003118441050030300070f241440d05e60448905840203440040b0b0b002103000c8200803a242010078140210030102c92100620066621080b07950010030315203042d9481e0085d42c002240d14000000340b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 768978642 1250 768977392 768977399
    0x3050c0f2722110f031b13120210031a040e0a32010902220b09010806011a040807030303090f150b0406060c0b180a080412050601050913061a1306 64
    0x41c443c0d030f14240c100480507800c20888240e00d000300c0c40017800d083c104020104064155201c00401c464040c14038032054160030340d481c2c100075800d10500c041030740304801d8049032400c45402030007152403101c82c600c00074003a1405481000024503400040b0340f4103201c0c0c1cad4050000540c032070800c22103a20507101c28440d01941c102218034007039001d506000d0340c1d90400d48075131b0040c1c03242c0214034040c05455086207014440000c6400c001e02120718403d42c0503144100000d031081c1c0c003080303440c10b99075501d00c02da40000d20b170600c235090391140784070b60200d6501040080001c00c1c82039002c03105262046007035448030702983d103c00920f103150f0350046041c40c2e90780d0150502403800344074440007007101d8201000c21000341c0e1140300741410028100715018010551940c0d85403c1404440c00d0160302841058590791203880003a800c850003101101d0a02c100400899140b4003111100c0c402c14000a0b485040380c00c50f071f0b0b46c401401c140d85071200e40b0b400380c446040403545c030107410324120010b503440090308514 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 768979892 1250 768978642 768978709
    0x2040b0c010501080715080a020c06070e0918072603180307090c05070f021906020319021504030c03140a0c05070e1302060903121903050c0f27 63
    0x181a0304c4030180c1e50041100300440d01044484584590321410f08074066552100c124000e03203d130000d1303803c140c010502007212868010340b0600d134010040d0303034000b52a52800e21552000c141007040c1da09692100380100160f083d0003600320305010089035a0180e0482d06501246580c105005604203051a00072650a90608004c040c0082003800e03410b0080c0841800003070000e1050150140800c68a0503080b01075494120304a00449101d0440148941d61504025207940001802c00c030310703000b00d4860281440c23000070109142000c100f50725038151100ea130259001d80e41030f00d0880c2408504110585103c41d1003001e064800714039140c0c6030803014035180007400c00c02ca41e08084100c503922401c0c00f030080100074240074010350680c0c0c0789541d41074910010f445c100c450350008440000c00a001e10340e6400900c61192990400e4400b407010ba15840c1c52038003240a1800040d822030414800754a02e4180e00c030039121071000d52070b02b45006e01039503c0441c0e80510304c0c031440c4e4241c00d1300240b84d10807040d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 768981142 1250 768979892 768979901
    0x31a0a050c0910030b03030301180b0301020901080c070f051c02010c020d0e04090c030b0c270f04020702040e06070324080a06150b1207030e030726070602040b0c01 72
    0x10044401001246460100400e0600895250743e020708455441c8800d118045d5000c443c076094010202c0b500c1e9a91840514500c5000a0b141030426050202000f00e80c10f050007901c07070340c21050b114601d181d0340d0701841c1c0e9030f0343d04120b005603074160b40c08400c100803a50501140350f0481c100032000d0000482e41030081c1c29a207400c0155011540125101c0303001c03036480300b03015407460b0313040300d000c0303046075041c18a103400e8030540c0c0011344040f0040081c4105280b02c1070080c00b202289000c1282c5080030050358050341440311000c2904a0380106c000c4a261406038020402ea6200910015101017814581c61400c03200b02d8400011036901c1d15038210071a103c000c1c0548508250440e030700ca20b820003d01d50b40346d80009800815240d02c0f04038030b40b12000141c110324080c0001c0060302b03880d4010b920f0301c5218210240c1c0c00340c006c280380c00c0710a1303007003c0c0c044100c0e0035003900b1805602072000010100203c5034512a07c02c40341d560f003031202100058071400148010020b1001043c0c6540648107041d00310b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 768982392 1250 768981142 768981151
    0xf0c080603060907060809100e0f1203070c03030906110a0c0b06030d120c0201180c140a21080c12030a0b0a0302090a05090c0d05250b0f07050a0507031a 67
    0x980c065010030480c004001101c074162285850030300a55150220940d08d00804da841203020b150034101c181c8080c80300000c6001c400000c010448100d50118441001c0c2072100b070302e03010006103d0481d5480480d000707800c040b08040c403c81d00018907000390b07029011680c03c03a41d190800540c0c90a08030044c0140540c0c503581000c801c90103400e8890f140036000d88100c00340d6400006458907201c2c041143c1d4003c2d481810300d084120400c00b400d4074540303003500d200001c0340201480c1e914840c2c1102e2490502a040f441540d242400003003c24649889140c2c50f14200002210008020425482c0c102d4050000e4010704055001040e102e0802c544000103980741149801d000383c50100d0204056641c042e820741d000b00c1351103000203464076040803c84c00c001040501e01d070442c041c840500b04000d000a02806e110814034070000c208040140203081c6407059108101464200340070003140d40d6600d5005003080e030300c03070401c03503110008641d80c0c1070030080c996205503404a01c1c00b480d010501ca00c0305465500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 768983642 1250 768982392 768982399
    0x1a0402010924080405030405041e050c0307090b0c070803131409070206040f1e0c06120507050d022d0304020a060e030613111e0109140906010c150f0c0806 68
    0xb0004007040c10b08900e404140620030021980c01040503c0300c24802c640180c40082d00c00c3c412a040348010104c0c1152200c0e503a03030418070f0a80004c5104511005a9000310b6056a850150514240190b0303140c4e040915040752038012003e0014900d40c0801c002e14801d41000e28908001d841d214000041d0210016800c0c09607601c4800c1010f810790120b00c0550081e400900c00c204492281070120040100245180020343c1403084041800a5140d000c01224003076629000c0e140080740e00c6800f6514291034802c0414424040781038416240e03000b0300115502d403103000103041d01c45502c2d400d04031400c41502d120082c0001c180015400d080801902825050a0044061005002003550761500429404015085030908810002906980140d6241c000d00c640c000509510046860f23800d01c0711214082a03610070700240c1da10b0030414088041c00e0042c8484031039a182001582c0d0280e1121044800800752300050106401c14821481120301d40030000410907895140600001b1025141911 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 768984892 1250 768983642 768983669
    0x1e13150521070201200909040512040806180a0c0504020307050906030a020912280c03061b020c0a060212030901230703050117031e0f040e0f100815040f1a04020109 72
    0x10217980ca00103e503118901a03580c19038075500c034200141440042c100580c02444002800104510300040450003021b0b0181400308180d03102400554407249030600502d0640c07088010003031407070310754090765120121b41131040c500440030b40054142d6000f203440440c9580d0108a140d020300300321003e80b45014540008020304012f0032a101621951200381a8222001c0740c002d1080114034900e1400466124800f8014002550380c4081c7e009440340254005101c1c68074040c0462502802110880d12144c02a1a50b5100301e40d03046080d9000810080442d0f480381202e40d0801c0402c29210320110050710f6200311b500301968000c051301c406a00444040d540c11034060a4040040100c2e507208800704d04408204554945240d9240106001c0e40c40040000c20009500c45c035107072070144070354444560400b5541e203052000c800840540150401ca80c08041202001c030301c030280703540d01301d1300901c000540c002d010380d1500542c011142c0c0c2090719a035017500388001c40d41c01c6041d071f1000c0c1ca8203050000c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 768986142 1250 768984892 768984941
    0x1211033c07060c1412160b0a05070e04090c030c060801031109010b0a210e010902041805030a0f09090908120610020d0e0a0302090405031e13150521070201 68
    0x3d001072906034001d00182128104901100401c1203c0b6490400480306a85ca8150680400f1840a5103400644540720400006800800c0500c9214490051901c0b040030050007102480020700301c0840445482d1004a00070022030301003c0b078103000701541e80e94102c4660451602030401050180e100f4000d56901005015407440941924084d140b00c0c500028513011645480c801014200c44007481c251400780c4003603241006410000d0124004d0703600b445405004101d800401c0043c10000e8182d8006224058515206007060381c1c100c0403d2808813402501d9400d00e104903114248101c501e00c1002803602c0c140340811141961004045038000445081e241c6c0103034450035800e04c80001c00801c10301e03c140d00d03074444400a01864020300b004050703151619065580f40d105450300090200f80201d401c901820481c21a400607111041000215180c00c0c0c0859003610b08141144c280f200510641c0c0f0f86568036500b8942840007003814003601c0c2800792001c3d017145c0f4285242e140340005001903c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 768987392 1250 768986142 768986147
    0xf192604030609110d080c0d0215150109091112010e07020604260d09020924041d01090b040318030c150e1e09010b041211033c0706 58
    0x2201125000a40811081c240d46807103141d41400700750441c1c5c0700300c2024175038050000700c001030004c42541004483c0c520f25802816656584c0c146982d1201d540c00e81c0024501c03020781808540b4610040c1080d4040945504e010000c0d5400c803103050300390711000b249104194200031b881500400005640c1c0e1900c0c1007112009444840c0100040c06404030b00c4030901e0403030301400581c0d80713681101107d6522501440384000250504400680c402c420390b83c0418459040d2a805e98218a0300070302410b1035030054410f00014151100c9011704401162024070f02d5040b0a01a60148078030a081d4540c49241c14070700130342104c0300703000103402c840b40800003400060210b20146098602c00c09890111002140041307500b4410720481039007103034000710901303400d19210000079000c0c0b1045039102501d0703880304482c2805006610078189404100a40000400caa01102c80240340010302a9079920414a1180002524100c00d02c3e01000e800344003071190349803844040b40d8410451002e0b0401d9441c05100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 768988642 1250 768987392 768987397
    0x3120b060c030901180f080303011707080712020a03020411030417090303041412030a091701110d05070e03030a0e030f0102040311060f12010906090f090c060c050f1926 74
    0x205418002d9610326a0300c43c0c03960b0b400c0a0020902001b0070010207884004044d100e4000307102c1c181c1c000083c101c842a03070000110300003041d1010840200340062074041d0800d01142281020f98000c05a8030001c80543c07500d000d0341c0c004000013950659242400d01d81001071700ca204448a0550600b0702980881e07503004022201251090b41020447c00f11903000a02100c01c440d841c0324061000160f80c81f50950000344030303811144000d03402c007050b00300c4180850982d480517a0b0b00400072010002c10180700081c0e4400d81e0803c0301e500e8210300030110100400c0c695800001c41c24085070b030f0351480883e40c0c6010000c2a41c0b0b041504001c2d800e151456035034000c01c02103c00c445202d40d0f800315982c5000d00280040c2c4203100180003a58116503541c0d4101d800500c858007403140c9640c03c10103400b00c42d1810b4017441c9019580b01c0307860012103103056400c460403641840101d4040c0504440440c4540c420442d01e030707000c2c1c03111410300017682c030394944200c030317090103803280c640d081645400c518041d40240c1c10b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 768989892 1250 768988642 768988657
    0x7110906181303051207030507080c030c07060f02090414330121052502061509090a02120106170d0c030302030a090b130203100605091801020705070303120b060c03 72
    0x107108000d8001d6103800d0344c3d03c0c0030b880404400c0e0542c400c208100b05074940c001c90301804142d120b02800b520b5680e07580105200460b00514025410040480001c402e58008810744585010050a203036950380040c040e03841080500507000c0b0000c040c00b2200d25103e1514202c1c981c1d050a0141c0501c0607001150080045422070b810b00a445848103801c404040301070324030302d02c80b1400b0051480c0209011401c2c500342043d007440c03905a030b019050031900000700b141c0103c221040c0840580e80203000c100f42d482005106280d1030091600500040c2c03550048003452a44013070002c05d0f103034103055002c1c42e00f4500c40c0e000c09041d0b2110442c07440c101c1c7c010300610802070705840e0150780c0360381d14504038000d410340c5080106010400010800d42400f09118220801c1c82201543d080720560010030064980b64000c00703a120f00c008002c00c01c4111000550048107003030000150034112a51a06810211668070a41c0482e511709007202d100d81c014800c2518085007110039a0400c1a41c2c000c8aa80740100c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 768991142 1250 768989892 768989911
    0x10e01020c0f0a0b0313120512041403041d0115030902090a09030912141b0a0e09010e061f08030a050708070510050711060906010506091e04020711090618 68
    0xb2000080e4454442d03450141040b011801e40d07900301602c2000c40100031030410b40c0d5039800c03040c0740031760035200e01c00b159544c840079a400c07102d03500c540d1144848050200004041072004000014a8403800850b410801c80400c0061520b9032500b6041406805020403103800c00d1b1500708010300690b03401d1646508000328080000d8071840f84d103000e82c2c031800d40d0b40010240c85207000080c0d0400805400381010038400d03205403207011300b00451081302c507216484035036030001000c2c10900c4030900803c00207a20034640c41c00401d014060403a8103007000401da8a0050214002c050303000c6144074501c48000400c0801c0095107400d00200006041d809820002001803000091100904c00c0400c1782c004000b03080f9004001c0f9082061018040007000ca9242805000b2640020541e000114140f4120f5034040c0105241c90010400c02c011950240c3c075210208614030317041c1046884500c0078101c1688201940c8111600c2c403800c0203543c0000400b890302c5082d43c0b198030142c2071090341d8074903040020f48 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 768992392 1250 768991142 768991159
    0x1902120609060c0a030b060d05011d0c04061214072a1a07030902040c0806040b03030405030703020913060908130b0c070603020c070e2409010e04023a11010e01020c 72
    0x13041c04902501003c4030b0954001e1002c991070040185580c0000e04171008032011a240c0324a68081c080074220440b004128001d0034082002202d0203090340e25481b03040cd0b8800501c40c43d803812030508400c0c0a0f00c01c1d500259880d1543c040440038800b100b20300440d85402d00c8503c084903a44c903610815030780440080c7c10708100120f814980260450118582c1c020810b01035003040400c01052082e044403075a200c2c9040010544d00c509010084806446002d0064032680c0c1c110b409001c0d441030090000c014000021545401054552148030b404a10409000b541d82c0107858914440ea10769412080c0700c0c00e41008080c1c07003401c0006c3d1103022120941005070b1038a42410040c1e0900c043c0c2e44c00303a00302c02d4808041003030400218200214190418001001c4071500364141304280c2d200340603072011881d6200210380503150243c0c034540000101c40a41001d2142500c01030031420040d40d24540100b0000c1c0d01c03100704910340d81c0c80341c003a10702071800c1303510500d201000039502c201c0110700c0360142410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 768993642 1250 768992392 768992407
    0x309030a0f0908010c0e0a0518040b1b03040c0503060c03071b021315030210030e030a030e070504090f03020c09090d032705070f06020304050a09020d06081902120609060c 75
    0x1c1000700c2c02410100b0080000322001e14028004403405004141310300c00610f404185460f00c0410b0000420401940c0501c9580f0303582d90307615807074024240c0c0c000a0b541d010392990052514009500c983e1080c410030104c940b41c50289454601d010380b540000c0e260038410424039680c48400581c4500424803060241c03a164008120022051103141c10720a091444140e103107511036010a007180c1c802d4403400c04014000344210110344501482c0410341d00b0402001416a20a400c101c0d2001000002e03200301c01d50b2a0700117021038031351080c102d803422800d00c00300007410303014090032072700c00e0040d5030f504518038252201c251908400d408040074150349859410b01c4001060202c42c80401101961031956010300f403141d55001e180c8200c0d00311541d41d500201d00741e031001c41a9030840307130301600d011201d50602e81040003035000360000607202c0f652000000f8000e941006041003008158900950b407030800e0040c004045a00c21007809903070b0015007032051403240081c40f5580100e56031561b94403020f4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 768994892 1250 768993642 768993647
    0xb060a0e04090c1508060411041211040524030a0b060118090510050310180f020f210c04060803030f13080c1b0102190308070302070c15140309030a0f 66
    0x40210000d00201140c010100c0c8490311315101001800094407101e0241da02c12007040103903540c802c001d03134030b110061004001c07403e201094985080e1080c4d400400d11041c04c00401d0894074101d9100d0754800c81620782c8000c400c100d40850000034000e81c0035107021102d6480742c50a200001c4d010904000502c49a05114110302d0030400240c10540c000307001d6410304040400a1580c83d0146622900543d1200d0751049458401e103007800031215084941c00901e515032042c1d8403241041a80c0240310b0b850b40a110740d032000c00c0000344070b180c101143c0c440f90803000301c186070469144881e070090345001d105005103000001074a500c80c410013890794181d075426580d0306415181480052200101080c001c100f80d5010981184540c500c2030100390b50392b1080c0049a41d142c00c1000d101358a0b015060150200e84a01107450f4081c2117414054a0b0036180d9403020b0001c40c050780000416250340ca6003400c09d40d48140101090501c4100c11030841c200f61303240f03c1d16841604030606c14019101c14001c0280e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 768996142 1250 768994892 768994901
    0xa080412050d060b030403080f070e060f04080f070810060e06040f3c0506011e090503100f0e0c060d022116030b100f0315030606170601090b060a0e04 66
    0x4149403c0c0b148960702c3c810340303203a0f8005507821400b0441040001300000340c0905072920509180c0d541c054004e81c101c0c240308441c2d014080c6044c960b1420000410841c1d41000100c012420759002400e110f40b4252040342007000c00c00740c0040850400c4030404c5900381e8140a150003001c1103a002808005c2015031000800404210003002044041c10f050000001040000561241407500400c84038800100f81165402ca4095010880704c3e40142032240224544107030070f06c1c66080c0329821503200c00c0000e141050344802425210b0312000420300482c200d00a52907189014002803001081400002c1c3d01e0340950132440c900558003140c1214855240032000760718120450809809080034003483e04e03004240440b41300840e060075a0346615050a028040c00c95100b80d585001800d200c0e41b04070041e00005a1515100800e004c0100c003060b0584922001051100c400228900605801d2400c01805900c03100c1a140741541c00200c50305c404085410307001d42454130300d4030103514100040c01003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 768997392 1250 768996142 768996157
    0xe1210020325050325091401030f060810060e060d030f0201020d020a03090203061005060f0a0201091b03120c03090306020c15010b09041118240d02180103020a08041205 74
    0x1c0860b45903040c1442d000401517005000c0306001c40c1c0b01c0406443c107840ea11900101034000260025820041010305000c8420fa101d414580400e0201104820781c0a0740c070781d90004061a0041d80741210840e10502c699001809001c03414021031900c03100140b005201d0700405014003d078441d40242e170300e2003941101d40f038040088085454001500000b00204a8082c04034006d10401c00403500a0758154221001c4030002403500d0300d0a20181c8102050303400911710542950349807401c0c00002000c0d8130b005c411146854080c001d80e0751640c00e140d0240c0120480e407005014090691801103a48485004256500080c015a4170308282d9042803400d40d5032603c081d100510310001003092043e05006001d0306030704503024004c0c02020784500c0c0b500e100c1c0402900c81210501441821420b000341c40e0070f104001c440c1c50fa101c0c0700300d80d80c0040321680000c0c0201c10080e800030340071000300f80700f22151140d402c0a28045040011403c009480c400000d000505000d840007601d4a0b001d10038811138041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 768998642 1250 768997392 768997441
    0x2070305010e06041403120c09030c04020408060f07090806060103090809030f0706030b0a24020109020306090d031401050907031a03120c12090a120203010b09160e12100203 76
    0x720b403039420096488100507281250441c07010301404003409400025101424015822000e60f80c031200400100b03540400d07402505402107101102c015940c0e44054401000b152002c1d04c16440c02072251000c511004025409010b41d460083c00b41c00d5001401c0d95000e9003e00340054103c1c07143c00c0410300c42c003c034004145d15100b0660940d04594020415801b25a569203092203012000c80800940f140e0343d000302c1c807150310b03041090400c07510b0b6148450909038290000103601d440b560042410210100c03001e200983c4003502100940e5454816000c0c08207222010030542d50601c1d0010302d842101902403070400d40c4400356000d0781c030008051f004000300003d007154000d180b80728240c0601c0c1c10102c1c44500c94000c0070044c048400300c0700110f0703080240c002c004226680c01c291070308a24060340c020907a095903070380144814585a409145004044481181c410035071009001880e0031303a0452400e00980101c0c0e200d0854620000f08216014080c5402588076030f80d00d110303824500c425401450700c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 768999892 1250 768998642 768998651
    0x40e060403140c071521020a2321040c150c060e1e0f010522020607080f030c0309060a090309050f010e1302090112090c0306020901030b1806122107030207030501 71
    0x1000d070741241140c6c0b0300414446054a9a40a138190b020481c003070304000c007012401808000300020300e010031000d0002800054281054082103c1071101550005102c419128900c2803005202c100e01c02c2c400202024483c40c0040311140c207000b00755111802c1d000301110f1301c3d40146442c0c03103c1032000c101c2e00100b86400c04400c4c030500341104d030b40c0d41441da040f0146503e82008210160b04180142c030040c002d04c1562405646a9400c3c0112a03100210666a04130240020162402040c00a6000e94480e00d01240c413070501c50f0400703040200c0680316240b518500340500740041d80002252040b160103d450804032000d180050b03409103480d9154a600c600c075000032505043c096406000ca0360b10030380e5046000440704201e00300311820714034041d040c0c2050303d030704100007105600107010050341813501060000c0044041540728030303800021626641d0440c104162400c29000e4040c60750340c698001c085100003124050761004410342c0000b440311001918000b458020004032000b03540c480005c20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 769001142 1250 768999892 768999929
    0x715140403030b10020a0c0e090708060403090905090a0309090e0f0307050a03091e0b091f0c15020909060405091e0123070203120712090f02040e060403140c07 70
    0x40040c03003800700644c452281c0128412125200040815103554006c04101289040c145454440f0320003c0c1100070a106038080810b4250090205c85d0003284a915148001810701060106540c4014540c18155020143e5440400d5200300f14500b01c50ba408000140075500c0d0710002d04041e130804158000740310001e494010001c0c0050300c900540d021b0350b40e59140e40d0700c4088010076440100700b64102c121100c801800246014001008102002009400165203008200d0310f80c24280440703102181554002c1c605011401800900c1704200c00411441d011860002800038800a04000c0c01556107200088840f01d04201407907082900503542c0a410f0b02000081d8082c0400400503d000aa41180412000c06c200c400314010308141d0003850406d501140e01018010000b00344508216144404c1c0030611414400d85200714003655000042c1034050040c4401d4030344191001045a005501700700210354807116081e04c10015290465482c03107205d11162801806030000d0300454503034001d05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 769002392 1250 769001142 769001147
    0x408030414030706030509060f090c1f0201060e01061d0d0c080d140f030a150f081b030309030c0108070c1b0806060109030b0705070f0c0b071505010b0715140403 71
    0x120800003201140c04060300c1d840700314141c81094910000d107038044400304149c0300c807900c1c071240d000101c00100c50100c8804070020307141140184030020320103640e00d07101e62140c0e820f01500000d84003a01e00303803c4951411000400481c2401200ea40b00240c2809100050361881c0c40c140301c243e000850b00f20550b4943c0c6e0084c0d1036041c0c2901c3d45001c10a600c008060803000b41041c0c0b556074071001251800c556a69600c82c029003c0c024005d030b0112134991001c6452070700619201c019003891070060140c2507010040302c0141200c40b40701c500c2540180f103064000c1d5000150402300300302c00c0c60800d580d40c54032441035608525113280180300304050002e9426000004010301e0445008404407059030b1601401554984d5041c003020b099400b00303000069549001d03000030580140f141c96004120041502e920807440000c0e000517160360f5000465009200744c400e01c150764610448820422940740550107142403140b03142c01011040211064150180d00d40e0203a480341503040d070303503400e40d03c0c181c07400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 769003642 1250 769002392 769002419
    0x80c01060b1b01050c040e090a1505090c0613260d03090c05010309020a0e1909050105100e010b0904090320010f110717180d08190e010c11010504080304 67
    0xd0048218401000d4442c644050240030701a0704ca07070244524080c00c0c542ca240100078001c148050f140b1800c0010400600e42108003070000907912800106414961655410000c207030480900ca40b00c14040c205030200352203401e80440b54404500d1001201e03011980d0907106881348101d0b40b0740220b503143c0b20050b416030040075205104207840309840d6142c000648c00c540d25a1406504050b148406120210207540d0b003540080048032003014071450700241c0026980f001608807071701d0351039400744090600d1146481c0090240c1390003e060035030411841d100140600402144100d4807418130030249030207500c40322800c520484503491624803103e4018041d002144441403401c0c07909100141410015060360200b03039002116035020b62100740e81a83d1a001060918a00d5020400300d00031035441c103a19050191007004490744a00201201c0780c81c041c8401d04a009100348444542c0c0780e03a9101d1282d604d03060341b00c44401183d41234440103c3e41da0055401641680c0701c002404240201c54950 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 769004892 1250 769003642 769003657
    0xf03030f0c1b0b0601030605122d0a030305070c02130c0e0a05010c03120b09070903030e0a12080307110105011e140108010e0406180803190e19080c01060b 68
    0x10203210040c008101119440490301040300d040900c852041c2c00101c40c0c10903140c01060514000c54110349035070006000b03054000036528941d0001c002c03003400710b182104141c20144030080d05a051540088101d0721000d15100007405c00d542c5200207180140601d15008086e41c025041085240264201d80c00a04031000380c040072a6005a4a1a5070300e0701102c00016100181d48942d030458040e602034903841603001000150781e03112108000c3c1a154a142c5900c00c0070b10b81d440c541c1c1c6519500b07018105520701e81c6114040d003081034091000c503070000444090790740d22400380399482d03546210445c2c010007440d44c602525400d10000040080725603441010a041d038503111000c907907880091030628a060740e074860215503600d00400059051321021075005001391000324095145a403d00765460350701074200d402c0712012090000d825200121690b91490f040010070421b0090b07000c250b80e50320b400c0040000c03056152a00000c00c0a101c0c02d584084910f03c00070300003580c031121001c000c2e8004e05d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 769006142 1250 769004892 769004921
    0xa0804032306241210110c0d020a02150304020328120f02070f0e07050c03040902030a020a0801090e210d052d01060e130204031a06030f0723010c0f0303 67
    0x24900302c46103042c3c14218213203060907000b044018002c1450380f000c0c010f040c0d030300320b41040248081a4408402d001103940307490075074090440e0090034410080c4000520300e0020801d041401000016200000c00100b22a810729040f03000c0d540280e1205411022110020b0489520002000c1103c2c2c12217000d01180b151a020344280545480140e824010903105000b004078401c804102c0050083c8020800d03020000c00f80d910701900c412a2405990042d80c030690b0441d40043e01e555210352000d40305014081a030300620030240c3c030384011680d480d880300c00503e1001120301108201601034049030142920340c0c00621241c901120b000c91381c1d500d1140841e84080c05c04042081c400c1c01010b555059800c1e5480303a9106155403410302caa6040444030080ca41e42e400c100100218500c403c031100000da03507604003001450440e090509041074a52090381d15800722105104a800081079008511030304e1600800d2125000c00403240c0c0700981401400f28810811103000303060340344c1c0003007030000300b000b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 769007392 1250 769006142 769006201
    0xf04120f03030f090b01140303090d03080601020c10020303060f062703010e0c0a03031809050c070c051e1c1e06051308220902030a060e01080a0804032306 68
    0x750b90030b02504c40c0390b03400070403004100c00148039404d41440e0600c400350303018040f2030134039107907401245451115070025800310b070000e001c00c10b00790307130400090900c1b0340144c0390841050720b5404040e540f0302000e0180761258080707409060490700c0702020789100e110310515075841d40c1c9210380c03c640001491114a4025402c1902c03a02002c07000084442030340c0400340196801320320b5918210b44030070480c7d0412560880340c402c0081c08030f419002c5c01c5d029641c50590155100c7c1c1754600118031340441d501490042c2e100e83c848041104902c1c100c1000a03005403803860070403040d001c490480c1c000301c4034001c00248084c1890104d481c00e264020004901c2000e0800141c2c96500d0182d21131000c114004118000c200080e800702c1d00510000718019441c900084d21982c0c49140c85026600115000c0381016550102000681c021400c95401806440d0242c03a0444c2c09840e40381507841940405004405200c0340132a20300300b051f070b001d07017000d20308400e4076040c0c20820009010f85030482c1003450001202e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 769008642 1250 769007392 769007411
    0x609060e032b0e06070b06090c1204060c020d14180307050d06060609230f130501060f020d050414041e09060f0b0306072f060a0c081308040306020f04120f0303 70
    0x8001105c9030749070400748812180d5150000c01480c107000618096250205000078001a800c0550503030141e4810100442c002e100a80000d10708400d02040b4010019500c18002c0080c3c21030080303590301001d14054021607481a400702e46071020a51000da048603030f5400c88014001e441d80444162500d0b560380506160345c8180001c841a611812140b03031340811260140036190002000440000c00f61401500d00907100300c0208480090b40020007040207644030240181d418405d90014490390305101d410203081505c5c800d00041c44809140c0640d544142040c07400c0708000380c80c0050003c3d00d0302030042c039520f0b01d400c4014140165455005a003052483d021030300d0b001c0760740c40c410031940e940c54031040380f4042c800344a20b42e1000c5824a84081107640011000140300a5100d0445850003055480c1b042c3c1001b05031000080c1500d0102c170754101c81c00d00182420045504886e04000056101c21100281b031007148902c0d4440100180c807140d19204200c0d441d0408540039000351000c021100d078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 769009892 1250 769008642 769008649
    0x9090a0302030f070c03020d03020c01140408070b0703090b0307020307050706090602030901030510091a0a09060b07121205040f024e01050f0f100609060e032b0e 71
    0x10814402009a0000e210303d01682d90720b80041e1130040e00401d1081d509a80d260042030240e52080b106900680024054030100c0d60804c01300c3c9004410309270540d00c0d1929104000ba200c0201c0c1c041d2010403030300000e0160900d4880d500c405c0250203401840c1d581d030304041101075540d6002100480b0b2600800c1e00c0052a0ba000750503010844001d17401547c640751000f00110020440184107040001c0c08540114100e601031185600d800b07903041c041c20340301c40100300704108103817030b503014401103410a402808001080e42c141c58440c3d9000f8844541004c00b000c05940c0070011554030400c062602040005025000c409c6100903402542c1200e03001c105400c4c1148542203c0044603a101c2500300201c940c8110f5201ca4110022110004900c03d00400c0d182800c0d99016103009000024900910178807400400c403503a0030980907404c4960461070840c1c05000c0f00150310501e0f00b4400c2d0000d281806803814455911000c0d0140b8065035407212413540061003d0a4180c0103000403512069a407244c05d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 769011142 1250 769009892 769009903
    0x7060806030604120819021303020a0f0639080403061b20010f06060c0b0a060302010c0308061207080d0f0810050d020a030b090a150b100e010c051b0909 67
    0x213400c14500d0140c6241194140c0e40b88001602840615a031440c040c04548454800341501160104002c0700c6149540108503000308160040e01d44800b1004040000d07039040ad406146a035405200c8044032515060f400c020501c092901417a1001700b042d40d030040008040090044e03030b00c1000d040202d00044242d145031840c4904092001c14007204108041e592150b92042404103503c3c0003152140e0f20103410000ea0790164003800110b4001c4d1440340401c00842400e50380400342caa010081039140d50002081412010005024040720710003244081c5c03120039050089840800c200d480c0340b59107034500340ea039800111400000880101c01800000d00c00c2e01d41030302403400309404c0c408890400003040400c1144100407640300420300000000102480c0b5924860514140900402d883c241020304402c110012441a01480d000403070b03805a07100ca080d281000510302c3c0611407590480d0050314000c681610180103446a10a421300000225800400d50401620307003c00302c1d201d00b000240d0b541e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 769012392 1250 769011142 769011151
    0x103121d010e030f0f010603020411030906040201210c0e010f03060617100f3201121a04020d050a0e1f050718090207020127090f0b0a08070608060306 66
    0x200c00c00385050007988124802c800c01c6400409070f41e0301480b0f01d82554500400485074031190b9460300820030a41c0707014031070728210850244200b0b15500d0100720140d2a00d00007400241440400c04480d0b504641046c81c02c00b10362103c0c1001c211020000b40040c00f2a1028264a03000a030402503440505200b405103400b01da03411781390010300701c80c502088804c89a000b0840b1740d8031501020001010101480c4440082410714100b82a0240c15098403103448075a5020040034085c0c1c411441c1750ba64082200c0d0710b091300010000031160703482108124080864001c080d8002d00105152120400e5030f40410f0061010075001c00209a151100e41e890b400c1808503a803801800c91171180140c6500d401940d03000d4018a0440c038201115408040c038500140c00c0504101d070b0204030740003196040307008491048405000d20801e602d140c418400c60900c0e42c0a00070b096a01c03200c007491500307800c5d0419200060001d1a0210868541c401030b0340d1100c40380300740c0b0300045e4020702085042c00d0204409018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 769013642 1250 769012392 769012427
    0x5040b0d030c050a050d1205150607030c0c030204051f050d030203030c1810030f0c02010504080d0c02010609024e06011101052418040204151508010312 67
    0x950094a00b510030000742e410603180c2d4000c01d51180e0000300c0502c00c0d800340341060f8594142c4103158010361400c0340c5000f0302401420003031324245800740e604c010a0790708559061400031091459072400049a19003988004d4200e821300c010b200310303880d0300d425084000016800d20030107503070358008110140340c80135005000342e002000440d00c2e01d4440301c002d000e000c441058081d020108600402c044001404002d80020360b07130010301d011500180540d1918090910081c002400d00d80c49090280c42a541c920358842e50301d1000e02e030520b0003074100318000e0441e000704549440b039900390000b045600c0c0807003007503c1100316004016400546130103901001e244664482d06400203228605490001d40480d0602185131803044001e4801d008852190072614010f0107000c03590100080c10084940119108046840d10800520409148164003603011100440d98041d0320415501e0310032581c020108298007020030422035038000e60031074122031140501c4240d10400010403605080390010b01c0c9030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 769014892 1250 769013642 769013659
    0x1510050d080c030f03221a090106050a12021009030b060d02181503060c1e091f090302091008030304060b1302210709150c05030906160c05040b 63
    0x4500300420804203051240d00c003a8580401040d05602e03641200c04440707400040041040309802d943e1191307801080d020b0900359491081c0365160f00013107000c1e0b4900c0110180807000034041b0307482500290000d050180880d0783c1c0d00d03100c90542c21810040c40042e4000c1c44581c0d1241d410394443c540704070450f508205000b00360f45486c4100009a80c1180341a80d0105c1e030625400c04241c6c4a20289000302240c10340144500c0e840c006050401e000280b0003892a00e06004d19040e000000c013581140a907000103465451583c4c5000460f45540e01c020380c012504440c1f80700c8190f9801552010a8900031201e40c4d03030700d035076000140200d0300d01030080c0b00c41030700240302040006100390825000203030000c00c030300011480501c40030101d070030a511075002590041c029040e410508499150400a940b03010341000c0c5c1441028281207500d440340104101400800d0070034401e040c0300303582036003d00034001c2d40d4420613642d40c0c031085c0c40000c2055503902e209800004680c85c1c54403d002d44100c02610f10003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 769016142 1250 769014892 769014899
    0x3050a062309180d0e1801061106010906180b120d08011805010320041e02130509060604060f05071b210302190c0504090303020a020d020a260c0d050c1510 68
    0x150402041810250402c0301b01001401100b281d2400c030b4040c00303031a911f41402c04007400b486407a007507060340818680d500e884070500881c5040f260fa40c42c1c0ca007045201103503527001035021400441d54035811454a000e8402e00442c5254880e040504aa00c07180000c0044809010245d040b2602880002d0016001900c0c43c24042e800900c0d14070503040081c0001144025061009183c025000c0314a81e100e03800545c10650310a1900340c54040c120686003450a4500711000c00c4484c03150740500341c01d106803000c466080301e1088085501c4c031507020b44442440d0a03005003254070b00b003140c0601030004150300104003140210a080c010303021b40541c002c0c854903e0700d0090380950300c41c81c0400e861828801d1000308854072079015940c5000e00c40c0d50300607030b00c2d006110000d0038508454984030446d00682c1555021400081d00c24002905c5003681c0140c1c0c20400080852601c501d24607001c030742c090400000d19054110019000210000b03041da2031440c1c5c0c980711540310303580031504801c0d0361011a8050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 769017392 1250 769016142 769016147
    0x109080d05070201110118060f0f02390d021006080a020307140a09090b1605040f140120010c020d051e0703030e120d1a010804020103050a062309180d 66
    0x542ca4004945d00026204200d0b0302c49403914004084151046600e030351400031000703c03501c160b1580440240e421400d204039a000500c1071010403021743d070090300c0144a0340d0080d4140000e100b0002c80c10044584680c1c0c01c11029450f14416007804506902c1c01100080c41c820108106520550080c040d03d51a41480c40c5402c00751920031009030010340d902c4000c510200207114107001540100c00348030007850050f640c0c84000d9a091000401c010041c40108620350385124140255491501d600c91a040d168004803980766607401d010195004503061742c11900010741c0510304c0c9604c0c503826200303104600d0b903041d81c01c3c1c8510103040201c62420702c040205000d2403801360101c60b103c1d03d00416407044490742145000141000c0c1c62042d000020340c0c004040303a40c8240851064420705404200c8a1000080d080c0040280060b0505889a000418070355580d03001070068416403e000c1403d0403008420302d00441029100d038040c2d030b08417000c12810780208035003410b01e00e8148024400b20403404401c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 769018642 1250 769017392 769017407
    0xb1b09040e0c10030504050708031c0519090602031b190315030f14071a0313020d060e0106051912021201021e03071b05030406260112020109080d05070201 68
    0x41814060004000c2c0c10b65140204000c2c841d150f80d13408140e5080070b0600604020311603000c60b881e980304000a405541d01a000310300e440fa10018005020f80d04d1010003601600034400b0a80311503d044882010446c0640c00b0718000c01e43c40003088191001102020b44a10030268480c41031104c44000c82d118034482c0e00003815101d1064024286555240c0c0c1c1c0c61012841444102d0340d02142c03031010030701d0807c108007440040c07c3d00720000b880110300d10703284103540c4000780c80600072941c01c2001000b551180310350132000f958404010401d400c10280400e0080404d0300030705110700d09203020121903030b1505c01004180d40c880003522141c8004e076401c000008001d03184001071950240080800f210000351407413507039074413074080594901d411003009020350030000d001840d40c50303804442c1001c00e2000043d40c058540f41d042030600f8200310070403064810680d500c01d1000b0700d2103000101d5564410280306003694400c1c0c82d01c0c3c141d1600c6041103921800002042d0002400520202c005903200700c0c2d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 769019892 1250 769018642 769018661
    0x50c09040b03101109180402090705090d0203072904050319050f0303040506010f0909050c0609060904050103050309010801050312071707140601150201020c0a11011404030f0b1b0904 80
    0x31104110006658082a02c1d00c56139904118680131a103144642000300d000c0080380b02d0b40c9005c801901d01a80000c28180003d000c1d001006008a991182d075218201244011900282100c054590b03900303500c0182e04161844951140603030b00c0b6104904c0ba904256819280020040d110400c800302e009041103443c042c01ba90588100c0460f01c82c2c1d4081800118010346c081c1c1e0180000e9810484d443d2408203881c0e00ca00c0303003189000301d1500403a1000ca508000707403800319020342e40c03100f29000141c2580503034000d89601038501400002001030000003403400b000b003070f201c400040c0c3c1c2e24805c054480703145040b10203c0100800c19000000c03403943c00c4c1710a1010082c0c0e800d05214890301ca126011100d1202056154050001440f44900d0107a5a41c0402074070f10007585000602901180c8071400c0741001428500d0040040344903070b0180c00001004440c0c410916100c603071701c0c10440310400100e20207541210200c008144c55000d0403100048a491441040313141c90604001e0000421b00b944 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 769021142 1250 769019892 769019899
    0x5041802150f03040b0907050f0d060e07050406090b030c01030e0604080702060415080f0f0105010c08090a1505071104050f13152d0507081305030c06071e03050c09040b 74
    0x10002e01c00c9001107015600031409402400201d14103c0110303481c002458005070f10981800d04c0d05483ca1303407450004102c695014001165103d001c1c20107034541545a00526442800c0142c04660140070781c0c01210700c01d004800b2681c5030382e4180015021103442140b00031103500700c3c01c002004128000300030100c10b440a85070a14080d035078580c031220400d0754008840010032403c00c3c02111681503042c5500907685031400e2549504d080d0018115404903d00141b0550020408811310b0303650380001001003c842e40020603281030f001004200d94480d0781c04560000c41601070501c80e00380b51150304d00c1042c20141c5403507640c40d20241180b0101c2c1c00601201c41c3c03460005c0d18020101c046c002d0740b65134032590306034100c1ca56481c010460346a002d03091a07200c0900e04402c2082c07040c3d01c04c2856400450b80c01c1081006140d5040440c218856085515483d20a800500038259030007690b44840b82d400320080961010000e20440a884080d13039041400002803012003581c0c41c141d84222541070004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 769022392 1250 769021142 769021147
    0xa0b0a050d0c03021911072607080a020a0e0103030818031e0301140d0f063207030c0503151903062c06131b0302120105010801060504180215 62
    0x1c00480568412490361000070741c001c141d880b1a000308044001072070800341040703100280400c0100b9514489403240300401142c0403402622200c0115403912094960710a4419080e21119100da8503d5800c404034081c051034400081c0403400070940a0590382c0c5595460301c95120742104901d40e201d103d10122450004000c1c190340580005d5500b10480c440d0313004540c44c0d62405035192840402c0c80b9240d030185a1041640e0009822080c00d80d1003542d10180001c0c844140e403000ba08619101d00a4001400d00004050014424142140d02c1203105507001c0c440305c019a182142c131400295102d00c0490f04504581c007040c5840d40d0410300481c900716040700440e80c0c0740c443c481500d06004144894000c0f100c0c00c3c0500e002240301c0c2018051900d001031400c0e08101004c4c000010494101034484103901411160003a007401c03040c00110740050401076a9011017108900811007841080e0440d0f180500010303540c1003a02521010030518903100c103514005809000e541d180740192840149000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 769023642 1250 769022392 769022407
    0x30c11030307090810020a2a08131802090306060d061122050d0507030f060207060504060b2d01050f0d11040603060801060b0d0b030f0f0a0309050603060a0b0a05 71
    0x1000a18031485081c0e03100d22066150a13a100c0c2840d10b202c0d90410310700c0c0104035109116400c111509490202090000c0d2050074103c1c11020005010000402003100010002e2034014040440070540340d000d0210100104a1b896800480c41000c1c5003a4040d000b99000074a1440d1400320940110300901001c40c1c0710080c81d01c02004e40d031108144100c6c4185055042130003003803080c1c401015040684d0944460016a224a95504004d100003032414607030040310010070000d0f4054451196101d40c050010341410b18129014020084c0454045c1503000b80300c1d2040040400c0b01159080625002c400c426900401101e443d0f00c01c021100781c41104010b00680609a0f1080842c00118140002d4540c1c0c10080c0c001c06075440d507844001d4070b03810407500303101014000c41160224400d420001509400e21030100e41002d030342d80c8180040d0300540f0007040c15100c0110306486894402c0d941d580c6c441e500e600400c43e05001c25071740d20b50090181102800442c040d100105848651410081d040840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 769024892 1250 769023642 769023677
    0x60a0b0c01110a210603030905060c0f010603030305150d0209160302090a080a120908120a0c0b04030905040c030e030a080907080703080a0e0405041109070c0213060f150e01030c 78
    0x52000400101c104d11000401c41c1c030950107042d030051500f0148015851034600600a0145006040c801c01000980820321a402c2001422080c9118020f22000343c0c1d0f820058002c0c5022200d40a4001103848c690a00d850482c1e11003404541c002d16004164452030041c8603070205240c0c3c0042450303800c0040c4800c2d82d0703400d05081c00400c00c540c010180c0307100c1781c0b410300c4099500700715020a2188018041c0a095404145581d003008102a0552203040c80700d02104c0c2420404800760040c03800c00f041c4800c0c160f21200b8001524026641840f600982d01c41c1103044460310941c9043c030740c0045c80f1203100f1034824000d568000b1526011a41c1d03030781c2c032821303840c0c10000740b6881102d25a03000680d120700990001844000014122002c211614203910f03000c0600240e2110700d845802c5000c00507020501405800040c0345d00645004080369001e620b1030020174290241c4424515034540001c2c940019901c06100100e0b50fa89030301c84d0258080040d0301804400e00045d0138880b644450800144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 769026142 1250 769024892 769024897
    0xc122f09030604111f0903030e01140a1e0903030e2106011e060801080c0d14070602030c1506011d010509040c0c030905060f07080906130803070515060a0b0c0111 71
    0x9000d404004030740c07104c0d54100110103003400720b80c4241c94414144028615000400310701140d401d4280321a0b12650b8000481d12100b50040d80401c0b0310011610035020340d40300d404400300c0d0306030010200115000200c250f0751001d492000800241e12100034441c2c0f8100b0402c00161030381c2d200c08805100381c0310800b450402009800c52480c08103442051240709201010100041c0404c2c00d02c0415075042c2a225600c81ca034014a040c010070108015600301300c0c0300984031042503400415284001c0c2c481340029226403001d00788004c28442d403808009612221480540a880e05845031881d2443e181c0516880c0030100c2c06441c10f2110900ca888141d4549010b4a20b50506980d5514850306007442d02801c1c501c07046c0c2140740901d5051106111900b17180c000c507072405801c60351560301c070000100060140e04c50081c0108840741e42820001e80c0d0a000005000050710510a941171001d0403011000d0301e030030403100b0640c4860100e6040060655a400502c5070050110002c240042e01120801340e55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 769027392 1250 769026142 769026151
    0x5040606020d030b0603060a090213050312070308160507020d1b0306020706051003030509011b0512030f0703090201020c01140904091401060503030315040c051c0c122f090306 77
    0x140c102d0080d030038000e40d040c07194205002045803500e0a6003412800b1844130700745c600903205070030350001e482e03080070744200ea80380001c0000170111000340f00a000090a940c205c1074040340491410701c007040d40854400345085400300c2a54641d81000250380800030111507800040e54005021440403031044a140c0c001c5014602a06003d41c1d2000d039464804102c03080244006103803d244d90f230600000382d03ca001c03203e9401d400d103840c01d8003c441014290f1384e104008401003440c403c25050382e6910305010061407043c5a401c00207030080c5d0310140c0035810340b50304080c02401a0007400c81840c00d58081e40c05c540c0e924240300c803600d007804031210100e0b040701c6004100355855103c280c482c40c03602c0424002e0401905082d4081c5042d801d00d40e5043e0b20000d07000308135501c142d86403181385594070720071000d0307950404040303108080060010713004400401c04071141200040502d4404d9816450a002c1c011100801c01c2c009a1003403c25030319442d05404244501a100b4010410544140d800f0401036004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 769028642 1250 769027392 769027397
    0x4020d0c081b0d0b0403030b0604091a0a051e040f0618061818060b0102150f010509011508190605030d051c0e06010308030703110d0b0a0b031b07020a05040606 70
    0x340003110144220242d8181c601449040000000000036610704c0207160050f030f041c1000b1544a00000c0055514040c940140c2000c501e01000c072559503013134940c1110700200a0b58440c42040e101c81c1800300402c3c120280d0684c1c00c01c1042012201d00313090313004003260700a40000103821911001d002d00541052501c1c03440351500c404007484508038115454288401d026420000c00102220902d1120741d1300310b015110603514158510140d0083c44060062020a1100100d80c6468444020005002e001e01c502802002001042e00180b002d1900c100045540742c103850341ea500d00c2214a10ba031140c1034901c0050b1584c10008064a04002004000c0750701e49072540c54940c40d0a02c240252803400d40d040c50f0900f05500c00c0481800862401d064035004540c0d60381d00c0c0c1e108402a80949030030850601c1030800060700300d00c03030802c59100011155003103608104850303030341d060b1010b68001541e0ba00f000c21100c0c20840c140609000052252510113418002c10fa075941c80041d04554031a40701002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 769029892 1250 769028642 769028653
    0x150619150525020a140a0603020d0209030a030804060b01020111090f0a0b16030e030a1e0614010909050d0f02071403150403080f010b0f04030210030e0f0d0f0207120b04020d0c08 78
    0x71403403c640c42c10054800100b5005c00701040380001900092030744944010b042c1e00044031742525880350101e40341204060110342c9280b0302890700910300d5401f10340c240e80103480d100440310190302c1800380455884150190340d0920010404000543c40300a00705030744190a03900005001090030040c2400c80081d0b075003182e0009941c2001750240d1884101a032082d00b0210700e080001d0300c3e1701142094400310400d40d0b03000b440caa2030b0000007016100d100e0b0340b01e100c44000009412000c1d40185210910a0054a0703030408010400d0f94045120354550307002d0f03008008107126542003034445200b641c0b4010120b42500b1020140c0301c2510a080d1f605800042050040201340101010f2050050038145c20b828500039803800e5200d110b0255000086c440c40225105492581c030a0f04440001400701055036060b040c50983e6a0780c0d0200c800c5008007044036618904022400440c1c0503080340c94040a02c9040f0100d5a1141c014140c01801264030112150180010852501c644000f07010107400818 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 769031142 1250 769029892 769029967
    0xf07030b0901181a1b04120611071a070201060e0c030f09030a050d020d0b1804060507091206020c160602010917180103091509051506191505 62
    0x9007540c154140400c1c00c03400e0301c283e083c0090031142401400c180030202c82e01c059182c6000c00401110a503940e00d01040303000c0303404200c85014030102416a0310640040080241c425032452150040403409010740c0c5c0c1e0441c03051b012035180082c19034132200c144000145503448503040203e114040d507140443c0c10000c000c0100a50b0741803605500720350440300030b508015000304000e01031b2090705d0b00907100380e401184d00b102ea1009900001500800181031604040f620039034160301020072241612014100b0011540136409070100e0b10685402040c41c0d00025030030788985000e0341c00720400030f03582e108440d035043c950318000b10500050042c5030300110700c0d183c15042c5124090045100b01038218007c00c0004484102400d030800c04400c00e0030046040c1e452420401d41d160a240303d424402d50610328040100a0081004554025007207040da28944500c0180005145202c0454000245049050041a00f040100e03d00d103a2a4036002c0e2400303007140300c507400d8201c020484801c403e500c10713a41c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 769032392 1250 769031142 769031161
    0x105040b090c070f0c03020904030f021605030d0804170310030606080c132a0203040608101a031003170304051b032d01050c0301051e060f09030f07030b 67
    0xca0020310304440d5140c0c5418141c031400414400e81c800149095031642078030b000c000e0711040c0c11004580080c11100946001c1c2000b400712140151448010300410742c003140007410426a480c151036020b401007982c0c0c2e070034034008d0701c1c0d0034030203441136481e0210f2104001012001c00300440c42100e04505e07015410b442c44c50988196a01a0800c0d000758025401d041c0d41c80d210381e40f60030130850081c000803401100189480c00102200ca154400c0c084c541e5050102e0150000010001c903401640c0f0b070300c00c50742c130800124404400c60080d0320200d025404444c0807042c101014640000c1a41c00442c41541d4a540345003410b03c40c09154142c4901c08010030052040038080320245046002850b2002c408101c00079407121000074030049640200103034500c548440309184c810a10380003000f0001030401d00c00c0d50140c0c2c1c00074031072648a0401c240c01c01036040c03800300282011500c050822814540c02c6001c04007d0303000f201410b1340521642405c00b4030520f040158400550003004800300c10304180d1000b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 769033642 1250 769032392 769032401
    0x30309150203011d0c1b0c1009080a080c12180406060309330207061a060f0901050d110304030903060b121506061e0307180506030a15180203010504 65
    0x40c80852031050004001d034900d0f070348040d11418506a21000300d907880130b562000d0350080a500c5460750308802006403060383c0004051800c0001220844038181800000f150040b140340164011908403c1c1442c00044e0450058582040c1c0501924141c01c00c00002c4116a0084207510200d00c8030340c12041010306244c401c0d10050480d51a0a1080f00c005407200043c2020400c0c0e00c464450800311816000485481500450042c486041d9911903090401801a00c400d6405041c66603038211017040303502d03200c1d0842d4406042d00038690700748903004005580c01c0d04401c07411880283c4400c98080407075000402144562b2103915441758042c1942001e2044a0b1008035440c000d41c011b43c000d01e5090000280001c07028065654414035603240070100da0b0714020350f05404415807010030415400401b010203907101e03440e141d032010060500200980340310b030258400d642c1c003c201000070030305803441a04400400e184101049010554903643c00c000e125550f24100c040c507502100600c4189031500a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 769034892 1250 769033642 769033673
    0x182001090e1021050a020f0411040306020d0605010e0310150e010905070e030d0e060f041502060103031106040b040f1b080d11010204140111010905060a0f0c030e0327030a030309 78
    0x1d11601c0f030f0350141d8410b80c0d80e18500e41c0291090320780c9200240140e0700c941049600c100c07041c9940c2c1e102c0e5039a01d44140690402609407031400e061200104145d440340c0c038030241001c1c0040042903280c87c0064950028513031031102188407032900f0710101d50001d80903081c500a007180303500011140303440d2900034100b29102040504c603412011141c014035510a030044815817085400c1552003400d0616440c2c0c40c400e40e400101e411404d8403030020119000300382d1f103040701d01980701c0c0300d421600002d0654541030102c0c0c000300f1b107054a1002c20081035043d00001c103200e118040c404013540c0320044100d500c260035800342e58240e00c295100c0d80e105034803c40101c000c0c0428002542001c0c144060301c1c84100c0760712403803810001d00c09504020780509421950000b9000030646e60141418002040504466000031281506200c0794564a911034400d1105100206001d54107100c040d191400c020400c2010b401c012100d038042600c01030340d00f030001400c2c8500ca9113002075000a58601090b05d000d1020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 769036142 1250 769034892 769034939
    0x130303021902090109020a0207080703080306030601120c120227090d020303220c030606030b0a0e030705060c0307020f061e011a03070c02120619182001090e10 70
    0x251074401a1901d03110541503901e40400940c49604200c0d04924040e90360b4810314251080d404000240220400294000c0d80190299411683c0b103031074000740558000e00042039007a1580c410440262428901d0343c0c1644000d02100340700041180607003001da1105000106c0c0300000c0c1c14080c4100040180509400c09400a0350035407400e500260b506403202030550f2201d058002008040080b0311528202465101208020a035100d05120400000844034a01041d1600d01010704411000065a00042d440402085c480c1e0700c030640081d50f608023429050552251a403c0c80d4666028040d062040000000d0074402c10400305001d00d0080041c0d000c8040740b81105400c0201490080469031700512506064085c203074603102080e48a14016440486402010103022100031900100c161107101c4000a0100040c40344010940d003003140b900504014105981300c2d140880c0c0c005000b0100070504040d040b9984d9011100e0400c041200c548140015404040c0108541c0a102001c0c0c1c0c2d2000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 769037392 1250 769036142 769036183
    0x1050702061209280f0f021206010e010918170c120903010b101d0102120a031a041814011b0507050601080d050d2c01060302120615100309060213030302 67
    0x6020106162101c4c00020f0851070300c07442c3c0c1c0f4090204172914004c850758080c100c48202c41015590039201c0000b802a41c0c1c405d2030a070000079012042e4020080d142e6200d00e01c06c0070001c3e00750f5482440d0440701d10a050b03100c209012542a031603003440080300344060000c0079540c0303218001c201070841e440004054800c445d00700b4000c12440d8000001401128003a000580a051040060303140021400041990103c0001c6c104030ba036038141c0102c0350061800000040000520040000744c0b5801426007650101020030200032a1050328094480308400c0000902c001c82c0b98480f03002c7c1840424000017080000440804100080181500400001c1c0c080d0001c00b4100e2801421485841a00c1900d69150000703104400d401c8035418802c0000c0108224080710184d003c0e50180040c0d00c402d911652914942d00e007075103004a046403050032420817071000354131001c0400503404584081042015aa47c0c4041300055061005180d1680b401c2207004200d032031403078002d2400d0b41c04001c46840c040d01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 769038642 1250 769037392 769037443
    0x915030b1e060d081207030c02100c140d0b0901030b0414030703170a1d0f01061e15180e040b090c010f050c010e06160306060801032001050702061209 66
    0x1c1104041d08128100d6068040f40b0250403c8415401202806264128560188080389425900c44803c00c60310742c00b9900111070b06010f09003140d10040090020a00b00c1ca40100c0c0d2143c013000419200c10620000a2462441700c080782e8103502c00d0b0412101c1c100500240418429444032007030001e240000114900b048a540003003944a6100340004c6104503c0e010641c80116908844540b40e0340d41e080da0400032030603071601e07a00c1e045040c2145440d403070f010000c0703402c8429010342d6180c2d003d091840c04080745440880e2450203000741400c000c00000320300e010480d500e186003090080004030300b041141c0c181420440c039031800282941100d9440615152203a076009425046040c4a509046e510f5074400d581580c05440f10303003e41c80700f902a65041110100c4525003000006060360740822015855030015a84000280405030541844409100e2414890305014204107010301d413880c2842d105034042140d9400103085a00b40c0015401000004442008a01d0b60800f0507100404082c08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 769039892 1250 769038642 769038691
    0x1201203060102071220121c26040807030201090c060f030605011b0f08041203050d0f050405031c020f0304030e1509060405150705031308070609050a1e0915030b 71
    0x368080007520241d86d0000e50140e5034040401210102901c00c0d01c4100c200e01d2003044545070b440d510740340440d03985009001c1640d0b40d888050329402da00b2091b50103607115600c2b018520342103124100c04540d00c840e1080005080ca510020081c1950386030300b5640d4006c500d028094548a400c1281046041c51800d0885030022070703486401e0b50050000104c3e0304650a282502e8880d0341c100c0c1282c060b208091408240d440300080c101202500c0c000c002c40d03520f032003800c0c080d69002d0f11f002d01594002d00002c2c8540c40c030901d4580f034440d100c5d030005141032018108050309800885050b00172900c640c0d0551100d080c0710300e49800e040d100c66003039481c10345c05800041c0e244c0150b0290364010254404800b04200c0003d003210702668000c01200d4541410b001d0700118200640940c500e98011002d001607100d000f1171081c41950401000d15054074142450302c0902141000307050300b0001780d0400050568070500ca9499400405030114156904508005540c1c00c03020b051b1500d1544661001001d000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 769041142 1250 769039892 769039913
    0x4110402070b0606070510020c0717010b030a15022704050a050c0d110706110c070e0106050f030403180602010e010e0606060403030e13110315010e030c012012030601020712 76
    0x40c421101071781c45110070b042261800c407460000b09403807480081d84560074500040c0c08004c4540340121120010000f10700a82a18000b11106400d644044061000511194a0308000702c2d5583d00c0142014040ca21584000e01059101c81603551911111642c50900307000c2d0075800b1a00709014456406d0202c18243e984c03160180d0340d0f607051fa440301c08810300b8102d207084490b082c1c7c2050042c071120745444258891640088000111031003030003400141d0a00d00c5035203d048900580f283c84c00c0010f500d502882e80e80c40201300324200141b11004018044006120502901c800d030b0000a05035140030060b400c407801c002220200381e00c15020400343e40e40b602e0480301038951514100d90159410320219840500034032042031440e040c08060034100b000c005c040c512403020100f10390f85000d0010f0040d10f0145040350030317681542092241c00c005500401228038851307002502095a0800040e20b281418124400c1e00c0341c094000081c03050310342e41004040c01803c1145d0001c40c41c004169207505a82 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 769042392 1250 769041142 769041151
    0x806010801181409010b0a3c03050123100f0323060a0207030801050406031e140d09440709060e04020102070e011203081b0c0604110402070b 62
    0x940041d0060a42e10080d000901c604054000d14007507400e040e07080a0280c20b140180c5e5004e11032036040001c40007031080208406d038035881200c000c03103100310f6040340d0031a0321100c581a502001e44000070008509100300142080120300c810361380c141c03146031690f4003100506040c8494000502c1404500f00c8000000e040f00e611850701a08800d1080c001e01d042113404d41c0c17160241c0280001c00101500300e800800c1c0f141c0c07103641d800c1c0442c1e0302d4404100c1251942e001c050302c007401c405c1105030105060b564460702107010700d540703000e052050880c3c03914044580c1304001c00960000000c01803400004600b0340407643d10001c94500c504003401c400d00b100c3c400e42c111103112101c100c06a50918042c88101e008d4010f59405026054881c032019000e000142c9080707006103d0900001200406050207038180d40b1002d1000d403c0741c240780c404440d18a4098001038034401001010030000c4842001000f5021031980030380954070b07050915404003041c003044d450165004204460000b6411407600740e02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 769043642 1250 769042392 769042409
    0x2b050c0418051e040f050d0512070f11070609080105100501080403050a0e030a03080103151a2812050d03022a0307060e0f070b120c1605010906021206010806010801 72
    0xb0383d03031500036a10071101c48080d0384a105080c0300303000500031903d00340c4010500400c1146d004101d0a00100c410b0b10a900300c500903828000c0c04241464411303028040c9d07200d89403419040f20f014089065041030711542c8128089486003c042241c02800e004040e40204900f151040843c9010b0000c0d01c01040240010f040000000d41c4072111802520072000ba002c024080700d03010585450301901502080c0030990300750203003001c4007100c1d0107a4040e000034603a0102800310254040024008000c08080140d0f0500500382007500344110440180002404070348884100e00c000da040c03690400740e95880c003d00b05401004000ca6035449040c03106090141c00c400b03041510140c0801608500403404014000c0d400c1080344907200b0400aa003620400681040e200000c0c0d071411101c1d000d03c2546542d0101000860000b080031032030b900607000d20421031581c0039000c5070740d40d6241d0844019100407250300f0760228800000c0d201003001075134440c0080c00c1c0003803582090f00000e401c2c0101489840503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 769044892 1250 769043642 769043651
    0x3100902041404110d020706050a0b0d051c030e100c03060e10051504211202031c0506030c100207080c18040b0903130807030215030f0c07082b050c0418 67
    0x50078070f1a08100c9005c076604030402c5403902907520740035000d040c09940d020401c0d41040c440c064107141a60240d440294400000e0580703404071801c541912030005451070a060f507521740e00c03401e200305000342c142c0c034468400c0c002540c2220500103421648250890308140a400d400c018070706a0104044040c1c0740119860059582103022459452140d80c021046031681101c200a144820014021905108145007040200700d071408036600c0c001c0d40394855116206c18203648116405074411a002107000d0300b91000d0791228008605503810a00c0c03040010b910444081084030020300c07526809400c1154460741d2180340707684c2c0896000f0003400291104a0910100704040b100300120703a41901d24034054011075655105440d01e644c1c44e440160700030301c5c0d00201c003c100520101141c1c031403500040329a05640b10025000c07403c0e04000811507005800300f0003281c00c0c103821101340540e10944070b140f880b021284220710055a002610381410b502e024402030018010503804009040401d450015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 769046142 1250 769044892 769044911
    0x10603110337021b060c090108150a0f0e0a020a210b0a08030c0f160e09070f0905060f0d110d02010509060c031e0a0912030c060e0303100902041404 65
    0x31181d40b0038001080c426118100c40c0411121290080c0c1040c1a240665055911422000c2030320382404483c04121500200072058240d03004100c00381e0000b00303110480d240d2104220119803001e070680c11910031201c0384c010800025084200c110342c08141c8031815402c2c0782d001c00000c0c2070240c0301d2010074910b46035550784000d400d00f035030b0101b100c0171401071400f1071450b0b480111584a40c441c00d6940c251b400f4044c0790b94a030750000110321444040f86002031a21924010184818910103400d01019014006001403003400d2900800003420103440001481c3c03c2402c01c0250711100080481e010310404900400490598019440040c0d802d8914505006152004a640b441140f0314140d0040010840602020700040036000c071030038110005040341d011701200c0c034260051a6080b0002801c403030b4284480d15803842d00ca00c01d140b20741000e40f03c1400311359408080d5a6103170850000c540c404000c01c10701944240c544401449a42003c6181900780010941c0c50759507424a540101d803140d0010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 769047392 1250 769046142 769046191
    0x102060408210703060504060b0f0712140c15010e0f0106050a1803050a020301231302060705100c0e0109060905100e0a0801050f06040204060503180102090a0803030f0106031103 78
    0x1901040601c1182c030709614110201500506550003594001c525140010840c944200304503200c40d032000b280f80d800c2410755541d0700c10070703141d0324042c404203c07860100d1201203610b03801400c800000480544248110f000000c0741d0084142d10100201900f01c081c01301248603c1c0403641503820314a40944e607001811020b030703211080344484400391308038800000244000490104007080c802c07002030103501d0031000310542800e461807100c210903c4110100c1c00100b50704013251561440030700300724101029511102d003401103a00c400c1464030345030420300d0790540c0e001412004030502400c004425a00344607000300010641d00800340210881805c0010560040c089c60312040c02c0144035800094903032030411f01a14042d1080d07040c451042c80070a481c0d151a00a07601940c00340c1d07440601b07565071041403100000f50540e060905560030000c21890b61980d0140c030014180e040011a40c900302040502d0103480c0590001c010145014602803031003144004503500501c03c0200702d2183c80d582000d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 769048642 1250 769047392 769047427
    0x10b0d05071b030503041106040303021903020a0812100501020d0f2f100507030b06090918010c021f050402030703080703031b0f030b24070c030203030403061b0e0102060408 76
    0x1003040d95120310061900301a807100045d03100e5441115503600380c0c41d00c8000d1140502450100801603006030b281503078944200510102268068811030788501e030f864403450543d5101c50000c3c0c0130280080100286004d1044068004110030b1000f0284175030001e01c002d1901d44200200c1c0c00300130340d1101c0c448a1161003525012510101403c814060486200d050341e9082483c41500c1040c0c2803c001408481c000c0c400c8107054035000d011070f4a00b070400e00c01c00030405da00404070580c1000c42d50155050150074400d030f00960a243e0020021344001c04080941c04200c02d0500c01d98a09042c10440181c4000c58403204483d40141026102c220901e001c2d006001407203000c482604074407680d0b00186520000d01d01d54a455600d080051612540c1070040c01700d0320002202c902840c1032409041010600c009100305170017458070402141e00c950002e07055034007590007603a9854407100071400b600d807501c5450442c54454100b41200070b103540c0c00030b500e400b0000c00161410138003003458079101c0c01c609035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 769049892 1250 769048642 769048667
    0x10e01050d0b1f170907030b01060503071e0504140d120c05030d0509160905070f080910091b1d042004180c060e060409021605060403090311010305010b0d0507 70
    0xc100391031100d40e90f00920600c506200f1581056000000c20316800780405e1003810b494011600c8240f85e0b003007030810388141d40041d0a00d810443c1c41d00350742128207680c00e64128900030710307076550b9911480c01c0f1100240c0503000d50a14829040031180b000003d10300d1071400382e0004c041c20083c28000c1a4200207086000d42010702885500f002d0400c0300044010840e8010101c10040e24410355460342040f2013114401c88000020918205002c18520b0007034040d664482400c5003214840345c080c1c039124055600044046652030f4042e2203a07201280040007050281004420b11702c90019803250002e105a805000688068035590309105c25047d0203411000346000a0300c18041d590382c0c04100c0ba24203c0e00c0d02c06407035400540d903010a1945c032490040c205158010700080c00e0904041480c0300039030003440fa200c0380034103460300580003400900459202e103000fa191a100640f41d820b2049103100906003841c101441d0800500012080e03205880410803691000a281da0350094250b502810550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 769051142 1250 769049892 769049929
    0x60c08090c031f230105011b030813080903010207230307150209040204091a01030b062a011b0c15110a050d0f0e1b0a0e0105011119081206010e01050d0b 67
    0x224440001084d40c0c1c5040c103e030000ea940c10308214128070000310032000e8131801800100c00302c1c0400d0700c2074006034a10f40b12034001c000d80391424a00400181c2240d03c07002c030403115543d8500c0341d5029050091807035070481400350003075031400d04565070b02000007641d01c1c458000c80740c2c081050000c0f07131190b6050b100500a0392004000340c0c048001402080700c4202c11960020341080300410460410b001030307030300040070241500241c00c5109800403a2100c0310202c2d034402c1d940c03041004121965442c0268511000343c40e00c100c0004581030145074030f8800e82480381b0240c1000b100301114070440040f660b41403001d1501c00e80b501c11070a00c800203416a15040340740a42000e4030072010b080d0208441700d101a503007858013011301d103e005002010401e0300c1402c4c0540b804400401c2203502905070300003402c925005032140070240740744003c6d0304085044c041e2829800410a260400c80c200c0e0b81c41c0d00007900342016242807030440d00080c4944500c01d0a401480d80b16650105640c80d1072002100048007203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 769052392 1250 769051142 769051181
    0x24110f0604080a09030f030915140a030207030c02180718081005130609230609190201120c02070612051302150903061905070c0807030503060f0d060c08090c031f 71
    0xb03040023803081555004c0c030304412105191046072140914501101e54260022160924407081400e90088d045440b0580c280244c6c1110b1100680c0c400000c1601c150b105510304000e0b04011000a11054aa41101800d803130811020302c000c810019044450764540d9402184640e0342d03074001c000940f2000d400600c00c504100002c000c02010140619850b142c0402203580705515501c3c06640c0d1200341c0300020180c004640000c0ca1152842548040c18010704000071102c0210301d82c441101c070303100c1400c00160014501440050360061810709610311410061029050081c058200d081541200900c5821640d03000610b412038641603403003d40006003075420920700210702818100130841421070040c07601001568090042c8a0700b904290403200c1d441c1000d07035658050f26140d0002d4016035210307010b00207150040d40c9401c4040070040c8540c90124140041e4240a4401d08000d041680c10b80c012243d0481c3d00e4400003182a00c2e9140c249501488484000a4200400c0c0d014024651030000c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 769053642 1250 769052392 769052423
    0xa050322050d050106060806030c091515040603050a0516020c12120a03020c0f0706020d080c2506050609070f050f09030105012c010605040b070c24110f0604080a0903 73
    0x1175005204640560301c6038591965620300301030b00c070700252207501e0740509107034007040003a0001d181655002d8409071050940a0001000180d030f60030540c010000292a84104030310000079002d1550081c0701e05100412801e14240042e48405452800c24060510300002001c003440800c18800c01c0b0480b43e044982e650010030740103000e0f6000c04810714003841107000c042998900081c902c0111000c56002c8e01c0d40088141040b124050050445a80d15205012032000c0b0340c10700081c1410650031510f081c4840c10640b5084050352002420148500e40c044100079450790030003001d4007110018541260b8440095500000900416030442d40640c40d2000100c0c00c3c64603090b020081703103141c11a130900803544600555000b01c0074040d03140043d80501c8208000c400d00ca000e0034501d07208903802c403407268503003040700100d88454041000c1c513030002000207a00e580000f20707410156001400ba18400d81a070000f5076903150080c00080503100c002880541c0c540c890040301e80030b142e1111441c0d610002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 769054892 1250 769053642 769053653
    0xd09020907030917040e0c03130b0a0f0b041a0d0c030507154e0504060b0a060c0b0411031e0109201011030d0204030b0a05090a050322050d 61
    0xa140403903040304d00c210300442d10300c0043d0648003113968401101c0c0b0a03030385000e41a001c44c2c01c0901175148410414107420300181050780e03840d118507809500082d9810000404c0d02c2030304c1503092580e00a45c42c007201d5441429070859040c21a81c0c0a8a01c00c0100c00f03c2e1030305020011590380b0140042c000c2d0640840c0c2003455a84040d000003646d595401c070005141d070704681d029030701114070352045180b400613404010303850389040c3c41c01c0205002c40d07040000c0c0300100c0e0645e0030455089820503502c6c005e00c2c40c50310300840d80c0000360816203481c18810329503a440b2130250070043d101070705102e0140405421540d040010480801c1c06048a0f036844074103c20142c041c217520740003101c3d01010f5003082d07007804500e654038240e034400003010390a800384600340075107600741f429a00b100c003400204a04030030001640002d00045100e501030003000c3c60030005110480b40d021740004026003151600b800800c0c030020542e030203040600d050203059512040616000082c0740c0c031450300310805030652000d021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 769056142 1250 769054892 769054901
    0x1f08010303200a050c09070f0903020f040204090212040201020d0512010e040606080f1606080402090402010f030e03040b040f060503010524040302150c011103090307150b0d050a050d0c0807080d0902090703 90
    0x1060b1081802925030107002d450451260700309100059089d1010030240c40c04c81030b52440540081d00040c9000d07151a401e9040e60310030001c18000c040e070300d01400300b196810404001d0041e9246000c1d400c1516800d0341d040060010300c90880385c1804000828140304059001000a000c040708992140c1e1104480c01e442d040140449600240108800035045008445840c13150398010648189940c542d03005490b0345528500a004165803549a1a204182000140040c214102c0060381b907620b010265454031100760032123070801030184010045030716421011840b144481c0003815140d2840020402903005070391010b94030052030109042c40000141c02880241d24001c000c0c09001245030402c1080e00c0242d965048560082010b500419092420303200c2085100c02c1c04281c0089400c005000300b90514070955217900580384039410403104000b1036400310601c1c1081ca60050380c6850b491a076028040b00900008000581180400150ba100341e0740307540c1c01404207a03d410b0500000b0000c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 769057392 1250 769056142 769056163
    0x50102190f0e030a0807081804060609080111040e0735060f0f030c0f0406031506060810080a0f080d05091b011d0120060708061f08010303200a05 64
    0x200c060b807100c0c282d400c0210b28070b683d40350001a032074907200c000c1d50389114550040c0c10b0b100011140d0a120000daa489000e404010010759890782e00b99800d108200e800c5644018001096100c00c110410080080d00c00f80c9034010994108040340304405541c043c1060020700b00c000e6034103082c00103641c2c18100c81104500600003607881ea4075040c084010720569101141845e80c0c075500c1040d80200d6072800f00911061540003620102e103550317481c0e5840c088822800e00007004191036440610046a0141610350f100518a45c0c084400d8a44500395440e9500d4010161071121802c4e1200c00380103503501110f0300d0200540d000c01c19031030701c400010346603821103054101c01d65440145004641c0704a25641146a06203800300f07000320600015038050f2451007116044000700a103c5115582c1800041c0c481c2103d0b0300d032020700f80351040400c4040c100000401f00c11044000110410b10751004500e815030354181000c0a040c0560544241e502c1042c00d651403440c85489010010010081074071100c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 769058642 1250 769057392 769057397
    0x20111010212010315020c101503171803060106080a02030c1204030f090909110f0a0e0a0c0314130b22080403201f05090901140102060c040f05040504050102190f 71
    0x3445030360130540080e17103d00d41c08018540c2c0604624650315000b0741c406c06440d0109c070341030403c103a41d07652030550a40100044044042c000320f0f4445440c0c042010040c14954114081c051640c1000009400c0340d1000d49220002030740400000c00c0003600030100e07400890a41443e030040e2610b0b142c02451600311a60100000d10468400202005a03028000c0790541c00600240c180c403409003031090f8001520a072590084a50303a00007402698403107500c0c068500300d9030120742c2c8038003510060159035590090341032828880042080748040c3e00b0710700d03501c0740d440746a103100e940b074400070364030f164a03e07103c400b4241100d00c1c0343e4020000d020340100100c0748501c3c00c1d9401c0003920556003401180c20308005400101081b035807549004d403400b140c000d480c41410301c90f00f00f8280b00082800701209070400c419004517500c8418103981c0402c040c9a2001c02c4000c0c5130300d00f5040034406042043da40c071529009039220008902044070a4064030b04040401408000b201c1c2d00c41d2004209800300c8a07551701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 769059892 1250 769058642 769058663
    0x3012301020a0f0516090501080a110307120803090607091211010905280909031b08070803010e040204050f061e12030705070f0602030c12070201030f0e0d110105220201110102120103 80
    0x20046c613203011301d50480b604400588040d00d026101e8952848120116561600801d0004500000000e180320a0075003e03001e115228544402214500070010305500140214a40c2c100201010540d102c00e540d42c1c44010388081040440041c0d600b401c0710f402140d80034000c0f41290141c1d00300c41460790208001d0000d0300d5600740c0c0d030b028518100c40c1c80d40302c0036000806140440c880100c4a40e19000903a00c100300d00361408003691100860b0760001e03007200038090304880600c000d6142500519801a04003000450a4102440000c8401a881c010b01d8a110070b440c911080581d50307a8103403859003401200703882d44c50005142c8542c030303206079005100701e6511210340800c48510000a032114074100400502040401000c01c0e00c440e00000b10803810152114000e142440c0c59004454822010a0003026181c464105c0504540742c04080c50745e00d43c0c904010003003a0040100c82881e07042020120300560401400100d64024558460a05541c0005184038200404407541d5040364002c440e1f115 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 769061142 1250 769059892 769059899
    0x31606020a1b0f0201110708070b07060501090513110307031a0916180f021c06080606150906031b03040b0108102c071703041a03012301020a0f0516 65
    0xc1440d0151030300603000003140404040117500881c004410815140100c44015035181981407034001103811410360100003051450420045003d0381d07014018030b620504c0030340740c031309003460401c904840d014150782920380c116280c5880601c801001780d41c100021100341d4020540d0000c0e40c1001f036a03ca480740c42560080848500304200c0da00a540d01e1529400c000c2020680403c00780240c500b40c90300135517081000d104d00030681c4c0b01340041c0000c180800705400d0f19084200b07080c41e0b0010941801444c2c00302d10340303400c0450700003191a200c07411294141c580d00c40341d01c0d140c03030115104081401d081001061000744110200c4c010b040700e880303000702c0e2402d2005140395815200c00b8005915903100c4800c1d00c1c002d02d09030f506042900d5608600300e40c1203698400c14144020a10b4000480076080040c040c8012a4104180302e90326520100070340c0745515000c1c003e146800e130350032002e020b0041e034594500c03140e100f8001000119000700c6410484100d40c1406c0c1d403206012004e8142014507981c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 769062392 1250 769061142 769061177
    0x40c0515030a1515210e03040b0c1006030807050124060c0212061501030f02120105130e0d03020d0f1a0f03031b0d0f081314031606020a 60
    0x40892580d00380164259203846042c0c00180200c08281c400c00e003800280420164051010301c100d0324610380d22100c3c001080b59603000302d56074032815004800d0070080d0308080c284001049508940340000001d544240c070300500c0e406e040b00d4440101d1082d06101c400400c1c041800701400089015000030130040c0300d1202e0100b0398442d00100d07980c0800c4080000c00120f0300030411444124009405030003c01c0c003200307400c1e0600f42c0880d04084136100585c000d83d88d030b59045c81140e248283c210011071078031620b00c2000443c260f051081ca072064102003950510400a9045043d000102208a4001008145014000c1d400ca800c10711500340c50f28040084044041c0100030801160300400071f00d03840310704280b000c1418850811a0540300422115070702000c40c03840c0407100318200d4007a1110f40803240c002400c1c1c2d0b40856030318003001000c105001d100a0090343c01000e00b035205a5049104102d41c41890560052010f074144252602055005102440e001000300e002d4030398909041600d080140e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 769063642 1250 769062392 769062409
    0x30224060915010309050a06050a0c05040518070909020a030b0103111204060c0e03100504021002121903180318081b09040f051606031d1b04020d14040c05 68
    0x1010381c800e2070780340861407010404100000301031040c034003c207120170b05403102d40c908145241d040b22520703070320020814228241d00c120480e403641407800c11f160034640000210562800c02c07014a52540c480c01240080d409001004e0051161070410f54031000c1c00c0c0d40141c01070070b03101d07801804242081c4d803a0710400310310011940c0394000c51074a10956105d50b26a81d00030800c000b0800280421070000140c1642c04000d0b12440e224145030218151505206002d500b940311045d1400390f6000316000c0341580341c6181a00c402c400c410790350548a2a86c900c1c111b020301111420240145581e0900b41c081c1035020b9448140c028100b00100000f40d40d030000142e45008104a044a9044c0c030190388100c1e140090a151304980601c446084404940e2242410605d0f80c00b0380307400c40e01c00a0020421140c05008510082e00c0c5d40b041d00e90010600e64400382c4030b00c141140004e6680c44403030b0184c0c3e2030341c459040c0e4960b0b45600100300148034001d201c05810601c203035010b42d00045201400540341c58062030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 769064748 1106 769063642 769063651
    0xa0b04020c331b07020406060305072a020402090f041401080c030304050a0b030a0f02030910110901020718180b0412090305030319020f0403030224 65
    0x804040307285612001500715000142e02004604800441541c4001034090705803403072140e04101c00040c0701d0b1000007035100f4a4440e01050342903040e80080e209400710f40300d81ca170400d8014442500c005180c000c2d8806203d004151074018205a000344c042141d0150048560001c0b1500041c240c1c2c00d0a002c09030207800d140010481114200062854000154091494a030070440802c418041601030104201070010105402d0303150307540060f4503404021000c42d103d0503d12051621180032514048032141030945a006000e49001101c20100050300104807031841e094801c40456808811314042d180e40341410749103948030060480f0028030580c0401814502850502c400c080003196103170420000420034400503038008201c81d0011206004020444031001d46400030348124090510000b5011400004044e00040e024040f1524207215442c400f80b202d601d400481b100300c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 768884892 769064748 := by
  have h0 := BRFrame.cov_init 768884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 768884892 ≤ n) (h2 : n < 769064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
