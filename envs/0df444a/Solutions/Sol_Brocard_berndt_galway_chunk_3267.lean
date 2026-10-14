-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3267
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:09:15.940808+00:00
-- url     : https://prove2.me/submissions/71324a53-00b3-4439-a51a-3173674930f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 587410071 ≤ n < 587589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 587411321 1250 587410071 587410073
    0x3021c0c0510090e070504050301061403191b09020310060c15051e0103140c0603060102070e150a12141b0f011112270a03020d030302040902030109050106030507030504 74
    0x14860480c240c8004407840c07440680d03814421540d00340e807504051a0140d804091012040d0000001c00458409500a11015a4079249010100c1e41c95601d00d81540282e245000d4042c201503034405d20a03c1003c0e50180c4041c41c00b4000482c0c090f0350411024503600105001681c2e55151844004007a685000c6007149000e80c0d52644603010b2a0191021a442d140440c080958841381c0d0100407070f4030002441c142d03a5a0820700300c00d10127884509514007410064040508286040303034410001a0010718019180c090b01e00020b00d0b00034080040e0f400c145031202e901d1350300e15400c0c10060844c40704076030b221b00c898182040b0803807820b20703440ea40d54007421483c13194181e40a05c2c05180c000c00c841408150580d403005071820700e100b21480e003e0340961b003509540d594800001e4035290b82c0810000c84800000c1c40c14042049100802c40e034403403841e03a0100300501c4c1c08030352400c10a100745405130901c1e80e50040403050341c1007a040080709903202d1006000003641407151541c070400d070f45000e101030304003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 587412571 1250 587411321 587411333
    0xc030601030201300c030915060e0601050a09150c0c0b04060c170c010c08180312040b0603101401060e0d0f0201081b030a0b100f0516030c06020304060603021c 70
    0x11080c41180b0040b02c150352020801c41d07441c600801d04c0d4900414071019a4a02000740200142c83c1c0c1111070814100b01c007805500d0742d210f01030950b5011882c5447c2a01c0303500054600ba00000e20b208104940c0c440b0108070070551902c10362543c01642c803aa1450081c910f08100100d04a8000003001e90081c0410403c0c140e0180086014640101a000c0101058101035075580710302140f1541070340c217042c1c034082c25075409403c46104a1400030b013101000800c0412030b0b1284200320701c480c42007043d60b0204001c14603c03854a1303000640201112546400800c11070b042d201056803880d1480c12070703401004156007103442c54603110700480302c1503460f103107990302e620b000c641262000e0b04100c00d90000409005200b03800f01011341030403402907103038503260781404054000c00380018010810307a40c03502d00d010300420302c080500906480d46410b14000303010315800181c02071002d8040020002080020072074600c0250f0249004e8800403c140c1d0440c0140404052000f00803056581408120000310b03013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 587413821 1250 587412571 587412587
    0x203120106031104091d01110702060919050d06050714160f0c171605030f030d05040f1a0a0c180306020d0204031205030f151c05010f05010f05030c030601030201 71
    0x1006003400681d2400310780f4820024002c0341c02c03130081940380041ba9500107080e410f110070240d000034000d2144820020a00c0030740d00075482d000750484424000780d442d070300c7e0144d0002c004080fa4102152071580d100b00085940c002e50358103849160342c44061200a0f58020b1004001d804416812480c080f1004002040201007a80c003404200c030488100003048800444a4014060226104d100801d003420310794884800043c070340c2c10040401c1d0002840d05001c40d0510342490000061400d2910a003541c1c00604401030081314103400c0110a000054800c1e8441c0c10501400180e2030a1440d01e11034110884400b04040c6050041202c14444080400b00c3d8070019258415000350300c8641011104010307000b0340d000144498030003c80000c0e01075116000c1c5114032002e40313507200e15444010104001c60b003500b06050300708406485554501484050440c1414810740c0000f9000da42d040500f01191400c3c0c008421556a1081c10002c130720381040326000780325049020384400e51459002078204a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 587415071 1250 587413821 587413829
    0x50109050d05100e10050a05010e06060a090503011416020f03030705130803182706041d060a150602061621020307170c1204080f04050a080d0f02031201 67
    0x519048840c20030003800f40900159440e42d00028810060f10107107094407030b000002c0002d441071500000804022007030217454101c030710315580e0a405848040034001c20360f2100403d00d040c001040c1000034140c0307003441819044034004011107020700b07000d80e5420b80301e040390062070212341c403800350030034850b01c003200322a04400241441c03a9240541004505c0340255980003010f28003001c200400030080003250501039200071140056030610401d403c840d003841200c40c0d07495001d501c1780000d58900b0103501184103881c16110120441e5800b5020600d086c004079034002c0d480f5180d00c4480300c2564072186d0340e4041c1842d40007030000c518011110420841e100c90b228030401c6020f00201440280c1080040c003070781c410403000d55a1703182551014010030412089507200c035907100300240854040c0c0040e610f0b805200402004181c0302d0ba1078428580d0010081e503881c20380200700c0021030340d407642c0402c40140300001c081c040c400d0740010050440705441d61008155082007003031030144810392203464103403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 587416321 1250 587415071 587415079
    0x711100e011d06030405030304060507081005010f03020f070c05030f0a081e0c0304031a1e0708180d020a050d050406020712050a1416150e0103020c0307061404030906080105010905 79
    0x12100c1c80e8200140c080c003210b005410400000c00d110a001000c130045103d640920b80900540e00e0700fa1781147e81c4202100c1d00c258480e01c4a00a200307941c4603001036008203005140c0941850310038400c00096902c0507800711600c0344075881c100403604050110f207c5215518014041640103a150b140d070038843c8105401620742030000d0b031401216090203580140c0c031004203e949454480c54418030400489861000c02800e25000034020044154907496202941f03103640c1071034903000b205481016003c1c2410190701c001c0400043c48800400039100800010b0380101016002401d14a0404c5203000321074042040070002030200d9500040c40c0003c665208544880951590030110709290800c10000c1003c010740c00800c5024070005214000741a06d095550103031507a601091030820101c500c000b000c14014100e51a40c1e41c0a580608000c41030601600d250001c50355622045411032001c0864452210040c8418540c2c003e0154000c0e000501f8815055410540081c0c001c0c0300c3c078800d40d449 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 587417571 1250 587416321 587416337
    0x1b27030709062711120129040918064116030b0303031e2a21092103190902030f0d0e100e13090c1203050711100e01 51
    0x5014041c1d0058041c207280b1036406031a000f480703040565501003840b50020180d148403400074100c8407c0380000d6505039400d078440c45c00389000c2070100600b0f94460a0007040070254080e0f00407841c180125407039118900048010710302ca0451042951480c0c50701c035940780500175526281020203030030f41d680250310100b001d481d0201901c0102d0140148966094040c0030101c00d001141d190a03003100c0030801825644107040c2d07600d144400c200b508400e0307900c0d50803080071a51404000c0074401000210100621080e00c007a40792201070a20380d043e1440c40030baa106151108a15104000c20b0079907504a1710103604e1402c000483c0601e0f40c410002580c0e009a40b454100110b590400481407020110f038142d411512880101400c00c100c8000458058442c0d14070302402240324100c0245d0b031103001001501c07080120b004000051195150485407481d50400202d18010600316040145210f030707030b9003503944580d840d0400070f000f45000762a0242c4c1e012404410701d2074025281495501080c40e00d100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 587418821 1250 587417571 587417639
    0x603020c030d0908091e09242d12070b0a09051009090e010c080408090114030a0b03100605030307020f041d0303100503070503061b2703070906 63
    0x10540c49080d88034964689060761402c1000704d400c002c0d00110b5400c54007040072a001c83c105244400c0b040b200d00e0f51001015000640c82c04030310300030104140000c8010303603182000300045400054080c803080c428110140407451541c0040f001066429800d96401d01c8198944041c10707641c002c80d0190f1a0414804101244658402c501104c020700d00105941d002d4180300c04050203d09850169620080c184031040c00d2080c41401092445189603485030031a0740d6070340b94041700b60096001310b03041202c090300c50311180c0f003480c001d54099507038501c00181116003001014901140300c11201c442c141001c00810180e900802a107001d9030301a15403d5115490000050060542000c040c01c5151303d0301c142028880004003940c403a250b0182040350181e22002015a20401482650341c07560045002030f000b102d50507180e84540220380300050800d01c44d1000014944015405e095a5600c5c2d44540a842e250400c107203401041c0190040040a0810031200394403051012451128401240040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 587420071 1250 587418821 587418823
    0x905071202041205060c031902071515060e09270a06020a180e010e0123180403030c0801180902030a060c0e121f0506030c150307180305070603020c 65
    0x198030284010031541c1d80e0b02c41061040a000109081e2140c0c0705200000c1c420840329402c81c1c3c003e03041e400000080d100241e803c0c5000e94802c4030100c8072641d010340340d889d95032141d00030501c6841c0082800621681841c0e401130014843e880d0703541c0f00f0701081d414424103103441d8030302000014840041404291402040c40d10f0100128001005da0b48006a1104069406000000410851070000b0300c010360b43c0021404255080c00f84401d50411381c40104003405d0920282c2520403e89941c40c95400c001400181c0e41424840e2980c01d0340001008020416926203e07040f800c80042c200140c1550420608155108050303c190340b0b03031641c4604800556808000000e0207960000c0140030031114510003d20380001240303081d0050790400d500c003130800000b181c00003007550744004080b0100005020403000e03010150a00f0b400d80907014514030151988901c8100f143c4000482075981d04002c0d400601e411101b100e0b0066041c080c06080c4000341c000700f40303c000c036802d6281c05a100c02c5445212 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 587421321 1250 587420071 587420087
    0x1205070f033b0709020702100c1406040803040201030b060a0f0f03111306030b0319060b0d02090708070801060c02180403020316030e10090e13170c07170313090507 72
    0x10380c900b0300c041c00002401c6803034500010b003642c00360010741d0300060341e4000c118203030b00408000039803089461890160705445005095031090107049104081820a511142030000a07107096400150010800040d56018000c04d5420407003070354282c2c41c02c0f040210051800f42016a40000c01c0120084a20124403a801c8820511359140b00e00c4e5407160055905003002c0720601c80d240c0403a06184280d01b0710716020400104410000802c00112255956618014446041c0c17159100c05280d00540168030382001d80f91040304143ca40c8001e90610a401410302d0070141e011908005806140c1801038440005040d02c128030304503e030016490314a0180d003903008006501602c8183d2040d910103240c1e20950384c401c004005d4622200041031818110b580c5419805409800000034022035103403421511800c0c1300314000d900c1301c1564024022843c405610098045d021707a84110401d02c40c0c0d82c1040c004420820180000314500340d20601036000021581c480c3c600307010342d0b803000506050f00078011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 587422571 1250 587421321 587421371
    0x1005040806041416090b0f03120a03020f0d020a21050702030403080f0c0109030801030614011a0d2d051302010212070c030f0b0a0c231e070b06011205070f03 69
    0x82c1e044c0782c0c503043c0800042c02d030110424840c1801031810b0400d03081c04284100081d9003c08000c5c80d2201e0f28074144c02070340c0300304810145400c0400486102d140640b01901051603140c0e200a4403000034910410f40f90014012500403615140c14000100d40000c1102d0403241d020306680d44071035002c2ca95145501403120410820350074061941c0815501c60f02d2181644e00ca034800300115504103803140c0000400f4000d0740d2081070062003464411000350042c00c034901029202180e8810500b00d03007010b0f04004003204210350201150006140c2c500e005450740256082c41e00c0d4070f90507890b00000d6a4803440d2030f14a07100000080c030301c01800030000c01e54000c3d41e04001c400803100b466140119100340c049811028280c940101c0e546418420661129442c0200006594007600c80f403446071190b0200c010000104517100a298490075400c0180c20f00c2c50040075150550b00c1c0039000540080490950924418609000c01c5400d07900803900001c04c01c910701e03001408050000131281d5400c0e034041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 587423821 1250 587422571 587422603
    0x20303010909061506080f13050a0803130c0b040609060219061d0604080711090411130e01051608060d2d06021b160609210f08040510050408060414 65
    0x710200704645c011000c06d0082c48030f1f10218409582c0c80301c41340c5100a141100074201e1704452000000f10b80307144055070308800b00300f44103c0d09118990b07c0202809856120301080f420101c3c00304003903034100403d50000c0c010b5001502e024155050703e00031102001400411665070340e40b001c11203d54429a03400814101000c4500f28141401d0014540c1c0003080c0c00c0380c0b4074078800340403a400c1c02c22946140c0119808503506081200400401410b40303294103e06255655607102c8030700480090040c1c5008103980303030032000c0795420500000c0c40c1240c010318150260078401240000140d01032456a036206a003078040d04090321713038500b0031001d003119100039203054008100751200c00c0381d22148446d4181300350b00705c030700c3e070319115190224580c0304ac418200420218441002590080b8259010402140042c00390700ba500c1e649054820609500c1a41c008802040520590134540030003803c100721403c02d1400e0070719103048166521001040180362a03c01040d0704e00c0d254007000b0041c90468038075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 587425071 1250 587423821 587423861
    0x1141911120403060f020f1e0c070323011e0f0915020913060501050702060d14090d0e040204120f02010905091503120c150702032802010c0f02030301090906 69
    0x114507210a07040b50006903940c903d07140440700d0468191007143c0b19003010f0301c07200d0300703208202d180c0310f40701800c02c00300c1c11400f641000740f520042d2007230080c140914400c0448440b82041071314162002d40f081c00b00810350740e00d89604c3c6000305c11034072004019602ca540f0b0100750701000020000281c05558030082c07050000300d40014000c1440c0d0054180e10406884511410b01c500e015102510224402e560120b181000348030f01605100d4000c2c1143c800411022602e02407c8a06c518945821286000e060b04560b100c2c0c0388843d400400f01540c840d080b82c00354203190400b105010001c940802c000c0c03851004030141d104690054000b00c0040000800c41c1009150920f40c20141510705110b95200303000d01d281850f02d518050701641c042029620003804541c0e42c481e0105008007014102000390f100a114040080c54068488440c1014211007280c0c25039440700c000e425140305059600501c0981c07070105040940c0002030740d0444580e804089002115814040005c04801d41c003800c0c020598 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 587426321 1250 587425071 587425093
    0xd02061f15050a11011103070513050a0801270b2e0b091c150b03030403170d0b090618060f0a090501210f03120b060c010e070501141911 60
    0x210703024040c81e9109850311303404500c103000080d00f00c48500e04040e003040000d1010a40443c0b241c00500605800ca582d00c2d19101e8807000080c00303280c610b82c803181c5680c0d190740c8141140e0403405d0040545041030304400b0301514055503810800b10001b00054603020f10191400109441e50404c12154424107400140b11510f8142d4200aca60010500c28005c2041d40b410080b0f51162009009125820800312000c0c40d00411002c0c001c0c0c500017001d1a0300d0300c014400840422080344032810f5030005101e442c0d0ba110b030507069110a039054100301d984100302960410445450b205400000e2011240415640d6a140c1c0700280c00803c1d2410305980000d0161000301c1c003442c199108a040e9041c005051043d6130401605401841d0b03451001015089070300e21200c002805650700d40d21091000c0d0010031801000000b0841d56005005000300d16034540603490745889042c06864094442842c256156040514035079003203100303113080d00c034210900d4686132821501c01c01c4044400100d04043c0d441804103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 587427571 1250 587426321 587426327
    0x7170c0d1116140f0d0206040f060608100501030c060e1f031b0503100510021903050f07150e03131406130b030109380a0906060302040305010e0d02061f15 68
    0x10401501c0ca44900f2200c0000a640040d090320346580300e0740241542d40c0e40b03640d02c9e190700b040d6000c1125110388540001c25900c0e824001061040c01d00c0d4000911585141020041c18046500c1501401a80f03594448251140008001890210485e49441c2c2500c148110003c10100082c6d02184425481902030b5950040007180900b0403807940e0740645855000f04462818001020390150b803211180e03402e4400b03000c075558407082c068200303c0d050035403054821106c0e90000d0411110030040d0801d0320b88203500f52140d050340341c0500d8000c41c10450442e2488400c4500c500031003102024060503240c09a5850085807241800d50f01141d07c6a07a0350388800303800342c1080c020342c03c01900f040b0540d24500031072042030702e0400d02044580c2290142c1110b100140c058165156002009040046825103060240500926481c0d600688d540c0c40c504101c0d007103401404491880782c01c8645508402130b0300180160300224402a0501d0980c501174100003450304a82c0841c98011141c1c40605c55160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 587428821 1250 587427571 587427593
    0x60903081e212409180102030a0f1415120c0402130e0c0304030c120201091b150e030c040b280303080a0203160809010612060507170c0d1116 62
    0x500d245074040b550715500003a00180c071660598050a000c412000d6030700e894124a0307075400880700950702c50040c80b881030355420399000701c800102164a5482e070403900d64a620814594034860526912241014140c05440080940026109801601c1c0c2000b803000709101c031520000c0000e000315922058911454041095407040d281c4e4040c1c07080018101407440006c4030300c43c51b4556901343c21403c4980d01d0306e45030403612800a04540d6a0084c500c00550081500f10001d4541400c00d01180c1c902103140d80340200d2110031100700011501d0401b010b460007c1d5001c0340078411a00825100b19034404641a902000e040c2098825090a51140c400c1c40b11180c1046c2d0780250303507503041962120054000d83c481600c0e801034248995040584403840707101025040000d240001c68078a40d00c43e0420400d44481e8001d507021a50746042c0030105d50031040b0305080b40c00901c00c1400c031b0318007007512000d18040c6000d500501d903140c00180d0400550941114010403030070040300c404d500f29040540c81d0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 587430071 1250 587428821 587428867
    0x15091e09021201210503091c0f0c03050c040b0f060705012007020a0506090f0111071d0f060102070b0a0c1e0f050c0f100c020607051219030204060903081e 68
    0x96400da130030100300203c0c112070390503998001d401075103000804804c1c84090718120782051400d4105040d01c50014a8084600310058040d00b01c1a40544c25418030a0920900c007500a12452801201a410340c540210294506200b2501291610b40501f0f1050151100b210b8601410712034101030710f002c941000180021131300030f0b0380d0742c04103940710414018240300d20080580d00140940c3c0c0f07001103603c17400d0001600015032060701d401c2a1b1310b49035058031488403105000c2d0f0390742300410040c880281c0110180e1085092005000306864040d05402034070443c05408100500e2101c40c4003800407850450280752030103041c0102c142401d003018400700b00d440368102d0720340c01a54207407000c03032600c0401d001c00010010030050b00c900f106a419141d05803d086c3c00c0760007000034044803011032070902c001c3c0070904188040c0d0399691901e202144801a07120169400d040c810300060000581c0041c011013520791000e0000d9503a240080e000b03c0c4078a030361141e200d80203c0001c41c4a080080010303200411 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 587431321 1250 587430071 587430089
    0x306070216050a0f0b0a031d07030b0606091809011107061b03051b09010309051902030706080103080a0f050c0f0102180a0e070507022e0915091e09021201 68
    0x705459004209000c4024800c80d04083c5148806000d001d41c0321006280c4403c40313081c0000c0c0100c480045500d4050b4640b003209084e0041501081404001c1c0c8405034030003000c43c0d80520305101c40001405052151a030002200c903100c1c00540c180400354011440210410a90703608c4d00050300d40781c0060300f40075954140ca4220080060007050290003098000c82c0c011105e070055440a03d000c8403250099941c44e8102341d150892000825410b100e0103800c041c80a01c03101850489005061400c403403a0310803010071540c400108040742d40718094401324452403070620080b00c00d1241c00c82d498051422410b940707000f81310500449490548c01840c08031170541441c418140c4020800c41c60f12001d201e158200340c60b0b080000c05c41391295000b401102c2c8020a10702e000010341142030002c1c1c2110342108540301c85020071b207890725000a1190010405015021541d42c410340d0f00a110413910302c2000000300006048294601e0724035440400b90070400320131034031610b600c8614a00d8082c00e114052079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 587432571 1250 587431321 587431363
    0x16030c290709091a0906040b130b0a050108070c120c1505090d0c020a0b220e0106020c09130201080402060d0f05160f0206041401090c090e011410091a03060702 70
    0x604441c5020314065040698a2140350051002c18801c517480020003855100c5da45003603140065890900400042e04000c20000b2260042c1d4113201c1c00300050f401283c14003125004010a4581c0204020703441f0380d00c80e82c1e0a00e807590180084d11780c0f00008200405a445252890501441d180e2015100e654403404540e440510b009060300d40403408000139400010903a000e2264020501c0103211101c15034088250036403003086848201c10a80e00009a0030b610480100100f80d4100885281c1c41801c0302d4104075810719002c0c10342031504c41c1d00001d0602081d94001015507481e02d0030345080c041005414000345000322008001020115845485141d0b150a00d103402032013120f8070000c511340d9800400035901c030794444120a00740d4a81c801010340d01c802c917400024000ac04060020100e2550104250002e070702c1c07150070341b0000100c2c001c184041008101001c04035034800d6085640c0c6446c000303248540da0308581c5001560920b4203405201300d2041c441d02550019181e0b140304407060f02405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 587433821 1250 587432571 587432579
    0x1e210c01020c1f0302030624070302071e140f040606020f190b1f0f0609061d060301050112090c0605030412020c010917030903150108010b0616030c290709 68
    0x1810f41c5075801c05074002100e0410640d1050080e8000e40d0003810003003083e0189440300c165251100f03032080301070000c03510105990040540401c4180301070040f01d02001d80c159181540c07142d4601d130398800c0c10f54103d104000c600e8103840300c440c86030342050301400507c156622018069a60300064580b00702c2c0741b0510107280c0da8030785085005008207034130000517105e0740ca4007a0b01010000555400d60004440c182001813490307000490300d002410710b5125140d10320701e8500040c04120004000307041d91640d07052501083e5544030102c0381992001d0910784448441e0400b07802c0145801c070001000b501607844045a656003003005948030743d1142c55000b5079000070800c01c0ba02c600030340c0c5c942ca02080d0151401d0085000040085010071004012241860001e10029240107007140a0f00327900d0400100502007483c080c06954003c1c41c0a8846500c0c1c00072200c440b4003a10310855000e02000126485075007040300444201c802d1194408507103010003080c40b040d10300724030709a5010001c02c0076400002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 587435071 1250 587433821 587433829
    0x30c0706030e060a05180a200103020c1f020408161e081203060d081201061e051605070b040b03061e0d0204050718141c021e210c01020c 60
    0x2140740310606000e0031064840001060181c00050030406411b0b41c05941210a02c130300b00000c4882c9030050001d20480442004c0b030021045110b4482410180104240841080e0000d07000c50702c0c070710815444a8030405040700200a00a5400150860080b03c50a10840c40c4011402003a122240740500710507a4006050000c404644680ca0664201c1c1e075252402500c50009143e000c2d0014080c0c04010802e5500c0004652244000759100c40c01c110051117020303807188549607003118411503280210409000030f031180c050f440030f2000e0001e01c050074004020086c850000101b02d5610b041d62116150038540381150012207071640030b10449480030040c0c0d004106114101c0d00f02070441200202e081d0240805004020b14010600000214580005c15080360f018014000000b8403600351030700408000746e5031a8243c0070081035424000c04009a0358402c80f18050075030a0301c0000d011520000030400c01c601e01244840310461420b40d001c5040c0340403a440750385090907401d90348007140c407200300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 587436321 1250 587435071 587435081
    0xe040f060f14010c21020c060703021606080702032d03270105010b04030209040c0f0803043f060906050408040503010b030706020c040917030901141b0a0509060d0608030c070603 78
    0x1d010071a085c080e11914440340010040d00703101a1054800c406c810f0b0000c180b0f160700c54282180103030320400d0701d4600b500803400840701811451402c80f090f4100404000d60702d0090389504400900e00c1184190290189551016001844a00a0303141d02d0700c181c20344d0b84580030500e030100c1d054900c0f003d9a0780450620905043e6035100322802d040c00c0c1075401344150800c0081c0115200c28a020020a500000600c1440240803002c001d642c0c507814420904020f00d80e502d20115403121400030313200e80c04050030444c42c56164440d00720301500100c1c113200d00500580500601103a25080600090001103002081643d40650092103061a9442416581d5006100f11030068000700307143c072800d2500d0340151a01a000d15455110001030607000e801d00d510584924030349039500c2150541c04410180d500360f1000c100300c614400040300005480d00351241000c1c0341d00700200040d061175503540305015501c203030300760460410215031a0074400ba134a038000d42140f2030a1007183d0300040c0707083c071034017507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 587437571 1250 587436321 587436323
    0x90f0a0209010303030b011101050a0b130204120f0203070312050904060506030403020a0b1e090a030f0c05030301030201031512050d0e04060b0702060d021c02070c0e160e040f060f14010c 82
    0x10020700380e00e9910700701d0042402011403410046541d2070424900d0003401698014012600006964a01d00c402c1061340ea042d400f849210b240144030800c00040c180c103c1e2401c4a40004281441d00401d1002906014480d00014401141352548801c282d6208024060b004002c0d1410880c03a608d81e4100880c0d400f013158000c00581c82403002c20001900c40c60301a4012500104001c0e02c2c403944000e03071040d0801119880c0c0f6541c044040201890b6020000d40c0150380c480c241650030117103e80b9030b56100e110500000c0d06040d11006c0340b40c03254440344409401030407000c01500c14007401c1d260050b1a01c1d2602c840310005169941480e08915240c85204111804416a1842c145141d82444101d40009020320703403c0f030f802d11402a8001c801c500594400e820001c0042e0307103006501d05007810040c1c9800c50710100d2000020040091500c029645008503581001d200e0703100d40000042c01713082c188602000740c0341055000920100180c1c420425940c00022440604c3d10300c2c001155865a4048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 587438821 1250 587437571 587437579
    0x1f05070909050103120e041127040615080702031e120108060c04170c151c0c050a034109030f040b0c07091e05090d022a090a05090f0a02 60
    0x800415460255100c2181b55030701500100780d0350401c04488400e0b82202a01c0c0014510000748801454603404d01200c1d0b02c60112000c2020a0411101c00b811044190801007400803400101d4406402081951004190824004c8101c0081a0600d04d25086181080c4103640d1800c001f042c1c4510105100344104003240826003068600740c401552600400945a524064032500b40c8194882c43d4401e0441c50448520580c3c6062072244914440c0b101c2d40c81040e000d1615a0102c14254844d04884015020780340105020801c0f2040c05441c2d10261040d820003011a015035010206582d020720104503140c281c010b01d951034086d6261a442051864040582300f00000e120480041c0301070103180d101c1800700c0d62040d481e00c0201e0215000c62070480044c8005102d07840700890640540341d404140d00300606840d115004010b543c0e83c5a8510f40c1e15614050000d8000c0d13418540100540e02c00001d10f00e030301d9410412003140c014901a94012128011101520148100001c04c1320001c0d82c00740c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 587440071 1250 587438821 587438843
    0x1a090d0e060d02040f060e10080402030c06090f090a051806090705121009060218060a1e030f050c040807050d0512250510050711030f03091f05070909050103 69
    0x404001065000c140840e242c10b50a01c408140450b018550001502076a242d200760303940e10a0410044107803512040d030420000502b0440180c0300410b4111590009980d0141c41d00031060004250302a0907805179048564002089180c2031590802402051901700341100d10070030560342a1907070806ca410301e282c8d0b840a2402c000c1402c1c0b01a0000c0d882000c00256030b154001a203020003601d070b8110081e50300540101e500b0800303044000341130080701d0b4121445031030030a0714800505200c01400408000403240c10400340809d000740c100e9030380414042010849131a00e140c400704550884c1c0245096440303000746c00300300c80c2010f0307041410b12a0064010032107100000e80b4245158400b40c060724414400c500304d04030b01445c2e4101809518071800180801032244201e10701281c1d80105450700300041041e54504240c80882141e1845c04d182400320307681d030380d405026440c1a00c3c0015411f5100d29a01c0306c8801040c0e40e911050040310346503a5071070701e166109050343c141c4401f0b01010b44603144034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 587441321 1250 587440071 587440097
    0x307030209060a0e0702100c0801150c15020406080f09060c0d05070201060324050f0115030e0a1e150c0e01030b36060d030207050105030a06030803041a090d 69
    0x903501d00c960100000b014412042c0e00c0d22641038814900b90b030f03818050380c4602a2441403d8440c05003486110103440d2201031580f61007003030a91110700c2050345061200003403201c0c05010036142c2420038032088038800c0d0340d6540c3c0c17140024403800c4c0c221821031000f050319000c9000c1c8100414042e02030140e07a08950704040198981000170200a0700d48400c0d03650340d41c400400560001140c4401c1201d218003000c1c00d001403131451b810ba0350000c080031440780d00703180144541020811605003651603850002804007014003400c0c50944c034800702411039882c90b20304000300d16015035003c500d40d108841321902410190304030003c2d210100803a102041b0b48800403007007544240d2080200d90381c01000c040200c840900c8100344032010508052003000242c4102e02ca1601074030b9500d030801b02c16144268413100380e4134003d44030880c50062a0400a00001241c1e001545400040245821081465403030500d0726207440612245513003000c0c18000c090001d601941c0114115101e51306540301c0070b41803001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 587442571 1250 587441321 587441329
    0x30d140c0708010504240510120c051c030207060c08040e27010608070f03080f03330108070e09011a070c08060405070b070c0e0601050706020d0b09060f03070302 71
    0x1250404103440e106600000886940c24056a80102e01844216404184d5669029820484000d00f0b040d00d0b41081c0520081210000035401100c2c3c24160302132064803035141c8529000c045501050740010058103e465420758038984c482241d100b5001c540709143c0d03604080d1202e0407610360141034003c05000c01c100c85441c000006a0140c1c0d0505080071202c1c100c006000224000096a41d044e07544010501c2110820002d940140080c0e150b206440e91840c1d54400091041c00c482c910030f40e1012010501c2148a2050141c91001140006140004445411407030840d0b60403960700180410010400103409094140000c4001030b1040c103e503800c040003c0e0090f40501c0d069004400200b00600200e014908450060500780002d000d180c103240c20300a15010290b0404512038000300040c100180c1102d00300d400321100c04540800340e81e030300341c0161200d00031900c000d0101030000031059100a45680507124a02d401c891034002c035103c9605001e10083c0213100150141d001c3c00042c0090302d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 587443821 1250 587442571 587442577
    0x6121203280c1e0c08070809041127060a0c020108040c05060c01060914060904110d0609030e01030f0204140d020406050a06110c0108040b071b0602030c070201030b030d14 75
    0x14000380c040307072a032203a89944007210284262030300000ca5401480b440141c944400310081c82441c60555141c1d0b072240c840c0c2007948101c0304010002000028014403c0d11203801181c600150b0412543c2c6a05070040c070141203107074200070000744400c0c0d9544030500e450100150b8030400c4040d42c440075a1541a4015954007030b0241098031a101c0f60340e00040c0942d00c6030000c0071180034060022440790b1800389040c090340c7c0c80100000700c2030036040c10003504e07450780803555901c1070f04060416081000c0a020540200c980740c0040c2c656801c1c201c2410c1416001400c6082900303080c0d904002c206101c10b60442203024500614004032921310b060310052509110b070080c0240000c00004042c0c1c0d0706c80000351a05000d501007000f0881c04071f042d502051007030002501050080c02c26041615180c0c0d240c40010704028403d0090056003d0700742d410310f01c480004a6200d42c003407011035481c204000b42d500d00d0b410503142207001a0502d109110305c1c1c107010851a10703c00d059180c81c0c8182c02e40b064200080c0d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 587445071 1250 587443821 587443861
    0x1303050a2003040f05180103020609090a020918090f0726030c0f0a05060a0501180504050a0f2303071e0213060603020414060a1202090a03061406121203 67
    0x1040d8070384140740356005100a10003046003c402e0b08140303141c1014020b1780d120ba54034410040c070f44400100301580314034040390b0142130129001030300c40e5544000d0030000d029003445142c01c441c001d060104107282e900452405428000d040310f5240e40c0031402180c0d26180c0c0d0007101100781c403d0b100c1c1202c4444019103589551201c000792410150302c00d03521032411030415106442031703128054420502409019040d009a00b91409200c10740c10803003044a400304070742004d419565184009000d2007414410f81c0ea103294000000f10400c0240c0c10301c1c44002a4403441c071401016003030f41c0c1150007800003086036401644400a1054040d9014184102c40c1811005a8101c1c04c6075213000041110381c0314000103801551001621281400c0c0c0d019440c6100d01c0c07180e8084c40082005590070b5800c040c03c101c032284031030800b503a50000d0202007901006142e000801e61800c003a0031364010081c51044910400c3c0680d01c00203151226080c0565580321048000d010a00410115209811340100480030b2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 587446321 1250 587445071 587445107
    0x8032401021e210d0b01020a0f15090206031501033e041e0911090105180f1305090115030b010e040615060513060e0a0b0c010b0607120201051303050a 66
    0x80410001043c0d00c940c440b203c003080a0f001480e001ca0b5000742c03007081002c01d000e10044c0704512207aa11040c00000b000300c007520082030003a400e402082c45420810010b070f4081c00e0152242003140500b0030121401110501080c10f0500104401000340c2e0300c201c0700d80040c90303c4041c0d00040106800c20510041010010100800c404102848020304000b5107240354220010844e183c414540c00311800e0304094019140104a44905a1380c0081510500340440e00f803015110104800a50070524111035a80c000126001d444c1c2803152980c041ea01c0380c400c0c5030003484400d01210184030f901140340401499100c5000040c0a000b459803551a8024413486002a41070319101c0d80c0c103160b1005034400c0303000031000201401b0454030000c041d03006151500344060154801800138030036070418003902442c01c0022402c0490110f09400a10203160040d00b0a503807038030642800f10482c00c061426001541c2494041201403a4902d040109660036039282d03400c00f1100d80d000c48113400b80c14181012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 587447571 1250 587446321 587446333
    0xb0a020405040c0203031f050a151e030606021603050d050c15181005090316060204180b011d0f0904020103090515090d020309062506060308032401021e 67
    0x100d88461003883c0c40584550021900c0e0301e03000c0b00881d01c00860603180d5030094801c2d4070070005900d40d01081826503c0040f800d26140c0380340701084071200000507498030100614041c100441c0d42640c000015103006600b07881c0c096418445a2081b469203101c0104564002e860306100148550007502030b005246c0b041e54003099203182c002e0380305501983d0612000d50f08900c00d006069080007481400c40700c1c4030090080e0328160303d005850340284080d0181e0401b594810004115030355045501500c1c030030001c0101901c4c1d11542c1002800d0000d2880c2c0802c0450008680d10748841020071a4100014030003c4140f0481051100241300a40101c0c141522030500380d000660502103080103414a03407001199140c03900d085440c0a450703403643c0c001e40d00100042c5a460f02c550007140c040000c41d460a6140c42213100000c0300704103500c44040c0c88a0f2500101000308030300382d401580515442c036030380300e6400c050301c4c0c1c9040405030390707240745015a12003c801480c14041d640d0f0056000103082c15190 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 587448821 1250 587447571 587447579
    0xa050307090e1504060e0f0114121c020c031b0609150705101805060c0906270a0f0605070209060301020d0903080a050a14310302100c02030306010c0b0a0204 69
    0x2c400790503105400700c07105510442c0c106090512481c0e00400c0d000403480590b0810280a1a90a006000750303140380b0f0840c0301090141d15200e007109041c040c038504442007841071020302c800c0820b00b420003a00502545200d84618640001c8100a41010811001d18001041c0801880354821b6800c2600401d10004202d0300034036142c09003440c00c0c011001f1b0500caa145100b8842112141d04c41c40380e501c5000441c0b000801c0001403119840320350078013100e43c0c0b8440d240015145006140c403052848c405040034285c092103440c100e0071000c80580d100c080e01a2101c03041c4260f4109806a000011024005a0090f00c1c01403806078011401030001498241c0500508040c0da01040c0280d01140c0d10310107000d1144214400c031503000c00c1801e0104541084c482c54600d01348809000340404207002d1400050907000c48070b001d181040c0d0401b050901d48079074980a502c6a61219030751055503e4400d14048460020013164400c8105030b48003030340d021240d520f203908450083e111007015130342804085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 587450071 1250 587448821 587448839
    0x50f0307030b1309020118080304090911041b0f1403060907090306050c130906030804031218060f170f01121505040606150509060d0f0e1218090c0a05030709 69
    0x70f090014025808100341301d031030001421043c6508080080c155010b402007100f240080700752070548070b0031500455200d0035810480c112517032021780d01d03500c00d140c01c01c0d040ca2075142036681c0b98041c1ca280c0300ca41c00b4440c0d60b1401e45582c5aa50161074480c00d00304001580703454080c8401d90301560302d040c14460301d0f1326501c4000844c1c0040f181603940707040000d505d0010301d203000700c28801010403007000d00c101c81c00c41d07035441114026480020000341c00885181c0d001c60041900791041428000310841c4103a4a01d0000e00103641c0300b00440100d4040d00d8921402d0046655851141100241040d141d0f4030300180d02d80c035410341110079241031042414028a64501340196400b56000c1d220214610b0704100c20302104007080c0c8a21401e02400704124217280d141c6c0000c0e900c0917208500300140b0382c401d107021a400352030b0880c40101c9500413000941c482143c400041c101c034552612842c84e60000800910170601400e6503242d034500d41c14052309103501d102d0b00095074400c0c11464078440a035543c0402c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 587451321 1250 587450071 587450089
    0x51c02060103020f1f11011d0307110a0306050903030f060303120c22080601080c1009090f06050409031d0117011203090812040501170f18070503032a0a03050f0307030b 74
    0xf4800550f600d607504540345024041c488202c601080c0c13000c1296488000c60307641e13118454000380bc01c0b07981c90a90409954802c1c6120080d41c011005011516001185941f40d50003100c001d02844040404544107080c004241d40c812610000700040c01c0c0c4441015030290707084510142c0043d0808040c0285688200880d0001881d020000385203950500d402e00c1d09102d05081e00c2c500132007541803e00d10003940292110122000400b0010f194041c2d4001c900142025400050300241007083d01000c155000c80c4010180240c140392041d442017080c01160900c51400c0d8000c9000078031001801005042005240100e1007402c0c12410996a095803c1c14002c44107495981000040303420003071035070480ea040107414142d6901a425141040c00e081c40a840901840001656550000b0038500c0420941000e080010101e82c6c441d540c00e004031461204489a1548050700b0340500c032514a0000b076114a2f07154552940ba08000b642c201e210b10381e0b04002e00761802c068503003c00c0d60f07060300e80c4030764 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 587452571 1250 587451321 587451379
    0x8130f032016050a050108160302070201020312040b10081207080c0703021c050f010b011d451b0703020a02090403112b0302070302070504020f07051c02060103020f 72
    0xb102803014900710410a0009107644402e051040400030080d2104a1180c0d10302260301c18200182c4990b09400101d01c0c5001d03809904001280340010f010a020803030b01284d120f090a01c900b100e51946484940e80c80c1c107a4030b0f20024030140144030780c4001604150203400101d84110072100c20381e90307a800045851180351205081c8003005d4010b00c0a02901348405035a220001000b40048403541d00001c051404000350000b0000c07400c8040d0a00703554581262058000615401107415880420010010340c0c0c0f04c04103411104260701409203c400c4a400d91040c03e405c0e2a402441c10240c41001403544210821001c5018000b002c0c00140d0303858100d036003c1c6000e83c1d10080c01040c0b004140b40b41c20401d188081d54092101400440708096150603410160a4a0007686410306450305070b18001307854000c07a0f8010f0022407045100c0c081c0300c01620402c2e0003803084502400811510011001d000c03180d640068000000500250130601203c1c100000d014081c8516220040106000700c964449 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 587453821 1250 587452571 587452603
    0x30916051f1b0b22031707051b010f0b0406050a06050c0723130515041508010513020f18040f1502130f05010e030303011505040518040308130f0320 65
    0x80c0114205034100351000d10340201c0b943c001c0608a178401510800480092904000c4644001111036100e40c040e603503c120781a0b400070b4000110074409010300200d900c54001c42d4503142030801e062401d4050a400c41c1da02500d4143d0003410810120745503880110309030140e00c5030000008200c040c1c52000c0111a413450211060300c0e58410411025040c00c4a141a5140c18201406224054991405050181154001000e412605040c413a00c800d80e400444ca03075190008021035265010a00720956100300c400710b0035002d02004001800049110700c102d09041d20300080c00250004d1a801e070554001d50206113068403922a01041e44d109646214aa02031700c1402c00030b0411031f01034a0042c20007400c2c154507001004010990320300051048101c030350704602d1801080c0e8020000c41c0d0180c0300c058000100366046011039482c5540940d0200c00242c140c3c40001c8802c041d82400c408502c0e440801c00c100320400e9141221002d01c1c0c591440980088402030000c55501041202d6000300910 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 587455071 1250 587453821 587453843
    0x80a110c07030f0b010522091b03030e130203090a0602130312110d050915090a15021b090103080403080705010609020309070305010506060a0801052b0602030916051f1b 74
    0x211301907600c5003040c0d00c00c0380110103c00101152280d042c031103085198078180005031000140c1045025030004419000b07000f07000040100906034090410410b181050b074044190f00b90010506d012840103c840e400d00740c101c0c244480c001292034000300030f584005031980c03010a40326291009845406040c82000c43e04604001d911458144a0106c0030051801c0040c100303804e143c046001440001c03450210311400240d4294240d8405103040060304183c16051082603840320041d45d43c0d0007103030a40015000c13030081006070740742007188070303041c3d0f0b80c00564242814030355030b6490300035000080f085425549604020801d01c40502c05148198401801020700c940344d070034500d003101c00241040b40035120401c000404240c21180050440e2403d8541100b4540d444005404111004103a0f105414401c05c1060504c2491703000b460141010b01d0030784a001b90540c2e00e150482c00c885c03181c2a00404502c0d0700794585e488402007041c4521180c141401c649001958250802449682c02c0720301c1c90b03a075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 587456321 1250 587455071 587455073
    0xf0f04240507030b01180b04060516120e030f07080d1d03101d12040b0721030204031103061006050901140c0105010f05180c0702120d0e0102061303080a110c07030f 72
    0x1c072410540b2442001c00c0d80e0a22030501f40d80805a10990107402d05010b800102c8404414030005840012500641001c201140420b0010010551010790510130b200b140055406200f000c5015011105850010301200180060545e807820006603034114030701d18581c4010090702c00f030028141a0260307081c0010002134080c10a80d0f0481d0b40103211425a0010170343e42003440400d0201c6003516608100152520407500d490102c580c004202d0041c2900d41d514606025a00340d000703001542d101c6c011603039101b0410018146d071030034200c402c1c0c3c040a1410b401046a5405480100fa000038185000303800142c6003148851150700000074110349030743d1200100902c1c0917070b500c40c1e0050170040716035011584141004000940c0301800001d003040d00003030400c0c01c565869150100c01001d440540351400147c00c000b03000048a1503003030b40580101c01c009a84c000c01204d0081105070b241d00c0b000740c0d5451300d548060081650000f00612800100441d0a0040701004920010340c81469401e4103d105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 587457571 1250 587456321 587456327
    0x121506010306060f051b010612080c070909020f191208130602010501150f0e0405010b07030801091e0e03091801062a15270b0f0f04240507030b01 64
    0x200e81d0150080040c441d00d6400f004d13a1200440320751454140100c1d12480180c800c10f401441103a00040da54900841d10204014400014050722001c42064070251075440c0c000c801a0b07000c0103002580107003080742c5540d043ca072241d00204024840102d0010160310340055a210741058032094542c1a00814280540b01d0701d01d00e148003414042c0300a01095141030074840360341c4150702c5d1080500c104400801d0f0841d00c226500c145180c0001c0040c40b80e07507901d4400e070355607a10004003070700041c4051002140700145806001c0c1003c04844504090592911a800082211444541c200e00003000140c10565668500a92890003260881e0f56075140072400350149121706241c05504c081c056210307048652403503000d05c070036401101c0a018510950f128500902e9545826004059050350355102284001614403100303104846141e042e071903501094000c5a03045840310980c404a40000340000c0c003d1103410149d040000c43c410f07a042d00b50800c8800d44900302c0d05000004d5440c103529600390b134 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 587458821 1250 587457571 587457581
    0x18040f020c06130f0b07030b040614030d0305071b030c0b090607180501080411130c030b0a0b2d0706020a02060402100810050f010e03010f38010804021215060103 71
    0xa4200f0000c2003110741e403080083c2c041444040c1030515400c00042d5200c0c080e42011611900081082000316104d036802141d07186070f51003040c013034403804810401c018000d1140d18015405902e0300c0b48408107800c0244036620028800320104010081400d0001d1500c0c1c040c1d40c000d28001010300422300e48680c0040c181c0d4410ba100740d0721443c20000400050f40c02040883e0015003004400c01c0c40c00d04140413861140d505410741c01c855241200d41e4042c03a900d41d00c815404481240c80756003071599800000f802e8050841d00b00c016001860903541d040086040d85400c42504c41c08040c00c0403095204c2c40c00303e800c1084500c001d40c010404001c11450038003928503c3c40007500b080c211508014280386801c4c2c10300c0c000c45020304010045486c50b0ba000d09038034000039200a000307000c0350030020b00da01c01504668261101000c480316202481c42c1034103c540c40290041d150118403640a040110390420000d442640c02600c60b04142c1d043e0102401124200407811903c180581042c0380010308480c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 587460071 1250 587458821 587458831
    0x905010305060709031203051b03130b0a09170a020c060403060c02060c0c0d03050c0f07060b0f0420090a0b030a0c0e040506030c150c0d080108070816030818040f020c06 74
    0x102521304140001034070b05603102c01c0d40b9000d28001a03d640d5107540b8001e8501004840b070f60158001c000c000384190034120520905110fa1120300094272500809416603800c490018080f1800580ca400c6142e165030107008031007581c0c811211081f0310600490f141da4400d130400c0d0340b4207488000280c0c0d020b80410034150010005c407011807509141c041d00c5910b99001c0070000041640396000b10381c4449865003555035a2400031820350350f5144500c0e2041c001c0244082d1203000320403403034941c0440d00d458458654012100710200d0005600d05000034125408100c20301e910003005200801c01814400c051442000c2c0f912002a0401b90900c000d807a281d80310410341c0c4114200020004191030110f82c1c0818404143d4541c0c01800d00e1801c80300581c002d0740501059842000304000c855944001418100c4a8050984180b10340f985180c503203c2c6400322410f080394042007810000036500d68000c0503e00050640700d004501c4010028060b12a5800a2040280c02080011501c0130a0001c1c40d000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 587461321 1250 587460071 587460077
    0x90a03030903050c0f0609040203100509160207150507350702010315030c260a0c180228020102071202030a0e03070509041407090e060a050f0f24040609050103050607 73
    0x400200d9000515a1151a05207809160042b0100f10f20007480b0115601a14004000c01554030b02921003001c41801d5503500303401403107102c40004145c0c1034001203030740008030303955103138070b003000a44034002011088038114800403141d10206a54500c2e14520011140203803849035078900f0b003400010181c400121036884c3c4240400e408200159840610f1400c40e5503114000740030b280e09104085401c0d401e110641c031140100c0c0c081e4400c100d0030644500a6818160840c8411604144900102d008001d45030850a548000229000400052404a45410b84005840c0003501c0d56140d07210903101c40c541e00564808103494281c03507000340008a03911800d8000300b1b81c403490070001910034540900050244103d03041d2114441005100600c06840400000d000c00010240072307694802003114018050340c82c04010580088800c40001c0c00b802c1503a204260648030480c3c20b81030004840300c0110104d60701182403050b070300c0d1401008000d0080190016003589141002400d001d8010802010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 587462571 1250 587461321 587461339
    0xf09050f090a11060f0301031b0803030c0301030f02060d090c08070501110c04050612070f1508010501081b25051c050a08060301060f0806071805010c060203090102090a03030903050c 80
    0x1241000182c451005900004251800003001d00424054807944c0d2490f100c6210000010003806450030102c441040a6186000b600e176480302c20544a02003540c80c404040010401003002c1039025101e04000c600080845182c294414521011a1903100c82110380b885680010402c001c4203200b00030080c002800c0140001e16050481501c0c0d11a1141e018400d03995480420440d850f40c01c045030f00206488100c4501945400c4030400a0b402885010500c075602482c9802442c801c101d2203040302c0701030312840441c0d1190032a0b1040b5400307994041290580070b0000000004c01c3d403400da0f400d812808190341a0411031b04040741170900005e0400b50424110380980021603222081701c036403001a28014000c0d444032400030740548040d6001900c00429032402049406021a2079801120f0075103601d00ca04011a100c01d820310440d00c179090102d030b4454885004608140c008540c0200d96100040c5004a400c000480000590300b0603400140014824403c10a04200407900464100c0706084 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 587463821 1250 587462571 587462581
    0x624030509031e0f1e12071d010c050f2a03070b0910030e011518060b032d090c03060108120702040b1c030806030c1c08130803040f09050f 61
    0x1c16042c070f2141d183d0900700002204032801c003108041e0f95003c0d0010660000c00d81c4c48610000302c0d90002954400710443e8031007c580c80381e0080c03150380c400050302c50040d00503640c508010361b145003040000352a14000c4440e1002da584062050144075046900c200c1c0d5592440700301d4288004c03102c0602ca000340e001078011300030840d805065030746081d000c43d413414280300c9145049024010700300341494198203000f070800032504070a80e04010391304030311a2402c030080b05a8040c4180c0d0001e11030040140810408140700070036048800c258610b4800304924240443c80080f0b081800884440c0b400d03420403d100549454103200c480c0c0142905001050200b450400e0040b0381d2042c01d030002c0c891940c40c0300c03001090321b500d00480050400350035008489a0b032400d002d0103e038801c540082c402d00035240100e84614182c080130b0b46080d1011407541411141d6a10b10145601030080c808020807404000699074004000500c0035111011040320300502c0c1c0803220080e00c01c040c0c80e02c0414116081049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 587465071 1250 587463821 587463847
    0x1092a091e090203030c07060201020301090b040216080d090b0f061008010f2105100b040b01020106120f02061207020a1505041e11151902030a21062403050903 70
    0x1072100718028100240300c0b07000d0300c0000e05d5441108455031490207490f01c0018000e806601a504859505c1c00070b200c0c52080b00c080104920a040d0402c41d003030003548074900410010405040f0042400400140340c4c0c9041d102c410b00184c08540100318006440c0c10420746040c8400e483c00c11220030b061501d45941010340c1d0142d2001c217400b4408001101c10021003260014a26892171283c2200030703240341c0309012400c0000740c46404505800381c1c0c20b048032215907501c1480780c0e00481d40f080c07112510005440c0d48080381b65078007034400c1e03a002c0b10a01400c0c00c0c2a014120302d501410b000c1d00200388542e01b81c41d020312420142c10300440107c0c900402c000c042003c0029040050700c00410f0001200340600c0c0084c4a5030750454041d4200c80801c600e141440804c000a06003655000955103d4075a081000ca07507910070303414a070b0b0000340030301200d0940e0010410048158081c0d01804984240c5408803024040c44501b1000ea0b59403c80320312005060301032184a42003403060340594035000382880c1349 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 587466321 1250 587465071 587465111
    0x10290a060c1707030320190503150a08100f0218120a0c1e090e03160804030209071215030206090f0319030507050f010612080c01092a09 60
    0x4024003000800940411a00020b4800c04000c1045030769203826250800034024408580700310801d0354070280e040d000915050550341c002e03e0040c0b00d10b1076030490131001ca40f150005804005c10601c0701280002554408403c1d40140a40d80c004150507685143c0034010340d58a01c102e90f03511807042000c58421135034500c0941c0c5002040d40c20901c41615114403610305000c26030040d0010000c04400b00d4811010300408250190f103050402415445074041c0040f0381005900b1140c1e03500c1000300c00410f601080000038041c0c040ca203420b003896603903000300e10900c80c01c0350030400144000e90000c29403542c9102d6000144000401926060b0841c0e010515512a00e21031904c01d90a8501801e01c50390b040010b5070030300080007480c1c980c0481a10b0f01a00b5900030703000c1120103000b40c0030240415001441424221a4240c1030380031a1083c5803542440d550021000c828039540300e03103001011418900703c0c204071401800c00c508818102c07500c1e0008500300c0382c115040c15424803502c001455001441d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 587467571 1250 587466321 587466329
    0x10b040b18010e040f1e15060e01090905101d040b0703050c040b07050f0606030609030f0703050405060a0e09060315040b070207031509030f0c12030b01020f10290a 72
    0x421a4001c800162401501000059441420441c021a01c43d003c1c1c3c1215400203c110740d03001e483c002c1503010300c00ba695881c1448940c400307407600c00c0000d02e01c02c292103120102c06052812840352134030318101c203803101103c4520011010f0030b410040079013260400c0c0e115840811101c1520f0400e5624121086009060001016117800100310116a100d04580090804900844d0340361401c1c03406a40b15104050800480d009980010381c1c241800f2a61a01c40c0010301c01952610700180800342554010140503400c001062101040c02d440e42c0d80101041f103416194100e401c620708040101e1000000e14540c041d80018075640c1104c450401f900d50460350042070003425685d40d400c120705d008160b0b80701500811805076042c001c00d01c6a4805480b460083e40d9000760f82c40403842c01c0c0d8100303d08101c0108451849038150032864401d50042200300c00500c150741c0c00392000307100249414804242c022806541d1401d004000d5010304001c00d08200c0c075000004800240d5002030550205445 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 587468821 1250 587467571 587467597
    0x1c030c080708180f0c120106080a0b0403090f171e0307030c020f0a0b03010905100b03070806010c0210120e0606010509150708030f0103060e01090b010519080304060f08010b040b 78
    0x101040709140c0f1080885044000c050032030390a900310b078000a81d10080c0340d070014015140150f00e4010041c044c0544000d1780c1c1010018a0310781c42a5803403c00e91203000384250200503841c400451030341e51850440c0001d0104180342c8400820040855041c2020703610349180990203010042150700000c000c1d1200075401d810988492003090004c10b03a001e2920302d00984c01764568001080181c1602c0145050b078070070000810440d91400c925400d02c00781801030031701400050001400340391040700e000e81d0204042c03500481e0b8020b290b010500d491012100d01c8080380c0c0c0360701d03036582001691045078440071440c0014100340c01c1a00005c1c0161142403103080c0541d103c0444441101e103213a08480450340e0150500f5070704c1c07074011003c88006000380801c5072550300701000c070f403454041406940c4405405c060040d10316443c3c0320030498401030b00c04000c00340115051001540140601c0a0b00c01010140c80d0702071115052400100750b0007058002ea07103a5242440305220f101d240509940e03c40440c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 587470071 1250 587468821 587468837
    0xf010206040c14010908030a030603030f02010603020f0d1103010509060631050403051303060c081e060609030a14010b0f120a08131203030e011d1005060607020a081c030c0807 77
    0x800120b504440c02c2c0c000c41b2281c0700000300845010f82c15400341c0101c07806640c4800c142c04c002e14089007030703912603c006540b002202c0205115450801c0c080c401c01c912490307500107950300131400300382500e008966080c45c0d074001e64100002400c01c4451070030f402c48846c0b1120311030601020003002040280c0070340324003156500d000500301405001142c480d480b00c41001403d403684c9103007802c0a480913841c868002000315011915000039010a0400558981c011845036540c00e02449440d400080724607902d0b100c0c28030303000701055a0320f001c840751613640000850800540400c0c8259258050700060141000c0b074074203102002c01041c010489540071140690b1660642c9075200000200d030058203081100458003010590581d103d11034aa91040c005d124051300100c0d000294241c01104066541010a100c00ba00303005600c20341e40014001c06242c10040190042610920140c101280d16442507480440900e98141d030912862450b240034400c903484078000410005000d0142020301203c0313 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 587471321 1250 587470071 587470109
    0x17060f070207031403041a03060105030601030b03030d150e0907030807110f1f030606020705031b030111070b1e06060d0b0a03060203100e01080f070b072f0f010206040c 74
    0xd11802d001150031048810200d44451000b60700e82d4014810045458444c419202040e0040c0054078400d91050712082e04580e00c41f80150040c1400c44582540b5001c104080ba0701c2100c184582d03064406540201200c150803d01e403e10350740c80140c9910080c1c1d10007802000062003200032070309a02d5200b14010200c00032580440c17403d0902000050788030300c0e1304910b6400090b01d018804c40c05861545c0170b20001c0d0341c0d20345c11fa84501da24056990141c1004030440201240c1807031721200b01501800001c1c000500000381c00c10b54000c084200d030030304003807001c2c0300580006178010042d40d810750b03101800d0382c00c1ca4000100c040c404e800495054a0316088050350307030f0765034100f01c10040d5003001c0c040d9034030300d0411114800e00c00240141c4640103880f00000c503c4c3d860000354441e840240b9001401445d003440000122342d000b040c000c96414040a00c0a0b00b0903c00000c40301d101d0f0314440c08003ca400f0300a08100c4229001c413207040c1158003800403c40491800503d5004030740503858034203240c60718 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 587472571 1250 587471321 587471323
    0xc0409080403140a0804060f081b1b03040e0412080108150f090109050a0c080d08060604260f1f0b0d08030601020f030301030b0907060f08060f060c06190617060f0702 73
    0x2440018040700c05c0414000352140e00407025861207078043c2d8605080e90307180c03100b01ea0710000070b603006052010184003010290400c0da00080b1030b50800c0c0c04490801c0c1d540c6140244500003250304484070001d40c640003e03116000049540544000809048507000b5511400110400240101111002c10000c030781c1845080d4040c6030150380020946600300414140081a03c00ca4401d8400324401e410302c4141c00e5200d04fc0c4079014440c000c0c86103240900d014042c1100181e04429403032041005080303400440ca00304881d14250000c100900b8448161141030201d4600c16005100300b18284192403800e1354a8400440b04641c0c03140b001d0f1348903281c5d000102d1400745203444040b01342c0300000010050150001160b481038215008881003030751a5101240c0c0d00f6010220040468440804149545001d06002019050141816062903c2013032103a14003d415920140748410b2180d60110440781030040d20094001c00c00080004105021729070b0380d810300240001e00e072102d00d4012942c3c00d84 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 587473821 1250 587472571 587472583
    0xa021b01111b0a05040e03030604050402011b030f0f080c070b22050106050a080a0b010e33030616230c0a050312060910030b090f0d03020405030c040908040314 70
    0x400001107540d021590305000c4080c2c10042501845000008800a090328050240c2c440505001c005141140ca5103030520000d454040c0041b4148640183c1a414603591104035400407400780d81e4654440c8014180680041c0580080a08000101c0f00700201907400d10f0444000e40d0303020822441e0340e5581110301c0c2c0294900030000c4414401c1e14200307014441c4c15040801030b182c2c00c880b0034025a40d107440884d9200545440103000e02d1800c8010001010804e444540c00710b0151405640c2075041020b08070658008110700b220035101c643d0744407685c1410031040383d0168054950b0102122014006000100104008039400c1c107170b4204079624101e41c0003540e035088030b520100c802100340c0345400313a140d4002c4842c0c2e5050ba440100080c860785000c40c5040d000755034988000c06034074299215031000d40b200804000d4184100324142c00201e07010007000c10001d1041d03400503151401c050801d420411301c00a00e5100d641007040803000300390703180708840c00c036a4450340103d000c52046d200981008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 587475071 1250 587473821 587473847
    0x30412090b03010b040f050f1c171207031503210e0301020d09031701030f030c03020f1501080c09010e162109020108241512100504110a021b01 63
    0x50040000a240a909000b90041d13542c0c031030092290076203580500239a01a001c40c00742c1e000310303401d0500389030780756411408503000e0103807050382d1517401c14810880c001d40c0309010080324081340c0030802405541c0340c400c0884000081d400c0306129455500c0d001441001c45019400e01030f4a02a040c030b51900900c0545050080500250f48a00144005030010a010001580800e00703040f804170400c14050350081c1030365800010140301c2042600c08031080310b8041000c9081d485601c030001d00e020820003c88c00d540d14054200c81d129810030302d034075044c401c19900c0e0900071682c100050080f032502c15070300d030351004002050400d01e41c14a041120207880c0e40210070f201010701101001c4141168000003041c50007a01c4170002610b4001c08000d050600c03505076091280903c0c40061207190010310740500c00004081035041684400b0308002081060b1004041c08030f44d054104558102030183c2e49540d04066005420004003100180d1a000c1c0540100c51241703c0c40c25010581c0e010307600d609192 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 587476321 1250 587475071 587475089
    0x60f220221040c03060c020d091a1213020307150905040b030319080916050303090112060503100e0c0a08060403050a020715110129220e030307080609070503041209 72
    0x1e400c1904224005040d140415102181004c0030a560240000b40140f40c0000c0c0c2c2ea99a443d15203401001e5540700d2040c45c03451514101004120a2a0100480341d8001c0a480c40810105c0c0c10a204040c03500e800d40d4031400c4130344181c0c111008042d8102b00441e0840300140c0c1c01042485000000908500c00c240c82d010f46240d040e02c034809200d503c24040c6200f580c81c1c90440300c01d00d000ba644002c0e09212441490fa05030301c10800704449512401c0d400ea0b0403244c000010658030707100c60029007460601501100c05540d90640c241c1d40301801c12840010000079528007a41d603040107a0789881d48001040901400f07000071b009283c40b8401c11005c00200bc02c17074080006108204801080b52040da0300106540d070a10300c0b2042902450689518400c8490850b111050001c3c001e00c10502841001c8214010f43c201d151180d003016802542e45216800e0080d550301d151140c0b02802154002e004a40a40c0c1800c00f0850341075001022280c10076082400b2915861038188101c0d00300075150448800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 587477571 1250 587476321 587476387
    0xe1e0303071e0302010e150a0b04110a031e0b0603131407060903020f121911090c030f01080706020c36100915050105070c0914060f2202 60
    0x31807039502440020038882e600a01c200f44d4081040c1c0da40e20402c0c8a80010706221f440410400741c07181d40007007040c0002501c0070446030600555009150010300b16040825191414200c00700101ca81b00c4000d19203000d03007000400c021401048140c0001048a01c88112018012003030201d0181d80060f000c001008850301d0340e4440c032009190071120b10089000e801c00d20790440052401c101000c604d822032400400c0e001d40c2c00c0c50380c2c442c040c010100c107a07045800500b20450030744a10201d1403042e151507141d180d99080000201c020318805074001c00b4103410503807003800980c2e80450740c10820501100c003c850b002c1001e00201c1c40c2401c0b10019007e901c040c1f10040a4000007a0300e1900c80c16035140303d040c00c00e80e1142c1440c00d41e03e6441220103030740042c40e001e001c59809003024011240c0644150102d25841d400000111102400030032541d0451408201c954545011040e0f01118241c5000c00030510324229910809001031044040751717004031754507140d0708041040348a000141c56007215 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 587478821 1250 587477571 587477603
    0x161401020a0e011110110d0504060b030d180b07030905040e1005090316020d05030c070902070c0501050a02031c1506030e010e0a02030304090905120309010f0c0e1e030307 75
    0x1000354003241d28180800c401d070241c1c5607590300400300101035424030380c0502055034082c4644401443ca100d030720a00e0030400c1c05540c82400061090b588075500c81c483c0000c0c4210490105440c040e100c80560041007100d90300200c107503201c0f544c8a000c4a100003e0a03465607503901d8156a0f41c0055008590403e15000390009041c0002a0480700911024010043c035101d0116040d2248605d801c95110200c2109501c00181000601d403020640207070252405c00c0c04407414107003044200c0d8488040c29801107401d80a000400d1580d400800f801d007440ea14048000310082d4490040c104da007642201c128a0040309154250031210740c1c003800380c4a0344009610340e080a4000c10118002e000c840d842e00c400c40b98030b007038005881aa1035070000d00450900b4584005840603166030003007111a4010648500ca003c1c0e011005540120381040005c64a000c0c40c0c00d1180031100612805410440d001c1c40d80c21450310349001494940e10069400b651104045c00800c0c6103200c0c100c4024002e6469404103c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 587480071 1250 587478821 587478823
    0x5090402070f0f1b0b040b1b060f07020d020106030b010501080901090206030109090c080a0503040308032e080d02010506090a1a090c070c0902040303080c0306010201090c03050f0111040f05061614 86
    0x83c0041c42a030700489040507203800e4421420342070190144d072030710400c424410194018041c003040c20040c4801c00105401c6c0c0c1c1624202802034400501c04030000d01407040c0d240d01840b15070313102c181c107100030000c4900d5910b4110b00f0020600c02c585c113011206000c101d041e0402c1d00545a06c40c0c000c0c00c00c56995035a80d108400802100000f40d41c00241000c01289003100850110443e58110008500302030558940d996940e00142c5205010000300f000c01401001e1142c42589000d20003a00310002032600e9541400c1040605c4100c085914142c200895561190385041e0418080100000c1807003941010604828200c0c0d1043e0f803120b500400c01881100c41e0004100551007454501565983c50700400c059019074040140801c0d00080051825038100024640c04401480082028440e0b5192460001100c0d04280c8032908041d61145c0548800d0041401030f09030a40260701e8240313000c10b91901c04505014540c85004001a058040c0c4158800218102d03040401600d44c4403501e0405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 587481321 1250 587480071 587480093
    0x1209080301150c0b06090c070c0902040e0708060d03120e031c18030203040501030f110a0e01030c0c0c090207170c100612030c020907031b0305040203060609011505090402070f 77
    0x490000b5440c1e08040b8991252100740c218581c494070740410740d1903a5003000548100188601c02040040c040e00001c2101c8070200801010721200040e5141e043c4001c407148208018a260148003503941841516161038000d8814aa0180313814603645040c0702d041c80243c00482d448680600c0086804504280491041080c1c00624070b400c00c403405003aa400008070748080b5010303001d40c10a020811445d4000e4215007880c80d00c0c000005164610200098943d4001c61200350002c1e0315084599100d58161080050041107410030700c00c4200c2d169141c030711168450044c10040c540100701c00081040350a03800740028a00d03006207468249000d00990fa4038940054002304905000c0005480b00c148491143c102c2c1d0175035581c201001c0e2035001d100314140302a054800b0956510907081c0300841001010399000d51540d00030619051500400d803405501414070340c8948401e0004010b801d0000e503010700c400066040c9a0b40fa940d500001038000d00a004024001c0f03909180040c00304101004a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 587482571 1250 587481321 587481329
    0xb06180907030e030301060c02150408011a12070506070602040503070b0d1406010905010f0c020301020a11061501020604030f1116090515150f0d06120b0109020304150c1209080301 79
    0x10060195441090840a5a2084000d400a134000308010b011342d40c407034a480b9000c00d0000c0c06c008150710042100070f0056200c3e901c0b0000c2d43e55140d18101c8410260542e0001d00302d0300300e540b40403514299a03c02d880340360b103101e150720a01c80007916108020302901910f00400000701a900040d54441c524402544060404107035249800086802420910700f854055034040c2e40e54103c0c0c03402c000042d2070101c003400000061110a484100041c0c0d0240001c02c100340c80340d560420b0410007101c1503807820780040d04040200040f6a02400c450340e00040d010b03481905860015200c00140105a50282110103084003034003c01c42000c0d14000150901e03011160703115010440f69030341e104550407000b4600e034026031000301c0607003a44040348210082d10f4000040e640301480c04010b450003804480459010102c4072580c1c40d121024080003500c6035006156610080d482c0d441c1c03503a1030326000754602c01d010280d80e903181c2960b1000f512450300320b5140300f4401d50401c01000703a410701008a40003486 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 587483821 1250 587482571 587482579
    0x50106020f0307031d01050705010c03020c15090c06091c050303040213180b09070b181c031e0309140c090115120f0b03030d3602040b040b0618 63
    0x26545580d008000201c451803134041e40c2c0e070002949503082c0c502c202c0541114183c10000244080c5002c07400078401c11407245615100107a4410015502c02c0c288a555400d81012002060400c144d03a000450301c2240c1c860101e40a83c1c1e25075030180043e10011400d018135203940302c02400c5d60200300307000000794000e5000b1941c0c1581426107010444c182c441d01280c42914902140750940069a00075001d5004069001079551054603502c0002e01ca03001910010781141140030b440b0301c81c2c1081c0400280114000100521005140e140502000d8142c0d1400c00c006c1640d45000d100c4a20983c098150141d0014903460103044400009545400f202e103018807030080e20000042d48485032502080c0c0780c141d621034a040350390f100342020007401d0249041e18669203400c1d084600d540c09100801c0d01c0003e4090000d81c0780520030a000300c040b080001c0305000030304c100000e90010316800040003450303412613000c00d441c00e0010208000e0002080459005880410f010000304000042030b409030500342c2d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 587485071 1250 587483821 587483833
    0x110d09171c05060d0f022e081006030209030d0507030504050603040f0c061b030c0c05060a08010608060411160c030b1303031b0e090403090b030f0f10030203070902090409020607030305010602 84
    0x43c1c1000f0506040010003458812104640001030034480c2411945076520100c42c65203110907031200780840c113445000300006454104000504420740725500107400d02d0700d81182425112004261b40d40d4101c82610148040803891404151280382210094840a041c06032241020b2601e4441d000d40514102c078211389030302e0045421441440c01b07110aa21011040420306519241940c079a81810b00580d224081e880c0003180b50703210103005014008280d0b0704c12005600d0010300411500000e065244103e0524010360829140581617549110003100a0002c58113646810916528035610050400c2d40c2001080381080c0d041300000d524901a490510000d94000341506100700900c8140c408075095503000221404e0101c101a8003030300c6418034410180e2180060794842c0c00c200d804100f141009020000c00480c10030005802c003211422014425040d83d000940340c0540c0c3c003491444030360200300720175160f485810076a4810b80241c00d90360383e1b90035428004c001d0b0009001d0500544110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 587486321 1250 587485071 587485081
    0x507091a0f0f0102070b0d060e01030b06030d02060f162309030f0303040c090b1201020304050109030306120215030702011d0d03060501090e1302040b121e01110d09171c05 75
    0x10409a0000c1c80b05074050040d2074200140d0640c40d410103c5800c01e2961784100208901d00d00002d0580a14042c0180740310928100c0200351170709040042500442d000030040c0700a2100184400b900a031000e903200120280d0942c0403209462504101441021800c01c00101500300000505c98000c0a5081e95685045076810581d41d03c420740717008204580d428000c103c690011303845085a010000d026400c2008864807040c00d903001560141d0f41fa956a1260001301a054031403072005100c0032424031060321160b00051039107560207134140710300c9000100003480140300f90710409404034400100791500d40e0340440c1c83d03034800340450041d011a10341503000c9529805041d20100b05c5078490140311182e034449408101000c150407049030040d8540020390050b507a4a02800c15400309032004103402d01e0340e10781d106180c1c545100c0540b06640341a100101e0803c24904848288181e420007060a44152500c034005a4048900140c2c1c040b0205049000800c50342000d2544503580da4180899221 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 587487571 1250 587486321 587486329
    0x90b0403020d2a020103090c09020405031c080a05070e06070305040e010608010321090f0b07022b06050907050409051506010512040201030c27180504120c0507091a0f 73
    0x20441c90103422845070410381c3c050070403881c00d01800c6071043c034000c200f020f21591101070480b9141c012100c1e0940104040c040760500304110000701c880c45005480c206112800a000350102504014100ea00c6100146041c0d014541000c00034a015104035a82c80303103402c005107503400074010001c9200c0d81200028a1510540d0301c241600e4000c3d4680c0c1c0101007490005204941403212101803080d400300015100381c40e144c0900040094801281d50b03400d46204000440f00418100a0203d0718441c0b410880f1003001546411954030100c005a1178940340d95903403800e030484d4415940981030032486820040003207840f500c42480e40d80395510380e0726503900540301401600f080e0303007078280354400050141d8481d0b00401c1740c00a083c01d000c0011a444062940d80d03210140748018080300ca00310030480305140d080320074031001441c0e00800950606649000004a06c40510400c1000011058040c00340c00d026640080440180820003600401400130b00700c40d210510501c240303c80b4681000300c0c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 587488821 1250 587487571 587487587
    0x818041404080901180f2402161a0705030a0e0306070215041106070c0306021306260916030c031a04031205073e0a05030d0c030f090b0403020d 63
    0x3038044045030503c4072200044400302e60b44002c4006030085140300040840030b5100c68005444c05070b0106000399958111003520551420500e4115480407100c1c40f0710b80b0a01c00c0381d03800d6526103124044545840d03001201c05005902001c1c000d0b0000250003c001508135661140040042d01505e80d680d0360700710107903102c4c40c503441c00c50a0517171964001000509034001901c00c20100070b14103424443c881d140d90100c507140d41c0046600d55400200340000c0c0580711384d800c004107024a041b100f4110600e008040c0310254844a2640180d104003096040318140f0409410b0451003894983d443c0d66820001983d404506c41035038a03c1480b50340d00c107025101c2e40014402d50300340e2500310080c081c000720cc100400c4010301007001c02c0454680c0b06403048005900c41d164100c982ea50381d81e07000169000b001a240c407460101c1156001e40c2c21080010700100959244002008000420041440045d0043c080409181200e68075092508040110901c2c5060040d4020390840f890080124030680c0c80c60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 587490071 1250 587488821 587488823
    0x30b011115090c220c0908030a020601180204050307030b0601270f0b091804051f020c0c0a05130b010c020405040b072c06210702030703020f0d0806040906090818041404 74
    0x4120a24506001c24045e040740341c2003003551420003035550b40d03000200d042d60441240a80160861801001005203071510001c40b403520000031403900345040c1c0081d43d250003c1c80010094120345001482d0340e07009868141085900c14001c07030607400c000b0385503001c0580602640c4250303140001d001c610300c085001a190010000b81c0300032512903550040803401d0030001c5c41142c1500c03a0150310100c669003841c01c0c40c03c2c80700c845d0b000740e11340703180b0110242003400e4448864002c0d504418100401ea403004e181c2c0d482a6544000000c079104901d0048035800b80343c640c041d4001d0300b08002c1c0002c0104030904188254403a5851a41a0380043c14404616070a0316104144003002c81084007589840c0d030040104804c4070450384074188820142c034160705030403140310002d03802c0441e00038141601070115105551220b400741924240b915000b400070310011b03146030b001d541c2d112540003c02c12075900400301c1f41d410414031501e4164a03400034401c2065800680c2c0128103203403c40c1070b50004220128051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 587491321 1250 587490071 587490109
    0xc08011116060b040b060f090108010b03090703080318121c090b0c1b010606030b0a08010203041707110d080306011205060a1a0d05070807140a0e01030b011115090c 72
    0x70030016110340c4040c0902140ca180d21036030701d0300b0149440c0e441070000c01e80c1d4100d0110140d22148038000141400e40143d103c11b071001c0e01042044030041003c02d0b400705495106c1c0241d82ca0384c0703d201641d080800005410b49461045610005051240c14040c1136042c2c0b04145009550082e0100c40d020340344c00d40c4000b040c0f035040c0710102e00c41304d41c0c0b0000351620703801140700084100c110381d84143c2501e0055015501080d594110b003429428440d6040000c0d0006000952031814036540d903100212609000c14440350000c44d10380100710810b00c903d0404900141121046811400c1a28140e4425513025000c6100d042800c10705200f03e00400303100d0391000b030500c9011841e09143c0003c00b4207101c1c402591041c104035075402c00d10240300b103e020f10081c1d50f071040700e45002c803000760003030803800d2145501802c140007001e566a0b01c240c056001c0c00e0b082c6000b0409841203401a0b0304185482d2002c081d500500d0100710240e5429541640f14101c0b0100702c0e07508908030000e116040006002e504d040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 587492571 1250 587491321 587491357
    0x60f06010e2b080f030403092106150302062212111c050316020f010302390d031e02030115050f0702090406090c15020a060f060806040c080111 63
    0xd00120154103085045004000001da101c03035a496003d1039014600e102074000b404418030091560003049400507040e4a02504201110a8081112008004001405251600b0030144010241740b03d940085501914450302e42240c421480304120030080c0810303019462a900003200410f5410004025801411083c4100800310900c03000808521505402c80b041203803900016034100300611150003140c1400050103401d01c10491401d594030700c0541003500501100b401b0001501d08160a0300d42592101e003080d51a0b414007846403000740003e0528003880094280607601a000318a84440d003a012003802c1115100174000c90000b80642d084020107600034803042e5000e1801001940a840d03912401d0402076400507034168001c60b4100e0700f00f42c84240b00e80421203c64a041c01070601c02c0e201d0503031624820710080da01c1c0007038517024001a4407090b655004181580c040b01c081c000038003d07249035280a00b00744109022511862400703600e4150750603981400001500d010903040008185 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 587493821 1250 587492571 587492599
    0x609070f0e100b070f050d170a0f0b030d031e0207110d080409022a0c100509130603050d020f071809020f03060f010f0503060906070c14030705060f06010e 68
    0x1404200500500301103408842c00304496440c1409041c0c402d1160390184018030507450300a0500101d1a00a030500c2110b040d4110780f5820030300c451b94008036244d00000c1e01c2030390000070f03000703089041031300f6400d8002d04d007013008200d6164200d40d004000b2200980e28011960300c070401248541d010281c00203c030800c9148090dd4107000040030107000c2c0b0034082c2815240c00c012400c0341d201151122403908000c0381c200c200c100781c28510107500d030040054194000664007181c504e100d601a65420000000740072203141e0f403034900300c6030600a4400b04200d0b0545904e042e40d039a034043c110200252190312161010004000380b010300b0f451180c40c4003281c10361402020720180040f0501240d00002e80702d44c0741e616803401c1009620503400c583e85196554540946104800300c10740086000350002020403a960200185860b00205d5600c1d2401100c04181001c406c0e220380600040c005002c00101c2100740300c4001401c5028601c690340c2c0c00300d561070700b100645400b140f100703041d0f4202c0304c0d43c00c802e9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 587495071 1250 587493821 587493839
    0x6062a06150f060509120d020a061508240c030421050706020a0806120109020a120c12050606040b102c030a050304090b0103020901090b07060f09140609070f 69
    0x31101d041800c0c1c00303020316510340000070382d00103080c1c00440c006840490024036514018440a05000d8000701030f00200c022018020b49420004c800a03103080d499a4a004010448950110050000e04199a9510080c1c2c085520700800d0031240703910f1589280116440300d0741042168059a03110b007800082c0d1094100340b5035005d00c0048500c0a1010600040010414a00082120308426039440314985000c004010703901d0045c200841103685444426401600c0782d481480980c0c44000f11040c05003068a040080084d40350005000052054004000c0140000e000c0c2e020b241c007242c1c10702900160b1002e00c02a00c0d200d201784000100503200da00ea404290000c0d12000020550400309144c40c0d64011a250513024401120154400542041148440c0c030890103809403d1074150300d86401c201c0000d08402290140345441000043c0b13000030451640c0c00441c1c1c0511500341441219480e0400e022061070035a4403070601d0080c407000410741c590100700c041c10340310310352817000895081200384 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 587496321 1250 587495071 587495081
    0x1802040807240f17041202060a020c0d050726041a07030c060b30060c04080c21060432100e1912020d03060609060f02010b120106062a06 60
    0xb0805114100b4071418036010354010307041c8200d008001c0381a2406c0d0300500246410f9004141c001890700c103000c40c0c22040400b041c002781c45121490401e4441c101800e14030264801414065400d000d00c26028100c034034110082c0040300e0740c4909101c6104000001391900b07215070000100004e4018204800160040d4401082c8007000742591404500881140034003602c580d41107260410300960308040c0c0c60701000200e9100c800022103e00b03040c60150403503942d41e950480c0d6842503a600303c2464864049021000500d041c11080361200e04040c10841d001d000c00c505200321442e29041c41e100ea000c1c405201c80030540c1150010005004000c45034401040041c0d02018203000350050115080394000d0b40c2c01e0218020f812071034008000101c0030740f030002c03250203220a0604001041051a41110000040300c11741d040440ca64140c29034203c0c014000207580c0c0d640010488040c0018800550001090780c0e01500c58260704010f00d40700c458408180e14600441c0484200700c0c000198064201c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 587497571 1250 587496321 587496347
    0x80405041109121e151602100c18050306040b071409040e10181101080403140d150605042403090b150312090303070b070504180204080724 61
    0x2d040480000c001003aa1205260705a11944242c0780c01003111030200300d0070101c1080c00020700c02404481010b01c01358500800c0c24207403000e001100400c1d10700a004030708001c403030310a0400400d120200d01501c030300c81003104402e20200c0a1303070200e642d007800900580107a401c80003600460703a40a000301d40300510034000750802c40d0207100034010380e1518043c0200f043c4002014010001d2844c0b416001c66507500d020703d0500c0140014180030801011a00036030040a01e40200f09949509040c0c2c0d489410b0b0310f00300541c840000302e040c072001075a444440415901c0040035041641ca0300115002e0150b802812002d440e031342d090420721495048401c019181030b0a01180c0c2c41c40d26210803449490854a0315103805500c240042c00f46404d101030540c034070001c00030b20f0800c01e03c2404242d90b8068000c000f41214035400110755194081d005a0b001007511070000c01c0d124001c4001ca03c043d4125210710b210750311500c1004100c0007280365001c6002c40e9046034140141c0c110103421941d410220708 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 587498821 1250 587497571 587497601
    0x1812031815140c1c050c070e0a11091c030e09010b0a0801141c14031314060322050c0907030f050c0f07020108040f021c03110d02061501090512060603060703020708040504 75
    0x860746c20001018082e10000740244003540072186004c00e0180d090301c3d6503051507138000c60100483c85003962485212103405082851a94601810745420788041280d0700910368080b204400000f0000505402000b0301c1c40c2907a21048188da0b121000c0400030301d40c00f60f0642c4501d26041507104038140000c1003e105008420650040b924180560304503848030180d4880d005014005104801017443c070504840f0065a85078a146001a10803800340c40709511040d2140d10043c40b4418008104044869508010003980d80f90404802c050010401004219041400d0000140d0020823040c01c0e6030510441c20516840c100c040d5004461070319006008903110070b0000034040168498484100d440c903448912000c0b0003125080182900080185611a583c4a40a50156298082059504012440c0709900255000c0d4010384204c4503580115070007840306d040110b242140007401d240030341c6c803c0d02607070349585480340220b05038410030b54060f0083c50300700010000c5041036030050001c07142c552 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 587500071 1250 587498821 587498827
    0x1903090524032d010807090f021b0607030c0e030604030f12060306020d05060d0f112403070906050f0403030f0c080706060905071812031815140c1c05 66
    0x11480101500140c030031000c03c08180e10019100c01840c81c00203007584603601d80801c00c2d0724000e502659000c0900a03500259220340400906003c2074056880041d09a00d01c4600e0848600d43c1c641c1d41c04040341c80c13200003810044154509801217890f952240703800b801511060740c1d01e44040d02e85400d040c4181c41044400300102e195940548070b160050f41c07040d500540d4940703103000d01d003055443c0a800b0500c40c0c400010b2403000504d82816641010351300c05d80c58420307001c21500041026903120540c25200000025012190302032000451013592281c440321000c0d40c4420044a140c0605079007001c64940c1084144013185c02101c1c00d1172400f40d05e00c1e22411403d401d035958070302500484c030101d0703045446110500c18802c4c14061544d11480703514020b11002007101840b007059000d0310407108400d20058125040c18401c8034120324002141d004c0348012682c518822a90150640b1900b001031084840d49500071001001c462529200c500280200040342c40000d01e40e0903002c1120701842010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 587501321 1250 587500071 587500129
    0x20609030a060b040516200f06070c0302101a0f06040f030c0905070201090506042a122604051302070c0815010501083c070e0a0f050916171819030905 66
    0x4009070761242b0b00c507541e01d03180405140390292804030b034000701150007400d00304041d81c0009070094001c940c043c2203803050b81e110074520200b60140310790b4000000d1940c030b100c00401030003486600a8222081c0c400700b04540d907601c403000c0707003201d515940092668100c3d402060104030902110700c100c5000100c17001032040070403454040c1001d070750701820301c04803074005510038404225442c07643d1041270000010380003490348810301d09100700c1c0602c1c0d00c161a0950034461101c80e84d03042d01d50055010315010000e07600c8244640c2d84400301c0b4414004940d01070004243e9503c1403e0304c501907218480e101c3d22400503030804e10f4a00d04004207910040c00e01002c800d511425036004140551515107800e6840d000d51010b00c009030131617400018040b080d0980070440798446900107940003440c00500c8000c040c2d04c10007151f1880a00b0080c800740346200041c001e12501920b2649141d1080b84111072400e044044080142c0c0901e05014010600f5050100180c1c14080354a41c500703509600c8015a0940d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 587502571 1250 587501321 587501323
    0x1212060f030609060b011112070c080607110613020603010902071a040b0604180f0b06121203070f08060f100309060504110108060312030112020609030a060b040516200f 74
    0x9076402569415102d02400050098038420442080300038a88130703005a41d004030036681e03502c001043c288031880004808090040204402014241d01c00a0b01d4031420510001444400703188030803040303405060081781e028500b410103181c0c00365002d024142180e2800003008025080300f00b003592507507019020441349141401c290392045200301800c0407241400420f000845000002c00c802c01003254044002161402650950b140e900c20381054243da919808070300c03241140800341b082445040954034062f80190091481401d01e5500e80811741030f20001141c03045010740301c40785c000c0566008401c0ca402c1018841c1540086410042019201d0350f4840b4100ea00480b029181800d01c0c80c410010356900000030307030b00074504800510000740c1d981040d01c2c4a12040c422200000e2410082904640b10300040e1024604000c00707482469141d0306181000d4028030380c20fa4429490940044d21b404114082e4070b4801116607669040208882041c0c150010030240700c2d8598452103050040e0810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 587503821 1250 587502571 587502599
    0x1151b05100911010203040303050906030402010c0b070c060b090103150c18030c0807080105070219030c0204052401050c03070f080f13090f090b06091306020a0e1903121206 76
    0x200e072040c0000c600c601c90621800030400a8080c50440d00200010004660300006460700300c14102d401c2d40da03d03220341c40142c610002031140201030019180c10409001d4002c1d410078050740c02540284a84541c540070404441400d0200428a0341d0881c4441001141644a03111000362420007074203609102c3c00039503040c4d81940c4202ca0450b01c44600f0300c6100fa040c8841d20090015600a009909003e68040c0d00c0742205604048281e0621050740281441a82031891440d0041c2c02044a428030280c3c0801d012068181944070b1105440000c410394070610890780c11220f910b0155003000340315580c80303031900302c0c070002a50030100500550069441240007440c0142401c08450380c6940b420308542d054404140311120710515000d5840041610000c03102da0040d0212160b0803182c2c1c1d110000c07010841315400c0070b021035101180c442c90068010001070074102c412a001017081025220200c4080e403036000040100304441001f00710b06006141c0b20b81e652205d5007010501135180c030350084801c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 587505071 1250 587503821 587503843
    0x10608012d0603031707020a02040f050708070801081f0917071e0b0406020d09060c09180e0c011b1a06040609090b0c0c0102090301111e0301151b05 65
    0x820112800103400d0640e039624666180481024042c080c590388001e070600260b0481c000240300d440700002c143c1e600c00c0c8129070b03030a54000c0041003c900c80d050041c0003060100c40280105030020081280540a100e546040310b00d103100400010450300642c128002d24001d90301d510584800d220300020341d00745100540c484582c2c0700e03e5282c01c803e0600c00c40c0c070801603001c03642101003071540c400800c2145188952260b00700c0005039580034000303000c0d4004c14404d100a41100c0c5060740ca142c02903488a05101240d010000c1c240301408110300100480f0242d403401c9890764031210382070303405502440c1d0804d41a41039584007548018251100704403c4004101150b94031000c10402196161500c41c02000d010019400c009008440c0d03213040e83c1c100068126001600042842c140c540340035011240f61503c0034000f44610410030913005d0701c50b005880025886880f584600120290400559040b20918841500d2640e820003084d0707070022100b6912998600e6030003a0030007080041008807100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 587506321 1250 587505071 587505101
    0x8040c091b180305031c1107050703030f120e0f0c10050315010e0a080d02011b0c0201030908130b030a050a022503031d030307020d0513060e032b020f0d0909020c01060801 75
    0x440c8000d03101200701c8150903050b0309101f40902100b4080741d4009400c00a80751705083c80420030b40f00700c00c00d031280c200758000d080c609030909000e0180640302007801300c4803206082c00c0f961071601120401c03841c62019010310340059800c1c0000f400203076032030820510811040c180910609002030101704d16002542201800fa445940340e00c1c081c5a0911402d11000e05225000c1c014142c0194003c000481c0d08101070704060710350303045009110418048601185903070b0010700070940e40c2c04100c81c5540040b1400f0150780e2904000072000c403403a008551441300c094882c0c00890a043d1081164080400b40940403d60345002c080e80c01120319200b80034096860006545030b10b030614000b890580d60906110810200744200c0f40221040ea4001013528080d0402c0014a080725005c00d150520140d048880c0028410100b218a50140c01c3d44452103040d6090399850000000b005558613082d020380710000d2103d8508108410302580901101c0421a00125509a03036501031820341d02503440c001c004d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 587507571 1250 587506321 587506357
    0x903040e07050403020a0b130902160623040b04060b06070b150d03020309041116030e0a08060c09040e0109060615090e060a050d030c08040608040c091b18030503 71
    0x18945024461907004415140c41072805040d03501040700b02c4124131842d40d0070388000c00c80200701e1a00c078000070040c00c1990411500c9042c22140c50b403180b0300021090f43c00500d402d094416000011502c03035801e490075810000d00343c440c0d41d102c4000d1a0001c2056420b2551000100700503600c6a00405a55014059140035420140c9540004c003e043c8451413140c1c01d21800400040d4020064070601c0350200e900113681e03040552980214030420311800c1d4040400382d40a410960045065410306c90203840054110b41c484840a80d07410f01642c071981005c1c0140131111180c5000d42105101400100021486814a03500c40081d501940c01065951111591400056521000190040c42081c602d03100e9814104082050480280945805000207484600606001c1c80c0080400ca41c00340445071381d0f40da105001007009005a4044808005003000064040c2050082d00c800700c4d15400602c181101084098038803002e0204602c4003600c4101001000c1faa0520141210384000c0c6030403070b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 587508821 1250 587507571 587507579
    0x2100e010507030b0d020f010f050c0a061a0105070503040509060a0302090711010c0f0c15110d0f060f030b06010e1c1109060d03051c020d050406090506060901121b0806090304 77
    0x1135480b00004140950b84010402016903510703e00c0c41000002030030302c0b403084000c6100071202840f50b42d0329100e0394400e1030149800c103c1035503c03907042850300545900402810100460b15031051b41009803040d0310502040c000c918001c0c01e0705411503001407880f14202c1d902d50216844440c100c0320715021843d0a44040b00c581c0d428001c0c0e410404403842c1174081e06011545c007820780721a201e4041d000c107280d001c140480d4103541c3c0c0040d00303c00b594500c0c0c83d02d40c0703485d140c20800341c00b842c00585002802c2c041e001030800040304007041602d50240030011940d9807800112184da49015049600c50760a2507038640c806d4901d10340031a2980503a0b10442c0701c1548034144140b00801038481030040a1110300000820760143c261a0184000511643d075041c0b00c60184010740114510440c8040c50070080c0400c00c800383d4440c40d50b0300d00c1141078848580c4c80104000c1c10b00403d204209100c080402c0c002c0000e8600c0608408950b030440000f0700c056250301900c1c3c64890200c50500055100180c244 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 587510071 1250 587508821 587508827
    0x50403111f03020d0c0e0604030609020607052b21020702011701080106140307050604060f0509030715170709140105120a09170316050705010b10120b010c02030a030f02100e010507 79
    0x483d000165003002043e10328001b001c60309500c00c03448090300c02a980c0c9084801c40d80c942c000ca0300850303000400c1700c02d00b42a4451401a83c080c0304d080c8a5201907030703000c0055440c042c0e103900740c80b002010914506d111080e14280c0281d849404103d04101d4440980096100c035448034038081c003012000000c0c55030a040c0110010444c1e0000c441c80b0307030b101c01010003113a601d241c1210180e40842c40d200340210040300060302c83d4003c81040c1645409120004902a14600e00320a003800c0543d840003082c441c001e075200155041a558040019840a4248035071211148201401403061500c189080803e00c0304030000715055403440161910360b40d0500a1148442ea2620000caa40640780c1c59820316000d0041d10085c24481c40e01800004038441342440020340c44a000010082c1c10445140d404050050039941aa40c04092151a140e000000d5501c10001c114070154050010503c207891510103840146039144590218071500400e14800c140394050784103a501c4180c008212424094006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 587511321 1250 587510071 587510081
    0x106030c090c03060f050103200a05030f0c0a0c0305031f080c0301060501051c0504020409050d020c0103061e091505030316111008130c052d090403050403111f03020d 73
    0x81c00c20503013495000e004980c100910402200c4090030700180c400001c0004410300c52204410f131507503076800f0404004050700000150710481c981d07802300c50982e90340014040180200b84038131002450304500900040e000320300a68201c1e410940394001c051181c01d01004901c144d402020b801e07003055000c280789060034098040981381c04d0900303900b822002201981c0f1483c481d942c180041d600c46011030103646a580c842c0350501d802c8800da860700056406c01a55800a07001e00c1c9002910786100004c010080c15288200c103800f08403402402450000a040035104005640d400700d80d00100004150340c040004040465820410f0b2406000c02c0c2000b40d181050300086c41d00130ba44d84070380030403069880000d0b2640420702140e0300c9461841814a100c030001c0c1d41c0c12050b000a14003100da4904020a0941c0c01c0741c64803030b55003841c282d0b1020240710f200c02068600901141d802e000610006020070038111821401800743c503a10035410281c01c0c102c8600c1a44240802e50000d50402c84407050300030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 587512571 1250 587511321 587511341
    0xc030f1507080f07030b1503070e0a0e012d09090b07020d03200a0e3714061806040306090506060d0309090b03070e04080310080a02010f200106030c09 66
    0x4280074903d4160903120101000418420805581e00443c0945540d03032590011000340c071911040e01ca142015010700514902e00e040740c410800702c0e40007e852021303518090b050b100c50807949001d0201d02107224841a1b861840d8004401080f44013003030f110381c94800c031300503d4002da036002d100703080c004400303802d140c03010111004040c181000e0396031070300007122072010b46c96a0102d410ba81d030001070b00440d03030701d051003020503442107110902001c50407010441c10200c0c040c0e01da513240413510284e0390410400480c4140c19400120007142005454280c000d13100301c0303918145441c44440d02ca0005003656100e50801c41c0d50030340d28001c080c1804070410600d80e200100741ca44a00d541015140a41090304900caa6000f458450001c4100707900c0078400e1600910f005100d4150ba42010714244601e900120b0390820312008101e80017800da980024090941070b010784070b007001c50140300d00450700d044101c4103000400071070300e4001c640c0560900c01c000c005c50040355030010b194240901501900c501c041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 587513821 1250 587512571 587512577
    0x160506071806020615040213081b01020a0510110705010e031209060f0f1b03100303110d050d02180603040302070302011d0303030a051810090213110702010c03020c030f1507 76
    0x1c07060010640003e080368100180785000d800180f1000009000f0b031140070a40c0d664216080400140b43c1d0000815100300d40e10700120000c050040030049a5a0401005c0517000d036204080414146005501c00580903070f41941362854901d10340c0b0350909490440c1416a030641c4000303004514055109800b6420401003409070109050038509041000c4014011041031605400820840414041c10b601c00300c001c0300d43c0d691607203400061307004040385921058000c12410002c80c250510042141c3e0700c00384254482c681040e61140d88180250419402088aa01200118074950b030340c0c2c1007d035106034400d5009020342802d610004000400c04042000001d000a40f00d5034166008001c5e0b1740d12039403000b0001400c4ea24800d15841d9464040d41c411620701401c1292212040c1581000103035030f0003540c1054000b03011000160854061004018071180d050013040015881902c039070580c00e020740304585203e000b0f1070009080c0b03110450200090f87c07040c242c040c50a103a00d0000703640404542 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 587515071 1250 587513821 587513867
    0x80a09030f120221040b1806041202010609021b07080613200901031406130309030b0709050a09020408070510050306190e0420030f1002070816050607 66
    0x99405070040306000c010000780242c00c060100c04000c1039066a0100b081409010741d007803030781002c8808000068400b40c4c1c09020300c40028034659802c11441e010b10105034000c0405075100c0d11000c1c00365144911140c115500e42d0b00c006080440782c00904262054210340c0c4401071400741b1081d02e132401c0b0f0750050350981c0020302041b80342c05040244c030040a800c46140310142d18058462034110746507004195200c1400c03000401840030f9801015070403003240e01100c0031600d61841d003d40e0950340142c014001111200c1c2407000031108400140c0003041c070b04160700d84039203035000641c521105403c00c1c80c880f0b40c0400c08200941c1304000b000001d2400303075203d50402d040c05c44020300c01d200c0106040d0048084030300b420003600b0080d1000000741100b14061002d400c1600d42803845501000c0c943d0b807400c4010710740034400d20707000c04c41044450181d40103203154100007072481c021b504800d105860754902400207032200d003681c4a12105442c031a8015014601c0c040c0c402a0940c01c01c0280c2500e1a4094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 587516321 1250 587515071 587515073
    0x30a09110d050705130f1409150105060a0302090f040f0c0f091511030904050a0f0b0409020d060b01140703080f0c0c060103030e030f0f010e01050c0c030405061c14010f06020d0806040e12030f07080a09 88
    0x1040b02d37800c055601e0096038500d000d0b40440d500120354500141c0241c601040f91000e01c4096221b40c01082c481d0faa0340c0e82c482c40740c07402100c01c2c00e400d0165018601e900e030441c0d00410f029542d01c84503428003e080c0ca00f41031050000034201c0d0300032114941803688400c92405202c075180316114494a003241c0800040c8015008252051120b5000401044d92100300c0182c0c1da0241d80306d048a12039032100d03243e548503e8500141024800c0c0c400506c024805804280d0702a41c0c101a1010602c1d0380f80240440d03840d549044070b40011101203950580501a61014043ca09003c104220300c00fa000118101c0110b04a045c21103800800c000e10310a01404031900800c00841143d08582c000c0328400c0c0c030781508400c0c020206948100c800451458005542d6880e104454058100d0740d060181c454100d070f41e8401a6200d5441140300e100090940000510515295101ca940080020111002c6568881e41c00c40b455006580080341a0409002c0250159003d10602d038814a003400900441c105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 587517571 1250 587516321 587516329
    0xf060109062102070309031e0b070306030201120b04150605030906060102030403081e270f01030b030706110f060c0d200f180303030a09110d050705130f1409150105 72
    0x101403540c003001900014500185445440035002542e0048c4032000c1001016801401d03464241c05c08071081c000813000918840c2c001c0c402c20080341e4060b140d890540a4490420b001041041700882d80503685801540e00030411601c62000b5007a1a182c060356814412039051800d02d000341800d04540c002c01042c0700250013801541c0058603210703500d00070079800844d1007525000b24601c0c040362100d80715000c07105000c5044070b424280800e44600310600242001142610801d20b0180c0d0180c0c8070507810400c0901c500c041c400201150001c0d50741035000f1a129600300701080c0d4850400d5407020810700181425889880c142c001c83c94903401560600008403234003405074091204101d80b004c24201070024a11804201e95070300101501e90303914194280400030b00360440183c4224194041001c01ca040810f02c04081071340180080500304d00d0001080901140000030000103a2200440e5414102c1d40c0107461203040840100360083c6420031441d46000400003042e140042108010050354503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 587518821 1250 587517571 587517617
    0x602040b0a231b010609020d0606110622030203090603130c0b0403050604080906070c1503150e0c2a15070507030e10050702120106031704081504060f050f06010906 72
    0x340d50b00790b0f4030360101c2c000d0f00140100265400f541c10349000182d010f034030080950107030b020345101c2e8440d1b1840c00c0108003601e603078120480303d612480c122440c1b05485e0780c0440850040f118460702c100d074500310b680ea000c00e040c0d03041643c0c00c180300300c3c013007510404002c102e44640015125220406041a20710703100e0b1035a505000d44041c202000004218801d516900115030010b508104801d6406546411015842448010383c0d400603140080c4075038180c1c4078100040031918406001c04a40d20f5008040702681d201c01060032003581000040c0360156000122400101401006081e1355180e1b015180c5911200070305072403c03c101008a107000035004185c45400020942d08032512824210050b0f07407620800c1d101a510150110000003026015000b000c1070301d100f03040c181c44107401ca000781c06941c003590150780c03401d40002071101100b84c0300b41525907000d40940d50101c0c0d4103842020b41030480d40280d4113a04482c0c03010381085902c0d600819003800405051800041000103045134038164070b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 587520071 1250 587518821 587518837
    0x15121b0a0e130e06041b080102040b0f0c010204050a090902031b13050c130305030d0e07060801030809010e060c060601030e0601061d0d050f030c0c09060a060305040f0602040b0a23 79
    0xd64280000b51400069000c02c0c501104070086070990300305801c1c500c400090034641c8800c817120b4000003140044041c0283d500300c0f410000d0050034901400100d401681003901c40801ca598280300000f015a254a0800018031860300f0010700f800b0240149814a40035480280341020081d10b246110b40b035900002c030700864144170005440d02e134000c1d1104240b207102c1d107800c1c04800e03a45000c810f002c0044010801e006101c3d608000b4103903260030880e1142d0f00d52042001207800c050040020a0800b401024040380c140350400000030305c0ea0000f4415002030b5200342ca15800b003010002236503090700c00c401c0c03a1a42c44004041d1b03903140540c000c3c889800c0411032140d08041061a0080740c813442e20f003420b019400000c4d100c0d00b2074500ea10039a25081030301504440e00c01d07820070105d5410110740d95030040313a028200940c0c1500708441076000d0000604102c03a20081c810f40480403503000c0c400740c0041c0884d4414560f42d0340c07400710300600c18840c900310419150030398006c011010b03800400b111f000c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 587521321 1250 587520071 587520079
    0x1b01050906070f021002070f050909210418020a03050618060d030e030708160f1d1e07230c0307170d05090a1208060904060b15121b0a0e 60
    0x10b40a0391404034000342d603c0720300079040b004403000c2c0703040240c001c2204802e803403401f10400101c0740c1e2442040170b800820baa0410461301b10b680e6041006610800180201c190708100d1440c10350b4420140c4100024404100d40e465408542c41425580c18050103820000c1124066080904c0035000f002c0c420000d000b030ba1003120708200d60001c25000d1b81400401c488001c040c3d8140980e0792152a480e85a040340402a28030000000b1130240c000f0840314050b141e10400325240d87d0f070408040030f0600e002070300300c1c0e4071000c40c81c000e000c584880c000280d108141d02e65401c1030b036003081d000c0c031510000300a41c0c09070460000d12110300b00c03000000503110b002e60040021512814862100080c9208201680503d54106410040070450028915040900c110120061a0031560003103c5210099503e160710a0b11b650125001c902a50401c42a0500013031030803a8000c1c03400341c00300d115071000b103115202e407860404101c0c06954070450101b0b11151a41c4992510b60140c0b0b00034a458641c00001e072007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 587522571 1250 587521321 587521327
    0x10c0e060c0c18010302120a080304121710050a080f120a032301080d051206130f0c02210703020d0804240b03060108122b09030c051b01050906 63
    0x108410400078610701a101802e60000c580c200d03003041281c3d440c24002a1300449408020354030001000488190854000b002c440c19500c03140d41c1c107145240c1c00c2070204c040000102e04c0c005000051600140616220f40c4240706040c6410107003c003020f000d034400364140d048820259844000440c50620885808040d00d507545c0da02d00064004110316040340d45084440601c5440001d15840006c0c10b0340d02c0c1070115001d44034001d03c21141c6105002c540303000210f003079010403100c0c10814440c0ea030318074484d800424038001c0d41080508481e03c4064400059010311340c0700301c24882070b6840c0c50990000b2540e082c038013802900c019640c2c1242404404c10801c841c1d00080c18844c0d50320000514041070b1059058501420342804050011401014803034028100001072994001956140c031000ba0907540303041c078100722a4000e1010410302e0303203068260303003038041042d9005a105e10782055100f5100d0452540e400e083c4949007600c001c011040c20401c2c100000c01507030300304054034035a0300200c824031b0b0307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 587523821 1250 587522571 587522587
    0x151101020f0408060915040c03020f030c03061303110304210507120f1a15040207050a12090305071e05130e0d050d150b0712021f020d0e010c0e06 64
    0x802449502115003aa400108021402040c040f440c140104038100495070031503044401e004403807006490013001341e00155800c20060031b06070041300c200040101520791034103640c0d001c6420b04000322282e121208a43c08075a040542101456118a82d003000940c1072070f082c12914864501358801d03411a05006140040c100042004500c0103420310348102030b40d1a150b032403c4640707041d0840c4216119940300d0446a1200c41019246104d4484c1d01d0004505601110030321000307520281701518a4010100700c0000f080511140301c441005a42c0c811300410301c1c0d82419401d021130b6030403101203040c0c10703000800c4024a452100040d241d044030840004c0f083c801c4801c009010081e45200030703008210b0b0001c0c42940240c040c0c016482c1841c02481650400c4007620b010040d0780c0034424485c8018807241002c900c261642c0200f803001801190003c10110180c461110364090442c07902d1600010054a11031450052581e688860740081c454045035003c0546075580c07030034045004500c0826094 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 587525071 1250 587523821 587523823
    0x6060315150a0509010f020d0807031a060f040e060102030a0e060d020403140703031805061b0c06040915050a08060a0509031603030b091e1501021513050c010203041511 74
    0x2040800d40e490010b41d81d0182e010081e0440d00b0080b8040d0104821514981ca85800821808450201c41d03840080668500800b030700281581107011154500b4810340d0402c41d00c40c20001c1c242060300c2005140c60386e20704641070304103800c01010241150000d010305940d03a600b00381180500002102c0081d00c036241c8188202c0240aa50700c090094207413000404500c2002149150582e402941c1e24000115520710707100c80c00d0002d115168008001b0840710784c041100429074110903e0072825104201800c00000d846030300f041e0800285140e403001c041c110a0b0344a250b0301c000708819a091444203150030b02d26510707200c0c01000d000815865900083c507100701841100c660340505508092881c0c2c46060040043c06000c20703050007421280c0c0407803100c0b4a4482c0c0480c1d40b0408100d42c66031130b600c0e858001044441d103200141544107004100800145a1502c24819104c413400a90302040d00d042003840e000306900305a055400801003441005020a4040b05901c110b0a01920300003010b40c007030b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 587526321 1250 587525071 587525089
    0x6050702100c081b042105011104030305120a0c080402040f06090e0f060a0506032a03030708070501051302031c0c1424070e0d0f0c090c090801020306060315 69
    0x7140d50340c0b03401e0b218800d0a80228041d802108030601e10075844d458584031890610590140701d40701c10f000c034a4040301c48051480000c0c024441c4002103650380940900040c0c1d6005600100c010803004900401e800004415040c0d0140710300500b841038642191020300000340250020b40900c3e2a0000380d403052240f5045580100400d032800c015040d0032603d01912402a1050b4000d50b00483e000b103501c000f81402500d0113000020088c1007a11150138030051015002c1d20100002d443c242d04108a40d42c041c4094185240070340d09160350f58000340303082421110014954014540044030724800360b00c00250003055006581c41c1c5400c1341c0c0a100042d00c01c4650503200400480c240003699105007404101c058030000c080700c0c100180c0c081d0304080c0c80c414900311066000207021440d58102403810500907103c01e40281046400c1d03200648458000344040c1d048411181d4543c8141401507901115010040c42d51400860440c145030000441ca88000f5140050007522618070031016500c002c2e071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 587527571 1250 587526321 587526343
    0xd030c02012d032a081003050d0816081314071802090901051c0b040311010e252103020c101206120f060e1c050301030507050604030b0406050702 64
    0x1996007248141030b40c4070000c54601c0c21000010382050104054080e0030414a6510350351071108192a91a00d4012207800c4d10040154504110444000000c244184611a80c0110b143c3d42c0d1611442c01a0200c9105007883c92404108981507003044103560a03070031512101c0350b000e4003450004d4294050b0300c3c5015419040f040324030700081c45442c016405030b0700400381a2410358004030303242c4c0d03190200008440c80174000700081a181901e24006402488400c2d030052290400d50500345c1540c48460842c0c2400b02e140545900802140010301038201500514040220b0750341c950300c1c24004810304d00c0200342c90844000300e81e24004800c00d40207220402d0070200c041c141e01002d0b20002001003a08030f044020806051800001184440e518628040400e03082000300d041004d117580d800b001451640600c4c2e0890140210a0f0780349416480002d807800d480790713604e43d101c2d4114141981441c402d9402580305a004200410004401c0e00d02c0662140d085640014555110102a4141f0080202d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 587528821 1250 587527571 587527607
    0x5090f040f0e010515030105090622120c050f0303060a180b0415031e1a0402030c0a0810060801020c0a1e0b0a09060f0b0a150e0d0501200403020d030c0201 68
    0x2880b0b040395841548190310801003a4111400040b41109146c22981c0a43c1c0c2800d0703d800a0380007526061f91084040240301400c7c50076201c07028039031500041442004200000a2070380c01c424000d01c48200500101c0d00c01d40000365185062640000e0200c2080c0d111345004201315100340d00b9404859405070626040192060010000e01084a00c4103038141c0011510410000881c0303e0900b4000000b84030f442e40403101c450810015a5540c49400300100104d0340352044011448a944490544000802d41080140f40701c1600500d0b2105686035a0031440341c03a80f041c08543d185290000b44110b034950028000700b0104004804802c44e100300c07400107411600c288040c8000d501d441d501a000d61030091004011141c1d10585000503540c050441030f600800312601805507203042c0507108603281d501d080004c5c0729010480800d00a00c400c00d02900c86035500e00401040000e00c1501e0300d4280500d400e00b070f180c036043d40e0004801c21000301014040050307000e810f101f103900a200300380c81e68000d22 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 587530071 1250 587528821 587528831
    0xe150601120f021914030903120c091206090f0a0f0201081f1427062b08090a0501090b07060203100302040e1b4207050d02060c03010605090f040f 64
    0xc07403080d030f804100e244804d0008002c0a0306841178940d0000303407400354920001842c40e0407403480401032101c00c0540211003604017000300c80740d2640c6801c03250303038101000d001428140c5050a129801c3c0002203140b40c2030791700711008600008900c8a0000b0026609080442840d140e0014a140b041e03c0e1200300e881008181c6004034044041072004039118000305e40c0c02c0d103140b01040041180205541210170b0486960f8041045480d0183c00442d008408000107007000041c0030707021400705420385099880140c0041c00d03a42904007441200054142030a001c14924500513030352126102e1002c010f440a41d01001013405030300d0384040000191740080081c000c091000002d29101d4401ca41059820558010809803e0400003801c81c0c40e0880520544101d00d0301c041c10b0300c40b040b0039141010150004143c00340941c214000a4500140210000c0461a0a140d40030385808806071000114080c140010402c89510030101c070701e0000f080c0c4180e150785c802400801d0181c0095516090391900745 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 587531321 1250 587530071 587530087
    0x604151508090706050f1b0c04091b0603020f0a0302090301060b0705060703060e0907050402030408040b040f0905070c1119080607050c060c090901061407020402030403030c030e150601120f02 84
    0xa06801200c00b04261203100e03990b64030035202c500c543c0311300c07030040302040c0b01c0c1810500007885540c1035144850140c861040c0e1850008003116030500303007207442c411105a203c15141c2c3c48825a005003210342802c61070411501224035171402103c590404042e000a00c060040d2000e41000c40102020710590751202164505103441300422650702000a1810300f000404100e020745c1c107402000050301074502207041000b400060360000700142c0b1400030402001461501d80401000140044200704000c0c4e4100892101902d101400d00e030200542a00c501c4041105454010700e40c1c2070407107090980210144865044040540c00003030f00740205001c101c0010323000001880080e4240d07080d669a07980e0080548554090203500e43d400c278410f0740042c0403650240040682205180f902c0c10705007080c07039000030182da008071401c80020740c844ac0c1c1c10710142d0705401242c01e50b9400e0006130806078250384821180003002000c06040040705591000403c07415408410b000050f00070541d568101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 587532571 1250 587531321 587531327
    0x2090f04060204050a150f140f0a181e0603051e071e030e010c02340f0609051e0f060d020f0409060302011106010602060105010f050f0d0f05060a050906041515 70
    0x6c190a02d00101e180c041d4010710b00c03441541100042c0c0b074880b121508003c1042c1d00850326801114008090103015040e480c01002d07594030180042207245000f0800c3e00c060a0049005080356000f030080c14141028415941c4000807851909121401050310596070503604498600815291a21305071050980030600d42d030541050f07906407103800c0280460210810101d81e240c10410803900e1030364407a1000c2d2100031012012401c0000c0040c45109515103444111103085903681c8081c0c0440c400d8181000b15043c009202e4406e00001c11300301c08400228030100e84541c19400e80350344213040000390713070341260306a6040e41c01c1148100741c00707038480307882d060604000c12090100ba404205001e51610349000c000410340d069507169030140005900c1c000044d50103044130820002401010300c100c903107004010010340b0a03003003001408103115440c19410300c125200903115502840100b401808562281e044140e0045019500001c0743e141e03282c0d0251020f4000e40100f503920507a4500c552250354 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 587533821 1250 587532571 587532599
    0x40c05090115140a140c011a1215190608300711060417030310050604050d0209130b09150604060302010c11040906020c210702090f04060204050a 64
    0x24152515000c90340c0390140703101c1c90303000c1c2c20001000402c107840c40c01c1c40180312030183c030000800b818808840880e4100c450550740101c10560442d81d92030341150402900305000040d40142664034050140d18207403003944402d5101c0051b0416002c2e000800c0071001081d805e40000300074240b040005a488908103038a0352580c00d40100c5a071240400300641984608110440010210013280383c40c90365651305520192480802d0740c4094203220000b5180c04078a0440708039200318018507664038100b44841143c0001e6048240940828401881903803500d008840001d41c040f03844500d507070f07a4509210000140848014415041c1e50148940003500040000c1d50908207850201300e270356280280401c54825100290003d1008904d480109030f124aa41d101c40c40d000c0e10206e43d840c002e07280d8805036030141d40d031f840140d4418800c041e4009800542003c0314071040c0307a640d14001054000034140300d009003038030303240031a054085000c00c1070701d904a500402014211300c400030307134605a240ca810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 587535071 1250 587533821 587533829
    0x90806010b03070504150203070b0c1908041718040c030209180907090906150320040509031e070c030602070201030609180314040e10240c0807020414040c 68
    0x1124a200110700038a0748410b80388144416075880382440d10700400340b04541c070702d1001c2e00e003540810054400403c0d04d1402e568403a400d800101503031889090300e0350802498500c0244200000c80d8240030014070f0b071380c078400d000342446460310752140400240600c0d084401e08900741d0003841e00245141080e0560041c0107075100c103c070030308509618004a0601d1400480711104035400041d0140f0460b03509610801449005c0c52002540380c200180000904980d5001034803600c1d40c010380c0608400d910b26182482c424103903000d0046080c003c1c4020b50724002d968000c5180f20501c4035140b005840d1b03006580c0c07000d41218240d50304641e1390800320020342c08608140e0029007403d002140d0310010340100200340b803030000101e6080170681c408484944010641c4400c103002000700041c0e1580601a140c09109a44e16040c000d92604d0000341701c9003507042001d08071240c0c0080c0a01c0c039a820a45005007140c2200419584078014800500141060014042c661100c0c1041c4400d100610400d2401d035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 587536321 1250 587535071 587535073
    0x7080a0b1605070b041112060105041b0516050f07030828051c021b011b0801050312030903040905070f020115080c010c020f0411130609050604170f06070908 69
    0x548400541040c1c02514401440c0480c004105aa000401c0807201d40d80c010b00512040c445620602c0004044690114a44140c1d601004c014041d42c80c1a20503000711542c4107005044001510348090054001c004294601204296104041c004184140f600b240032100c191606141c5a140500d103030b07004140c4820224916114a8503492070b2482d1340440d00c3c0e107603241c003401c1090840d0040780340b6020392403100010344c003030090f07454a005401021102e080440000b0030000e580380d04c2030700c034608044d50f000200300c026801003140d030701c01061101e640c3d24a10301d499581c2e55407001c503d107180b040b640709641c02e07440e00013080b031030a601c00b80303408007100c1d142c2c028418801100d03022850100580104403d981180d043c01d04258040c804410340e02d80701030f01d123624074903000c0000b604076094000190480c1000055131b0341d0308020b2a040c40c01524080c04c1280d152820140403462034055405100002d80405160400c0d01100300000808405103034125034451600b088000c1c4011042d20a42c0c0780c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 587537571 1250 587536321 587536343
    0x30106030605270901090203070b1e0708040b180a0e011d040302060703020c10060b121003231c0e15040b0706020a050c060a090b0702060603060c0d060807080a 70
    0x70350b10f841c1031060b580d40d0605420300e010201201014209100260001d0003640d0388668450045c0c6040c0f00c8940280441001561203002011291840a80700e0066480c030300010402ca400060700300c401e03901a1104d0017000307529985040404000c14001400e0703961702481203030740000d011110052890681e000407060380004151141286400394003501c0050150b042034002441091003075003d4400b103845141114103030981f010102048034a59008075810301030006400781030040f9445100d0b0410302d1410000069032440c1c07200c00300b14001019030820b4043c0300703480e503600745820400022012181010366418249458001d80351440b14406c15006c0c0715107154940450b285031003607070115184912850314100769680d42000030f40c0700125810a0120070b00c0301e0344400300d00308080c510800b030700c000001e0360783c03c2410300d280c10b508001c114604550101041140a48021500700d402856104a494444440c0c5460700081c02050b0422001445406d800080d0040300103000e1884600403017007001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 587538821 1250 587537571 587537579
    0xb041101090b07050703170d060e0f0601050403050c0d0305040509070f18080604121710080c060405030316060209030f010f0e0c030a03140405061809160e0618090c0301060306 77
    0x82c42e8021544040c0190704903603000c0003c208600125285035030f4100030149003018601e141c030200c030450b80060344048041010000c90308403090314a5040714003420002d051a15680c0da00740d6030071b1081c11840c05040c4140e04281003600403010341c0cac0130306802030009010345403209d0300900c0007409000c6d6000040c4d10541042035280014541c07000d845440003d08910f42d5951a5400303500050702c109400c015031112910306603054100b01d54017a02e000007108a003d031504003c1c9160021440c0c00e507110700020802040076a40000071180000c2080428050f89941400d101000380174400c5010703014050001c16400c800019803100c5087c0c0200c10701041a80426080240e0358148074074080d4255104c4030f03007072011a0052410881c80c40b215040d451034540c407180440c0c111381005050809a06196070744590341d290900d4000d61000c0114010840039450300030003043c000786c03403004c18081e8400041000320040c43e003500204038200601349a106042c59141c980c882d500911403140040e140180100d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 587540071 1250 587538821 587538839
    0x9022b05010f060e0f0a0e0129040e19020c070512070b0a0804060f3b06010b09040207080f0403020310020306060f03070c050d05031009020906070f020d0b04110109 72
    0x15060310902c1c0c1d04510301504001c2c05607201004511484d070b000c078045402090691350b0b003001c90090070340c00041c010503500d00f20340081e5000c0071400d0501c806074070001444150aa4030255411900002c100c502562900011401400c40c106030002d8994000100341f044100d002400c00c040301c0003560100100c510b1b1040b81615101580201001e85204201c0c01950034400c6024a8015020715400100e051801031720740116070386000c0307100d070764070200030b0b880300e2051482400381c101c1c1200341e6a008480130140d1f1031a1038400c14042c5d40100400811000d9047d1660360560314107581c0808601c0d9207600c4040e0803110b541051008074400c2c4100b007902c4400011900075a40100d40280c00c0303a09103041c14041405030340004002c00c0410035030718613007404100b042024103603908071911001d0f070302d0802600d051403190f010f4101d20072450040000070865240e000071901c103035401ca020320600d4001c6100062180c04140809040f9034152014041841584140346801c00c0c000d80712841240d83e142145 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 587541321 1250 587540071 587540081
    0x50c1b0105070f140f07150c140102040603052e030213020f03090304080c06040609030b0c0702040f09060e07030b060402031f060e2713021f0804020306011202101809022b 75
    0x44e0810a0547c0400d80400303008140b07010480d8410140d040030050000403160880e00300c0e520600000b510781e0180595902148040310044001c00001144401041c0a43e07140e0400751000070300800c0501450740c04401f240c0c0c15248002d260024040c1c0d80c1c2001c801c410b84c2c90300180150f5005004480c1400c1c070a2514008403411200c0302d440722903041d46952204855040002e103a8005c8840401c158401030740c40e446905103020707039050006000502d9041c400c0445060b20000c4009071311801040c8003003500160840d038031100813500943e980e503a444611b003000390950010112540c1110f030104803644c10600d99000100150b0300d0741c88000940186000d00c6405c080041c0525032954081002c1d11410742050002d5400900038030303018072803d00c20703200b03055103c0c241000003602e0100f0b03c0110700c4c062095038014010160903e5554106800269012401ca1307110010700512140310b220705002c414050f001000980340841d00c0f11080c01d0708046800c905c00000812030610300091401010354426 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 587542571 1250 587541321 587541329
    0x70b1503011415010c06020d200313081605010c0809010509010507081306060510055a0f07030206100b0f0c01060509090c10050c1b0105070f140f07 65
    0x407986900c0303020320460b50383c094480d500e0400103421078440224560340001d054032182d803c00050001400700906c10148511150300581e08010001e1100c04003030f41080c0060650031600c416910b002e8111107500c01d200a01000348a03509024680b20a0340d00000443c0c400c6a51100902440e07036040b00041c00c0b038100710f83c2c2c02e002c2102000407400711801c0d60035400c0f40c207120f10070014000b81c881001450b0515465041000508006134014074440ca00000c4042210070448510541002803000070722510a84035011040ca1a50380f85800e81d035001e0781074603042d500d68a0fa1330f91000442c0340407070b0355400214281c0c054442c107408210000c3c42000440200c4041138041410a41c044002c2c802036070143c0c1c0350305002c0d9224640401c1d40d6030f0301c107440c0340900c100500805102c030110080c80414130400e0403060501c0802d211205031050301045048490021580c0303a00c0404000300140c6241c000c005002d025111224050305c10840100c0016020104000071206207100c8071014540e54030716805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 587543821 1250 587542571 587542601
    0x1090507030b06030a150614011106060108040c170102031509041a18030c10060803030c0313020a0306050a0c02010515030709050709120503031905011d07110102070b150301 76
    0x103000c0020400002200e60450002403c0d103c01035180d4039030f01c500950140214076040d0380c1d098100301e03a0000c507112812840b07007820b0901c8048042c00c42c03d40c4860000741070505210010340000c04005c6004c02e2803014209091107002010320004406000307400c11212074000901c0f0303c440700401d2405a910034840e681c0f0a00d0300c2c2640d4000001000c1040c80601281214000c03c20780a07800d5005102408041d5100c2c0002e00904a500c0580010303103d02d0750107070105170020000c0c420030b10081c800b202e9000310b04611041c405d10b00c0384003055000d150f80c0d101901a901e8074003444842c1e0307a41e4110b201080010350081c0040d484400d1007600080803041116490340c0301c904100410030050700120f5220010f402c0100301c0300d5884105030f40e40e12510008564641000041203103240c80112800740705a04c1031001c0100c0d6050a0075055030000c0742c44246211410702000410241c45004450501c0c038285009646a444515054000d11800ea03001e001440c60030040c10941d040520800225140480e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 587545071 1250 587543821 587543833
    0xa0605071b200303040801110903063619080d050601020607022d0706050408100b0d0204020724060302040e0d0516030903061505031e280c06080414010905 68
    0x100c450802c0c1e98510308840d0507000500001980031020311500c984031800003642c80ea21142d107801c041c1440340c020403110a54a29009018001003000c980d22070191400480c040c01c491039810807444e00e17885058040354544045400750070810810054060004000b81c20320094652000581c1c41d002c1c02c8414000503800020241c040c01d00c800201030100a40c0c050754811815070f2400d05041c08125082100454400a020003420004100d06952000381107410840103060384001035880c22551b8000c1c0c40703513130081084420301c102c0b0200542c0d1f0b04011981c1c1da0703082d510031507620003515440c80145c2c40b9a1500f10fa104407890003140544c5100381076a1250700e4030340c0100c0c0304a42c540980200f40d04004095001100140c003500c01d40282c1d0740e41d481c820078400d1922003050b141c5840d408008004e460164074076145441c000600303800d4103040402050300c404281c050140043c1a41d840a029030096138000110b55400c90080d81c0502c1c0600304030300380a40c6410750b9500344c4000c0080100994402c2c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 587546321 1250 587545071 587545103
    0x1509060f1125050913021903020607200d060c11030306090604021b1005040c080a0302100e030d020712030b0d0c050105030a0216030e190e0a0c0e030a0605071b 70
    0x1e92181d08a00aa8280b8554050380341d80114011210484404c000da46640040d1010b42c03174211040c80f1104500003003c08a9800c65011030224080d84000a011502c0d546404100314000c2d06220000040544200c0d020112803c000b17026020035103a0002080051100421400000c41100d20441000d400d418040e100d2506020007588042c000c541e120403a001008075558003440700074403112046401083c141001d00385652485060f500440040c1d105e170240d40300294010852007075892030f82400040c580c1448048a06501c01c01044603c0b440c030004e0008100f0001005c141d01011455504200000b03003041804003c500079000680204510b00c020869588a00c0c000c2d6401104010098281014213620b17506128200c1012004210301c403020522604041c003141c010b03082c3c5a001c1c0044586030a1035888510009008051040e481d28070814419005624403800c0d40303406000c4400d514000d0520400805e8241d40303850000740358451030b554052591100030f0680c3d8100700503058030908 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 587547571 1250 587546321 587546353
    0x50c0f0616020111030112240f0b010c02011d041104030606030c0f060c0803130f0501020c010b06030c07020f15030702030a090609140f13020a020c03061602251509060f11 75
    0x90500071214022380c0c9590a8814956074142500c041806a0205030055040c20400c1990b0341c096060b4100030320075000347e02503a40300e5008607482410f00d54001e0b01c1c840010110b00a401100300e5000e60a1000030000100415684010112401104105c0c80c50b80c80d00000044041a803159100042d129500480452041d6004682042801c00a0744405800e95501104140300c1c1600b0f41e0140d5010030141d5101c8001e01442c0300c41e680403198a480d52030b01c00840303a01b500038148068094080c140503082a51520300c603454010703c00b08001c4d5101c2c40c20031002540da600480c0034000040da41000010303901c0c011b001c281c0960715006400b0003403c0992040c4600e10407401c8140390710180104000e0454146440101300c9090541d001d800b0301410314040c14505100500119416603882e107220b0002503001c102100e801c4c07009014100442d4180a00ca80303811001e07041141c54055050140c4203141c0c10080da08201e44c2a6120104070500c12002520640300c80341c0810900d401c000c01004100503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 587548821 1250 587547571 587547599
    0x41a030d1103130909060c021f020f12040b01051e0d06020f0d06060f090e090a060903021501060c02120607140a02010f09060b0405010806040c0303080601050c0f06160201110301 78
    0x280203045a00301440e9545042c0007821075130000d5281c581c0d41001d40d00b4044140241d0610010a0004056404c145042142d103141c3c0080c8658050f81c0c040742041c2c0382c6000c603007110900f001da03a01101150500f41000040b1801c00e00c24144102d0204c0080f100a03903240c21000b48203c0024031144000c4502c0c8c548001a602107140219543e504109418201c0d07210300c10342029140350740d58005504103401d40608407902c3c82d0031821984080300104020008005132424040340d111304003064507400c61809a01d050a001080086500c001d4000300d0825031066820400b1070003256a00c84038400c48881c80c1d01d465081e11414002142c0c0d0b111040d1404040e801003208000500c000a5001071090305c00342140c0050b0b204485e00394590344461060318150060038050300702000640600c0c18280d50300e4241a40c80d11006041c411542c0006005038011402d4030b10300030180c0103a504900701e40314041c0d100d400c21034000054144d064445002144148140c3c104800981c3c1c002c2d04d107909140711004518 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 587550071 1250 587548821 587548847
    0xc0609120d2c0106080f0a051f0204030206030c0a080109050403080a0b061c0501090c020c01050a120b040507021c0e0f0f0d060c02060907140f04230106050702041a030d 74
    0xa20000750400100e51000003610b08090b4000900c480c200400c0b10300704035004400caa43d9500c4441070a02003600843d00181c130041c1c7c036a80c00da00021240c40e20010b8040e0b9813000e5804400803041182417011200101142242940d404085a8a607180b9100701c4109860240000d503082c40010f040d103080e0382c80442490401800c80741440100308d64565800310300002002d1035521b440c01000340003658020b8448051139030010b001d0010300b41e00000c14a00524481904004901c035100c1404a047d80c010348000714081e00902480c0750080c4040e40e40c2040f04444808012030b900c681c3d11081c400c00c11007120080c0140b0164002d141c0344100b041c0b0901d1403028070f40c40440e111040e00052441e2003101120704150700034207801c1c41c0c4000c2880c00c0130065800070b0102d204038030700c1880b07030b9880b02010b0301070840807240000e404010580c0d440003039081d130310a20051140308002249041e0060302600c1e403d48216420b01c007801040452500c070503c60011725405600400030005100e000b0001c1032590 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 587551321 1250 587550071 587550101
    0x120210020705030105191406012a02130b10090302030601050f010512041101020717070e0705161b0f050a0e040f06230a0212010620010207080c0609120d 67
    0x1c686580000707003103c0d0180c8400b824a00c0801800c0d0030940180554031071420001c607103c1e02e42c505000042c00402e6005072140000d007010b142d102c034510030402010740c9580c014040164030310f554008803000301420030106118a550300c0400c200c5906c41c100290550785d019000c0d004507440c04091140c10012110864180b0805000001c85680c13803514584c407480c09400000140c2c0b107820700290509010703800c55074020f51603100d00411400d0000d041d00c00c98020841440b81c541d1158401c58450003200481000017161300000400e0050601c0c1015026030000c140020051303440120010700b807070520a054000e94003040c200312103102e03081800e41c007501600502c0007481299442a0480760b1a035601c0340c681c00040e0030b0618664000d400d041d400440380710704500e481007201c010344a03400705204071420084003843d0401c85d07224095131884042c85140003903403111400d141c507214079005095a8010b500c03441001503101d4000040040706403510140711450701c1002100b01e8003410f03c6241d10005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 587552571 1250 587551321 587551333
    0x50f0d1707020d050307064703030c0d0201050a0b03120a0306030b0a0f050709120209040201202104050d03030e0c0a090507030506041a090a150b0a14030112021002 72
    0x980c64803c40451650310910185a42d22501d00e000011504144621401c40c1040c1e52403040c4044540e407600d410310480f14207400c2c0300030030400c010541038160b02400d415000110b62810704620010b0140141901c0d50024001642c0d60400c0c1c10441e09251007042c1d266100050000f60740b1204801011040d0252602264a03a240d0301c070002e403880140d5441001943da0128200c0140142c0b046503004140c1d881d10070a841e14101001300000404880684107041e0200803400b103a0042e40202c1d144c0c0c44080450400c840d0400c103154891032071481c607410392903c0f00d080c0c01c0030324126412a4180d41c0000c1943c140e0400740d80382100180b00e24103450300b40c0e00c201c0d08041d00540d81c401030b00006204015021070b041ca0100002401d0300c0000e4040d42c003030f49c18401070303010004000ca103094402c0026500c0c0d00c1c4a40d01c2d0f0740b02c1e01c043c190001c441000007100080100f0320000e00c2c0c0007402100d650b40c994000e00071402c50903e01c64030003407140030554801200030800501d0a008884a0b00101d4070440310 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 587553821 1250 587552571 587552573
    0x52b0b0a03050312011a090603131401060503070801200a020a1a06040b0307031e061805060115020706210f052a120a05061210020a09050f0d1707 64
    0x40d100015400541d203a40c80490040e100f080901001e038003510a4107486800c61040fa403441c295401900c0e2400c0c0700f0740f40800040c8011034413030079064003039810105100e612002411164000c2040c0c0c0245030080c00381c88400b003406c240c140034001712201c9140c000700c08444008142012504400c000100314000c01070100d000c00c0016000c031140440701800740d40c427400d0500400c0122015032892a0080c0c015440c01c0011074054031640780414601103003800d0800041c40e0540c01000f2841d83d904d00070712400c5c03940c814800005a40c0d8140d030b01f40c2c050005c0e05c40040d60709994a403502d00c1620000740b12450300c280016400000c4a2045451140c00301d071130700c0d00562000c165001142c07080b003040c0d080c6503200180390742003d07030311030800f40b840031285051119810004109801070a0001072030303c49021850706c2c0c40e4180080040ca0304901a80c864000d500d81d448040c0d400010410005100b201c0041100d24000a04403501d10000348504440f4420360755800984811a03c082d003241014480b200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 587555071 1250 587553821 587553829
    0x40b030114130510090b010e060d1106030c12090d022a06091f030509011802031209032d0c090f0a0519090602040503070b04030c1406041a0a080106052b0b 68
    0x1545e28458a1485560341c18000000c0440100402c00c40c4141100305d242c00114001025201002200b40c800943c0c2e5620014034252038030400c41024600901030b410054803007000b041e1449081a50344c02d490005000e002549080824901800c901407904048462145001001002c0c5484090078100c2541c6550b103074180242810300101c00802c1d110010060011020321800705078030603000c480c15144c3d0a5402082d65851040000c8800f000001a4407a586d5810070030312113080003024900034107400c0707a14154814010b03d1414000e03403041d400001c0d99450860740062149417580341900035a511031a64802030300000e0240d400c1003050218840c0c6542076402078400c1240242030160761a8513040c02d16150210a603c8002d001d0302c181700a00010355a9805241200d940e9a11072615000203030000d90184619440003009500c01c00d05d10300c81e246e0560213444418801c0c0c80c1c04c000d81e0780c0e4580603141445550300382c040994408a1060400000104422262600010014200b0207500100f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 587556321 1250 587555071 587555081
    0x804020f100c0b0f011815050603010f06090f0e040b06040b0306100e2401140405040f060305100e030d02130e01090e0d0c02030d050c240105040b030114130510 70
    0x10000036450840c070803d204400d2140d94020411050403030196240081081344680502e41c0750300311356194085070050130188064000a01002080329550b035944500050400034107200c0d02000c00c03000080083c2003080c08c0e035190304503800d80b442c0d040305c3e0303880380c0d00c0c90714100780200b6590307100e44c0c1d5501015403624100300c514440e0308d248205440e9182018960b44411000070045500b2081420b010078581108403001004000d003030030003140c00280750f00c2d01e18940c011500304907042403402e00c20318003413130681c0c000000700e074080c00546e44a00160280c50055919003080b070f00581e0710030000c80d08608003645c010281e8200c0d0003450b003101350306d0303152191031580281d012003c1e4070f03110303541215801c206204030403506020341000c1518950030340c04a602c0c2d61220410340c0070b010020400d40c2e1300d8030061284150340f1400c407200041d80b00010b1100281c519080c068180100e207032241c0c07445241014440c4403003080c1c0310802c8801e15503d001101a800b24150380c21a428080d4207507040d521185d0b4058 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 587557571 1250 587556321 587556349
    0xf170406050105042a1809050c0307030f0b0a03150906020f07020a08070e070c061103090a1115070b04050f121806030402370807030c240804020f 64
    0x308040d494841040241c40b040f01185c0101070400300311403104a40f05180c45450300040c109072070036021101c94001003800383c2d88a03c1c0c8990600c5c080014501c1140c005620400058a0801c808034002e400102103500500c68190031080c0302d001800171075909501904060441c04021039040f800342c0da610142e80142220007044071003c0348860461810300d0000d0085c0c1003450080c0707e200d1504150b814030a0001d0050f030184062a00c560090040c0c1d6000000071005070501182d8034140b0114090f6035101071401640c241c10b0000210209203804140420702034181541d03039042c81c1040e141c0c40712003d800340c4112924401e038000348820400a1000140841e04c501600351140442d03664541e0320045034040500c143d804204200041e030b40c40d00300d0700000303446811016280b03241e45446030301800d0500380310711020b185000015200c1000100c0c0b03410b0320301c5040c012900c0e540d114203107d4040c05c0e808090b00b4400500001c2d08181c0c2c460301038680e10a00040003e081880c0740004504040c11541c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 587558821 1250 587557571 587557583
    0x712050c09270709110906030f040501060909030509040509161e26010b06030402090a1814010c030f021305010f12050c0307021b0a05010f050f0409051006050a020304060f1704 77
    0x16081100c10a1442604089490140421b18180f1028000751052000510081e08542100c2c00301c1e09000d0300b5400b07070000d045001d004102c1081c950030054100c0e0858a806403080d8203180005440c2c2038046004490b1503003a46840960320306000c0b22020410202c202c00d80c08010410b80055040e80740c1c400f803d0340b0960110403a003135100c000c4ca058295480c01e000b0b50f0040004105100040c1c85403208198400c07021180003807166500300d203001e24400c0124000d080100d821b282003103015019031240000c072603e51020451071104081000603401f0702c10403860380d070391940302c200295405111404001c00d042d10300b0080070081da01c010001c48001762840c585014020040211058040084102c644100050107410303040b40c4000a0b4002c0c054002c440c108244000312841d000d00880540354400051800320303440c0c90710303800c039400200000c031f03800034a01d10700e4140095113a002e0301c100d984181072507003e140390501b040001d0f58402e1000d4114420071080c885202c408a0032001c500d80502d110721 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 587560071 1250 587558821 587558833
    0x10c050a08040b04081c0e010c020f090c0c010b01180302060c0f19060507020606150a090803070b040308060904080409110903010c09150311070b06150307030507020712050c0927 78
    0x5d9005854801540c202d400301c51410545540340070b4108a0744001440d0900e00072004e50418070110760200c46584225800020440c1402040c0502d000a840030306525400bc01160326031000442d0000340d0381c4803403401002000d02c240054100107000300411000102141c41c001e0f03407a40028544805004101441402d8541000030030a880c092950041080d2004003580e0404800081c03866082221844034040c000540400040c001e840c01c400502580003070342c5d290401401c0c1850800c4088804800051403800000c40780e15100034224000e940140d450b074101030030003007001c000b0b144806a0f00444078052101942c2603070240500e881c80b40c3d4568920800928043e60344d640c4e00140000c3e10145801c288140500f880043d040d600d209400c20a04803082e100c40c00400d000c18003402200515840000030003030341a815810840c010825903088500c82951080744000c40082d03038100500341e8000c029941041d107090342c42160000103403c290040c16a042c0301c010070001c2d100c83d191a254101c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 587561321 1250 587560071 587560079
    0xc01020915190e0f010c030207080a1b0b070b07050d110a030c080a06080c1e040203010e070905030102211005061b0c060c1f0603080f1209011406010c050a08040b04 72
    0x1441c4030307940d01049040440c0680003c200050401d0f010700009810052039000150615100b0840c40004240c00420b460400b10b96082036820141c2e41c00382c000394204a0040091a9a80b29048030b0020740c100005580782d4440c00350488450340311030220040c050701c81011300381c5602140024281e501c4c45843c006060003c2c0100940503100082180308411301e85581040058008940c0082c046811152a00d1070780000c1c001c0d20f00751085e0300b1038079040b0348048000b254503c0c960800d03174021200758070f03605680c6603182c00301800e0b03102c0e001042082c2259510700740c4011a00c101d0003034100c001d184010103055261404200d40b90019600b200790410076035a40c0c2191501405200ca41d80000d0302e00500c6d141d0b40981040e9202204889a0b180600d0b195242d0700c222042d81c07040000d503520904962783c9250342c00f40030541da0468a0940c40f050f00c07401c046444000c0502c600700f201e541101c99401180e490000550700a105a80c00392824000e40050b400061014001000684144000f00303845a080c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 587562571 1250 587561321 587561347
    0x31302060c0f1e060f010509070f03020c0709020406021902010504090b030a050f0c010e0a030c0b0a090f0608010302150c0a11040f3e0409020d0908030a0b01080604090312020c01020915 81
    0x3611204085c81d1450052003a6120700c0409940184a803c0c1411810940d54045009210300c0765610900d00506c03101082c4660700d5001001181c1282e803c946440f0054425480e0000d40f20500902255041104200512454101d0540c0010080c107841e403058141e1601030400d039800544440c0c5422280540c3c0c141c1da007100104030508000e0710916043c034195a624406003489008203800c0c0240440c800d9580d5115118101c00b4001d03804078800f1030342c1e481303501800480d000c0c0012131050382d48071200321400c2d183d481500d405043c0c527801001829076a450350240041e8045d007481d0001d4032a00d005541303051900403011641c001800403090122080351712003500040b45540c28240100003a854400e15500701a039060300c2181c01c0c0182c1d2089103080340d40003032a03000f40090220b0703c00700800040700c0203a406215140300c280c880600704d80da210100b000702e81e420f0304014040f80300504801c101409075406000c04d92411000145002140c00000300190301e24229050820703000180031401c500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 587563821 1250 587562571 587562583
    0x40902030a05010915141e0604060f020d0309150c02010b150d0605030a05060714072307141c111815040b18061f05070215031302060c0f1e 61
    0x5075045805c0c412414290955281c0342c80a0b102c900c00d00018501d411080c0e2058044c0f0a200c0c0010704480d41d813030b913820000c0c00c01c0c01d0000021015008500b80020194028018090500d92140c0c2400440e04000c10410040c42d903142020215980d900f0f46a000e51190405481d1300307400040741949580150301c0707007800c3d5145500075a010b40c1000f10309800023030000032103582110301828000c882480e42c030060840b601500303002501e04141181d04611002a518449640781613a40c1510340301504d030341a1010031541810185c1e0008980d600030b400ca020382c51403042a25100e90a68100c4401100003d00046031514105d846074092030140304080c1c04001c0c111400c0b0000313075000c0c801620007a00080344a1190b0440f01003c41101c000900607aa6101103101641142c6950b809020061880100960002c00080380540c0521643c1c018032040304003540c1c4030f04450010742d014001c25509000307694010840c0700345584200b600190413180103010420041120f4010200403001d1070300c07441d14142c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 587565071 1250 587563821 587563841
    0x71202120a0f1509050303040f1e0507090b0105070c090507080a2003180f1609060308030a020715060b03060f040c170c041a0d14090a0f0602040902030a050109 70
    0x2501c844412400a400c0920b070406154008140360b10701d03500500140064420358030018a039000000030401000094612601500d02601050301e5004900c1c868580c0e80411000107030055204d50810400c003c1c958010008042c010704d40281405401d80e5224940100e035004104655165010415000d60040c0c01c17076800951428103000082440f02404244c4440c0d00c1007011032040000018402e00702001d0a0060a2164048803210628240503984230002da101080451140034030000b00351009026a1090700d805c0040a480c5449241845e0029400f1050407110142c102184105081c43c40c45410020150904002d83e03a242040400455001d05c011440c4160301c2d1081c5c4404140d8400c08000800c0c4020741d80022684071103100380c0c442d020769409108030554203484100d00da0621805804450038600040c44079508140081b02640b0044178616141e51008000f0000b04107580c600c0c15001d4010b0b0342c0145401d4540e40800c0507a40704440c010b400c01d4403940108020700c40361041c24254 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 587566321 1250 587565071 587565073
    0xc08040b150a0b030414160605030615030406060e0c0702013e060f0c0f030609070e0a03140607110d0f1709011b0f12020903010204150809070f0f17010e07120212 71
    0xb2071f00359480c800c4400c002d018010030000c0120020f80551500162039a458030017001d240c5c0c0b40e260501e0501d025104900815000c0180c00b4003181c1a40c0e480d005481c03120368140c441c004075020407a402d010b58503c2c202c11024510f07102c00c0200c0507125408001038503032801c0001d1b00542c40c15039942241601d000e401e4000c480c0d01004054040c2602900f600e4200703604640d003008030b44400d00215103255403030390800c1e4003143b0f2400c008100020031003082d07802902001a40c0142c0d4031014292460384080102201d1500074105c1000103a2040c3d018145004207414603003500007480c0e510000d11030048441c150706070754030028074520501640541300040981e02d090481d61104020041c01940c2c044541052260045056000740d80c080d011b8030b01034550240340c0c10444403801002040500c1c04e580080840c00345600106d840d038400341c11801a2007410203a0f903443c910304121040c00a60302450080c00f550f8070400380d0011030b420320410000f0f040c1c01e5a0404150f0320f9004006043d20341c80001005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 587567571 1250 587566321 587566333
    0x60e0d03050f0c0307030c0e062d04080604030f0224010305100e071814100e0f04021e040f050106091d060d0f03050f2a010c08040b150a0b030414 64
    0x1500004004076075028034541b8001c02c03c007406030700540b01c44100328490360388900e01081d482d81d80c0c101030304111003c0f1441c160284414030082020b8042d40b04078000c2c40190781201d800540481d0080c00c19004c601c00d244119101e00041c80c050680c050301f94031f40300c200160584010400e0100400c208402081d541004100c254800c0d001913944c0c482c10300c140b0400c2030703050a0160b8049103c0d844192540b011500c01c2c5900e2074a2804680020700c0f90140d0840c1c0b694000220740010002100948219805810704450001e11840e80030041c0102032526403282e1a84010720000c1c00d1401614000d240e40c1e00da0150b8581414000400c007400c51100c90b40d812122004c000b010360b074080c1480312481c1c00c24007201c5101c0d00c7d42022503291007180941c518819001442005142d070f0700345544003510304200062908619020618241c8122a60010000e9017400201c0c01086003080c042c3e400901641084280d0001400850907205040c0d0288450703400c08000c101c103110300321082d815041ca60801801d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 587568821 1250 587567571 587567581
    0x61112010e07170a0b12190206131203030e010c0302071e0c0314030919080309191805041406010303050720120c030c060f09040216060e0d03050f 64
    0x11004105104840e95011072074007154660b80541000305100d0500c2c1e0300380d0003d1808250410140209a2629006084802446d40701e40d50103e02c7c001c441106020858000c0002d4007084220340281c4100e640071401014005481716260030102030b071910a407000304556404030003140c2101c003541d505205250042109100017480f2942d41c0c000c1c0510701e05422061401814004c0340e41e0a25040104140e405040365210444004060400740350222690090070b0b850701510084018588100010395206225074102407904200c0c200141c103414920b03999550f500c0b80c108203a0a150031400940903696801d00040c070181c0407200500c03003103480090555501d10f550042c5244030b00100a8140c0720a58114a40c41800c64042004004014400d4480351084d082407030303c420108a4680c400e100d5a501c1107001d083c001c05a80040008020103401d1148403818000a03501c80d58a800410502d020030340c00045031845016605940d810080c003a065400c40040d0403203101610b001043c00d04001040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 587570071 1250 587568821 587568847
    0x150804030e040e0717010b090103140c03030f0415140a090603051503060714091e1f050901140c0d03051605072f030d03020c0d082406070605130611 65
    0x184c1110110100281c009040480b124010001248070030f9021003584c2c000420b00c22000e04010f101c070460019180341c05101e004069a0784075004800308027031380910040040c00c140200c031242c6400d290510380c4e1050044c8140905551141e06d116000c1003d2040501880394107102d0254001141c25101e020302c1e00c0e800000b652090014019020810040c2d140c00c8042a4903094030000e2801814140c091651540055415141c403680c0500071750f0103200710a4030f081100c0440d02c0c4106140c890030f240c002c442c4011282c041c5a216115846007080001504205081080340c518601c3c5550001305402e08411810300440c20341d0710501004003c2c03011a001c140021160904886550910030031381c8000d042444481d9450304909030b1500450184044442d01500100242c4400d01c0a0764002d160020050b15210010b9031801e031000e452480c607254240c060a0030b14010340c1c0090110303040c0f450a40e41c00c402c0d00d030201da00708504c00251030003004209060140d01164082d0200250614848410705 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 587571321 1250 587570071 587570083
    0x4051312091502160905040f121d01021507050a170901020a140703050406030923150108070303090e0a061a04080c0901290c010207080c07050105040501020a0b0709150804030e040e 79
    0x12036a586d50364045001c110919400c2604168443c0c800c940202d07074248080d02c11b40c003041c0c0c00c09240d2000c0c900d8107415840031410005001c0c08000f56015a194814211801d8000c1c205507014480100000280c109030009011702c6248100005a40c4000c07194000b80b1050940e00d28108103030301401030200103500142130710259200c030300d400246407400b81440d004010480c002120038004040c10344140f0340001c103551138101d051007910342c1142d0380c0f030301c0381d03030f9580c0c3d05210140000c0c00841e0144005031440b134907103411044001c0c0108100f0f4845200000040c00340407244400d1074005410405804144118400790b00c088600003010b42c900713594603d15051520500e90001081c0c1d2200c030210941205450000c40038000071500d0700ba103841c2c507100c1c681c8600710300305080c8a400c0300041d40b580310f072046509540c810f038050440169566980c1c0c0011070094881c80034080103030780100707a2a14002c1e8080c543c042507501c4102c036040038180508400c40206807907000324200008050028000180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 587572571 1250 587571321 587571329
    0x110a030506011a07080304030503041b120303052d09070f150e041509020c01060b07080708130503120d0f0c02070519031e0b0f040b060405131209150216 67
    0x2480c001d10360341041c3c00458407610754000c101482c040103120500d940a40550301ca540318107074040d00541e21480e03011117004507110714a1025100040d10300024801d8000640040021005003d40078480c25864802da560008900e0546d8811041251086040042800401803038003900445403c00c40082030444a1004880c103010800313000c10a191903d91000b2140705148036400038140d20b4103501006507001c45ca04584645c00e00740c0209075001240e0071507038519842207150340740443c5651480d00030b0700185010b1424124000700041c1c540c13414130a5085e0314004d03031021a5603a203405407030b0088840b42000404103604d8075040c401520b4000800000392002101c1c1c14104243c8200142405003240c0c0004048101703000000712400744001e180b0895a10905081c980c5903154101d442c4454000c4030301821b07600c600c1021a0040c103282e4003403030700407200d400e1070812954551034404901440800c2e0b103000500215003001036080c100d401041d0f0140501c040c0140803822500c0c0020b450007801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 587573821 1250 587572571 587572589
    0x3111318061e0506090c092701080d05161415010902070c1202010f140405030703210804030c061a030102070f0b09032106040204030507060201061a040846110a03050601 74
    0x1e58040c0f664230407181106100c500007414014124421388000b03c11420b01c20240a44034446070229030700c2c050001e4135109443c82041c41c807005581c2e11a140340c1d90070b000780312065010f4100911505d58542c0100c03406001160000f5035a014a441c051080711030381d0f4007020490480100220050fa4000003040868440d80790080882c03450124880941c4601e03481140c1c548a2007100200b00180e400228920b00b030004c4101003c0811240c0a856a80c0202c0d001000111116650700003c4c0c4a41c0c00802c550402d10880d41c1725486560200b07003240c2c0005000d031214034002000c2401c00068555141e4402c2c48040910708100314616036000140003d220004565000300005080e504c450f41500d0040d508203007194019661288064000c00980c02842140c02c840800040c84071000070454003150540c0c0c004149800150307902c400084050b18080b2101220003a082c03136491a0141803480406003e1f20700424081b452802600486441c4561070040c81003000410109101089160464100760 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 587575071 1250 587573821 587573827
    0xc0c0b070905040c0c020a0e0106080c070501020d05010308120907081f0b060f031e04020a0b09010e06031e010e041e0c08030a03050a1503111318061e0506090c 70
    0xc0041d14400ca1640140b41c12038035000b45488290391081c0c82d10311043c026140711031000c0d220070098030148404d000701404106d0441c04030308112140802003080500910006007041c000e0b00d07518082e0390081c2c2c81030b1561b81011070b0361004d0340c00da2125150059590070080550624103420540c482c1180d03441e18105070ac0300c044c078103000b03c2e440c2c100b0805c050005000550350034950560008540060700d056084208113103584c4428a03a40b80060300580c0c005202c548050702d0442c0c80b800c00c2e8030402d4141e04000c0d03809140035064803000701540c02852034101d250522081c1003141040118160300c110034034400c407828440841e850b014480d450300c00010130072100300e0b8a41001100718074240d0004096100005030703009829456804207001d402d06520600c840c216a0141c80710340301c030600001d45804c0d400c42c1810a946829048114402c01e102c90106188603c1d0800064003940e81d0401d0320710680303542ea050351103555141014650320000f082004542800d10104000500040a4840c40a400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 587576321 1250 587575071 587575081
    0x402090d0210030222060c140c0d110102160f050909071a0304020f0904051f060302042f030f0403030506060c0a030314072a1b14130c0c0b 61
    0x8451201041500540421845030000c40000d0096200e104030f030504506881040c2841700c01500c0d000708540c103951f00d910031a0f20316102c8008940080b02200b5007072046448070700d103030b0702c54078090418980100d841c01e96440c2980f0019041490110302514500a111018843c4000b0050729800303540007550803aa09940341d501440c50140b01e9040310f0308000d0420740090345000d5000044d0310481c400e0b10700c1101c0300c0f800414450103410940b4010800e030020a21200c2c1d604c883d07841c40c1c0300004207010205605940e40c011030b0440300c03070880311400030440500302d202d071201c00c0c2480903101005c0703040b182c0b841c500701504e003000d2400500010105511080826075656035001070301e17510011102520746110746403070040c008240403130106950704032040018002c2801181c070380800803010407103002c2c500301e45c0c1d407800c1c8541c403040340449460300082825209038154445240150231820040301d0485003110420803051030606083c070700345041c5517024400e990700ca000300551940c000001c118075250 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 587577571 1250 587576321 587576329
    0x80c010908030103080c0d0908252c06060702180403180b07020f040c0207050d0816080a090503070302010e1e03011503060e0123040303091b080c03010515040209 71
    0x1208041d011800102c000300a00c414036004109168101c0c04403070051b52880780070b0b2045841d9104c0c106080c1c00000d0380340c2102a40c02900480000108e2082ca002d40d20b40005d03e41400d44000440c040418000c4903170301031a007002c039254011008503049410507819a00289007001174465480c1088009001701d001c243c0110001112010101602c0c104692240340425441c0c109003016803258071908003407003450900d0311509402e0b02495000e002d240e41840140204210507040440740c4481c10072440000c40140e0004c81c0800c2d104d0007407070b0b0f41d400b80c001c4024002581034100c07a03c80d170003001c01000142c0e00014182680c5c076041e80e400d22002c0c908114503941005080e80640c00d542451007880b0100180f00001050780e20950301000300a02600c50b45e401c0700d12031401041c2c0503070011010041ca0700030205003a446442460042500c180340d545406000c0803080e028114040c0d00b52007808002c5c001c1c44081201c2801342c0c0204410318000c115034035030791180074000d4042d541c00a034000303542c2c039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 587578821 1250 587577571 587577581
    0x3090127120b07140d0b0105091201150b03060a090c020a1703074d03070c0303080a0515130209060c0d0908030703080f060d0f030804121b080c01 64
    0x1400011818180e59a1516148000d6030420704862080410001405040c001c030a020b000c410b42c907064900300020005104010250845014180001480032400396a695004404010110000842c040403600e0000400b104541c1110b0380e25001032080001a0f10b03045441c508860f5441c0f004204c0380444c00059040500810028080c02d881c40401005c1394200c50003540581e010750ba0301524000c020300700400c0e1072011014010b5203083e84210301d0310850340c400900340c21a4820540b05084440501c164510780c0010011685c0741c0b034001c400c0081c150012613aa5015a094405008601d4042c461454400d0351a0681e842005008025030803080c10f50305441e40d2140c080e007000e9030b07401c0c00503078582d450040701c007454002111000085101840482552056075041d01d400c001c507191100c044000140040581d038001e40518024400f292154440c10003250003615501603a08180c00c0850000607c1c0d1080300c28030219241480c0d54400d1a201003000607005480705807101003ca5070140509 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 587580071 1250 587578821 587578877
    0xf08160f44041e1e0b010e0c0403031403060316090608060601050a020a02191521140a0221040b040b10050f060904020d020f041d0c04030318090218090a050108030901 73
    0x908014940400171501d034031030b051318800c0700654220355074010420010701c034902008002440a21030000380500c8040616000203005050300d00b068807800040b070480c2d2903175101c52549600c0c1e5104200c80013052207002d4000a007031800301e10b80810000301a42d900b000000c020300415000000381c0340e8110114451001c0d115400701000240c0c00d40c5401032042035140030440e0307520000703141c0000054491088600ea04d40128554003203550740020709000b5040310b21000c698085240f05d04002808100c0607a00c540c2c4614000040c0b400e10b41002544414000c0480312408010001442203030340b80000683c2ca91401c640c40740d41c414550300401d010b4001c21800c8507441d8004156010242d02000c041c00554405000140386207003128110354075800c054400c1c60040000301b000f440401d100d500b5007002c15000d07903410302c8000c0d0f40300810f00c126880001c101d901c821242d13028540c1490400d51140e088180d12206000650611440b1500c074441e10080c40d040c040084031041d281a0b000d03c0d010030030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 587581321 1250 587580071 587580113
    0x30311040509160309051b01030b060301120b0c0c1002040303020c0f0603012c0405150705030709050d1b0b04180e0d030c110d0f0f08160f44041e 64
    0x4402c030490700c01001d800082031f00b400329041140900b800e08143c0103a0b030403560032002c02c40480426444003c0f100c0720150401420344000c1201180d4690104040210203c0c80100165124510f0600904240846074814801c0111540d49003499036402d0035607040d1404c1c180441362000f041c4841d4211440c1c0841c0ca41c0400304003000300018014085a003484045500070300740c03000d41c0c90032008c9500e44812116000800c0514206214608111103041e20843c4113010034004149034134000c40c0c15452660100c074207000300103000c0c071a89801c801100155040014180000d01c905001396031a408074401c40401c060381c0360080c600507803013250002c0c030814012042d285c1c0080f03620741c000d005a840114203030215091240110400d0701c18a8554480c1c45486170000c0440e006060869031070f800d42515800308551079202595803c06208904446503ea41d2442010032080c0e80e183e03007500c03020340f4500c009903512040102140040c490908104503c0c8030959001e542c51a01c0881c000800804001c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 587582571 1250 587581321 587581333
    0x603131b0515030a06060503130b070e060d0f0608030403080706020708040f150215040b1602100e070504060501080606070b10090216020909010e0d110c150703031104050916030905 79
    0x1107844640c020f500680860206101054403008240c5642c4400d440d018002a448920980410070003217415800c0b40091406003200c1581e60000b429903040381c9418242c01d9914081d40c95194218490306004242010155081510399100c20009010300c602c0601210340005404041019140031107002e806d001107502001521030009211400c1d40e040200090b20412600c0f50348801c1e01120780d446142e00003e5104565241c1d6040980c86100c1100320017544604418004812030030302941811a40860081c0361f040e182000b04800d0b03541a90209060210620a100081d1128400c07a00c0d020307003042d040007542d01ca518820300500744641c02001700c5c0e07102294840740400301c3c24000401c280202e400108507144c0100c424225007076100c009025034003402401080e50701404142c84400802d405239064030241102041e10591040c940d000d802c800003c2010816405100301014051a03140e07280c20a42000c01240260101500130309102c0c00d4003a80c259040d100c0e82000200756444025507074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 587583821 1250 587582571 587582599
    0x14010f02220f03170a020c0a06210606020c09090703021518030d0207120809040507020706120e060a02161b0f051206041217010609140603131b05 64
    0x40011900c0c4014a1100e50440c0005011900301041d01c0a03039410184080c4c1d00d8409204980c6640c1c0181200010343c0201c01241409a5441c540600108003a44a2911400c4000c0d4461804a40e04d441e07040100d2808900b4402540d0000e15801c9000d0113843c008425280c490815290990941c4002d51050340724181800140411002e0030001d20405a10101003411104150b141c0000c141d0510041e445208100821180700c00407401060051001c1440c03da07008010605442c4d003243e201001d0b910401c4200121a803104a0b103808a000c2801082a001c0100707603283c0b19040030f044019415004200340303001d02055201c1410007a4400300c48603120210325000c21b100805885030448066410318002021b0074200c82c07443d10540c10501a0440d0765a44c0e95a050382c045a404070010841001c603054420905842054080c1055840e4001d0703541c6850000010103000500a5014407014000e220030111000c4d0f09811840e44918041c0e1618060000109145059406268040840d8003114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 587585071 1250 587583821 587583847
    0xf110102120f0a0806040207031d0a030b09030c0f030c1c0311030703150503010b0105030112060212130b1b0306120f07060509030105060f0d08070204181208060a1214010f02 76
    0x22503c1d905407a80c0ea040d5072a40304010490042d241d0140100b450004107501901c1c42030310010341c0c0e14005105444140d100e403038010406404860145542d400000c5e00303004180c080104414590484e002980348c5600e00c1d01841e25560504005c114000c02c803c444c1046c103000b9006108140c4400c0c407600e89030300e4031440040140c10000c0325504072035401440480c00c0d00b01802120074048040c2c441510310391912116803c480040b07881615110f5003071240010345425100304c580101034021940c0d022500c81d003040d134011000580f900141040b02c2d800c400300c486262056940c00715084512054080da074518103410004c010501c40c19900600c0e41c041140d0390442c0140402000c240c000b00101e030303a0304080c083c0b010280000150700041c03020340c10001a020f9402050054400352020884203000e03014041c1d1034540000c112405803c0e003d00700445580010a5a44403104462140d9403502d06007015203502800c000103841c08010900380029a00e003500903005141d000740003150b07102500d580340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 587586321 1250 587585071 587585077
    0x20a08030a05040b060a0b0f0702030a061b1b0b010501050a0908010e0a0b0a0b0a03020d0303090602030c09100e10031d0304030506040b0a020a0e04050603150903031603090f110102120f 81
    0x111121144c3c90041a15400c0000300310b17066421646a99242040c4d50150340a140c0168108903403503c500d20480c0c1c00036825004400b92a0603103a841502c40c0307008800030781a03c3d0340c400200c024010b0b205112021490780c40040381103990a00b409503407041e140c08100c034460800c0c3c00000341d56081400588642d140000c0340b004080c01490b5490007621021204800d54881d840385982c403110085007070002d89450b403512002035101c2d080008090046603105002d0341c00480e00704075400000b081c01c2d061414000005001e80f40c662405845501031100058580645103968004060f59074078418201421085a601d110704000e0840342c481e41c2d240360540d0b5034581158100d90f405027840100c2d0b1110314500a40710096183c0d01c41e02030440b40302c420300004200c020030f0326502d48211040000806042e071455400350328500083c541e40e00c1e001030b85408031905030481401305807502c2800000300d42888040010668040620100d1282c5400100e107041c1340482ea80f401c0c100c0010314104800308480003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 587587571 1250 587586321 587586323
    0x1107030b1e040b09011505030c2214011a21100801090b0703060e090a1209150f02060c09010c0807020301140c070201030c050423032d1509120307020a08030a0504 71
    0xe200b00d00031100030b50036060035032084540550027000c0d090700a10f0075110585008070035000800a41503410b2006003550f1688004586260602c00140a0500c0700e182000b003e05411161614040000d00743c0d40c106880f01414600080d22240400c42c080c2c801002d113001000c0c5040240011245030408000f007100075652071b0702007440d00d60000f8500c1d404420303503440b92190002514010040e82ca40124400c1011480b10401001d100d0104020320300c8903800d01440c0781940c50032080d1040c0003002c5e18082000c1c0c000c42c100c00703060120aa0907a806136114001075480045e45482d10070745c0c40400e0240012100c860131014144003000b07071510004010f495281c1c000d0f44c0c14080700c0d403400d0f0300703403640d01c2240101500110b0100866480d4002e03030101035181d020203021280a501001900348000a0040880080b07800310303201c1503601501080641d01020122007581c0c550b0400d04201540d89a03039000d004064040440040d86850007030014031a6250081766443e0b4034030340881317120700501048030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 587588821 1250 587587571 587587573
    0x309060e0109051e0d0518011e08070f0e0d0314191806030209090a0c02070e070c05010f0b030312040606030f0b0610022808070206071a071107030b1e040b09 69
    0x106511342c0b0b02c0005112401010344d80c5855242c41160380e8041c20030a040300c0d1032030600c036403080003541c08603d01c8a40f81d20760b41250b1740c070030041c2002e400c0245600b6107507910608000e40600b0140c095034a81e400940c81c1c50341810241c3c4d40807450001c0c0500b40c0641d85020b0796500452900458554000007187c20410b47d102c1100503040d2243c0081c0c089000380b0740300c65002401d200000307100051036801800040070f83d004443c1101c0d650303da030780440001110208002010f21220700304024090040b0030260300483e0040c001802600003207552401580002030791012580086002d02c2200e9011501641c0c00c15400500c0e0314090420701c80004054920070700075949001d80c2100c01d071000c620b40700c541c404c0c010071b0303409040c8400082d1580601c1d000103540c5080c0c2049441f0060380c0b003100409582d44120582d41da502e40c4500c9010344140010001800d10540000c1c4036600c900200da404280d07544a203002c0d510381ca0f41031110302c90004800800b4410b079840014082806003d0654600c80d01c0944 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 587589928 1107 587588821 587588863
    0xe06090f09040813331205010602151e0c0c010b1f02061305105606030c03042a1401030c0f0309060e010905 48
    0x240e400321000e0f40002040120010030000000c02451000100c60581883c03150307141385104a001c0d2011084500d00c204001580984a0841280d5648030304000365a11941e000e96281c50a10380601000340d0340c40000c01940e18060031081d00408010502c481c0c2c0c590201d41182600500000b503030554a48040315031607100c064860b6011281128450041103ea407006818580050090b0004400454890001c18000250207518008030f840026480d18465202c10030b038074005040c840c0c00780d030014050940d1841c3c0300e42c2120900c441d00d00f1540c14900a441c01c01d681c00e0061016412200900c0000c1410f00c0c10b402540d4018081d0036411500610142d810502c0400c0b8442d4500ba100c4a107070a01c041c00308006003c2c11241c080c2070410a0040f403000c00750044504050b00380070107848030000e0041061a40003000e039032030054007c1c02302004070b01e07282c0d803210110036240c44408021 = true := by decide +kernel

theorem cover : BRFrame.Cov 587410071 587589928 := by
  have h0 := BRFrame.cov_init 587410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 587410071 ≤ n) (h2 : n < 587589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
