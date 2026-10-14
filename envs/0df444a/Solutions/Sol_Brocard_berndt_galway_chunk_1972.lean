-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1972
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:21:10.131833+00:00
-- url     : https://prove2.me/submissions/b31e14aa-6443-44c5-a6f2-c5e041db091d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 354496402 ≤ n < 354676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 354497652 1250 354496402 354496453
    0x8070801150906080706120b03060103150b0906150c030408070e07090e07050304110d050105180708190215190e100c020a0e0a14041a070816050a090503 67
    0x10840000d99480003400c0079140907002d64000340d00301704070410007640105044c070030500d44940d02047c038444100029003030110990054600b8004d0032601482c00340c1170311030000704050840d00d00809007810008901c0040c0b9043c890410681d001503400b00364182003095034001c3c050b010807614229210315604500341015a00d14001c00c00c10900429464500c0c0c0f46544515241d030342e40c1c0c1c00c654683e20f4984113260024521900041d642e5460320100e03c0c207005091003028190f10300c1e403000da2840b948030f14000c95503002100680098010307020101d492001c4035001c6030100e441c0f00151100c0d1001c004544244604045545142a10a4030040d004000040c0c4e28908a64800c5002c0810100f500e08070301c41c0000075400a28411f041c05907203807001c000c41c4c01950050001030001c010a5070603006000035a8180c4114000910700061686100780c13a942c040d400d0324100d44035041501c4000030b000342040070241441001700e000081203101d0f4440c14020240141150f114204040c1c812400010280 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 354498902 1250 354497652 354497681
    0x2070c153b0a080c0d03111614030307031202090303090a1517010e0412050c0d030509060901060b030a0c1707170a1b18050918011b09090b030708070801 67
    0x2440300625140c000e040e00c040703c455002130644c110512040008103840f6503821400c1c402c1d20368261240b00307003c00044100801d08894460414209104420b00c440e403800d48900c81e5000300f10640020303034020340c28840c0c0005020007684038856040040d0541c05800f41c1c031900500c0f81c50f00020301c50000342e41c641c51030b40b480e100c00713091000c0a80c1e840c07402a401d004858082da1504085000255505060204010b844c9440c5040c44a20420317942064601000c000009880c0c03802d124402000b0310000b500014110003c0042e00d2502c66140c080380002000010a56030328035040c040c80b401390840200100b2409114016031404180103026034081800f4140030f00c49900015018040d58450510304186102c0100c4017407a90080890b411003103000ca903015680200c10020369615641980d5020702132605180f00c0503d101440a42120001c6542c0c0c10148441c0d41ca1010b601c1e0030020180a481d03100401003498004403003c01d1403d41c03c0d901c110f01c1803003000310008800506500407003170303049081c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 354500152 1250 354498902 354499007
    0x906051005031510090e0a200904092a08060103020d02060d0902040203241909090c08060412020607051201030b04021804030504170708300a020a0b0a02070c15 70
    0x35081c1c541100e0808079141c0e081040525130741c1d0702c0034021009d02108640140081a0990103507200f0410401510113040a21144114910303920710792240100a000c0c8100100b0b8103604d0340d0000303841410003105c064064200080c0a004009203034109222841d00030b0070a640d642000c016004103da028403d90500e10300640d4038034850b1508580720b0150b162907001c4040841e00f0611080c0040609803021079821907034100014803030b081440308610541c0240341072200c14220342e002a0401070000c2c06201009410000b0040308400b10f80d10a0549401c8200c1c0c1b220780e80c41d4030100c1c3c261117112004090056410041108042c0e2000027001600d410381280b1941d10f007001c8107140d07110246c0c042e43c1c00075004112050070f0180c0712000242c1c54010041420311551282e482102258040b2181c0030058012400900030f00c0300c90031125030800c40e049030451501507242c131508403502c514040c144603001c4061140980d03d00c164030649584d40c04484000c0c0c0400c188281a090395074811501072662800d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 354501402 1250 354500152 354500161
    0x60d09260a0e012106080601050a1e06030209130906060302150a051207020a0206040b0a1403060d0f3806010c0506040b100f0e100906051005031510090e 67
    0x44100340c81c900441c0c0d40b62405441c0000c0015582000410003c640410441c9480c11825405029803002005424040d20241d410b020501007251045c2c1c01c242c90b00c00362000460501c09a003101c6030b003211140c0c075005894030404400124810f0b641c44540d8041410310102c801400846d603c0482141d10840741c0c00065030031000703004258090381d0b0290000c030b23109010008050043c1080c156025030306105885030042d05600051454002d504181d040340004142d0701c032500e411055035111741d0f80210a0301d04524240001841c0c03520301744001003601c5c0c0000750890421070007400a41e0950781c0c180c040000c07210170050300e03903090a910401d80403031890f18000c500f582d4000c6400003000c3e6000800b034000d03940d40d619580740e8541c003d46a03122445240758000b41000d1840c0c2c100c0c02426091852001504140460549038562900b00c08030342c92400d203041045a45500001e000d011351418000d40301d94a04402e2140d071360400d0005608401032043c1c0b1340182c2d9000358148140c602501c5c0001c01c60301e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 354502652 1250 354501402 354501473
    0x150a02160608090d030e010204090c050304050106090b15071502030a09020306010b12060d1509080a0e1005031603020409020f0c0706090e01061413090b0f030f0d080402060d09 77
    0x4143c607100700b00d0300300700d1442d43e00b94400d0b042042006480c9002615096940841404681c03c0c000741c1e40000d040401440200308080c05982c0c010600301c0010300c050046c100006000081c1c59041141d0010006590410030010942036280c54030480011500e0f0300d07180c882d03000a4610403030128424000e08002040c03201d01c0e54151042d042c5061072095081d91008103000b03c03400000c0041d6008480f519002c0304c1c55030580980b0000c11710a001d01a2280001e002c003600c0c2c99281944140315008103491044101d500030242d981c40341098188a507941400c050039402403240760005080b540c0001000b00000002c1740007442001c07080400ca0344a1690745030304503995885801990100024140104011807043c000c16130308550b00e0040a03d0030947c40100c2807103041592010a14540b90070f9907500b00e160000c204510310308190050b040b007139400026140c450720840007881c03d001000c0e000c13806544070742042d2806041c00c0345041081d021941483c003682c0d008502c0c03030a80b50107034210600d04c501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 354503902 1250 354502652 354502667
    0x42102031618110a110a080307120b0103051302090a11040b0a17070504090b0a05060c06011403010c02060103021903050f01050114060c0606012a03050403021306080a11150a021606 79
    0x550794052820040c0c001c004480404041c5141201845502c1b10b490109805800071402590301c0c1e01c85505a500d5001b0308030030360388402d00c05814185040e00b00312500641d413030104501b13a8110b40c40c08443d910112841c000301816030308043d04010102d03001c030340ea124070001407001c04e40070f40b201c661000e995000202919030840308140040c10600c81040080090b4104c0390301c4c100c0050810403a941c581c004109a038020880d50b42841e4012001002103210740c2a0b01102c0d0b80055000344030100c008032010b1358503079042c80001e0040c00c1440d01d100684a1122801024581c01025501c8000c107080c81c1c107010b0b284c207000b90b807010301c0d58010484413442c1071030840e0300da03207087c00c080c04a5070f5a0400544440c0701c5840500d40040040380240b100b0764810a48034181da1090700d4071500c0d1421350040c807803480b55014008106524100c010f100d00d000000742c00718400c1c0d102081440d40d5004501107040b4422403a11200c1e005000f081c2d058665070003041c4600c01d504c0c00c100469009a071104201c41d001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 354505152 1250 354503902 354503921
    0x101a07050c09040c0b0309071205010903090b0406090314152502070f06030c020c2d0a0b1b0313090b010f02060106050f07030e0d050a0b100b042102031618 68
    0x213540c0f09104000140ca440051a4040310790025074111035641c0629810044411401b110b59035910f03000c813410150001c01c13810241090901d41c5080a05101001c0c143c0304140c08064503142d03070a007201e400340350100804002c01c503564072030f440c0c182800382e40d4003c040600c00e0381c080c2611000c4501c21400f440042c040040b5017541511882c514a00312054008040008e4024114040c7c4600c122507a20303140820010401e614003032148241c014820300c3d81c0caa14034492a84542809101000b2400100040d0384044502c01001d107030f07040300e001f600c1d4554403880c0080395218469440004481c1ca03550700c1040e01c28030a88880200004801c0d0480e00c0b40c41c240117103c00b081003070141004506000303010b400d4091080c20480070200b8500009044045040c032b04440b260703c45082c24040000780030540f500454450450305003e4104507440032240110702403070050014034103003039510014810101c3c0c0b82980103020f45e944420a20303911a1380e00007902520080031404204071100a40300c0c4a40c0d402d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 354506402 1250 354505152 354505163
    0xd0606030e120c15132406090b0a03171c0204051201050405070e070e060f030a0623010c030c1b1a04060e0d05030715050a06060305010b03060405101a07050c0904 71
    0x841003001c010084051029006101450442d045c0c440001c00e0760014a0442c0a249114049100c440c3c2003038050340c4154000211103810041d0080582d1280e03080340301980c0c0d0050150204410742c4000065500524640e40000302888005000904440d4018020382d10b003513a42c003c0116413100c0e00c500b43e500c00c0d10000d245a0065208125071601401c50540114040c90026165161031002070210b1300310302403110a0a500000b4480809442c0c8503a0005200840544456181c1914000164414030007110f050116854210041500c40c85245076941e510452030602840404440480c5a180f0300520034005011040c01e026045103000347c07070440d181950740307404c065a140180465601502070454062006200b0700002548c80d00c48140f400c5d80001c0e001038103207801c0d0a84019180c0a52140c400e05140c407006116840345035080b264000001e803000308080d2602d60f810300e59030074207a06c03103225080c3c10f40521150401000007040800d000d0001c9580140c0442c040052548094400901 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 354507652 1250 354506402 354506413
    0xf022b14010c0311161103010c0201020d0b030c0102071e0302060a0e01020d050903030d020d1d061b0f030a09020a030c080d081602030306211b03011406130b04020d0606030e120c 78
    0x680e4034604504841040c810480c910714200507402180c00d42d09c0b0b810307513040540d40102d91a0031601c040d22030381103444012030041c1200301005001030b4448145010740c405c8034180d40341d1904941c20a1035104000c0d40e019101076a508141c009c001e0404000311004d0b030042c0252005c544034a8820700c1034884541005020310710b070a00e02c44400d4000e50210041c5410240c0f10805000360480140754990590a6a40500010300e48200b14101c1d2600181d803108032a40103100c00e80c0c002c40403c0607a030f80001d200000189140c824000954911085d0340004c0c11851464070100d9000408a05100b80c49850340381c81240340c5910412901440c0c04c02140401030380180001071171840c144230005e010003e00404880c500035640c000a04158240503801030001410080c2c5440b820300b44143d20300c40100d10901840343c107100300060a150f00c2100a980c00075207407500301810f56a0355044a606e030b01188000c10845a65080186c00b900018407003803040c5c05403201c0b52000b200100215134101401002408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 354508902 1250 354507652 354507667
    0x50a0c020316110d060914160306180c06030b010e011b0204020f0c03040e0411040b01020c01080c0f0412020f010f0e01081005120c040c03090f022b14010c0311 70
    0x944003007048000380d840b43c0200d102014107450341c8540e85403003030103510040345988007800c00c0400c3d1f0300d4030142e00c03045902c0303c100c0106240125850409990744180042070010f00f10300701d440e050f690300201411b00350441c00d0000e0325039050752000c0003142d030a0303e0714200c0c03441841c0103450050104a0141142d096040903200600d441e074028801c015050034807a0a10099041052031030b0000d07002020751508240070301050044c40e600721156000d00716814000d185079000002c0d16210100c584605001d104408282d11081880a03a4009981c903840991903a603115000d01007021300c0c0c4802d0780650010514901c40d075101e9000090520081c0c2c680200740d00c0d07030b0401180c081d0801071440384101000d42001c1103c2e680c0417085012040c11200509580703030705808220444405800c854241450b10601c14000391032035001080482c1c0450b130a11041e40b03541e0240b035070415110130340202d420100182c4802c00c60344500782c11803800110f00801c66403850711004c1e41246d2540020380c8400c1024488038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 354510152 1250 354508902 354508927
    0x120c100b010201110406020a0308060909031204061b0c12030c1709070e0a0c0905030c030c0409080c0a03020a05061e040f061e021e040311010513080a080d050a0c0203 73
    0xcaa1003010301c00080e241a00f100e103401d16802070b82150300180c0099080c0340034986e0103901e00c4d800110460322641c0e5801d025554503079038031070f000034007000f4854580041e06004a030341c400041038000c0c060075060710615a4004040c58403a280484d04055980101400d4a1082c03040c08103140e203540303648030386103034040c03995080c040003c00b14807081c0310702075002c034054840a600724019040300c0e20202c2d0030b5041e142c000d4440351041d00564066440140f0b0301c4056580000d01c40c0e000705094500203650210390038042d00030300c501240e003c074510804503014101a40011110350890250090f9080d0741c80300860319080700c2040d500c150700814203001040106100c00d5102240710b00c20000050809010780b04107401000c00013207103260a03800302e840050a140c404c8803061200030108014641811540c541c11500c8442d007010341000400b20300c6507800410440d00b080946991022101c0d2904289000340c500c0c1c0c00001891145410030703002c654031001501031a040e4445540103941890318440c0f24 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 354511402 1250 354510152 354510161
    0xb0a02010531150c0509040b010e090a02090a0b0a0e13090203150c070c08060105190b0f09060c010908030a0b010f141c02040909050d0203040e0a09210e0102120c10 72
    0x103458a00c90f680400301c40320840c2c800c441c1400d60b0760300e445455101450411044941b00c00c800d40c140002d10b04085410f0780d07030000542d4041c0326002c00680f98807801010038a030310502e402c80e00071240000742e48001c994000b46580318110040302c2420800c100302c5c9507241918480040250154040b111903100c402d60160b0351944881030210381818003180c0e07150150040466413080301907800800042c001ca05205410340701100d080e0001001c1c1e2464801000014860036104d04401e090105088615903181c400703ca598144500080c4150512410185032a51080d035080c2d802174a0050311f5203965002d811b801c896458540c64411243c2c0c59620540f007603038001e01d00d100490190104003117262045201400103040041000145204903103000e070725055822011405650090004000000e480e403a5a80c3c4001c48101c00302c0c480400745803114542c11441c81116500d08031508198425a2002e1007400c4000c00b613080701c51880c0740b2400200320388981041c51906c1d42040019032844180d9411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 354512652 1250 354511402 354511501
    0x1804080a051611010801060c0c05060304031707020309040b0d02060a030b040f06030b0f0a0e0d0f170403030516030b03032a06100914070507030804030c0c0b0a020105 73
    0x20903a280c400711010541c019407180b0021181d4a20840d5610a65644950141e02500c0c4600f02110345014907114002c0c0005644503041c8202c41c0000000e00301445500c01c2044480c00c00720b40801418500c001039100d0300032a4600d40100e28010728060945407200980c015990040c0881d803802000d60002c4018004000701141c01c287c44190f80310841c0144d200354001140600d509280d02c0c14101d0b101170881c480580302c85252030074401441c1079100702091083c4900310a0070f01140854180d2010b032004403d019920468002801c10071040c55050b401280c802e081c8103810b002c2c4180c07a42c0058040f500c0191606030594018801117503102c0000b20140c9108103e2820902c080728181c41080c0781260864802960712075003082045046624011100c24900245403184c544c68107000003009406804400703810040b5800c041010306000c0c191510081c1d42050725129141c0d00ca8090b40b4081c1d00151003800198030b002c0c000f6118241500075644444941c0000d01c05030440b5120b0344070213445010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 354513902 1250 354512652 354512657
    0x1b080f100e070509010201051e010b0c2a0f01020706080a0f090b041101090602060408070206280306081009110603060a090515010806010c03090e0702031308030403020f1804080a 78
    0x200c02140c0707100c1d8803034040d118900b02d0b070f20b8a90380c0790060002400d464000e4032285a80340c0c0d410040002d4101241068155a004511252184a1403000714604003070300f030340c464019070150402907409a0284030f5080c0700c0000e9035212051020782e0012642c4d0314042c405c0c0d1000440c0c207000f10704850715a8002500f9201900c01c040b85a1545440350401b401c020f88080303826030500d0b00c80680070b50700300702c20340010301e5180080c1c521403405856100340703441214802485280001098031114501c000c918095000c400c8290000c180c6040d4040d004110714018038509104040711703031201c80b80c04d015007100c1d180c1c000000710310801d0030018810302d500060403581d8002040c3c040842d03410750512400d88206440c505100ca036041d90f400141400c08050b14030341c10410200801000721b03400c2140c41c821249060305003556540c60a000707d0540c0204a032003910f0a00354040002c039001e0000c09002502c0c02100d4403491008110200701d5541e403034800303c0229104080c001404a2207000203404010b0050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 354515152 1250 354513902 354513931
    0xa05221508030310060318080403030c0f231002090a03080a03090f08030610030603020319030e0303130e010503071d0709030f05010203040c0e06130e030f0316031b080f 74
    0x510078942103820403a1460299031440390100701255150145114000c503401a0b00102081500e035a00c0074031980c04090300340410703500c1400412181046103e4255041040b005000200e44c4030b49241c0b0300f4041c1c205190340726491a0703030b0f1410894402c0782e1403200c1c0140035450052540e0389002207a0007841424040c55590014900410420428158007502c81c41010b81d480c80d00380c04004140039802415800c052802070144010307180082c14502101c1c03241d041c0504404d903894110381f9007070340e110311036014000402c00342403011111003a1802d9501402071500720741c1c0ca5400741a070310750291080d40020f075070b40c4c030304c103400080c6416a15804c1000c40c0307401070190b0b03140d4481d10a0f8650141007113030a42e41c00010841400b41d15940311014054580020006040038000030300d01d5104407400101265131869024610740e41001220400244450080c2c2c8034a013144c8410044e192427200540400d0412807030041c905a120004001410b65480310f014903180c40400c21003078580101607503180d2030003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 354516402 1250 354515152 354515159
    0xc1312021305180f0a020d08030417040810060e04080412141623010518210106030b0702070806010b16050a0501021312120c080d050103050c0a052215 66
    0x450060b03a00c1840240c60300003028844011070740c0341c40140702001c22181c204400c1140160760748a84400d8154026186903126101d07414500c1c8915240c16010342c090500140010f0300c20000f0030301c06505801c00c203042203010740d2640c940c5120f1004540081c00c840c4104814054251a1055040302a00070074818204e811b40b8980a403600e12204d0300c0709940a0b002d9410406540701c04504042c03e12000403030759001c05c403500007030014040c068404103400c0d84100c0b9942152282c0c3c40d05040100d20514a2003e00801c180150080890b17000580300139402c0400242e80700e000040d1071701140c80348002081141e01c0c1c0011021583c01a4a446860910814174040414010400c4118550141c0700040c1d81c2c0503130403000001c9114690143c0b61904841d01480c010640301c180b1448140b5003410125040e10040c642100b40b0301ca47c00881340320500d401d0000c0280080082c40155221060b124241e07000c0c0c0341d500b04210005c440c40300c41070307282801c0b0030790805075416040010074100d03c00f14510741545 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 354517652 1250 354516402 354516439
    0x601031b090e03030a0606020312071b1707050c0d12081b0304060e280f0c1e060905090903030a0c02030c070303171612051e010305030d050c131202 65
    0x40b400915125807004c001d001d40d400e1036206400013421a8002180b8040c3c00c00040218800300900481c180500b0040340d2030380174000320004110756800500c07003510010b003a21203003140c0c0010505803080d20402c901440281400882e0b48504c0307811040031076500c030f0f50303840498030144028108051103803031180110036420303c42e001d540200e1041d0b5020441f90390300354000345040713619190358445900f9104107180000302d00d0300c241045d580201c220340549040303003801c1a4007003c43c3d00644410304003182400d58409860341700d90a50301a6520300075000d0b915010890042e03800d84100400b03030002c20102d01240701c1c5601c82c131200701490058a0908070000886070030070610b40e0003039010071508412020441c41d0f40305490381c08601c03005401c150001c080001400307891007000360390364613a803a000b240c1c0380d20311021066078415076520015803c4da10f03840c0c001d0b2260000c120317034a0380c41d05000100b2503441001040e1a054001440c9000c03100b445c004814420740004001640c000d010078622121010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 354518902 1250 354517652 354517661
    0x50f01020a061e1a030105070306050607020904052d1014010b1b0616091a03160c080409020a031a10030f29010924050a05120103110a08010504050601031b09 69
    0xd40c070b0212141350600d1040c14259800100f00328100351401005200390790300c0382c0a03105804e8056804001310350320ba00e0306910b0000303901c4004186004042031040060f621180010304c170803942e0180c8510000c00045401500d403203101040941461800500c81503100ca000745c2507030300010380c00d6411007110281c06401e04205a81d44824501501c2280c0c040c603401071122402041542c480b10652400084800c091340400741c210b4099080100704644440c0c42040c24441741900800e1184d51196550b50b0f0100950280c139030880843d08005c1c0e0319040e441100d1107203070b40c1c81d1b000e0149044644281800c9008207540c0c4002c03029265100d0007080d6400d5225400340b00002080d1402c0c64080240d0b0015000075501d5020a08461100222550880408890a109a1450a0054880361000c005640e94000c51507a6100c0108483c0000184580c859100561f8082a208280310f6074039034480307030b00780d0700d088070043e00561008004200082848403114800940128800300b0b50352a9003540381a0b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 354520152 1250 354518902 354518921
    0x50c2701050d02220b1306110d27090518010b01090308092e081f0e04020f0405090106150c03090302060f070804030b0105150a0c03300510050f01020a061e 68
    0x20075005c00c40c0c00c200301521b0010006440541050300c101f1503042d144959a40b0b56548180030440c1440c120a485045030b03860001c1c0d000c8042e92003244540f1030f03c402005250848203002c02d002c0003000d440301c40f4810f1041511005042e504c000030070303080d5240c00c0c1460380b0088031207800982c01c614076444121044d4424032071380c40c250038080c00c03030083c104010a08a400b40c90802030348002145c04070803415650380f5104480030681c83c0030541d5198000140041e0760b94100720340060402082040e00207066001c0c0042d114506080b500109c90280e0840f4544542007000f80882c2c4103200c18005850008041d110f1142c81c102c2071890000140d0b00d20701c842d042940b040341c8442594005002d9468a031100e9121054640d20786400c0504243c0c00803e4175100300406803e2004000301408850780100c504041055900c0403055411342441e0141c0090204855441c80146400c002180900d855052001e135640d05a0003040c0c15601c648940e0001c0000444080701c0280c4401001c0004810b4010f00142 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 354521402 1250 354520152 354520169
    0x503090a090f05060102150a0c0c08161a060a18060b0a0504090c0309080d050612010501080c0a0509010639110f0306101512050c2701050d0222 63
    0x203005894482c6415280050f04440c15500554054000a00d039074041aa1210284401084400710134500b61060440c00c440034084510000d1082d4109030940c3e078004086108003842d100210128180c1d00c08607109442c0340381d111000ea03c0c10004071804020310025507040d03400c0019000d60b56a00f0034829403211010740c010841c045410001381c034440c450b540303209500341001e0100b020b140d542c030170540c0b16901d00c0c049026aa400821714941350a00c0790009800e00b00d00800003961541c10f115903608803111618483d003186400486d035030800d800141c2c1210711544a418031507e8044040d8000f0b1440d1446030340f841c0161250150074800305030141032441c0906040c01c4025014000d202083e01843c0c0300d0750295100c1820311402c405840249404c941405020464107040d00000f210802c0100010040550401040c48600105a4000c010100070746050081c0d401d00d0110010b032246104810502160b010321411190000307035002041ca0003901e071805061403485400038155400c1c03540007100c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 354522652 1250 354521402 354521411
    0x5031c06151107090c0917010227030111130e090f0a0c0e1807140f0904050102030a23010b03100312031d07050a050d08040506040b070203010501090c0206060d0503090a09 75
    0x1070b007032410320298024203c404400d0201050060000e03082d92010b01c610f045003d190703000c58421810130360556408001c0f5240704c806840d44080e00303011468000c01c07120303c81c1d4641004040e021014200310785c0704116140a40c1400351612a4a6821010052103c1440e0185070040308052206000d800c41007803003800320840765800d012055007070300001082e16a03400d0400e030420f103180c4000101e510448000300c500b07040009004000c650500180300034160010000c0c810f00041101c1174003d03501c41c1c11400c0d81004800d0110103007104040307004e281c1c0c0136020403c3c0014006400040000c40d40310240001c20f0210707644c1ea0766184820040d0490b040700107035480c081e00d002146203804555000c1d04071001408481d045c84c2c0090044882c9100740b40c03007500c0c92500042000800029940185801005070741c0b9195514513a4080345e2110740128480c0d440c0200100d00315080744100701c4014015801440d95a9802c418000403583e450425545803000303000c001c03815610703504620054509a4170209 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 354523902 1250 354522652 354522677
    0x80f091008010e01062c01020c0a090501080d090e010e090a0f0609330e0106030203030f1c0204060e04150305060705040603230601230f03090606030a05031c0615 71
    0x26403c0c02c06030000c0c0c0c204030498144445a5413140d840740305001c0c1802010400101400c0143d00d00006a8980c0c0c3e08854030203000070352a91203602060481e0003807816078205207030f00d09049900c15114090044802c0d04040144a2500711b500314a81c07008a40b021104000020380761a221a02d010408a4996454003500020003507001122110690820008040b88400b001e100da6103855407850303040703003a903202d413113201d030610941040300110780140aa075030f5541140b0940781580d104004142404041180b0056911046c1c800c131404c44d002d42e9200ea000c6003070b02042101070a2a4409800000b41c65080440450010f02102c0c0c0140c45035122150760741d00d44000501910450130010946040c0c2442e41d02e04002e11346440c41d403000b024a406000000c021101c0081828a0014640b88034004240303111140c64103001140501f41d040101c440f95510301c0201035464841400017041e41d04180040041001a140e002d6610340b455240440c4d4180c0b544500300b00d400c01c1c0038440001500020b8510b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 354525152 1250 354523902 354523919
    0x30d021303030e04090510180b040503040e0c090604030f02040e12041a070218040f05120702040b030c10110a0204020d0b092d0a110310030201031b0804080f09100801 73
    0x10380703007000071391313040c8000c995a890b819282d281c0107049000d4280c5541402c1c2c1c060300c07001d0345901d03425804000c00100f41480d0800c99500d80090043d101c0f0458a007020402454102c0d0a860782c1200040010340b0341820740e5500c2904c2e0102c103074200e810a807200c40c180391074941032255200e01d000400c046a120391615880c048280c01c985030480201a04200040140c1c071790002032200c0c403a41c10703207000316501e035450001c5c800400054054285c0c0501b010300003102e080b400007018018021a42482030342055010942c542d4400100a54040c0301c40c0c04084041c0d001c1c401c1c00340000c1184003550b401c50900e8012606aa0048151030809a580c140c003a03e2481c09041d1140c01c1145441c1540491081060745210394220320198a8244903400004c4c1100d80e85422241d050400545d00c291607052038241c0c0075a020660008902190402c80340320a400d203001c2000100c1101d603a248a06500d4a445070201075000408015100e9410454005940c540100603d0003410643e5552a5589007400c42e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 354526402 1250 354525152 354525167
    0x150207060f0e1212040b0711070e09060a0507020d1110140a05130201080408030a0612080901020607080702070b0903160b0d06060203040e0a051e0106110c0a0f120302030d02130303 79
    0xd10400020900582507540c4c5a25005580b140d0301642c40d940c1920360306000d0316400030b00c10881d0b06a10a800d07000c42d4000c4407803852801100a8021910903850b0941400113807041143e040b80181e01880d0b50b044d10074807440d582c0d040756000100791450f001d0b05c988041c0a0b603802c070384c0c00c90340c824000d0207114142406204a0394450302e1012256200442c03540000d01144000c4c0c00500880d00c044003142c90450585d203c503005014042e082c407080e0340d003407a0294540d00414003641c054011040010301d41030080040340d00c101c8030f5070301134900c0c5800c00c02d0817445a00b083d00c1968240c82120024000c903045102c1c0d602c00703401c0345102161124900c04c0083d054510540000c07046410500040040c905041001038105070410b0780811184d541c0030142c0d03005003d0100500c0c50925030800000e10541090481d8209800e40059440300400700c0300f8002c41e102284135510000c50451020041d07006101180800e09110348140c915103d41000588180d0300000341c1c403c075151000500f0410160003a48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 354527652 1250 354526402 354526423
    0xd200a02280f0305070812070807080709060f0f11070e0603120c070902032a0310050f0603070810080102040311010305070824060714011d1603150207060f0e 69
    0x8450040461540c0d0402c0403881080700800b445004920b8508008005040d41c40103011403500090603d845c1400500c108070540d14440030030820b8012400d07541c030660814082c1c030001d440f03140725444502d0048500c0e156001d070b00d1042142d954a4450000c500340304500082201003c0510720b0b00f0b100f002c2600780300f0150385240e069502002004400540843c1070422907845076401030310381c0d590034001500404072500640b507468507410026603040700c8001440c09194480300c41c0520a44405c1400610180c600301e444d8404400c2c0f0000710441d128054440c0e0090142a0000c4605d9442c0303049400c2e0307041134004a6500c18a011200541e5034184209684244646000d908130b06141c130722960b81000b46660041c445152071300c1555203481c0c0004031112258800c2083d10303d001070510301402003042d40d00c01402200300c52011010460002202c00003003880000a07408a46540e55400a1250500c603200650b034003480700300081a418822185043e132000004900d890f030b011001800c0c16220725 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 354528902 1250 354527652 354527713
    0xa11100801030b190e03160b090706120207060b030f0601180501050d02010e0102120d061707030203150403020a020d061e050c0a0813020405090a0b010602030a050d200a02 75
    0x1001000403c000c0c1d000c0c80d40001c00b410094030001045030105024280c000f0000940d40300001e0240b09521b40e0752080384103a4001d00c0400c10944511950f161555540c5c401c130f0300010b50601081004140d80d070300410a1910510000070307090b4010300800e061810b48041c0841c60381012004200c4403110705441c1d0032859007810104810b604240002d000c1c14550300000e410800d22800c2642c45034020800601c0c10f10796024295165040142c1c52401b0f4a00f601602c9071409074100d510000160002d040c1003500d034000c002e403401c034030100084802c00c2c078002c1041d0118030a030038284015884c1c072254210500d000c0e0101040e0007008080140709450a08040d100281c5040100a021000142648c1c15143c2c50300c1d10100036250f56003880d800441001c1c1c00382d0b01c90714000c01d000c401040000e000f507080d440707204002111380c0d03650000e0b622401558814004100c1c1002400844086a84003903248910003400600102e078100c06108190401f06003d0096030201074071200d00540041d00711401203449 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 354530152 1250 354528902 354528917
    0x1213110306220624030c080102090303030403080a090f0f050f0601080c040e03090a0f051306050f0d020103020d0c0503091b0d08090a0305010f0b0a050105070b15060c0a1110 76
    0xd0308046015061040000590b00c481c050300010042c96401000c0302e41c0c240721300070507101000700a440b4071010342c0c07000700d170b1400759103c00168040040c0240d40350035034014060f60550f0f48135202659207000c000c041d080050303690110131000a00c4034442580c00307406168080b0598060385011460500e90b0f80301103c0583c050001005409000107031100600410b95012030280300002001d071440c000e4000c070a40c032003151200071655240010004045850480396a40044501601c4604442260007499009120300040403040c0c200001016038040c41858014a4030044014500454144132a070030000380f800010b1104030031042040d84004054000c002c0201c1000400080034990a640000c024800101e640403071a0f9860503400005c43c4c2010090080160100500c0d00810100482030720500c84c02c2b5000c220f82d40301d4002d4607110395000290703601a48070100c1007025008070904043e80300404001200748840c5c14800e55503030340e11850000d140d43d64183c080041e0210740d40b2182c410007442 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 354531402 1250 354530152 354530161
    0x9060803120411010203070203151e070207060318150b0a0b0a02100e0106120302030a03050106080403021f1508010203180a020d1113090b07080c040f1a1213110306 72
    0x4058203030001d0740f00422075180c40107240140d00314040c8680183d4035000d0f0700501c504208103225000c0c0f081d247c5100156070240d000e82e00565141c8203541800059120010a00c150f038002c3e030040c100400e90700040d4007024a1a41c0f07000402c40b0f1682c040030b40301c0d1240380d0107a141c24400c000c40040c1249a26007400e02200d0f080003540c44050226500c9100e1710307084030150381c0c10f007980030502038020109290704007045400d01035030700e40c0080c030604002403170301d400016840c0c8603c1009000e42c0c0d0503405045902d80340f099080c0101e0040040c0c014075036a5501040c90302013048a584002d0107000300258076440c200840c1540c441200301d8121180e0001c005032001070b40c48407a06009240d001140800403d00900400c0b00d0621301c0000341d0801346071a1400e8180200b4400e042d03c40c2c641d40d921504269100701880c3d030b00d40180d00c00e504c00312203480014854a0101c1e40304d401c034810078440382c5050602600880b002044280e0700000804000000c19051081c2c4a0f0151070002d010740c0100b800341003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 354532652 1250 354531402 354531427
    0x11030306010e0913120807090e010f0b0c0106050a0f06020f12161a040b040b06031507050d0b03160f140a0905060f030105040b060102161a07020d051609060803 70
    0x1400030090b105a100c0400a040384c1c10701540940070315002058101d050b02c40b040054101d0805581e100040380e10154001003404402c500700303059900242d00c480c1d4191805450304680e0b044000380003400e5484180119203511003d00407402000c19180028440f0300e081c40107400c043c00e90b00c0007000350300f00d240082020494407045500055000040c00c0904681c3e05000041c1c0b0180d0303210030841100501800180700030300301e540f40251300942c0302059070744070a41015034030380025072001b00e6480300d11300150540c1c0c000d0300581008116420041404010000002e007000d007540090700c6000c0d6515400d010080b6190a00b001800420302080c400c41720490004552a50754428043c885807104002200d64940384c032070b8446030002400030f01a80c20145000302d5200c0701110702d98014454024041d0300202c20700841c80c100c0300d42a21a0b0f00c0e80d484595014400d42c007901050741c20902c040b0194001840400005088640c05a5802d000d0380c101036051064404550000314181d1090041c0d003a21035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 354533902 1250 354532652 354532667
    0xd260318030309060601140c0d0e100c021023040f030501180c0b030a090618031209200d020303040603022d031906080a0317090d08181f020702011103030601 69
    0x21002d0810803014040c5500381e0301b42d0321170048c41501600824120403070003900504541c5485008441c0750801e4408210104c1703a5140d84038029510217890361510503128003d482080d0950b0720342d544a0716a82c03003510040b44581c17060348a4130320600d010a0410503c40c00388070300c4003100b010001c0c0e0340300c0c0340300c5407640d11084002d80243d0780c682c0310000204440071040d0784040c84559002100b4003e1003030a802a003030341040070078282c01040d083c0d003003161035180350300c1040316071740e0b1149a5492070064500340c9030906840500716038000079400b80d03040c00b50350708002820041501e40e40140e03441415414410081515041240b42000722030100031100b0701c0740003500c0e80880c080321602c1d200e0924005034405030040e94400007260184030066000d1581c05000202032511120106079030761142108583e80351010001103000407088408684200c00003003200021540910446903400010084595000c50140c02c1c42c08031030340000d0020842d40c112039000c0420410001a60845c030f0b1900c000b82051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 354535152 1250 354533902 354533911
    0x1b16090515040c11010c08061804060e16060905011b080a030b13020d0b090402030c060a0215101e0312050a020f06041a010e01140d26031803030906 65
    0x840d00c61001a5070101d040e80c001403038810060040c441034454003005404079013400808000c3e0b500380800b000c0d950740115a4140202c802034111180e40460f104424028030025208842d61902c654030850294801c00072000700e140f15a036052400d510f0050301502da420300358003180c1030040d000c600989201c03803d518858501d40000e0001d5469040b05070841c0102070040d421503000c18040082140900140d0260502002c1a4800c00410900c0ba0401c082028100e50007989079000e9000d10303c10b4240314014024084882c0110303508100c21840300800e0903070407560005006000f510410076641c00241062001a0344102213034464150b448408464060309070420034041c00007041e150140c420401410b000544805070b41107400d0034900510841170b180c540d00301c0c107220342001050b80100c0351003180c12100248920041d4921079405d1112a11200c0c4040d0741002003803024100c03e0010004005a10000c03540c01e0781e903403402c3e140034080f4000780723076902c10b9541c410700c1007103181b010029100b0f410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 354536402 1250 354535152 354535169
    0x610020c030a08070303140a0509010b011103071101050d020403060506040b04090506070807120920011412071b05011d01020a1d0a0b0c0109030201110c10090c080a05031b16 76
    0xc0312142c0c10b0a50103011f03102040092515074500700311010400b58085d50160190000a2001094540046500e440c4540c01e120450b0004c110400009124841658140c10103050050410f207400c14004100c1c0c005a20585603583c8504c2001240d00d032500c00c5240d0403200b200c003002404965129695281c00040c0b484052144240118921038080e0f490b002a48195400c10305c900034180c9880020200300d001c401f00480090140d441e42d0390700620142161445034030b000c5080100000100d00f500d04090f091405014444081d5403074000c004d501c4202c401e0040002140c103000c40704000303001400601c2401e04903481400301540350795100200140803441400340c1601220760304005009552194881c031100d50300002d510715403003010340045c070045000b60001c02c5101c06548403039103c3d07c01d4407407100040c1c1020f40c4500000c18143c0c4024074041c0104039004a0325100ca88452816000076010355040d0320214085260080d80d4690451603400680038084c100480e84180504501d1405203412 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 354537652 1250 354536402 354536407
    0x30f040f02030709090c140303040b0315010e18040201021005130201030203060609191403010603150e011409071701060e2206110d1a0108011a09090705030610020c030a08 75
    0x41d56400c100e0324015001207101000340e180103150102442203584a407a80343c0c00d129035290b16500d0044156002c80324094601c3d40ba690300e034402c41c80c42001c45014603051103510100d4000c0e645403840747c41c04000020002c0c80407800d140c0006841d1074070850051907002e092804102070b004d816001414040d50a00700582c580d151400007490f640544a08035411000112302c0058207555050900b0481c0c20815034500d42c2ea64103000d260a03204a0700000c0c0020f03109198100e05603c01d5071000c58040036007c0009031a0303402004e20500f442e0b05a91650341c0e540503107414004401070b203030813075521000da20080001070315009402c0d00d886801040a02ca140188444886400d13000806950055210808000ca00505240e460043d0400754a4400003840d103040a00c0802c241c40c00b10b49030041c16100c404a0381e00c1c4c00d1010301c90324645106028102002d010235940c644911101c5c4d03000c0c44258640719100d1800405000b040b10340d00c0046400c540c0b1234060780c4941d0301c02042d440030700b98020700010b5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 354538902 1250 354537652 354537683
    0x3091203070605040506060915031903020a050f010204050f0102070513021b0a06050a0e0d080414030408030f21040c050d0c12150b2b03031b030b010201060b030f04 72
    0x1429409207a8000e41034a0070300003004200640481d40c03610645080743c072044252a56500e9181c24518000c0c03540e0154441d213961400041c4004803940814844c0c0304032103d0780955581c440c141221354000321900d80d00030400344440c0c6408140c5480c07481c3c003880105406450040020700301d125880242903c02da0015080c07032040c040c690600f410350f580804030360702c4110524050703009140494407043c0ca103180204c80d84500c000485d410f00c404045903115030150302e894075020082101c12a81961602c820040010406820b08c00342442c61f06c0443c0c00c0380c6512001c80d810501140c060300811142c00c406d02004000380707107103803680705072101600e0140e006800340ca44440c0240064116001e1440c040c1070f400700b040341c2c1c0c009215003058500001e1201210b5081404203042c0042840020207580d4010300c1c0c2da0b840c03072420115440380a4a0f0100f0210000e5008060110781d0452901c0003070f4035201e8030f4002c0d5809004542c0200724404920b0301c0c5142c08154000000000390004111a990b074890a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 354540152 1250 354538902 354538939
    0x6040815040b0112080f220b0c07060302040806061e10081b0309030414130905011d010204150305090304050904030908060709050904020409050106030203101a09063607121803020309 80
    0x201c2a80c3c1f60042c6403d54075101c0032103004507044000c03403495501c186000131402c180710b80240c0f006c171405880140040d41b6440104800c0d140f001d8119024090310480c1100680c1e03507440030450012645d01e80f01c0c00d604121032002100104501c9003441a2820401e02200b04400000c0b0f03000c03200703001c414041060002d00064240e02407d64444059811b0000a0742400010341c441c010380729406248040c1c0d40c00580300d0600780e010354421107090034151505072980300d00035004990b020b4280f000341c900e0b05480d00e0021704c141c40255415400150543c1007840300e41c00c200300c165008100ea0402919041c6000d001401e0801c0c0284024003446d21800b1110800009401203806185d00506540510585a040c0d4000340b40c440c4607815011a499185c0344c090503c01101d5010f510084c00c40800c04031000e0703a0b001c146924101c0c042c2c01d5002400d5500f2442006407045004e024980d98443d54400c1280b4180141da2a820b503807a050088044c02c000007a0300082143c0201c102a195060005007040c43d2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 354541402 1250 354540152 354540187
    0x612060714121501030e0114010506090a050a0b07140105100302061b060901020c1203060f010c0213020a020a020f0102010b010e1011070b0a180308090f06040815040b0112080f 77
    0x94540c0404040144070f400000020103050030042070380c04002c0080450446400d98469046500c002d0a000d4014885800e01100400c1c0011020f04036002103595040030640e091b4180d03100c80c2c0c1000012441c04208900090441103403403c00c0000d1100342424840b6007598015840024882c107000102c00c24103074280504003001c100038800f40c5d14149000c20007640030754401d5040d16094080c0116001d40948801c0980e409010040c1a810545003500019a891500c0e044207a9000004500d40309003c03190f030005041c1440345602034180f80550b071050041200b030241d141410359041610195459a21180160041c0700071201503455a054940c01c0d6003c0c5203c1800c01150301400d4030100c1c190a00f0b400a09240029603a9000812100d00840701600143e02005210f0314080090380e80514011080443c0d0260052003180790503030300c1d01458a40f84448011201e180342e10004c0200b03211031016424014118520303850311072400c55951801500c92140403103290040030400c00d80c80c0101402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 354542652 1250 354541402 354541417
    0x80a020f0a210312021b0c030a0309091518021e0304020303031f080a0c051203090306010b250318050303190c1103070b0403050601080307030509010309060b06030a02120612060714 79
    0x2130455441442c0049400381c4e03040f00e242640709109001d5010001e007070006200a800360941c1d203800c50795082030080c40282c40b14040c401403a907020000450784090a00e18106080038420006a5138480714244031841c1c0c0400c00d00e40702d1a20140204000340e100403048a600142141c1e5944255018103083c13440240340da04805214403d0743c0b895000c001015072441c0581e035007103c2c848618006854025035038410034401075019044800100031301c00c0f0b07080103804068080707008101c0c4030560301060344003400454001e40c006028402c5542000301c0d9070a844d0701410064025502d41070440044c94401000010b0740d8081040d100d076031600703200e0400c3d00d90003070313040003416240c0443c2e0790607864040383c0003400182c4882c002d0500010341d2007000421074401c030f0b80c9074855134144032000005500a000030780381503071185d4a602e00e420b5940d0702c1400840c0f150300059401611130452003038074445998014001400b800050200340344401c03000134200e6114403a442c1040d0200301e4551b0300c03a29070080c1c1c003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 354543902 1250 354542652 354542687
    0x9060118090209090c0309070b0a141206040f0603080322060c0804031119171b0706020f060105090f071e0e0f0108190b0105040f080a020f0a2103 64
    0x6804102004542c00510401500700c0d00003005880e6411a031045110603510908654801e075070400059950760050010100d250034000e40b03810315105520305943c0b012071550440700a20b410400141750a11a5506440d405da8040192a0541da21402507100103840b185170310b114505a501041403000c010004107510000c18042a00215805415903100f55011004a400386899400b85800051502c00c0247e8a60184000c45000e40313500311492410012961000e804210341d041d4035601c210300110300038084004000241c50424020305000c22000409600c3e08900010400c590720800038070742080c02110708131940e4032582002d44807450451810f461010341800441078260300a0242080840180e89071054400d0302e9004481c0c0035002c6440c0003540c051004e4048011801d07901004035003038181401072a01d0348032002f524107102d43d548400007540c042618141181000e05261480e51030954a42c00d80e241405151000313031400342d5040c50095140c4860700e0500d0b1145a42d02428152007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 354545152 1250 354543902 354543947
    0x136031223092a032a2d2116030303060815041203150303080609010902031915050d0b04050115030f20061b0106080f0307241508160f05090601 63
    0x30703a0986007080d009010354483d0f041b5442403c41000b002c1c42986605074010039242c0d1640c40c03901040b4080e201c03c45611703403002548400e00101c500401c18400140201c20075135810901e51314000701640c09940091440707800c13079003001c105600c0c980402234203c0d600240c2030541c94004482207008120307010311741c3c5c0800c00c0004000181a040341c5040d00642c010755846030b484e0380700e620300c0302a84010390f0402c0e00014100d415940c2c280304c41d440401100f03100100c500c0680d503940001144985044c9090740d02d158001c00340410000244903881ca042110300211701c15900d10784a00c0c01e40f460307442014086011494808405030354026510203007140003040c1d1912205544810405004801c4104403190302c1c01d000814a00d40003d0118a01600c0074011441c2c141d40b0383d1210802003016a80200e00d0322903c02c081c40081181c000c0031800141010b1522a03245405549460b03c090f21041030403e02c4e05d80350522918000001076001d584042c0c0c0e41e84286d49800740100e0700503100301c4001c903412208 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 354546402 1250 354545152 354545203
    0x10c2a0b0406090803030103080f072102031209010501030201020d0c060b270603010902150904020d182001020a03050315120601080136031223092a03 66
    0x10015209445007650f44108450304e80c100107990307210038000904084000d100c40006242e990300108080f5209144004401007079201072624082c00e800f8a83c0542c001041e6036034090364441d11039500041040080c819549142c0010f504e43c07417164410820032a54081c0c40c0d040c0f01c07054006000b20103010304086052084081d4178021204819100c1c041c0034403c41c04100545814001d841040780c006207226441800c4c103540c3c070750b103600120803203800903000c1c06440e141c50754501c1100b150b25421010b030f0a20545a18002094180010400200542c9244030302d034207990014011901c1641820f019035292641b0a000d1200f0803529201a80300d51003544003244401c1c0842d0450480301040024013210955005814840c1d00801440c25041d01d1a05082c83c0c03081c203016941031441c041c1c2498040b4000815a1b602594840304003040e14a00c0003003c842c50340624604640d104c0e0912000d49544c0d40203100c003950b049040384580012508040300014650f40502a00a44a041c1031040851a99 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 354547652 1250 354546402 354546419
    0xa0e060a080d0e090711070b0d0f09200603040b0723280e06090d0c1a18040c0c020d021302070308090d0309080f1e0417011505010c2a 59
    0x303d40c031507540204d01ca6008500c0c6613004182020003010418060102c1a0030003000c1c0b541600401140010389840340034261010714103220f0000f9003401810306215880310740c551101c00442459001340215010420000450b02001600d500b20126183c000d040c0341b03040112020100d8005180300300ca80c00001c001941441c9510b6400426682020040c907044500c071056851141b00c50501d40c00030710030440c1d0110f910f802c008a10700c00388a46280840c140c1c0300d440c05418280600e2005941460005510310794a10444a11310302100c01c0ba400e005002c00c405008040420805000340a0074145c1c000504555500710b811111140c07650085440360342c40d080040c8002c0050311001c1c5540a007130710721b03440300d4401e0003240750340c98229a0841c5414146c590100303113980315542105401d010141c0300035007807d440c00108010820306120389481c410f1245507608681d0541030b0035003510b92014003040140d0b003004c0418400c681083c54000c507000c041d038141124403204056604076408500c1d0200e050038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 354548902 1250 354547652 354547667
    0x711180c0702031b060d1e050103051005130c121103060901020a03140402150c0705060a110606010305090c06090d150519090b06061602090a1e02090a0e060a080d 71
    0x42c0210111528640d000039200c41104049094580001d01040303c8424021250031440040b402c114122820318020800c1208840d0203030800c443c1e41e0480c00d244180d02c0c91601800c2e41112301c86a518100741c296664020400c0d209224908050741d51440c243c003030010300c501c02c1c40c202c04054156070f0310b0300d441340700c030342c000d60200a822011170724008100d40c8018180100907c07413940a07004c0185103401d01205102a00007240810562107a000d002c0758039220040070f0103004c0101d403140100b85002082490030309500810705410035160008000d040040064804c14484094800690b1040050041000d09080180141100100c203000c1c0a404110b540054405c40200c02590110724810b138206080d1406000d018104a0650021030307a2441e029005011068410311110751140660f4017052161404803150f41d044d0b81d840c02200c00030004440103000303410100ca402c51030303d0030040024603d07990358060810b0f804507245c0011300544442e0a0344026161900032580c03d10a0300c0340c010100c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 354550152 1250 354548902 354548917
    0x60618061202060a030b03160801020334050915040810060e040c03020f0d140607030b0f030319030e060c0c01150e130c1508100b070302030711180c 65
    0x12868100300084100c25000e0038904180d005010900d084401c10045014042c0c25042550500038600c150403001d003444009802085644005a00c03446c240c4628440e01c1e00c071310780788144464000082020714a00520208141c0b00500f4044e4940c104040451070300e0a180c0d42d00350302800c00007000300d02c4400024140c9a03d10010300e05203d021b03151018400c8015043e20010170040700315078248010700d005a081c004200024003400e600741e105444042e450000511201180d030055814006010b038540507020344984255035044400000002007582c0380b0401d10001d080b1054240a1408548603070416000141b0032001c0340c6040c1020709400c05282d221442038001503213130030340492901100e00c0e40c08040302c090810502d0381b5900c00101c03d0060103070b2a02110801010f91001c40c803807500081c9070419900e50b03071f5034010526280340880140d12250700201d54000b802d0002c60002a40001141e49a650091001d075807800380801050000c85641000c0c4000d0700381c1801c01034403030030150191444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 354551402 1250 354550152 354550199
    0xd2307030b070507020a0b090303070803131209060f08090123010f09110d0e100203010f050108130b01120507031709040f1e0207081306050c0f0d05031308070606 71
    0x11038441d84400e4032103221340c280080d004491340c0d81c02c0004080f880d015107a103d00c0030303090764038100d00c545d11010700b54802c40344641e01201c10140c2d2000d02080001c0515150214104200f130141041e00241c00612001c0004082180f098009208504290041c2404400d800032548465095411000488100f4050400c851107899400a0b070301c5c03000e000341c1c2c0700d08600c911158070704a202109400505415484004a0f00c6210740c2241d130341d069880218020031080b2a50301e03940b410310000400e000e401070a0602c01410032954200032840401015045581014018080703040902c0d00703a084c01c4d01e0b81d00c007405d158803207002c3c20b5194071903500522003030100b11010003d000380d00340e8034011508010f05003d00c001841e6001e52101589038010b12101d8003821015040582c0002100541181508180000b800128050f540e8031010841240c400c06000d018001d4032841c0200107040340030041c41c44c1d80c07180300d40c0e500364144101c56085443c0950018400c0c08400e4880490201c5655252240c100c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 354552652 1250 354551402 354551423
    0x801050f07030b01050d020d090c0f0609050301020304083c04090b102307060e0f19031b2a05030c04060807050603060604080d020a0506060d0b060d230703 68
    0x1c264801d00c03440070b1110050b1145402c004031050000000e401000c45010030a942c0e101c03410129500354604001043c0c65a07003841d466003001e800078503500b107036070010b4041c0c0e0061043c0000690b051041d24100003c40c030384444100001c02d0318030201c411940301240c030303034002030040142440450000c1040d50403c0741c0070b10035000c0d0a02800700a445001c920000500840e243c0c920341400c04007400012844a08420304101c00d42d16800100c0c0e102522140b000c1d0701c038454105480405001d80018a80420401407a108040e10040c0c0112580b6085241460f1300030850f008001088850b000c81c0602841c0f406075070302103250004909a40380c080e56119100c0c4414903442440c1c640a41009d40d0f102c00302400c0c000349032109004440c1c20181c807140d4007407001c0c080820800002c100d18628001e00b6401400b5031803003418520706014000d01542c0c00384002d04403540c041401919600c2c2c0041041e00c04903e0001c4608120234060700c010200d000c00360302000f082c100d6400018000d401e40707000d0441c0342c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 354553902 1250 354552652 354552661
    0xc090b03070509150f033402060f010605090306040609030c0c080a11100905040902062118030405010c0210030905061608090114010315060b04121407060518040e070801050f 76
    0x51140121100f4410451041001417000f11501c104007c0500d125407003610918440c2d0f00030150010031b910b1200040e4001010031550380c0840120500400c05400d15030b18008000002ca80c031848004d0020303110b0740d02ca22440c1e04052080544d00c0d0309a401405102c10240c07200003958541d0750081e02031f0380515950120081515181e00140d41c07021481e102c5100c0781d8542410311000c1c0640c00c00c1039034450300510583e044500b0991801c0307001103002040600e0751130056100c0c11581c204442200440e40705000520a0b0798200c405c001900b601203074494400075034500220050f2548050040803401820148511f0303805005031520b98000c0e0380c07566445a66444011402c9403e440c00f0417250081400042010401c0d05911510010100902240c0d19407036021505403544540d000122807032001e004082804449944100340c07801e20380180c052035150247c000c1a034010800c1030154800728501c006850341d0b55502c007008195400781546c0d00a640d801d020f500901c821142c100c100000f800015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 354555152 1250 354553902 354553939
    0x7051905120d0206060d1119050112020403020d03030b06190206060f0d23030705120d0b1008010611011e0b0301050709060813151a040e0a020d060c090b03070509 71
    0xc2c81e1401258000c00165984000700b003182051804261901c106d210120030464941c440c1030b81c03440d03c5146411841620b054001040c0e01e200348054105140b0501041c4011799520000d11000760b094030f0301161203140c030300020f00c040c45004040d1840407400d81d03504c072203590042101d5101c0e60003118000d00e04107040052080601c54110000d000c0301c021502040d201ca01001030154080d0741c401203905011699480e24641001800c03181349000011505030300001041c003070100e000c10309464a1145045903240134004000602400e428800420190407506000750b000c03c070410f500d070004056041000340d22200070300c44031582c00c0c001d500b03000000b4002d900400c1c80e041164007a0ba156a4075946000d41c0c2480400220b078110380c11141c1e420022900c0410b03004042101010b4841440258140303000c10003110b640b00032030300c001e812100300c038005071740d0b84110200400e410450106a44c1141e0104640c510020f801c540202c81c4040207000189078003401a10350b03488182d50710000b00c160400c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 354556402 1250 354555152 354555163
    0x6090c1b06050c0c1605130e150603010b0d0b060406050901060f050c010f0606050310170d051e0a09030b0901060302090c160c1d010f0602030a110705190512 69
    0x1100408900c04980c40021000d90006a0041c01d0180c0c050811110b19641e42c14000310501c4200441001c010601031898048501e01c01c01c0d1f0300b01d404110841e0000e450305d840c0d4512080308850368441c0000141e00c0d4400b90001e9440c0751008048800f96012840e0103007080c0c000b5555140514580710000ca11800c20642e0203050b241309485101d4071110800d404c4035030394000780440d4425502da4140180d2850f0501402c0013074101ca03100d046d03c034500307220070420070141a40300410b80310210030050002140480d40a603050040d2410940e039030045076a01c820040419659040c020000407842d03406da030301c4118202541c1c881c803140600d80e101c610b5160300740d56250002a601507804c030013281845c04c119008010012050541182c1d4646540b00ca204201503544048a100c03452507a14103480c03180c24540c3e01400307440c0c140750209428200000d65030701600c0d030080144540c1848034912042e041111300c00812008002c01c21403200c140014100c241148601401031800480c0d40e00f129001003107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 354557652 1250 354556402 354556427
    0xa080f070f0e0c030406020403080403060515010e1026070c120c02150327030307090e0c03011a0c010203010b0a090504021c050a0e010218010f0503190f020405030307030306090c 78
    0xc01c42ca40da112188008015031002c2d008941156003004008006100d00c0e001d400214054076001034940307854880d0204a15000d8003540c100700307401c0702d1100e6a94542151758a00381c0a80b40c0003101d1f8000c1504005240131160883c1450401c40d410000280d910034bd840c03070880c0c4034502000c154514420140d0341b601c000c840003503011000d80c855904502a04000d03542c40703450038a402803100c01085000c420582040d010100c2ca030400410801410703001940070b4000c040703504902c4130a260045410000740418010740c0c21001440c2c4400720b4092104049e0350000c85804001c550f0382d65075011000030f40d40709003c2c940100703018010024892806100ba01c0213201c0380345001000a2000000400a010092100d050180d0307600703081c0032030942480500a0801c010943d4030019210301c00140840600d190380d40200141001003261071444442d100107081c40080010960071480c0702d50078040d0149810031074052101154a0b414550715401c5001122a685000c000d00c0b0340543e000c4894030182c45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 354558902 1250 354557652 354557669
    0x120307050607022506030504022704020108060a050a0308030603030403021203040905010611060604110c010204090603150519090203070b0c030d110c0703020d060f020f13090218010813020a080f070f 87
    0x10f0381004411b0080d002035602510040403001c89440b0003401c0c2c0c2002004440000413007403900c0400c8110358100e8002074100101b107a00c03002030f5240900041c030410003400014143e250104c08900c107600c0c100152405140d0003800b40c8144006e241e8004d507071740c12912440142901344000020340502a04800c28074040c124087c010b15940c86052001a22003050039510141c420020028148820f01c00780010306908400421014598104011a0840300090307200641c58442401017090641c01c0800b1003145d40c00000c41c20126600000b03003022950b5002c110b90030306c0001d000b0140c200100003030010824011081000303400101104115025070b2101c0d43c800d62200100f4009894008003040449104040c08034141c1444042d010130398102e45600002e02d44007017221009201140c03020f0015004200701103040c07480c2c0c4103003414130300703143c1894a050000341c03808a05100c00100d210b0340e0803600a00a9100280d40e2481c035540e60112001c464114040c245000c120030300030110441c115004035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 354560152 1250 354558902 354558973
    0x91b0117061017090c130c080f090114010608040210030903050a12110d1b0806150a05090d0b01060f0c05070b0306010221041d1902030612030705060702 67
    0x1d4240004000c00302d2695080c001400b2100342c0200031586482d20400150000d045001602014000a800380140c03603404282080150b0030919444007503d40e029040c0c0c441c03001c20340c4402d0310b441d006280011000c940008800c0c00421080d810401c2140154800c0e45e80880e80c40e8034980860490341c850300014001041000401c00c81c5105942d10196242c04940026040801401055241c1e0080141c01010394503111512900c2558981040c4e04920300d0a0135211454424006200f903d14036002451080c070208422071214131070070a590810901400c02407820413a800c0284000009114100010348080c07034210b4900e100302c1844c5c5075107038400010b002c80742c141101c0d45500c3d08000c1a4504520809441d8401700038801c00c510395410404030380c03a03035540c1014251000e540c0c10004001030400c1c0c4038140010075401d03110b4003039010000d42005807262540d20010741074041140c80c10b41d040c800815041c041c050702040036401400310380c0860f42c101003020502ca402d03002c070030508072542946 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 354561402 1250 354560152 354560161
    0x909020a1d01031d0a02030607050307050412080f131406042130020114070e090a110d0605040b01020c01050a1805120d0806120304050f18091b0117 65
    0x1803800c041e10707500050501041402c074038510b28444412030304581030560b0008450809500f424009640c12081a250083c41d5140c041000340862041c1d1180c03000341501c5880314028486250140e5951510580a850b03031222031150003400304e0b54500070030740c0355001c00d07065041600d01b0004441c2120000c0302c0e1240300c0b102001d4a00014046000c0540300011010700283d40981011902416005801c080d003080c454108802070071910f01d01407180c1e0101c48401440754042d004103103030302d80da0310445000509036110850b0740050021a1f81101c5c0400340428030000e002c1290b04060282c80050f00e040041030440c200490b512200c04004a001ca8000c1080107926441140c00c0e80c1f00801502000086c84d9441e000b00d0149004001480100c0c1c000380b0b003050403180d00c000c61907080171013210300b0741d40340019008c1162244910322800340f284403003e01300105519854a1800c003154903000b041c64510704803c1391500e401c0c414090300746001c0c5082c06025550b005100d4a01c041c41c400c060b2510030fa0701c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 354562652 1250 354561402 354561437
    0x190206030402040b032a040c170421031406060310120f0f060b01024c0213050307060305040b07030209040b040509160609080c150d1505010909020a 65
    0x81c1003681c00075100c100c4004135440800140e54100c040c4c0f0a64419101350f481c0c1480d40f00980030b9054440c90038011070a85942c1d0144000344200804820714a09844518180301d00300040d03400300010041032040000c842d0780641c820b40f085079605000340001d966803010451644000c54803e040c0200400b414007000e2103000b84000a10f00c5565500313111041d503154031010034a900011150340f6102c7d44070703040d65641800208840107203a4082e41c40c1da500d261008000314648010301e6410303440700104901d004403503001000e007200420421596080070440300001c05803907002d40d9000c2d104107400055036901c28403c4512481d006981034403552a1117100320080d6202c01400703540542c80d1a01c45107595a94030031103000f420104014030303200c4101007000c080040e0b194890410301903410001c1201200c04038000c121f04501b140d1480401c848002c02240070302a901c9802091032801c600c0e10f0700b141c0400d00389030503507400741c0b5206242c560302d480c000143d11541204c1000111001046e41d0802e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 354563902 1250 354562652 354562657
    0x2090a15020d020f3003042904050c0105130e0108010c0e090c0a0f0903140604030206060d0213110403050610080c0411070b04110616200a03080901181203020f190206 73
    0x24100c40c0d003d04040701c14141100d1381040d501078552592110170743c80d04030708c4250402440c01048030301d01c0c110300e41a00e405803580c411707900041c14404000ba000d00c00c0c0c0300c1500c0340030161442c030408020b13075612000c0240c020040e030500000892071505e40c0e0805442c00020310b03440740a00c4600c071071a00c215088221860000004e50506100354141701000080451101d0910a401c04d4024104c0b8501403e0003480e29002411083c001d610703200d000c60140c0c83d20035a0207044902903e001c203541070001d103014054400c0383d00c050500e01444043c05600354546030403808540f034003c100c0f0340c0028000104070031540701c02400b082ca22010030030035001400d051b50881d40180144841034501c0800d4001c00c820f5400380036880762031004000e480081000020f85020440c00c0d110380102d1162051010400024140c00040d10301840458000c035560702c12401400c5003005030007040c00007540d410201e032011041800072005401040d0414190314800502081c0064030095441d1290b880c6e130302031001a5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 354565152 1250 354563902 354563953
    0x3011203021006060201021c0b0609060c0f03160309050109060507230d0504052d120a020a060f080604091106070201020304030206030f040b0f04020907050d02090a15020d020f 77
    0x14066000420b20090180c416a0000d280b030f9000581c0d1003a0b0200c011540380c10a8211022951030f03d540412551905030503030b42c1d001400d03180d00390740d00c1380c107002e59180000c1110048910321000802c6620a4103030010246550710a031078080c61940c98900640f6034100700c0c09a100010001e00c0b210700400c211550181d0043c01d0b1120600000543c4000142008490002480441e40000702085a420110101954a02c980801e1010030a503044c03954817803284021041d100e2450142c820b100c014040c00480040c9030300400f40a0916903843c0060003c80c0300ca070150b004160946d0005a8604190251413182ca43c002e4442c001417a1080801405030807d4000782d0451005100200040c0c5543c80154010f640c4071550800900d05481c0500e0780100080c803801380c0e071508100340300050f203805004a03003007034003810400d441d901a011400020300400610581c0030054403030001e981c174045014001000b100c0d43c00d581040408401c1a65500c2414200981b10ba00c08040d00c40c10b6a136400484003207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 354566402 1250 354565152 354565157
    0x3010e13020118030318080705130905100e0706110a03021c021509030c011d0c041109180a15030209040227010e100609050f0409020a0f03060218040b0603011203 71
    0xf00d1024040804518402c0e0401c0300802e50301680450166806172004006200010062280509000109984800e034614406101e5104c156480402c0810702c448e4140403074030201000b044041403031a99603802c007032054101103140c468998450b2400860591080b07078164009108445c04c07800811103002d800030750f100440c029644982c00f0301c03200d007003428028080f8200641d1100320001e00c0c2c60848010220040f122404144101b0b801040400c0a20440400b140c0000e41601040c05c01c420600c15001c2c1142c0c004035000844030038840405016001740306100d0200f000c50806640a084038055000213903200744041c0c00500180b4041e10207102d46045561490301c012800c051041801d0001c2c2c01c1100c08040c5481000f08035181d0051490007400c4924100042c030340b5020100b28242151148540600d8030b0f16160425900e4000405005207011080400035542e2070400000a401c80108110010089004484d503032500c2e01030071210710002040c06145910300062102d0b1003002d00c07411801d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 354567652 1250 354566402 354566417
    0x40501030809220f09120806010206040b0a0b040903080405210d050604090c0807030510140c03070e090a0c0905040507090e0415140402040c090b09040b01050423030607020303010e130201 82
    0x3d082e4540507242c92490360000214101800d032070444020004a201c100402c01f0400401c0201c0c1e030300040c02500300c2e403c418512040d8555918000181c449281d60345c2d002410a101c00b410154084107182c412070094060b20900f00e030712000008007007a03003500110510403d10140c0c1d042c4880c3d9001e150810320003480002c082607140c1c1c0d03600080c0311590050089400064081083c02001e105000100500795030420542920341c0742d1880051010b00100710b045404400601603d00070400350078602c0c00108988101d1a0130160b5a000e881c3d00068400000d0403560b0010f00d50400f40100783c0560a03a480b44c095140c18208080070380400140141c954541880304d1080d28403140c801c0d0000300307400f81c00020840c6054010f02060f201041d03000c0d8104296480704100b800642400d4801c042000c40b0049001520fa01c0100e4207030181b50014a20f8813048001c1440e49204c0350007a4a24100680948841d542c5402099882c1d0200340304500400d2174100c0000c0170710070030903060000345105041036078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 354568902 1250 354567652 354567709
    0xf030b0d060e0313150507060e0309030109050c01110705090408032502060402010f0503090a08090114040909020a050109060e04091502120406050603120708070611030a09060605040501030809 84
    0x503501040850b0059402c0041d8110b41c1e02864042c00002c0e0101c10502144000f00040c001c02034451020080d059070344d207805141c1c054005004407202d0341d000030020b000410107400c1403030f112650380b0b41040c0440c0f40c01e801c10640840219415049071001011010b0b6a0ba4640314800c0e82d40c4000c0c22041c01c580074521084050718908008102098681c1c010002c510f032510001d48104c5142000d4001d0103c18410803081145c00200c848180b54023401461b1160708280050300e12078068041c03072050040100380460403100f203611600d6124003ca5902d0801d56607000103403082307681e82c0294400640c4500d1001c5003401c0941000307048034482c00401c4d02c40c1c14050103650807a000403020141c61100c0c02c0620080c45401c1c0207013500800e085010742204071a0b207000080c94410050004d000240204881e0305200343d644c02041407401c3c2070040c2d582e902d818269030004150400c4200c8400c0d107420000300e070608040c0300701d038162076201606030318003502c8104100c140ba02d20080c20380c0d10442c100007031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 354570152 1250 354568902 354568913
    0x50a050916140321030103050c0901050306040f081b06191103011208070804080a0b0903031618030605010308030906250e0a030606061106060409030c03181203050714010506010f030b0d 81
    0x32404c0f0f44c0754031003151070b94118509181080410004207110303800c0c500060089650100d40190002d92000c02c40c180643d2620f07088840e8004c00c9813005500890883c4404406004154680318800c51280c0081c2844c00061142c00c495840d40d0018210800f80b00600840308902c1c2043c0106019818450410026680d09603150f40705400c00400c54204140c01c80410103014045500508440091819031030f2200c03c2d44018180011280200800848c101d05c1c081100080040a5038000009005540c0c50f4100360b421703688143da10f07110600c00c51001902c1318400c41480340c0c80c444007100c0401115a011000c50b101c1e0344c04007185500010040c0c0000015180707108003401400d041d00e841001c00c510051003820800010305860180d810714003228000395024842d200742c1a8107060100c2c6254441318109480303400da412034000146240100c0d01890b800c607001e803010f41d204207408414a880d03000401d090b603200381d400601040d000d40c60b0801c802d002e030b00040030354240908214040011515403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 354571402 1250 354570152 354570193
    0x702031309020406030515090604020d0204080f030316020705100804140d02071e120f0507170a020a17060a050c310b030f1302040e030d050a0509161403 67
    0x49070038194001001c001040d00360081c1c0d030740032035404490041066441c0200d41050f1004040741e1040d980050343c5d00d100003541c1e0666001d0544501180d8030300f1000038919a49502c2a5039144070041030b0069068101c0c40040d00c4c20580d04042e2210410302e22943c8156070001340900100d03003402c01d208150b01c08040c20050035000c500c5941c010602d40e4a0310300361040e803000082c401c0c7c5201204c0d8209019240401c3c1c80c2d14aa1a0700041e0a025201075041c01ea081640c10741000300d560142500b0b00c045a1030001d03600018500844000805664580004071005030140241c0d03440d8020348005124015207030b115582c402000c0084514006101c81174158044521000d00c0c8402c131100c000030301e42010400c000c00500341141c08280f860921003825540c0c104010180c0306441e221410600031515290002804110f1150445e07440322442248880a00f04c21103040ea0018540300004e00d83c150002206100d134500c0c1d0301d0461045003040c4888220601d00d9a81940511500e070000c01c403800103094 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 354572652 1250 354571402 354571409
    0x100506120604120e0d170c07150302070b010b1216020102130f091505030303280606030905010e070b1c09050312150102030306060910022d10091a07020313 68
    0x2043c15040c4010501502d07640702c4940c070600603e0800010300001d41202e1003480b014102d01400d548888222040340d00c1d041342c9420100b028020041c40319140c40c1c164020389905482210701c5100e682e02c1d04840c42c40342c0169520744d2400c110000100d03c080d03c0070078000717025091a20025103080b0342d40c480a924196240e0100a0301d007224001000600064403503216190030b0f00500f034400d1807800d00040d0741e0340006414030110280a11080c910882d540401581c41d810450051181c185e803540b014008020540c0166075650a02404c4000d0b4540446c200f01514400d2840340e041c5032044940a0020229003400680e2507507860f1380b040072030010400f5080181c21902c00c00034a140c81c45061a0750a00b00e1801415036009005101041c0e03210340c1503801d07800c0292050324643c514507100f203141000390084a1484603409402c45514500040d1540c941202007086401d0000d80780105c400b110741c05500500300381700010203055008004100070b500010644110380c207080041c820715490150316070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 354573902 1250 354572652 354572663
    0xc030e01121b120203090a12050c1903110c03120702210d0207090c0e2e030b030c0a0b07060b010c05011a0907080403020607080a0603150204030203071205100506120604 74
    0xa451810b4550020580242d0140c1e150290b00394105000e00307540c4e80132a004018040074541010480c2248140140d5a84242d514202c41071188030701010074028050440980000e1724a100c0313507203c031760001455801e80740094020b02c40e1184c46103504050b5003048a0881e404005408070100c084081103e1aa090301e0310005051442c441c02c002034608402d562184006500b40341c00c4c3d01820340c0140480d40048420b441c81a09504031103499010070b40e110305401c42c2d0100d4110b880d03000ea9416846000c500d8000e13011180140300b950304014403060144240301c1c001c0c00070000140028441e41081031004c03010704004801e400e45648560075120449111040ca1119024680c0686080185a40c000c00b070350800700302e1802c003034130000e49841006107200203106500d4049900082c45a014800641d0410300c0441c1e4103010110b0107010390b00c180b10907031203441000c4010400001c2110001030142c0d01c00001c05d00710080c02e26a801034480141b1140c2e00035401e50301c420700c0403414080d030342c41107204070f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 354575152 1250 354573902 354573941
    0x30f060306023c07020103151d070f0e0307052103030c13060306120609111002010221060310050405010b0a0306090c0e130b15061210090c0c030e0112 66
    0x6450f1032642d00c0010800e4160121408007056100c03a0001110811602860302140390300040400c0c0e40c40b031000d40d00108010b0140c101c02903000c101c09400a01541c01551200c0d851040010b0480305c0c00c459000441c2c2c16044000b0801aa10f06000030446820001c40c070115001c104440e0035055400840301d0303400c440c6000034811083d01c1581d8008000d4001d5003000c0010301d04050a90a20b0704100d0402409160380b08041c2090000444003010140801010004007410216000313020350080031007036110b13401c200c40c580e40c40c0c0e03501112039114800280c02829420380345500e41000d8840500191859580c0301038036019911000e0400006c0c40c004c0001040d080b441e460001846030030f69000710109110300c000e100a42d00e26217181c209454000034800d00c00d4079001c5030b0118105100710704607409100003a02e08a250040e044042c45500100b0101d5400c80d071f52000030040e16110065880020584c21040c0006801000403800210040c500082c0280080c4100c0089400340042010200c409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 354576402 1250 354575152 354575197
    0x3080a020d0e0d0b0117010906020406031410080604240908120a061a0a05090303071a0f010b0a050a022d0c0103060302060906030415150312080702060106030f06030602 74
    0x40700700900ba5000d0700d60703007541c80194865245010041c0114a04031214550554104009400600c0c01c1600524110b60382ca80d03801c000340041c40e01510030440d6801d840001071002e215040a8001c41d1300c2d02010348600c0e40c643e41d8034054610000504195101d44030300910707075216148a40c04296100d4007800741d0319020301030309a0030000b00620070f4042508201c0240540700c12080400c0384107004640711603c6103006081591035004040081e5014440410b0100c24050040344400c009410b442104c40c003034607071044e002d05251090291410110701008a0300e40540303d00c004045120706407040d120070220311408410100f010040d8648400b2764225150074400f0140040783d400ca2090904000c05450b681c08240c042c05419001413199801200007070502c00d00505228000b803006008000b0070100f500c04290994160005031442d646100c0c0740c011041c0104821401807006400804080e0719105007100580080c854511130181c9880c00040010440c2c0058118246144150000c1048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 354577652 1250 354576402 354576407
    0xc0904061d06040b0f0903091f021002180f0312180406050909100c05090a0506030c070803090609060121020f0a0506040b0909130b01060e1c1101030b030f15040c03080a020d 76
    0x14064401b49840c2c10820426020345c3d1004000107180a688142c240511804e404c2a82003050140b10031240c58000139075143c0413074811410100d4882c04480c1581ca6441010515030380c0e90401450b00602401008800551104603409501c151001000030420548039000301d106102c0c2541d54070b000d42d201290501d0032041b14051603c1a4407030b0b140036030502c6c11620015140b14030358440e40e80544c40c008003041301449260215441e03e50414129a642e003401e0380420380c0da1900b1030b20325015005200020030001047c4400d0305143c1124503906075071000301d8080111160840002c0c540c00b996000c00003516445002c083d05c0144201084030751110051800d02c008170800038040215450303095032000000d0f1080780028103549080c940850642c4e282c5010910056080016005a0020100010800c031100324450070803a420399050154a100e0800d0542d9055003540c9a140758105042d8680d0303141c0c0444503245c0c03041c010705030b031025140d880c3c44841c83c03a4024211000140c005100c4550000e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 354578902 1250 354577652 354577681
    0x150609090f150c02100509010f0504050703140a030e0f011224050a0e04140f070b0301140103110a0309020607140c0102160312050a030f1505120c0904061d06040b 71
    0x20100b181c00d211400403010001e49501c40c5051007083e05980d100400c031250401d50010b00761441588040140c0c1c1090f040c0035640d0350079840101c845408a0300b928440300e00104080b046103a05440e40701c14220307044100208801121141410801d07000c500d41009440b90240300307180c03010700d1071002025540488180c41e011040d00486d01035500c0e40400c0100d400c1040c40107501c10b82021030618842c0403c009582010003a607c40d105034402d0010108010a245005504943c17018a1100d0605072490066050703813004500f95506010911404040c18041c2d001449514401007903141390a0342d0380e484024809902060031100e1317210119298003560100070300101700000b18036800585240d0340d41c0c031300e1012000c403451003040f20201d001501c60303000e900202090504040b003480901c000b00f12510030341c03e00e44074051144070000e5405060600203d44c0700400d40c0701400300c00290340e40d600c0e0200034041c0003207a006c4e0900025901d014031a414062140614442e074152039403420000708017504407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 354580152 1250 354578902 354578933
    0xc100f020d230703151701020a080109150512150c130501020a080421050d020f01050618010e071b0501020a200a0b091002040b0c1005090703150609090f 67
    0x70040610201036490101a0007030307208050b4500800d2840c0b80145007410440d49902c034102540b640c0006c0c200d01103040d0080d210126203a590b4102c984e03a0707240d151040e6009801c1d400100c880c0360000f4081b509203007096034101c2020030100c1e40d50400880801300515400c40c0c101ca482d0700b000c1085c50400340340c0c00000c40103002c01d01c0107104c100c800b9200d9134104d11071407190101d00300f0b001201c400c005600f00c0400c9035603034001055a00882403904080d4480c020324100020551901c4c0000d5842c7c901211440f05050703002099000503800c00d540d00c2d21040d400381c90142400541c1071645544d070b00611041030b6041c4203400140e10f6880000c03001d4409000d00302c0080044000140d410340e0398000080c8604201c0c1c015594441a8854001580c113049034030720080342c00750000902044111210005118800f81c5108552111b00c42041c0c03101101d40c01e442800203900300000400c0403070400c003d80200c00c00f0b64200020540d80d106524821101c0ca420125031512000241d5410300403c030071503c0c440e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 354581402 1250 354580152 354580181
    0x509121b03010605011218150b18070504090b0a030219081b0d0204200c010603020f0a03050d0804060e010f0f050f0f010b0c07050a0f03050f030c060c0c100f020d 71
    0x8144c2000b0018020354402c44a4006203645c0303160b084c4621030010001e811040c2c000410b50032010440c03000b20007030410f14882900603085c0e02140c4005500c100396080c4514035955480e42440c0c01d103850000600801c640c0d0b07a50000c1030707150102c0540e40720092307212141100d24580c04c00d186004c00503070420740c2ea5440215944119002c203c8035407601b40035a1140c80e41250005004a5131070001710151869418075501c0d1000400c0b4200c80c01c10541c001c00540e0700845418840125a40401c070301040c2034003008199802904a803484203000d9450f40c1d810030303c00c01005c6010703041090058211789030b5020103d002c988802c6a4240e0681e1807068903008200b1001c101c04915100130018070f40d00042c4540c4418101c0091904c1c0710070310510a42d40a494000c02c40d0200b07595410a05c102500781d408140d845d40a01d040c417900f800c000104030340c0c0400c00400500b0030380c0d4480081c4036458201100400d0240110200f01d2001d6541c1d00c01c01d5030000c0d0b00300c0c006880d440080c061034110360240c106085d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 354582652 1250 354581402 354581411
    0x6150f090801090c12020d0f08040815040c050d0302120304030e0406080a1208060a090501030f17120412050409180302071a180f090f04061a0d0308070509121b0301 72
    0x2c25004d04c400800d8130421203000e1807404942c804505551003d0740701800c980d9a11070008108600c2000034803c8480032800c072104900c1e1401d445120310019103009104c45001e00c0d04000b1401c0200b104c1d0640f80c042e0054500c4103c00b15680d00c03440d44110b50445c0001d540202190281c41d140c498a4041c003410b10081c40740c000c2da981d4036249808103070603260510100200040680c1d4075511290050101d00b0b8082c00381d560343c0e00e0300b0200c008806104440d00709070344440140f030050080c1580c4c1d205842004203000c40d02c072902c6241900b08140c0741603041002c1004041490710442c09007c41d8511074106101d1609618140281019203c1e000b0780014150740c4100100d90300c0c103c4c1651501c0300b0440540120100c903030005583d84008203a12a08002810300300424011241400362085000310801c1c0700312848601502c5411841c10140b541c802c40c850460701c0820b10490003a90312507120300300700d46850343c04800107440610b01c80c06001590301c40c040900300d50010101132958400260020300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 354583902 1250 354582652 354582671
    0x105070f0c0b1513050402030c090615091801030b0f09011a060d020c06010b030411090709030b07090e09030c070e090604030c05012909070c1106090406150f090801 72
    0x3001c28000034005851180c1060104940b409201d00399024208000e2030600d80f0004242c90307801402007210107900c01e000d14404100310341003400039a0306c0b519008ac807108d41501901000300d0590856030216420901e1407030f11200e03200c07008400501035406120903240314507103020100c1d441d101c000d04243e0a64107200c2c100720301500030851244842c0c012143d03180c4034104008000028090080704050360f1041c0c0000003000c0340e2a800540c000c074015140e02404080400c140080480d0586e0200001841d10f0b0040000c030350b0b1403104c250041d0321460710702c040d541d40e12070400b80c05000340c5815140d90800108402110000c200c0c071303c0140b03890307030115099141044546448400051000e01840820300003074042110070f41c0300c42107291010300980071000c40420103400704a81400c000d0b00580b011030104083d58081c802c000c0306035603c000503910988040040c46426006582c010342c0013621004041107001e046800c8801d441034079a00d0340300129105900402c0c01096900411041e4500f0900c3e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 354585152 1250 354583902 354583907
    0x61a12010b0616030c082a0c060a0804020415080c01020d022a030a0b151302030402030c011d36160305070e101101151d2d010501020105070f 62
    0x442d03003500e10b0701603c9208052401d0540c1ca401c0d485800620b00240042e451100301c41c3c00040941c0800c031404450b09468140000c180d8605200e82020780c84802407050524040c41440c1c440d40c4540701400100e450201d20912048420b003d400c00744041d044400900d00b60b5904010f110308940c090300c010920420188000301005070403141115450038041c0401045440800c00328440c540e00a61800c100c0c541040b400d00361118041c809445a00011070360110b0103800d0082c0c030300a6400034040c01041c0d44600041d5213031104100c5841808014000c0024660340c0c100e007001062408000011240f84010060070083d411800090110700b2890240701024680e118808446c2c442ca0400141c651a001c40039034005441d40030702540006808a8892019480300da950040074404000784003d0101c2414000301d16981d0148050140032039102c40c800d03001a0769050781000c0a640030041c0610312800400c0000c404841110701c40c1d1020f13004010550303091040a501895900d80100c4451840800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 354586402 1250 354585152 354585157
    0x601050103270210020115090e07120b0a2c0307020411120a0f0b0a06020c030601091107081827010b120703020a030b06040f0305160f0e090109061a12010b06 69
    0x40c0c0204c02103914810014000d41c411400c032200002059540c0d0766555501010b41509140c80c207060141203c0028900c05d501004020960310445140305581d40c1c212400050a441d5489060308480c000081f80480500c02180f079840038030b0003d036035540300074014031042d12500046051814401c1010060a80d64107802070b0b04034445000100b0883c15158008014018070424142e22030008800003800b01d0700060f503000c03500b4058040c1d03603c0ea81c6eaa512407003151005400124220301c100421800640048001c24405c030700c66800168001c900300118141c0b18810081c4001036000c8403409501011940301d19004140009071546048030300800700c902c010700642800285600455140b612a0081d0446a060600505002d803141e0b035402030191400350724401a1003d000301207440c080c00c18010b0500045d41d0400022a802c9443c001c07a110b5110002082d0308180d550780c0004c24002041402220b0416400dd40c014004002850400284c03032420000100b81380c0c58a045030b48991074440a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 354587652 1250 354586402 354586481
    0x40e150607030f09090c11061f171c0908160308090108040807020d0b070f09050303030403082802070b01090b0d120c06021606110f03010b0d1b020601050103 69
    0xa00ca03d800680410581e040c03034154001c3c0d45818104604042d4542d0b0220b100e042c540e9841085501c0c40c1c907040c804000180510700c2000d41c0d885407110511140c1c46158030011f00d44c0da80000c5540c84600c006d024610304022100503000651010020400240204161301c40804924822006546150344104d41445091002030520034441c00286c1400b2000c42903d40f0340f500513007141ca400d5010300d0030403400380e03048071a080072504510140161070b200c0c008650503101d001e802549107444a450941e16000300502c0401e83c0221281034690b0755000107014032100c04d1050340942c984820345030401e0003501c140c2110081510300a103064050740c40281070018540c0001213201e002d07414520131078607039400c840c2c0500080e00000382814443d140070207a9401500612041144542ca030380c04901d02e11a03241c10000c4400144014805085c2d464002c181c404a9010001052000c041215514120000e0650302503048a00100020350301401407005010f00304030101043c50b4803000d0071080ca401c405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 354588902 1250 354587652 354587657
    0x40516030216212309150f070f0209010f210f0c0b040f09110d0903030222030212030c1b0414011206050609160302030903041d07020c030d0c0b1906060302040e15060703 74
    0xd46c100e0010721048841d40c0c11b0b81400c603590388140741440e148016407142c1c201d00481800d4000909540d0156480054910141007480350503800031000c01761041070301054940c1c484079140d0000290000054000500000341030380d4075145441c0d6041102412584018500b82c2010380210605020304100c85c501c5807a01c40c000f55441c030320304046009002e016002400703081c181c0d5030107038881a120401c0048034401c4a9480960307000c10801d584034041c0e103004941d50380c0400d81c0c00300c80c08a40d0b00f80042d15075016000140350280b2403400e44483d44281e0080700b002c80d100c1c0c2c1500034407000740200c80d44a40305079003260712420209100300444000903040420175a02002044201c04c040c0100c4000300b03c10711409050307028004490303180b0740702a0760b1352000d80b02c2e01d162004103050104002034401015212a4081c0c01e480e1140d0760310410081921864110400c40301005034020b05c60a8050002564010388481c00c0820f1401150382c00741c203420f11408091055035041e07490104403000c045d40f51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 354590152 1250 354588902 354588919
    0xd03080c0703021f020c0f070803040b0711060a05210402060d090309080a0804060207080105060919140910110712050a1101140703050105040516030216212309 70
    0x605041341000d803e0002a0010b440c280c064448500154028006461102040d189500442c104590b5a00c1d110722070b00b0b00c2504240820001c400314a005041d2032401010101c555035001400100f83c2c2d032120340d0031404500003140c0103a0070002c613000c1d04051a48480c08400070308160b00010320394001c410200215a480f81c55401c1050710a02d40c0ba00109804021a549640c16203085080b80c1c01900618006200f03200d00000c0407601401100d00480b409441000b02d80c65880f5205981864980c41a10040d121601d45044c3d89600840c1031090411002a1080e020110a00c10075aa0054101641460180490004030361030f881c801800400c2400c01550b00d0000207001e4820044031404102c0325403034040510380c3c0b0114480c5c1a4821062036504001c02e17a05c0c8d80c1048200c54095071109810b5030b80d8200400240c5c002e5006001da400a408105031014040d81c800110f200b80848000c4648400d03c2c640d4119504000200e05015030500c440c91b0848030300300c008019020300b550161280b40d81 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 354591402 1250 354590152 354590167
    0x6091409060a03061821140a0806060d020405131505030106080c041d060a050109053d0f08030c010e0a0b1605040b040e060f0415030b1e07120b0d03080c 67
    0x40c03113000c0074043e4004210480490806c40e15240f881d5075070342d40f001244800b407411720060724110407109805110340354103496444c1e00f01403084507000b410286007000d50801022455503580f800819109200704004075a8080b12801e1461308002a80854001da0400720280041d480215a040052106840c0004e00c0015040104940342c0340c0d11151005025810500c504005150440c0341660b0090905200b0f40d1150000310185810710200c0d22003030080c00410f14514070301d07000e01c0b0303041a01d83d1544103881e6803100142d030340401c4140d1250303016900024404180300402e01a22a407065004050300306800d03103807178501c40c461004040052242d4900624240540504c1c250f90213808030507490742d2900c0d1035001540c108030701684d241c3c0c840c00c00303031208031024a484d00412110600b141d031a5400c0c43e1841c0d40320501100043c00f42940c58502d000c1500762154204546441001c2030b540b0400010343c0b07080c4180454582030110307401070480c41b2804021036000408250006402c1d2500d82d40c9414 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 354592652 1250 354591402 354591431
    0xb06040f0612110406050304110a050d060c020715120b03060c04030803040807120504030b090f030f0a0e0607030201060f0b07050303040221060103230f0705060a0908030406091409060a0306 83
    0x60303d4882d00100303140440e01103401503202000d188070342d10850712110b55101d0340d002c12204803002d1081d258048410403c0400144c5250800d03505110940103d45075141c407850181d04116901c14044005403035059000c00c12b00150003940300c44407095024007554104260b94445a106034007010f440b2100c000003180401403140229255107400c80c910102e002d2580000a00c580e1080c803091320103607003400120383d5a55010600c02c40141385a0b0080d8a4040300c3e1001d6200780d042400315a060180c0c49001110649801c0d0040840901c6540005102824104580e00d03a016640040500e80d0003440010001280041200c0d0041d404840a1100000e0582c1e4644007010807141081a402107070000010802e0a2003210288920b5110100651030840c81d0a6605c9103403030758a4000c0d501c494410801c6082080040502085910707151800546482400b455a4416272262002550a0304200b05001000041700b40d07281040f1880a034a08201000a460407810702000d80700680e681c0005c0c65116 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 354593902 1250 354592652 354592661
    0x60a05010f1b0b01050a091407030510080708030d1d03090f040906020c0d0f030b0924031c0306090908030703150f031406130f08070501060f180b06040f0612 69
    0x100c4400302d058021107145491035220070281710b910300400c101400407540109a01500080c502030074090303a00c50355054070031809000e01406800c0c0c15a459030300810140c1c424000c2c42c01900c4554019a941c1d20400045070484000c1d079001c0c02c0005204a0100c1c08084c04011180b9842c81180c101c015600c40d1800280103180c03030034004110342c7c0b0001e004043c0d0500480c6402039440c0741c1d00c90324680c0d181914150b087d200d20820480d8803608150009401000e0504614800303155070044903004404500841e2810114066403c0078000042c1d28005055240c0221030190210f5002031103000410340d64030b01207000281c02d99049c0760b2540c001170804e840b02c100b82c20041c5841407141811541c3ca08081c680216010403002441c01400000ba42d03aa91210481100030f030712a1a0440100c620f0306e070120070782c00440e001c58103035490303e2001401c0c00b0040311402c064210724100030030f00c00004403410220f40c070200c2c10500031031040c007040220103100c4240200301c40c41c50600d5448140912041c000a1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 354595152 1250 354593902 354593927
    0x708070c0f0c0e1f080318090a0b1c060501050a0506040611010e0d090504110313020607050c0d200118120f1a010e010f08100209011101051602070e060a05010f 70
    0x103a00e60f08000c400c00600c1080391240c40c000a40c4042252910003440d1607200b10401e01243c800c030a0310002040c103001003800e6010403c0071000800c0381c068030025040c01181d4804500c00c90503404000e080c00094440c0710300404044038500410740c6048040b800500136407283d0401d1024818107094001020342250410140010542c0c0b0104c01351000640b42da1000c1c0117450040e45440c009801d0f0a4100c000c8034042d002081e00e90b840c000c078035400c1100c6a0f22801040360f441c01602644203a84d1203981d01c08100c1845580ca94207a1704020b480c0914045001d6500341c1009140004212a01002c203545400e40d0306607180d402c50201e150030076444503000e4500051058084031000c180003060240c1040c16989082d0240d281070f6a54070001101060500a000303183c2c202d801c9244100c10250300800c400e00c011305085903c075205010315400c450044600c407000040000b80c00301125030512080d0043c00c4050240396490a003074010a0081511340283c0d41408040e401c100e0b1070500942d03608181 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 354596402 1250 354595152 354595169
    0x609090a1a070306060c020a030f020109171b010f0f180b03041b06110601050913051014090d020a15020f04090b0f0d080a0e13020409140708070c0f0c 66
    0x6100e529049001d140070300700c0c0c1e90400030707142110210706140700b480040c940940007030a0b4212982103403074050b00d140c82030384100d044c070402c04c0f0001942841030248503202c10a8001429010040d0f4603201601d1500d10f00319410060046842e46035a600009100b4005030140b6110038034400c0c04200d00ba2411158000108281c408010441042a0390100c0c80108001d44084250141c1d0b843c4142c3d000c06114403400c4254209000601c0107043c0101860381c0002103035403220000b1807603107845080092114a03030b40600e4031294a12078103044aa106a00840381d40018800d01c0001c0314002c0d265000090300405185100000781400d010382e40581d00861051280303555580c0da104801e8008203145460640641200c1490445038544400b0590045401c608074502d8041440340445000005402041c4d10401a0000a140000c24070103080130b4044640c0010300d90711409564500650001c041404000c0744000708039a180d40480468140c0390301c02010b072200d10543c07410060f2124940c100101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 354597652 1250 354596402 354596423
    0x909020d02131406030118020d0f0e25060c0f0203060702160906030b070f020a05010e0a0c0f050a050d06060e070509040e06060901120f060c210209090609090a 70
    0x850356039000300701e00e003151011400c034190307602001e140392856018415030214050004004440740d0703550351001e80030080c20042c5440c50340740d800c10803120000e00d09003400d6552030784005602c0040011490b841109885041d2600c0c0484807000c459115000300c604200107032004030104844001c0c1d412142c1e6008043d07aa00d1714056034001d580c2d0800155114014100c501300061240b480d00c2100d0a0f03075003184003045642e88100064480000d0711183c84118812142d902c004101c00707109810300040c0030f001038100c00c6000d00b002c0d0ba000da00c9030481202c0050f111030400c960b0b0b40704403003601250010781d81c420492001d0f0400034014071182d40030b00070072046003042280a035030081c010101000210380c100250030300c00b1200c0340e075410202c0341035401c008030344011300254803420341440c0c6c0c0d00c1c881c2404d100c2c1423400d559440262040340b5050300104151401c4203609006000d1201c501d601901000c50610300030000042c0b070540080d0407a80141814001304240b10014002e542050350400288070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 354598902 1250 354597652 354597667
    0x303010335190e1804031202030606040e18011103060301062705060d0c0603050a050a05040c05061e0d050a0b03030705030301030b060f03010c0e0f0f010504171905010f050705071a07090902 83
    0x40071030441c5c0c2100025207040c28042c20742403500c2030700e01840000d021181020b042084122030000041c0c18140d1844204c00f01c0c4e44000000d016001103c604500400e03100c2c181b5005050940d00503811143c20380f480c0803600718405001002449114121210220f038980720800801c0c1004080324000e00070586004003c6030480c1c064010b2401801d5030002040703e84e41e482c00013403c8440561b0010201c1200801c01c010384d1421801802c14503c43d0180003002c9400c942000313580d0361246d21240f590944070000c2114901c8a0710440c489440107802a61412403075690b065140d22050100030312010001001c0740140c1c0300c0440d41900703148050000c202800440b0360152502500220442c412201ca2041d05464244610401c0411700180c541600f06404e1804000e0f00c00c9a688031003280c2d12429540101000401c0300c2c0011070360280d0000540c290341d0b404d14000381c820081014061140c10800c802c0011104000c40d48214908445080740d9108c07548c048801c0c2d0060340c0103104050003c00c030078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 354600152 1250 354598902 354598939
    0x308120a090c0e0906060108060f090601020118202e0c0b0901140a020c0703110301090204051003140c130c0903170c01140106081f05030303010335190e 67
    0x49004d86941800c840340b5585110044070056000c43e0040e8000d40d0f0341000c600c1c54100380c0341844d00120b05000211f0f1039046103481c015008816031041c1c03008054507000c6400207850000903580448181d8407040061448000808030780d000421034000402a00c42424280b8428440405450381c0000340c401942444041c0c98080c06400c2003240b4400c0d540c4001c42d4040100384210b6241d134407074101500e002461904e640c145540b41d40308040c1c15540303c00f08070005981c0d5204240c49078980341400d840440c150700f000304200460202c1001d195021110101050307803480d4042a650201150100c0c03920b84100c0708648c101c81175800100b80f5069075803075505c08a2207201810704000e207035008204517a1141080e4411600a00c03403500440c2081d40030441081003251a070441480542c3e81c24041603540001c02d1039039000341d00641d0242400e1a260002001c21501d456a8a1080c2c01062a07420760340400907641c45030240144404602d03000e045403403405218004000d42004003030003181041c85c40f80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 354601402 1250 354600152 354600179
    0x80909130b0103061b030c12020a112409060103020f120a0c14030c1522080703080d0606020a020a29030405030a2703080a0926160308120a090c 63
    0x404c017078840448805078500c03a200e040352514035650382c0340d010b80107071b201d504c020340c030040c0c255040003000d62036000700303207800c00014980d00c1c0c0c0c40014482c547c4401202111240000d0484182900b01900400140c0d4909502103c079080072030f00c0d0401c89484c0980303146003200c00c59009100401068001581d4401c00101141d625000e40076031750044410410000c84401002c0c0d4004454030a000d54512608400d420103804120718052080180c1c4401000b80381200340da104840001c2c00003940d05901e03500340501c10040c141800207011840c100c3d03000882080460080901c0c0d02001c51400c464010000303a0040c00c0d10280041545c2c1c0d05060411507100d40c041d85200300851001d4101c0308018262052403003060100702030244516045a50303491190b40b246146c4410000c04240c045035040482403108989100d500c59983d0885074056540e08040c4011070313940c040e40b14207108202188850301240c0da1106903100001c11643e548859000619030180c0107003804c5000580071030510b000c00701d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 354602652 1250 354601402 354601421
    0x20c0a0f030206060d0305030c030603010e150703060902161203290a060f0906140d06060804060605041a040902150c03030106110105100b03100e0a1d0307080909130b010306 76
    0xf900c0c9165200c43c14880308412034000200003038002c200050002400c0b0380599000304000300040341e90b01545800764035104407003540151840d00b802c1480703100b54041c41000e00038400d4400560401d0b402c074801c2004204d40d080040c0c03c855120f001100d0043c0b01c4c1c0d01c00c2516244d00896488851a041e8000c0c0c007215590481078050320302c804000c6180d80c0902e4801182e00d06545d00d0250240c14148121000c00805244075403110090151082800c440d00540c40074054070b40e141091403501f030400509440d01640224002e1f0702e4001c41d96560148140d014020042c20385004c0382150720351010070901c0b4490101d040c2c84580104013a80c070b498000c4000c5040f00c03255601c40c4003002c01441c4080c2224402c2d80c91002c002001c001c10805030494001550303200700c031051401c81c2c00d5510314005407182821a20100c13401d51342c0600390403400310110342c40c402429010045081201c00d039220310303e034422000e80a12901d9014000340440c0f00030f030021000690300c003a20580d103595034640900a000d070600c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 354603902 1250 354602652 354602657
    0xa030b09091e01020c0706050706020c060f041a01032d291503060106030e030d050a06090c020304030b371505030303100303051305060f040602010605180c0d020c0a0f03 74
    0x1001046800414000c0e030f0325011540c1c01400001d403501c20300f680d23294401042100c001da024444004005418000a48600d507100d248200c646840e00d0081044034004004040ca800c4580050011414150030340c078451704038108000c0064110b903008890003039690300080c8040c0b4409280090700b00c03204064414420701d485041c52035150b21101030502c0300c0104841d03030140d110200410400b031083c5c000074030304060441501d181030281c444200907641c003150028031958884070104400c1a5500c81e0307613051074652001c0c50400c0d003150303039207030700c0410180030303420850f9080345d9441c200900c406001200b0380e4640341076051891f1540181c00907051200b40600e001c03410f00030005007803c0100480c0d2050440f00303181141703e400c44d507066400d070b04549106a1040310b03807280410b2603120b02008041141a0781c0316141c88529045009003501c2e11900a03071b01611401d500180c02d07030705a1003000c1d00b000500c00704603121554040e940e0000d0045103855a0284200071941090150004090541c58041d0317 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 354605152 1250 354603902 354603943
    0x30f03020f0912101523040605040c0206010f080f060a0b04110406090f050a0501120929042102030d0504050a08120609071b230105010605130602210a030b0909 70
    0xa260410b0003000300e100da6a46c0303a207140d1140200b10203125050789480002400000c403241c961021a04454004003400e000d42d00800040c04010070604110005000480080018400c0d10002644414024003031a420a40b0350181c890b95603601d420a042c08280145016111903a40c1c40040581c882071042038405490120b011031181440c0315510151441a1508020b400194840c10000c2c40d1403d816185c00c4154500890b035005007082d0014182c107030b0b014480b0641843d0401d42060004040821b107800d40390000400540e03008020f46204521400300010181d9031810882d0406d040b40c00000e2080d01c1c0060400c00c004505584103000e40019100030440790b8503030340241d408110541080521070024003e8800054240c01d074807101d0541403506004028403c58001d081d14003e80089c40401e1780030030840302d826000c008001c000d00661005001c1d690303581c2d4034990103d4084454480c8a0700004003000d040f8082d0308240301421000c0d05907087c1e8540010b03d1502d50761070070701012178200300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 354606402 1250 354605152 354605171
    0x40f020c160e060904150b0a120501060e0403090608180102030403050a0815060f090114030a360b060609030a0b09120403080a030506190311010801060c030f03020f091210 75
    0x410714120b2080d00003505030845911030303481b90300c24640030703100111300c0759190f4000b14002e4a40b4001b0034002c080b0400407100740922458090b09540c0540c001d111041e00c9c007003c01010980c450219421507030b150421a00980b9960315a84841e00c0e094544951980001700348010590b1220003050b400c5203658030405c10b515205441040001901c0ca8281d00140c244a40c0ea0850040c0008082c480014100401c0078080c4a202c805260011198015215911112240c41b04c011111580d0309041e0b00424900001c40d41e241c9406520721401c003d841304001c800040c10369128401142c900d41d0006088813900c1040f45000007403050104d600c0c2c007190144685043c08003420509a03400e81e03070302012490401e00c1e2510102c00a2500800803607100b00310030004c000c0c648410038000003441c060a030100d0000007180015001000691005040201110002c4e01103640301c0d10110b14803103e850056500c10a100500315540110f01361644e02109403115608042c00024696081440d0303401c088c4107007901c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 354607652 1250 354606402 354606419
    0x70b090c0a0302040f020702091333022104051b03070501140f04030f12090509060f0d052419091509080d05093403080702040f020c16 59
    0x8403501000e80240e5201000c1c4010314254001091710302800c42e005007070a030345400082500c1000d8408500f06080c803017242050004140c0718400412505490343d100660401400749400309041c03580051640c085040521041041000021f20b00740c0c0b000c2d0134560a0501304191070f01c3d100d842c0c80e0940c508000300d0a9460801081100072a04142c46018070818049034485da55440741000120326a81000040005460304294596003406941c2c02e82012001e43c402500d8050382c2d0700100d02c034290000810446a4882c99800b4481500b41c1d03480d80e41a0321894100e02d40125042c10400c04030044034150700105003004d6040c03140003c0c160401aa41c201101001101d07580d0101a060001c0350b061020126890317000080384500c80c0b040d16261511940c00042101e0040d6a924103640042c101c074480e510602c001e80040d005122402041c545407000e50000c0101507210003000500007251103000d66845074805402c02c4021031065550310b581c8a02daa468510101c03152020b0380030080302041010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 354608902 1250 354607652 354607663
    0xc010206090a031103120112060c05040e0a09150c1824050a091d15040e0c010e030c03010212060a060908030d02090303070c0b1b010e0c100207030c030305070b09 71
    0x15150805010607560b02e4034101d03140c0c400504042c02d5848100194006c0c80700b0001100d008090900c420004e5a00c6842c0c1385090f030316909032401c1005024803042c01014003864020360041d015410000f017280c0a8507195128422031011204e07071600e81a130300000700f604915a44181010380220b0303010a034503598003805c0040c0c4ca0a6046e0240010400f014919004078002d0146501509110b07450700d07076840480102600000080038007044903402d00045402d210201d40c3e94030000c407000d000c0403400d00704480e0750b00c041547c594104549000c0c01409030301c00b0700c0024031541001c2e000350b6940c2c4101c490000c2d664400d0356114000c00030034100003071aa1250b0401c800759407160700554a020804105030011350001e0100941c1404208800e50004401c001c050005128420010b5151069092680101d01c5080d1020341142d0424144107404100070412000d140f0080391389100603096420300302d00d4400307a900002c1c1041200240803081c0750300b10b80a00441031103078103040303070554030b01517514ac840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 354610152 1250 354608902 354608911
    0x30a050d211b05030403110a061a06310b0c24070503150a0806040b07030f1503081815030103110d031e03150e040203010b06070206070807020d0f03020f0c010206 71
    0x5010001d8a680b41c00c1c420001190058028a00b0f03a2060017045601d60811502d44811075506950354007180d40d281901401e4001c0b2a011203100b428068003046242d400305807403068070039407280e0324005180c0c010940c0c01c040281c0000e80720103444240c50044603503981c070701400201c0003500019405900c000c0c02041c19200b460b0319034540d0704680710301c5000301001d0207401c201540550340e8000440d01c42e4041150034403403400349103005058202010080d044882000e81540701c141000084462007010141403012603a0009042d555007099011f51011442420300b86544078204c003118841d11003002c00910f05aa001d041344414000c0c40c8010002e8010341c928004011030605584a05600d400040030301c24544076041c0483c0c605918003a0745240c50f200d400c02054110500c00340010344c10309200d14901c540d4161441443d100041c1c00080050081c40c10040580b800001e100c0219158080712a6055500100ea040c0303004640c60080d4481c41170382813440a504c10205810399540c40058954080e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 354611402 1250 354610152 354610181
    0x2070c1a041d09120d050703051b07110a03050102071209050105030613020c1c0f080c07112107270911060711030f0d0807030c0905010e030a050d21 65
    0x102c00510900c9a8400030007030002400d0b001d0394145200701c6007203000400083d0401c2400081c1484e15120180841e24090012a0088071895410302046000b2084611158000d03910344541440307100010340c910480e0700024559400421403204012650854a810104544075007485c240c40c0e02c0119514001100d00f1544000091014254499a17900604000045100b07540203000c03da6401c103041d805074088840040c507400e000300b5000e03500501141d00201d01e540171a291954640b603070151121041c59141c811000e00090103050f41100315400741c3c14107500c00341e5180d641c2d90300520300c002406088003100115084000c00405001d4480e4180b0307681e0160790b10b18612405010300c040b541201200b124049c0c00e07120100400e980401071102101001c1c0010510044062030040902401905030401e02d820042004100c9800401c1041600d0f4280380202c1c26500c0c0d05c00003454800d4200c0050424014000d000d13100076403021151054640400700c44e2a0101008034000c101e8680422003c607 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 354612652 1250 354611402 354611429
    0x215130314090a030b071b08030f27011d0109021e0a09062301020a050c090703020d021603020f0d02070e130209070c051c0e01030c02010f02070c1a04 66
    0x2030055011008100a200c2880c2c104094103011859000840e08141d03030075070645080200c8240c4c40700b240c40001481d4402c40c40d0b4500b55a640229502001e44a210003030b010100140b0314034085000c0e1080049000c449040c900b0020b00d03140e001b880c8682c1c0480390603084900203020900d05004001f1601da02802c1401c03440342c0380386a12001b49090850310341c0311100a40024800e200360141c6000341c00d080e010080c160781010540e85407030031543d5400e41550041c030310300d0300844c20106455030b803088192121101d551784c02404a00074480c051407072048601c00b01d124440e11200040741c0116607c66000c840c40c914605004542c2c80c0401d90141d00180c6c4120b0080c06081010300c28150130143d070700701c0c6c000388001550004150781c40440e615000591140040700c18024200010b5500c5240d1000442d1f201c400c1100003402a8518000345050540310100141c00c43d01c03d522824000328819002c549802c80c170b25090300d18100310300c11400e00b00408141c5c0b0048402d4202120202c6210522802 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 354613902 1250 354612652 354612691
    0x50108160b0304061e0e0106081005090a0f020f060703030b0a0e01230f0901080607030609020a1b02030f1207020a0b04051c06140a09021807120e010b030f0109030215 73
    0x1000362905c86818035038038800d008038180c1014a4000d05003c0c407120800401c0d0700341400041483e22518941444000e420101071110b201c4010400494041e04080800c0101c0e8580c004102c240c2607124001d034125100040b00740526903d903010f00b8082c07100302c504407891a60b8042c2c801e08050300b030003600e05800382c501440c0401030b028400c9d02c903010000303400240721390141c01c009030320207800740d1101025400c120300700951164188103500c094604144114140b8050610052401103941c44404c1840c241200c00d0742035640070080c003405402804200c400c00f05611000c0c41c02c81d04940402c0303001d1611580c0c041421a03501054030152100580284144148002505071240d2072181c140c0391566101400001b40d090386034414850145507170042145c030200c0c0b0500a600b030303030408824070b05920b113800c2c0103034158044003401201c040440041000c4c04050703400390050018802681e418414401c41c908151419000404054021f80903a4682070701420710026540c002c8072840ba103e40c8007d500c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 354615152 1250 354613902 354613913
    0x61b06060f0604060f02120a18060302040b0301050d1e080c0c0108040f020913061a01090b0c0606040203180106260706170c120a090b130804031115030703050108160b0304 75
    0x40340c5c214561046542c40e110300004c180385a0f00141d0044005208000c1d40c3d2440440c00c0b09080c028911391804614040c038204900c0018041801454071a034150300424003445290714110b422550300300c0c0076007044400e9103481a8190f100741e8000e40c0703e010710850040e41c0d40c050700300d043c49590041000e00ca40284c035030800c00e42450003002059440042103405010407614400d00740c2a82034030a17050700c00201c000000d03003030142681c0f101420040c00c1003508125600481c8941d000b4405480240c1c4980f6411224003001d0405100c05a141d03181c0440025280b05c1f03081c401e022051f1122442d90000001031100762104c0c0140144070105422809141c0e01601c1000c501c2e82c40903050003050700301102c040290704090300c290b03688004151140041c4081c408501e1540380c0084030741d1251103041150f66038100d6640243c0c4800b5200c2a0340c5940b04400d51542c06041401e200e08604e482e64918140d0b1015000b080280546805841256000d0703080000f41c0001c2c5051b552003110407400c503603455581 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 354616402 1250 354615152 354615167
    0x1030b0702120a020d181401030507020f0d080a060905010806040b102411071211040f0c090e0901020913020d27030e0307060507020112020702061b06060f060406 71
    0x120401c61040802d41035600c0411800741c88504582c4c0c0c0602041d10607042d0040001c0521600f00d425140d021004100c801d5407065032030705c000000c0c200402c0c00e0b52110310607800d203100100401a5801460707802d03803038070354410b41044c85125000d204121060b240c00342241200c43c2409201850b034085d101050100b46280900d940c46512042070410868441100d001c800c3c105042c0c000310064a105a91001d9800c00307400110f6001c4800201856490100c480101e450300300f002400e00001a0300504023511030b6008500c0507880000e06005005190000400b0250307588100c9007403240c040049000240103000702c0c2c000500051425032012244805076000358030400580025642d100101c5141501250544d88100c3d00401e10101103034441c140600440d00c5140168401d8124003c10300019411000341c5803590f8081ca085480f034174a1203400d40c000c2c0700c0c09601a51000010880040c444400480401a40c01081c00c6d5002c0703072104024004000200581180d200f103090009000e1988241032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 354617652 1250 354616402 354616411
    0x309120a0803010b130305190605160207050d0201111203160e1003020c01020d060311030c040501050901030f051203160e010503040308040611091302070b0c0309070303030f021c05040b010b04080601030b 89
    0x729000103541d0351f40701c03442c04413081d40302000c0d1000c08100708280401445201d0b0700101c14000d01842c090103e000a4a0f41881d0084a20500c03040d101d11042d64400c41c3e032004810b02d088101c2d06030312458400002160822209a400c0c0d200c48400c1d00c41c3e161242e00e030001840e502400d042c001d42c0e500385054001e5003008019402543d428802110300d4003060043c1401507015220005003c0420f8060504208036100510b00903410b01004010988800404604590b00000014a801c199140003400c0003940c3d0512030302c0c400048203018508a0300c04211488e6000303a1601c07036134076451100540f4070b8081118040d0106083c05d00103001300c0e525400c080348090181d9002440c180c903490000b80c5048049680c492000d501268810030085014105600f01002901c16402d51401e008038603940c1c0510700005041503168100c9582d015200c1d0152013241c1c0100390610a0003100b0494540180170480d03041d250a00c4500000844c0024001154251011040078245e42da00f0b50f1240c40320080040c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 354618902 1250 354617652 354617677
    0x80d09090c140a090504050c0903101512030207060f1403040f0c05181f03021f0c0c090203070e04020a2a060513060f14060d1505090309120a0803010b 66
    0x8014549040003680204034100c0c0382d4460b10000d501704402d2008590b002480e002c0340b00000c114041036980d00188041140c034011001245146a6010f0206031441e55402000c0d1079101d40080010950003144070300640b506980c82d221196003010b012141241c4140a8414a52040010501007140003002003101c600807400140c0c80c558440c00f04040103004110b170750340a6402d0007800b032012401c900c60488051207401c104441800c0d03400080e8030305c4071000e400c50400ca00c0712a80c580c2500400111845941040a401e039003030f62846900701940c003c130342c1000090b004051001040c5080d02c00c0e01c09240c0c4580d00c40042c010030325212401076403081d264103030500c201440a80010418010144070f000714200c410010102c6180000035101c1c1c0d544c81c5c2c21401d0134a0a95a4441e0811400075070140045801250320001814000d00b0308030801590940340b41000c00300001c00030000002c001907003099507a11000c403201c44115480d10480b50006181600400040000e2100040900021304a80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 354620152 1250 354618902 354618917
    0x70c0506091206070c020f0927010f050f0a0b031204120c0b0c0a020a09050c0702060a0c0b04060b010f0c0210030b031e070303030506010c020f060f16110a080d09090c 73
    0x100b162810000701d800200240c050071083c4118108407100045400064800d9178060900c0c4100c3c064100200c0d2a004c2e51130218400c4007010348094001824000400c0810402400c00d000703c603000e820119250b403210303030400c851001c240c20009075186201c901482000d051509080304234001c010216010f440180b208a03000c20500700102c010410940800000d01c2002c0c218410301c9050f0302c0a030300074441c0d145000200400298a00d084411403a41203e080c1d5850802c103805441c43e188050011700040c0110040108002066006401d220f0098031025107520080900b21091070030840000d420140b8070300780008007402908401076501c001001e031195480400320291142d24101b24101680d0f110f00e50410500d80c062040c9a0018028a0315400e40d113100e03000702e00c645c210091261300489000411400344030b0900103a661001d03680c0c803400c1a0550b039041a0300c0f090503400303906200d000790440000b501c0c84005200384142005498400c01207180400d070034014883c000b0800d09000b5030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 354621402 1250 354620152 354620179
    0x5070e09010f030b0709060f0e010309061e0e0318130e030d15050103020301050d0b04050c0d051005091c080601210c0e0102120403020910080d05070b0c070c050609 72
    0xd680d0114060040740700366030070503440d60504450440c40505038409002c02d031042800241d6015510085003c00303410604080006a40100e00800314500050002c6103015001448890004d00c0802c1c3d02e00f502400b4032a107c02401116106d1107200706107443c901081303540030b640c0d05010f00302013410458094002032404540040906603409485081e076015a40e0880b04c07100c001910081014003000e2808505641c106030200c0c0c0124000d44010b405000c69200040801078100141c0b02500c0d009812148c0644144c507009980d1a807600d4042200b070300307100015010800004480d801c1489000803d518040c080d10260340c4840081c01c0f0030f0400403003011011a01c5e5080c4240c1c101b50000c51030004206646c550b0040c80c50200000007411900680d56103600314010005882c10740b501280e021013191101c11696818080c6036120803183d00503d4000c641e0780ea0418040d00d9000e0140c1090803103aa2041d0380480c00744a008030050002d000b04000340142d0030b01001030201c13090007400c810342c074a81 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 354622652 1250 354621402 354621409
    0x423060303070c26060f06060319060f052b02090403050904140702010c090305061f08070603090201080a060e0a091a10050a0614030109110409020304080703110a11010305070e 77
    0x12900003c00710f00c0c86042007404d1480110f5406110201400644880d040c0010055030400300500903a00c540b13004408256a201a8145454084d0360f501b02008810740d241e2000c003c0d00c113076228141c0f1035880d00c41c0080b481103841c808031241441700340982c4120003080c1d0811211a001910a40800c44140560314031a2a03d20443d48105030040340002d1914001e2002425601c02161900030844e03803407020000101e0004019400003d107002240100d01e020990502082c9550b10148080c415800c0c0024003030b403d03907c1000603034001e80c2c40103e95510303070786003606440403031081d80007070408400010042e030300395031210510502c10b0380803c0c105032110000b4044041700351803040b20180cac0b0100420081c600b01944d2001041c1a0510580a40304006c1450050005215200b2a640c54500114501e200001101d0140203044c034115104e0926080205854202c41c4c000c03404a410364481c02440360700001e1070804590b2040c900c85440c81c0e280011000380001030024410710580c0716101d000b80d513 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 354623902 1250 354622652 354622673
    0xa060903090b040b040509061f050d1401030b011509060e060f0d050406050a20040306050601020a02060c0102030901060b07110f010e1c3c1a13020f042306030307 71
    0x4c0014400c5455071300301403c0004025000d03210301d21480c50400b403002030100045008048104508002c0e0700d854820617200003412006c804201d000c8011800070042204441c2594141d0b0702d013480c0400c088201510070395009138a4052a0301151102050030005d10742240244411490b1500d802d080c100e418015201362002030314112207ea1700c52007001a85607070341c031030071036090202555484256841640c1191920550001030020750702e4000084203640200b0a8500303c5034090300c0141d407241070502c078a0003500140c0d2001410350801c440018a007501800b5100b04d030360840c003030b6100d10802a041001c3c0b403002c0300f01c1c0c905105c01800341003e02d40c1c8030210704803546d10710f0124604001640c03820310350509000305403c481c02640d0303011091080324545c080c14040f0060007400180081d0303082802030340500d400900e41da60501d40401180348042d000e10601d40f4400d403030718203e070001c071001c020946001c205011a4002c3c6811240c2e000107207c1c0d403154201001509132482c0152540b80c010075070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 354625152 1250 354623902 354623909
    0xb270c0d0c0c0203060705250503040b0708071106070c0902090d080a020a060f05040c18020c01020d06061701180c0e090103050d080108030f0d0e15010602060601021b030a060903090b04 81
    0x70b515810b10000d5043c02e1040790342c011b251b80381ca249084a102d81080342c8a2200d1146c80643c90a5040c00c000c00c41c0c10000c0781c003d045090001920b80084d8607201c00e00c2e40c42800c08481407407036082307104418146031041d20b808a50010304102c80c039042001b984000c0d0446003035103a0028141c0101070200301d80c1001000e8a4a4a6000e0b050b58901410070f2800d94110f00c07451403c544c034040420001c00e51908055061f1b42950303c910340d11611104519002e07006160113007425520000320302002040700e0f4405070454225440300b460140c4d1001c10074580703074402d200b0170380e40c0f100804002c00e4140003980031441140003820700d800310f5130002c0041071606800340c01c110b84640c0726940502005070082a22401080d191000b50310700100f04282900d90f001d00c100140e94240c40d0424030340d0810307042c08961000e003055142800709680d00c1c44001d607510002d079101c41c00760040001d441445840e42807400b80114020b0014501d20205a0b503107001000440c1041d0100b006030600440c200c0f4220b8000c0005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 354626402 1250 354625152 354625157
    0x19090501140102030c0714031002030f0727060f051201090e010b0a030323162f0a03080304020d05070b0a031a030613061e02030a0b270c0d0c 62
    0xa98104a081800c5248000455040d98014440c282c0d164400054400a413041203004034041c94444021900e0700148030200c200d480d0010003004644070b070106400c1d11490340ca03540c0350b0114000712425400d801640c001043c0e825002c1209000c218022123903030f01010303000d00d03100d0300d807444a040b480c111500a8003d8040c860b00d0b0720051110010902070a00501c00440300c23546210f20315030b00503200c0d8204a8441d22450072141d98201c0400d1031006544207401107583c4806610082c1ca0580074807050102ca12610714400002000384406e02500940c3d09803019051046190440d01d540980ba0402071040740d205190b041600001075060100000410074a580e1036100c1d04803000c06810394280c080811070400500c21450300c1a98001981c9030410042d41c0280801902c81c1042006802e00201a001c603d4906c141c116000f480c1e075000b180314510f0503404000ca115800c00b00100000c9a104c6102c410709800c1000840e403003451000c41d003264034034580601e8514520101030a031740c20403192401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 354627652 1250 354626402 354626411
    0x3062603041809060c0203270303040b041203080c0c03160203100606090303020c240313061a1905090610020a17030703050a0c02030f070302030d1a03100e0a020409021909 75
    0x3088500d0040011750180d500140d4140410205130300c03811700c103208002d414462003600041040c0c5091040b100504607001d10783e6662525540740200800e01000b044000941c0480040c450b100440142c032580c0d18681e020714584060950b4241080e8000c20702a40d00d4040c0c0201121102c0c030300d02c11300c801031150b0386400c0c030080c0c55418060b0510b401080ca00340210b1100038401c0c0501c5001001f1171802444800e00b1391281c072464861074107040d15080090040d4500504420315500d0082a030381408001c48410700540c51180b8200c442440c9849000d8105165801160281c9030008440700c900d6554411a0304181484d10342d20b400300004140000520400030603c880540d00d4041c5543c49000003000f8416101c03850b000966034440d0501c101c416000c041000010180700340b0032100180d590500602c58a1149400e009038168030b41a403074800e1182d803200c0c840098650207183c0140e0710480140880d241e031502840090541014201da020b541203144103054007221114102401c01c400c070008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 354628902 1250 354627652 354627671
    0x2304060f030c08060702070504091110050c07090207080a0e060706020304150e03070521070b0c04080705120a0f020a1d1503150c0a14070503090907030626030418 71
    0x18806059038000e20f242c2c2d0004020003000507000102201140c50654000510902c2420441052a040703c541a8070107050088204817550182c05070100116000035140051703030f520f2002d8100c2c491100300614562060008071641070003000030107980d40c409445c02d8508062943d800d0226030046074121030342c1140c03402000807500c03117200300340f032100c2404000c52500d40b841d110541d680005d41011141d00084400703012880c81c014090303812031507002400700d03503a0419060f840300c06e8000b8020f4284a105903800001d46181810307106811440d018040c2c0b100121603100c66881d075043c0c0f2016a00035648980c00150004070340f043c80b140e48c80088040306a030901008072a030a42c9660107807407003035001007445148281880035007504020320b081d5403655511102016039504805052404060b80081150400d2040120081445050803110141c0d2503940c03442c10b504590841c00741c41c0100700c441242c152281d0b1443e1006050030b80650880e4286a81c501c0c00384060f114210141411948a600c0310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 354630152 1250 354628902 354628913
    0x20a021f0f050309030318030f04090b030c030a0b0c0c011103010b0702120c0102191a01030308040b1e07030f0e1209190303020c0108071809090506090601030c2304060f03 75
    0x1903003010000d10b001859402c0c0802010b035a4040a401c5603000405944c9000304424208101c600e841140b4010588035a0794a600700e0040594119460083c003a280711a0014a2b01007074000c2241e6006030301403919103d1240b41e641a4000110840896594030040c2507500404000340d0700a04025507540e075a0740403441401000c2e803002045051a0348040103910060380c021403400e542036803c03041d0b442c48408034142142c0038000341403841030a210b040008800d255000c00b2803131140340540c140d00d01540740d5801000c8800c010001403a82100c1810218004c94840d411040c0362019003040452000ca101004a00b0103106456444003544d00007809103181c142099003a806100c0750346d60040382e910315100a515002c1c0715a01c981080355010004000714060701f40d030020428030800640c940c0d40c440e0450001814418401c1d6894402c3c0c8001596410000030914140e99101c2d00c2a00345500d41034203402d40c08003840f0f164080c03c44644c5002c41d5a100c0d4840d09006060a0044048040c03031030501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 354631402 1250 354630152 354630167
    0xa11030f07060f03180b090706111501150203071a06040e0105060f0603060310090317012301030507053f010b0f0901050d150602010b03030703020a1101020a021f 71
    0x2408141c0d00400010005550400d5003284103800a04005c5202c0c02c028036200c5d40810141ea0082c41c40c0038000a000082400166810030744406468821180d50381e602c005a8071107a25003280f0381220786d00010300c50207180c0034501104074441c0c01242e051031290b50f6100013104140c910001390301c48140800040d8a014000c420340205290001c005d2410b0402c0419508051a000d2a0113a04000003042050700c0c100402912202001d004114140b5280f03001003d01d609103440742c0c1144ca00400104060044e08903012018440d8001c00c50340c4042d00c00103402928006000c071040c0241844540780d1340d100c0c038103804481303003943d6840b03c0760303074a112503e45580300c11001c10700c00c64850f100140080e061a00403504810128441d4507240c10040004850034410b43c1400c442032402c8c40d025888038041680c1c07000c16101c20303400034469900c41100b415943d00501c00040c0050340060860385c0421415100000481c0042c8152850300100d90045070900450302c00885000c09100092004158440e40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 354632652 1250 354631402 354631423
    0xd1202070503251a0103020109090b030c0904051e10110c030d0e0109020a0b1b0f19050a0803010605070606091104050f2404090609090c060809030403050a1103 70
    0x1141815038548416990707018000c10b519030120b8011442001e10601000c4103031065008a890300e024580c00d85103143d2000a100481c003003108404003160002c403c0c01500c40d4001c014005260701e0314103004004041c0d40240050301d050041c00f00d8180c003d031105d080d003904002201e0007001c01c42c203100024021a82008041541244144550f01003c400801101c032290740d42c11000c1009160800c1440c014801c2850007075014414903c00111100c051000d455541050500d81200884000380300340c03580c08000e080242c5030800489500381d00242c5003c40101c5000b5021900c214040d40d81d4005203a100780c000402040c004034868041040b540100c4014100c100c1003408401440c2c206036245004602420744101084046250207890321042c1048044626503650114610610240c020390300500800300c000e42070500105d00c12075a8010728080e01e620940842d8510320b041e00889206002510128042c0020040000419010060b11001c00c3c060b02000d11a06002c1040516219032280e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 354633902 1250 354632652 354632687
    0x12050901171005120f011802010e150a0c0f020d0b040c0603090305091314010b090a060c0209011707030501050c030a0b10081602010624090618140f060304050d 70
    0x41040050b10a49181d00101d583c02d40c0c200e05503c0e80e162031181440400401c0c590340e98030704041000c882c1d03042c0c246020414001c0c0c1704c10040882d614113100c8100c02640c1c492040381d5003085500c6c0c8551142c051600311500603100c030f5440e9803656001400b002c03440348098880c0042c0c1800e2106006801d116100141034500b42044190115a0003038407601859280501c1100020000409140f90340c104c0d82c4410300040e1500b10a603100c814061494000502c0da50103018420404109a802207e81d0842c244c2c000b44141c45c0b036843c03e80c410050b0b44007260200c0540c020802d00000013102409601d000302c800300c5809440745403800110085440c4581c0c1c45110341c0d120194040903a4002c0c03a000c0e013140902c8410884101c1500e02030307024011941c003200c58058124800c0f40039803101da69100c039074000c66039501f40c411350b40c5000300c546400000120b031904150340c0c02040035500f003000b18008a24042e003130a47c000e8028001540c0354004441c1a156900202250044113500c00c2608814001c000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 354635152 1250 354633902 354633947
    0x709240b0403150209040b03010c020a140f0604060c090e0a060e070509014509050105010509060d09032c030d021c0806060c01110406180303050f090d12050901 70
    0x191a00f041c0c481004044543d803e038006650201c0791600c1e04440680407000d4000d01c90a03801500084d50f5000b20f00c1e080e02e03285d0054142d180c200d4000704a0500c45442740004006c5070301c0f16140e12000b4400140300c070003409220b5400040c810100d03150b4038450300d001140051894a4002403054038100101004204a400c02600c0743e0340e07070485002500d20500c200b40440f80a54002040c00311b068482c100f08040c15000051200301008007503501c21f513a26210144100e0340d8440c0150380c20f009088009901c00f10038000711003038440507407040346c2050080c50304001d181071001d05004a40f6407140120300040b01d0b81c10045690074108442c480c6480684000c040703100c00b40300310420300600079607180104420900841c6c031541c1d0b80c5040d41d0404540d40020001e070200814600c40561240c85880d01113802648a10600100c0c644140100c82d00341e100c00385032040740c1514070f03896030010004585c03100300300c8520790100c0d80b0500d41c2c0341c02c504640c8680b0341e10b5001c04005000030401c10f5004104007643c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 354636402 1250 354635152 354635159
    0xe070503040803040512180f0306040b040b1f06090501110c0f0409080702060f04060212040b0a0522090218040209101407051525020c010f020709240b04 67
    0x2201c1c0e115401c111425100c0d1140d00d485814000c1240c0c0480600101040454420307040c454881000c0c8001c85010588070600000d05031200d80864018000080c42e02c006408100c020828507070041809c640f14400131141c81d00f0301401461a04039900083c0b01000920030381d41c00418a0758404140401048902110000500d60b80c101c03803400f502642d15800290204a8442c081e81c0819500801068480c0c410380109821a00b00e4400c840040c801c5104030b1008604450459041e80e0b58400380c0d5140c400c40c40340654940e4003603a6000b103071001c10058000d103c1c20020018018020141000d655400e0074012001000008012244a2403040254071842da940200c20f80e05528a030070b01c07101d0803014114014243c09140d0300904140145401c85880c0d0f10a414035501c121100ea1660200c0046c503511b88101010407144c40d070150b40141d200021660203a541300d25a10900d104590070142c66100d81000c0d5075880401c1d0341090b0103c031050114a0401d0143c101610103140054182440e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 354637652 1250 354636402 354636407
    0x130303020703151404060b04060503100902100f0206060415030219090f0e07050f060403150506040c030c080403200102070506010513110a031e0608101407090501080c0706060b03100e07 81
    0x4c05080240700955480200107a40c5454011000508000742583c0140b203000c142d6001070840350a00320b10682e00380d508440e08601803002c221091080e03034000c24103940c503807091200520b205c602400041840400c0040180c1d0313420300c010103881024500c00c1c1005c0c548081c24040c0c1d04a4811540d007203040030076010400c100001c1545c11140111048059040e410b030208607a8407581c1c0014051030742101d41080c281d040751701b040c0e005a506440c10440f1161041c402c8049501d40521000040e00607004100480d11a815000f0304000b000510f44040c0c2c0c8505030982207a000c500101c03941c0d0880780041101d8904001d40e040d2100070140305001e804104000c0031136902c40d040b109014140c1d228031034003042d80369074100959000306800800c4000c0c1c4540b18941c0d2111400014043c06041c411804280d0b20000b01060003030300940c0300c10352002c0c2007900654060200a010000050080c08510040781c0c907401640004c140380104036a90f810240248400031b0307901e8102c41e8a0002c84002d00400301c0d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 354638902 1250 354637652 354637691
    0x2100b010e09101a0705150609150a0b180909030426010e10060e1806010b090103020702100903211205180601080c010e0319030e0613030302070315 65
    0x20421201c149981d030f80c07410341c40d61030751a0390440d11310001900c0e030610b01c041c02c4034002c10708240164121034010707132440f41116000c003048031460303041225507010500c940c103500c000548480c8020710420045403101d11b403030389641202c201c00903500794605912041d070038100351081d04051031101440c40e00d402c0a0a80b0109800c84c5c0300c81413003c070382c060106540c42c1e0a40c010001940b908059618104507100502e0260449004a141404020010480d420b0184d011542120705880c017900e5184e1a0008d156459005204085e0503d9001c01c400701c0166a00c940203004005d054036145541c0c0c0c11404c180c2d0710b55206a940c030751110f0a10400d01d10040c2c0115252003450400140421580d4581c898541c902d0045851a10948101400801c8840d404681246808001c2ea43d070030000300d03460209659074043e584101c2503400010408404203220f04032902061401801503450075041d513030603034240d0b0180c0d44180e00580103502d06008200d4440c0032200d0000c84902d0502000c603c0090340504c16 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 354640152 1250 354638902 354638927
    0xf0e0310061e031a040201020a080307021f0b010e010e01170a090c120c030f15090605090d0905060f030709151d040218011107090e21130308070206090405090a0302100b01 75
    0x51340c07080020782160f10030081d4460139a40328405c1522030510b00000ba544401c2c03100e260100f070075044c1d034880002803d03200e119106c4105030f6500424001800040d2407003002c0a0300c03141040040c0440000c3c01d521241241d000300c01c90030b80007503044803034205500401740e1500700340a248801940300e004a0f040d0342c1418150b80d0480b00300b41440d082c40c9808050750001d82c04080c00c4900f0203c6036824000d0070f41c4414480c081980036514402c80007442260400094095264460014040403c51080c4079028640c03140440c18040b5010b52a03081105c00c907400d0540c44000100d1856440301013000d0741c414001a490107a4066091405580d44000b00c0b003031000741075041102181888119007801c010890092400c5001003004a180c01141c41e03c3e01901003902483c451b820000e541c104240500303d60003440d51240e2068a1419503075a001198004c06003a070303101380203110340034540d5507511649024400020061400c0e181600d0701908041303a001101401d00d1074030169420a0b600007480c035204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 354641402 1250 354640152 354640193
    0xc01090b0a02150906090729180409050303040c06090e040b13060501080109031e020d0503090109170703120b10200604080301030b0a060b0405010f0e0310061e03 71
    0x12201141000ca10308282440c402021803a07083c180704000801203034082c00b80d07103400c094814050300c40d08201e0a0003418030042c0503a0030b0786a284003028100070060300c0c1c4503054081c88a020a00c400c0045c040d00d80d442415500c5400c000207100810144c903508200404150400844043c030340042000356003001000a0b0040580c0300026080d00303042c541700e10a1a5101c041000156128800710380281302504049001c5203196600800c001200e032405050800030354002c0c26012090841105c0300c0d00090f11034003240d900c904145000520a0010100207806203c0f001d40b00e6082e8103000f08409243c0218000c960710f802e041c14a6912600c40f8444031400700d040044003125103845441030280d440700000081d000301c4080c07008010300200158100c038003c4101c103034103840d400f550340204c50f0300d03218101a90a0400c41000554010640c0031841542410201c030702d1180b0380b0210741465885091920384681d500401d1240313003011100c103070480752401d01c1c144d00c040c00d503500d6200001110428a49 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 354642652 1250 354641402 354641407
    0x2010915020109060e030c010605060f030a09020a080d08070815180c070c0902120609130308040f0b130c15080105040209040621020f010807050904150503030714010606020c01090b 79
    0x8500d03000350065a180d90340315000300991482204842d442e6041351320750720f00c81d5083c1400000c0328540301c8151940c140f19800560300e1500d50645074001446000007ca80244440000041102062009840c0c030003040e190f03c481460005c90092070000d00608000e002903c14001c2002c03622501c010f880050104801d080c001c1c0c071400c00d416264002e4000c0140b4450301e03810046078100c1190058110b410501c80c2c01a042d0303c0706130811112410845028079400344a0480f00042882200120342207402006050110001910b5410602c00229410075040a64000c884100040c000c010002407150302a40d00d0310100b8014000c2c4820018815188110f8010900c01e4842e40c4551242000780ba6502c0c0d016081c80c024502c07075595180c540c209a00c1620100d800301015401507040714411211543e40c2850503100c00104001004820608806510202d5000c1401d403020402820030900400711070004240c5905c13094251101908040c0464201c206903900c182d800001003c01c0d02c42c2104010b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 354643902 1250 354642652 354642689
    0x51507020a15061a0702090601030501031e02060906041706070f0f1805040c020607110303060a331107140a210501110304060b010806030c0607061e02120a0603020109 73
    0xb0103408503820020120f0000c0060341e02c01140200240100c500c00c3d11000b1042d42e950340107400300c41c005d01c0042c011001403040c4030f03400e0141c0b8030762480303032440184060708003c14a00450000c0e0807940003d29902034020b01034403586410814503034411204c1c900700550750800c810050102c0c0d0540449000d01007810400441803c03118a80c1000e020050700400890600e648025521070342615400b01003901c81e003201c011b0060120841c0c1c0b00740c00c0680000d214500c0d000300e0701c0340c650200303d08203114007050030b0395041410240b858034504003d50392018485071414120600b03120442e4401d8bd05001107104208450301c1340c0030808200d88404801170720042100b502911021312041c0010695480c1c40b412643d841c5104e005140154082c210801183c6200c0c00151540c81050750110761503807210149003007519114000b0038090748680f2000c12001070740155200e515050f030314030710710311900490000c407000210084c0039170041070403c09000d00380ca15000030f026440e150184050b180f5190000342e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 354645152 1250 354643902 354643943
    0x20c10051b030a0801140a05060f130609080c06041a1303051f0f05040b06091909050a030f08070c300306090c020102130e0a0608100207051507020a 65
    0x79900e04949900090003810500c24068490380060038007004250020000300d02c400100110102d00e08004c2c3c1300380304003420041000240d4020a0070380e0407410041101d10340c0a024004064000c080715207a824a60b403c0c01146814185040b42003405040300707110802008c682448c0a000d0741c02d5540c400c07582c1c3c0544c208240c00440b8680c0000c2c2c810300c01c22110000012803003a04201c1550083d108004260f0b07150351000a580040d14003504822082d004111240380108505400c62018403104c885918040d201c80c0550b82a034600f980c15400c100044e00170304da04204500c5030a625031410760602e1400142c09003c44071000c0015001c01325028000341d014088410301503112815240d0311004542c5100d004014050902469800d24140541004040d0050098800101502046c02601800d00e000c100844a0041401c5061030300d238040000c80d200d040c44058001c9001e1032000d652541e00707080c85880d001141c1a04e18040c01c1d20010810110b1f40411fa0f0710a65034001011a403412004241 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 354646402 1250 354645152 354645157
    0xf0c040207110f0409201503091b01030b22050c03010f060c05070509041104110408030a030f180f17160308070309233003040c03080d020a030f0b01020c1005 69
    0x1400c2001d41600d42204141540500700301c46c0e012a00d007140c520555054100c103001c140c07609002540a01c1107120702c941c00e8078010015050604d00001c0e080e5410380000d022400e0b1040c000c85c400c02d041031913900000f6034041c680c0d01880d0080800e00d035500d0004084002c400741c0c460b40d01001f541561600811405002010003000c00070300d000d03014101424000701d883c1010014611541c648001340c2c4175006000705807800c44107510051410315641c2c80080d800f81003400080440560781e004040e81e03c03608a801403a0380c40c028050310002d0b165518102201c025a55502941e015080c08140708034a509184201c803503a00d440c04458586480340103070050041c12400412400d500c000c1c4220807404041100454044981110100048050403202c0150302007030342d104c00c00c1e11754415104074034034800958100e44244407841e4003c0c0d503900d070840e440d0044c090701501103400064004c0099810b000b0310612440310300e0b00700f00000c10400040e5a03618059904c80c00352114039000ba0b100f5004609 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 354647652 1250 354646402 354646421
    0x30a020303370501080f060403141b070905160c0206030c0c0f070e09070f1a03040c0803030c070309061b060507200c032407141b0f0c040207110f04 65
    0x400803001c89103005507014010074082c1c49698030803418051030030040019064040c5415403544800925a012b0f20040d03035001c0c0d21511028202040881e031506400c01510000305141c010015550504031002c000b85007550003a0410840d0750038103800035a4681c41120340056902c0c0380b1964845514201c1400c00c6070309880302c040c5000c2e4000010789100c0301c2540c2403040140e070b000c0e80c4451392904481c20846109004e03410060400000e1985240021801980c000f4028081407882c3d035910705441e403960b44202c4480300345640c0401c001c420950405807a40282107281024256801c142d41c0c41a9030034001c01e009060382c1e88481c003160100303006820047c1c0c800700d0074084060060741003128582e00c240f00300d01071b8028820040060324031b000c3c0114442c030300e0381c0498826181c0c2c2c58410040b142440d00f0240e48881d03120400c50000c50600700c03c404088e0b10310b0b00001d4403001c640140c80d1414554002040c60040c1d004000b00300c00034220318203030289440b08440240912444c80c0108000788540721 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 354648902 1250 354647652 354647731
    0xf030709050301150f0b07080405040b03030c0601060507060623040b060d090605060901050d02090a050a0b10020f060c1809091501080604120f0c0227070306060e03030a020303 77
    0x1141c40700c1800040d51310b02c00383d4450386480800b890703481002d10007501ca2040c000e000810240420300c1145800c8d0444401e56400500711790410721290a00741c103000e820380c40000418000101c0314100040c50103080014900403000313a0840120a41a640d83c1a080035100d03c42ca40d1050a84016a107440556001c2c1003c5002040030304e00e90b01d480700050030300707858580c881d440a100020b600e00d0103050100c00140c2c0034002d0300c01922051160000342401600c080c10407030315280401055122000c00030700300320306680105481d001d06603400341801c1c4003a049552102c0100a025810700007501d1083c4d05040550744004559600c889007414203050409004c2915004400000c04a8000a079079004074003440c2100307441c00b00c0880580ea1076956542000100320300c04d407508094500b280c006809071080031554040c01494075441c51001000b22840300100c0e5486000b40201a8400c0070554444002c1c3c0056190501c0c1e44000703560b9001c001d0045690b0441490808940d50640188005104458 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 354650152 1250 354648902 354648911
    0x60804061b11070509040503070b090a050a080a03050603060907061d131b020d120914010906020a090602060f370903081f0e060613030b0906070f050f030709050301 72
    0x920000707100958a111040441c80f4048002c00c00d0b203040d002c2d5074007803644100118130b04444c0e13646d880403010009101400c5030040000920226509005038a0f4003480341d64025625a8048005800c44038060b102d14001d500c240b040100503200080e0340c0040c0c2c2d0f00e030b08201e07100d001688100c91544406168a0740c01c0321262400b00f000c2c08081d004001500e400703864035180d1800301142260769881d085100e0002403030f100c15018005240e5800b00c0307685070140403c0703911040840c21041c00d5606040084541c107a00107010b000d2944d10214403005070485200ce04114200b00181e501001070103081d02d00c0001c8a480c14500d00c0800c819030056140c41203c0f22003420b01106000401042d44c560103801003042c8200207016820302945900c203800200021b03020b2607041c1400c00038090002801c040d000b07141044482040074100183c4002140f1924140080d454a49030040c14039001400501c1801400f286880d40c0903085003e03100324510300141c05443c0c2d03070361400c2151088501e500882d01035180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 354651402 1250 354650152 354650201
    0x509031605060603010507050a0c0201050901030219180611060610020c030604080717040b071202120d05060312090102070e0910090312150602070311040b061201170c010906080406 79
    0x2156651283c0b0302100204480d9031041002c3e951803080054501c0000c0442c00c0c1200107600600180c10341c001c06144c01418205130311203140b583c0010820050103c0c1e4420020030844003500e054001400c101c5c6800809606480030384c541c2d5180140032584103807400e8510441c0c25100300008803000500604452850400e81044003070f0340c1c03000c2030564400310344004040399a0304201c210381c200c512800200d4030f000280e85511000e55a409910300843c01651180c1071030400b02e05c040c041c031800c000c0e0005100c0c188801010324003400c008254007031240520408081d680c01140c620200ea0080f0001e110b9a9500038003035080643d2517034100541843d100040061580c8a0440c03c900780f07950a0400030b180501c00d112141072100d21582c2c00690120409200046140d99200561480904080b076040c0b400b40000780303250003490940048100340d600412900444440040c40c817014a0050300700810003400003000854a030094070144002003010504000b010344c084d020b914a540c000381c3d000d082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 354652652 1250 354651402 354651413
    0xe040b0d1202070815161707170619030803250509040518070b1605011107031701030206030a020708190e01020c09091c05070c0608180a021305090316 66
    0x1100700861005216003540410b00000008265200c6445550030610320782e511141d10840815481c14a03040100800024043c0c803010444c06019800a4540300c0078110000c020480030340000b03241f20700c5154854030155803081e806070550300380c0e50800d06103562a62240c102c40031002c0000d1b0307400301c89440021201d01d21988078004e0440100102e60600942c2c42d98281203849070400411380000350041c110401c070140c06080104804c00308007546e140c1d180c0305521810708440c07815036200c0002390006400010598030400c0c6908103442c0c25255016941550080341040c04000c000078030443d070000e103440620a070307881561650814103045061454441d000100b040d080201180d01505c203c003010704003860910001031180441200600c40342101e07840d00c900340e05050684074207005003000158046445c1205c0a40030f82116140d6442500f040100d10740c900318428080d100a80107280a100180d40e401c02152150b4885400801c20380c8440c040c0608511500158450400000807000201302 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 354653902 1250 354652652 354652673
    0xe06030a02070c0b13092d0218150304170313020f040f0207060906060815040f0f05030d062105030d0903030f0c020c1008010321021006060c050c030706020d0e040b0d 73
    0x6c5009106114015417800035102010109046020140011364a0306a501c615405040199040382044800541303140c0420114100b02902d148885030000c01c20050100c040819160321000d038806914501d8540e90244049480b80070082c42035460030350302c09403603a81e50000440c14003e030508545e06c1c071451625070020700100c982102e00c02d00700000080d0710400484c80301e070071a820720003e110355944e83d0340d04195400400b808031450802d00c800704010900800141514075100f60300015000e040219610105650b0000510707145000c04441c0300240d404000d503070340749207540300110b100461450113030007404501d12011082487c00e43d8420f0820380c00958aa030102d4203540100549401c3c0e4811501e80c40f09000c09440600d809440e607070400020490041c05491070320651b6140165083c10380306803149507016200044800d0318a00a0100900252008d040308070010900303a8030380000a51076514030200f51040c40300c0103407c01202e4540c2e4004020356400103207c036140001c145030007100306 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 354655152 1250 354653902 354653909
    0xf0b0a030b0109121b1a0d0614010c060b030a140703110d0b04020d030c060203040b0405150f06130209030106080303070912030813030e040911010f0e06030a02070c0b13 74
    0x1d05000398500d15501401c603038801c0c1d40f40c83d003080b28240b0b502d403540152410040d40c1000c0101d03920740e00080c420744101c0800b04138841c21a202c1d903180d4070301e08128251861074111070602040300350281c2c4c05a80165030703445466400000030a41d01c10203800241040c504402c00740c1003280e40c40703815440c060040b942d6425a0301c07a400200b01003500e0310621814502c40d000043c03031004404c0114016181602c000c0c13000304d01c2840c2c03a100c004c04646d00c03141660010389017200d410811909003c1003120501c0700b003c1450788485004901e203465004c075070010348041d0149004120040d10003601036602d404071010000064001d200603a80c2c5c1003180d0380e0354000c46041c070004410300c02c0172918010490031942081c0e090340d104042500c90226400b644000340700e04038103010314483d48801075200c074014002d045000c0c0300d9413403105a0130b20000d032111012021103c1002400100d070341480da01c00060741d0300401007020041e1108030b94035202a02650941107842c5614000c5420407240301041c42941c2074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 354656402 1250 354655152 354655157
    0x9060f020115030303020310230f01020c030703060c0207080714090106020f030d020d0b180103050606060403200d05030d0e070b09061c112a150c130f0b0a 68
    0x11101215422070032242d200d844400704840aa204001091080d0065900421343d20501070007540c0c0c400c1d0314040784a400302014000e200b51030302c1d581c091910401d144c52500003030025110444030100060b8403030300c043c00300610b442d684485880c030b00c030b100300010805003480a0031160f05949458400c00360074a403807202480b0b0000c59001151241c8080b61941c81040309000450511a060702140c010b504001250806555504c0341083d03590348414150300655141443c2106950540c1045810b20750024281c6024100c100010000070f071070240d50800d0380d0804035524940150010005000d44800b10380901148030114000c90b425180d03901000c1d02d030380000700304c80c8407a50720841460203001d00710711241d2000d8240000c0a249806104030300d00080f00071000503440c10b5031500340f03003290080368010301d0030080a000d81038445e101204144040c8800b10061060281415021407020401800100c1544020400c014100305c010703100300c0a0001198004441070311400ca2049035004024003100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 354657652 1250 354656402 354656417
    0x40e0a0b010506210c0904060b03040606090b1302030903070b010e0f01081506040b01020a1401020703080f15150405040536100b0a09091b0605160f020d050a030906 72
    0x580340380a008a6580400c9043c40c9400c800314444d01046214000f040240c80450410207006181d4440c401e690140202904140e22400c00b4107010080710a20307080403000307510340400744171150b440190751580c00c40000300150f901e5031102c461508500a01000034030b030400c1c410011414038441c00c0b6581c41070000394100b4086a0740e501c2029510114042c141d4040d19204010523014200740d0001d94000340107004403600624155900036100202003103481050f540400c00d1410590301503601038201c40c0c0f03900300310080e007440c80d01c46040300003400b2194840c41451520800c0960003c1c266801408000c004000500d40103680011390000c090804a000840800c2c5038143c9210341004880a100d43e0001c06402e4a0388400e0f4004040b0803110300e50190059a0024400034039001f401c038201e00c80c0303824441c0912918002044200c054112b03405010341031005082c20100018030a8541e900540810011001400403800000158101402038050752914000340b44d08021a10100d405650307c415 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 354658902 1250 354657652 354657659
    0x60e0f010320280806010305090a050a2006071a10031407090b180103081308070b0a17070e0609040212070c200108010e0403021501061101110325030b040e0a0b01 71
    0x40e08460f080242d40c01164032072010070280e5109034842c6a0107440c500c1191911822900c1d594603141250104803000d24203003ea90003501d003d600080f115072004d507901801e06a055903140d80300780c480c071203800d2242c14890001d044400000400f0340110b400080c00341000c51058006a00c3d51080d0041400983c1001a00c000c5401c108450007214140d802d90010a071742180c0c2c1d030070303419404244810308d0030b100a50701080624041c000c0340020800d074003003d0703500c0a040c1c202030070a01a41d00030001440700da100304400b06030001c080c00d1107501c003103a8055a4108800004000703004540d5900701164652040100d02d41c1c11a0008002900541c588422000341e07003142d0410744407000c01280080c240c100100039103400001041d8100b48a0700594066500c950303800205804260300400000b02e203041c00e488450000c0c800da034024141c4503480c1d4035618103a0a02d147d003a0030300f41c11110380352190a546100070712a80c80744900c90401401800500f030720318869a07540700d4550007680d0505001c030000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 354660152 1250 354658902 354658957
    0xa030311070b060103110c030c071404060812070302070308070510050a0e0a0b04020406051c1205030c18010e10030902030c06070b040f060b0603161701060e0f010320 73
    0x11906950700c0a0b04031415602c0e4030045014141e000f15a1040b15020710071450704000600c054134882050800400d4a240307410a8030a21040c0622042d01070780c500401403080460108401c44001121802540d5850031460100c2c50060075600203400324102103000c4040200c0456004c01e802812030040c07103e500c803620002c08a41100702040b406074048000b40b070000f1852030b082503115000400008101e0781d02c0c404180d94520f00003100d078034107605901100401415201c4003161603241c6ca440760541c035103441c84000c0c521524488603000d40074111840c00d542c0c400c09103044051070251003031080d4480b03200060042c00503508120b101c0e01810016880500b00142540e20039a00801303d0074564031691140703640e6030140d803400d41c0c449458200724026610340320021409802c81c10444004660752200060001c8101d008024a181c416001000003540c00f14151007050011a410301c44001c00c040107a000340003009401150131003002c000219000540090f01c8140e55840007400740c3c10302036201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 354661402 1250 354660152 354660157
    0x5010807020d0207060e010e0301090b0403120c0822060c05030703060b030c1b0f0102031e0f0f071409040603060c03060e01030b01091a03030c07151b0b070c0f050a030311 75
    0x481e0041e8041101009103c2c400c4107103890b210b4043c1405029908d010b400f00382520003440c001d8940e01080d105002c200742d8844000021030088100400620764000b90082009a0250081c1020400b11716107801e2100d0f05014503a106a001a041024098000000c1c0450700221040c401192409030700103404015002101d1081c1100c581191800f07050440700702e030100055840d15202c0c40b030512030003440f000c00d00c004d60184400c04600180c8015400502d00400401010f0f40350f01581c036801e1040301150305448ea9082045c44c20858001b545c018903040c00d0f03000c0d00020715031082c00c0603800000e00500394024002182540d800740071903038a0b200300300d200130804c0c40000c049000441c0100050011a40549001510030880ca083c100e000c0002a15542002881d102203070490801000204800380e12844c104000d1b0800d0080e682480c800342070300100c000c00c0948241000380c0003a0085104107040b0107500e5000007280c0c036030810750400c1c03a039850801c102100464034092189603500d904605 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 354662652 1250 354661402 354661423
    0x114070212120109090c08070f1806061d01021903050301090509010e1f06030f030815040b0102030a0503090703080408030304031b120309020415091e0b0a030f0318030602040501080702 81
    0x182c0d6460b0108000003000310440581d982411054007280c494804d002c0d442c01800720040f02100d03d414054a00032842411100c407138a035140210400403560040ca1106108500300740d00703010119a000181d04121403204c200540c8010b0413102c00406400102860688a07903110030441503980038001e0342283e04000e81e41c602c55004c100e403440b0303904401c495142116407902e030218a0070f90b256a0300342080b0307005000320301262148007084040b42c0040101e8070000c0007200e080c8414088140007075240e2003020071038003c007c0000001114800c0802038400159401600560b40d40c0d5250f0901d03850703800070789003100028482000029034102003940f0802c4c85401051540c0000382c3d0001c160010301d44480100c0e003040d140c0036200000c1018010304002000b0882c8003044241440040080c0d40743c03044551007050380340698421550703c9105120303042d01e0f4840415140700d480d90600fa200c4201e800010b000400381d2441c084100811030f00070b44125030702a00d44c160f5239285c0040a98a4981049 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 354663902 1250 354662652 354662677
    0xc0501050f0127021e09040c1d150f030403020a0b1005010207090e0c030a050c2b021903050102160c05090415020307050f0d0507020d080f0a1d0114070212 68
    0x10001042c0b0800703801c28a0707110f11410040c135042101124402d14203004038000d40401000c55140b49600b40350003104038084042c03400000c003034540030401d100342c0242e07103005000390100020a010307080321600f204c54518450703825903140e14091500a540e072489800c02c44007480203401050f1801c182440030003c1c5da00c141c01402c42c0b0384c1056108401444440800c1c103152107240130000c0e039078505204c500701203400340007d070100103160000d10003941c03445903402464503e007004200555101000f1540d0031503049550402034040007210b181079811540018106510001310585150100e011003140188100d00003031031107075903004120b44590101d070f001c0e200d100a980c00b1030480d0041e0703000f55417210385404c1c44c1c0d0408484080401c9150460194003103910f0303030b40c0c061005554040107020401e880e689407402e028038081090440c0c0d108090190800e490321211131411200300841c0d58066449144001c00001052401d41c0324189000d8503800c0c00350080c0e5061300d1801030001c1c22a201c3d69000d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 354665152 1250 354663902 354663929
    0x15051014030618090f0601060f0918150605070c062a0212030705030c010f0b061c09060e1501090b010f140c060c03190204030b011202040e0d0c0501050f01 68
    0x42480c4081070340010011507100c0346520682c20007440109810b8050f1071800c00030300304000301c4400185400b41c1a0002028850070b10101000540c1c0712080009030b0303401d1040088182030480700840508280c0c404600094181031000c503003d940b19010b0084c00380509080a80320b9500d48081d6071009c040f01d07000c0329403601c408000180d03542500302e01442c14805400c1503a00c0d007601980c2030458010400031509a000000c440240d22402d0040d0168080c4214040102c2c649010000c3e046e0720541c4404150012480303c840450b00366039000c81801c541000040c0720007103402030303080d4450042e1600124540c4c81c240020842d1403542c070441408000c103844850040c0c1c21500146c42c20000c0e0b02c0c40010001c0c2c10032070460722031011b00006009003207ca01c40c537203d05201d0003201100c0c00c03201c00762110300d20500041011400e001e041d00c0c1155442d801c40c04146010b8000300e0050642480501c070544203810344401002c2d8030450305451035000d10001c01c415202c0822840f2400028071401c020001d52 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 354666402 1250 354665152 354665177
    0x9090408031305030f2206080103030c0c09060b0a02190b011707080109030503010302120316200414070f0e0607020108250e0a080f070e06030111030901150510 70
    0x8000440d08402c4401a024403002581d035001c1c0796a000318000044480c000c6154401440040900c0792448031681417905100e040c000c00130700f40d0b00144000760400c81d81c45e0004050120080c0d104002d00030b20282813240680710019811940e00201e048001442781050030344e030750200311002001c040d41c0025114416460000c4810801c0600d41580304140604040051139403024420311010b87c0c429114151658918010000f40030000d0031000c0c8550001c00800184900c04900e03016050f42c800900003a1420642c40e1140b030700301200300950820300e45484c401d1030070020280c251042810b81c0e6051209072000d44101c0d010180c0200b9076400500c1030042c00011340c0280b041560061580110329046081815a020084680d0020b0008030707094250030130480c1840c440c0304000d0042d03207000340f102403007c213501a5200c3c89482180005815103000c10203d581c207400c0000ea028190b4106030300e90400002c417a00802176841240b01d4004200300024250602c807865000751100c3e5100c14040b040b6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 354667652 1250 354666402 354666413
    0x3090b03270304270e06070c0312110a0206090c0d0203071a13092a050a08100f03030e1f0f080406060b0703080910022b060e0c07050c06090904 63
    0x1000c06152620b40014030001c00c040d90040044071035841d0602c04040b524180c150160300f102c40003407107880160040d60401031000d0300300f030341d417058254945810410890140011002001600e0b80f5040700100020199551680066000c0c080c440d56400d880c00103070402e041003070360b00f01d503000203405400140301008204686008082102407241560386420b900c00c05620702d034490354002854440e56038041a00c40200795515116415940c0e035480a1042d10010290460050361200401c0144c04000100c00c58001c5100c10028040d2080307402c030154a03440d01a20010182c0c0d1454000d402c0c0c0307210a0300c60b01c03812120401c5924551507019403130568403c11995460020010340c0c01c1ea4a4110016030314507070100602207140642d550600600746900b2550504001d0240600260300600c001183d4035440207035000394403c0d002075072000015219214016080c140d204890818190041028401400004206080c0f0070300035644a001660704002d40c60003128002c0303030841e2100c00001c00080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 354668902 1250 354667652 354667711
    0x18020304140607020a050c04020301050109050f040f050a0b090907380a050d050703060503030d3207120603080405091801062d14010c02270403090b03 66
    0x10702502861078071a80d085601454070b182920300900503484201c110041c4402401413101a480460b404d51940d498400004d10120381ca009942c8a00200b20046986540f568480303402950811400c1c0030740d2509a409200401c00210381900035080b490014031600004a140c0b0103484508010744011003ca40d41c41400e42403d80d8100c05440c0710014a15007844840060034480c1340325950b00b644e0303c001c0050307172080d6100540700c8824141010030500c0184c0e8084103541c10700d003540d40000f070000d00b8100c0d8000104900742020350f496407080708044142e0f590b61010f034800c03081512105404680c0a901e00b040703447c10300c000342c02c2c0c8100344418003852500d0700c4016040108400d20300c00b450703450301c0a01d0856501d64080101c140c0c26004051036424000e140c8180301500f0250039102925245903880c3e000403600c182810800000c5000b400c55603510020321180d030b0341d4007103507068010500911403c1c0c3d600740e60581c0800c448000010f048810401100d11074020500c03e02c5842204808104001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 354670152 1250 354668902 354668911
    0xb031b030709120b2202012c0a030b01030209010b12040f03051c0f1107080412030c140a0b181e030d15140d17160b010308071a01180203 60
    0x2c20440c40c00901503160324a0a200e881c01142601c901741442a119010350745d51101c0b0207864403001c888100580c1c3c202c00d0524003c0c3c42a0300c005803d04454800c6899080d2040056034820f070401e00c003205010740c03d21814141d9109a45401140c0d8803040c040220f402400140890003203480d0006000840946440301c2c80761007414050708001c0300e012256104500e050300d059070300d41e540118034452141e6005240c17280d48040d40305490510b050312009003600c5a40158a038030301c8001018020903101d100007004850708881000d10710000c0d07054054841654040507100400d052000c6210142c1c1c001c0c1580d14109000010040085248221001c48103403001c4040103000501101d490112a0702901024010b124449142030f400c0007400c22a5400e1044094001c2d0740c0c42e5800000942c00b428420b10b090380c0c04c00c490f62104d50110720794400410842c0000c1200003200f000004002e0100b020703000c101d1051030a0f40200032050000c1c1d014000c244200b201980c0f0000c200d00303002c003140e030096820 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 354671402 1250 354670152 354670157
    0x1020102043206030c0f0c0a060216050105070e060d0c0309061505030f0f07060503100b1306080a0507080112030309050d02070e0106051e0c030705120c070b031b0307 73
    0x1441d079116015010001007000340c003041961000580048207107002e0301660710004881e45415070401c2c2140030683d0080a144800c007030300014450030035240411a14103416030010f415991985030304243c130104440c440d0203d401e51300308808548458084d240c40105c450000d402c80d803c2a43c45078000000c1c00c07055085400f41681c800345c3c2804214507002e0072111200754014034450501e49814949005040702c0701101941040c2c070700711032a40c03011603c2011240d80d8580545c4946844e03428410f04015503000c6101e07000c0000d08144020000c0880104950841d2611480366841c038142d941138030070485882000035121801841003810301041104014000e240014160342903036038091400051104450259001040412050007610031907409040140741c03042c00c0020b0400d2012034981030550035020b0740030109690350f40c200e0410583d442c0c1038110040359070f00400c12100d248a584000012503044c02207007004124801142c0840c1e000303c0010740c01c40038441400302e1200c01a080071304003104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 354672652 1250 354671402 354671407
    0xc0a120b0402120103060b030c0301090b060f130e01050a1802090a020f16140d02160605070212030d0b120d0210050a0b060406020c0f010c03170901060b0a21110f0901020102 76
    0x340510380f0707095903000c0c51242c1c0c0002100980001010b181c0b82e01c01c0d40c250f2281e8185006000003c030451a1950000400e9401d101c000942d00005030744080000800c1d001d4515011000700c0c065015041903014144900e410444111120f601655500c400b400203500700380d1900106204084680c020a208607080b22503d0901c42e051090842e40841d102c02a07030f42045d544882840004144003980c0c24007040c0c00207044040440140032085041e91141000307024000c1249419034407031010540025441d00d05883d61001c0c071300788040c02054443c894502600e100701003181d015100144442c50252907400030190f24002c441400040c1000a00c41010944c81d0703031112402d40c81e130a019002402c069005040b5100341c1d0403d01003482e4100f000581000f8202d0385010200c0c0d0800480d03032444900303280511232a42c070b194030729000d040c040d880940603980024412191650104010045040c0e0300114191030034013003507407000d40d001180e42500c0300d0000c002001110440000404002c40d040c0005030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 354673902 1250 354672652 354672667
    0xf0b0f16050712080601051c02040801141003080708090907030c0f180e0c090303040308030403170f010e0402010207030c0803070312062d0504060303260f0c090307051002070e0c0a120b0402 83
    0x2002000110700c40035023a500440c080c04800710a018042c1c518805800408962900001300e00100c9110b00c0301401041c000207102d0244456101110b042c03440c041c2ca010b50764100500020020400c01c1c2c00440080e55117414190a81e10807200800507415401c0d80d8962181040c001300d20050000c4e16040c43c0340c00400040d07100745c80610141005500612450b500c914203800c0103444070201440e040d076420404410070904c2e10207548e406042d211030b0f101d404610f9455100603890052180c0002e041c69180000004a00c140007005002aa01c01d64030100080e11000c220f83c15a10240075105043c9035440d204181a0a084603d58030840700074442c007011a0350348085821604203405c2034000800300f0742c054a4080c0103185480705072080c00081c803060b2401c610040b5040802a007024004c103000615510f066408101000c09002d004203842d0680c4c01c1c641000e550390320700d4441c500380750817540b00280c49071040030141c2d03c0c01c070781c5a1180181104021510b0008203810051598081ea0900880 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 354675152 1250 354673902 354673927
    0x607110703021f080702030c0303040b07230405010e040501050a053010180c03030305130501110306100206550b03071805040f0b0f1605071208060105 66
    0xc3c055200c1d12070704125a078003050000c1082c20002c08103010b42d84100031000000340000704584d801608080714261035154200708903100c403026080041d00c9841012908104131190004108030781c4244ca0314030b100c5100005200a5402c244601c6501980c2c0303c1e0100220305080003025041e083c00620028450801c940c00100d0001417085401207074840600340703c521405114a21020304424a41c2c480f44402d95100c990280080c0002030405440c1e1020801441000038040300c0c050307010000740f00700100f1001c034403007075003089503400d21800c801c0880d003c804d070010600034040d19015405445691001d2605811a8400c822515030240031013050b8540c4000c442d04410034aa100001c000e9401c1130305903090030741c0c1015224610a41188a08009101c490754500900499151002c54650344504101010121414000d00b5003002c40041006c0005825031992140503505180d603041038202d81d00701c589001340480240950204520820694002c0d007071154030440515100f441c0900100d100e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 354676258 1106 354675152 354675169
    0x302041404110c0a030c0c05120307030f0c02180f0708060310090807020a0b04080601080111031909020a091a060f19050708070c1805040203060711070302 68
    0x2e0058603510001034503440e840c01c0e403c1d80e07140081c500740074200c82e00c40c001c11904800290b03c045200c0c070302003094910b00c0f21100011401e00c2020356040d15a00c035100b000ca41413010300717a403040041e0740e8a074000c240c0e0086207002c419130341400700009140001c060b01c1c2e42e09100c5010200721450b00d0011b09003180310001d07040413403080d40d0307420007580511800b4000781d0080b40c1d69a02107660048040284221a03582003240c02c0c0d60b0b0f03140f004500320b1380388403100031004004001141d4403c80191984404403640c03e0005050a40c1c1da000800c6034a240d4400002e5946030082d03066840c1008080c405c1100054529078980054400d031080300b803084801c0440389241058039402014412b4055505450340f002241e981e49072181041d16100c1b51504c00c00b5041240d0003181e4010700100e000d000e008960280041c20b10b615091000e480c000000910061603114240002025a5444a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 354496402 354676258 := by
  have h0 := BRFrame.cov_init 354496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 354496402 ≤ n) (h2 : n < 354676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
