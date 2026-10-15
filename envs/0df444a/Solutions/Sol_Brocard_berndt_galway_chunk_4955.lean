-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4955
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:16:25.117484+00:00
-- url     : https://prove2.me/submissions/25e96d40-5443-406c-a285-0b77f1dafeb9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 891007194 ≤ n < 891187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 891008444 1250 891007194 891007217
    0x20a020d0503070c080705040c05120105010311070c06050a08180607141204050303270703170f030a05190603030e090a1103010b0c150c0703080a0e07300c03080901 72
    0x4100e04c0803002003c1c1840a010118585410032003260b0400070314034180802000103840e8139540c2c51030716066800900f000034040941c0d4580038154040e600000341050682500403c40e180c000028000000c070b0340d560340189903200080800c0d8003c040700d5164495001c2804590028090014444480d1412041508000c1600400a25070740300781c030166042e0b000002802041c002d000803040804a8031191540c000c1c0228060950300c0b002c6202c060b1580c0351301d2200080c030b0701000c0c044851241c6204446030300c03420402ea0310fa0040400b65205048820300c3d5490b58000c405500a400440c0d8054640f503411414660500c00301141c01040c0c031140e03070340d50121f40b0004d089031406503001e4a4001200354031402b0840b41c16145c08041000140254040810442d000106a01320b551895240c41e00350501d803140c4041802900352402d11a406016020010801205c01c500c104030403d00307080e45901502c50410f0868070504a42e0000d06030f01008071052001c540040010000030074113140036400c060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 891009694 1250 891008444 891008453
    0x30b12070308070501050604020c060a0b1807020618010507090b03100302040606090611072102030f01061509140120160e062e0f091d01180507020a020d050307 70
    0x19504115250000420780f4001d1180c01d2061942c0f10000f91021841c1c014410700003a074499008221000703440c3c490f90707640c00e2910382e85083c040c0348580e2410703030505041080c4042d480d10030441c3e0344548460380108280301c0e0309050142a004030225240e12140034100104840641d000a150700350201003040e0010040c0c44602c81c01f4000c2203141c0e034903001c4c907080c550b0050014150600d12400d0382d02a032014068101920717484003001044081c504096425880404d00f81003460403150055440e1400000c1c603045409039a050081c200d0340c400655580301c2d082000e4646441461a0000d00701d4000d1080110600500740b6203002013000302c0780c3d8080f0080c01c24003000040e030008004061600b0a00c85581096910741ca0f490700250000348001d0b0141010300c1d0102400c04081c010801001035903006075001d2042c100142213002d01d1010446070085900b0140e00742841211008003207031002510000161040c3d5008070407550103003010440035000c005241e071508005540c903000c2001081c0015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 891010944 1250 891009694 891009703
    0x10060c21020312010f0303020715030e0604080c150906061207091a01030b04050f070e151809010602060702060103080a03020d29010216170304380403050a03030b12 72
    0x190040c1d401107a6541d007401e18034040c0c110603030150751a282c2044040c00000c0d008100304050360300c03144c455411031413006001c50181a0058052407140544018082070103810741c001d01c0c11000103800c4611001400031160109032044131400482d80003400400d8085c500810036641118a80045a401d0781d15880b100040b52050b200300e406850700100301c0d2186503054000da036800b500031a820007c600d001c0100d4003130100010b102c0ca040020351000300714503548825140204400501d8025242d85401e05400350310520055064842c3d0043c0700002074051000400502c550700950107059103901c0c59540789010f41290100c0402e0640a101560909070760b80f25042034203114001a102c112180011071003422449000701d811504110864980322038055070420031950b0200c40030b10001c880d05107040c25809030f43c0003400c2305007032070310041c41c0d09211101e841030040b60540c04e442d081100c200c02c9101d511131840000c06940240c20060b01103406a44200500c1da000750803080016010700503541030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 891012194 1250 891010944 891011003
    0x10c050312010509011d06040c02190503180a0f090f0605042a140a0e04092a0f0311060309010b06040602030d140112021509090a0f0f0510060c 63
    0x250280c07940104154034080c03c0050040c141c2c0501c131150700d45400b5621038444401805103008030340716000f04090364420401d0014030714611801904202c0e803803030080e40380d920808001801d002100302480301840e02260345d508582448918002691074400b41e0005000d1002d01c909403a6902c101c0002c260700c0e14015038460340218000301d0004810b00380d80d071042c502141041000c00c81800c0900f04040510f208031a40d40e035260078000300000c656400900a0110000024101012214108000501c84030441d0035050851401d5140c5a2111601c2400254500c0041d040e5450383d5046002d03820804020b60f005480040042044001e00740405c5450380320f640b1020059100089020303418415226400e1614490600e0122a5142c5840000c0110b040d01001c0d1007500312110400305400d401046449a9001525145640ca000803402005007003d0318400c0c150750401007043c0c0751090f0383c854107102e5098a5200252142445d1003255a410300b90002c440c2100419030300d80d80d142408039080030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 891013444 1250 891012194 891012217
    0x804080114040501051f3305090a0e0f07110f0a050d091a04050909030c010c1e0219060c0306080115151e03020d0219020a063602010c0503 61
    0x5040c28280f07007107401c50700000d0542e0500107412440c0c424580700c40302c010007121860301c508041740d80c801941e0026002004801c5042920b28002d02d03440941040160000901c02c031642e4403602c1c1e64036441c1100c2c0b0001c9481e814400740c28000a00580d00a244280e80c00d1500800c4400003800229083e180c918a14026186503002007441c2043c0d07070f8031030780ca40017910314010300b800d00c03040c0b24220751034a004a00480b403060446400166120504100740c610564902009024800d41c14401800740c01c2000c1c030350042882c800c640c0c40041e07400000d400c038200c210b07004070b0001200c2680341e00008014040100e81010748540c00090240b009000710000c0105140461002074075041c2d5074109950f007003c4090074010348404214000d401c03054a00100b10031401c0142e91080304c095184028840e070b01340c10001100850035004446d60000c0c0e110043d62103628100600161341e0660060300c0713090300f010304030180c0300c15002d903040b40d280c00c00844092040c10071240280c1300f40c2c2c5260450304007100281 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 891014694 1250 891013444 891013481
    0x4120c031b180b030c06180d0308040209010b0c1f0612110a060806061c150b0c0f0303150402130f0b07030305010b030601120b0307270b06040803041208040801 70
    0x1640b9200e00e03503100140c1c4110040007a8203903007012a031181000e4810794800c1e540800da01d007613001e2a415a00f02828000c008442481c40d5180142402070140c2d0f060340140050310000c1244140c850464007003000260007400d4142540141540d2900e64039619000e9940300e45000540111807507288c880c01d84940c2e025101e60040308140800c1080c00d90001c0208802d01e400e002c4983c40701c0c000c403200003014a002d2510700c91824050406810000180365182c00b200d40000369038103251004e040d01c041c2c02c5082e41d901c803015001d0b2035904e0000f42ca480d44541c590121071440c6140a90080444c00d080d1264007900c150303612000c88452070954043c0003510000140e6804041d0f06100e4180034010400c80d42d42107013400710000740104442c0403200e5401d9610705040c0e4a503a806c1080300028036501ca041c5091100c608005044190303c40101391304c46041c44145001807508609480941d800c1100440c2442c1c0b6110b00c90400201103030094605030310400c0049400070003809000424000d40a411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 891015944 1250 891014694 891014699
    0x150207020415030f0b130c121e05033a0b030f01020403030503510a0b19200d0e09130303020d0e010f0e0c120304120c031b 54
    0x1005540c1011841c031a0b000c44004240000b4070200d44810690381c00091441c3c155595101e84100068001c1014016098141000a0301c50850000084040c40340c44162180f02e6141c3d440789100d03204880c001e00a4009000c00d03240c02203501e44040380c104404002203070311402d54543d002c401c030304c3d26042e07001203403035031200c1040d81820446404081c4107500210700e80382c42c5442c02055408042c041d0411041035404080c6818120404c4a001c1c0030441c581c41c00c0c402c5842c0a1416026002d2641c006110a1180510f80d5142440d002001c407000c66160f6840d0801c20035140b00200c1d0050b10751300030304c0107540002c11403603086440c1550324001403000300400400c03084040c149552041940b44121140c2007042903498056145480c03050b4035080c096103425268048601920724030498a01c29882c140c02e03242d5441a60f00b01092400c01001940c0c3c240c003040f0288064549440001902c1c1d5000304420000320014840c5d4170103460145032081001512559051300c00015401e102810031441d9105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 891017194 1250 891015944 891015949
    0x50a1e170417030c030316050f120a050603030405090f040519140105010f21020a1d061809031209150103060b030c100219060f0603210507170307020a15020702 70
    0xe0300c42c00c41c0b030500031401c3c80e403031302d102039034034032000703240d02800300000c504540c000e8050f00a991116200b070748400e840b00c90441e101100c206045030360092450810020840303c0c2000300448054a202529441c0c0540c2c9448583c4480c210241085a0510545441c01c01440751001e215410341c0c402d1100020044134619910300351081a040220303900c00900c0c04210101c01c0300d0400c03920044d096250032040d81345000048003044035a0044c00802507003540b070014483c40031241e80c4104421030b1482008030401402084c0000c049415410513441008081d40c42c11600014503406040d4500715080201c075180e00c444920400e078000c40d45241ca0f11240741c01441d051202c080f420310252031021800c0c038000c900a50703a80010304810021240025520144261500110600c2107810401e101407540c0b4540b2111a04204900e403118540c2003c2c40205280300b2401c8500d007540010360003055000445610381550b00c05020320f01544030351158040021070340848152400d040d0800107803070700f040780103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 891018444 1250 891017194 891017219
    0x516113301050a050105070609051006150206010f03020616050a05010218030c0102150109021305061303020a06050f0a08151908151b09060d1a011209050a1e1704 71
    0x42d4803d00c0718480500c1140d81c010155400340343c0001c17001c1355001240c24820704005a40d0701356680203003040008580118814603890210103142d080f1400c0340c0e030ba4500c1000d06078480c00000d50202c01002009507160301c80c488a08180d000f80300761584840143c0c1c1d82400c80c0d1010034445268040310703186a106140c184400209810280090710380d855030491440c0c140c11050088129066000c280c40304840507443d5102e000d4100600f000d656142c01c2c4042415500c1940300491148501d0000400c4092199041e103090b100303003092450400344070701e4085d55030704802040c00b504c0c201c2c4500051041d80c1c03540481204051000380c0c030a2041d0800005c9414030600450900e0f030f8000540074003540c45e030340d80d59001c001c408404119840d4130844002903940c5c450256800409400d10303400c0000c150070f00302821340c91a800d0b20b50740d460a1049014400b654810a4064240d41000c000c01001c41c400c000d540e004060126900e48045015a8139050490b501c031800e8044010046010301801c1036202 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 891019694 1250 891018444 891018449
    0x50c07180c0e03060403030e0c0a08150108030a230d09060b03070918110627010e0a29160302011a010e101206091406130516113301 58
    0xa42a00403072801d02c0400c1c2d40d1040900000d04040c2d603040d08140f0b031141070010710200f0710300138241038080b55918072065456994403003039010107681800008042d5000001c0f46e80799415503c0744100220304880c000c503a009081c0290740d6105041209440080c15480b420701c42d070b4480c41001482503071400c20f0500d0600c40b90456035840f07207089280700c80024113100d24021660710555041c04540c3c0440032800030b0180303400002c040c03004a9180c410710380001428104141c02a601e11903a9190356007000140c040c01c1c41880030240510040c114040031480d4040c0700104005138180c940084407e09a810441c4100241c0050b5560300c1c803100b4100c0070034280200c0c0c20092070304141c20009400041c81c0c040c80380c0f00d04018840b581030700725408003140e0854402070029003010450b00220700d06c01c1c43d01c00340c112840c0c0d11a01c40340c3c80201c1e11481900c500707400341890800d584002289100c0a484143d54110710302c580d44074609004da0700c0c1003240000560341c03103c60030f0742250f1003201c61014190441038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 891020944 1250 891019694 891019697
    0x90e0412030c0e06090f030703061b0e0306191d030a2102070803060603180601060e09070f0818010902131512120c030302070c030803060a091803050a050c07180c 71
    0x3802e68240c584d21041501c0200d402120b00c902c43c941e0f800002403a00d000382d4002030980e0b04195018142082000b5600140b2030580c4420300c0f242484002c050b224a002c0310984ca5a0b4026102c002c00464581c5c811040210b104012030322840541c801c55155801056000c80000d4420307034003202c000c2503c1d10142c00c44520080a5007401c000381d0329400b841c0401415030740100b401000003620800010b1009402d03850b06801c0d1100e03540c580000400c81044081820b010351019000300d416171340300d03540080d90004c040d942c80e00280c079140e00c20462406280216131242d900c8411340c0001d6500c8108400a03c8079001c0c0004800c0c28216101080c05640d92005210020250000f80404c10000d902e01c505130b45480c00f0b038100a190328060b00240500003000d0001c1d030210070040300308650f410056010300300848808041030381d9011030800b034401015994041484240d032400000380640d014210540c080e0600604060300441d85618000e002e41c0305026800f00798840d940d50204603c103459421280d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 891022194 1250 891020944 891020957
    0xa17041409010f03080f07080711100806030c040b0d020a090203090d113a1106060604063513060f0b180c040b07050606090f0108100c090e0412030c 65
    0x41c03425100c0e040c000c074413000d081082c0c000341e009411551003080326030701a44a401030b03441e11020308102010781494441940a807041280c0f06840c0d5004600c2e05105100c014001c260844000c4184405400d804102640140c16400c0d0b410042c0c1d900710050000c0d103010307040161a440d011002c6407600e130302c0030b01e8207003440021031308080040c84c00f150b903401001c042c91100030720b1081ea0b901c51043c02d8040041c6070b50007541c031400f4420140d001d9611000c185480048451940300e01c4108000c0d403055110b540e021801c0d1400b641d09061040b1010404040e041c080c21030681c003001249071a0b01e40440d540c0c51288058103003007041001c903101d0040d0390541c0c07a06c20403111235001c010076548401c0100d0305101c2030900c4002160100c041c1c00b20381c080c100d0042c1d10ba44400051038020b5590f00c06403940f501c40c60b10f04e000122200c8810784650704840342480140354000e0702d07104100080c4602c917600410480c50110104511040b0b0500a0080b449091034910001c03c0f440020221924080102d003080316 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 891023444 1250 891022194 891022199
    0x50d060b0301121101052104061a0a1809060504030207080f01051006030e0f01020d1505060a140c03070611070311060907061d0405100302100e01140c0a1704140901 72
    0x400c040d12403032441d4004001d642010f144e43c010703580b50244002d60394030800d2a11004c3c0d40c00b07900558090203035200b00e909000c00815482e0510b07200c4400d00c3c0c84c680040b0400c0c000c0118940801e203901010944000001e01044140c03528426904121010f90159000074410024180100140c45005200710300801075800c00c2007a01042e0044c920032501015124810407109450500c994456560710784000c5556109040140c0007800d549054901c074205201c1e400a02ca003002d50886d142a881d55a03541000c0341e18071140c00d12504003842d89903c45c40180201c0001039428414035801d80c080e0400d15803a07141074a8010a0444180e44845850304544140700103550000b440030296860b0f410010f070840b45101135444049168914140d00900300014050b004d030100000d0820369000380d230190200c40341030805407054000100054002040c10500c125a0503095018281c400e41981c25140080c13620303120f10ba03003c8210301d21131500e1b21000404101140b00000441e11805045d149000b881d072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 891024694 1250 891023444 891023459
    0x912210e0607022b1b050301180321060b07231b12010f0902040605090f0105061b0f011b211505090a063014031603050d060b0301 57
    0x1840200030700602c0c01e0032a0f43c0340402c1c0b000d64100448500d6107071481408131800c2210400010b4210715401125001022a0034101801101e4050a100844110641c45a0340031614a08040e185400c2040b00c101c07a03410602c0e0382c0c042d00004090305d0b001d40340c0b2011142000e00d010f180f40c015010900101c41c0d9859000074020038602d240b08001030040d0344c154441303008106401400344111009518109408075044490b074400c201d454000c0e07a0420426440d10300380500c034441621a202141490350040080e0710b05080106040c03181803d40740c01c4064044403043c0b40161074110b0201e01d075101c0303a180d800082c1980441c0c81404c1d007880e00c034683c0c16420510402c590006000d8100791615400850003aa240707902c004001d20010340300c411645444c4404030010010b074080c11081c0b2400b04003503c21f0020a0305038240613804149224400c141c50fa8074204c90200d10300380d0642900050100c08a1401843c043d405220300a4840e542e42d900e00c440002d0803101607400500e02c03800c0c1840107100b002c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 891025944 1250 891024694 891024697
    0xc0306100e07084f0c1208120103080717090f0411040f0b0309060a0209010e010c0f0c1205010e0a030c0b0403090344190912210e06 58
    0x1019a0070b003980f00e900c4900314040d070030b038004030008041440940b03420144469600302000c1a611124522440c6956609100304054001005082c407064100280602041c450907003046a2054022a00c1c002c0b220340b000c146103409910548544201040c04814010b0440804042c8141c0b110902c1c506040c54000407513501d0b03a0b100881c01582d8901c1c007a07109203600e1048902500740c4034501c18101d07545000601e801c0c3d10071903544619028000110309600030034020349005050584031126103802100045800c641e10320001d403907103024030341d4502c041102241c80324060049074010102c02800c40c2492425540c0307104410300b45034450210704001c0390303110348100c1d283e651105100740c0540b11420203d0743c2e2b00351600040c01083c68070280c9031010304043c40d00c0d2042c01380b8540f84240f4820816450400700110075581490807010802c4041080300601c403800661580e082a0b8005034645000e0b044d17040c42d13460200c0300318013117041c3c007900040b00c480b1007404100703545002002208040c004c62480e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 891027194 1250 891025944 891025951
    0x315480e0906030120090d02090a0e15060307030f0201021005160e010903120c0221011e0b010e04050a1e0b0306060a0b160f24050c09240f0a020c0306100e 68
    0x48007140034092580c47d031010810340d0b03800820680c000d08003550312600429a260004045200d03180b0140b07030112084044d0b510a04e002006030140710f04e5a203c6200c0518026000c82c11402801c1361413214050f54410309015401110350740c2d91031040a100078005440c1d001090741071100c007080800000750241280000c1030458540589030198500c082007092408100c1d150350920320100360302d0b0080056001c200303401800125110110840314494048407140c85441d40056440b40211841c2e00702504241d03001200b42d1070000796129810711041c00304a03045240d542040e107034090562145801c02910360095000c541c5004030602c3d2940000940c403869a22824400f40040d5000c10301c03c150500c40340d110781140303c0c002107410b181003141000d400650302c0c1079224608004144a241620240e554003040a4103140d40d140750084003c0381e014140502030b803a030344108072400011115034050043c541c102d800810302c0490505c1010f060000040c0418400050428100104a05001090b40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 891028444 1250 891027194 891027251
    0x5070e030f15061e060418050c07020306180c040e0601170303010b0415020c060d050901050a0b10120902030f1006120f1b0317040315480e09060301 65
    0x10000c01c84e084040302c43d101001c079070f03101c0c40201d0000703013844010f044010415100030301000107a446400101c1076015005c1d0203034056000d070300050b0b203d0060790f0b24804907194200c102c4008121140c000b4065540c210401035158102a00400c551a07480c1e00645400103640d010b035041d50705240000c2114026403040445101e822483c99a00030300138400d2001428014200740c4c0e5403815854204098102550b0f007104640c03a00000400c42e0400340700f01c00c494540140100781c0c035406208121000f806800b8a4068207554020200040c2d40c10007071408070069000142a00385040c00382d800440d66a988804002c000c0305800c4400100e810752005003150740003c0080d000d000305100b1445001c0c0542004000ca10005240940102060050400c83e03106203903110b540103640100909075030381060840312410383c000309019212190490264521407142244200704034245604e101e26010b000030034041050b001a01806c1d04006180c1030340154142c1c000d002000c540c0001003040c041030303540101c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 891029694 1250 891028444 891028459
    0x4080d0c030801060e22020d0e060129070818030f010603081c1503030e09070305071e1106010807081216080c12070605160509030714010306085106040209030105070e030f1506 77
    0x4cc0c200e001c032030503901c425402442150f120320036044154000c14440709164443e1180c01c0b00640030100501519050300c0c1d005484605205600030002e80300d138400c5009400b5540c0321131410610103400e552110045029588803002000030b0710078040366002c00f6185030109401d01d0100039041c0e8200c0b00748503450030302c0213072000824050801201c21554081e0a0030440c0604000000d401a0004441041c0c52041c825103201950030310080090344580c0041c90881c4801c0c0842001090982c03014024001c0b0303601c142e0b10344182c0c06444180c26841107100302c6803582d440060100b0110000c4001b200b010150034010300d0184103800207a035a47c1d140c810240004080d241003100c0e41d10030381100f001001e41c1012a01c6041802c1b4203444160b001944080c5070348000c02002400541c1c080a0550a0644961220715405070a6094a640c5002800d4a81040d0200610b1071161000d1060910404039a41c40c908804101c404140c07c0402c030300c15840716075010081654810100100c0d40d90041001c80e083d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 891030944 1250 891029694 891029759
    0xe010c180e07082d01090c02030a02070902090a0803040b030901060b0c03180f10022a0112090f0b01140103050c090609040504020f06040b04080d0c030801060e22020d0e0601 76
    0x8540d65200803c1e5400c1c000b5203860001444e0700d40440c028103840d000c0c4000e000c020201141265a4021001d000005074021300007084081126402458040d5018120750131058480800b5807450f405070784a001010f03000020041091020700c208005040420100ca14001c0c802c0e006039640d0050051002c040340c00306802c4d11542d5652140342c6819003003c0d0000c0c40000800b00d020b926000050b0601205980c103042c140908415980445015401611001103c118019094000384030500c002c0b500400e004402c100030865440d140b5000f000d42280060010846100060036501c004c1d00380303402a54140321503000c0b40e6810b4262504424280c0300081c140c0d0761400090f004502d000e0440d5040f18000030301086201d040b0303006000340d45455049540103020348004944110034003602a0028486000501059200c0e100c1001d2120b00200440c0d03031424481c1d00c9400c00c003040e407902c20301030341c1c00240c46013400810300641c0040f40d8804040c1c00150315155807140d051080d840d90550200c01c000b8036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 891032194 1250 891030944 891030961
    0x90a140111090f0d1205070c05030c0306070c0c08060114030c0a05090c090102070504050907031a24010e0a0b03070f03090b0f060d050a0303140109050907140a03060e010c180e0708 79
    0x84c071001c0f60704035a40000d251000714014140b90f00c406010341d1604240c540100d2541030018026002c010050700030446d070756448a08891072440b07850200d0380000740c47c00005074490100302c5940601403050040024071030f40c0c41058034100300c4a900310b0240d40721403800c008581d115003826a0280184429580e101800c4004030f090940c69080550300a20b00b40a1254045000a10070140c0e44a15500e018040300038034401134007402111701c0c18400300643c241000200202d00aa036400d2410f0412840601440e800503008101a40005203003100200070030104d0b640c0480d60141e00e40460071304200410030340d1281c00c01520002e1081c41a84116800b158450b210640103603203180d004070a4540d410054036006000c2c20f0030001e10030702c141c012000410b003c1c4640c416607008181c9640104400c519140056070082d100740c0340b90b5400400000000007041c054041c01d8800c5100390000a408004e02d0000f40900c00560440300030301c404500c040c00314402400009800803802d00f0b1506042d40c0d01d206 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 891033444 1250 891032194 891032209
    0x50f0a0c17010e091509030313020406030f1a0a020403030207090e030f07060c020606220b01110709050a1107020105040303050708040b0c010c1e1b0515090a140111090f 74
    0x2089151010041c00018498400d150301c01c3c004d8840c41c040d1245104030340d40c3d01030456801d075202c80e2030360400c101044c002e600d00c2d032213800748601c00340c80450304640e40d849182c0c4603540740c84240c6180040c400300f40392140012540c0c1798071202e1000218101801c0d40c40095654031f0601505000b90364865071040e160b0001c106071201c3d080d0301c0d00e0b110b68030f104600c0c102025011001e4500050b101d0303075000c2040ca1a001001d140c0f80441410f480d0310340e080b17004102c0c01401d41004058140441c4c0c0c007143c2206034041c802c80d80a030010002c04281828004100012103c0b03040c030030090100280300020040c0c0e8800116801c9a80500e0043d07225030050408c20500d1046038048540140300180c41410f500040d00081c0c0c00f480c0a4480400c01c0c0480040340c4c1c03a1400100c0100c0001d03040340c4e0308680014291110310031481c050000c41e03110b01140702d01c03018500c40507104091a6480008200208400c0c075885a411104400090100c0030f0944001505030080c4994640710788890704802140703032100034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 891034694 1250 891033444 891033467
    0x130f020d14220503090306240a0b160309050613051509091b04120b04020102011d0c0d050c0604030b1609030b0f0a09240b0603010b0f030402130c080a05010801050f0a0c 74
    0x1010b80e103650500704405800e00c002440000c070015680307503d08c00c80303203000c1250f1011100d1028005c2c1c5800d403c0000c00103804c48c0350b80118140b0040480115003626060003030b2031540c83c00100380c403645040030300708403124413140800c00c4240d0341000030079021303101c0703003ca15040030780310341010510301d4142440e40c424011500003090f0704d4401203141d0180600c10b03401c7c5015a000380c0081103402ca0060035405500c0b1880503241136540038606040d40c0d0705100005480444c0690244c40516440b0000030318994400d0f0f009903042503905040c00108103006c4986a80301101d404d0043c00c0915550b00d4144070b40c001030210190540601c00030f454810706420503030820368018032045a40908601c0300e0042c0c3c1840d8410364280e03141c114006424100401124140c8040a03c1107081c028a02c018001a03800140101d800c034440c0003105104070021b010f0000d1215103521b40038201c0c5001e158050480701e0585c8445c2c0c40da1304000c14090b00007501340205410980c0000041050000b121003500d802c0844c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 891035944 1250 891034694 891034699
    0xc031923071e02010507171e0a09060e010614181b12070809070909050a0206030402151303020405060a23033d0203040c090b130f020d1422050309 64
    0x80c1c0d00e4140d003d0b41984220300c2080381d03031100a41c0f1226020900003200048540c1c250307182580303411030740d111f00140d4401e520400791180850740d07041c2c6940c0c00050f1480c490094038aa0344560041c85543c40c400b200c03510440080d101070807404004141c641c54808040c002d5001c1d421100a1640508140012101c0840001c01c20703034802c1c00e0018009244410445440c0400d008140000c80c40101c24007030003907869007000c010031a184807902084200da01c050003c99101c00050082c0200c44884c2024040840401404801c401d00e140107000685500802403885590003000c2031002d401240b003040070503a554161120074628a1000c00e19080258071420aa402c004c42c3c84102c2c42e46400c3d0380f9056038905100003407080380c8090500d05a010545009000303c100703000c24414120242e0000010340001070048580075200304500049030101c00d90b51407200d03000121242204164015981c210400303000444d02403601c07100c840781c414112004c4005030741c4882075980610500f04150347c68007400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 891037194 1250 891035944 891035987
    0x912020a0306091101080f070f0e030f010608031207030212010909051005150a150503060127120209060d02090a02090a0314070f0f0803070204230c03192307 69
    0x241000c0d41513140c0300480070b00281400d800030b0a0101e06494160007032174151101e1010350b650940940e0000080805250940f050506894100d00c090241000814880c0003450761039440c46038405000100800c03803c2403500420140981e011450742e400c0c111180b00b000019145624070340343c3d0800b2070709580c500100e0300381018000f0b000b0240dc030b26000e606c001c0790f41c10390b000d94403501c006d02c80e000c204400011034014000519194000c042c2c9448406455038907516014161503001d2200e81c01d508580f41c2200c41c90311450460810500860300150b044034510044152940064940c28005244000098011498264585902000ca0055030340104001c0101425016450703445400703120307490445491050004541601d03145160070f40c3d403000c02640c07800480d03800340030182c03807150141da2407076100704003d41c50400c0c0341c00b82d0b60040c1c41d2520312950f00c0c200003600c068482c1202d01030800d10781c900148048203800482c0344503101540c8144600c3d040e40c800c642510400304c81070146a0395003c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 891038444 1250 891037194 891037211
    0x7020a0f08030907060810090c170c0a0801090b0a18060b041508160807051e0a08100b040f092a0305040302010612031b11030703050f010e0604030912020a0306 70
    0x800780954441c031540002c40d18010b640e44400c4580501c00e50380030b40c0341c0c0c20f070040501020081d908095030f82c144a0520300c80d8100000340000040f00111101d030b602002c08114281c3e190341c000807060040c00481c900f84800c1150b600001c2030300a880c400c2e0000d6a0880c1015000c0080c0382d08410001d1030040d290350340f1655901f00e030040e801e402c17100e0040050a03000c0001c10148140c804001c89c2e6005580740d078401d950750607059030540e010084d42c0c103100e45110811304c0341101003001400040d0a40e5034411140c107048a0207041400b03540c10402c11883c040c001405422034010446040360951040480c010310039040001a04061814003c0b100006401c4c0d4103406416401950141d48a40d00800c40c0d40d95500d2004405428030300014000f4265541c6005560311158914403418000c5100c0c10700b08070480c000901e040080c0d4802c03541604007000c82c0c0c060390000e11a0f003030f40710102d07000361800c1c0c60907540052030040c050180180480b075514143c81135441e8017a014004d194080c104014100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 891039694 1250 891038444 891038453
    0x30d031a04110c100e03030c03071b1406070f1710170a1b0312120b03070f050103050f0106050306012003030a09120c080a0309050a0c0f08120307020d0807020a0f 71
    0x41c00002d0f22055480740000100b0511034901c109896a800800918103584804098104036407015015008000e10045900c0004840f0407804203007521911409003501d542595040c1004c00007045401440000c10b41440416000320100c2c80200500740300c04550b1382c400d204044420f5182d04100c249651105d804004440c0000d900014140141101c11a00650007580c0ba0540d0003404001c200b602420703500d0350801d008400302082c00c004650b0100b21401c80d80040303858010700d98030a00000c80050b2007006a56010f01c02d45411131098680d151480d81001000f40243c800980303950304008500e10940c0314640c40c00021100789220500352544c0c0e05080800d0741c00f4042250b0213640c0030313054030080754000340103588210500ba4805800f5051035800300d4150001e24401c8001d8400d03001d54410080080c288948082c09040719200c8501010304050320140760400f10450508a01010800e0181c000c0c0c0005551a46105520f010b40b10359503005003c03800c00c082448000c0400c400071600346c0400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 891040944 1250 891039694 891039697
    0x6041e110a11070b0909060402091f030e0304030b0103030503130b0702011a06071208090304030f050a03032909250c11010c0c1a16060227030d031a0411 67
    0x40d682daa003a40000428855580b5403005200c1c000500600300400940d030300741140c40703540c0035200500c01410040421b01042d0080a103241d159910054480080c0c080740e010f1140d244070814490055081078259594600c1c03440c03042c08044d0912070048001007a40c0468441040240e91181d510b2006040a900188c060700c40300040203101345010030502440c0c10720005607007034180c10084100c07041590000a40300c280000c0c0002c00716010410010000c02c0c003100c4a800101c1c40b5070003e103009044c034100107003211100d1301080c030141c4400b81c510f40300a11202000031020b10440300d070cc5841d1108400c1c1005211008480410007440c04841038086400581c41440746000340769003c04080d100d80112903445080900401c2901c40160502c4070b15820484501c0c81401d0075021843c144009c1c6081c484600b50710000c03200d042d000124800c030720700745007078120704049180501c82100100381c2c002602d41c2c0303040c0250001c16654900704444038900724000c002c00d000203002007062108400000c00c46 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 891042194 1250 891040944 891040957
    0x7050d080f07080403021c111f1a0a1820120a05060303040b070c08060f04050f030708030403030207020f060d1a0603040201090b03040c0509010e070813050606041e11 73
    0x1d150794200041d68150240d42218495a4198080c2c07c0a800007091100b544502c021440100b110401f1445907040d004c0151441d050324601c03205903884814842d407400d48400c0a56201d003428081095101c40c0c85555500c400e40341d110040c10280254107044100a040c1d80140340c40c5500d41f0058076040c01c02400040000040070020340c0000e958124550701030341c0080d00c0031034056000f00400c01a901707103040a880c2c4184a4298418150340d50103030b03180382900c1600c2c401100d0710180240804c1010420440b810510644061410165036403101c80705070200410180a01d0f40010703041086564100318071008090060105480c0c0c0960120580103080e02c0c40d900c11081c0c10424045c00e40e00c0c0c5001900c2c03180307034140e4409202a007042c8185401c1d07000540708642041217144049101c1d81c80003051f5018150703e124503112032a00d10401040c0d0310014110300d262809140c02d42020a130041905d0340e0224042d1000b0031001b1003d5050004001050490b41701303035180c0180c0004103200c49008044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 891043444 1250 891042194 891042211
    0xd0c0305090105130b010519470901050d09020301090b0a0c021f1508010204080a21080105060a0507050a050606030c0307060c031812120f0e0d020d0807050d08 70
    0x80c50f5181c0194084201c13103070b4000f61081c6408001044240340112800001c1c51081e91002c400c50b43e02c3e0010380e2166820805c822801d44180f500c0010b524807070008000e8841c0440841041c0550702c03403c0402403142d040d0340d504004c17002a0714034149040303030007045c03507107074060020004002582030010180101340c913907071101400c3c0505001643d100003840c0d58400c0156010013130888030035411314001c01181c4c0f003100329140c440000140600b028400343c00107010a10140c01025007500d03010100c4011040c4e0100d1170300c0342a10240c03001c0d503c19200e07810f40340c095420550301c0005040a80f1070740100c40005000f40710b411a03010401402160580c0154401c2e07003211030f002e290204040d1500c40c00c0c0617401c0080c07048500e240100e881071f20300d5040c09000d06400c0f41d14036103980074000c0076100104182c58004504100501c1164808685aa04034035840e0218060b510b000020f0403900141d44042c4c450b00c80c80400d1805c2c480c001048600d0198800211104411559005000081d08031000803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 891044694 1250 891043444 891043451
    0x6090105040b09071a0919030c05031218040e010b0303040f0302030c06030f070c031b050d14031b030406060f0f0f0b12011e0e010b090f0a03080a05030a020d0c03050901 74
    0x4210100003d200d00559100c00005e501700c550507424015036030040c400d0140d00803481500c48445081d00c00480300594011861228414208030501d40341c20510100700320080c2d02000111074022000c000031b0707400f581c00c5401060031080385034194090a60b51100c0c41e4507010006000074200d44c148040002c480c401c0d02502d01c43c03070403401000800d0004a0748400c2442c0e003c070004010341d2080c48135041480c0f007400e050128440d01078a003c804d0343c1410040310241e02c109051501a50007030141c0c10010120074081b4650719000c01101c1a07145150002d400c0410040003040401c039554100c1005481201040350032603035683d0a415201d1064810007101035483c0c2400300e0080158001c59144800c000d092150913441d200c003101c0003042aa030401900d000503003010680751020440b15000305030180c036031500d030b9420904211502c084402c495106070880c40c800c00001d45014191034a000d034a0921035120b55819a40402901c10518020501c0e03180801202034903400d9401075006200c144000c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 891045944 1250 891044694 891044701
    0x80c0d0e030c0c13092d060f0519060506041205031215012c10050c010c031a09090a08030c0412051612050604060c110726033906090105040b 62
    0x410480d09045c6003d4030380b000903003e40040c00d4410941a0014000c407102034903d0915445034004c5612004031041c1d019144e4080c40701c1c803601c0a10341901500d407910200081e510b81000140d492007070380b091080c4801c1d55410403060040920a80f44039102200c0d000c038641ca4a4050f8a0302044040d508a010600421203400c11600039058002d80606046101c01800110001c10911003810555041001001c000c4c484102e00203000324a0501280e44003c101d88d484002d04000740d190140d4014060000c0c41c0403c210000700168010040c0d400030101a40c036203480403001503500c1550400c15409640d00700e00c000b00480003680041c001120240e02d032020741c0301c0b109162000d0090380b000e085035004401090108500ea80904240582820013007810700310142641c2c2410480d502002c800c004140d0540001ca089000c0c0c00800007a0300c01461810251500102402c0800e400041c0344031040030484029401c40c4411501ca80c01c0782c4101c0f05c42d071803c20070072030103003600700c1e001c444010130380021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 891047194 1250 891045944 891045979
    0x9080a0b01080d0f020a030e04020712031a01110604020618030303070207090c080717060310111306030b0904122d03110405060a05030a0204090c050307140a080c0d0e030c0c 76
    0x704c40c2c0802e640682805070380b5841c2101c0c2100858451035116508105a01c009050305008005042c1c2c0e9482c08949000b250548240c260095103825040c000c003450344c0a061403001c00e040364043e03811228551038000500e000c48503a48040151a0140f10000034409050b070000b03080c20842c0c0040405020751030b59840100c5003040d05032030a0012482c1d85081509503d40b000704643c0c482c8001d01120880c02102d883e50050741c0c0c141461802038280002c290540c5040020810081c2402d41028803080302070b0f00216022500060000c0c00d03160a40002843c010301c20030f8120030011345002040040741606010701c07102055105001c01003498242920b184030002001ea130100e440062a503428441c0c0c20001b6030f40c96000074042000c207682008007149100542c443c5684541044d07031031a84a103001400a092402c0305030b49080102014402c1c14807040e40800d107242d0003072029203503e40701c10700c14402c240a00042000c0301010b000206d840118030900007108042140101c4420041c1c0c02c44036038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 891048444 1250 891047194 891047207
    0x303040b0c0601120807240c03020409060b0a08060d170d1a0a0501121802120304050907080f06040b19080616090803030a05040f0c0b0a1e09030b0709080a0b01080d 72
    0x4020840a010b06c0340440d039485030f039468265070460803440039003c1030010012104881c1e40350740402c2d80030a06000b1a150792258002030588017105511f48014160094440c01c002405107100e84000404542089104481001c2401e1464031280d1114000c1180102034140d0b02000103000c0c400d024a20401c2c98018291001c680041e102d6410311014040ea60018142034510441480324054038040161900c8040008960a0070003031031301c550400003000400d1744050104000c0001100600c44412118800039400c50030442e00001c4680d00703072000c14440130701c2e0381d0110008003a0060001c0d9184010070920b1161104442d001d1000c40e44180590344880b25014010071383d0700a100080c0e900d81654419a0401e00a1906180c0355030746e51348004207040341e80c001c50040440426250b503140d80000c480404200bd40f038500d41ca0f6419038800402941172844080d0807400c02402080c0794a000381c20740d101500705036080d0340686590f0309120000f0310080c402d03105c00e07110380302c5005c200e6840307002c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 891049694 1250 891048444 891048479
    0x40b040207031d0102070e0f010e010e0103080d1e051003051002070804050d0c03080c0d0207061715011b080c1e0706050f130608090c0102010b0109230303040b0c0601 73
    0x2c445110fa241580c0f1400d901000c200312407419845200c5000c9100a40c184904e0310440045010f0082c0d58100070390701411070010f0340202200882c12005000088040f425240e20107120600040d0280351084003048061440c2e501441e46032400e0107100b40f601e404035202060f80d0003042113504003c4002c0c601c400300d200700100500100e20a001c213002c0c80c50040c1002100d103020385200c100f0389407a0f40f41c20321640d100c2c038801a03c5500003603004d40540d8052200340010103450501038076a440e10301d0040c4028800410b1101d88000e00040801540e02811050b0008480d52880b2004092a45081010780c0d10a0403d840c81c0e00c100785245400e9000c40c03032103800703192016014101240c901002562581c0290003454840801400103440c000c1001000e40020000f5564000050808107913050500c0006504107045905085400261b660005000e1080b204401c01c0c1501c00c05034540c0305240b00011141241d40340c0000140040c2201e404000342c1070034260101507030b81599070354515852510000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 891050944 1250 891049694 891049697
    0x316031709090138040b0d060914040302071406032a0c07050310050c1b0c040203100501080703091709040608010c0f17010303020601120807140d02010c3f0911040b04020703 76
    0x40105206e60004580030f441c1aa17041e00010402130348900e110310075104990821040005480f0820040c50f0381000814014041d54040c2e2000707100c01400700d08503200c014001401c2507030030b6a25150004c40d2803041030000c10554417264035414508485511005a44100ba1080c42243d03010b070400401031140034055001424030502d440551b04844400d5811240f200ba02401004861490313a111400210f01c54421204101d40c5c1d1401d200024017030801c00350089040500e004d101400040b40c60710000341c144200c1c0f094035161000200090003a00d00d0790441180c035420024100421a04141c2c04071614019032592420b1006902c3c00201c00b1000b40300150041c0e1044004100c81461000c00041280c02810300c10301d05041c0703803130703e110600a512510a8940c445902650080d45c20300c6010034035641c0d0714041000003095114020040049408401a810b110603d01241081c0f2641242c903a0440082484088400e003000c03401d0140f00c2c04858003e030300b08410804540303028802c40c0c0a042d8103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 891052194 1250 891050944 891050947
    0x90c200318010516060c090602011e1505150d061e0e0c0c01050711010b04060617070507170307022116081309020c010b0316031709090138 61
    0x41144007420034078409090b042c000704126400c5000b80021000c044507004240102e51110480d50040c24101a07512240c1164500707001d001802d003002c02003d00f081c031080b0011a55100b010542d601030741d8170340d000310381c00100308038011004458100030f042c2c4054009402c101c116952841c020400104008462800300183c1050100c1c2505052554004282040950500d001c02c0b803400d084940c05d0700c8050100f107890320340d480109000d009180078594140d8061100b13918084000d000d001c903140d070200d0314010010006956510030419640312a42200c0000c1040700c0c20014440c25520954082005000d40f101642d00300d0100d8140030440d201420301300d0702d0112001c509841d500c80c0103104592481040050b1051099640462000362210450042c1c0e1a4080180c082c2181e8040c50004c0c003940100a06604520000003c041202d0b00f0114440c1c0800316061880d80a00c2004103280d480a804c01c00070078000c43e84001c00710803004d01c889416801101a91904d080f0210b00d04041d400d000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 891053444 1250 891052194 891052207
    0x510080114060a0b040e07230a05190e10031e05041209270c03060308041e0f030203071205031204030f020f060f011206020706062d051302090f0a090c2003 68
    0xc18149003410784010441d48c1650800c007503072407440d64424448400000e002266150b45204001c008401c40500e504011001e20800e4000c258101020903920062698800d0f44004048008403038200c0c400302d6007010400c0c1c2c0751624080c0c040700306000706800000d58104000c90850281d40b0103041c4c1c0b640343c0000f8041c3c1c060249070400505481c01e0b151042603120b080001c0010040c201520181205241c445581c00070601c00c60060207913603000c45100b0451000030005a02c02244080541c0c00f41350b940320340c8407003d0038a2843e600c2020540810202c07031600300410715074018003050019038140d00350307a205901100469a40e0a00b503400c0052203000400421480350360100500c0914800d40015003400442e0f119101260215030241c00c1c0144042c81524460060000b0001c0900c1d2466a1030001030901004c100000072420308104540d9001401030f01981e5495004840e401c0000c1425a000342c8078604a000380c40040c0c1c1c0c95020908a8280c1102440780040f4151000d07501c90046040c2007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 891054694 1250 891053444 891053447
    0x81303050d0509150108060601020f1911010918270b060609040f02280c05030d02030c0d1a010201050a0c02060c0310050306010b090a0902090d060510080114060a0b040e07 75
    0xc0050043d0007944240200d5a45110500c10785034020130210010b019140b514800190600b000c82404407110303000343d80610144164403c042c203890750055500000a040000142ea190003550031003555140c1d0b84685100714002d0340c21154601d0128405000201c1070105021500c1c13040d004000e10140690300000d90609000c07014000d0b00000400104440416056501c03c0380e00c920850500145031800881894240c03036000d5190120515080c401c41c020703501c895440e030080e241130500d41600040410310320644101641d00c3c4080220040081104148801440c03013505041d0700d0140d420b00001900b21481842035050064071600a80a81e6858a505046aa00c01000ea88103094515004507140d2020083d03103018025038100a076a40000710100000f082807a8440343c081e03401000100e425031180716518080d6540700801046a885003032504e072031041103400c80e48040d843c05060a250050880c07a803409082c00f03450b80395001e42c981c0d4620a15100b0303400b602a250604401081125 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 891055944 1250 891054694 891054701
    0x3060c050418052203020c2106070e0109050622090c020307020904051504050a0b091902102a020a090606140a0908150a0c030606090b220f0303081303050d 68
    0x2400c80d8024140d162160130f00010404004401a00103a00c541c0002c0d03d607003032601c11031207460881464800c2c00c88022069959a40005020500300308101038542c4903030740a280c5500c09890000c106c0b68813842c4c02030041508042100d038036802203100c0a4009002090b038860b81c1e00c2c4c49501e0b4051854502c7ea9002d000a00318042e008946511840c1c0c480c0303110700842c4410034011031059001d0000260503042c0000d0002d0007400030403141c0c1004004c09a42e800042190741d055a06682c2c0304000c0b05000000d0340c1036201899210440150520200a102d00c081680c082c1544200c230404049515503014100312812402040045015005410301c1d02d1100c1000c0d01c4851001d1408410903034542c4e454605014101482149210b401e8050245000441c01005650706480c6000c01100d0f00e000e0004208076014810a01c40ca0400520441c0c00e8102c1d82e83e28494161480016107126034822f0305400f00b021a100581c0062040008128050b040c5c4420501d41c1d03415640d25410003048040d844001c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 891057194 1250 891055944 891055951
    0x10c020901090c0e030307050705100e032d0f03030106020f0102070503030a0504050304081902090141041b02120301060c1e0219030501180206120601050702031603060c05041805 78
    0x1403040b40000c481030f59170200010007050b0321460181284078545070a0140c51004160b4801c14000d03000d450a005880001e280f56100b1484540803464070800c04846c81200030402d02c03602540100c0314680d05020000000714100e03079040c2d01300d0b180340104200f61801c074058180010043d410400101c1d4122100303401040c0c00601980907030340b400780e46600c05440c00c800709404d48003940449001d0b10542ca4584400b80c01002c0d40c4500d0030b82010020000380301d03c072004450302c1851025201c020012100490722130282d0740c01030400c100782c00c030640707905510302005138517840144660700d0456004a85241580e04039603090319140d0507900280d40b148101c7c00384088403011240030461810240c1d40c3d28801070383d00c0031170b04050800c0c03d0840c1421400d41e06811400300412804001d01801601c601048440341952440586250b4994500480d4588200c1601961500c6422500e00c008964259040100c910410040002655641c0c05850300c1c0254461084000e031a0051400c83da141c84d001140d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 891058444 1250 891057194 891057197
    0xd090516060801052b150b040e0606010809190312060605040e04111f05120708011a0d1803050c070504050c04091509020c0309150f0415140d0f0506010c020901090c 72
    0x3540704100c2414290305c88880b006480350042c9080070a8a070200b0b02c10800d441a0541c0c0c18440414008801070391441c01a100504200c809000100f20360f00a100c40307902118016481c0030700d500caa003401841100d03c4122550241c0c502003000648502038005c540484050800c40c07003090799903481d00034184102c4869250046041d00110030000c1c94071000048034151501c4198a4541c06a11500800401047c0c2814051120018051000510403140403c0161419240c0d589411050000509888080303d00321503d0380c4038510030103800c04007801c00c1240c1c9070115514581e0712010807090324810340d090b81c4490810401401940850f42000c14885030110742d905803242d44010b410200e074801c251a0400da00b011460070f40602d00040e92941074941d509400382042c0080c03403460351324491440f4503080d0380a54100c1c80c06413130007500010711902c0301c181d1013074031168000c4900d00500044400102c06e1440d00c1d00043e075640c00785e6400c9400301d070050b051001684c240301c10940180851150f42d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 891059694 1250 891058444 891058489
    0x270a05090c071509031101053c25020d0903020607061407091a070c0e07090b0c151608041101020c0a08030705121606200d09051606080105 61
    0x10800c0c0fa050800040034924000800e10b80e40c2c18001c00ca014094031151041e410901884680f0345814440c0031854031114a010000440074681054110380074040c0c943c51801204219000500300064481d80064100308030000c882d40c0d03c100d0b10f075060706030020081040200d003800036003031100c0644595481402c0000303034800c01504280c00e0b42d0701152168009001d58005001209091003400001a035504005013884220f075100c06000e20140144a220610b0200289000c0d00c26850300008003100021142d0301c80100c0c1032039441e5040c80115011031022078022491000c215910102c00629994888409442c0c42e07442d071601186050109045100304449512182d8801070480002c007980b10003141e4030041440d240e8106100c0c2201740c840c0710018813a9801c0701c502e5484404682e0b42c40000040d00075440f020410004c0354602c01fa035813251000c41c8070320f64401c0703a13405518160f000310101c5560012044030032081c0c0b0f405010360000208008010081400d101c00d115807601c2c242c181c0700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 891060944 1250 891059694 891059707
    0x40f080304111e01030f020c03030c090409020a03030513240c05120c030408070b070f1401060e0108160803190c050a020301020310060e01020703020105041203111002270a05090c 78
    0x600008003003042c00b80d095460f41000d10300d9070300f43c4504058089040e005604100707044a401d40c403400000d1500301800c1380000d00700880d580b2940112042a030080542405a4a90400514941001c074103030510a4480501040041c0080b01000c0c00300005c4e040500000d444050840b1110354034581101d0314480c030b485c4526641501030103001809400340096407918a40069a807030b001d40b540c000e850b20602000450007080e001280006e02c25000300300390f65800305080da042d004103c2580042c41e141d031000000f003082c11010a001c840c0d442000750f05201151a054565101c0c4500590082090400c400d80d0060500600d00a1642e0340078105540145106070042800da900840b8262120829410f051040a400504a0483d4042071008000040c107550002e4054400d0b402103489240c02c0310300704420544a6603a840741d4510980944204180c2e52040202035000340104164030001c1c0402d886242080c1e156000d60102c008000991540c41c01c801c0c0a10007801030111074400c101004207 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 891062194 1250 891060944 891060949
    0x906050d32010e0a111017180d0e01020c0a140409021c0606051009080709111303060501050102070e06060d09230601180207110411041205061e040f08030411 69
    0x41d85031010124000c0d0200c1c201c0c41c17400c81d220202502e0302501c50f002003051035024992162407552100c82040500b250746c0c884045203118000c142d4007030f03d907a20401c102080441d9104411050414082e0212179003c4550000c0024002c224094080c10161a0858110600d03058200c0081b00c0c0c00644407040c50100004150380c621551101030b43e586403200c2e410041400c0140c002603850101e49420390025091041164845019108001c1d500e5103e40c0d400c250000b0311000c85840c0c407034150603804d805940c3c0ca480703006080309110b240d000d030044c81c00000c1c1c0d040071a0207080c03081c40c00a02c100c1c039000044c0201002007010b40d00640d4000c580c04034003d008100090700241078070044006040e03561405070035414a00715091202c08403030040c0304150029900c40650300029400300c0d00031400c9240040b0344c06841c0160780c8126400010090488180f1001051681c0500104542c00c500083c01046a00c2050001d840042c5a101c00400321808030304650301458006105030041407045403003000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 891063444 1250 891062194 891062201
    0x60f040c03020405131512120e0a050904050a060c03061208030903070c03061b2a02010225081b0a0303050a0306050402030906061f09170a080f040906050d3201 70
    0x5544001c0e9440c25400b120320300004552000704107001c111f1102e200c5aa8600c80c03400003485452040c4072510244070132959504046001a1a0144c03a01c051858a4106140c1c1d5058554003940c123180381440d0384022901c00c0c020107081d981004905800700002e9540e003c00d5501c0280480c4003030105004220016101e981da0340021340c01010003140e1035461400541024807078400013000c0c808564103074180d5005040000038514250015403115819a000503814090703e03034120071088950160101d0111348040c5844288c450202c2105ca0008004050014641102080c0e540c441c12042041000a1049004040b0f029062a0201c1c6880d0344402140a82c3c1040d07590248d5034102e002000542d0a00c04441e2000758241d404d9104900c840d99405041040180540110561015548502480100101c00f113855012003400c0e40c42d0764054943c00700b6045401841440d80c1003d10002d0326103880102c1d00542038010000b0754a052000307217400e6416030f601075051200a402601e12958031001e12 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 891064694 1250 891063444 891063469
    0xd11040e0f010e01020a08040f0f0503030a0c08060a060c1e0204090c08160e070f26010302120a03020309130e06010f0504150e01090c05220617060f040c03020405 71
    0x1c10300d4100d614040307802c0d43e44100501c80282e106105402d0080c0d4042c210343e801c5a002242c0c0e43d002441400d1441c042e501c02000a4028403001082c0240c0300101d6021668001480e926045c05403200401c00140c10268400c003400206000c0c1c00c0d5021a04081c000700e1174180f41c1626a0940e10b50ba40070a05a170304041d8181c64546140b5020441d1400502141d07010307038001c07030303000303030200e00309100c4480580024000038104074034483d0903440c4034010342c1030001c00044c6400141010000000c118507019003400105d0043d1800c45205407200e00012b051180c09a01d88c02031420559540140b0449001180c9a108041d03220301284104040c203021081c0601008400303000703118100410701050313031041001c019025250b01c2003003002d982894941415550000d5000c240c44221403012102801806080c0e96507241104003450804203042041c0308860658640303400f401d600120b142c03848101111100e800c4060031106c00c2c198a000d5100d400090400c0c1001400c00c0e032074a0200c2c0381e045c0e8a6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 891065944 1250 891064694 891064721
    0x221150106080f04030c06020d06091b02010605120a0f0c12050f0f0a08180f12030a0e010c030c030e04060b0c010501050a121e0c050d05030304021009080c0d1104 71
    0x5000612180394048503543e800442c2c004140341d00d0410f84c0d070040095490000107420307036501180014481070903030480c030002e1000c50810300490003c1044881043d03d000d116002540c81c0c1100050141450450340082c1c0c00f081014081c841c3d51600c5039039500c505038000f219100b50b9808080360040e003000e81c0b41c09103401440203104d00c500305001c10b840d121920398483d44a50020b1045000100307400100d03a405540e05d10101c1e0941070000115982903120452558041401c0112900a44000000d040500c0044d40d03076481c0c104001c001502c15000142002d80040c003100d00c48400300b4001e2801025507000644002900e9582e4051032031180c1014180c048540d440d58010081461700f465403001800c0c5200c01c1c1c41c004a03180d540c2164a0851000441045420319510310034041011660301c0101000f500d9881c511076146413840e2a43d0040350100e00c243c034182d8813004034510030801c0c0c10035220543c00520650035402d041004400c09417204440700f52203400203803041d031560301606c40c20326100c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 891067194 1250 891065944 891065983
    0x81e09090c0d05010f150315050d12021504020906010e01020f0d030606020c0a0e07081e0114041b12021617070b15100e1206040c0f0501050c0a0221 65
    0x1481188010f546069220000b00700c80c6803000e0110f42d54004040c00f03140c0c0b0a040005038070203d006600c4c841c0d00d86900c2560300550f04003428052051518641011b00c50940c29075403061182100b4001d110800e940103500701d8004030000d00c4650250104c0c2d4018441401210544141c010b1114508150000d04200080d100c4504001d5660100502241607408585451009080188003854584001c0c00f2004004e0b070940420f4214030b040c1040400c40d001c0450350413a541c2c681000084090860101f20300035450611008020b217051008a1050701031551840c1c1c1c2c902c4130000741000794100d480702c03904440c2501030710340004411b42440700f42d41c102e000860f619420a07090000e1490303030040c00300e074507103d02c05085442d0351b990024010300304800d420603160841c440320110311810301d4100c0c4c0b84154860102400300703008983c0d03030207011100546041c18900e41c8913001141c80340110201c6040da40d004855100052034610500c400d05100c0c4240801c0d004404c1c480103207062131038038040721200320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 891068444 1250 891067194 891067207
    0x61003030f110c09091c081608190f0c110d02060403080a0f0f0902092208030406020f0d0f060b120a090512040e160309031e0306090614100804081e09090c 68
    0x54446c00b91101c0c12071030521407404c0c6007851440750510b641044503c100b002d0f00c00095229104240058225185041e040007115052034940e0003c00400d1840c10221784044107c48541400003003841402d4003c0c0c0c042c0c03086444c1e0355000d55030b1303100140058001d240c0381d1908040b610f05501c5240c4c404031070403002040000140c010b000140c040a0100490340c080c000805004444a15140785001c2c2e005840d42e58030b03a15402c0000083c010100310009010002410701100c032090780024141e00c800314401c009280d6035680604651189601e03c0701d8401021001a0340c100151340700f40c032240d0080044e00c031045001040c15078140c1c8503400444034080315006008070300ca0305900030140c50501d418200715120312514054454000c504240c4030f140700e0418150b90441c0702c0c2d001080106101101400b6098840815a04a0003016101402014892035482010340300710182401150846902ca2900d004516a0704007556403940b07040794000300304688880e43d202e2120940c4101290b115564a424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 891069694 1250 891068444 891068473
    0x8040f150c0b0a1e02030406270f0809040501120201120c090b0c031e072a050f0f0301050c070213110901110a0c0314010b010e060f0912070314061003030f110c0909 72
    0x1034127444000070a010101107140c015950150500000707070800c03031282c0c07059694540100c15201d000c000e0780c4c1090500000180c450b40700407909082e41e200341c036002280f108001c100780888813100da603800000c994a01c100007008100006203d050068801d417403a00040c441e01c29104144038079401c0388103030009003480600400404014000552000e44c1c1c0c907100d04810b44100100840c02200c0c4074015a016104469407001d60f01240310a0280003404a890620011403007600103613800d078021502910081091100d0703110f1401201c03405440d00d414143d150f0011900b80760001051242d52051102c2a004255540c1c0240000c51062a85001c7d510340c644690342511a0490300c1d41c1804507a56000e44142e035620280c1d51076411015a103a01c4542c1140000c00c03101d00c030b8410b80414058000044180200a1944030054540800320b47c407036251314210190403180ca11020700044c10300200c5c1200a80b240144c103000c0482c01085511b210b103170000140e0456402d6810382004d5211140101021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 891070944 1250 891069694 891069701
    0xf060315120708210c161403070807030b0c040e090105101409010b0315040e2b02071a190e1e0a09020702150708040f150c0b0a1e02030406 61
    0x412941d40903018142c5010700c0c5580c1c80305004d403600c50080e91041c480551008420941c0c3d01d81c48110101c4500b41002c0100d0002e0302107600400740340c0802c8140108081c10000b903444c1c21a20141e0042440314a951112a5002005000040082000c00001841400400029010b0304000c1e000043c641401c00d002c1483c140e0a134400015491020000000c503035503030000d5411a130308000c1c0d180e500e036034102c840d040501841d5015a4072514264007000e0b0400000390703400070107003800340d9500307075000300301800b410302c00b01000c0c0c8001a40070000501561041080110030300f01030700381088c1070054443d04041147c104a415000051030240b80c0583c510708a00ca420311400440c2c0c0c4264a0700e105008a884442036000320590703107400050810464680a401c240c0071044000c0b4a0346a8500c1c0c908050b80d58058421803510a001d004003080c0da640803c2c0040e070340340c1e007038585034030141d0b140d40c6440e08000001c00c0d00c0303680c55403601000e007c025865680255a0f545020040e41c03450039240c200200d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 891072194 1250 891070944 891070969
    0x120601140f1227011418030d050415060306020717040b0304060c052701080a0510030f021503070512070806010e040b0a150908151005010503150d0c03050d08091b0f060315 75
    0x6c444100c00c0640f8901400307c21555003a090b2400401c10f607031641800d0918948036a50701071039030329001c0000203221950f80070348000c0d840341044040540c90b407030b00384100e80594010603413400c1003040800c3c0003440e42da11003504840e03541012070808403041a40f40c025174800c10303400307500c40401c0740505496030f202440d141c0c0b000c82d10b20104a542880708140003003144c3ca0000a11008054002d8001e5664981200030b114bc0d00910190744c0e851320340750007416604101c03c040141140705021070340d0a4000c103007441c460340040c0c0d00c5400000741c0030304020281450b450003a0308550540300100700180d0400204a01c810780ea25072647c01458100014504000c070240500d98036440801d202e808524a006202224800d02c2c10301c2d01c0740c4401000c1c0e002c450009044641c8400300040d10000c10003041c1510007224060f000b07440301c0b4480c07001c042c0c500b04c5040f80c2c0ca4480f90404031280e03400903020305272680c01380070192080034545800c40228841d0391003512501c503518a144500601840c041000002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 891073444 1250 891072194 891072211
    0x6020c010e010507140d021201090204080d080f06040f0b100f02190809041e0204080d2705060f09091801050603070e0103061a06120601140f12270114 66
    0x314601103031300405c05100b050000904501c0003480c0d0481040c0e0780c040d10110400c420309a07455503941c0c07080000a500500c6203020034010a0102c900090140c42e0f11071103810083c034469040d64a01007000020046e00c0803061059036102040030b4981c0703e040610080c0b510540b9a28060246601e010b032070400144c2d4009801e0003074916400000d0b1074082991142c207805c1c4c0340415401c0074a401c1c05265040240030070b100368401701e000610040700049141160f60180c44000c1c448100b048065208181c0200d0340c142ca03802d000040002e400c00f04000e10344005826440d80c1428020000950125400d5455006c41442240704200004081c820260000c0c0102d006188003031410a14040d81d2005200151000d07990300d02c0110035801c0c083d00404074a4004240740e41d00c51020744500c0c4400e4050319036500140590040700c11040d000c03822500380320403020309075080103428069100c8440e802400c00a1032860801c4140394202c41d421504540b145070000400c0c0300440c04021081e10500400a12 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 891074694 1250 891073444 891073451
    0xc030801230f060403051603021003050601081906050319230a0b100e07110c22051005060408070806060103050f0103061503081305030f013305090406020c010e01 71
    0x81400d15000105049002561a075094107040c0c00060200d004c0c0c5e41c4003800500941604d019015406844141524401c480401d100748940c0021000c807003040302d4490204820b100418a0140c003081100d5282c081900c010031102e0300c5402180c10311b400c60400c00801c050004901c01000591408019141003808198034280e0401501a41d201e400c10f2018041011000108086c100d959070118040c082111920109007000500148800034031100c184160150681480551414801450280481070304000d0290740c000c00c000020b210207460b81c81d85803051000082c01c0d85504020f00001c0180401030450b552030326116505065005000a0405107090204040703543c4c451916030660f07420180006d04500450100000d813401c5800241c1101008201c01d1f03c2c8950480301c41c3c05030380d010b605075208081d407424400d098400914104140e070016010900891841d00142e110303d09801c14500d01c480e07961008039211200030746041d21050340004e01000c04000074080c0d042c151100380d0080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 891075944 1250 891074694 891074729
    0x121e06180c0803090303030403050c0102120c0c1509030d0c0509040f0603020319020d08090402070b0406150e090703030e0a090e0c090601080405070923090a03110303070207050103020d0f0203070c030801 89
    0x103506d9100040c002801c1c40408208801010009d6050b41d80000c1d494203d07403580c1c14020306110b02600309260046051244132958a115180500c02e2409000a10011414501d840c01c804003d0244e08983c031003000010305c5086103580e10360041d0780da0240e20441c0012100d0540c0145410701100c58000150348071214903940068039502200611542c01840840d19154004005000791083c4240641402c507907400344400c1c41090344c0b0100180034102e0040040c0c030345e64120050189070441c1d0050854215280800109009114200030302900a00c503201d8680c80d2010300c0c08030307402c0898140742d80d404940d4240342d90814000468104000342030449492400b55038142d59105a0700500300c2c03280c0c070764540a000070f4028440504203c0f81c0700802c6858a404205190380306c0c06244154006004c1c1c210000700c0c0000031003224010362040d40a805824140001580694050404500c0456442062400015041c40618000c16655981121031201401c00902901e4181c201d000a620820100c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 891077194 1250 891075944 891075949
    0xc031015030b0607030908060106020106120f05120f04231c0809041a040f090c061d04020a02061501050f090415030606180c03020301121e06180c080309 67
    0x602040311540468500e940404200450190441d4a4041d0b0840000f08041040640004140b826103a084007147e9181c0c1c0c0c0c0d039000b02e00b0307038840707110f070f024940301c480e42c4c0a001c82d12040c070084c00305001c4ca0031610040b100610303034582035001c20442400c0040c04130303060040180020402d601d0219800c159041ea16840c0000380000a100c42010780d00311140098004020013902500c1c1002e00c010800c0000f403028001c151040340c0d603042039500c1503240091301d00303100c00a0301c03980480c540c002444441d49402c0c94820390349000842004a002408140c0060550780c590004242004142e800343c03141d801c00c07400144140b0030760b00d0081d06100c400c2c0f103440c071480883c0003a151804000c80b4080743c80c00c001d040c24000c0c090030307400140426052a00100da01801c07840d02401d017100b40030f000c0140e07103841e10045080740000c0c06090400b1074800c00810206501410101495110322145603070038403969038030b804845241c030303203c0c050819440811040c80791f402c00c01303401000004003035031a15042100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 891078444 1250 891077194 891077221
    0xc0307051b0f10031413020315041a04030314040804060e0312032701020d0501061b0c121103010507180605070b0c0a0c050316060f021306030e160e0702060c03 70
    0x10b116000b51001d035009030b540c3e0300ca07030088032000d00c908503601c2150a2040040d00d121080040c2a40240f24001900031507003920b4061394400c603004401b182c0215540700c3c10b881c8401d0b001d0300942c1015101c154207003560990040c1c4038021440f61021603503481c03908601805450100ca070b8280f1a40050704811141651001120380c041104148142181da0b800d00c480035a501030a841c1200398804104002c01c1d1a859120605842c0e10b900d0b6242000010700c507420104044035002003545039038203030400c183e00c026150b45403c1c82c0b140032801a103228601c0400e003111802c80b41c1800045136140218000c5602c400010054001d6150091034502c0c10b031980b441c0010040c041c2c0e4014400040c0d02130700e56100c0c0840c6540940d0141c10307030f680c030fa400c40101442e0b544841e50540d8042c0c9800c0241c1103802152084a500071181807404c0d01f0140780800a90042c03140030307100c040c45d001b114030002c8610001004035001c1c100292a54007241000c0d1002843c00400600480410b0000c0040c800382c1d00d0f0050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 891079694 1250 891078444 891078469
    0x90102091011011d030301080f0a350c070509010602010c0e0f0d022d040e0c040c031e0f140603071203121806111c0506040605060c0307051b 62
    0x200044100705004540703006111101110130410703880300010440201c040025412500500110b030040404110320315107404442100070050f00e2000c08140e003144d4480c0318002544480e5030b2290014031140e410080c90b40c0082c400710f80982008605001600e00203103068058410343c402045000f05d0b48601804da0180da048642c4128200c4000d501141e949240c080c0080b43c0c040d0524111808081044000d040d2468a20b00c4104030b0000010705230900f0720940b00c20b01441c43c000c20f1005900014440145401c60941d4101500c40303141900400d4a000c003084004140c0d103001a2840095140100321100c000004442002402c14800c1990f0000340b0348080c2c0342c090582e1810030380e0700d190a032010070902c00780800300c90030181000c40c2d131202524000d8409003e44030a0080c504290a184203910417001d00300b40c010000350311891015030310f40c0100d60024002e44000341c4a0b4907080000d00b10381000c02102040d038000644541000414829940c00034002c488000504258000040d001d10408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 891080944 1250 891079694 891079697
    0x2010509010b13110702031c0e030a0b0114030a20090109021801050a1b0b0f090f07060e03011103040501021308030403030f031a0406080321250918140901020910 71
    0x8002038006115002c0c1201c5030246d00804075111043c0c03040030030800c1191b6040200200e000314040c2c00781414041100d5070f00550000c1b00000c90703801c10340150205502503181641600c60003204100149902c12800c682900144043e4403c421820402a103440140c00c850525401840380003014015100c2c90101c041c0c090901545a40d61884115002c0002c4640c460810140c41c00070001d0200c010321140c000c6500407004030740765840b0344105660342036003014503c0700d5210740310802404d8811031450150b0a00180042600d01c00201e0500c1c05400584080d07030140d500040440c4503241d003040000c014040342010318105031841e1800b41500e900022201c086c551240380c129024003102007550b145280040003001079503110082c580d80e0f50000610000240e41c0026104598200600150720a00034480040c0d501c0e500380000034038202441891744140441080c0108007138140c02444001406001000282c0c03496820b040c040b002c501401c1b0906030b0744104a000750340c0d00d6451450030142001e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 891082194 1250 891080944 891080951
    0xb0114070807260d060e15150f070b151c06020f0706051005041d0a0f0201091502010f060f060c0201031d1912020c0603010e07181502010509010b13 65
    0x142403c0c011080d515007007008000d5003280c102c628441e003802422640f0128002000220b0322040400d050100a448500404861500720741440c642a044e41d041c101e4011400c90806406400c00750917074002d0401152070801d030a04100c400d0840d18030021280104540740400b588407040ca200512000f01000341000344c00003184005040c0100841e207a150340204100607601d0910441e0441c41580d014551140341040c9148074118802c50908007040c030702901a0031056031542d00d140e000c102c044412414051500c40010382d108015500c901c0c05044d940000c03844007a800d108108507040c81d00801d110400160080c01116440001c810303003a542801d0004465030b10070002e00c0d1031044c00c0340d01006403082c8a1900042d0620008026281d840382c103105c2c2d1884500903060b03880707c0c1c0602c43d0341e412140c18001048190101d003d40390f001000ea042c060055140100321440808440d080f4544d0050300901e20048142d091045580c00340c80076000f0441c9850ba0070024030456a080c6040d44100d49 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 891083444 1250 891082194 891082207
    0x5041503050f070e0a05101d0406050708220614130c1e0b1e0a0e090f1302010813020a06050304120e01090b0d02090d0308010512060114010c0f051f0b01140708 70
    0x464240c4101501440e0619040003449445043e8231240842d0308990240c02c06c000304004c0381c0680c0c92140103c0b0703400c0500c3c4110400c01c552095a0b040340d0002d881c501d03191000800d02d42201000307203015a8850030056840c010034180142030224a500042c40308042d070002e030b1b400d441d60070f508000b9242a00e0f01c25a4620b610300e07554449142881898106c180700203094000c0c0d07600009940c8030520141c1c2e407080076039208006003031401011610305940c0301c504429400198452001650b1142c3e800e200150706103290703004144a080241c20080102c0c100105000c2801155500e49800300312614044407a9400040000d0190704a0311a80d16061f0020902c0030841d0a660140c4210501c040c1c00d02220b82c101d4203000701082028443c9d6409101c1c0741868203040c641c0071030f07650306a40000301d111006070095001190440955141a216020540e2481c000504248800111040c00d80c001c500800412481d4070111120118294103010201207280c0b03c5c90303c00303404d03281c200740c010b03070b04a40700c41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 891084694 1250 891083444 891083461
    0x2907030b0d02090c0a020d03110304060504030c050a050705090f10030215070b0a0207060b0102070303051215040e010b04050907060215090f03030117070902120f040302010605041503050f070e0a05 86
    0x4034140c1c0003d620103102010090071030656005800300c203030142c0c2140c1c0d008400da03006504072000f1650091401d00100300041c0441d48503040550061300c60706d4a100c0030a1143c480c0e03418407459880440702a00003a0301004540340604807142c21500c2419002014144481c040c91400c04900c0002d018401d1a03a01c1294182c0400554141c0354201d09005e0440c0340031480e2800950201f070040350498500208840f40e03500c0004e0041c241c0b81c0c584c591501c1c0c0f0040c4402c401c0500c84c001c1c8541c0b10000001e800c1c07929619940203c03a0680305450000c104006280304200a40d50010001078181d4000c0000304400307a80042da49140c0380c0c00c0c0c20a148561039010f812424114078864000aa00c0700000000e018508450841460b4440e4816038100075166400d050692048401541c0079800120101701d0410280e14210707007080c868000001e2240e9150046030075246000561203640c44800f03800c1017030100500c0600f80c0c9449185c040d100c260f0404046143d0004068810480f003551640010f4420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 891085944 1250 891084694 891084709
    0x30303240a0608061009031713030812071d1503190510030302060903040501050304080a0e04061206060504020c0a0813050315160809100c02030d020d06032907030b 72
    0x5001e4140200152503920181c00b01c072040d5000c134042c0500001111070309204444041c140c03984101500c01154441c6488965500107020542c80300102c02000000200c004000300b000741500c4c02850303c07620709070b030000e042d114132a24131000315101e04142c58440d5a4651546c020100c03000394140e240e44400d0018210034101d40000c0307216629040500039403092010b00300c0c08a921a03400c43c0c03465550707401c20607120300451207440c0c085035080c40850005801c240161480d400546010019014000001030a640d8154800325026409200d86010300205018010250105036000d620301010746280a0391440b010f000a13201400128028852a85101204001b0000242181d00d81a20003205526a141c1502c08035001809541d0303c84465000300c4049209000740d10103040030006d000f00010141c9a005002d2046000c10800c204480d81c03148082e0100000c800c00014009086150811040e03509883c1c135410308440c2c0f6002e04c0425250040182d0101c698903012410b0341144020403960b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 891087194 1250 891085944 891086011
    0x1060c03050c0a0309050907020307120509030a061b0216080606090417120f16080402121f0207030e090f0604020a0e06160219050306041704030503070c15030b030303 73
    0x3034000c1c402c044061640c00380001003522004c407850303e101d48823070394207a03502d00ca8008004d1023044241e0400c003490740540c010382244032024041c0c2c3e40d0707102180c0d60402280c40c2c1c00b0802d02221020b074103000c052039042011124a04010f406e082c01d090400e4501e81c0d4072076008240521a818103000078080003403045400070001500c65038036443c1c0c85001c0301512003e604503644424122040d00203104039207031014200481d0070380e45440101d91110740912510f40034183d48111a84a00f9a0580603980f4200022b10203c80c280e20041e1910703210300c2c0042103440480c0c14284185180d105002c514240260342c560019001c0b140142e40704100702007503429481d4100040c2e800000891441c40d00340320806642d0380e030b510884081600704004d841000303e0020f580031351354041c0e000c6000034002400b04d42c0c1480d80032900c1c15085007010ba90b0b59883d461580b00403004c0310507002002c420030041d41c183c48030946002c0c1c141400c1c072400e414080030a0b62404018404445055404030303018010300302100d4540c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 891088444 1250 891087194 891087217
    0x11030112050723181e04080c0d0207030b010f0b04091a0d06051608130807050f0a081b0c060703180b030c0a170423100f060509130b01060c0305 63
    0x40c00c01c1049552403440c00024503d5008065610100d02e03482c8030500d40904c04c585401d800400140340c1c030080c6548080c028421030301c01000f0400f0b40080c440030054407102d81500c0e40102603441c01e500d0640310501046c0d01015582c240c0200500044c0711003400d84054500300320300083c2d044548900c2e0104046c41c0d64189401203242501c280c280301468202500c20407641e080703e4450304a07601c08032180a01140c1703e841440003103c1c0350001500c40c0000b000054024000c03154400510b40b081c6080c00003500d411030740b08000044c004050301d410780c5e20124908a05000e0a13050091901041c060300c20b0060007000c0101c1081c102c03500208403a5041c000d42142e103a02c948a1411008085c0644c0c0300178495800714540043d0090b03682da12844561059620010308840340102c0c0015200290044071006058000d5200300713002c41900e4820751881c401c14039000301703d1504e010188219048050503200368819058a00404a4540c03030129044070410300d440e50021800d401c0c2210640a0390301c02d0072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 891089694 1250 891088444 891088469
    0x40f08070b1503011a0303030c090a090f0c02060108060408040315020d11041d04110d0c080303040305030f250e010509030318091321030209030f0d080604110301120507 74
    0x140140010799042054000b82c008000d400300c11a400321a01c1c2601c5c19240d45030303104000180380c440110000d4402c0c000c02402140e020b68860701c0800c1901c200601e488500e964603048560342c5641009810300600700b12015000c10304054031844010b00c500d00014029000c603558810030f480b1141d04a4000c407039502810069400301c50780d019400c0d4801d00c20500c00010303181070b0070804082d1000440c003540d407000400c04000e02d81000d02031040c108010a4502c04403012002481100034030095109511030b80d107440d900c0ca08289180000c507009002801e0404058810b4140d10100003000c16180e074280c20300c010004044d4004031018820381c0f8002e42c05000c0440c00541c0842c2810065a140000f150007043c941c1c3d0f030625403202c100c0d0359040503001260040603010030030f400d48038200b1258210700c0c0140c0780c0000c02000c40d00d000d03403810010606038403105070700441950010361103400c40001c480500c000c1c421150080143c0c041802019084859852f481041000820100008040d5445500c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 891090944 1250 891089694 891089701
    0xe010b18010f05041a100c020916050304141c0323040b070305041b080703061a0d060509191103010b040c020d0305060a03060615020f01231b0c07050f06070b040f08070b 74
    0x920310501c440b1f080f4040c40c008404101207141c502d0600445403601e42c0c84a00f596a151501c4034692107070710180b130321030052000c1c3c1325181441582007121511151000700c0d8103a03c48070318208840e0400241c80d0806024000d01c4001500741400f160401d003107140105090f2a207003000c085040e20301c0170044200341e103180006800e81c1c022441c0c0741140d0240408200c02980c00b02c03c01d030707080111018542d108100c4054400080c07600c0c0c0c4400d030084009021540629401d602680e00110039641c1551805e02c0d4010b0540e8030b1500b4041c2410384d21041e94140302a054041001e0750b20030149540005160325480010100e8484500303401c02540c0103041840600d9541d0440740c03e01c2e800c0d1036a039006011b1006643c29103501401088101c03e5000304500780ca181c075210124003520040d02003003407070390824011f0094415160161492040040144c410140313060100242c01108a4049000324001d01901c804165039040d510380c80f076080300302e4581448032494200c11134840c0201c0103048440c4502072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 891092194 1250 891090944 891090947
    0x70f060210060e1515090603070e0f010c0c050d1412041502161502031c05090106060c050a08070302100c0306030b010602060925090e010b18010f05041a10 68
    0x1445500350391002000340ca9152110710030405800c8a82e0100d4140400c030382d03005400c050200c0304030810b88040306421b0031149000614960300c243c569000183d1010124030f15860040b00c46e0407017507024201501da2004655600400c40761a00c101340c86507041007201002d104403016540a801540410b9540d50a450345081c119900540115001c0300c06100740107518500005101c1044e0ba02005d415980602d480f003045440c5d040303a407001046000c184698452600300d014219003c1c28861404aa00d1405441060845070507901c810200440d8511241c042940803d040380425000045c043d6203810724103003a454a00090b8204041074603114144103d154983d1040056900c00c40040c101c50b641c59004990381e0109661032203450f0010f01040842d0142100c03144111034181004d29802d03a6500100c0d412143e1460415070740740d440d0f694031221072401e09410b200140704840200300715410901e61210f00702c01402101d0049951311042044040c0b05c2001d1411301d04c2c02044081c00b80bc6a510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 891093444 1250 891092194 891092203
    0xa080f0409021204110d050c06070c050d140f0a030504030f26090102010515011d1504030b370c09030b07020a0308150f0f041409031e0304030e060c070f0602 69
    0x40c159800d02e8016901d0041b40303460210140021b0b0450002c100100c00c1408010040d80b1500080754149503400f0005000d880700ca050000641c0640458400d80e4102c0c490135051841c11003140300d407500085241c0c00065041400c1d00d0a83e40c000078412070f070f2001464940c4c884440400442a0b010951540c044e8900801c0300600040b40c0aa009000c142c60b46102100c0546400c421540447c0310810400e40030b0303422051460326200c3c010000302c0d0a48240c500e060140d071040d001a1031100100701002040e24914240c0d840d4800d104005001d402103203504031441d50b04400c0c0c4c10600b580c48219203068140329461400c007440c1c20158210b03a50070018800303035445041440c1140410540c07800a800203840c0344004c14404000703821662000c107103004218405036103605055015649241b500049040c04095078800c0451400440c0e45240502c14403002d0b0110044140c50402d04108010000c4e602540e8031b294a042580c0a640f1996131684d02814910140c00848001c40301c5240025025070008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 891094694 1250 891093444 891093451
    0x5040c08010605031513020d02060f0703030e06130b0a09051c030b0405090303070e030307140601081e0312041113151d07080718060801030c15020a080f04090212 71
    0x4002c100d2076550f40c0034076886001c02503040120f01c100100051403a8422078069a500e44002c00ca4210000b8550014403503170030824007280c981d540401da1008054051040d480a0301c9060700a128914001c8511100340580b040e0043c0001c40000c0440d603200f107990400440d143e4008203480c010548880750f030455002041003400024206003503280c4608007881030318007070032200d4080c514556032401c00f0f4401041100380107415100400c00900420016102d5028000c01000a0440b86d454401d500d440c1080c0c065192034102d0404008210a050004c1250082e45010504800700d542c1ca0038100d407540f594850940d0480080c802c85203044101e5841030320020550395460340c03003545452003003e60321820203000d4000c1500f080440c00341030062062660044140c6451482800c58841d040c8000d4400d074880c03000724482c0c0d0700500410560040c580094820950741003014103031844001d5a03180003d4010300881c0b8002181043c100f03260003228080d05c143c100a542e61300408140c082d2021b03046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 891095944 1250 891094694 891094709
    0x303010308120a0507090303230309010609061a030621010c1713020d1e0f03030204060f031b0c03021212010306060e100308030603032505100606120906060905040c 72
    0x10010703c5080651003060b024000c0da40c0d034030104c1c40c290756040e10640780d40800f0b003481c4c01c0021900460031b03840600a62143c14414008200c1c103143c412208241c666942100e1141d03800c04420200b10300001c800e4a0b400382003182c180e5590509003240e01c409260504c00c0c5602d5500302038a0381002a00006180c0314603080010105d6644d48801e0001034030418171000030350110000307105002080302107503100c403c0d043d442201498803501d41c0d140d0043d6041c124048000c642c02107400c00c01c59800c01140049400b003801c0a00404a125a079140c0702100c04007144c0c288100c4030100707401c1c1482002500b12122100c2c5180e03079517542415003110303206024402200c4d000d0a0000114000c0002401c0b11301400705c0f50284d14a148c1103903100d40c40e035000181100d406200034465006903074100040d09501c0e500c040210003400004d070034182e0514070308203d90000301d810890100091544044c04040301a5514400294000d0915012000d04502c0d40320041403800d2500303100c1032004210241c4100c5156 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 891097194 1250 891095944 891095977
    0x90c010905090c07061e180b0a0510060503151201060509010909030905010c050c090411090603010501060e1003140412020f0f0607030906090f1103010e0303010b16050f0303010308 79
    0x80e58104084408101d840c041c007140140b040384c0c0001c0c041e401001c01440540b41440810f103049044030100c400c02c004e40c00000066007400003e000d20001e4082d00800285001d000900d080c81c04502019110f2080c1c400b000741c008002400c1c00007804181c0c4020074003d141040c5190255a0540130341014002e20b8410010000000b030b0402c204d05c19400e4095254540105161a010040d120901c0c115030503103482c020341820623129900c04054902c5107119440d10060650400c0c03e00820314801050305019a243c440103004003134000c0c101c8061004102d07868503032885142d0003180544555402c100c18120040280070801140c45000140d9038081c0c2c4c201c58510300130481d05569940e0107880b8110321342110003c60b291768032036081a048540501004114252941c2e904c640145998000303407864007034602d400340b00345420300440d00010361400c0150300f19411704444903603511812400303a4011000c0440c0d00b042100621005040ca518401640d40340e69490078540c0041d4002881031214504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 891098444 1250 891097194 891097199
    0x406030602092b0219080a03020d0813030207050f0612040503121e1501091e050102010f0635070306020309010c09122a081614010804110a090203090c0109 68
    0x70380c091061407005032200501c41681502400080d11004448645e10760841c240440c0d000000c10603403d0092103540101000100d4800042032900054040c20490b400b400c2c480001c41d07030000d68503040d0b540c1121000704401b079190000b0014030421900d20309160b081c40400c0107110011001e400c444070505580603445c1c0d2008401e810303001c0d0215042400c10700744008a2101d1321201c142002000040c144041d010b80c40f800e85106900e0b41c1d10340a516404041030034031031968203004000313090b018224240805410886a021070403550742041c4c810001d07c404414822811224401c81e08503c2030680704030a0300d03800d150010390310481c1da03206550300348204601040c2c0701e03000890450b9110701c4c42000b014055030307805e603108481d24810740310b54502204000400c50002c04000081078081e00804040d1034800354004030724900d07030011034007540782d81404e83e0b181d82107a165988207078494410b007030000f61240000c1c8090855081942017070300c0030040040800c0006480494110262100480d10ba03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 891099694 1250 891098444 891098479
    0xa1b02030904060f0b030a020f070209090604151109040209031c081e13110102100c0e090a0204050d120203070b1503010b22150803070b040317090c10030b040603060209 74
    0x41310700c1071500c045130402c000707404641d00380d000d4001150741e1080c151520b0100d400142c055001920010048e4001400340b00400a240d41003094840e0320580a00800c586550900390364000e000b03d99000c0c0350001402d070030550307082c0011000c50010403442688240703c400d00502c10304044408014081540d0700c030040e60142444018810f00300a0b501040f1040340c3d170b031000c0d900e54548000c10705620621400d100c100d92a806081c2e801d841c01d40d1246408030310f03c0c080000b50040546202c111510400061001e41c8070a248d01e07459030340052000030902e0703299408a1642c4911603002c1d03d1600460140030140e00409088005401d040303009000c0c6d15560010080859101a803010b400c0101c40c3c80545207602030307000000485000e03140d221425560340c0c440e50442e07101c5481160240d44c03000c01c0004141d0082104c0220701d900c80200c108614142c080c1a81d10845821030501c40c094800700754446502c2600000c4008002403c148903443d40c82c60041e01075048003414601ca400005504070103030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 891100944 1250 891099694 891099719
    0x30807081e0405063004050c13090203150619180c052d070605010305060f0915041b0506180102210d0b040b0d0f060b0d0302030a080a1b0203090406 65
    0xf07480c02422a840c02142d000181c80c900780c84440d0034694041d50189103030803552000114443c038010b9000e400310074400e60030014000c050310205800701c1e141030510b1000d6100001c03d81c900c1541d0341582e200546600000406000f440008240020b10b07408020031490710b0b0505420050107000c1c414021720180d040705441600880701d080d1014170540041e064900d11804580d03400b103005015051800444d916a04143da40036001512264461424440c02d804c05200c1294440061000380c00c2c5800c881039032096208000e000607214080e20054542e4004a5a00480040c44010000ca43c1ea481401d1480154000e4032449400b501801c0508010080c007d040086a541c00c0000d039440c004140c0c404100800fa030900c410342295032041070700030a07241c4034001c0032060b0050340440211207992420300c01351050380ba4514092142d25510600180d00001505e0040005c2d041c030410941d602031001009240002909660340c81000440c509590007200070301121005071014018161580c0c801c6040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 891102194 1250 891100944 891100949
    0x7061119060b19050f04140f0403090b040e01140d0201020a0b220524270f010212010905010902040b0a0f0c150608160b0a14040e15030d0206091b0a030807081e04 71
    0x41f02000c40020040001c04030040d5100b442400c2040c030701c68031607003e0100c6800580040c011600c6180041c002c050a12030a403800c80700c21521060b1509440c3d00003500c61f2001503005004032501c2000c2451200101e240f001d03c0b9038403842d034215a4503a0f0501559030001c8010003c018005600410b880741ca88008881c4a442c5000403003402c00020100c011416580b0200328a25004083c00006600028002030038085440c01c1e040e0102d5041020100071510183d1140c40160320400c0108000d030003000944202d03075018100a2007548086c001500d5887c01180c1c000c01c07400310000900c1000145500c800c05544080c0c08031040e0700014407440039140f8207030184040c0180709000307070321500c3d100c0e030410032103049048001e03400e0a544002c001c1c100d10042c0d484080c081c082a25801e007a040c100032103103081da010b200500c00d60403d00026600c48090000c021448528900c42d16280e80303c0040340c000031540300c44003c3d0790700e05c1d50034a02c3d06604036240c40191030301040400d80b0f00380c007981d040c0d030103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 891103444 1250 891102194 891102221
    0x31a15060d0b271f09050c07020a0b03040f021513080105150312090613091503110301020307081501020102070b04050d020607050f190905031e07061119060b19050f04 73
    0x4040e04d401c03050104840c08906a40819680c03400c01140c1422a03005046c00b407602800000d4840881e441009502289034202110003a024001c020225444601440c0d02603016a151502094500004c01c154820070005070b414600021b000541c6510552106202c1c1d0701d00106a000081d16070300701a118507c42403144c002d00d13010b2200108a1905100421051501d440b0208600b547c58240c40155240108554440760082a040007408003000040300c03801c038118000c500c1c500e0300c440007500c02c403005031071032103224a400c0c04840d01da4000d504550f2410381020f480c0446140c54030b070495440b00860ba1060043c005c40c0c0115080f035000d0350507144100c6003c217541d8140f013660b0700710088403041e001d2074a040100c00e010000e11610144800d522007140c1008001c810001861124500b0480da48400100f000c00341650003910b8011407a000300c080c103110445000c840501707042c0040c01d03001c1c560030ba220500032091149011003020100480300256882c245281c4942c08210454526960f502c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 891104694 1250 891103444 891103519
    0x920030d09090f140702030703080c0901050a0f14041e0509090d1101061814010b090607030e03030708040b0301090c020a030807080417030702010b0316031a15060d0b 73
    0x20880e04183c004940b80d0503420000600c0040034104c115509506842c040e002d40c00c006180000c2c0350b80300b08201e1340003000403541c5180c030501e500001c16900c21081560f00b0048000000c1342e000e44507030490749a80403140756403520350f51103452140148400042d403907000c00748110b0004250038000580c1d44618010700207070440d0004034106640c0010100d144030011b5607036000c04280e07071a001c8034144148080400002e0a0519400c910040c03860603000a0401041889030018a41e00c100844030032301d0f07040c03070003100d600c40e000b010a2035400b65010003021000d0104000c543c0344800c1010718102d80c03c00c141070100e8071860300d0580c0c585a40307c50281c000350340400020034880c0502c841c140c00c00d00c01c2d85410741c80480d018203502a40c1098175990010f0351600c442031a18a070420403011003030091041581341e0703440c541c1d9050490286210782d9a851106100140c80f820484805550301c10700600b54503501c000c2080103600414150803034074800d16000002036012604e2044200e81e4404640304507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 891105944 1250 891104694 891104699
    0x60f061205072a050d170601020f210408030403080c0601090207031407150c03050105271602210a03111207051804021206100c0309050609060d0920030d09 68
    0x1809030044a03000000ca60141c0100c3d500154040290005202d100da903540001d100a04281003110300c0940b10320b0440d440f0001015400d80003042c0b0f00d0f07818a10060030808142d0030480884240201e0740100300b140004030f400828001c62100401d50000441c0684946030788540170901280907556004e00080c3c0001c080c0c414441020000380040c0b07000d1150040724421310115002640d5072200c4000c0040c0e100c50040106041942c3c0304501d191140c00702824210308941c2014111200504401640d403e01301d000c58498001d02040106654080010340504822500390345190310007241080020b240c07000d0010494245002d940d90a1342c81c405081c06030700c2c0c0030000c40d0903400841e00900c075801000c030b40c10701c641c2e20361005084840c00c28808400f1031500c0c004120040000e108814240191001c84900003940f0219040c280d540486000e900c0e0340da400003003005400340d9524a070640303240c00e01e502c0c14405c01c0c4a40c0e0b04880c1c0041c14903413103252a001419100c811141209d00840e580c00f00a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 891107194 1250 891105944 891105977
    0xf0c2004061706010308130306020a030b030717120d0603140d1403070e0103052805010e0c0c190c15050315040c052b05070f0f09050d15090501060f06120507 69
    0x8050050403041451205600d07500c9c1c0c18205c0e0700452111020a0b070315440f20441303050a0011000a10b41d620851514500d00b50b000da07218a240b45030b03444250000a048080340340c0340c0d40309102441e000303072201c28007400845a90366a082c0c055150400b08146807103c80c1c0c01141d00702101d1044a55607140754040e07038100c1c01500074160113820002c1c44000c5440c00001214034048298040940c01000300d542d500d4548020110749001e4801107008008001182114200065800014980714030302e0541540904040e44c101905401018450030a01c0e01d9010455006028500940e804864a400000c1510410007201e4107003201c580481c40031f00003003d000780036041760030824002c44115040c2130008004142201c40840d032010200740203a0340d042c03880d680074422420315820742c00c105840a050000044202001440040001c1c9100c041e2a03014403032904840b17441030f801802400f0786920b40104452098441c05404005901d0402e0910380b03280394000c69001c2c41003526840c117598401c024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 891108444 1250 891107194 891107197
    0x504080a0507030e030f0705010e090c030408130506070602270907030b0d3008040f0b04110a03031e1d19031505072d0f0c2004061706010308 62
    0x10903010300c148210b481000d0788090112500c0c0c0c0d1b1420703010300b614900b0140090001c4d003c2e0f083c11409041e15004001a0544a1045903002178116480c10745500b60201c5a0140038044d800154001102040407010804960054182c11a441e00070098581f80c090b4101c11081c001501c4503440801000807030900d41c00799000c0c004c86200601070340b19041d22030311511a6402c450450340c0002c1e50040400c0c948424840e00e1400e00112071400305440c0c20603488180c20740c6001c0c10050012a40d02c000304d8100100300204a800342009020850699500d04002c0c000801025400a480550701400c100c0940300b0880d00351140200501c188810201205002e00503106207988690b0440000f0040081280d010085146004520340420306180c050801052458024405070740ca4031104202c21005d5800061140c4c0315040d803900c041c00c03130548141120b4880c1840400790140131224003480001620768501001e8050903038050100355500c5800703501d002c40d40c14041c64190000300c01800010103420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 891109694 1250 891108444 891108457
    0x5030a0f1101020a08070c060e01180e10120501090203121c09020a0e0414012702040b0103020912030705011d0604030c15020d021e09010f0c14120c0606040504080a05 73
    0x1048030526a020b94800030985c6c80403d050318002c41000b410001c0592020f4201e454000a1814aa036401008050512481c1034010304112110072000102c0c0300c0e402c2150400201003d006000440c14507061040c024024954203a0180c000c40c9079400b400c044aa040307a0280d00207001700008a140241204000c00c501ea00481c2d1000c250307040020031a405600f024040c13070141d0b030f40520302d4803070050382800c485c08452800e9004000300f034900c010f00340c03c03007040041f40c2d01510086400858607004800911a1f20100f83c0d111000c0c0c004540c1d9a14000b0203003000d039103e42c3c000c10400c42e0208005a2100baa07211407442540301c200050000303403080303003000b00c00c92040c202d11200d444071040150590704090058100700f6404100003072135120110324000c03003d0400c410f043c07030300051074002004501401c1c0d4500c140442e12801404001c0d05246020f01403506a090300c0d98040c100720381c07a900350302c9050103a085100d014041843c5241c14400c543c0030f107034403000c524500302e0000010b407966000070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 891110944 1250 891109694 891109697
    0x501170a1b022503080f03070c0204060906030c0e0f18030c01090b06010f11030a0e120f010606120b06071104150b1b01020909060409080d110d0605030a0f1101 70
    0x89840700828400c80400781c0d000070141c0c0261071072045403030b441003090710041c6a041460880010410200c0c0c0428100c1e0301e55650006240d030b8942c0c0f228001e41e000c00c0403010007074204c1e141c040c00003500e2045030f1002c3d081d03e204002032980281d44a003111028034095031401c0380200b101012414651941810b0f040310505d0300d0a032820010201e40c65421124121030aa03600094117003081150342e8401c4000d01011560700703100c0d810769150903d942e603d000c0c00104409000354070303060400740d940740180000c51281900481d0003c100c03204440e8040c00891188401082c000f521a034041e400c0ca02400070b04120107011141400c00d152580380780f40c07044450a0350820707640c0f1085100152070b0b0240302c0150018042141d901d8003106a0008103803140704605080380d10622a100ca035075130b80050641c0101e0100d402040008450800054034441e0612503003035a403a0006120400c0400b0002c2c01405903410000c01003a990340d801d06460718158903005110b95003140100f400101240300040070301406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 891112194 1250 891110944 891110951
    0x20c030f03031f2628020f010f0905040b01021920011409011b02060d0903020d020703051f060e100329180106050406140a05010c050703030c17072108010501170a 71
    0x2c0f54000051a414540e00c4103c0301400492071080d41008128192598021f10b405001d0300758002005005041c0e4bc02103e1140340c660512044603031080082c0381c0069400105940381d03000034500000401015010040303503140c5503904007030355805844203c0543c64880c018902d0212102c0c01124088020b000d00020307440702ca0400720140e12060042c01c44850440b000180d42c0e2800e050180c07400b243c3c0e0f40d80304115480100140002540400e0300e100c2d41b4003580101c00d000701c04000c00e1014042035017255412418000030000340351100915401100d006841489101c0c2501b0004402d0f1590403510b24111381c124008280e0b080f6042580b061082e05d00400002c05584590020702510f0b00d9500207241250703001c035400d055107402c12580c0300400c1d00b4280418600381a0b5034041e00c95195100207030600c0390b402104414042040e01403111004001a50f0350b44844c0791820101002c1c1800c3d0100c2541101c2c034445001c0d07806880301c18143c9038140c440545c0c1d42d150080d00f620065000381541d0302242c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 891113444 1250 891112194 891112213
    0x121003151406040e0c01050711030d0c0b011a0f0d0b1207171504080f041d1f26030408060a020304021203091f020c030f03031f26 57
    0x220042415030300416048003160880c010805005044806456140709a19102e0b40c0c4d000b1040c00685500740d03030b00c2030801607120a12810904000f8043d0014160180104100d9080b01e5a0088042c00e905114058801c2641d0322522480010a55844280c00303140f020401c0d1801c0242003c050034400e05d13a02c60114016174103001003080c2c451000b9002c106a40840d40c00d1000792041c00703440100307044d040700424001c2c031401e203e4020600c0180c005007403c840024103480f0701050b00c00701c2d00509010408525040d800f1040800e01000844a0750480d56551000880d8404080c540c4002c03661401d504000b1139030764034070a0200000519022441d40701c10040003070341800c05c0c42000c0c85801020401a2a89030600600c14440300c00b03c0c800c401a0000c00c07040340e9582d183d09004c00780440411007403d026881d410243c0c40e1005860500780d0500c0b03100701950070950000700440c811440c612040350b845100c40c4210091080c2c2e40a501c149041e40741d480d02540350079000039100041d0308003c0b10308002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 891114694 1250 891113444 891113453
    0x61d1608040b090a021f09120f0f03090308040305031b0c030601030813032f010f0203390a12030605060904050a2a08070c11151c090b010812121003 65
    0x14030040b00d05241031b0444640c0e003205d500310302d01d0001000000c081e40e000341c429030b031030340750745160048000d11902c1e500d40084140741c4118240030243d43e1101c1c4050340c1301e0312420107a80d03903046405981c1441b44100340d42c03004510040b41521103014060f0050040740d0035581e40450340d8010721180083c1d2149618004045580c2c07010030940e40800d80e512080303088041007412460501c00c043c0906000c0504041c40c5603540c008100d52280c23400b07400c90240c4240310f5149550f1640e121b21407500c0d8182d14800c140c58140c0c0412507080303030313480740c81400744038801c1e0b150079419514075111300d5611205c18021501e00d0305058104a40c813400418000540545010710107507405414440590041004407078202a10340200e0380c641c00042d1400d002c541502d6960f00d0031880d60140d58101d01404032410b041008101610a035101c04820968101030a0000d0005000601d407422003524500c01042c0001641180890000d00d5032940308034041c0b030329280320313507039096140e001d03101c0000c10f10800700000c0441c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 891115944 1250 891114694 891114709
    0x30e0d030501171f0c0201061802030a0605030712060207141609050714030403052d0d05160e0613031203090b07030c050a21061d1608040b090a02 64
    0x6816620001015410801c00898241c07440f115080e00c0d43c8a00346010703000c0b00c40810344a1412400502280413a91180103d000d000c10380e20404120b44240340000c040300071034001d1440749514141c2003204507918400c050b950031b240e10540d01c0d0000e404260002144541e00240f007041e00440c40060000600407446203414030402d01407002502c0004140020180350007140d030403030482e2803c00a8281c80c105a64075901c0f024000509220340081c10303c0c01b06402d41315801d003d404005283c10501d01e40f84211003aa0311502c20512440c1c60840014840071049502000246080c1e503107843c595981014401181d22041402c0300c40c0c09108800000600540304100d109002540d0214400556141c00441d00074090019401c0c142825041c0076125801412b480701035500e403a20780c0e50080389149082c14652600144000103052100201e168600380c8003501c00c8410b9881e50401a03521450b0311541e45042c0401c002c0024403680101c3c01140010082d55000303910303c4240e402d50811a400039200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 891117194 1250 891115944 891115963
    0xb0c1305030d0507050d030b1c030c1703070921020114070816020a090b10081e0a0e120f030411270411030705011709031324050403050d0f030e 63
    0xf850002e01da01c1040301c28001007443c08460305050000c3d581a0002030004800a1051035801215503d11703c103041c8104c004065541d040014801c2220480600b10f02c0d40d03004a40c0300c3d020408404000404950bc0c2c0e1036062810031022140f51071680c181e004540d50401401c4c031071410f481c1407000f00d0128250341c0c002c0074a0303840100c00450f020701074418881500c4259000d18541480c20080000c1a1a5840941da034600e5a240841307099480001000005508141034142004144200100d044044c0d01481c000080301084440020350355849071301d070384190850610a0350091012034000742c0d58403001041c50100400c1c102d40e444045000b40103040c2180d24036007500d007a0000b80010300074000414290b4010641c0a4038002d41800e00191a40b00c8820203c088000841c5c001a0b5100c014000d41d4003040e00701c0030036016903a07100000e80307c080e1040c5150f02e5628490360b11006443c010720444d400c070303035104016080540f42c01c2d0b400d840c0126000007a005064031a82260104207052254100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 891118444 1250 891117194 891117197
    0x90c080604060b090106050a0f020106261513030e030721061104080a0206030a0b0d030503180a1509030c062315061905040308030c030109180b0c1305030d 68
    0x31549002d040020545011010303860191150800611a1950013012580c8000392420045800590602c0490042c00103074080c000c0e00750b0003850f64012140000c180c94913900041c0454a565a180040101a0b101075805a400c0862181404000390207120128900b540080c203a0b58166a54003403d8200c0020a40c3e050f000180b0000c44400c12250344544030b07607409200c0320603080904010015030742d202d21400103072040902000040312007400707400100001a0191000207070321040c4ca0054443e070000d944030140210040c81507180d408000402c040550740041e0719400000000308503400602c95400c05608008040c0e102e0300203d60240200c1c0401010700090001c219000205c1818141010b491000c4043ca0301c0c0c510245541e6250564460410001041400c4038050b0020349151040713a00003003480401104100c0000c684030044c0d0b049500e941c8081c0b1105001d100000804045900001d01010002c8042501181040050942c00302165a54655251a040000d02d0503100380301c0d100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 891119694 1250 891118444 891118453
    0x220321060305300d022122020d0b070509041a010e030115030816150203010e06012f12070b0912180402091507060911031b060a03090c08 60
    0xc2082810042c0d11030080041c54520940300e0b218401c40d440609071120360b84a02d8000c644541000c4069040741c401890541d04030401041145000341d54040403a6500c03a81f80b40c510001d03180000c1e2020002c01d456008041c1002c989655031000e03174403030000c1c00350001c010050040156944940c07041d1407141d1750514101e13a41c1c241c010001421121410040d80c041e90400121304c0078038103c49144070580b50f012001c103403030780c2c42c0c3c0d1070030201150b0458001d012400741440d4004142455070045060b615510101a004d07030342c0000544075902c12443c0e150310601410482c010100403c1a10000c00e5030f68015501c0c0d00c8140001082e1a8011450603101701603420180080001c0c200700003801201c0010b60031f030602d0290040450351240e030030849802941c00007084085a5a102840317403401d103180c1c0002d81c032070856041c1f208c0206106802220403c005014560340c9280c0010001c1d031244802414a454031041018800541c00641182c024140c0300c65465000418000140014204140c000d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 891120944 1250 891119694 891119699
    0x7030309050a150c0525080c070f15030e0c01320c07080610030323040b0a2a0311030c030307110111090d020f010e060a0f11030322032106 61
    0x3c02142c10412910090200411a41c000d8516002c0a0000e148450300c0c440d142042c107091003006403060100d9000d90340590000071484030107080e81c502c113a41403070480840b100d20055055080341c041c85a0f66045d80d101059280da25840733440320740b401e00c4140e00a80844441c013a0001c041040c407040031341d0340c0711000c1844482d889040000000814030000201824108440d09441000705800050100580403000c100928010b850103980d101099282d69030302c3c1d135501c0f5260313583d411042140c400076400a070200c0541c2c03031035003080c1ea00c404400000800303010183d400f03448040541041000c1c40c041400010340d2140148041c5220307003a19250511001c851890441c00c480c000195000201818051881d003511010504071040394140d821948508810700141e03031000f41581e141d94840c01c0010300e0714a00f0740c080c400b420380c903800c5e455165545880c1c60b40c450b1640000c0784e580001c4c251082c4815508038540c11a403484074001c3c00d0485d59105622100750054100b640300030710a94075100704 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 891122194 1250 891120944 891120983
    0x90607080913020c0f2a06030a060806010311030c220209041d0f060f100e13060603060c141e0f071202010b120f0c060c070f0f140904080f07030309050a 67
    0x51b41d94120080040c800001d030300000d112042030450034803902626011000030441c1007903a00110240108008031181517a603461b120b44802455046513000e4000e40706507008030708180b0704540c400c450542d01410000e4941000c0d00080d0800184e0a511034bc44000c5c841c100d0820078492111515135070050944000303400304091600002414000d103510005042126850910704c500d81500c100c5155800d494498045a40c1c0c8011030b000e002c3c001c03600e4240c3c0002000300310303031080210410035110310929070000b00a0000070b019001e038041c6040048542c9205001e070700d038014000f07001e030389075000d0911503035458400d52010f595581d540036079519241c80c00300f464111001c444944029004010940c0030602d00c03622024003100032801004080f078034120605007070000a0203050011040006155a0000641c00c1c1a00344290b0180c4083c90380341d1030300e40c108514014426074122110a00e00201203e000a2541c0294416001c26035074540150024900f80305e0f504c411401000681c41d49a0000306 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 891123444 1250 891122194 891122203
    0xa0504020a0e07020c01050304061d0f010b010c0512090103091406040b01050411180a080307052104210819081512190615061d010302090607080913020c0f 68
    0x6442c04007006070030841d62950025129016610a1070860b0322a00c039071034801c0c00341003892100810b183c1c0a204d030003018100094003440e0f00000c0070003400401c4000c1c005541e204a60700c00174009030820410340305a1450350008203104e402c1072400080540c040d46506402810140010146800240030300003882141108540580000c80c1d0400070181c0703811844005100e405003441840d908080c000326603950784000d8a0050202805403036070f03083c0c01e1400c10389880d881c040030042000d44070103100802ca0701c101030310b0545a039909590000c2425074508100552a410100c400300c00410100d20014038040e00021611013130b4544181c54245403000e004103200440b0a1030103915491920346500707100103407000c0a001241040005108107007000303409442c2d1011042c2c0c500109182c00541140c0c084080003030300c001900d02c1c2c00003c140c03000440681c4102015150300c041e060001c080031812410043c0b210820051030b40c00c0c0188410070250507600408004002a00030b402e00c0d1903610303070522 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 891124694 1250 891123444 891123449
    0x120c0d02190f1419030b040f0c0305100b0403031b380609060d170a020a0c0803040f060e121606030b0609030303010e1e090a0c0b1602010e01020a06050a0504020a 71
    0x410140380040003110180d113000e41d0a000e22041d40c01c00e49540c3c850301aa00c0182c008501400070311910300c0c0d50920f08080c10400780301c040081d10701000182605915541c1c10107603960002440c0c41c0a00e95202100c8a0862090040d0f030400c02c102c03203800040003111402508080d10320480c038a000c250090005e4031a491702c402210500c140d040050507501c0300c12056000304c04448140d04c9a5007814a8204580589881c60300050000340000303100c2d4000591010a0740b05007601c04809440b10b00180d01d81c0150700c95050282054501030044034000c401554034a2009002d0780901080244103628010841c0f107a040341d2585a4000d00086515000301a5002c1095502d107187c5030140005c00c4d035034401449403804491030280480ca00303c1e00280c030000d15031040c11101c500c81c10450940d0b40c0301c4514030740413940c00d0b03103415002901a081500352140c0d400b040c000a00001502c0d0015940070722240401030443c0505a00310000030100c1c455240918038054000032075140c0361040c0290640680c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 891125944 1250 891124694 891124697
    0x6030c0c0302070b0a020a060213080d020f07090908092206170613020f18060415030209130230121201030615030209180d03050705120c0d02190f 64
    0x10000700740c00003812802c650044d0006513540502c014100d04080200d20010175083c00082e140d603c8614110004080d940c0801c1610034a060741c05059036208420800300e0b0300e54010380010841310b0400d500c01034400f40101100c500c0d040030100040c0c100964510210700e140701c15400000754003882d104004c00b400881d00c10040391705201e0740d003a90ba0b0b403008002440280041d0380070002c5440e0300e000515500d03805445c1881d401c01c409040515100b084466500880c5400c1c150402d24641020403012240c02801580395511207446031100d2541c803003410390300405c000d480a40701c10542041076000618104070710390300740c00140049040003644100c000e00800d040c00004051900070320014110b80c2e1021002070002c0082c01441b070700e440154800b07507111717140c0010041501080000c01c2100f09410341a075030034051481003901104c00a03258440081c800348910039100110040039034220aa00c61014280355011880c081640d02800015020079504c10b0780000c03450b0401c40704507030103080703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 891127194 1250 891125944 891125957
    0x1030b18090601050105030721090c060c0b060a1503020c0c0909210301030c0b1804020a0f170103080f07050c0a08031b1c300608100603050a060509121306030c 70
    0x230045c010714005103070107200304c040d41c0810b946100c0010740d4418040c02d40e0003032002c0045036550b01d0241c00490f2014050317070f6071121807002400501c0d103215114156940304504030a031075070000b0118004c0d0030501001d4018450419100e40315a100c41006104580c1c0e80000d05c214084400d0a031950b0120140740401c040c0180010b0001a0348502d880090707d04020790544c40310004c1c030881303040d10702e04858280c010f4400a0082e519603030000e02c401101d046621056242c048a03004460070040c244030160405c0e0f070511030303514002d440400400405000d00211040c142d03140c000921416510b6125540f10b610000300003042000b01003086403100301240103890540e0b81d0200c0c5404c64a20420550100b045136049513444030740030084011802010105a00e920b440400000c3c001c2110b8000d85099101c0d190240030018044c1c00340d80c0a80f0b03030060244c42c0030a0643e4030b10000c0d220203002000140542c14901c00c2e0900303400301610400419105a00303a662510f03001a0498aa0030200010803a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 891128444 1250 891127194 891127201
    0x17070503030f0d0e03040b070c060801120b06090612070f140d050a1101030e01020c0703140a02010c020d0c050d06020a0e09040f0f0c0b0d020d0501090606120b01030b1809060105010503 81
    0x80415580c0c074100c11000460b0840044c1800c85c111700c166044090011000304120082c0008a070170b19043c1da107240c03280d181e141d0b00e0b07aa44103500c5020801c0180008a50f1000442d1030800d010036940003103002e04190801d4a403042107031b0404505070410f0004010108007080880c01f5501030a802100c03e0b6002c00000f0031030f0729801c1d211030501c0c03405403171a442c0151010749a4401d5100c40c0080d4511802151104040440103480b80c006100c1950f004004600d0340704400c801103030b01e8454681c140c50342002c194081e402e00c0644054a24103845041088800041c0d9441d22014029004d201d510b005a40d0051540050210308084040d80c2c05030509008000008130081e10880285401410001d081200340c82c0040740c004807604810045139000c2124000280c041d0090000ba1101006c2400f00d680c0f02e4510004544492041d0000030b154080c6425900700b0980c0000a0f101c1d040c500425000740c1c02c4d001c41d449100719032034407851841c0d000c01c00120300130921801c0d001d01424a0b10760320707501307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 891129694 1250 891128444 891128467
    0x190605180f0904080903030d050a09030906033b07080304180603020d0809031c0207180b030705010516060911030d09051f03090b0f0f010f0302010207140f0405011707050303 76
    0x142c0104020b000510000e400c004543d01041641c0c00a07030140010f20003403404100c9040604006075045011400c44d0002248250280c02190500ca426107550001c003242584440c4400000c12070700c40549201182c0c540000c40244808009421070b0340c011035559103084a14045401c484102407906441d1420602c0184d0300c14024117103064029050316103c411000000317040104a20b8911440c502010024076003a8000c261103049540c034034880b0090816071102801540c2d085002c4581c036030003040b0244203541c055005054000c102703040314110005546d0380e0904407440340f03400703a0b18a00d00c1c10a503d03841c0b40400c03080074481c0d05c80c6400c8014a10700400b0451300002c2140d65003201030f401040994003031082e40a1520550844150a0541040080d4908590f004e41e0109081c3c43ca007000492030f0310f004441c42c0d007201c4d8180d0062040390b203000350080b200314589080341d034400c0180c09140c00d56a20350048602074064440b2030130129910030b5669140c80704c030b503001038060340080c887c0300c0d03a55 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 891130944 1250 891129694 891129709
    0xf02030f0a050c060a0506040b0103051015231b1f0e030c060f0628060507110306151e06041e03080703020d030c08010e0a0b190605180f 60
    0x1410080c99080d01c49580c528103030b0359802040c5030f048082c4156810445c62505541040f8004c82068904010200a1000442c00ea0300112081c1c0d0090105500c10421105150b5101c010000c00d441e146a00008540d01207a0800248000c00c010304004140109501c8041c601c0e03800d00100b40740200b8140d0341d4007040300d110800071088810002d42e03d071354502c240c600c2401180c91043c41c46044e104a45460b005850700340300705460039801202c5903a021054a08441c1aa8500807200c1898201c41460000100c80c15405044119a003111004402c0301c141c030304004050103008080009041c102d040008e00c42c076644981072904c1da600c03280c02d2500f65515444216820745032460881500e1801c0e100c084445d071001540010b018840002d00d040515030302050b48940355074243d0b0b050282a06030071040f02c0c262000e0140101c40389800000c2003001000e43e2280c2c90880d03028101d0810741610a04020f03121103903a02c0303440803500000d103c2d034401e91040609030444504451403807644c1240c20210f00407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 891132194 1250 891130944 891130957
    0x2030d020d35150402270409020a1a16030e01080a02030114060c0a1703010f05010507080313030e0303030a020c06011203050901080405011e0f0f14060f01050c0105071e0f0203 77
    0x80da111240421181d50011043c0e0b01c0502e4094800c0d90b41e090b03c980c0c1700d07044440c1c5003000b8031401c20303c40c0801201d1600f80a06104660000c010034810703420b101401504144102d114125601d0030090165028600101122294003039180c17161021682000540840c02c010400042c60384104014090759500c040d00d807850981c20b03500c042d110440c02c1d0125207054614074028069180c92800c031980765a5290095050310340304010026641d0391140159840c0c090744030000c06007282440055403500d0350f484a410340500034070b0050a101c01100209056500907103d4000d5242c0005420b103100c50104111801421018400303051039a85886c02822801208040c0e410002c909006c1814020250021101c1c3d00003590100c10401e143d1200e00001c0c940407104803400d50038000d202d40c0c110720305d21030342c051801c6803070200e1403d40c2ca402c1041025040880e007141404000c0c405080c100800b4803925210743c41c4c03a214078516085118103c0b04036143c0d0709865040062129022000641c084281c440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 891133444 1250 891132194 891132287
    0x905060f03010c090605210129030108060414150108030a030e150c030c220302270613060e0405250614030601110d031e060b090f0102010902030d020d 66
    0x12247c544131600980d081c048a020310541d0004000418060104290100302000418800c0e202000c400740c0700310307140403d118190454100c40e0004000c204189505801c004819042d46d00200c106500107051a42c207800102959101042080d4010740620500705404081c20003440c100e040c068803201c980d01d004240c540c05100102c00324240130350100a448071604024480520340e44641c0b40342480c2155072106038400c1d400b48205841e00d07494140298401900805184200d0340d5a505128814008070058110550781b000c3c00900320300025103450244e0f101d003010348150151a81443d00040c28961b0314200512005010001a03801c020b5001004050300c40980e01d17565a000140d459450b058211142d9010354401210303402d0b45a4480c202071001c6404c40c2d100402d00c500043c0448040d40210605c44004208480091504c0908141c86a505200218510a150340070a041c441840c0360f10340568006c2c40e4014500d9000700c404d800b0740300d4080071038076443d0170100b4110441d5070120040700c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 891134694 1250 891133444 891133447
    0x60114040b1603111c0f0e091f18060503071a030a0504020a0b0708071b060c030503060a1208040e060904020d200a0609050307080d0e09130204060905060f03010c090605 74
    0x508260007044c0824881c0f540790241c0c0c90910a00f4007103051982c80c000c00100080c64001606080d0b802500a1154010050201000d583d070f9201d20001c218141c0024040d1501ca041d4001595001490405015440541c010892030326120a1516050303a40d00030040610664003a40c21904022055aa0000f0720080200c0c4a482e940007050000718160007401040400003070400c01e01280c04014400709104500000a4a119a1542600d00b4044c007484d0001074007484c103200880d118402458100000070300c014211540c4202050319103803001411030320080c0c00b180401c8982000b03081c0c590b2000b010fa450810030315003030303000038401202400b00920140301a9410310840d03000d50f14440e0340d00c9003c3c24051b80b070341c1c45902c0a000c11785030b0303c2185d10030300c01c90401180440000ca00c2d00200c024584400140411007810030406000042006e1240805001c2100c05a5114019080240300300030001a06042650902001c48000f910b858001da06060002d82580d0340700031450200d070058034280c2e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 891135944 1250 891134694 891134737
    0x15010e131109010e0402010e0d050c0621010602070302102d27150c0b220f0b1009090c031103031b16050a0303050a0305130209040b060114040b 63
    0x7041400c1801507641003200c460021036982000c58850f801107000740c07516800100c2d20410807100c2941d1810042c0340340c01040080c91a401c082020304802000c505070281c078054100000020754400b64031501c01030748400810020341c14040114108500d5500e01030050084240040040140b0303102d80b47c05806440c58400b00d500c0c1700300008000078007004103050b500c210f24608886290018040d8580e0a4a00008000c07641d014005a1a90320351240d580b00081d035508080c0d19000070254840c400682440c06c080b00000c4480b0044403440384a120a071645003018a00008111380540082c0700591400a031140865011200038086a610048510314031010300d0109040d8001d808034119405150030030f85140c5800400d410b00030740c10b0b2040c010b0031580d54408115a01c191848080c010440400903801d2a80c800d400240c0c0c03103a01e036030b1303c030107000740640c003140d0784940444050317500c00e07100710a0010540c0e200c1a00006940c004410b503040c6814510f01454902c62054240d244400740c1c80003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 891137194 1250 891135944 891135953
    0xb0f0307230a0c0c05040c080c03060d120f0305070e01210b040905030405120d0f27080d020d0306140613080d020303041104060e19090b0709060215010e13 68
    0x1c01811001540880d8441140090140400c40080e000f21940e802c007a0000c1418246441061000030703d40d610220303d902c0b8040c00c41c0842d031015141640001006034641c4c00b08400101c20400c44569545400d4042c0900030010100e40f40501038800308400300420300900d0b030344590124500200e240300345c1c1c03d41c0401c0000c480202000345001741c0007070420306220280003000c03000d001180d6003079844010754100100925100c00c604455000410107414110803030511403181281092040c81240000c01c92007500b0780303e40d5a0b00e900c80d090070390000c0d072000c0169905000304840d080c2c00d42410b00c080790500c80803c50245801050600904000c1100000c6c010800d07511001003074110207031140b141789040000e403258000c44041d14100d04090010311305003024450b003404c452001f407850007039840d080740108405a5201c002c00c1103544a03520000403c0c1c00298540c000c42c01c94030351603136081c1740080c040c1c145602e007442e407420504400010411907480d040d450340e102103258400c0703442c0c0d00c807440c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 891138444 1250 891137194 891137237
    0x90303080a140a060302040b42030a06060e0f014b080c1218011e0527070e07090905070e0a0b0712140c06130209010b0f0307 55
    0xd40309a44002c1402c0c0084030030ba6500ca0810349000341c0307045c032402c1c1d106810700904105401c0906030580341850001451000c404a5108200b02a204406032185104000180790001c1c2d400d8038200c2e0383c4060030000302c0d40109030500c2003002500c0c2781c5c03100c001c0e01c400070740603907481880c001404c00500312000c2a40d0048000410444920200e00c8030f11203140c0190007480c54000400020507908000304141e05078540c181c5c2ca0402110700c02401c3e50356000d0030070f220f450003005101165902d038400c04188000910310710a80301c96031440029140f4029001c0c208603900e02840100e500200c10820b1580c0c03401192190170350307400307900c000e5494030349641c02c80349440c040d400039440c940340a00340455194030104500c003000048642205154035810108001c0c4580b8a00070044070000e104101014001c501482061003040c00c0c090429007518211418904201d582180b5000701207144011440c1284d012805400d0b00d554080c10b144d40d03041032001510025195400f4002c0b5000c08043c012238004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 891139694 1250 891138444 891138461
    0x90609041101030c140c010f150803070f020103060b0d0504150b012c0d060b03070609061b0602040f061115070f1b1a18010c050d1d030301080d021c090303080a 70
    0xb480d43d4400020703280380200000f80041c46054203103071000800300c01c1010b00c0000cad18640701c003540c0b6110310343d07840d030b1240f50301e1840c02c906164071400e001848102c1030001d41001004664046090319140c900300d0300110340d01c18003403c050301d000444070080c1d03401000f002c485000f852800081c069032030500b085440921080383da0203600c0519081c00c004194011410301c2d03c0940c00c458886403582c0095511100310f004000c0000d00f0001d501d071568011031401c60141e80a002c0061400c1d0b226080300c02071100603000351011555080c2c16864822040040c40491204105d5031090f0f800d2a5500034000b004d501c0d0494104109404003402c00c043d80007042d580e503076001e0b0866410201040c8072049401080b19aa00002c031015018520b41c101801212141c8100356503491500c12030300c0a104c01070901d00d16103152281d0040c4000e02c0848104000d5020f0000d24004203210b060006000b890011a034074451580d64481030b1680302ca541008407201a42c0c3c1c142030842c3d01d41c3c2ca0091340c400900c0784a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 891140944 1250 891139694 891139727
    0x90a090f0503070b01150c03120e03160201020c042a11010f050612060103030509190509090601050a08010605181305011a010210060807060f0c06020304030e090609041101030c 77
    0xd505181003000c00401400310300d00c50302d102e20741a0fa80f1100107142086030202400800c401c3d009843c0003a1090000003055544908000303440c03201d44410a02c6c54002c9040d2408d42e00e050307400c41e4107640e01002003c0d903e00f070444003408421a1807050242c81d0038083e440325012050f14400d18009401070305d54071f032036800c010000c0040d07169044421026240c296081401860f10b41520703104010046841810399030180ca505140070581e4081c0800d050580070b03c0361810300e500001103455565041058080c5092000400b6654105001c0100c80b41303240e841a0710707603032504038108156103a540035651034035020311200801782e031291f40701d61540c1c601d40c0c001002546000880c0d60300d0401404044401c140c2030f804c45040381d0b040d40c8101d04490441c00348a90b1680300890411200b0b01c1030190303807510034291902c1c3c1015001d50f603946e01a600103172000c90100c0e40c0480c04182d43d041c400000c0703030311a41c12100030119040c0754680000c0202101041f904040d100c0c1038100c1c545004074038404891911 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 891142194 1250 891140944 891140963
    0xb0d06110406080601031401141309050303090c030312060d021302070309090b060a0c0f050f0d080a0b040c08040611090a091a191e051f08010b18090a09 67
    0x120094200d9940716020300c1d008030f41c0c40004204554031034400c0d080140440c6a0b001c2c5c00b0390902018410900003c412994840003075440c600c40007070f16000313802480d84580c00642e2241040c85610742444d0315008c01030300aa04c140540c0300010703000b00c0116040542610011020702d8180041140c0140b0711324035981d018000074180e4200350b880300b410800c40304100d804000e540a1401084011720400c4820400100301054480100300c200100710310300c2e4440c42c1103840c0c0f02d60264070141040e14480b040404140d0b048200070075940640254001d488088030b0400515908002c050101c8001600c082c0c4103036a0f0700746032100031000404984d07441d0b50044c2146102a942d00c511006800201010111540c1c102c003202c1a904002003098070300484000340c410200d04200082c049510131801c4000319104801c1d0010301902c510180c1e403040c420250320602c01b490380000107005020182c0c01b55035071820410406c100281100c0316071042c050112045007040e00c032700c00c80c1c034081c24000c64090301e035020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 891143444 1250 891142194 891142211
    0xb060a050702030c01093b0403180803071713170313053a06060e06100f0210020c0c030111221412011503151a0604090b0d06 55
    0x4014000e06481c1d4400c9080300c0c045482140111146140c0f44507d2000c1d5003804001344a412000d001d420f1607458111203580c80603101002034100c514250750640c04101010250b02c1c80c0d00d00030f40b560010b401004015031a1003400d503070303450328040c0b85254a5200700c00070415000c0a4003005040004048540141d0100c00c60220015100c1d401720b0400860844070303103000a40d03802d082e40044409500101d4104500d0000340d803000e255141c4510100019100c6812000010719502c5000080c00b103901d0800d038a45401410b0105001d41024070300c0600035010304c1e45032610b600086000b440d5010010140c0c0700e100e602811450903074040302c06941542024018695012450050158144106622200710202160501d40d809450040d400c413255482e0708404036003001c00b49030303100f20100000007400740294035021031980d00d540c2040720306143d82c3d000d000c290a800e000e00f41c000c07515441c198011114000c000b0b503843c070503440740300c2019445004400b407a58520481c0380304a608224244102907 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 891144694 1250 891143444 891143447
    0x21020c0406090b010329010c150e0a03031a0906060c0307051005100509010803180604030b130201180b0715150801090b0703090b0f09211305010216180b060a 69
    0x1001c3c0102c070b00003850020300707100d1072034200310761040441400750611032030072180011601441145010b5035644c9885c10710440340d04081c4030312104801d581018251040180c640142a220f1041c60307070b401012801c20328089948c41d07190b102d400c04811903405a5441441c2d4100381140500f5501600f036020702e40c144815042a500072611903101c490791800310319210001c00071640401e00841260750f00c02d10540e55044614000b04a83d10b6006040900b483d9032030750f81d43d940003000c44028141c0042c45409000315600309410714624002a00300d442281c1c10a543e500f0316024200000d0210050310f4a00c50818140d64418504a0091000040c07540c0d00c80c403140340682103c40c001c5400002c0e0703200190785140310f03105018107103510444030010707602c0d4034189511b4010f001e0400760650040c04042c182c2030f02d40341000030300c04102d101c1d4103840301c28038040c1944041284d4041419500030300203100c41c4014409000b0161140610703055001c0c04883d03580c2c8003c3c0a80c02c1c045e50018800100d10f110513 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 891145944 1250 891144694 891144701
    0x4350f1e0a03020322030210170a330302032407080f010b0a02100204060306080f0c010206130c08070906080d11101802090a020304031103030421020c040609 69
    0x106046225800035a0624025511404540003600513081030012481c3c41036a100101000058503020000d03503034480d000039000400e104d140e180824a584070f040358103042c0302d0900c0c0c1c0c0f0810400080005002c10340c000c0742c8040f500d8225080da0065811941d0ba00e1032601d4484000d59000340c01c591541020080c515032640c1c039100c22003112070410700040c1e600e511490f02c0510410446420b80700c9a46021086034040d00001000401d500070022200710707043c1c05101520040200c0e03038001c03522a18059000303041ca103110040a0481e08004241c403100d9130001140381d080704140e114050703199800e040010740c0d060a0342080c91a401420700008012601d074001000307807403048080c3c48400115000a44050000b00303214059608100b08140d0b0f20000341c0e12400f8002c4400165003d1030b82070794009607001004942c1c0844996012040c0414035501a24011a2980e544011451400c041d1100e040c0103100d0404460002240318a801d00548240007803280c0010140092007203507165280c0d030000d0f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 891147194 1250 891145944 891145963
    0x1030302010c120e19020103020c060a05150111070501081f0608061c020d030f140c1c0c08070f080d0e010b03010b0102031c02031302060f03040605070504350f 70
    0x907243c05000070b100c040c40c443c05080e0a40c8500804081040320040381d503191030b0000990500d43d0074041040190000d1107224031454003103400181034134208250000d00d800e110030702410020340a500b403960840000d82d10090b51070900703201c14903a0b103e911181c02541c8031605000244514000016800e400c0b4180c2c500840046548600200290f054100030080022021b035000c41c0083c03580010038013070740514039003e00915185100f01d1801d40503031001e40c0075440980c50b50b8040605200c48070040540c60f00f00381c1d07007460203201116007510752100d940500f02002e0321074034108040380f0400c481141201c004441819060080c00001007180b4000c3c14031510081c003079401d100340d2184562020080311000003030b080754698820101203129000b03400090001e070a82d1503090440016945180c05803036a04031802540356a854541b6140c019100b002c4d0000781804820f00090020805100c2114803007010b11244825034460b010441c001e80740c1d901c031404124002c108651010721404a0800c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 891148444 1250 891147194 891147197
    0x30a050d23070807022209050c090106110717010f051801060801111803011d07140619050304030e19050126240406170f010b030309040b01050d0501030302010c 70
    0x2041c10401a41c000c40c481c440005251010800c0407400518000300c111b8000040f603100a1103519074441418102c0d05010010340da15805002c024a00d494400c6009000d413149281c840d0861144000d01d40c2c0c1c801507400f6012407081c5074581100d48070b80075488820300340d00c4040c060210342002e02c204081c05200000c0c0030825420044042560f035014010540c10400821107140b524051062107000c1840d0108104d90654890510548071301d001f00211041c2c45112015040c01c61910808200050395807008a000e02e0080c0001c0540104c00c0e6018200c0081c9400c1843c2d0341e41c0e45103070450300c10000002c11360344000c280c880413200f8241800803030142c40f001e80b00c0c81c00b01c07128480414510345101082c40103400f00c007800240c4483d80c8125803a14468000c194060f4520103200140540d250b0350071101410482c03915020503000b00b0000c10040c440820020454251200d000c00c0e1a84900301002d40201d890710914041070b4402d0f82200c141010070745040000e56100c0c5802030203406003040e074130f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 891149694 1250 891148444 891148487
    0xa15020901141c290103140a0b0f040218180103050303010303050c0c040606030c02070e060f10050d0212070f180b131a07061416080402060720100212090f030a050d 72
    0x80c401e5001c0e201f292490900441d07844115500c00031500040c14486428607004041100c8000e01a150f03400941011304241a04800c00b04260f03051142ca82c9000d8208909400048010000f052002c01241d06594062070504e0b668005542c40350f103480e1740c140d21150003074584180090f005a06a0041c10400840d900381c42c80140d4400324002040010f40d0780075800080311607103d8a500c4c0410214141c842c41d418001d007804444c01054003243c014501080728140f0b00c404008030150301910101800040e07080a5000d00c41e45c0280a842c1011406010046c07500012403c104104044005000340001c640788000b203a5161048100e40e042010201e80281c140f5104451003401c0d40c1510b48503980742c1c403820a100c642c4000c100c405540140080ea000301e81003040300c3c0421002d8114801c210b0ac9020b4445a0340126010b00005c942c858a0450454002c6101010a070b080c100440c2c00b61841110040141417244000904052403400020082d1003505990341b03040b9001003139910120482400903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 891150944 1250 891149694 891149771
    0x4020108061f080103021201020406021c0c0807031d1e0d051f0e010b010f0c03030c0c0b01080f070801050903070f0c050402071b0f05060d050a0f05090a15020901141c 73
    0x3223007030780194090f00c070151b00503040b810001c1200070a06200034415240c40c0319000720300d440e00038860384080019130005030484500000010045241481c0314010394000308150006440941c00b04031210b401486070303d503098002c00b03109081000000020030700c8200d600d15224500045c00034031803900d824502e9400d08a000200798028240e07e4802005510340c891124416a411002040c240081206101581501c031000c20342d1000c0041c0a045c404008001480340c40032810300d054280ea00401260381404200125800040b081d18101940329070008e914a0951800c81c030b0505007504072603005071010801d1401d0259150784604901c184900303071984961205034801e85201c06000700c030f42191040013040e540106ca80e00c042d50115100400040c004245003411094036420784640d102a84102444001e00203014454a8402d0001500310f00d044050800130b80300d0101d0884a1030701540108900340080000ca10350000700d241e0380c408000c010180211542004402080030f86c0f220501001c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 891152194 1250 891150944 891150979
    0xa0210020a110916050c0f07060c05010b0901030819020f0d02011401081603140109050708070503160e18030712021f09030e0402130e0c03040201030516050304020108061f08010302 79
    0xf6240166801d0f401c4c8010300c1401401510300390b0008030b501c0043d03c42d080002c0c000b20000c0c0082e2001d4101c503a51800e650080e400c1c007601396004804d0b02d03442049900300400c00910003108a900b56007100000400d1404085416414814441040c0103103003c0c8100b05031460b54194003c00aa100d0804248030b030b80d0301c4280040d80c0c1c100800d460510b90329044001d1000c102c154010845a4a1040001c1050f000c503903222801c113581540628810340c0400310503c030030300d8180400380001120400c5a10f1651900c1d00c04200904040c0601e1000d110388a00507051036803d00440340703c1500200242d003012005440250349545094030b00043e2003200030b80340d1280720341d4045d4000243e0944d852000050880302040001c0d480400c4030034100400b0140011413458000070316129070103e40d089074403440d0034000035040e01e4006001d03001d154041182d60140c3d0340c01805517900140c0a18215105690790004510307880b0704480d21940202c02901a8001c05a1210801741030741d10907100d0b01d2140121495 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 891153444 1250 891152194 891152209
    0xc07060809030a050310051002210c101a0a1806050d020607240608011401080115140d020913060f2003190e0313080601150309050a0210020a11 63
    0xe89200d40c0e00304000340040f0921440185410a103805100e540150f40d41c400103c2d580a12104040581c100440c90b44203510403241d12480308001c7c151161802102b2120152600d00c4840c00589090303860308548a0f040240503444100034002d05400300103920351201b1032464088000700a80f03d41054404110360500150306100c50307a015003040d0400d8419500d4103a04034910b403c8144004000307500800b00021402081d00401088000141508062074206410b0b08140c20a894a80c1001c4401918005060901c012200140075216804d02d45100244031b0f5864600040d42c09407031802803224001c00340301c1c603040f4035101d8a000c000e110505030002096a05040c01d01e103a2000c04440c000c01c4e815100700a6a000143c00d55000542000306001c1c0101d03503c0c0114500e1076440440c02030121080d044c014009004448010300c00c9624095408039851046103c0104050311200c02d9001c02004001e0001e071580e0060000344000d01c0080000d50b14040814241c8800c0a103d10301d20f66420680d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 891154694 1250 891153444 891153451
    0xc06070908010b0a0b1b012409051605040b0f0d1a0324131403070b0f010b030c0307050702031603030e04180203070b0a09120b060a17100c03020d110c070608 69
    0x40346400d10310186d01d07060840341c00284285055407203400c042038982d28403516079100205c2c81b0031020f01608002c0c50004440c40140041d0740c7c0d8103c07030b4082c1c44e500d4101040d41c040f2120094411b0344c400301c0503807000442c01400c008039442418100143e11350b105218101514807029130494654000540004000023488441044681041c4000c5420111080103198201c1c5c024411a007030f2400480900d0b103580d000b0002515607884030b105001c58a010b00301c0d80c60041102c2041d2a0441c03c09010608076448098144801d10800084100454a0502000d07108440c10b46003189015964107015061291496089101c1d51908081002001c0c0b4228100182d9030042d000b4100e080c20030301007003c2503010215020a00014110009841440b0548450200c0c40b0720b505000d00d0a0000c00c1c001c1650317403504408003004042e514050b500d00c0000320903004214001010600d00c006110a50081c800c4171481c80da8281401802a403a480351002802800056000c40310a55a20301c82102c104800780c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 891155944 1250 891154694 891154709
    0xc03030e0606011d06280f0c0302030d15080d081501020318040903170705040501020105060a050f09040201120218150a050711040b130905010c02010c02071a0c06070908010b0a 77
    0x43ca5204c4d0340304800a4009070003c4083c02d45440c0003006100c100200e6040103039000100350720324207809101d91080700454519902e003414040410ba0b90380c00b035140d0186802c1e1b0b030706040d0b9900e80c500b554843c1d061000000c101c800d040d16150b050844008021410480c1c54540120001c881e104c065407001048411041c1c0480c1030407050240c0c04100005400d4014065040110604103400c5500d1b000c51000d020b1111900c4155480b0720301800039080d11801040188181c43c3e50408220a464070300c0e6004c001401210705030155075883c0300507a0340d00040c00c01c807a03240c5d1002c80c80320700f07040e058a402691072004035403880d05aa01c40c180d0004a2040d01e08181c0000c00601080d40020a00111a2100c8200502c007080e1800c0720004103564003c1164000344058031031040c4428082c00b031050180800d56480280002d82d40410301954514440c45290070110390480012600d01d0603900b80c0e4040300c013003019074029003800300c0020102d041600480005500c1d00c080c5540c6480e205018034100d8045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 891157194 1250 891155944 891155957
    0xc0a1415010e0c0423060f04030303141605031e1609090204080d0c03110109121b0507051201320702010b0d0f0609020409062f0d0518030304030c03030e060601 70
    0x208a81d600171240f0310404940150841102240c080c0e6401000c0c3c102c58800c4100c0329121842d50400409a4005a85024480700c044090045503000001e00c1e820380310b00c5003000355a03a140c01c2500540190b01d0401d071150b0b10056021304c048107148480640c50916207a031100500c64a131101d0800720703c41e85c4503c0602c0c2d84500040000343d07000c2c280120340c0c2c1d4028101503c0200c04c0200803400c1d42c814101c12a04404218951004240c202035110800b42d80512403460031003207550b0b4550389075941d00505104140292801304840c0003500540e443c4130f8103c4501c00e07108419500e0702d5918035803100c4800b0415580d000920f03020710500c2100d42180d0300804d07401c20302d545a15050702c114843d150a070703040ea84414811000d81c540340201e807081d5100300000036241c1c03008040d5031700b00e84850310b80d450550140305403015150480310a40e900e54510800005980d1240c4900d101d4a10744901401c480740000f2040100340341c1c104508455190003a01e0074410310300301c1040d150316a001128000e010800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 891158444 1250 891157194 891157199
    0x4060f0219031119150f0209010f081302040e03031605070b010b0a11060f091006030b01050f060702100e0306060a081c031e1d030403020a0b0c0a1415010e0c04 70
    0x41100248030031400b81060f181c102100e40020004c1c1105120103031003c24415007042943e0000b840756440c412500e800440c2403c00c21000204a80d0319045683e0412018402007240e400d1980d240f201d209500410400c052000c1e6501151030b900101c409052081c042c1109540c0039014608642c4066404107030111143e09041c0304000c1074206281d0b801c10040355038903000841c0b4040040c02c2c05800b038100c01b5009443d003140443d180c01d16848002d0880360920000300000f820030509681910001ca50000e54600c0c0c1c4800b050300c6019019010394494484241003071a40d801c460307917141c81e00d030507020b40344d0030781d03584040c4000c0030700034860006240e0013998104a86011400c1c86084054280707008266880f20b038440c0c003058007161000403100b5948141f043c905c141203061034028680703070300080c50078589035400044000001e0b00c5100003046002a40c00c0c00c0c1c0c0d00920004009039488160091802d24040602d81d0f070b030301d00409241d042c0b055a0008144203402880d911302c1119036090451a160 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 891159694 1250 891158444 891158447
    0x303070f030207081b0d0513060e0f061603030b0301140c030a090605010f1d0907030f150f02030f10180c0311030a0c1409130b011b050304060f021903 66
    0x2046503000d2401c0603803d01c02c1e00000b464010040240e04880403031841029201d58226042000c00e808150034020100700403035040c3c11044030801101c080d401d05c080c05066a10104000d06003041076140d00c0b49000a840482f00581c0340e1140040e03020755410023000709101c05040c225401d42b90700c000358103c000001003d4081680043d5400109100041550b160940c0c80405440342030b04201c500c00d00c1c0711403c0c4070440022449403030000350102840703050b0600b4800b160326414540006055040383d40c3d220300070312412580c0c1b0742e584051104100b05d501014608900203410581d1248805844a80410a09201880c0107802d40c0c1044aa03050800c41d02041400181147ea00e04000d05403550aa400881c1e81e00c000f80d4490750040202241c0584288001894441d050084544080090200c031215841c3c902c0000a44440028005180c04881e40160754460018120603410380102490008101c170100c00350044030050f4541c2d2840078185441683c803416410ba500200021111500e404207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 891160944 1250 891159694 891159707
    0x1030507320904111f12050f16050f0c161202181009090f0c0821071403030a06470f0c031213030206071d030109050c090109090203030307 61
    0x103104510381c41811301414086044000c2e101c1c04004424960f9189106041d00104251103401000000300f005240c03041a9121000018203054074190102100516490198044036001134400003001c1d2503900b030076003032070782d8030300000703601840c01000d082c0041c0450070b02c0140034069900820845941c001080110b411200080180da99000c41d40400168209940318402c00340e40542c0a04022181d20305007048812050781c08402c081d84201c9081e0302124102200d041c448648014080d95000d2906103c00038890361039424809000020902c412004160b102d00b01b220240d811081421701240c84101d00e80c079034858501c12190004410f0702c8102008041a4001c0c0a43c034a482d041030303144142c0c03550341d8020114445542e880010030b040200e1000d032103964840300d00303582046440380640e0300944a04025210f01c090240540c00c5180103d410f0f60b03a403820020140c0200a914024140b0030ba0303d802c40780c54103000d0202c65001154021260240c0b00b501600a00118550380304c074407044588 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 891162194 1250 891160944 891160951
    0x12050a0b39031306110f130b040b0a03110403060c020604020111070602030d02090604030602071b0807050d0b1e1003030806040504031e051608090315060109060e0f030303010305073209 81
    0x80d150381796200c030042e90b00140a808013900c28a1420340b0703500310003540d909500e0303942c10101c0420010301041240b01d55810889840d4120b603d0003140c0d1201155420400c0d02850b02300034006070030510034900711a8006440d0b071203a4001d9030340500801d0340c2008035450b16500d015200058208014031545008290020328081c400a001d540c50309559480c0c0034102d800052045400b460f08001c0140641041030000010300f0015004d800c0d100d00d8030000441d500c50486c0024188540180016001001010071000b5140114050130391882d240e00205034414050004401003a03500e070119805081038481c9a201d21743c0340d294120b0400014203520021000c00014004101c010413506204900110551040a100e0128540c0790001c1800701803c00c1c1c10240107219400846040205a80c4d100206600302e034554208414564010400b0030030007040d175112660540b1000000008110700050403804880381a448a00114444031824004048400d00c121099609044000036071a01030000303030300f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 891163444 1250 891162194 891162203
    0x626090c0f0a090f0603121b02150d1b030e01060f0303080408132907030c06050a06120f0528060b0a170109060c0903020a12050a0b390313 61
    0x1c0369550a1600e0030b584800d511444c8480d04c60341d0403c20040c0c0310048046140300da04108205540d986c4801480554a00c406407051803000c03108000d20b107400d412114000e1204c20144110b0340c1082900c2990088100c44400091400e00a44800541031184e542034625860700c02c23120900d181c50449100b50040c1c001d962183c2c0401c44610f000c82e01001c440000d0000b540000746040c1502c2c0301c650700c1042121803021030007041000100013680455024100c40e40084006030b80c1e01d541e24104d009090740d4100712826107820000da410b00c1038031b15466004602c5581156120050041030209070744590341c080211028070161240000d5042c0c200300488103024040d00c1c0501d40d10346025010040032455411241d56948010060140c0ca02440c0240e0525081110a151640d40802c00941032440f9901c901d000154940c1d0800000b44003c045894004501c44140e04014801041441040c800800050078070344a000b052008102c49680840e03001d004507040d503652080d031141e4410070f00412130b0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 891164694 1250 891163444 891163459
    0x1050405180a0b010501020618030910180902030405010b100815010e090a1b021c0c110904051f0908090405040212031c05090304050a120305070206040626090c0f 71
    0x601e042000342102d2503001c0d100e141d8030f65261000190070031401404403890405a654010070b018000422186e09400c01e071410300d00e005031b100085600c441400b00f460311841c515007001a1100e03c0d030f00558011400381000300005c81b10b2004220700d4031490143c0c000030030080c40c0024031402030242e602c10030400605200020f0409140002c0891600711008188030f640c6003805080c0380451480107612441500080c8104115101e0515100d21210013500404c200e855680c400c00c82103404c261841000030303125842c00c0c03e20b454485d444c2c04190ba20750890f0001180c0641d01030034580542031026421010091034030220800780300160074010416a002440d0800b04100030300e0801c0100300704003400302100c80c40030104540d03006403080030f82070f801d60380d10a02040c0050340d9603e0380c6004454003865000072583d580d01d0260385a01407100701032b5100c80b000ca0002807080c0c001852103901c62040d007102003031041140611020080036544611031368000340b4001c4442c181500c60f40c20707131100140000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 891165944 1250 891164694 891164731
    0x406030612021507060216242a020f100608060f010317210c1e0301030803070e1c0605072c1011070311013902011403091516020601050405 61
    0xd50407154944800c4078220204882c800c402c400c1100341064048607107d082c4078800d2045103d09e802440c90884e041290211481c80c0341d10340c02000f03038182c1000b850b402d07100100c640302820402404284900403250145100182d601c81031660306605980c0c0c41841182000840c601c40051a04048170101c1c2d4082001c2c2d09445500e2140e403042c0c8122001e8505a64500700c92500031245414280c400210035014001400020314400589a0094581c600050407840d170100142801426414501008440b404040306000282d0800f41c400c40d46510b4800070003c00c104401c045200c070fa0024100f114806a242e042d07440c1003107900c0c2402c449403802da90880305071118641091480d80c011180d9241444d9101d1540d60040c8044e000d451220740c5440c6211842500030031800702c0d402c41c081006640c04031000c110ba010301c80745d00c8000c4a0320702590b00c034a0f015480d5680c628111080c403102041340c500085801100d40500d6407001036541c094007a5074030b00801c0c0030282c0400303086110380c2000340028 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 891167194 1250 891165944 891165967
    0x81b0f070f0b0f0415020a052d03072604150b041d10050c03090a061104030c060201290f060f0c0d080103060b030c0a1202030f100204060306120215070602 68
    0x103071070040f8011072000d102401d062a240302820306180d0740a0003e40140b140a40303090b004030030740340ca040400031110130040e06450086405960781041e060178800210038800c00681c8140708410521070301c00b0b4001d04540d80020307010103100880c4d004085022021100c00c240312281c001e04922140500082000a510400300d50810041d009209469100800d030000c80301d4079010f03480c0c011401d41000c620311f042021180382c5400d070349400a042291148000e801c010780c2d01084900031a00840280583c585070030009001c0c01a0b42e004070100030380d01230716800d0070350788869048000c040146006441100c3c401480a00e800c40200c8a80d140c80c1070080d014a41d02c244040b40c5504040e541d010328541c11442c14070700b11080d108920740654402d0844034140e40350154071a09a441040320007004d801c0b00d100084c0342c41401100361406000d00411030440f01055000f42c0143d0390b0703585003070000b1030312000c204074489c061440195100c20080d070300e60306042010004007661740c022580540b070070144031503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 891168444 1250 891167194 891167213
    0xc050f21012c010b09040c0e070e0d03082706150f04060b220f050f0402070218070e04050c0a0c170f0301050a09200c01140115081b0f070f 61
    0x3852000c80c01c42c00d40c2c0c4410030710a1142d921018000c407818802401c0c00d84031401a903003a0700030600b00d02503110215903010300a416180420100030300d440000b044ca8a8010411a0240c0c0c4621894240c0c0c40d2180c008a214440708810918400080c000c1da80c5803580c40d107104401540c880d4005100480340510b5446600990001e014888802d503582c100d003070301c400080300c0a1603d8220a1407807500c00d00c00039050b2a0b0344011100104c500210b510801d00000d0000c0c8074084000350f0241c3d498406c4c5554078031071501248a0f59603911600d541c4078148051000b40d803000c8400c0e20a1110412858005a0203440c594486900581081070480e029400090707aa0b4085a0940d03c5080e0100042100c1e140030300c009000b810f100c0300117010122207002c2c223410740c91450300f200d0762048005c11001032005c0d09501c14507254014525082255940e036408080c0302801c440240c0000788180005941007415103104602e0740d0318040f45901e492006c002200e50760304a08000c80310318000c0b094800100703a030402c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 891169694 1250 891168444 891168491
    0x40c1404080d0f080745030215311502010b030c060a050d0902011809050105040b040920040f1416140d0203061201180c050f2101 57
    0x1d0041c265081c10b04409808038003010300e03110401551108010640d5481190301560316680c02c00648042d00c0008040d02c1c0c0b000e100012a800d008010a200704088442d1511080b039000f6560304001104200180e0a40e202d011240342c0340001c030f0039030324003181100407800c000e525003c094488115202c8103000245020102c0d003400507074503034121840c01d28007407080104c1c1040071507104d440d1204010b401380c1140612001c00107100d669919030030079a40560994281d200b030028468500c2c50700d0b000342000425003070144500036440c008050001c3e044c18483c05400f41e8026461850749503025001181c411890290241c1007926010400149046401144d440600714405080c0a00e8554400040c940000b43c19104024480c0311414003001c14400300e0740711000389c0c0800750f80c0395910070206100e441c481c03404521302d41ca0401c00303204000890511007547e80c41843d20070b0140baa100108001c600e410300c3c6403544007040342000426458141d2462002c031541c000045000c64000c02000941d0f61843e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 891170944 1250 891169694 891169709
    0x303030f1e01030f110301110a0f08150619030e0a0303050412090b0f0a0c050d0306061403091009020126011a0c070306020c0f1b090a0b010e040c1404 66
    0x340140903001d1541d450000e181003060030410074540c5141c81d91290750307200030000b501e00c130440394203060a901d003908928418544090381640e998190708004000203008100707040000c0c034a0010800b401300f6250050001900241803e0030010b030f1072081a28008800b2124050694400c0c0c80c25030040d040c0320112100c0d01a440c00a070314905410030b09082c40e16104000c0030092030b000e0610140c44008261849003d001d42525256449000b0a40304080b40d00400342c40c910ac0c10382514141d81d450380240c0d0a6400a680c0c40c0400d125100d0500040e02081e115010160004a03d840009220358460041140145800002400413032034554000754502207510314100900010311240c0003420f00d030b40200100310300b81464250400d044a41710001400000e0185400040b5a4007030401002200030300368080e42a01c94010f00c0c1d183c410002801e49020340d00483c01031000850895440c814040c00f030506031191540341c11144108001047e03480340c91024049910101d0720983c00c0380c0e000e88040d0061 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 891172194 1250 891170944 891170971
    0x5010203060a0e040f06180605042616060c12020703030c1803020330040806041a06180619270c0f21050c1b011a06030603070302030303 60
    0x7824046110100c2e00101101004002031000103035903a00d480c1c009a4201c400010400410394071140d01d000c11580c0608582d091809101c2409030313000301c02440307000c6001c0d24400204407082000e8103000d54080030340e069101d401000e001c503e0343c2e002594044240d10300455114022406201280c01c00c0c0e800f50300195690350710459151300300102c120314031070441c1c1160f0b01e180f0307507800240e44415403041d001c1e14105010b000c8500e04072450299400c20fa0901a00c0d4507151207001e4a5a9211700f16000e0b1140c002c40a10340612039106240c460003410080c1c03007100f000101481598440341c01030b104a4000c0c20781c04903441030a845824030b0003e010014520300110003540360142e03540b542c1800c0d0f0744400d45003843c1d9503019a00440000002451410061031840101000c4404404540509070606080c0010403007072001e0780000f440540b002c10381070303084a040840d0355030890360080d440c074400c0042e0b49845035540c90b000001e19400304000f0308075880280c895010a080d0b130001d0703410025a000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 891173444 1250 891172194 891172201
    0x17120306130609020903010b150a0e06120106270311060c120406020109020906100e1504050307060e010314010b3c0403170c0c0d021801180f0b060405060a1b05010203 73
    0x102809404e2011000f01c8889c54a040081c0a201c030034807a00c0304040074032060341080c8065490b0103066030465021034200310440e43e035461000e010049071041c0b1000800702000c4011046203121000340680b45c114800040443c02481400060f5000c0c010388256440350144070300d10f80107108010406841b143e400828614050f206020103094064131403071043c01c20910550b800c42d0b001d1800c08104004440501280c00003100e90980b61145401868040c050740310301050094006040ba5074079070007130342d0410030620383d0b08105144c58001c0c040d03c2c500707000801c14003d11f4114108c400d40c00311611800000c100108059041240600fa10b1550055202140400511401d5481044d0320f0340e0003a50140b5000c0304150312500c5d240e500c000700d032042035074a02c04800c2d900e449401c08194a1081414101c0756180c4800041802c050400024841c1c2041c05400720540e043c001d4480340040641400d09190600040107220703080552a6410482c1d00c00d0b41c101c001520152501e605401400010780d00d05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 891174694 1250 891173444 891173449
    0x140d090c140a030b070c0317090105040b0612070303050d140a0903020c030601060c020910090203070305041e05030313081e09040501060314040b0c0918010f171203061306090209 78
    0x14800e968030752041d0003103442007020641c00c44810343d0003003152030086400702451405031108031402400b03146904408080044001055100b42d014074001c840ca00481d07900c050070003080d480c81c9081161140c210700e03010000a0b000300c02405198242060125464608416400703003a0002c80707400d0310440d1540d00d04000d168042c018419a50410780151800e0342c1412405000060040704c001d00a031a41e20004441c00c50f00c0e079800b4041c0c400c1c21415540c82c18860310081c0a01415074040e640100c4408140084080b1018901c003802d500c80041c40c11a0707500b1200368090b001541c001d460020742089124040040c0301011380c280c105100b912922115030005000c02c84805030001028549040891002d85a1607882e9503030040d40318002003620350360b005054240d8060351809640000300c1c031041081070344030440100d0690b915100c00e074481640c2c415101c403001c04103100b5600b40350081d45040c002da010300002107500034405081241100052410340d001c950460b403007031490582c0441d41440e1403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 891175944 1250 891174694 891174719
    0x10219021507020a031706130204090b1201051005011d121f11040b070309080105101e030f030c05120708030708070201061a0706060308030f010f08030705030a140d090c 74
    0x40302c544000d2100a0151350080c0500c0f40160a002220703c5110010703180f0ba6403190852200485403500359107550307440d1000c601401c00d010f6014031910440c0070f1001c1ca200144201c505c0307600141400c078100c0d0f2034500195002912004001c0d10078074001d50300d041a0f03d4840140d054443c03100e00034094001c18544907503c40c3c0d200c9800d00703d09d5090940781c2c0d0320903140b030f825541610841d465166994843d8078040c0c864810b20ba01c00546542040e040060403c601d11191003154403401550000b8068410181d00c0c14415020042440d0080e10350200400d11441c15285918410f4003107841141c0a06400c1d40541c000b04c1d001c50300c100e4000b0803c1075085d40003034066040049400203100890134800c11800c512140d62509282c00303404510101801090340007a4000d64101d101996a03081600d50694180300900400d01b140060004c0001d11500000484450680040c0071398102940f601301250a1460a03d800f10501c900f03014501c41201e07203200e0030088620814104800a01d05000403180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 891177194 1250 891175944 891175951
    0xe030c09150109051930080903010e16180e07140a1206091e0f020108071809090c050d03080604090303091a0f0c3103050a05031e04080a02040b030102190215 69
    0x1903003803225410201c0803500110100355179100070681e2302d03000300501103401001910851419031064a684001140b40143d009080e42c0b6082500b445403480c2105c910240d94419080ba4802d0740401c0c0e040105401c6d6410544100b5070080a82c52140d80d922501196100c080006541d01759031414420100007003200041c26440e80d01242245140e425180c07500c8080a1300006410b1210301000111518443c98102a090107102c0b901c3c1141ca03228240c1000619484408517100900804081400e20744881e050115542c907a5a04041d42e40b02000e2101a29892404800745078a6821060005e0001c3c2c900751038441009801c0303a010b00c0c148440301c0c10a40c0c0601805011034041214811034110303213020344000e00750303010355203002900c000c3e0000031000e089c1d202600c54050319040ca81046070106c020b100d15400c042421003055070a51080c0d455104511a007010395004207858001414560406003204100030001800c1101c650345101000020580290058100c2020712041c80050482d841d003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 891178444 1250 891177194 891177239
    0x8160e0904050304230f04090309050307030b2d1303020a021c0b060402030106050a03090c0f1e0503010203070c0204150b0f0a02070801020304021c11130c0e030c091501090519 77
    0x31a4846070101b400741003011440b50149848414540c2814051800c4000812001d0200c401841d42c1b801e165010440540320100154540b401d500e181c80b03019010b4004801d41a00143c0d0551200c007002c0503180c1c0c910b2303400c40a602444540c003000da5039810302c40f0444840c14070408203880f4141341542501030f00034025441540705100610440350701c50140d514084040c240041c6404032410422030a410a45c40007004000a00021882500542c80f0380e40d21690030381c0c1309013002c0d1903400b01400c0c0d00089606800081c20041400e001d454150000550103010f103610000c01c0f0303202c1001c000355501c0340120019940b0000b6101400710750402c400c3c0004d00c00d13580218110300301a800115803100c0c035080700340104986001e0405108401908080e6494010144801103513030b6140322000d08440da55003008110a0986000c00e800c021a4950142a0091034040d1640ea100d081d00100301c06400a94104911000d002c1201c1d01c038001c0320000001220603540d955845d02603076070302c0c2d025581c00341e6a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 891179694 1250 891178444 891178499
    0xe250c031101140a020708040e042f060f37020d0207030218040302070b0d09020f121c030207202103070b18011a10090608160e0904050304 61
    0x5030039030f0110350440d8200300e8040025a0300c54a03814060210301030b03038025500280c4640d0500c000c000000600446205140c0d0200c000c209000c00450081c05007407150300d030044030800800c95184540f40081401d8860020004100a20fa00d034000b00c02d400303000880a01c81d444499842c0440e010000304032a12f2091000702401420355002c0f40094850100003010700d04640f01060406000703100700005811200c40c469202c2540001c0c01c4d01520600038140d0080d4818450082142009088201203400200090000f501110ba40d105c81e614114000e40815a0a010302c00c006007200c810420f40000881200e085004030800300071800c86a40f45050f054003001d007458000c01c1010050340d440c150040500a560f644c3c0301410604000e0040d03c0d0b07540c2d0352801981034202110407403d02504901520f56600b9100d0795a400d8400341d40b0780c020b000c0407491a000084504001c90b256603d885203d14001c070301403400074040340b520401500d04507008d0f00041307020700482340001440300e0450548607030761 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 891180944 1250 891179694 891179711
    0x1005150901140706090209040b0a1a03030304031d150d0b0d0c0b0f1204060912082a0f0a02061803090d0602030a09080c0f0609010c090e250c031101 65
    0xb070009600050484808000401d100c014029941e00402d002c503000740011049207480e103009603e2040480b88030f141d152a0041c034140d1021100150064903d020780290714684850b14156181c113a0290302110030005181c40003000c1d00c0c0c0199001140181a285584035032250440380c0c1a00d0484800350300901c0c02005000200d0b50610008044404140590740e4681c6e20650b055110700c503120188607505007010500003000420350140c000d040c0a0b100111b100c43c0c4025088402c00f000355001002601d0f8581c11044003540360b400e03c0b0802c0c0e0b6a409151810b50000d0224502d900320b0410800960030110402101a2a41151107207a078101006103240060600004054900b000302c00744c0420390105c006010340341158030041615800c0f18200d91180070b0030700340c0c1740d40c0c441c82c69174a08240581b001054103401c05000391100c651054454204e0607091005803c40c0720740043c0307551800b04141d0403003a0441c0030310302e1840c0004c68950f110003100249040240c0b03001030600740030b10b250f8509200d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 891182194 1250 891180944 891180947
    0xc0405070c020603040c0503060c0c100c09170109050d05040f0e060d11010201090c0801061802120115050d020a0f090e0906070e0d0b090d0905031f020904141005150901 74
    0x1071035565048860030b86a8440c0d00749540340c02003d41115030588964800c2c03000c4005010080d00e2860f500800b00c1d0700915000c0d049605131181c40d19000041581d02c80c09101e03070f039a120800541d801c4200c000003071020050312001d2401c0c6019118401140d40068240302600444054502401030f5036026900341c10a05d000c516100c00180000d89403046a82a584e040d031302c00c0d081001d034076802003c0c1364001901c400302103000308064490a4811840c0d50546085160341d4005d50714020391280300c942d00c1f6031821555094000c1c0480707201d400c2050070030064107174201c03a00c050051424196100070400f035901501401d000c2c215000a655004050104030b8010f400041c02940318069142003622600142c01203070740c20506000081c1041c0c0400200314102100107551f4a4409090b928030400329510741c28191940c0300f590325101142c40c25031000e2214400b94000301040317600134000046840603082c900070225015a155203888c0c03242c0c4401c008918005000755849521700030240e1410111100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 891183444 1250 891182194 891182207
    0x18040503030a090c03020310050702061021020301090c1503051b1911010609140a0606170c070c06020a0219120213060801020c03130e010f03080714030408010b030c040507 75
    0x75500d070b9903101c4452a08000d11441640000d59000c5c085941c1002c20140c1d65002c1c200031115000103110342c5c0d000481400301010042c0855960350803c510b03540481c0300085180b907203610203030b0b0550348030b0361610002040003442000500c043c0181c0d503454800114020241d1300082c08060504440200c0c0d0f03041ca03011041220001c01c0c0c4981940500c000e148420b8a512503110b07501d51041d46071070710016001d46c4580181c141a0004e020554959407080117003011907e00b4060180020012025414000c4a0300c0409030840c051710b4506c0e0500100360f681e40750000054001d0001608204404421400c181500000031241135142c0c1244600b0308060124014034100b02a200b040b00c0a00e207941072220752305c048003520140b0000d5540d1580f10f8449c95a0341e20100781809104610714000950f01e4081900340d058a940c51481600c25195880b181e503540c1000f02c040d121036034058100c0300400300420090004000780b0b0000714210600303c04041c184001d1400300d900681c1440300304800543d1200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 891184694 1250 891183444 891183451
    0x3051e04020a05030f0102070302010b100203040b0f07050d0f03050601170a020f0c010204030b0f010b030c041a120a1a0d0b0412020a140327010e061e0403111804050303 74
    0x45406566031980001200d018295100d1034050142c0c3c003c12000c010103400402e103481c0039400920614a1800c14130401400d222001d800581041c0401d02c182c2031080d00030400a05500005400d02155894090030031840320032000c0800c030514141c403074064045c0140e50b4405d40908003460750201d00c440224070f0b0a0b009040401b15075000400741001d4a81c801510702c00740760803002315140c90712890f001a10207002c0d148100807681000001030700700c04403002c591041000d800024185490100c01880d020f48034105110562002d1091b1455441c8032507030f8510400b84003001041280180b01c400f08801084084a0f0082c0c4d481200c010100d410f24070032540255010f4244480c3c1c03c6240422802c02a03242e500170558032454102206802000000e0321708841201342500042c5100c0805814041c0b0307202030207010480700000e6140c07900d40316019128140401140d9590030340e49404000f00c540c003035082100d10090050502c41d10b810400403000c0d110340450040300302e40c20140c607402e9403404001e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 891185944 1250 891184694 891184741
    0x5070302090307060e0d081b06091b09101e060f260705070203070b0702180702150615040b1c06030f0f0c0e0f16021609050414030a1e0305 61
    0xb2419a000d6226128130030802a0012007c42e00c2c0e6410f1090451039440300729400c1749520070440440c680120108a02c070700400301c04c00000340d1075402c03400c3c0305000c04001e085c1c84112101880c0002d6201001c500070107a400160a010550742c00c0c108090f0051907610009400c0002265680341ca52080714600186108900340c80703440c9950700101110301c2d100700c000094050042c14800201071041c1009003000306e10031100790f0b28601e030704858650021400c80e000d0b40142d21003803050300f41c1000007200a820000c044c1180c10b07940060035410405500c10761040c4583d4130b00050182014090743c040400d0f81080c0c000902a071442c0d07071944103041c041c142001c0c1c007200314049001c040040c50030740310008011610560034a0714200100c0400810304a980030b031014010f030440e00301584045142500116100042c0d9401e0381860000c1c00205002082100c1502c5142031403904203004001070040f80820395101f6041d0717003604075040e00c0070070328019403002d05051009100b8021108400c4c6444080c41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 891187050 1106 891185944 891185957
    0x2d080406092102011b022d04093f0f030e011103160504080f030705070e1003060902041b230f070305280504090507030209030706 57
    0x2581c0b44034003402a035107020b0056028210056000b403101c0142c0020381181c2d0701060110110a07480300c42c82105001404140b038007410600d000200644050003030780c6c072036a80c055001030031490705101d10b00c2030701c411145010003d083d1b10312903800f080b01413080144100098103540c844041400041d043c2248600c0c1d44070b05000e00440105416595407840c3e0b540c0400c22410035299801001700030381040000f50340081040b00040c1340c8480c1010f155074651070301c0d1942c90f1000d00e03030100c652041c1c0707130013008414085907200701c08403504114046200c008070302c001030082a078070080b80b102c50004903822060b1980305da000b0400d0b560b044465140b001d003103211500700c1c0c099000d2602c8400300c1000130000182c41440500040c15180f09288252208415942018081c1c4160000024400300d0b0401c0140110301885030050740b2418114a08014074000c40e40319000740c0141c8051000 = true := by decide +kernel

theorem cover : BRFrame.Cov 891007194 891187050 := by
  have h0 := BRFrame.cov_init 891007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 891007194 ≤ n) (h2 : n < 891187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
