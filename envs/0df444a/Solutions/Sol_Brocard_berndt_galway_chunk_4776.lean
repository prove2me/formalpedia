-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4776
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:41:44.617881+00:00
-- url     : https://prove2.me/submissions/1d1c67a7-7887-49ac-a7bb-216a53193464

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 858812949 ≤ n < 858992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 858814199 1250 858812949 858812993
    0xb070f09080a08091203090319110a0303110d0203040e0a0c020f0f0102133213051e011a090d0230060a0603080301050d0f1202150a02070f 61
    0xc0e8a4401051030501421400c40741e0038400980c1504038100381580820f2505100700550410961a00080d00c4141c40f000301c01d024030702e1024074170500502c05076800615502601c4160f502c1c0d1a414024804000100c200e04c541c424540340c0c0c8286803000003110204c1c0e070310080480254030b803000b0300405491148041d008520880304542c081c450b0074402d03082c2e5100603400050f9204451480c00500704020350180c003005500d07429902415100303103406020100b40382501c00d070b00d0014400203880c224840010302d4010389010100010380e0301143d41c000c40010500d00040042e03a88800101010405549409070900203004541c641e0030060308001c0d14500c000c10134041282146070302d00d441d003541001d041c035142c4001900c0a0300f003003d004071500892000c2c024400c1d542541c586084038401032250b10700a11034242184180140c541ca01c3c81065401007603007a0303500701400029900e041846290a00d100103a004c01c1d01d0100070300c00c5608443e800303400c08028854944400f011400f1550118a0171307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 858815449 1250 858814199 858814217
    0x8030319021207050c010c0f0804030305070207121b05150403060b0303042408010e010b1b010608160801060b0412080a11011d06130305120403050c010908071a040b070f 74
    0x404100000140b1a000704c0e9a101d403901307080a081401c1d140004100000c2c815001d668441d6a644078900701e50240e0541030105054460180417445c080040c0d21807042c0d1a10727a0901d008000c0e41d048086c03000900c1c40420300d002e0340c4031010803800c042c4c090403030f41c40030b2000c001c10400503085030070120f422440107007540d051a9691038002d40c03211070a920780342c603801c242c0d0036060900e42100705103001d480c01c0d010740166581001404401c5103d031180e602c00d410389100c0401d45500094003d0405050010180c0d008007180905410760351410f4081c000d02c650810708081011007504007560201e42c180307213090645c000300d500c941c100c617400b00c4210010014013245407862000f090140c5d403618070040741b00640030402091a1410204007034a6a10784074001812980885c2e404004d4410714148100c104249807580e103410340300ba11640c180c040c21035081c030b0240340a12649201074241a4004d445100481101142c100d003202803c0710000c200e03094001c00311300d03050700c01d18250b142014642841c8100c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 858816699 1250 858815449 858815467
    0x311070803030114040e06040245101a090d0302150c0406020d0c2102070e091b010e030706030b04020c06091b010801030308130f0b1314070803031902 66
    0x442d4000d0b0403c41300c8220144d2403c0071402c2603c60045030020410140000d0705060b800101d20070404185109243c00c12004c02602003800c2008d410742928628140600103205909000740c00d40c2158100b0a40040920001d030312881599080f4403001070140c09441c11802c3d1013000860340303600d44240c0c21480360b80c1034401d040c2c8203840c04900412215010f15280c40c5800e41c02032801d024034032040108103000c0030020003d000700700314206424241c02484040400030b0001c1340340020981c004c0c1c89415a03030702072100034080815502107581c107103000c80e80800b101030700541d10702e5403103082644c241c2d00405c01000240c0c4607a011090100300184090301d404001042540703030550640701840302d43c004075200d51000c1030000400b41e0101003800c0c100310329031441c2c8014002c21801485503000a840200c04010056124014030000b54400d22400d203905003140101c011101303002c0111410a6401511180480700294401c01c445c1c61500651569494a1810000c000c0580d0300341034482c0c0030b00100796 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 858817949 1250 858816699 858816703
    0x9060706090605091209060a0e03120403120e060a030b060d1410120f08030c0d051e3d03061806050a0c0c03030b03100c0906080f1303110708 62
    0x20140039000c0400c8190050404a0840703030050001c00455101020300d21128040c44140c5440c001e044403002c0e10791007071040a403481051280c003180d050040702c5084101d500120064015a030244241174404501c0c140b081d03825903000505940d002c00700744060b0910b07900c660041c0c040341001030103180c10b00c8209a00ca109880c2c0d0b421644c14140700003810440c129003071000303010051040307449189080c0101d458901d0070034420503018100040000004403100801e0044805580c0d11000c00c00c090720303117005466070328515100700220420a40c030102e03519076203804480e41c840554085402d40b18000f111000850800e100e0710101c8002e00a40010215549109070320044807200c00e038000703a1265140031001c0340d4000b00452880d6191001403900305502805507081d02c0e91600780041c5074808400060b26203403084001c010028180b81c011502c555200015400b00c40c41d42e101c00c10640c031041c000c0c44494104507281c90128960414902c08a44540f00c203080440c0f0f90000d5402013519084658 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 858819199 1250 858817949 858817957
    0x803030702070608060406030c06051e030c040806150913320f010c0e0f06070204060906080c09160c17030901051806101a0c010203130c05190509040303020906 70
    0x480940c010300c2d0300304001a08404c03032981c4030f04100c81c100041030442d500e404080e4a43c1c050b1004010000c184c4c08000e18180005514003a90381c0704aa440b460f1a11031030b501640079001c2c0c0e144038021135010070300840030b5036014505010010509522552907002c002401119418261000507020840e50000c01c80000351410032035000180c0800c3e08040300c5503500c0e14840b07005140315030385440e40801540b41e00000444101c202210b03400418528040099914081c424011754490714044d40001e04540f5036005074100c45506003540d6111484100b003010010f0b0840d00f90b40c200c40304002d004072440c800c060b60b016140c4651292a021110340c8181800c41d04201d9090701c20303a5541c424401020408980c0d800906c1d641d00060810f4907066402610700115441818200c208103058680d00100d20410703500600c941c00002c640383d10b8886549480845018002d603480d00d201d03000404c80b4280f07c0100d843d416040680443e091f403804050200b2084014000d800305a400d0140000550b04c0900130 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 858820449 1250 858819199 858819211
    0x60302181003020730021c05090a230114040b120402010314090c150705030a03050a0e0d0905090a02090d030c030c0204091208010b030601121d060c07051c0503041b080303 75
    0x4440b40d07000c000305c00c00301d881c00318815805540c014640b0985428134604070b200d5404092400a84466614010410078101508501001e5560002c83d0f03010340c0c140ca452140f43c0600342c0e54541e190314000000c0040384114002d0f0320154004108045e0705042d46030369180c115106240001c2d444840c0340003030b8102c20064540300c0049d00f11180042c1c03179180000700406090130b075010340c80ca40700043d99400c0e920300c14819183d06143d03c500000b074400425a001c091159102e0042c1d410381c1a07090402440920700b8000c9a20803482400800e0466441340309a40a040d401750103109010415181a551001122405c40402412070120b40058896024078240b4921414201503012451341d001317002040160800c7c0d80103d0144100030591b80d110581c212208040400042c003120048001c201c2d1140d0080c501c40940319000c140003950361039400415800f80a1402e6031641101c80d0750000c0c50742382c07807042600000c1c42070010801203001c002004400703d610040031000c055075a0503c82c1560012519 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 858821699 1250 858820449 858820493
    0xa0308030403111b0909070302041d10020429040503100606020c010201050702061302191403160501090918050a050105061c02030a080c030f0c01150603021810030207 73
    0x50104143e08801005205001c80c009440c01c00082d014400b080190040c403507102c5d0030040c1c00708032003034001d0140c41c000d10b8000d442807210102c42100c0104002c445410480548503800ca0b00044007941e01c00c2e5010b40c0c0056a42d29002030141e07e00c0c03440c2d00c00110300408821000c2000151980c1c003000204a0040301c000c02240607440c0903006402d120040342020305590400b003c100400d0380c0464001e80c003128035020900c16440c14000f04520380a013400071514106a2840812103564110321000d80b52001c070110f80f4506004d80889800d55228802c0c03e0101b180000309104801682e00240c0c81c07102100f0f02d2090400c036503200d4a02d026130592065130141d43d0380f803d11016061845100341e01d0107281742c2d09500080b0a03070100e940d480013240041c0c0809400301c1e1005084509004450a0300c10740c146075500c130942d10301d0381d0b4020f1804001c8543e03540140480007802c03e000f1700036a8407901d02e0384d00070015040c0e00c200344401c160f000103201c000c059003000031b10005051003034162000300d18506 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 858822949 1250 858821699 858821701
    0x12180906081507080f0412020a1505010f062307020616060b01121e0b030f0d1101050f0903190306050429030307170a1b03050d1a0d200a030803 63
    0x3208001c100b000b610810410081a003004290710b90800d10a40040d070050059000404170001241230058034100140140c5c5d01c07918200406040e80c029a0507901c8440852001c940d80b460b0a40703050060038400600d03c10b182c1c003030702071204120001e042c1e054000780c11145043e0560240c4501c0542401003102c032135075102c8952883d545c0c0702c0000f40603c5d010407400c00c40c031040c000202c0d140440000e030b01c000045d283c1100f1840c0340c40500c482c00c2c000e190a030480391200120f840180214600c42740d0303c0520742c41d24000410034101900124010f880170409180b80401503080c201c0480401201c00e81450b84031040000d054880344100000c501d80c80158050070009140c40340954007010890034443e50003880050081010040011558074654040d03507030365581000c06584041d00203004100c501d80102d0303a54103041d0000300801c0100381008080003110220400071901c101c035000483e402c01074080c0c5500000f0180c0102402448410080c61403220360700c0001031502485030800c441000c0044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 858824199 1250 858822949 858822973
    0x311030f04091a01050406021f0b060703200c0a03080901022e0b040207050606091b0412030215100513020408120405030f0c060315010c350301031218090608 69
    0x40a03040303140f000d1030310714030301482d01000a5882602c06400724010030f00c0e0010501d9144030f548031180c98000907040ba619000b150030090403a500250a110500107801c008407810180130952035080d00300104042350f12411611541c5035600001105415441010340c82c0d0000b500c4408032540403009510383c03100c44083d85100b60140c5854001040c01140140042d000098001c561561701840c2500c000d4141d644210584450800c0009024480d1b03000203004030303201080200c4141c00f14041d40031201180c400f024070303901051040320316100c80c031441c00c024085850440c900034000c81000c00003505140d16030f4442403c05082d01614050703600300003410080b50409002021200c60700d20040c0403a0325502011900e10b210007054100c0000f6080030b0190941c0c0500d044003500c0360445080709801c03040005031a080785035072640004144400d40b03414005416041200d060340d078040da083c0031580d1400400d452028541c06046030860b5020000301d0024071034400c0c3e0300100f0031213000300350f890980 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 858825449 1250 858824199 858824231
    0x6050702060d0938060105030c0706020d0204050a082109040906060b04050102010e03040b04060e0d0f06050a0b04060303270b030709060e0618151c05090c0f0d0311030f0409 76
    0x90440c24111680c1d034910f5122207413250b0405078480000c2c200169289d4680580c01043c4c40742c100c000300f42c184007013140c084600e055030251007a51020349065070041d40700c0814544e2200402043c502a48802414049050780c03003000e0b080b13070300e0080c04c007042c2a80140c0e11181580c00b00d030004180756a011074104010740c3e09002d2041c3c5e00100c2c0c40514901810650720007170b644038502401d000d00c039102c040741159860b11241c116180b5000100f14060030241c0ca011000f07008240d91111801e800c08107041d64030f107450310443d8116035058071028140001651a2100010140c129003c1d0000d020000112128010300440c4039a0300c540d03d042d0703124103008001d80b404000680050103035101f401500e0905004c6003d207070500c20211468284031960718545034081c420300854084039000800710518811603038019600545080080d640c003c100c4000f400f20448403411025880b99614805401081c007806403507500b1802442500d01c4c01d0f044c1d80f006a03495106a000b00480c03655025488589082c13 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 858826699 1250 858825449 858825503
    0x6050609150f0d140a180837110f07090b0307170d0801080c0d0602070c0b0c0c0901091401230916020628020f0702041a030601090b0a06050702060d09 66
    0x51928200000301c1c10700c1c000c414400403039030002c0141f1000913850550141004103500315005030301d80140c24400402d02c40d03c0f218000301d80c01c0c2c08035071801c1d03042c007802c50701059119207100060010803d030b900d800c0c0803034090706140f0300d0280c042c05680c41c040380420581c2110885251386038024004010602c20041100f40d050b030202c00e4940100e0071850071035546080820159400481c05620b81c00c00e8240206410280d1b8022551041c2c005907a803060038012940a02c180c100f2141400c6a82e40c1d001c041013030f2007010701c015114403140070041c05600500030b1144844144c40211851040002c00442c040c410284d44404103642b0011800d1411541080360f5603204211442e8014803d40c50086c1c4c46100d0314030b2128503005070300411581c1e01e0800810035121441d0300188107019030080315003210100d100b1850b0990003401800000700d443d12032800380060f8550003a1280c400c1070300d0b0042c100c99607000000220307800740c001c010740380c032108480c012503403642e0254803c09041c4a5103240500484c00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 858827949 1250 858826699 858826711
    0x33012151903030e010e12060106230405060304060c0c05060f0109050114091611060c0304060b0a0807030209071b0c180903081f12080904060906050609150f0d14 71
    0x40d070400610001c2d5000d01c4110f030900d02800c2010380302810348001a031441c0d003010207000d281315400c00000c060703030f000603860703050584918008000328a81d1400c004602c914000c07142c10900800c08180022416031001180c48010b1030309020702c00700c90351090f0905009507002800003c854006006101140c468240146150340140c07820200300008107164a0004110300203000081c00035800850089481d8541e1030103800641da460f18040070810382e9a0810348041d1842440d0503c2d4002c582000d0740300609817510f80380140110b0340345508012140348028400710420568502a28036000340e0401320000ca8031960b6041401800d2442e554243c00c00140d4440d480743c20105448080b9411103051508070310b0120452640d010700041400f554281544070100414a0f0b43c040414086020090429140126000e01107641e46803000703001d480282c0507159102d082084090403518041d00c6207203030700c554041c03418180110307a05c035034001d03401c0240407076401a2258944220405002d0b200d0b64040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 858829199 1250 858827949 858827989
    0x60e04020415031a0a1206050106020703030c200d0302211c020d090203030c0601060206100e0a051503010c050405011709031c0207020901030c0503060603301215 71
    0x18030b008840030420900307895500c1455075400203c9a0180391100d100030040340581349401c120307520040e0751002d20264405035842c0746400c0001c10032910103d0801e0407a038240d51003a04180d1680ca8100403450540f00c1a00c24041c0300a625030692111483c643c00940241c0240119a000e0321020001c001d184c400c1004803a02003014400c800c40940000c140d0291411006840301055061311006104061010f541444017042c040000301d000103919040c1c58065007913a681d40c84440c1c105000707000b1405090104038402e0002400e41f16140c0c0312940c41070a00c4800c0c00c01086140c0444d0854030b0300320381e050002e82e00183c107004558104c044040c1081200e40145403603d484464030b41c4074020748040c550300300c20589411281d03020035016600e07002d0b002068281c480d65689006c0c0d04481062081724040e00900700010142d10300400e4921a50f003459041860619007448144036100850700300840c8800140101c8602416099009104581c240c46015503001000d0811014a8160790440b8a034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 858830449 1250 858829199 858829207
    0xf060f0312090b0d09050703020306040c031e0308060d1a1609060c1a0408270411030603070501081b030a02040602012d0f0603051c11031e07050a0c0906060e0402 71
    0x1404284088507140250000001000e00941c1b52050400205030300182d8588a04000d010502080c2040442241e20485078046444010002a82c0b65400ba01c4054003041440c00010202d0030106080c0c0c4219202e03810800c0804410003241010000c1903903091400c82c824149460b446422040c1c4c04090405810088211041e40e0740320001290034445800c00401c14001003010400c204041e92000c032203015440b80c184e81c1004c48611146d404e5203920b8840ea0804130b07a8400c4180c501c080301c0c0141e501030003900141d400c000065074900c102510803008110001a10004448034201442c02801546d034096642c83c6404030090039102070159100650b0f140001c082405454580c80745c4404034507610114046484c500341c2001401c9e00e5102a00c00d025001104119214200c0e038404c60071110303141c0c2d8080341e0070880761036520f0041d40f9000409410ba019400c00d1400e00001600040f4070420407103210203001e40d00c400c80805280c0c40010001c0e266075040c060b582d008110320384689030644085083c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 858831699 1250 858830449 858830459
    0xd030b06160f060f150317040f230904020603160908100207050c0f0306010303030506011407051c03020414131b410a031b020c0f04020901091502010f060f031209 71
    0x300c941440003c003911008001411f09444001c00d8800070200e29609211840d9902d508511121401d4146000200580e80c10a501d20f02046a1402550050021415a503640c8a511010b07804000180280030fa0704000241083c820865044130505075000036846a00c04c1c98064900841e00510501c80d02c40b94049500c261400641d07641182c2e014500441c07580ca8100050303070491000c1c22070001c04030000401106200000401e0220f502c214000c1100c4a00b80306011012030095005400281042ca0030018062504641d61600c8081c80d00b03000605000c44100d0404035110703100120301190b504058441145121400c034054500c58048600e045a41505058031544007209400202540070030b030f00d204c40384a5807001c0d041200b0a41c803590b084900200296803003400d550401d200c0e00e02ca00d00d1005900740f038026980240345c1a116811414103010800c12081c20b40300f210000c540d40c0d8003501c0d0903005603001e007500a191103000b1ba82d80c40c1c01c5081506852030101c00940a2101201007000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 858832949 1250 858831699 858831731
    0xa090905060402092206053907050322030209130b01171005010605032a03070309150903120c0804120f18180b010f020d030b06160f060f 60
    0x25129504130f078840038035030341d03400000649009180d1000040e6608921041000207aa11981c001c8600f1030400c581c00c543c0704405e02025003040036811141130b141c02c10140f9009503c019068891150301903c4c10280308a04001c1401c107144401e075070b9403445007800c0080d81003000c03825420059586480003007503c1d540317a0020034401032058030115080d0800303049070004240506c4a0031503503070206108559403444000d1040d002641e0f2940d0744030a41401400013064190f0050b40540381d041c40c1c90665a03a074a00b40c1c000c1040103019641600d5200c280d2598120500c1005182c0388a501c80e501c80f61071202c140c2c002c4440741c1c0c0c13140d4288400b441c00d22000c200c5a60054060840c0e6142c1700c0c2044040310021100d1124220031201d032004804400308605041c5190780d0b050b102d030742d44c1c10810360061100443d1810b44400c85030025802040e120203805120b9046401c24a4000e003081c0d150100114401401480c1900252040c030300741c0d0311a5040050034021521055074000341032003802c0c00003280781c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 858834199 1250 858832949 858832951
    0x513291303111516031805060402010801050f090f0c0c070803070605011202130e01020919031106040e0f090a0f05060601080105192303010e03120c0406051b0a08180a09090506 77
    0xc2000003052890300c00c5442a004022034040c0c0c5641201034601a14009070352303040582d0228042812100082003e0801c903a07000051000280398603800d85036a817011000e01c2e0042d000d0b100c01c0d5001c010034440c841c0104105da00405501c1c0080da50792543d030400400700c61068001040c0009213048140c050380d2214442624030010300000680c0741000300441740203114110707085400c44404101504c0307020b040341030f03070b411030b0b00035407180041c80c0d4002d04022240c845c501850b80480307041c401065010742c2080e01c1a60008804d82201d1407112582c4400c1c6080b003810804940b690302840402400c1d59010044038010401607410200c41c0c0c2e010b50100740301c90520b0003440d14400042c4010162a08200070403102c001f4040e008010310f960000f1820344070351000304480c400781403000c00b00701c0c00d12070141107604640295580c0e6040c10030b107075242d9100900c041c8061505105001203040401c16080c01400c810016010b4410381000307007000e000e000d014680c440d0407420700e011800008140c021402d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 858835449 1250 858834199 858834211
    0x9010305090c13020a030e030c3d051f050f010c080f0721090323010e010e100f1506050304050f01020d05060901080105132913031115 59
    0x1250650707503402100e1922882c0c11409910088400001449801c0c40c1e0041400c15400c4d42c0522451900c01100c41e5644030701c8075111129400700d8100c20010502192122030050040c0c00c02c400400b503007800c030360320780a40e1010380019030b40e41c414004080102180561080d01d4841000125490440042c4440800360315031814480780c2c106440c100100002180c2403040c40c0c10200c1d49130032507030a00740c880f00e04000303a18400480043c401080140112000300407280e2100e00022456200d011510f070a01e00700c21860420364135226209400b800c00c2c02066004003070b880080400c4400401c00c04191041540640b005502d0107203e9204104a003507610190b400d5418401e549480e1031610078940300c006075080c4515480130a6000b01c1030b0054100170b0085108aaa10340c040e601c1c2c1c10110700300d44040d12161002000611134000203440b00c0c9401d08140d0328500c0da000c0301c406171140d0503001e10040340c0400c60208812032440c00c158021b23400c5034031085644010003401e00f10081c03855a1240147c50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 858836699 1250 858835449 858835451
    0xa0609060e390c010f0513080f070809060a0f18083409020a090b0a0e10030e0f0c120303061302130b1204150203070c08090a0f08030c120f090103 64
    0xc115211004207654182c80764855072069850416074603c0d0300038621540001145420b05011524404141281f01289608207441c2031500b02c0984041c00160b1062001f2200c02c2410b0002c1181c5a9542e03029048000d40368541058489004100912011220402424428140509010352031340020541c24007100002241c40201415041030300d280601c906e010b0f418051803d0100e603c000b19009440e0004941c1c0316031a81c4c640700d055000050141020740c8002076812034080d07420385007244003009946560b080c0004d45420554107281081a03003150400c01d03070f104845400c09400d107007104a64460b5100301450440c2081800100240d0b440740350219215004038034150108811810540204a0560701e25a0361080201c501c040c4c98003254251002d8814000010218406000b03c0388110030941c1c91440900d07465580500030b030172008184c0e400c0030304620302051842c5800890000740c08140020340c3c440c482c0340410307490001030082404441c0001c0c086d00000c00796240071ba4503201070900b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 858837949 1250 858836699 858836761
    0x2061003020d02130510080d02150c0a0c1e03140c1507121815050105060f1608121602010b0310110c0105070f020d141615050a0609060e 60
    0x110007559488134102114a007800b4441d42288a401080489920130150b4881d500c8090040c1c0e141c000e174800c52402081c10500040d1100709030001094500460300f13205842803e184c03104040800302d03601c5c100c1140206211001419045500c1030030404810b4442480d15160154907601c800102c0d02c1c1c4a124410130f00410300c00d900481610b44242c141410402c0f407038144901c00c120350070404000340c82c3d00d42030403802820703441c4501865040c1c1e0801782025181280c10032120b0342c9a40054084071801140c42c21040001e00490700801031000c0c449803200d1030b4100341d040101d45111144aa03415603161000d4041640c030003041d801d905100c8080001202d0100201002c1144201030400307000d540b9020401c40002d412081040c081da24590850b07002620740102520700d4039103407600c5201c0307800c00e2020760560f50025510b410f2440c4603e0250404045881c89803050347e0065642480c02c641f01d410500040ca8180b1810004090521404801e800c1003c24200405211040e0318502000d030b032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 858839199 1250 858837949 858837953
    0x2070b0301120f150e0c1503100b030a0f1404020f0604030c0b09040e0a030809061f0b07060b0303030106030603062d09020a0f0939052212020f0102061003020d 70
    0x2549441d421200410b104010101c1d08146c0c0701d01340311079114403c486100d030501581c5141e0007900d03c1000c01d0112201690700f04020342c501504001e000c400c047c0d0b101e00c11101c1410241c00f0350401d03801d498242100c1400c01d0310401200380800101c4134051101804200081050b405055003200e001c410110b90300c041c02c0700803d001d04000000325070144246070380001090790003180188140040c2050340c100b505c60020100c40e0b80940000c0c241c00d27034035041c42401420f140350001c1c07851601c0b9084c0004c0c100e40c03404c04207003160000d81c041404650303500800c005020407401801e07000d480000c106408034043d5000d0030200301c0808052280c080d80c030801c01e011516034410b81c1d000340c804a800030200c59628040c6801070004030442c0741140c1824442c20402009012401c2a940c00000c1110043c4070302981c115155004161000291507510020501200c520380308900640091000380ca181c1440b4010f002411140c07071a00750440d44001b080001d4407510a00290030b80398100c0c3c1c030380c109030f100d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 858840449 1250 858839199 858839213
    0x603012301120c0306180209090c0d14160f1401032c0705040204090e07050f010905093102190303120b04020706050f0906010e011d1f08030a02070b0301120f 69
    0x1500010005498040e000c2c00c820b2051101045182c808c071660719843d0b903452034040e103d91480c008150408403c4440b00000340b6103051510309140e4001c200d428070503110034034003119549984100c000401c0200d0901c04503031002c08150340a407007820144180c001c1c034840d0843c50700740201e084d40440c8a40c03010b1240302e072080c40044010f0038014001c0d510f490300e6072a03004c005c00403039003803000a103d0100002854140800c611950140584811400301d151000340302e0301110041452040c0f090048500f03913032070000080034840002104040140f4403252051044104d522141e060500d41c0540381080020340c081d50042e01c044140d400815024030100110b00030b80202507004141134100010090459100901c0303a1080038014100c6480340d903101010741c5403040a000700d02042044d0303103c214181a008046607003200711740e04c1d04d54502211500040512034035130000e03c3d00c0c0c0c00005004104940c10031604c0081d00e81086000e145524142006440c000103e400900d80f88410002800344191 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 858841699 1250 858840449 858840473
    0x30606090103090c03080310050f06040e0c0403120804031106190f021204080705160308030402040b150304051b010201020406020c040b0d0b0a09030f0e031009080412060203060301230112 82
    0x41300000c0e0a001d80c591911042982080304c20841c00a4480000115441c010001c2448614080c2c0007a281078202602408001e000921407c10030340c04203c00400900c02e43c0c80c840a60f2040c2e030f903000140c100340c030b4020305403001c94000c40c3d0260320040038458801c1d6000054620b4410b6650f0005880b4268003040c1c001e4018692607001040c1d0040422040c40081c80040c09250b11502c191003162101a01411050913030307010207820120140002001428594004403420340024441841e0303806444010000780d004035012503003034002d001d0154030414002a8a218003800740003d50500e414008002e54400d40184c048d2f1040d500c0700b50380c1c805625409050b00a254001c2d030482c0103407901b0007120000e4000c0300011400a6210784101003403d200d000282003e240c0103016100340300b96451041c1c0a84401c032020340e2016070401c030005008400041905007544a032402517181d2030050105400c461030f140034405144030100c180000c020205802c40c0c10f50b4000c5c0c806480240441c2012810740c20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 858842949 1250 858841699 858841703
    0x1030f020a1b0201030f060e1909051e071203021506030c03120706180c06080109060e0408030601091518120201020604080a050f040906180b060f090f06040609050306130803060609010309 82
    0x1203804002300301361b202c24401c50b11524950b01000d01900c0880c080204440f81541c01400e00d0b0040b02c01460300358404280107003200b81d4503048a0340e441d01c8558527060450114801c0f00568441e050b10314042800e604032980c8010110060454400143c01282c2c8400009903800018800020000300300921b690026440c0c009035407195180186626020001007150700400d400f2652440c000101d11300a80220001d48140c1603000044d52074a42c1c542c43c43e5000030380038a05000003184041102c00c0032083c035404040b456078920200c0d0000c22413441d0b07582c6441d000100320590b40c50b91030001d81d800184040d013260f4018200c964070122407034115110300400017000c2c103031600024005005c101c2c80d000002911450581d45204880760003039103049880f0740320442d41000c03045c0a000410314109000e003403607a5029000d110904004c00000d20980e2154000002150000c0e209000c2d42c00c040040c1039120705d00840d88502a8103a40361800b4a01004090520440c400039000310140d00c82e400c083d0040b5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 858844199 1250 858842949 858842951
    0x61d04090b0c0901180b0703110f0a1b080f031b160e041104020a0c080a121b0305011a070b10181a0102150a0f0b03030c070501030f020a1b0201030f 65
    0x20070100d00054640c1e03c07502c079290001d50f0010103506900450003500c8200c030106c5204a00d46085540e059442402c40f0400c4011406000100000d9407800d01030317442c05512580d41e81b10030706204240b02607941c115400c5050385502c408070300c0701c00d18400411030307111025101f855200c0390110404581f41c1441c81e120600e0007400c4620016400c68042c0045000d0f0744549200c0942c98104001e06c0224011440c01c2c6000505120a40c03020580c1b14004207000300d400d2401030008140002e20009440d2500e8120044c3c031054100700f021a42d0500c00d850151100300c21170f109001181e440c003400c074080c419025241c40710710800b01d802019408248401010700840701d80070942c07090045130080050600c408210004101100300c51342c40400e02020440004402c4030940d02c0e942c001d4002010269804800381e0f40c1c4052201480d038040010340060092000140300c0d41d414a00010151035131031500612282c010300c42d0001642c0c0084515401d4400d11245062414607400120f001d088290f426000d11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 858845449 1250 858844199 858844201
    0x21030a0902030c0d080a2a14070b0408160b030c1210090903030f06080c0102070918050f4c11031518010305060c0d0608011503150501061d04090b 64
    0x13440e40e001e801440d61980b0340f5141d80041d81f1942c2d907081d0040b08042e5440307810800b0070340003034184124403110441d00c1040310031140d1198058a003d82c400d0304206010380c005071149100d01200b1807040e01404c01c0c03810503802c504240120740120f0140f10b000c250500400b2001868074804121104020300c50f07107030240000303552030801400038802480c18151082c01c1420102d003a41c030000d150380404106078001e042c52494042d442009008030104c50240d125030601c0d000c0422001c1291070040082000074200c200859142d142580d001041022603103111000103034041184510400203511142c0d2542c2e050500080051008020f400e9007428840f1011090100072000301d0114040320000b500d074800e20254000341a0016402480024580e500103400203c2d508140005040300d111b40c1c08010402580700c40c001c600392450807038450400c4600f440100140042c005034424441e580600400c000e5040030300043c180600d040c1104a2411040d8141c1d5072602d45074050640c5507000303e60010b003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 858846699 1250 858845449 858845453
    0x1e06011205121b010b040506011409040e070608072a06050705070c0305030d0f05040503181f0f0909021602012a0b010e0708070f0e0111060901090521030a0902030c0d 73
    0x2420824401c4011a6103017500c01380c0c55040500c6814000c00c4140c540f9840901800c0b0b40307826541c40100190f42240c3c8480d444400c0f44002c001341b1002c0c0c038481c0c9031101686090100288494404249100e54054204940c51602541d88603140b9058001c81d01107003650300d80901359280c0c42401c1009003a0038440c40c000080c01000300c0501240d25804c2c9060108441048100c010385e20190b6028110703270070801455111b0880390748096a10b4401030326034104400540804244c5120388080200400e21038040244425480313282c0102602c0400c00860031302d10000c0640d003107200000d0009040c007041c80485c204101c4045811410fa0502c1185c44a2101c080e14000080b40028401c2d900c1d1407001030085408280258043d5100e980cbc29900d02854030f035241c504071144407003000c00d68180082c0e40f01410b08484d0606c4211302c940001400802d0910161903c0d82c50000740700d105078039503661115011041c41407001240e03040346038a080800d150034a4000603060142d40c0203081ea01ca4400c1c029032003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 858847949 1250 858846699 858846727
    0x30a0f1d040f0915051f120831030c05030318122506020c0a0e0f15040617121905090402070212060405101e0b040e03030f0411060304020d030c0c15111e0601120512 72
    0x9481c814410540d440d03503033303d0900d82d0301e0003203081d007922a40303202c1100c40071820f00c4051041d8208072034084070300601e041c1040e95480e2904410802078004241030612000b0780401003e0320201084d18041400d519101512145210144c40e00c0c0401c141140800c83c10082021002c1c2d8080c4001d004000107075641409405019560010407c5400f6500200551005481c25981d6980b01808034150140312904c0890f02a480b03101d00310390255080c0100303005600c550310f91100e480e00803030041c001030070241081c620b010003521012041c98204501100c451400660803c01c8501e100004101402e5000008010740390082a2018a1202100b088500c02841c0704a84c0641c0c01054070f884000003001c00d011440c40300f1207011307400ca050352580c42c0000307100300303010b84800e4060b640880400c0d840340c026014031400443d45c00c001505250302d803149600144164103061203000c800c9001580e091000c0c1d074942c401440381089509648620400b8044c0900040c440000f00946003030b61080003560800f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 858849199 1250 858847949 858848047
    0x70e0d03090e0703060f0f050303070206030406060b0301090b01110f0723090c190320160b01030602091203040302091f080609030a0f1d040f0915051f1208 68
    0x40707103030070300c1040007c0180304824400c041e83c03409400b56140c181207030288250707070307002607c200c50855a0b0440003406240c981c01550207800d04c0c460119aa14070500010143c80c41c50b104840305400800d03000f1510480040c2400880b141c0d2600d0039108030410b858800d80b050840090754100b81d00e23004000f84001d0349001882e503441e6810907111681c003c2c520440032201100350160010715811906182c49244401070b008042c5c00c104100007040306035450f811652000e030f004541c840d03000301e00c0d0070541c5061102e044a1919100080d41880e1542d00000c0d03c08030058085094040c0c034101407a51503207401c0c80800a008140c0c1112004e0602d880c00c5950303030f4084450039000841c0031070203881e80351041d4a40800184900e007110000e00d01031003000000d140d41d03094005115540c134061800a060f1440b110304c9001c107400c00003118075000c041020f12110140c3c0c00d4030700713480c00d060a1141282c509400c8141c6908040c00c10741303035181106078090054540c0c402013440342401200d1100040c403000f001c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 858850449 1250 858849199 858849209
    0x1806160b1e0c1905210612010c020708100b060403080a050f0c0f0607111c09120501051905060a12020a172506120f0204032306060306070e0d03090e070306 68
    0x504540307903d000e0201c0c1c0a0140c00e01d6460601242e01d010265164100038080d0800da0003003c0c0000e400c545c945040c00c44071048501c80242c1c204003401c200c40c8070305010100d040d40c242c0a050017291108000520700e4422400020808039001c030f402c0205034411004d0307a103a110104100c40e550124195555680d80d1000702200b080d118034000186070350310826850440010b0030000388148850380329042d20100102000004000c140000050000c44c030140e0603019601035000000c8505050040b85844595441c90381c1150f801c01c1e040c42095101c20300c099044808512021502c0c4440c1e2000a4003c12958051515820701803403070002c801011030030905c1c0c002c2c2c0d0b010b00c441c04914400001c198003058403e00d800b01d1218070361001c010304503800070300c4820000b1100600d801c2e1269100005106007450341c1000c000e41007840c00c04850300300070311500200d00300e0003400a0f24000800620114080c6140ca00496400000320109805184031402a05107804107420340d14080200400602c1c50f8420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 858851699 1250 858850449 858850477
    0xf1b07090f15171f021b0c0f01200a150c030506030c0105090a080d020a1205120a020d091a090706030b0a03121101111806160b1e0c 58
    0x40000769400d841141030074040c0c0b50418005a10789548409200c6441c0000541e43c0034000c1084040308018005000014092000588031031103c284440c0440c004000c00b4150392250310303d4082d030743e00e000c110718030428246804030b0100a9005546501c00218411043d06e04c9648455400c0019881c40b000d07802000c0300c010008400d640d8000c900b0b9480076661541c15400410194000d948240010074080b2800b401700c0d00d2481e42d61034075a207816450302081e401a000740074031030200203010290300c161404615100f81803810164821080d28405440030f0429980060341c07001c9002160880820103401034000919003000c00d0312482500310864003100140903044010480600074816010b50352409410080c0003420b42d61003446251000792000e041c0200c002c01205501424014000035452110b0320980318030200f411109440b412090701445690140545d40315202a4443d008109411503c0c0c000f00742c9a400c0310214161400c82d0004a0800142c100509103520f84000c1c030349101041c0d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 858852949 1250 858851699 858851711
    0xf030609020907080f0a41011d1306060b0304030801180e151509160215090a0f021f050418020403081b07120302100b030f0d03020f1b0709 61
    0x4000c5401c144222652000b41c5c0e403641c0803504000d940e911000c1424040c44261050404d11550b40c0ca0142840c0c20004c0000f2000700c84000e8015900142401400d10984440c138800c0031281c110440a030003011400045a644c18600c10301c001500079900030850650310720f0740c9050904008106000900490b42102807000c5200181545842620620368044000d041d0030384180c00304071110040608600041098514840d01d941d4500800038011003042030034000000103410045d0034210280365100d54500c002040055465001c54213980203035000c09445080c05241c0700040c000c0680c01e00c0300c4920301070326140004440e0480003c03c1510031000c1801107904c003072f0800c7c2050780b080340030060110130184200c2e500a6071350600740351080040019204215110001d206035801c2200080d00182d1010340d0480c1d00c4502403040c0b44001506078040e06200664203507550391944c50b5000359007010f6000a03c034400883c08810741e41501d108404000028045941c00c81da40c00460046018881c41e101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 858854199 1250 858852949 858852961
    0x70c020f0a0b030708011a070201030b06041508040501270206070311030d0e07090605011b050a150218040c0905010c030e03010c3506060c0a21091418100f0306090209 73
    0x40d90000401f191070017020f190541079401100a440c158041e6500f00388140800b00e01440c8441d000c4182d02101d985510b480c1c42c0074104075094940e44030515040c900c4612440706044a8040040c2c080f940641c0c0a9aa903c0c5600c0c00701e44010765408101c50900010600d00040942c80d08042c074030f04c000d00110b511031611010448100d4000340301d503a01050950041c4035100c0c070345410716650b56001c4c2065070000581510380600d070058001030044038642c001402c4000389500405010b070301c4030980e030400024504017030140602c400d1303002c0c00d41804540c0c0181010107102d4161001c14503400380080c00811003d0101600010284042407180d10415080d00d401c0c03c840c00c0100781e050422001e00203140c94450501446030310070b2543d4a01401517001450210b2081001710188010041591404003034280000304000da40d9000500c540c1c03c030b081d1b560f583d82d441a0702c48072005000f0441681c4d03510f500c00780d15058049a80104001c004285001003170115030791045212600944804125070340381 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 858855449 1250 858854199 858854219
    0x109050403110f1c05031510140f21060a1701060503010e06040b180715030603120c02130204050315090a0507150306091b03050703060b0720030c030303070c020f0a0b03070801 77
    0x2107c400746105100540240c0354942158240200c8615003803400e80503100191400f40d6500080100c801d20900054510640c05003003030f6542411a6201003c007107003001400628003040902c6203106082c54040072512184d02035014000600d0001c0c001c10110181c2841d254982404480966001c03806c940069544451203513152012682c0c04090074146003440c0040c02c482281c81d804008150f80c49901100103078144444100a480c541c403034644800840c030400000001e207440c418001d50060008214589001400043e040d030342540d00800b40c0d80da586c20a14100c14040003801d944103000001980414072507213843c2205141d9028842a9150b15080782a1140010030003200240c10701d0f40c8a9041c801d03480f0603003000c545d241c0820201e80d2403080781815040703028247c411214025004022130100300128114a5043e03020f803104c3c44104002940b2030000410442c24800224a48000c41d0b0b2891106101100000e060030f11440c1c8030b0000d00216003049904c14046003191002003944885 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 858856699 1250 858855449 858855451
    0x40c020106091b3f1508010e0a020d060f05010e04060c0c0308060d0302010b0603150405010807060e0904030210140405010b0108091f090501140910020c060109050403110f1c0503 78
    0x3c03070b114107004d02e45191000780d680714040d4001d02214a440200340310204c5030100507036560154000807813651781c10000007044203280d43c1300344810782c90100c4042d0307203d40c00308034204200d8044588038034554060814002400c3c01c40c00080029141c40008540d0078000b80b48180a20f001d00ca0410258402c89402c1e20140410715010b0007180c9a400001c4451800c0c0c90240140362091002103014031150010031000e4100352081080c00e03002c004040041c0c1024442c0341d005091104c0148045450302501078101596507a410340141107580018003414003c100c81a400b108200003000078901c040c1024981800580d0704444550911156600941c031410195004401c84c001a054404000f0120758000c41914121a429070300c88074480c0204d0400e1241154004129440310740794031f0329540b41800d040d0b000c160002c00c03920500801651800c0020700b1415034240c41c100080c15260f0307040994800307600d41402812446142010103c0d1003022a041c80481002602110041d4042c2420769082c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 858857949 1250 858856699 858856751
    0x8030903060c090402131403120f0a030c02070b161202030a0f0e01030e07030503120f0403050a0f0509061603080c0a08061c1407140109050d0b0a0b040c02010609 71
    0x211103400b041040c9203440040c62402c00040c001460000e0488042507a002e80307034440114501d07488581c01030713403c09109202c4500d422443d160b01d0408004070500712030040700c6401c81003556428000307000700d0003000f400b406000b00e00c00c50768aa1080510240d40f807101328001f00c9249032940c40c20121140000240c0d110030070561a1071007075003000c41044403821410049981019241d81d8040142c40707083c00030341d000e14002c1001e5503540303001e8180207100d880003400440000140340200800320f5480020340d500f03d81645014001c2c01000d43d03045031a0300803c0b101d03d40c424400106502022001422408502c0c820345900e2503035614010108264013450001e64003091000c00000d20034501080c02e0717900c1d40000004150306044984403485841c0407001180c1a6600101c2d06115840c5180076043d80f041003403814000703550804c0c0c00310705100c08408008001e008642d011580303209080d0050a07900e94054400c0050f20000745009001e466144039884000c3e207070141500c8503c10201c06c07601081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 858859199 1250 858857949 858857953
    0x504050108100f0605041107050c010c12030504061d0312010501140904020702040e0d050c06010b130303030e07090216020114030108030a08130609030323100b09011110050f0108030903 81
    0x606440c0414080d05000c00f1402200d5640c40c03010078159103a1003460107602070500e03c103444000d01e10f0401c0ca0610b40b00f5980d4103105002080d03100203a22501103c0311900545000300b82a1100c1c40d1000203840345d640311070388182c1c10b00d9241c0b00c811000800340406d040040f5806c1c00b641d90319801501c910142180c10982c152080103c01000e04282d001004441e101a200081c84160a04141d0030f00c0440e0b000700c0b001072000980ea182e036001c100110340c0542891015289040d0640001e000c0c400b0507880010b05150300e5040000c03c030b0009110180c010a0141400d565410340c0b1456840175032039012040780841e807a200c041c04002d126005a03416580f0f11002103241040184040e82e40c070500a00c60f00100f5081801da40c0060f00c54042c505807144030b5103021a81002100e95910440c1c0000560360203151100100650917904000c42d000301c801240421b6a211840b40c0100c2d28201c91111140c41032003040c04a106184c0a41d001030b1107444a640b048003986d80344c00e001502e901c40d540d00ba0381c0c15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 858860449 1250 858859199 858859213
    0x9010f0e03160f150209031006150f1b03030204061b1133090a090506101115100503120f09010e0a03021c050f16030f170f0901090504050108 62
    0x568000c000300071031406041c0702d80010243c1d5654140c00500c0b00c0322013000a0300410f0038011420200301c09544102c2903d4140842420314400306284c0d08040c280c1c1c010401e80500c002c01440c0200340c0c03910001c024800700c4094241604001d0060f500030300c51000060022080e60316580d0170f07440312294080d449030900b035400c0100c90030400703140d6807900c0d50360401e070901480c00c20320950403581070a8144528881d9403241c40c030790100710124102d54840007280d814401044500d5807450111240400c46060468641b40300c5214a880d080703858200510038804007007440341c2414201640300031134804508035101a01040307028401c5000f2040050b203100d8090251403c0703580244100117000201410040c9425036a40004000700100b00b50001c0d010302c1c030190303201809000c3c0244580b40000000a1844003090f40100e20185c010b07200c09440d104600341042c00f08003106140360320304a2543d9070b407900d480b91100a0322860b07104080d0280400c5800d03900050360b003010b000d00e9048965440c050004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 858861699 1250 858860449 858860467
    0x30601140901030f17070c050114090f0d140109080702030c06040302060d050a021303030f091e140303090d120e03150610030e07060216050d05120c071a0309010f0e03 73
    0x7854000e000c003100c1001c0d0701d06903c429403a182d0003a00040c0d0181585082c11f0745003900140140c8000c50000f003194a0030082818240c03034504030810b106038262084100e1506a0405020200100b84076052035400c0114010a00c80701d4000b40c12200e008030103503242c0d1391845041203031503c40c40c80000e402090500c140c0c5503d640074cd0201da0b006032504005468280340d4103001103410095003086000c60b54180b511288281e0050241e03014001302d49800c42128501013902c4401d032040e100c0c07810300b1207452040d003030b00f914280306030340d440070f0050135034104100b0501d444c615031302c0e51031080300020b011900040c495140010b211200044400a61590398440c0f0043c4080715441c17448840c00d141d110400190403402c100442c500402c015405024081c072420202004842168403040c0700722101540400071600c08600340500c00507054130705a580c140c914246051441691001d49045880300c00e082898040d1001076115111001c000c000c456410303822207003200c407002da0703514040d48248007400d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 858862949 1250 858861699 858861713
    0x10f020d1e0c1e1e0c030f02060c0f07080714061e04030804120521070e010306051516050f0d030b0d0309151709010c1b050604030c11060d090203060114090103 70
    0x102c0c5000524100030071390b01410810f0201060b030340c000c00008854a000c4410700d07a21503141c4000c0116440684294107003586400100d00601c0740395400c18800040741010064032504079903029520060645065880a4410340c4a807011500c0642c180003100040340d020140c404c1c0b032441598940c840380c14030384550320751208081e003a84808003800300c10004410450700059031075100e050450922030451801c84001408030b6031403064a03050608141c070174441541d4401002c51050307032080740140c540c15650b50b80885007102e18400703010350040c0e001040740d50a000ca0032103c07a00058030113000040c20305050080440d0011f1026000803012035017880804240e14091800c1440ca107080e25911200d01c44004010405451010003a90750351224810560001002c4a083c00c0c54400000c5121440d140d55031600d0000700001d00700f00e0291000c3c010805500460940710b080900030a481d000050411001000c06240c02d074401d200d000000124ac000086084a24140117445c02180303034a11303070b5030384 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 858864199 1250 858862949 858862997
    0x80f011a1c08181903031806051206061606020408120705151801020a17090d0f08070201140a0533060304021305040c15020106060503041202010f020d1e0c 68
    0x11800200244050f0080d62696019009200c4416400d40043d15601e07014091202408410520b03c110003020800c454000081c4c0396008112041c0e42c81030b5554038006211486044c0c00103152282c1c408218040c8000c1d6405401640d43c448200c40b085104250010b00e01c0c0100d143c000c010b0342c48a41050810b01c501d00d8000d812602d02c4512130303090b4801900c46400d90b0031103150030000032800000340d0000001000e02c5600910140c1c080e107000d50050f00001c1500082d00d51400c14005010041800c0c1d078400d500480c3c80408036102d42140f41001c8a4035006882c2c15110b02a442005106540705840e2120450105941c151948401025054103108076904000c2c01070341d100c030040900501c152210702449100b01d12413050f0400c0b0500f0710172214000c4042282c000c2c2160700d40181440042e4110742100d0700603821400d50a44485882c1c0202e01400300346030126102800840d0a01600c500c582100e09120a500301c031000c100301c001110400c03118442031110009181e4043c003195140c0f00e0b1101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 858865449 1250 858864199 858864217
    0x6010f0b09191a07151b140f1908090111030712060902070f02150c0c010c150e1006051e01111e0c1e0d0204050907080f011a1c08 57
    0x30381c1c4550380f103000581e4200044154850303464002101000c108060161101d1800c2c01c5404008080000d02d01c0820348070f011007000c0030701031003802e0070280c244480c084d1021320b078616000c541c0d070f90032201c002c0e10280035160300785020030f4200002c24032410040c0681900000259013040c107650764034108480c480d88811615680a070389030008980170a1500040400b580a401c1d48082c04c0d5036031051101c006104c2c5081c04080b4014080e0001c0e240d408240300c13010b00824039003a40c0d48030b43d90621401c1c800c2d001e82c2d40c11801d45413b00c0e05981c240d010400c0d01500701100790400c080d580c0c5806211501e034000e40c10303d43c0c030603064443c0012980504007a105000c058001c6509078140003c0d550f9400c003124418802c1d07075200c144140318520308000d50b414144d00b44c11245a03202881808101d030034030b40d404028401e41d00c1e80c0000c2e0100000304501c3c001800b08008507110a00c1c2007590728000c1c030541807101841101c010108076141016884551aa014001040c8200006031103042441c0c00c01c00f90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 858866699 1250 858865449 858865489
    0x1080408090f06180108010617040b0402150a030608160b160c050604180609020a02060402221103040c0b0f0a0c030309080406030e1605130902240a0206010f0b09 71
    0x14a1100752500f0f0040c103032084031044c004205619100c005004114164003140030030016440b0349840298809106030002e621582e142c2041e11035100003140304583c00e9076000c2404002c500d841c0c1c55940b40c1c00c1081140e1250050301c281c0224028140c4c118041809691a8110b0401080244240c46145003031030358026582d088900740c64000140b2168041d0740b281c4d0303070050325408185880b6140d1083c9801010199011840d0140c0400b0203034403460300820180c46503101d584024a440009503a80100d0742940c00100b01d640e100700040074240d0403d480c16115214119004a42c1c05c10303070380445101700c0c2e265500354103003245103400b02c5400307940c084220201500e41c0030380c000140550001c0c4c400b800140d1008519540450342d59850701e0840080c2e82107400960800700119211002541d2812000c46e8000c240010036001240b054041c4400100340d0410910400c1403400d0000041d012404240c0d0940e00c190343c0c0c54501e90004c04281c0180b03d0080c10402800c40b03075161101c40005031881480e0303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 858867949 1250 858866699 858866719
    0x40b10091a0717040e0a0c0f0e0a081e010f06050d02060f1905041e030201050405060903011b020c010216080606060a020c040c1206061701030204050712020a050d11090108040809 78
    0x80d40942800004404880041c0007140c107110b00740d40340034941c3d4400d06c1510100981c1d611054020808032100026006010b03020511140d41d440300038498014140d01000c6503824492100308032010100c5414580b220352901240100c8030000e402042c04890b00106014a507050a8003000038a038080010303d001d03060704000516200c0d0544005200596403a01c8550b1140d29103060342005401d40c040c0b0302c0031500000030520050307030001d041e9400d44109480f069110220400883d004000303140d440c028014007001c07813140f62580001c144000b21420b90907101c4c103499080003040340c4e83e514010300010b40c01c54000a1400d0801c036000e01035503100361040300c0208100b0f102203021590038152010000300104d100a802c40761a004a60040c1201c1c5025602301c0c1744d10f45c3c004440076060200074882c41d00c50022440385d5210700340740d190110b18410215a14186024050000c5e8018100c080c1c4842c00c0820754005411a001a51404003041c0c40d40c900c241d8130303540d81c8003980d4410030486d644410151 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 858869199 1250 858867949 858867953
    0x10e0604090506030a12020c01080a0e100510030203030c0706030b0303040602030703080c070b0709050a17060610050f040f0e06060c1504061e230103030f030906091709040b10091a07 80
    0x6440b60384800321b581c020b03144600c0d0f041e0004094140051184a0660078031130315540600d000180c10049411401d8001100d40b12121054000d1440e40d10196051201003249088001d021558904990264a0810039080702c0d030245512030081e441040003603003040c00b0001c0440e0107460240c0d4016581c0900501c2c208040e5501860303218251119000180d0641d400d01c05802c24800c810b024018542040b403900c0010780c07a0075a0317501c0083c4041e000d24110300706000c0c06401501030391804034440c0135040e251a107560242d090b02035a40b192801099810003c10850300b4003508503070000980c000505100c80385d1030400f0120841c040c004498103a96480c0440b01443c40c403400310820a542c4070045010807401162503c110f00203030541040502c601d00410000382c00001c2c01195403241d0402068881e00c4c3c0c02d25100911b1100742c06403000b21071450200303070764150301e0003450384203c21101000410041c0e0148200d00d420b0507410340208a07001000c1c450106401601c81c3c01c90024400b10340381101603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 858870449 1250 858869199 858869213
    0x30a090f0614090105060307210b0f090c060a050904150f060509211903111905300d0b04020706050f07050c07180e2a010e0604090506030a 61
    0x1440d0141c80e4595680107988040c00c514600b40c1c2c11000f03090003403080d414403000282d1585a5481800045503a4650301c4c03600054906290007030b2508201480d00d54a41850200d80707081c0204c0d9020158042c95020080034500708081d101c4101051351107506004a80c4244801401d108040d80070600741e4040005140c115200c03000c02511480c1d95154603901c482003404440e002541150100c0140300010740184800062010301e003161142001c0a40c0b035280c20140c1e418509030321100c425020b050902c0c000c080f584100302d01824400c0044491100d443c42501c0c03215468056007002400800680410065481c806043c82080580c0005145d401090008040764090001126042c0e02c41081201003040300d071920b41d01410701d0070450316041e0380e002c035503480307020fa80241d0028040b0000407024031480740d80b04c2d5148020301d004403400c400c042100c144050b1850681414041001c0c0341440c803c1d44507824011584001030440b03424207041a6202d005000010483ca40520503240e0b00c0c408a599 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 858871699 1250 858870449 858870473
    0x20702040507020706030f060506030a09031e17070f0e01030b0303130e041101112a0904030801030605060f0607060e03070803010f03030e010c050a060504110a0305070e06010320030a09 81
    0x260f9001014018601031001d030a545100625128603132a100c41040350307032542c81c2180e5102000d40320004400d1518a010307600040c6404a110488100038840f40055403c032250b0018411118004000b540e00c4032401c890640c007100e10701d40001c10b88400001d241d40a504440d1801c5002420f4a0901c00c412803072000c104400e610149034440b0800074403040c0035118501c40c2c0b1032002840c0c00031154003040d622071707030740d420750f0510b2030900024031480c0030200940f82444000c0d00e802041851641030506004000e03500c280402d070b800614110204000749005003030000003480152805080c07005544483e00101030307258000d0005d0004110700c0c0c0010311400001c0d4042c01d5003071310b5109281d0450400a1903d0820f80c00346040c45840041000400d0001501c5145607510010100c0c003607940e40b401c5040120001420340e00201b260901104202d004600c00050b00c0081c0a10f04440c2d8503100110252840e480250903034060701c8010700080044040150750110441102140c0301100350740d64508049 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 858872949 1250 858871699 858871711
    0xc180114040b1c0b030105070f0e18090c1224181c080601090509180a050607030e0606100503040b07090b070804031a01210303140a050402031504240207020405 70
    0x80d10361441180074484d00c10100920016802080103160a540103404245140c0c1303a0420702213040c030911019520011000c0120a100c0040c82040c100302c0d92059507544003101141c455001854052044940064115414044000c41008000190707808201d40040548074052000902d01d0a20b55039004020340f4401d8440c05c2ca81c54420b100081c0c00400c0460043d08460400503041c004212617500d000e602500b001c43e0728100a8460001130701645440c4800300018014020f103820000340c030340c155002074641d403a0038042e540e10b50f4460041040c683c50707100070240440d10a01c00310b00032920604045038881101d04007240c0454403145240c016170401c2c0d400726502c5030005414401c10808410142c11032282c0c06200c4203550606104010b0b250110303544030000303403001511009241c4a6080748003140c46580c1405814200803803c40003604003210268068815540c082030301d00703290600a4812600990340c1d40030ba0a01020320101c881400041042d00380c0c00f440681c0142c4d86500c00d00d0b010f80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 858874199 1250 858872949 858872977
    0x13031b0503030f0c09130b06090409060506030f0604020916111c09080604031416020402070b090706050a08070f091508060f010212120c1c0c080c180114040b 69
    0x12402c21850450200c00801d01d138a880c105004419403a02c1d2502a10b08010340c079072021030a00c000b075010620700e0180c0103505038024202a055403d000c070302d500282c021541030741600c2140b40f0358405d180d503c0105880013074020000c080003500c500e201c038482c640f5071040c6152904d43c1184802100d4030300250341c04580c0e4130034819040e035030102c0e4101c4000307401401d088000d0911450f00b501e000c1e0190a4100d460380c031510001600d40c00d041024a0400700c01540100115224440c43c2024070444908440046a9105506011401d14002c1041d0350104659644000d440d030b4400c00c0c02c4130b0040145141e101407004d103003004540c082d1030030320310400d4500c10307030300e051403460600304001806500d41c1c03045040d9000341044400350303003201084560b000e05001070180f0a4840c4c010356003080c492586087d18002c030328202c00e240d0b502c0c01c0e00b044a0701d200d16600c1c0060b5803200341d035000c82d42c8903140100d10302c880112030b001050b501580e202c03504040151681801d0554030dc03401c1c11582e00400c030380343c084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 858875449 1250 858874199 858874201
    0x120a0e07260102040b311809050f01020406110f0c0d06020c101a100807021002090d171c1505041a060a03060614070506010605030901020c030406050403031205040b13031b050303 78
    0x710803545224509541a01d03003108219140444007d11000303500307950a030594441c0c00d03103001d0000c200881d05600c90428002c540d2180d48480042c6041141031300c1a4150148640c2c1d1080d0310000034419803811402000101c4800c03590fa02c01000798884070a224150144810100b6002e1a5104000031a10030302c2610f85c040110328100318074009406088420b004290080c840110340c0010440c801030700b109401a83c808050300018540341015000130001c41c090440d10125150140281010503040881c43c610314441d4014802980c00011510003094984402048685060342008030030b141c00d07070101d020910414002c100d982c0c0c0800721500101792035032401c01c0318076404030424107034001540318642008810754446440d00320603c2400200400400403849400082d41201ea22200c80c40441e5540c50fa5008007914a0704103110540109481c0c800d0000c0910325401001e10541d8850380040c401c0c1e41e0100f5134040f103040d444003601080000707540350355407500d10b40c05020102d000701e00031516 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 858876699 1250 858875449 858875497
    0x30303150f0901080c0d0302010b030d050a0212031608191b090518060f03191b0602030c070312050403021c1e0c0e0a020f120a0e07260102040b 63
    0x403844501c00300314082c0d8a50801004560400b01e50103c62060494154036480c85a0504034003400800070307400e515000d6008c0c02c409080e0050003c04000c4a15003c1e03508540040c140302041380012a155a0b00380361221400c0c980c184240c4141781c0c0b00503580509020804501c50030421503d03006a500c4080c0c0d5640c4101d81010b0b00040e4010040000b101c401c25a0f454000c10301d5070100001d4050341c02009810301d4018181d800703201c9040d01540320b103c01d01108d40a41007111032008051f12100881820410200702e941c8003000f00c594011040e0020402c440c0384d55115030303046a110080360f08000c014400400107a840489440d841c0344c0034185100c0400260407c0303080d07440052090250000a071000d04c1c006800f0388036800403907850080440c0f1076035691103403602900c00c020411050b80800070344d141141c11207805880c05203540b803e08000001140c0700c041d980f0308440c040c45124a00c40d000344000d4503403074095904454024400503013407a98850700750520b034001e036498000f00c1d4000c2e811650 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 858877949 1250 858876699 858876709
    0xb0603011e0b0612040317010f290f0418060929030a060e0f0c240d0f050106050a17060603012c0127020301051c0f0203030315 56
    0x5000001100200700c6100455040c000d084034030440607a54a032109103a000c1c0c0d507109015036403030080b21500ca01c0c01d840c10340750003848007034130100c401d4011945a002103910304600c2c000e001640c0044074000841c1041b000c003281404242c001a0300441c004202d10306008030781d1000b030030090444400d480061690340c61040281d4201d0b40044d0202d618084107120041e000000b58001e4410640511000ea4044408a0304002c440100508198103240e1090036105001519107001c801d0841550f001c003044400b005109c8440b01c4165640c40d40d248003910024214034001c2c0b60741808240002600d440402c031885c10b540c0240d001401040000c1030080c0441c0d0040c400c6580020501c20200c024a4404005007440c00107008041d40314800d204076884900c649052140b4840c40c142c010806903035641c051621034504c1540030f0200c62540b14201051241d40c0c020f6a05954000f80500c00340d8044082e00030711605e581005460701d0104804034405030303c083c00194010802072031464016045101400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 858879199 1250 858877949 858877951
    0x6030312050615030a200a021b0306061507050a0b07020f070b0301091806060b04080d1b02090421030b102c03031c090201030b0a06020727020a03090b 66
    0x8a8641014200003240d91103c005a0341606070441031512602c0d00030000000300003c0c8034402c284000d82d00c984a81151101c007609001980d40d0854142c2803003008008000c1d00c4155000b80c250b40003102140b514604100d8441512014501c000d0800e2a00d1311703440c2c0391000d40301040d1584103180c5c09003c1015418040c981c0b0410601f801495014030309070300c0a40c103100500c0f804420b681e8450b07104119149111052051130b400802c188001030b00c0307828450982d40316110307180a81c4a10745986288a004101c84102d0107840000c2140d6232031103400340150220000d10880b02003031040d071020700390303a05420481c40c1e0b040d165030005034111042e400c1c0500110307401076882c203100d18036a55070b16440c94808070011211410b8081c1454000141c0800d145010301040c40080e01d86c1c2421058010001d030703000c0d00030503000340da05100c00091201440034103559800350400603081401d050100954050200c00e8070480c2c8002e2072000441c2207441012a0041e000e80b50000c1d071a04020000d01850710406 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 858880449 1250 858879199 858879227
    0x1c090b06120f1c0906052701030b22050601030e0613020d0209010602010504030e12190201020708030a02250315020a02030d0e0c0301110405010903140307050610030605070e060f0702040b13060303 86
    0x83c030340740c1455a4205101f80e00b40d800910010f0f41541403055910a40102c0381200026090900541d200104035655980b003917181c000880c03070400056050b61003401081d40581e43c100c0a070010b40c03910100720550618040042c4c0e000008850940300580b64000228000c000a5000203414101450000c08981d200c51019105a002a981411900f000b00f2910382c6c0160003100300007000355510050b42815041d03401000180000f007101100c0c1c9401150800070368844803851800314100328442d032404a11400041c25054107210030511249075a40209800100c500450341407a14044040080c1c03030502406c1499078200640b0200e1a007024055901d40481c644461804c02d400d01c00001d01044031480007070300300d1240d8103030640d002d80e0a008490b040750700308054450b01d1411500c101c480e195a4441290641e25002c006007403503100b545469606140149000e1a01868100100903904810401c1c1c1c0d0295840c600c43c0081da45401480034000025400484c000e40b07541405444503110f682c1d9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 858881699 1250 858880449 858880457
    0x110403080424030207150c020709050c040501080108150c07060608070b0909060103090308070e12010e01021315080705070204140403201506091f060201021c090b06120f1c0906 77
    0x58000018446c0c40340400d61310103600d00282c0d008a07220120320705801c0c3c2e400015054a480280011058440c004005442c1f003a01c03003090991340e074136101d640c40d404900c1c0c0c480707801d528401054000860740010b140c1c041c0210808510346884003140350a11410394003452005400013021072083c2040e8182580c000c034242010000c01c105902d0180a20f0b4008004078200a840182d00700c1079038a0300700b11b510407203504000704003c0c1c1c08002d91074000d501420080041080c101c1001501010b02e207072550300100b0f01e43e1100b50a840d5400c0c141e07aa070b04440c038100d070300c1a02ca038441c61a07001100344442c0300c0c0d4000d6892003c0318100e484a00c500f4000c9050031505a04003400c546c1900d4941c4003041c0d000749060b99840c01a5035642d40081d88441d80003840300c3c0b005c892080c0000c4290b415000352090000e0901000f98040c1c1c2c8080d0541115089003000341400001800038405140000010759a101c4840503190340801201006060810540b112010542d0400c01daa444a6010901c00040e142c5418 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 858882949 1250 858881699 858881707
    0x112205190e0c011211070c0e06060c0c09070918141e010e06040209151231050309030307061a06030c0d09020a1d04052104091104030804240302 63
    0x140075522004000005814001012580c80100c0031030350021200c511842c03440c9458000c9413030840c207091403d2140340c4105060501080c3c0c83d144c03500446007041d224600a0085a8022062040c0c000c07004200f4002d210320440002000035a03241140e51400c07038404009040d4079400100680b2081c090300340244900d01c0100c00d03c54500050001d4191001a10001d2947c3d0341c080001d4064400d0a06094010386941d02040c0200c0750400139080e1540e01e03440780d00c450341d5500090342c2150b228915484000c41c0248445031460030580800100500402c19240380c0360391400031038656070194108845166941c1204032007050102c2c0d80c8031350500110392451450070041c0c14001d4a000d441d1000b4a00744c4c0e600c041c00c0440d514070740c00e100100086519603415521515a08010700c80c01c440540306070184d2001100404a1000b5002040c0380c0c3c600010306081c00d010f400c3c03005200e54a4035509202e410480440410811b50250000b401c1c1c0a60b504443c01e64400000e185a1078404807100385030040c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 858884199 1250 858882949 858882971
    0x603050702011d0c0d0602070f1202060c160305031b13090b1e060c1501090c200304062f011b020a02090c030408070219150e060711220519 61
    0x45102610164204c0e51034944c5c02c041e08001c402440398450040004203007a100c20100440100580880c500031b03003d6501d1075540345007003105032240020080c211418413134050002800b032409150804241d0f1201b95818442140a10f004d60000d104000f00707045034441008a410350703001e1000100380580d18000301a0004100750042441040064403a0320003180c00c080e821420031801c0c0d5207601801e0407001a50317442e11380341d0040c6040318084000800742d41c01550080801c64002640351042c1c1e0045140510342042120f070000c0143c200c241d000c010003001d0180c49103141c405403d602504000282c81c4840c8010300d4a0207420f440d92038113641003030200b24050781da000c0416034480b4080400396901c0c1d40c0c42ca84265244944c00c070003540451010110038a2400320410541a1481c181c200030101080705415210669840441584100e0030820701000a109110000d0008000340075029469400d440340b14200650030046240d455984007004140301d603464800414100540080000c01602 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 858885449 1250 858884199 858884203
    0xb180c0301020c0613150903030203040308150d0326100519080706230a1805040204050904060902030f0f060a140628052101050f1e130602040603050702011d 69
    0x108040005c030468201481484440a0300343d1751880040c000700449182458080c0c02074205903402e07000135050800140384103807228484c03030b41a40010001c00000040b5035040342c0c001588941403402e070700c00c25001070701d100403020014040c045041071080691b04000510550860201808003684002003040180c1d0748007007441c8060f10490f00c1d1945036000c8031420003050404243c00c00c5514500010348400c00c55000030b030101d010000c008100d103044d6a400402c0268016801503e510108060100340081c03140e600107006144044c09482d500e00e140181141007400c40700c4c102500c1e4200000700710000b4035500c201106121224078000c01c03400c0c00700c0400c00b580c007221004440255410440c0d204491500c40c2e4070000c100041c24445003e0031419240300680c035941440650350b08010100e07141081d0002c0203441007011142400509030901c1c004580800090054120814008048004110203000030700c00780c419074501141d1030402000c02401c44070900845140000e014500104074180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 858886699 1250 858885449 858885451
    0x20f0112153f03021204150e030606010e01030906090b0c030702060a0507050d0213090f0b01090b0406140715090303052d0109110f0c0106060f050f0703050708070b180c0301020c06 79
    0x10308102050042c9a40c036040e45415801000d40760b50207030101d000503280d511442204c070350178203c0d03641d484101c3e29401410760b03524054400c280443c80c0304000d8003c2e5403203075020020003030081034040780c8036130f09882d4224540410394202c4400c42e800010030801035010001c0c690041c200b840b00300070900e020711009150b03002d00c0620b9103840d03400003030440460b00303241c2140c6e0280c50050b208000480c0b80702e904a004140107002c0314089090104d000a41104010587d030440700140c4403908561580d0801c1c540f00d42c080207007140c8000c0c52510040300c205c000c1c03041c5588036200340c40c0080c060411400c0c0ca501003070b0800da03e4a104049880c0c075122210156045811a01c0000700800c0041c0440ca410700c00340a4104ac20002c9403020920a40750396054014104856560300d400c00702040c016001c41c4c551061820301202840c04100d1000064030583c004c1047e01c2c00781d03141c1c1342801c9440c0d4500440d800c050701d201d10596040051742842c0501400230a0603d041100210710b01b401842c1140e854443c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 858887949 1250 858886699 858886799
    0x5060c15090d09050d020d170c12040f090e070f03150509241005030f0304060e0904030504050d0c1e090c050c1902030705060d020c0705120a020f011215 67
    0x442400c4400031510b40c1f481c0e070713440c0d0b5070700039400319042c904010b4041c1c4681040c020142c1e40e01c02c840c3c540508d00e02400403034050343c0d00340f10307070303142c0b01741845078040142402c101400c0d000d00c610306001580204188140e0082c51240e0000000d20900e0b144400a44001034540c25294010001d0740d1a6200422000e0f0f81110280a80314030980d01c0c10240c1d8815851540016014041c642d41c1c21a6060080f0040c0107a0f402ca40340e4803101c5046c0800c0c450840422200100400e0741084180400e20b004507a10302c01c58428029441da480d02e540c502d0f600349688a10b4680d203181c040009100b29003107030061244e01035107840d18500b04650302d5031440d51422114005501d8054041e818000e54030184143d0015060181446585000105014009500c4100314403802c5c0580c200105440ca40705551140c07540d143e800410800d0b489800b0010405172030409981845000340381c0d180010003d0044c20102c81000515810613480c2c84600d108020307402c02c0c5c044040b04038184000c0000c00000034001944 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 858889199 1250 858887949 858887959
    0x1b08070c021905100809061302012001060506040b1c020901090905130f03090e06030c0a03030f0c02151c090206070f08090306271b010f0905060c15090d0905 69
    0x10b004144102c1c0c140d0b00316041550031500740d440d801542a00254058040c0411400300c580ca95038100c5c25085510422000a0004500c4e9202804000c004102041910a400700005400d940d41c00003410951042e0310136804510f01040e02d001040c90031010800182c10031034194a020300c6140001c0c000700e400c1c041e5640d00c0e6911408200801c0048070082c96242e403180322a0390300b035440d05018041501a116003e020302c03c0030006800341c180450490710400c0d000c4e02648003142156010703516580100740c90000c11031040d51000142e0b442c680f007822880d2082e040c507039542915440a50100004034596118541490102c2006071522401caa004a400085281400342c0d5890101c08504c20b1000c05a8544289401d000702c00c0501501c0395400c0c0c900c1c00c0820b0309505501807030758540300204c01300318401c4408981c0c41d80035401034411400d6807129241170001c040d2a48001861508a00f49070401135108000d01e00c1000e0642c800e80740c2056030100149015240390034010040b5441e0702444e4050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 858890449 1250 858889199 858889219
    0x10c020f190501020403050a0f0213200306030c0306010306050702010b030102160303090203120301030804090c030b01020d0e0a0b0705030301090e03070b011802070f0f060f20070302030c101b08070c02 88
    0x800004e5056030050b543c0101541c102c030041d420025203ea083d130170203901c14048081c0c0000d00740c20354868110214034000a0b01c0c00e501c0503030311017001c981009020a402d401000c20100944d0380034841079010398072403500018a420f10440003421903840064090181e841040700a60003600941c007002c00130b9040c5030200d0074144070301c00300341400342d40b051113095918040000300400c83c0043c06070003030f620a80c004100321b486426003142502c02040707440d40560010b00250b1906445990312109103003000d4803004402d542e070500030700c1640c0600d10945240d00b02000603c50795115000d4241039130300c100011401c101d91904d81030031220042c81b03030452011a0241c21100700038190142e4800a401c004418030401d1207041c1120116006002210214a8040703071803408140792183d04401d102020351140d03414101c0300e0000d400e5002c50401e030190321003889400180d000402c11801510905a004a000420031054600351407110140b1402d00242e03804010301030768000001d892080c0c0441d084900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 858891699 1250 858890449 858890453
    0x1b17070e0703110313120314040b0a060b0a0207080106080303010b0a030c1b0305090a051f05030a0b0306091605010504060e1306210c050414040f050c1908010c020f19 73
    0x180346500310710208440103c2048080c0458542445c5c00c075029040243c0d01c1126140210100d820244c21407580c0044103003c6804900184c070301d240e200c15480000921143c64119945030798100e800380c000160f01c02501800141401e002e0a002400705400450440d410400592443e00505a00c0c004050303440c0c1b00d040340d1600c9000590a03e14240e480c1c143c4807241414002c0180e40210f120740e014104015000816040c882e03d103038210f0500e1111000400c1c00c8500840e090303030014207490901500c89001300d0642c0d5007070140900426809000300394081c03c00040418a903415030105050045c1480208a25a0403000d6650300741c0c0f08560b90070100021a80150041c40d172a040b0307107070001e1110781c85600e1495a00b218009503000b00700000140780e81710200410f0300c110358001c0014241101c04100040d25100201070464452010ba80381002e000000c19400103240100300c8030380013100c0007000060000c0c422103840c084d1910241501038084905151b072020380e040344104c41d030f80090f15101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 858892949 1250 858891699 858891701
    0xc0507030c0b070506070903030504061407060e0a121b02010305091e01060906170c09071103190e181513050c090411211b071b17070e0703 61
    0x2440e4404040e4281c1c54580360140b00c82e80140c034046135a40720b214041207807280144007203030449070306d035a800e481c146c2814012100700c03418468451200809102d85400100710307025524458542800500609010b41412036030704d010b40a01d03c00780300051801000000c56600000c003d01d40a090109854680c009d80302c0c600580340100c0c0382940080d07502d003022700c10190050422501e80000a010150b00d50102c803004482c0403da80700660b108066840c594100b01400a5000e02c05081c90724445c0440c41c041c50455001e41c050418481c42c0e13881c0318032180e400c2180340043c1c1c5001e503402c2030080348140c2440b64a840240c64a103030f0f204803641401c5650382d03940c1d00c00701a8450481c1840503041c81c81c0040c90359000014081d03c0b581c03c04066131514040d6009813680e9007009903030b440400e200e078000c1c0c446001c0080c18803c3d688480c00310110b142c8420f01c008081c140c0c400c1c8940000e1072005181030420107072503003220359044402007984401d00d5000a600042d10503042c0d40381c41907120a0001d85c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 858894199 1250 858892949 858892963
    0x103030816140d0504051b061803010b15040503010c03050f1306020c070609080f01050c120a0906060b0d060807050a05010509040f060e0a05010b03100918150e15070507030c05 77
    0x38101d42d41c000b0f480c40f10760805810007400b451043c4116005282e00700c180c2d18050400100c500d801440a005c0b0300000701050141050580c0d0150000551510100100b1228251280360524859001800300f041741800d2281c01007400c00c03450100301900b8502010500248007a109150360341d0341640480078051130f039048490b5a0356410031200860359602d409861810188a401610300561020018032101805043d100d05e00340d209452820b208203040c1504560301604010360b59613100112030014905105034005000101103503501c0e0521800d004003640c8094110404a42020a007080292144106002501c1003420300b907403a58492000b140040c1500030414104170b081100001c0d00000025101d4040e03c82144184107680e04c8131001d03142884140e42c0200004200c403000c1007180d21903800081094000f62a450342e902d26501d800b81902d0890401c5001c00741d50740c0b003188215201700002c12050750702011303d04c1c0501c2d040a028000d80200f82d40170313052000080d800030810100748144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 858895449 1250 858894199 858894227
    0x71d01090f081509030306010e10140403032d090b070215070b010612050103030e010c081e13061112030c070501112512030c0e1f0807080103030816 65
    0x20220381d55030320300e6190b0351804404a4015404001c0114004200c044126071003504181c460041c2c1900c600c041c0030090b500c01c28100c0c1000103507460414078880031001000154040d03070343c4080f81c02150000000034840441c0d1610300448245651035103a0304000c112044600c8142007584805644c000b040030500c50300b13050b2145440000b0058108002c03e105181070700d40f280e032501c00c9028140d6070070003140c00c00e00020740410381c21020b2102035031007142140c07001c0e032050f0075241c1403055052120040042001e05c50b0701e80a80420a941161803142070b00000301050301c1c0c0703e224580c20119076510362088071a449a07040300000002d1070402100102c80079a03034010300030412402d40200030031712a00403140d94003203a002c10307250f4144910501118031650f0341000041c3d640121001069004101c1c030003942d024020441200e504540d00d07043d030000601080c60700c0680c01089a40000c10385100144400103105d1444014030200341d0200c1d8055209001040b00c40420021000540e100ca2000c090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 858896699 1250 858895449 858895469
    0x30c12030714040b0306090c0f0a08010e0601051809041407080309040506100e0906130c0903020907110307140109151a03010b030c010e04090f05061608071d0109 71
    0x2224414091040086104001030b549000d01c0085440030000d540c895485400c80700d90060012840a141c24902c41d40c01a210100491520109021601c49904401036000202d051300c401080070400c40381081e6849903003480c00b02e02d4502c000c0060200320134600c0c6818012107030100010204200e003904540c0365281c0c4401c0351103190340d40400c03551369405101c026024500701000700d03801c0c0c2402e10b200e01c0b0f86040c2c0c2c0c50303d510049039003040c000707607120003404c207a8005034181d400598035107940309110705010341b40e444400301ca0131801800501c00740600b03210200401203031030399120300000c010b43d22070325441540250048030900c2c2c00c034050280d1400c0600070241e00c88032a18038070300a0b030000c507400020070010314802000d01d0030903088030525400c1603010380040426070381a6209036100442c00d140100002880351460311003550071440380c54201c0f400d41c0480709010b007002001400001c0b113002454804403038035102e080100302006a170f88441e00d44400003640760942c1c0c01501008043c12807001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 858897949 1250 858896699 858896713
    0x1c0b150c06070f050f0307030f110a020a020909060609040201080406060b0f0705010b0a0b30090d0206010e0709030b090f011b09061b0f0c080f010c030c0804051e030c 73
    0x805840e00710964038000451540f144441d5854014000e4414945d10f10b0100d40c2140d40c5c402007a0007418030075136102c400d07596031032882c0580584000500124000d41d4001c0090402e648140309003040080e1110206902207020000c2a5481c4000103500a9081c42e00400341d0715a860001d010305850b402100c01c2081c089455140d2402040c0500380300c44c001c0c0f0091003103c1d1020140a0081040c1c09041081142006205030f2981480b20001124203024030034400d82d0055107552901e20416100703101650008258003c400d6410400ea601509555181482c0d90030560006800c1100e40c2c40020100900308000070310007001800441d980400302c10080c409508860030000300c000d00300514a02140c625080491007a1182140305082c102c00301900c10b941e95140c40f00c940300124020111038031542004d010070715010a1205101e20300d060000072034554000400502540c104c01c550004000010003008003180000807940305c58030075207080403d0811080826400c5116840721407010b40300e240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 858899199 1250 858897949 858897967
    0x103170f12061815040b0f120c2106062b03020c0406170a020f0406080a06152705040606050d0f0b0a090302030a03150509010e15061c0b15 61
    0x85540b4482c0c0c0c030444410030366949001103024841c0c4256440b22030305180c0c030550605030820358468070b040c0038018990512800320b03400241011401c1000c0020030713013004680300345509005452500401680181e1720a181214243d10354500004016a110f020b408508101181000d40400c4010401c03101202c00500903080203036840421001140c051840c00d0400505100c06007602c01928002802a00c80f00c1c1c01030302002241c5850782252617000e6940c580002c0c4541080125560041c4550070203c0c6050500506d0041d00d2030b41d5000850b40503004080030b0050803014144404d0586420340000c10340c580e07081c11001800c41d50030440d0001301c901620018890602803060070188180040d10082d650840410309480b007240d40280964801e200c2a052503001e9000001600001d0140c500516665000144959803c0e03101085246581040c0604a414488900b01c03491061f15450300d0300810800c031041d8a402401c60607200341e950308c030741c0e1031070390b1002c4a4091710f009595207191219151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 858900449 1250 858899199 858899227
    0xb03070c020117010f1202060c160602070e01031a0a060b0d090606170a0f03020f0d030e0607020c13020903010f0207061d1204061101091401150509040b0103170f 71
    0x404020707404200c401c0345011154000a0425040e81d00010315450f20758540b400280790000c0c1c0c0402241d010300148000c24401c02c080001c5442144400c0d80140d07070500d0f0400180c1040c0300d0750445070044035503100600209007030500d5241c601074100e41c600c50b1981d0b101c00030001442035400c00560240006503421b03081905030011000c040c0151001c00a041c0d5414560603005c0e42515002025088070181d8400310301092000e00c0c9441c000c0c0143c4910b0841e101c0c80500b010b4202c2c104002081da14180401000c20400c4a141c0c0102d65000800c0c5030041e490015280c4503002851610003500010364a410351020741000001c18100398055498000602c1c00318080c0c4403921301620301090b044c03c1d18944280006400111601c0e03503c041d443c041c00d250040310003005030041051990740364240c0340700040b000003410b000d001d10380000107040582c001c1c0700d007400c9003d03500151082d42d0200500000c14075280d842030441340e00084143e2028920001c0601c940600c00d503022500c400407480e050703081c0c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 858901699 1250 858900449 858900467
    0xf030f0c040e0304030c09090f2924040c020a02042c070312050a030603050604120807050408070b0d0b060316090605070b040201030e3406020109020612100b0307 71
    0x449091050790b40140c9001c0e540e0049200141c0741036a1104100014030700781d804140c405018109400029010b529213680310400c44410049944c12a100e06030440490031406030030082d02c19420382e4010550b14031f1110325285603802c500c83e642d9811040c642d00d00802c950014158007510601800300e54440c0b4580c54028043c0e4107070103249c0400484d0444401084520542c3d40c80f8642c07a0000003010811640c9422091000d014145d4800c2c000c80416410481144118482c00320030300d400c0881240102462000ba0555050100030701050148002c04174921040c0d44140c80b6481e00d449201e02500003510412880d19004040002800000710380310920194140d21a00d40100b86569000c003112644240b4038050490003c2034080f90042d0f20135080100a911a102251210525070701d50155003800074030309031020304e808a40800240383d11100c000041150340002c03c24040180c02003541d03442450b1407034550103807110014030050600714903072001d0102c2501d8107440e8900810f0260400c48 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 858902949 1250 858901699 858901723
    0x10e010501050307060c0308040f020604030f2405130b090106090204060f020105010f050a0b030a0b030d030207021203031e2508010819021c05010b03060f0f0a0c050909060f030f 78
    0x4d054021a4103401101c461501c0b66050751404180d9030b8540f5841c000e244ca122003241c0c800070420000010442c00880d050021b805440850009180042081c41000b42c1c0170810788800e09103010401a020301002204043e604003105498130341d10108264010300d80c0c0d030000d010f09440820040703011980011184c41b0f00c0543d40081010381d03285c4290580340d100c18401c182e807180c182e450500c28002e686002d590040d80d1170201144140901000a0800c2051102103000980c017040c14010351501403042c00a85444102540c9181060b40750003411a41c00301c1b04400d070b1803400d17000c18180c0d01202d10492160410755002c050383c0303024500084c800c5600307110742880ca01c100f2450101e48010320a11a000b15401401480c401001c0882407031055010030701a142e44d540ea1500700560b8070180140c80c45195128580303100c620b80100368898204010701a1491289080e107080328041d008022511038200454403d103403540c41000081c035016a003154a50107002c0d0021100c071020000480034490f071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 858904199 1250 858902949 858902953
    0x90609150405120105060319060b3304030f030507050f07090609050109150e09101406010201202203140d020607020f0c06070f0c08030a0e06090f0f0111010e0105010503 74
    0xe4000f002a400c3c0c660940b00150305802c4296030520b0041b1038800c1d9001b10748070703060101c1c1007041c0800040d2420b0181480070300d2403440c004c1510313950b003150394880051845400001c2c100760541e2114030030481c0c004801000d2010000d003450034480c00b04600c408800c10b01e0119000b95403140d80b400082c00700791103000c00071130400b0000300f001d00d168010114610300048103251501c4c503103103600c89008809401c510442c0250410414a402180201d100e00c0060240403081c50030714000081c00c552502c41d591801500402d81401c2c0e02c4020003c9692000c0c020031984445407403152045c401c4031482e4001080c6045181582c0300207580030407000c1444013140c0a588050b40c07400720a98a8942040940c80190041040560f0614251024008890141114100ca00216030b601810b0a2054200c020706a00c085050410f980c0d00c2070091a80501c00e90303071a0306041450008c2866445801c0010380b091074000c801d001ca6901c034640681140b40414000c0c4445407010541138002c210a001d00c1e4007034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 858905449 1250 858904199 858904219
    0x30417040314061302061603050d0f0213060906120902041d0d08010b03011d0c0c030a0203071704050d0b04030201320c040803160f1505011d04020312090609150405 72
    0x606900a00b1490345c1d0090074240c60040d480040740003003000280308600340881800800801c0480c0c0c444c000d804044101c0040e5203403124070104041e02c1c1d0070303480034080082a0200340500da52090103500c3d802c201d1030b40894441c19910005024219007036441d800320301f00e8417048140c030384006240e0007141c0240d1603600721030345c88440d04034903440b09001b4030502103c0383c083c0c06921035500f050340f80d101c155064001e04010f9140420390441d4130511002c801039001080040510226000701d00c44031007030760740180c5054070b0319000c03408103012110301501711f50030f40c0006002c1c54000e410550500885400c0c03c0d08035101440c00031000c0d60a4000c0d1840ca58400b40041c50b820860021607094816002c01941040240030303030552000900d0208543c40313112003001c600000d4219002c03d060703512a2101144641c10105414410300c02e88050121042c81d4409101c0541c5011502c20010250980c85565990844001c1107041c4106c61080c3c0d001240390f002c001c010a1440041c0055903800c803070100304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 858906699 1250 858905449 858905461
    0x21030a0b010c020f1003061a0c0d0801140f060d051021020d0f02190305031b031926090606150a14070c081005060a0b1e03041704031406 60
    0x5061102c8009400074146a194149403030209000c4400300c0180c500441c216440e803081c0700720035040c0d01410410300c0012030800c1000c5002c4c88001d10305495490f02c4141589014605910700000c25005801041d10086d58940c03a11010100c902e080007003042440715040c150003045016107640328000c0d04c002d040000c0c03880e840b5402c0c0700d11500c1d9001000b0b410040000c3e01c0e01c001c0c12551640c02c0742c0c0b0502c004200b20280b49900c0380d5a0003580140083e40d01c814082d10781d4141014900c0d000051074004000800c03150301d240c508003e00c650340740782444180e1124004941086891401c0300d01c1d5010040070844050000555241704003415154115400300107208003c00380078140c00200468000300c0c501415940d848042c107a0a8011510310782d547c0e613070b0f80c00c103810301c040c0c80d6070001ea40e40c90303108002450a1000e220700082114007900c40c03401035182c0c1c0ca200204400c1005200c81100000420103218550210444110400a61030f40d40c1c0c0e0b503440c207088115900283c00b00075005030400114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 858907949 1250 858906699 858906707
    0xb0108010501022e06210b0603030f0306090901020909070e15030c0a1823030127060c05070b090a03082d040213060e011a040b0307050c0f01231006020c01050c21030a0b01 75
    0x2014840c0c03100d0103045898dc00100204c10b00003d2107a421990309000318401039560486290142905441c0c01004000310814400345c0d801421140071040380800c1804603c00302042150003440003844c00707900d411a400b40007611185541d11060311000200003004c05c101080041c1191035208800821590801a484000403d6030349483c10804042411180114403107800c8030008803a0391500c00e10748560381d640c203c10034905640104003a40a424500201500a02c2503a0810185144090499160003030040240799140c100b0043d50500e0300840d00310345503038030b00017641e468101007402016150311403520306950034031400c0603210032449144ca15465480407070b0282c03083d00107164550303500c0480c00d0352180c2c0300c0b08112031540300b441541100d82c1028400c51440c00c1194000310020302450001051541000c0c0c0401041001c0c40380803c289500000d0f40d5004170301c08c0c20019151055840a6400d00d00c1171000e2880d4241500c4150490380c002000951140303807140d004010100010004407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 858909199 1250 858907949 858907957
    0x609110d150509161b0c050d0c050a0f030b0603011b031e0207110112090b060f060705010509061b040e161e030603060f090507030305030c13090b0108010501022e06210b060303 77
    0x1070031b44080c1c5a424442c84c107001a10451182c020101c03d8400d80c0d80c3c20100303001024a6100030b030340c0a080b00e400d10030003d054400b1174000404a009102800d00d001503103101102150707122007030540c0e642c40c241c50483c00c2d042010400c491440c00b10b4498455040c217480d0003511390101c900003840003540040c07010702c0b4490301481d15000144000c50740c0d82d00e02840702e11440c6d010201d81c004424009040001e02c2401800d2040e000ca001804ac1402e1544100a010946035001101d40700140030500003070310310701002d903070180c41e1500f12454014022020343c0c5603195010102c41e001c1107000c148190a4040c3c0000048030301c52032041005041080d600402c032408804001c1c03854000d440300b00f003c2880b5102658220342c2041b6960300d4404003008000800045070300c0701285030340b0f030708115403150323005511140102030a00281103280145e1000354505402109509840518146509402d01c40d5911001c0070b881010901c1c3d2254088401032458040d00090440b000c2c21000002001401c01000350303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 858910449 1250 858909199 858909203
    0x81f050d060e0f0613080f070204091505060f090c0a14070302060106120626030d02040f051f0c030f030906050f090f01110405062104150609110d150509161b 69
    0x1c0b0001021503a0b00921b90340308620400b10010701780319200c0940d0b19072281c0080d8510030092455260056003405007a41e100030013152184d0322402d501c2c4031036103030541d0b0a0740c00070800c1c07021551148110b80030755100301c40354030102500c039001c2900410182c000541c01d050341c4094a6031107151125070b0544054541d46d010315241c0c0145800d80c0001c070403d1041015469035107100340c03801c0130000403051040781c01c5903010745100310001d1820031907400c00f0790358622000181c04504040c0085c100000d8800708025030001d04100340b501804502520a41c4159030309540701105022a08041405503070701c68049e00d1500240c003c40f0700022441d9014403030040d24030381c1c6000b4541810310302810400341c0e0b003000132509000000ca103070070308421150203a00b42c070940c403440503d40703405400c2d4015400c460941d008811082e141c070100d401e882c1070400c191403200c141600f02103811000e00f6207520b404262580500d4002c0c0584052001a89440a00c3c0d41c482629581e003000c800fa6541990360194801030b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 858911699 1250 858910449 858910471
    0x405070f0813120201060e16051204080d0c03140f07091202132a080105130b0d0213020a030b0904150908190203190f081f050d060e0f06 60
    0x5803054080c58181e907201004102c011014001601c2e5100a0400d403102140140d549180901020625030307000e54005800482e8522106580100607040340300d450311414800a0342c800080400c5695001c40e41c4a1a03228014001c07941106005005451600d090034040800f42c400541010000c17042d07135101b003500d40c0d81c0c001d825180418030880c1940c1c0b11000d036001101100c40c004015124003d4040403030020500c40310700c50300ca041c000b0840c2c0e90b85051401f0400705c08010805565100e601c5145034003450300c0000c8680c0d0380c20024281100360203000790001c0b0300c0303944c40ea054506a030280900d419070761001e01400381701d2030800010510072140140700c412034414072828494160311404000d0300c039681c1e141c90080d07240518804003220000d441c0050380002009103801c44c0d4841c032109104030074240075040c0c4080120240c03045000410304200e100752045541c544030300110443c2c2c000e01025014803014059030804002509200c1e10681c294481e01e4800c040c030000014500c1d20400c40c0010b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 858912949 1250 858911699 858911717
    0x106050313080f090306090c0a0e01061e3b0625030c1a0105011d0607110102010f18050708070b03040303050402011707082e050d020607080705030d0b040507 69
    0x501c0040907040942081402070f400c1c801892507440c00c004032801009064020200c454a00040004040058000d43d8400190b42c00400070305410400046620700700100b840c58002383c0c40c03011160180c0e822618603c42c02c49942299040d00100f060956110030a80c20102860a01007807096505c00d4001e035420601d2016100701a00c003036a0400510644286003210140c0c0c1591035107802d04254806100d20741e560000100241d68220f41444030441100d49000f403901d03040c070001100c5000d5032501512a952030750750b4401982c406c1d480b00b030070620301c640d01300304c4c0e107a9401654bc03c4d1481a0001c035413070700ca211740204841000190035000c90340310003282e42c40c65686580440140c58041c000700e042c402c00265008000c2010071001d032150101c0d9695404524002d1624000800000b80b03a450400c0c0d86030080c41091516070000e420754205a510007207400d000d1010030300910035450040d11103c8081142010410040700070280150794034030034032a030034100007000229081610098040f4000301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 858914199 1250 858912949 858912953
    0x90106140717281805010804030507230304212406080601172418030d0504082205010801090c0c0209093307051b1c080106050313 57
    0x11000e04042c84090329040c02d1030f080c201d4103000c0c681c00c000281d45121800840c5410707140c0c001c0c83c124000c00d00744440d480356440c100001c0d0508034060806003c01000158090900184041241c109203c2c94030310b082c881ca01300d61440c0c9a4109028441c05100e04000d0000e100c05065041c1c0c00840c0c210030b1980344074290341100103907181d0300404091100d032030b003a0006a010007480410b00030080c1c8801c04100d4031004a845017864105070202411654100c0701050201500c40f0080d417003400d0710f48104101a100ea0300381c2c0b660080c580b0390031590f030078001084200302010001e0a207410600a007881c02c0400d07240c81098005240c092980020f01203c010000082280c001c407850913182d06111102a0075a00410b4024008641480459000002007903828003c0031182ea0446250f83c04002c580070300c004094a8460054018001c1080100d2869805444030104a40d40400c640446540f071008101d914061041d003410320000c0741140c000001c45501820880744200030022202510100a03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 858915449 1250 858914199 858914213
    0x603390f0809100b130501330210021303020901080705010f0206130206070311030706140109020a1407140d0909050f01080c040504031803060b0f1f0c0f120503060901061407 76
    0x102001d45d404250414005424100c510449010b018610160130072001c08146080301c4550050894100380c0140d920700411950118032405c1d04001041d0250343e950301414049500145038102960000c401000003072122400100403049401c2078880c4441101c503800160303110351044481014148104402d4401441e007200140700d540d1180c00c2c90310101003402440c03032031500014000c480e20740d5200c0c213081032205540c00650040400f010305501d8a481000d0051207070018100c0402d4901001c2400d01c10004010907402181c1170b08070031244030407034010008019207403030710070000038628140c049861260b00001007030503590200018200202c1c644c052000400b07008105030104038096100c030783e40320190408200254000c01c0e010900194240400108050b600c04c2c03540300c0e4041b01028202c07900a000d4205031518141418481c03100182084a0b40100c1d410000b03240b615040ca5006405c0d811101071401040c7c01e940450150f80c9541050b103260102161203040b04a051100e84009845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 858916699 1250 858915449 858915461
    0x705041103040507030f1704060203180303030105240405092d100e0907171e01060e041403071506091407020723040606020303040b0c0403020a0603390f080910 70
    0x10030000e2610b00b460302001d4247da80c1098029a00581000540784215040b000580200480c01c40156195515010003d0b040b014410600c40c041e0000c030424020191011080c0c800070301d0040c0c0b00182c1403800701c6404842c140203044181c030383c00c68840300482c402240340324948145001e804903542e56007402c5040700d49000080c01c4015502c124030f0080f030b803005e1100c1c010049038441c01c000c1c202010001d102a1860007600302c2d03000382c1c1c0c0c50401c0c1002886890800950007580000348080c0780740000c1481760461207904006804074845107020032201c1e86551000040b54812841000105030a0a0a41f406d900c196100801a8130480003403004106010380d082200710b0402c48400030100100200d0140e131601d502c4240540c01c0030080009103d0401c6602d9448140d08074a00c1c680b0741035038001134861500c4d0044c3e4040650300c010708400d00c400120442c881c1d890031000c002d07041411001000c0000300300c076510700020b03203500140c3c4503060040b458540648000320180681ea00c203880050300400ba = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 858917949 1250 858916699 858916703
    0xb010518030f070807050301060b03090304050607021801060915050306010f110c1210051b04180f14041202010902010516020303130305070807060f050703030506130e0705041103040507030f 83
    0x381d000000c0c030b10b0340d040000d2002022100c001e400301501d8101010308654881c1d02040c441402042005030700c80001c400c0f281660350840340d81c0d8a401590001c03c00e2003201d90000d80403210824004a8183d8021980b2411207050200c010110015140b045840b0300090701d180b400700d0a0062000e0032140130794482702241034510b0840d02c840880d800001c02d661241051030409800c000c81c60f022109090046950051f04002c0c500009004018404207510a0344201402400c40820195100c68190450311410200410034084003502600208000074166011664080311661060410f070042c003a07095600d40584445040c10791002c50755140c540c1d8818101d81c540010010f500000031000710100145011740001c0040b00d0600200b030740b0700a242e40051042c84009001e1200311070340007086a010b1035052801040716140c3c03901080004a1282c542071141d42440d00d501070003200051040d0490320700700d8090040d52080c0c0145240d41c401500c01800039009027005001061180c0b0040710082c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 858919199 1250 858917949 858917953
    0x30402120f010c0809010b010806030a14010f1e1401120b2706040308070e1e0a03020402040b090a050405011410050f03040c03140715030c120e01090c090b01051803 72
    0x4036140d55440d00310341c00fa01e0b4501c003207007060007802085034003440b54642d03042003800c000000e424418002540d8005020000300072030310480b0a515401d6003034100700c400e6400044148000b4101002c0c58204209502d8a86001803500e1203024500100c6401d0314100c1c0c0d0601c400d00c0c101000c54070b403c80c0010000380031409000c46074009604c41c02c6a20425411103451030040e054908041c9030041c0744042c040e000000300040410029000d035180c500142c880a04404684000e10704200400c0140308180d101a510520120340001e80e808042c00074840340c901141e203000d500341c0720020401120002c0c01040b1051210380007400329401d000410a003541c0c021309200e03050100e60246050340342c1c411502106c007010388070303420000c001d0784200c0c0750300f001d02481c06442a20308007561040b4843c100d90b007082c03c05488282400b4030602071280c0e6000040e41c0401805815000d450260180800000840349224802e1001500130b24070310400844a90580d00c2a181000b001203002522106015141e458 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 858920449 1250 858919199 858919213
    0xb0f16080c04051207031a1f050315151002011a0d0f0605100f091509020304030e100e060403260705121c14040201030b1206160203070c0f03050c0a060503040212 71
    0x4110312130740b200c3d07010b0101010170089146c80c88d28580007610300070001c540142144000d001b039230303008182088281c0302c9100300c20865075800c4191000c0c0c0d40398912a034124484103920100142d064001100420462209203010b4450b42d0a1084503600c400c030240c038262400359100b002940940000760054140340c3c00c000101e80700c4400c15a00d075040d6100c09106c96484098494020300c10610400500d4140011400d52520340c40c003600c291f00b0700001c14407810544140300041809140b403450350f0080980b40799141c2d070300c91801d9a0442c0c107110440045010000ca0070b2406590384048482d5240c1c00307405440041c20007448440f00303070000c00c0c104c0100741c2441003504403c0d03910310400b140214208031800306801d150001404440101c103c90b03004004003004e641c0401c50004086401101e9000860364846c88064102d0650141e082d006010107400301d80000c0140d6146850015207000fa810b60300d1689149040180302c2c283c501c41d0b4800301d101800002c01501c2d02c481851400081d08058500f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 858921699 1250 858920449 858920453
    0x203060105040f1e0e070e22020111030c0c15070c14012606010807050f04140312040e160207060828050c040608090c0604051c0b0f16080c0405120703 66
    0x503016600c4c2d10041101e61324000452030010410240d0300500304800401c0d41c070300b01080380607240150003000b00d80b0801d800b0017140071a441010060001c0c00c400c0c003929121041409480d4a405000003814810340c0b030700241e484c032445442d0483d21030560020f07403041c074030b0300d001c1e444e481d43c2490701700c1c0605210a00e00201c61680c0056002109404001407200c00c44c83c2007030001d4401c440281048003048010702c2941c0500c40e0070400c0f05e040c3c5222501400096507240002450f01c0b000e02d079080d060a401150001361400203161007402070070000c540f0b0355190b2009900326501d0100d803044030001a01d000100391510584000580381e808421401522800c4141c510070903603074159041422503d00080400180d40e1041206d5004000c100103031050141d210700140c0c043c0118043d040c400d90600300d00f020b83c1e500c50540406072a5010310800c08500e0103441448207580c045886a2520f4150040c0b005040d00c211130440c403030744816260504190030207050292484000c1c0040100780f16003800400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 858922949 1250 858921699 858921731
    0x20a0e270a02090a0903020d080606091917070f0911031b0d0629040e07030513051b1807090e0613061221231204030804031b0203060105040f 62
    0x120494004c0c6020409951750318000f4601210503005104011105003441541c0e40d801b0129400000d00715401ea01d031150b0049050355200050f132228015001c0c3c012914520500031401c1c0c02110814006880e4090796020300e07070280c031201c0c40e1042d08407034200001020710b004448800d410b580405180c03810048120040c2c0c0c100e6640343c1000400001c80e414043c141c001034020a10000307440301c21103040c50300c3c00008000c810340240140e8185913795000824584840d0180e44007150000f0443e80c00740712210340d0242c4406031242042c0284000929482c40396101c924050065580d079541c440c07024680f1503a80c041c0400a0076142d0320072240c111001c008545802484090030503040c91118002040c0f40c6201c001c035491003030447d85200440100140360b08042c211a01c2d540100902070710029a03500881c0512660140401e07054014080c401807560100000b440740d8880e031506403c201c0f00c280c0b03006e0450064030000b545548100700500550416402522100403a1280855185884002c1174 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 858924199 1250 858922949 858922951
    0x8070f090c2a020922060506030c0d0c0f060903080306010f031e0b0a0608010305070b0a1b2306190e010603061404060c0504050607110f03070f03020a0e270a0209 71
    0x101090042d242031005500c4c0c50660660003034680c11001c2c400d51179a00610449415410020f06803070350b02c00000f041610207000801d0b211000030014081c00846d4a002c0c4507415007804ac0904400c98a4804176074107000d8035103002500d401c0740804c0e044d80c1da03017001110907800e503030340c0b101c1015158885481c4594529003d01000c8203904408070781c08410781e003400340d000c0e9258416400c01900743e00400104001207101c000f0795810031801c03a170700e84941d201074031514640c43c43c0095480e41f5151103801c1c070501080a9025016004e024030120300344813801da0359801e05448090a0201c0036100032408003450380b10300e68406684001040b41030340c0e42c0321081210a2204002065030a07079041000b0001c0394881e00e035506a5600f003590509050801103820381c01000c100a001c1c40481a5090f813940d200701200f92401401001c45045540b14144420015410721040740240911080428003218400c51503101c0d41c850f002401c005050040598a0b205100145001c14001ca0713141c000541c0b1160081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 858925449 1250 858924199 858924257
    0x30a17100b040b07110f0a060c051603120e04090201090902090d0614071106011203080603150106050901020c030c0306070c02060d06060302072009060402030901270c08070f090c 78
    0x45611030545081442145801d071700003a00c00e103200c0d20400855513540007203100381d890380d00d011034403040744d0b00e041d51814221100c01c07043c000c9480320010070802c0c22100d6900906087c0d80f40040c82c4e0310b030010300051310368071400203020600381c201c10300100400b40e0190402c141c00928801d0100505d03198030088507101021591260b0303100080240e00c6030007164105042188000034030b80742d03150205072a486101e03120010704102c811004500e545e40c0410540d6598a483c0820291550751040041c1613540000540c3c0d0160054100301941c910300810b0b000000900900039100503910f07203134200d911b942c1c0e10404070b0f48034005000341c00f0040070f984212000350841d5100160780b01038a0800603984800b00c40000814035040315042e07584d444244015401440680e40544c032a00da00d200706001d4103200d01d801c2c2c852038003400f01ca510240c03140f0a24486501680c042c418058840c42c000e900d8001c1402080d055440e000310170094440d86502098440c0d20610703041d0b040408003091401c802c4514258 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 858926699 1250 858925449 858925469
    0xb1204080a090b1204060b011b02060a26070e0d03080615041505031918060914120403060509060906070c0c0e040605040b090c010c020103180f030f020609030a17100b04 74
    0x405c02041164450316140305400d080c52140440201403850880c19440130090140c03402081030710015004100c0c0b150a1841040c80301a0304500341d41c0c800c0400011034200d400070310103400d40d1101d03007080c1040601c850780591b1110041c0d9520428410400b103060302549203040200030004201910340050344e0005520350f40c02c0d9580c24a4200d444004510100021509242803041c0004015584082c02e0702544140046440022410007102c00a40314041030b40d140076058066000041c07950081050324492501040140c0b44d81ca85e444d5204021103107581654030110120b258140254071a241203880341c409880115203c591004450341c09170b0301201c00a884400303000c1041458201254010102801025080486400202020044a40a0705041c0e82d4458800c840c041c07031010000a60b00042b40d562058818a0000c0004201c180c0072030040c002ea0002c948110300203c22100c40e6072481d0303031b0001c80e0602c5200d0201f4018000e0807000031501d61007000a0400a420b014200601e04607034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 858927949 1250 858926699 858926701
    0x141b1e0d0908122b050709030b0a150302130615200a02030c2b03020d0206100b0d050c0d05010b04080f03090a090c0219050a06060b1204080a090b12 65
    0x100290841c0c0c2542c0001615800110a50500d8400e40342616616500c40040000100c41c0c0c2c00c0d180c04000c05074041d540d040d420030307041169098001c8095030450780302d030202070240e03911a0444400c4400640340302002842c109420405458a500780000303a1138440d0740011865540c40780441c40c01000c0003640b02041d801c41204100710318110002c171031a007441001e0444004180c0c0081d44500c40325144a01c0754610002c20035251403401118185095111000c4036a00040d00b03000e9079840140380a04010b1080100140b8400c1300085000c045414000c030345030074a0520324118000e00801000c0c40700b0300c142400100d84c00103240c0140ea008004001440399103604000c000f5080001d24005070710241c0c01080302e03400b182c5514810b0021111285400510108445012814021065950f82c9602d0680c1701c10310600401080100d942840f0352401c001d49075035407a41140074042d61901c80c0c140040c010014021400d50801001c45d081d0311300d09500510744408010340c1641000c020050a050703a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 858929199 1250 858927949 858927973
    0x150606031b08070e0135040b010506041a0f07120e0102070902120a0b150a03060e0f09031b0f150108120408030a12021b0d020d141b1e 59
    0x3030070140306441d24011440d40b0f42190090300e2098a041c5070383c1040003001d882d8035180c80706040001d03104182c0c0406000300b25039039401c070904001510161241031491f000002d01e482d201049504a0351014030380032440141044401258224404045255108012500c0012408004a03a001c502600d9801d50115420002490149140c0080c0280e5104200b0360411200404116030702070700d14000801c10f0b203054004074000004000d001c0324415004246a1111038245d0862020f44414403069026641c500034085011101554800d486410400900100c101c2d040034240d0790b0305040089038026035801e04403610b026040710702180c2c40c45421b0010701c00100d00f40160220060000800c900700781c14000900e0300e074814444800c040c070448040b03290b1b440080e07170191403500f035400d0a82902c00c069041c5440c0c407100d1400d510001070244865600c43d03d40220900c4c1d070b90000f03240d02c43d41010b40c88030104c020b00550303103c6000e07148188005281c2092034008520390b44003007640604000c00f052 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 858930449 1250 858929199 858929231
    0xc0a0309060912140a20010608060c03010311040506100c1b0602010e160305031605010f0510031101180b090105070510022208030a0e122a0d0b07080415060603 70
    0x44c11556048000030000004529480510042d10094070700308040900c58901d400d0703004262503400342407240a0301e420441c01d4030034440a54100da02641c0c141e8011042c807800c01040711002c44040b070340400c401c290004607074404d21259210f00e11848072480310300c1d40e40010351540101381d070220300142c1d101c210507542402d0a00c0041d4940030785001452149080d0313514a03882e401070000480301c1c03540d21124039050003000d4110701501c3d400c21500b007100b800c200e5a41022030000740405e4903201c0c4032140d443d030039520882c0450604900400e6410800b4207052040c2d03920b500c4060311358108141031010b000401c40074031441d00c12603d01c0c980141e0b40c9800802000144260034510003100a043c403003004207040100407194014851b1030804065805000042d010250810304042c1a02c40c68198030300314150606032400d04441406500c48841d540802c0180381c029400c001042440030101140034940203441d002d420500c04c075580c512078103000342010b040300d034940d0110700002d86402c4030803103000c06 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 858931699 1250 858930449 858930467
    0x30a0c03080310090b0d1103070312020616171501030209132406020c06090120012405011403040507120f060b04020703020307020f061b031803150c0a0309060912 71
    0x81020500400300d03c0400164500002072002c7c02a0b001c80304402450b5a044c0403050103113a10000d0300705010002d11f4029561031040380c0080c200000601111a15401111241d0b6101401450032800781d072080300050313111158480c51414150203101d1241d1744e0f52403841503545005100310008141c100b1142c0160030f901161508040d841c0e8644040c8035080d40403881e4443c41105070740550381c82d500d00780101d40c00c04406c8842ea000c0c00501402ea0b800b96010b4200d03e04182c2012507648408000c09402d070f1050355a40708031404030f403041034403400383c041d00c0e0b0203981c0c4540200291075030950b031480450004801400c040b0355440b40d9850000030412240b00f003019a03101918110700300a42560040d50707030704c5980e038040c0c4110514440300c0e201ea990b030405c407803c4a030500040da4520201c200099940c4d04000d031a1100541c044540d08030a0800080c80c140c08901c1e1260011580c6490329003072220b42c80701c00e28600300f54031410b6600108256000746008948280349a10918800440050810070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 858932949 1250 858931699 858931709
    0x216082103061008040503090607140c0102060105061e22152a060e1b1c0c03200a14030607080f06040209130f0e0f0d02030a0e030a0c03080310 63
    0x1409106005540d01c6060b69032030303040300c1c41c14030801c161605e01b00306140d8060b10b130b4115845030f000204901007001240e20607800c0c0352070000b200c5d5401c460500681c1c9424003401041d81180c824416000444500020124100da04201e503a2501042c60040c2081c0501d042207035618190245d0100890400c80002c01e03505025458019040441a004552001a011000c840004484a001050020b19405a81c0c2c41e000a021185000302080010a614602c0314100e80b19402103204451082a95045400707440d50110300d1b002c80e50304583e6020b1074001d08100e100c04c0302c4181541e11080b503c60380880c0c000f03003202e0081440c600d82e071b020030180f902c10000c00180c200312048051210000303c01d1030807508808101c6016844038034440200e5400c080d00001d444a290822000f84801c0903035a2002e001e0007121400e0355414091004029600c642210302103006a008100d00b01402d1304c103000105034800002c081d0340648407640c0301c1e14209d54042d00b065401c928000705024641340011300100040c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 858934199 1250 858932949 858933013
    0x405070f120e0d110c041d010b03010501030203060a0903021204081501081c030f0906021b07060c0f1106040b07060f060f03020307090908090a0b0711040b091303021608 74
    0xd032149650a0700c6400e224144014481c0e00d464041d040c4a00f4400385070300c0180a081040130400c6950041066410450340e45036075441d000c01c50201e2b05041c0600c4c0c1c16039030007400805141c0c0340d4551010040c8141c91040d02107000e00707030118403880302c00b0f8014401440060024044103078a04006064000180e002100e01c2d841000f2001700381280c02c06004d010609401d0000d00e10300d180000350085c20300e4100090016100045a501903070390700b00e6a441c003403800c1c01190260341c0c5468040c0ca1106081d080a000840c044400e18001492045040c01a44000d014981019900d980c016883c0d040030100300d030440d441d002c803158488400c0c40b13158020000b0b040103141d20341c699008280c42e02001d0154000c8075440741007403010f000d0810300312402c555003e1b1040401550f12031046000e07030405c2c1c8080b00c03908854a42a0801e14007800340101c440b000406502c030701d80b62010503107101c0c001071204405501800304480c082101c110f48401c0100b20050240081c180c5484441400d0792961490140702 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 858935449 1250 858934199 858934211
    0x110a031406091603111e060408031e0a050301090b01120f02090f090601050a08060d02060f030108160f0b09030a1209080f060f0609040c080a030509040b0a03031b03050403020405070f12 81
    0x4212154141e044041041c2d90700211072409501c0300146c0c01783e50503c2604036000080000c0c2c6600000021b01000500741801c1070b0a12408070310510600c07543c500c400c0018018001844145d5043d404034200c003005041410b08452140e801206480c1d580214004442e40031915200c81d09101d4044080040b0448485146180043c00030302030b4016250f003c1704200b581c01c005007841d1201c9040b00140f80c0c004012588400044440070025030090042c8107050040d46c03492031494094880c804140c910100102e0021802d00e0400304040c0c000030384007581403190180f040046070700c041081d10304c070009590b068101d90070b2504561500c1c086002c442c00660100040100382c400c0c0f06030440c3c01c90003c451017034664a5609114440c141c8581020510f8002e11201200305600080200b502000030380302404000070140800034184818032001d000702d48001403160b003138005c8401c05111a07100c1c0c04c01d981071640b01e802160031560104c424102203a00740310100e8030b050b08006843d0070a41440414020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 858936699 1250 858935449 858935453
    0xc010510051801180c0e09010905010303140c0a0b360106053717060a05010501020c150d0f06120201030506030316030c23060a060803070f110a031406091603 69
    0x518a60800c1401890380d00d0281d041820310407029441c40003c0201f03264030650f1610801c0d40204002e00c02100840c600031440901d501000003541c0d83c1c554444094111550703141c8070606204d50090103001c5540109034081e00300c42110b603404070702c4500030b503d0750003011a03820600d0031140907400151080890000519007151000e40801c2800500043d003000b244c42100201c1c92400d00780c0007aa051741420903e001034050004a11f44664201841404583da8400c01a80c17585a00700120303401c0b0814134001c00c3e8035440c04c4001c00c12103020010000e81440c0b2034810400303c032000e4015002c2d21001d4406501075685c1030295541241c001c5014510340b04d20078014a03485684120002d0901c82124209400e101803030701021010b0f001d240c240c07142c1c645080a02911034008950343c00c07100707280540204143c03c000094030030305584070344240348417072840d103031001151000c0c80125400040170034088005070564100107902c80d41c3c0d0f00203001c1410110340c810f0500341c0d0350300303c08800004d01c201000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 858937949 1250 858936699 858936719
    0x3011401180209130c14071a150a0b0d110c15060f130c080903040b04090f1d031803030a0c0201030f0e0d0c050609031306140c010510051801 62
    0x4111080e0409040d807200d401c01225000c1d0182841c456403084001e46641160b140c16080322008004a566059034908141082c00c59070090240c040c110030014249030b5846100a5070311038229482d41c607015081219400040c04100c00c2e50800032200178041012458074100d4011007200c0386011f5072180c03e103500d1002d403d944440711101150840c0c1c0d100d02041c00d60f00d80b0310840910480c003400301c100070b00b60400010040c1629900344d40004c3d4210000500c003800c08000d079400d4480c210140345c907241c5080c03c224060b129100e110004c4d15580d00327410308000740290a0300c2c00208000061512a8407002080480501c4401c019019410812984070200c2e4007c10341c8011b5030382400d001800500a603895001803501c104217440c3c61145030003041c0666000070030304407014400c000703c840d81d0747d8070184a5203034000c250580000005000303040c0700003405400600e0310000503003c0f090410b000c6c01856800e40d0001d56401e209085184014062400d10030741d003900c213140c0303201150500c1d403400c00548 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 858939199 1250 858937949 858937951
    0xd031a0618060f040f0905070215060105030105040e1f0506090705040311010f050c0a20010c0b0c030402030f1b0a0504050906070828020d150e010b031005030105091b030114 76
    0x75215500c00070300115401c4100b010348003e00081c0000a00550b200c6d112480100805e4841c5c0001d4419103130700540a0680002d807500c10203040e594941564a00800d002c040c08070507005080c0380c01000180032541f03010b00c01c08405a4504c000c0420b0505000e800d20041607005000c590801600308801e02c04240d40500700b080000d020b203022100b00880c60000c54050082c1b407484806409501c0c0340c1c03002d2000721442104c540700707501c41a40050300c0350030041d1024160b044004000c00001c0c0f00042c418405000507640c0540081c00b0741e0b150b0450b000000c1d0a043c0381d038080e1b10790b681300924400c4060400c54500c1000c0c10b07090f00c080120303040c11031195680f031000801000c1003180d0400090040c007070f0a0302d0014203080034001190320b885820000c0000c1c1d0002000c8000f039620780200d03040e400280318409401c407808048800c0c0c0c2a4200442c000e0340b44d000500550403505211000140b070f44091151602c5840301d80c01410b08584102d0544140c807004100c420f11980c10300109014030144c3d0101c1d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 858940449 1250 858939199 858939247
    0x306150308031f080a11030706030e190501090212070f0501030e060a050a151206050a06030c0b030c040e04080c120406090b09031914191110110d031a06 67
    0x80141c00300c0e58224000c0c0c200f101c0e007020300313070b030154200000402c0000c1818140d5083c0071010790700c50a0321850114104c52640d41c00b084c1c0c0c1d0b4072404203a1009072021900b40d840c42d00842c0081440c40182d000300d042c00c02c4814600c80703103074050203080052607401410706010740400d00e800e1051044007149581d40d0034014002031600360f03a8101144400c00d030350b845003400b40136003084a0300146d605c0188400f0485405001e0f0f4036181003000040000542e8850041035a0f1302c8a2a001007038200002c0c2601d54000406e0305002c05010400400e90300302200f142c603c264450707032605640350901c85846061070302002c0804a505411320003031105640000400c070540342d010640545031804200000e2038054040311059010070750382a040d00b84020b800351381800c1c50701c43c03045690240c0c030a80304400750540703100c02a152517001c40140c2e9107860010405e03a00213009281c42103261101c18802ca0074014441d030480301203559103071400a4004402c205404418044030042e09204011203330850078074140c003030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 858941699 1250 858940449 858940471
    0xc010e01050403080114010903060e0d110c0612150a030c031b032406091b110a020904020f220b01170c1e0f040602070e01090203270a0f0804030615030803 68
    0x100f40b01b241d00c9042003200440d004a820f00c0202081740c0380380d442e12030100706040041c4003a0f204005001c40010109080f00b4080c106519185104210a02c590f6000d050003004d0900e8031246000c0d0343c0c6650030503015501803086082d03040c0c6546498443c0d2440000345086d923886243c4108082603501501c03556441c100e5000c00520701411440300f00419158111500c07891030404492017441189165449a92403a100c1603030620780351a400d9035603c0b09a00003548800604002001414604041c25080310041c19101450080c4492414100000d482c024000c0d991a1810f40722580e00001c4000740b00381e5004581c1c003902b00321606000a208100420601c80030f101241ea10110001013283c9096100000c080d44664032028000e482d54498458407504001280020072007c903640300300c0b405991a90308940c8603540c02c4421152041004e51000c0e07150041500e40408a4040301460400074864040d8a54540c01c520b0140c04855425501311100e5075401e10030300000c0d5540c1304613a001107207044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 858942949 1250 858941699 858941729
    0x14070305062b020f1f051c051335030c041e05100e0102101d0313031a220512070f0c0e1915050d05030c010e010504030801 54
    0x4040345042100e0381c10030b0002400d01c050036905030b00700c0c038804099600c22240346490b201000100884c10f0395083c0004c00c00c0301640c00340c3c80d030180100c00806105d0b680c807429980c00132514141004031182114400300724070126001c0e0082220112107660020180300c1c0c01100703031414841c612280d05900400310216400000403c0b08010503c2c1581e00801000c203821368411519500c44900c120f861060324040e01983e98000e2500703015240d010303078001060723005045000d0a0902d07600074000074440e20388604034814104940c00300510040c041400103031840020a0301e0b45c40d0001c2d0151000740e012000e100644240030a1031461140150404500788840c0c03400c4416042c0a0300f80340488080c802010000181a002c20108041b812401c0340034102c46040903a5a500da440d03a5181215a18a11581101078401141c071652054003059080c40703985075030a4035040800e072011000c0009480c0c2e984003103486450703042c0c02d004403181d11a54400034441400d19507030203491a001801006807401d0005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 858944199 1250 858942949 858942961
    0x20d0f270609020603072105060d0222050108010204030201020c09130b0903120114090a0515011214010f15020d1e020316060e0f0a050a12050d060e01061214070305 72
    0x50098002d442c1c0080c0318560700e042090000d4851841c145410111446008008054540f0352280307078451035014040b24030469180d801c00c8400c00c0e142c146100140da449040040383d100a20459000c1c00c400b03c00103a80d58198000a45040c2c5600c00b180d03c512041c404200054400040040718a1381c0038050b441545c0761000098151b010b001d21440441202000004800070300610704903409900740c880c143c81d503d03003005100a540f0308891400e0b5010410b18070f00545d501c907400031041040704000020341021881040d1100060a80c4a40d604003003441007880440f507814603241944034580003c00308000120400341880b8003664a0311201d040c2c80103126681c034024011174074034803480b10101d0020000b03460510000c08402e240711480c1d10642d0010800f61000140407221160000002c02c1c4602c401d50741c540342035814200090400000303008601c20050355009050141038840d1050342150304001008216520300081c0d0644075060401d04d80b04900d088082e0394114207645000308540d500c074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 858945449 1250 858944199 858944201
    0x60307020a21081812130801050f0f07052b09050d0305011a0c1203100302100518490b04020f0d0503030a15051003020d0f2706 56
    0x1100016120403050080b54440401003036180b15180d1031030303d40e602107489500040500d9080c0d0074505019501c4004500384030b01e0130a001d0508040d0070507001c00910307101c082440c20769000303171442e14a40c843d00050004512000c00722991014191410700c1c14840c1078030704000c48100e03200740d018104140c4d82ca010410a8643c02041002d0b800400f1030304443e01605004006003000d10038030030480401c03070000e440070100c20101c42040446000500c420400307810707505d18941c0040d1142003a4803214400100586a420920a0040c0d0356161103403900d81711010011034400c4203e1103485058404d089400c055240b00900d14545098245140602c0104003030341c205420200300f0201502c191b00c000801c1000071805a48210310980c1d41c140b494007500244401513440b4107006000d5081840001d42480041e0300016841404c3c02c001c084165580001c01c0c103070b142032440e603c0000d0b00025200240310682c01210580e000d00d860400030030020b41403c0518140c0020f8400342c050581e10400309001035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 858946699 1250 858945449 858945463
    0x3030c030c0b090303060f100903080904022a0c0301201305090c0c0c060f031b09210606030a0c090f0609020a020d120e060610110a03110712050c06030702 68
    0x40b1140040c41814001c00041e81c0360811155284542001641b030b5a45042400b40121842104c0c2c0ba6001701c5400e595a082241e00114a0390f90826824007080b610340341250b8030444000c080c001c188001e09680301c101810b21510858280c0a42c2c18042e401c07466003016900c0c1c40344031300c0748024282c985030754011507960034000354003042d4804508001d000041402800501d02641e084080740c5244504005100c00e902482881803201032083c0009440215848051085800c0300581b0310b260222074800140a9001000003d9072000e82d8454407217144c1c4108a0240c2202c0300301d005001c1e0140071758642c5441d5105000e1519030b25260f04540a601c5880e40094000e803140300300c25900d4600d0420025a5501c00b5566000003889264a0703a4151125110301240000741402a00381c40c0ea4041c00d02800c10030010480d405c0041c0541030081480b410b000c40d000340791207559042c4019142c2c110003480c0450310f41101180c0d0380c4010038940043d2000640110083c4103480443d120350790030400740e0401e20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 858947949 1250 858946699 858946703
    0xa0303110d0606020631021504030602030709030b0106020105060d020f040e100911151204030903140f011a010503040f020d0807060606140405100c020f12101d0703030c030c 76
    0x4240382d00480d85a03000710340280302d4070700c0386035401e01c203506409444010840a1100000181c066000c0405814400d48540d0b40307c40844016103030660381e5031504200d034411940c01d0f00282540700180b04201d11251440d00402e5103100a101c00d0401d54001740903030b094140001e02c00ea400300c1c0d070b0262507111900503444602082d4259034a81c240804024041e01083c2c0045030100084004051140307041c03480034407020803a016031405c082c0c4500c00c86c104010058010750611207280c60002c0001d00380751070180303051300300d1000c0e00383d0400000440d400c0d44c800180c81e0491144550001d291a6400001d50740c0c000c1e001511624880d02c1800442c400d06086600a81490400100c105c10700078583c0044044035000e65683e0f0507001c000314150f180d4040e50240c15400f20220640130280740c4243c044240e2640004c00071500c3e400510300140c002c03912081030510b2034100c0c0007169000005803144180d44844081098135080440301140d88072f407201c0c0402014400c00d1420102810701c58091080d00030307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 858949199 1250 858947949 858947951
    0x31d10081005030f0a050d090b121b0f0903060106020c06090d0c050607081207020303010e0118111611150f0f160b0423030d1a03060f0618090a0303110d 67
    0x41c4c4101c0710b445e261703e0b04040c1034030341c1c1c41248440a0120711840207c0101c0306207682c102c7c00c059000d02c0403401e94002401c252010b00445080b2107410407410000d1441c00c2e100309901e030360b40140c54141030400e14141e0129007075401242aa10080e2201012100606422230ba5072501c0d820526001c0c000c00e4164004070380240740030070780078104104503000703000111248014075074903919904200e9491100740a68107020002c2c000402c001044400d002000c40c10121001c1218074000344c0c4801241c00405503c032894a1b110b030b10005000c042a205c101c801c1094462580440c0c00004a602038415074100c0e501003040014003980d0780800340c05440020625200311a17404d003050412420880042d01c0942d0040015000c9292826204410f0200007840c600950304000354001000300400c0c009808600307038086009100c0d41303560188151381c86488502c1c9414010f007008030a011602460b0701d140480c25010300140043c0380400208100119410301e03000c140b07840d9624606226006540e0303004d54031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 858950449 1250 858949199 858949213
    0x11040303030236120a0f1223042d0305060103060b030f07032d0828080a090602040b1303061116081e16031d1008100503 53
    0x940e040d0010301e1582c1c500b103c038080402d440410311282d003000c086003840c400e210341440a22400c018043e074008051181c190740c0a01c28580312040054030403d021541d1181c90040c42c90300c1a04080106100382c1c0d800d22403a00c00c8a44a1800c266204074040da010380b503a9900e00d440c485403e254000694049016020102c0703542e4a8625610744081c0000c0740d0315801c03c0d101e03020314103001030004940a55140140b8506140d1749400361540380741c4205031603a002521640f00381400303e545504c25640309035031840e5a03803400400001c400f4124400c0b500d0901411100e20041503001c00896000a9003140003c1c82e0b02c0145040c0000384615407001c81800c101040c1c014501051110600440313015040070b000b4440040c40100040c07044c4103c20848005034030417440401c80d900040c041810004141d00000303c0d0241d900903068104000203d21082c507107240101709a41705440c150030000100824803821460030004d0140060988140c00b0081c130040040c014240e42c0e0410001050003409840d0307a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 858951699 1250 858950449 858950453
    0x606230c12094b03010c1d0607020d1101020118060e1612060902180103050717060106050d020a0c0b0709050f090f04031103070c0e0a0f0606050409090501110403 71
    0x1c5500000c900c00d104085070350003618440001c8010741d40c5100304484450746460381c1c072004100303049901c0d04203494480d00c41600c49661424400e804072000d46403507010346001812184181d490b00c85180a01960b03040c030030301c001070b180c03044041c604e1503000d034030020600e0310840100d005200e048a8a804030030319804c4101405110b0f400329080720184000e0311680742c5101c0602e01d481aa6201d0250039111340e005500210f02c59070300507010948002d085445a1442101c0c55543c07500a80040c2c2e0705810020f000c01600000e0005080c0808072200a40715940c5015400b0b045070146100900d482a00050b07625a4030388a6420700c0c0348a6400f10002d080341c01c20800041002a60303003d0b01d80a956594103070151403400c002c0e070900c246090100903c4568543e6000c070342e5810b94040c001c000344400e0080c540003590056400c00545410f186001b440e19001e204031040c1d0f01e020340c42c000150300d060428083ca592040407241075a00740c01001c9003074110b614181d4018154503440e1191494003041c0031003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 858952949 1250 858951699 858951733
    0xc011103100e06100e0609030a020904050f2a010f05090301050106120f091226040807122d14030a09140708030d05040804050418020111010606230c 65
    0x205031481c2c0040c410a90b40d030b01003801030508811103284049034409940c4211850440020001103501034280c8010051642c0405d00c5c401060b20111403540000c1800c50302c2e032004014007000401076030650300d401030385000d240300f101030000c1d06039040128009082a4841c020005c403900d8090160003048190395488000b00a0341495003111140fa080c0351b1007885c0c2c0042c60082c180f940e5000080d550003885a00380c140c1c0c10b4040c6800400395191269103c28100c0082c03d0002e00c541d00940509503030342d6940c03805201e0810301d2019001072214201c0c0009400c04254469000321171441d20308940100e880600381c07084803d108142001006c0002000951840c50b049001298861a0543c031050704260701c041e19201b05018120060780240a4020340340b81d50b400880c0c115004040b103034500782d181d10103d0150f4004040000f001c03c50268042d045503030055226071001c206000030400d40e42050401403928055080208444094019090141c1d800c0400c5030001c18912040716200c44003408803117 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 858954199 1250 858952949 858952981
    0x61a130f061403030f0901020c03070602030d23070c060b1903050601080a08030c070303020706020703021e070819021206010e0106020d1e050d060e01140a090605090c0c011103 77
    0xc0c406081400014004081414811400c0d0000f0040c40c14101d401d016043c05030000948181144140b40b105200f80e01c0a001443c0500225070140d60348005e0603801c642680c0008070440800c025070807c2ca103240c8186041c4038ac01121318900821025060b041c5400034040141c0c0440d0b02200c80051400c1840407140180300b120700c91000d40d0b035140ea980c4111900c441d80e41a02900d8140c0400001d2155840c0c10300030f1800a100382030041c2000030540f103540403600310180c1140507a0084402c0e00032081d0b02c109456404480c3c3d0010810607007003085a50f100c40050280ca106c800031b150081085544014504940301c3c0300300c08491481d80d46804050150720301f0b10030310001d401402c0c507410039107220311201e0840400020708461300c1039403d4000c440561005100300841c603500c40300820074003130141042d0300074020851300101e440031500800c91039170544d0b481403d1451070450100090b8440c030440e81e5210340100f00d029142d0f00010300301e5025280c030030142802c00710000200b068012982d1603003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 858955449 1250 858954199 858954221
    0x9010f1e0f020702181009050408250201023c071802090a0311041410050103140105030c0f0a09050103230628020f0403050f12070b04061a13 62
    0x24071840701100110740c1280316912019410120302e5803901c03d00024445460342080039180d40e00b0240c0c3d52994000204c600c1590708444ea0380d40018400345000707601d0040d21b0651010002050031007c0342d40082d646000c086042c0d40c10036140a2244a055000d8420844c040d1200f5000001422808039680c0c0303d0070385026010402110a06000510100d44207071026184040c01701450181035813900704844184a040355803264503a24000781510102c1c114074002e61015021030202402e0500140c19201c07241e11a4107918240d1004104507580002c5017540e41e002a030b50103980d00c02c0b0074003240d90848150841c400d41420301000004200244400c45c8050080448003161801650110742d1a043e080e03401c4038550b8014284c50b82038055000a00b80703c103080081c01403520100007161a0715401c203500a581680103440d984803c40e005100004c0d040d0313580001c8500d8a242c0355038a4080940140c4007401259482c21520421044284490214a4000d041c20000d082c04040800504050542 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 858956699 1250 858955449 858955451
    0xa1106131401110f0a08070c0b0609060d0501021908090a03080a02160209150f060f0901120b030d0909050f01150516020d0f05072c04020a0506030108030403050c0f150309010f1e 78
    0xf08440d01c03405511203c10f89c4a9408001703030b262201045000e510103440654003001c401001400035400f44001c08250109907030303c40c810804000c019100700c40c000c0c8170030580d404c002c4065000aa01000c2554400d601c0c0c8001604d07808080e04518402d00c0802d00290450325900c1400340c8264586261185d0405c1150701190b0042000280540c500a0903c0305403092401d10416000d5800741c4c401100500580800040501c040300010b4500410504c0c0940421002c0c8000e0003008980d005040d403003040c1c2d480218580d45072213540c0f01a140328a0034070003009000314081b101c0704048038201c1034a5030001c1000c010035119081906101104104c212407502c18003800280c5107544c00310700740183e00b4504d80039014150445ca09602d5610040c4103c1e4051546c40340030440740d40e0003020314082c092060085866900350318103640b6040d5445070441c840d5005003884e640136508c8100e0f412514006454147d1070741c60f0f000031140074050304802d95240074100706c0c494960074405c0a04031040418000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 858957949 1250 858956699 858956701
    0x409052508090106140109120213020d1a090709050907110318011106010e1b070512092706040f02090a0306241404020715110a1106131401110f0a08 65
    0x1101780107504821201038082101c0d40020404411921210303403d503800a04103c0308400342910105c200d0f407000c18241036269079009200e505960040c4a51221002615180221f00b01700c000a010009144952441100e0650000306660301c40d1105c0564000325108803500d0784947d24080300086424100302d400600805200c0700050f000240d030a0407105040e00c00c1141d0b845500ca41001a0b46520000050200400c0300c01d00040080104a4070b180b070046026032a01040002c00580d0002c1c14414902c0d02c80ba0f09490820180100050750041011500050034412891101d00030740504150968400f1b001e000000620800d6040080203000d603028030781c11f0f0a507202d24a44c0c8180fa5014003d03040195140c0c040650905500501e2030f030740136004c03810241d4020070303d0005540525442c3ca905400210303400c050310350060645c0d080040000090f01462800102c600d40e02140100081e005498198514002c00c07401e6014a51038802c165449550720400c031041c070340c6503201e01000000104180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 858959199 1250 858957949 858957959
    0x130f0b070e06070c0b0c0f0a11010e1509011b0f0f03141216031b120b010804110904021f170a0504020a060c08091c031d03030409052508090106 63
    0x4401c0741e1106910040b00003080341031484c41e441e0354000d81601015880368404541e02d40301f04110200c09507100301c456503a807096140004049840103801103015100b00e0003803110408126055072810b0600b0328058100c1c0519144940c0c581101e000c1c042d010340c44d8046c2d00c00500c00d480d41c070b0001003030080d101e072004068100c1e1001c045101d00290700020518082c0401c90380030102500d08440c450619021925018a001442480704110464030126482289046a154071801800340307680b02404c2c200308600d043d480d41419100710083c211711880c0064005011942c410720003101c005511201000b2103150b0285c0505180d0002041d0703450020fa0300001038101c01036000c0c0a21030f95000d014601001c0ca4090255070500720000100c811920074000b404850310303180014400108119214032107a1071034200500302440280131650928010b00c0c0030034082d1800000c0b2811204264800107141e41c1f45000405001000c0c08009107010444e6400f00501d41e1101609018012187c000c220360b039525 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 858960449 1250 858959199 858959209
    0x102030a02190606030b090a03090506180f03010e070914240114190306090f0c050318010e030f0912030309070b18030f061b130905130f0b070e 63
    0x3000c106001a4414090900302c001c0d0524050881803142c031001c40d0742c41c0c599517080740107001190807041d5548000d5103041815030201c205001420142c0d020b9240504103210b00d440c8500700c0c45520b0080c1240b81440d100c0e501c5c2540450708403081102500c6c080c80e100d540120240c00842c81c0c82c40c1014061001c603000600200c1190b042c0320030403814040030a804401942c480e250701c050300031040d02c1032150604154400800c82400110347d039000901504050703100d011902000100c104286c07800d1407000d481c41c0c0010482e504001d01d01c807042481c107540070344503014100c518680c502d1030101285104c1d005150343c0c058103800c403089403182c482640840400b5a0703400102d0300d00c0f016501420b030401c180c51501c0010900282d003c81c41c00030260f88000400e15000c404a00600d09074401001c00030104240389071104107c0c4140c090303500d0300d010400161442300c500e0044102503541c4030f0200b46100f403815001d40c0a60760001980c0c0301d20740e8506042c181e0610488038a004140300d5001c4e92510716003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 858961699 1250 858960449 858960457
    0x30d050a090b030c3405060a0f050601020a110a050604120506090d12091415070905010f140a02010b09040f051c0c061e02040902090a120503042d0b0a030506010203 72
    0x8600c06a50a101e42190020168000c800070300054801107002103416219040d0303155070483c0606c0051000c0c3c203041c0000811151052400101c8074a08000c1c4505680d02180c0382d4600c43d0040c0b04800e0b503c0c44400015650000ca9120030380c0071000160004080c044075044d008114042c0301500d0b91603940450440e02c81d089045030900040048100006a962950154036590f004100d081c0130181545106841c0c20213440341805000c1c0d501c020050665440900640500000c0c0b900b6251455182e030083c20154450450640b00000800d6004c0454400d51007503001c110028108a20b50401d4100401e01101640040c0c0705401003107488008500c0102018050305201d03a180b506560040c3c44170001803454402480c0c4440e1898400c00440c6c81c00d001400140c64100d40050707a9482d40300401c061500c2d1a4407140101a05200100c04103901105940c00c032a250421070328131454040800801894001800100b208100070201d419148103020f02024411920204111740f140001aa83c0e409 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 858962949 1250 858961699 858961711
    0x5030c1306082b02340515090a09150b1b0d12050603070e132f011b0c03080a0210020f030a0c2c1c030f0206010e040c060c03020c030d050a090b03 64
    0x3440c0729441c111107095400d00f440c0701c40d0603980302d00203030f22000028010407c002c041d526861001ca11890b0600e41012040b008020103202000f01c081340d0314804c40c206500e44600910414080b504040b015002c00100010a20000c2903c1c41c54803018400303011602c0710300400390503a02c3c01e40014014100042e1030400e032100441040c1c0d15540e51213051100b00000075040714014040b000d0004405064450a107a4180404240d081946801d000400c100b002d11980d0349081c440c01d803484049201200718000340e9410400380d903030341d5841c01d40507850441401658081d0390b01c0043c88c11120251403001d5400364014400a01c4940c0003404101c1d003840c00100b4a185071100320940180c881003454400c5280d40010b0031000c80d440c08010990294003800e1401c0d070125070fa180021944545c14048203000d0044095144050700b03054a4418001c0b0803070183c901070118014842d0305160080059500030308004040b102c880c002410003c0060300041001d2010410078500401c04c80c91110580e407040c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 858964199 1250 858962949 858962983
    0x1226010b030103110d050106060e2e0503090a120201021b0d140c070909080316020f03042120030c0f0303030a0f060302060301062705030c1306082b02 66
    0x83d08548610480f80c824080965000100350b00c00d0001034000c0c000d6000416440e12800c101000e0f1405202c0415107104844400145411301103d81550f40c4070f0510380c262061811a07203d40c1c600c04982c0c0703011046500030784a414092261800301d0350540041022412450001450498602d8039541d20032200d080a00482d9808a0b050b82c6916800081e01400084c0c500f1241f08c07e41e501d06030401c466041c4000c3d2518800002040094640e0300d1007100e420741d041c0b00a108003410001c0d032036241e010342e00403080b0103440005103041c1540c0d241030380d80c0c0040d0400e44021001e801c0c80700403030958580c900c5550180c00346101200403031400c49501c001004003d809140785030b591000c80001050900000c0f03180a640c0d4102201580751800514003030002500c0710410600500740340c11002201520910102c0031212050001e070718082800295142c0640e500005803205840d0903000e000b00b9003005402c2d02ca100c80c210484000400b01000b20810040c1d0448240d0444808a131100341e0070301e0b621190 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 858965449 1250 858964199 858964201
    0x1273c061a031f0f090602070b15090c0702041b031508060601230412030f12110417101a0108061905100c0b0c12151014071226010b03 59
    0xa04082d81030411040c02c26000080c20340c18130440001210444902510442e90100301c0d40104807507000083e8022102c04154003001c10700d040090406803004100b04109000461840110348a031b40000c1d9509071170320100b00b4ac00f17480b0b48000340100580050481c2101130114001011040070864500842043c0c0d26803d101040342d4207050380c01d82c85809502054020000024850031140603580f4561080d52101d00650420302c1c01040c03005101040007450f441e001649a04104072011201200d0312010980c00114001c030041d402d290084d00d0102016041c10101d00003600c0401103944000c2c0300b6200c1c610151907110034019146c2890300c0300ca6440d00100e000340024901041c00d00ac101d502858610b607812140e40d10404500300503622001c0060000c9490001040c4100010f94000101c80300d03501c5a060703000c0056140c106a02902080c805111701c0950a000004100c4080907081b50341803000807946440105088035070048022a090301e0b0f200c42461200034603001d81200d1940b4442825 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 858966699 1250 858965449 858965473
    0x60e0120160f08190206070206070c060b012001050702010e0c1c0f06090b0105040e30040b03010e0402180103171b010507090801273c061a03 62
    0xa2801c184410b81c0c41214902e49000014040002800da041420048502035100c00e0b030041c4c9000030113000c400070340d0001b80c2088281a400107000c03122542142000c90f02890010041c1e5205401c141888200c1c6002092000f212605401950181c2c03103aa00030442d0003c4100c3c042e407109420704201d680200322220700001541c101c4540d5048600900160105c6140c0d55601d804594588000300c8e41c20b22200010403a41c42e203031250070681010800501828441c00f40c003960032800c2c011003005200c100c180c0382030346006050161809080303461959981e03541c65030600501002c04940880c1300d6082c0d40d039054450019440041d040b0384c2d0102110404864a541072150381e017001d1040100302030200d44003c00c040f400d00440b80900c40903240c0e0300f1403508098020342503511174201c2e24050b012440d45602c0402e4181d07200440d140c3c2154070210703581204205034903040740c00c2104220488440d0308662000e0079010443ca0641d109000130880d03c1ea075031803901c1140c100c4260959041d0407480c02101c1e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 858967949 1250 858966699 858966727
    0x20a020a150c121e08040309050603040305070b0c0c1902042d0e010f0f0b030c01050408030406030b0a0b0c06100e0c070807050a0506101e050603130302010b030604060e0120 76
    0x40006400e090019852600d460b04180c0818132840c1800015150014001031581125490700504802d541087c514509610090124492220010481c0c0154000281c19015082c1a070700300104007011741d81c3d00080100c540b0707402060054164451881c1540c0c0c02141150301e1403044907103000300d19000f01c00801038603040041a20810b01e00c0c95548074000c2c034284100c14825002050180c1e580080c04820f03203411b140c030f0710004d600d2150602c40704000600c044140001564104d4503e4500412043c1246000ca03032180d40650000b906007402254001c0b00c001d0115000744964520b0f20110040740ea502c025445c000002e8940d94400b0804000b4200402c02400051030182d00510440d14442c5c100d03512075260440031160310310782403100401404030101c5c8114907001e2609030410100354500f8400000c3c25444080c0c0407031005001c1500080416000307401441d10b2600003001d4500e2403900d410410081e121340f0003548003d51805843d5280003040c80394003e09092440c1c5402d00340b11640c11815 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 858969199 1250 858967949 858967973
    0x3110109050715170a0905010b01032f040b0c25060807050d02070c090606140315120a05010c0504050418030c080c070503101a0306010305120a050c030a020a020a150c 73
    0x108002500300840204e0b000e0000d403d00071078200d400060b02d00b5090428608545002c45898100340c1040c1808104103c00c5000c0c0c191080c0640104004d0421206095075511880d407119580d000c001c580f60090940104a406e03c403542109292542101c071049000c4241890158a01144100011801d0b642c42407001c4c0840210200c0010300d059003d0702e030110780700d010fa0b10060560b916008240030b1240d02910762000c0c204c903200c43e1400c50501010a100c041f20340c8400314002c1c0500c226085c007401c401c0210300e80c27154001008100c48420381030020310aa000d405590300035410b05411403415102b107510b014502c1d0f010360394017821004556410700154410b00700019148a6448081100e0b60103018944041d00c01803800100d888540c5804125003a400665138880d8100302d0040011810100d111448002450107003581d602000380141c54034040e402c03501c03106110124041204d01d4000130782c260003500882d80303001060340c1c40913611a0760b28001c030401d001402050100300026200c140321 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 858970449 1250 858969199 858969239
    0x4031406010302040b0a290c1c14040317161e03090f1d0601050405060c16050603010302060d020703090f031b17190c0803070c1818030e03150c07031101090507 70
    0x500e08e46a641c8a41c2c0e4a0900b10203000004440386003628041150408800301c042305a20a41504007403850f2604c2d03104800d001400c0009280000b01a0401c600b1440308600480e880307000300d4111107000050410080304031200301c0105078150000704440e004290088100e40e80c2982c221905120b0b491520540745000c1e100c54180141448040f035103030307950005800540c0590000b0b103c0c80c000f460142d07468000980c440c82c001c1ca410801800940c076500704545803400900e0b030144c1c0d218030134a4112100b03015640070074034402100307102200300450b00000c0c1141304016100c0168158954a0800005400813401c80440c0c4c400d110203074001701d1400140203054003079a40b0030f480c90340c0d1340a4542136500c0090100ca12000000e020320251880340101e50500807142010010761811801030503c448070440041c040c81360441e007204290ba810006132507009030143d08000e060800c2550b4175072540020004902003840241e40700440401440b400c154940c00400603c503075458550740d409407903d200f90b1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 858971699 1250 858970449 858970529
    0x10b1e0d02011806120501050604060c0803150a0f09050a0e190503120106110f03071101080606270103060911070308071b1a0105040c0e06090604031406010302040b0a 73
    0x50a41d803001038400f0314004103203640b140149a5134103083d0100302d81e0160000d42c400c4d44140800e06c025903101c0d4044c040300d94000e4515a0300c0d16055070801c9150b20050780e01f40e00c40c10b5248089501c00d0305c45151001c5940c40310b018400c588820044a09958100b2008041c030b60007810b05400300f02400b040083d100e800381050360f103810b061280050703003808240c110780c020034005109040320300710400002e42c40d040500b001d10f0520109588410b8802c180180d56410408040003040b265030300e00b0708a802801e5900004804003003441d8507411044402030400f4082171030b11800095000050003441d00348e1606803c09032915940d42e50680f034a14020b8400000c100a080726482e03c0101e40f90b62101180c05020080003038140f01c0c0c003150480c201604190b018030700b01400300400507045030034440d4040f805c0701c9050301e403800b882c00301e20140030310f90010340130a011840b00391030b414000c203105041c0da000b60f03001d224a42c40d550620070700b01c03090711072200d051300c5400760f001e5135003e0052016561101001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 858972949 1250 858971699 858971717
    0x10050d0e030c010c09120c1a1b0106051e03100c0c0b070203090406060906020a150b060d0b03011d0d1815051c0506130b03010f02130602010b1e0d0201 66
    0x40d041e280da000090b4000c081e0f95161203240d501c81d080040c4500800c0510480b0014074101d9441c820300086901c200407481503007480380c484032460f610a03502c840c450800800600100b242925011302102d20a15016210010402c3c14009074903880c4529030401500524007101c071b030b2954034001c1986440c0340703041104030078007840010f44050040b40904203075070041d0b8903200048100400c881955115000f80b101c018410000baa4020540c01e208541203054118010030b032488890103040030703100d107030f902c060000b900c14082d640550180035404400d5000b085a03d040c1b031200010b403000c4802240040e8040b03441c143c8060320441042d40f16041d105028800d840c1d4a5020507650a004440c2d1000b00d0408250f04071010180c0452107114500b1050a011a05000f008500d800d03600001c8040100d458410fa988143c40c25007202154019103502156654407245620404c000745000340d2005508084e01003035949031809400b03080c0c40254401d240c060030410308000d8a00e4a000089060102ca14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 858974199 1250 858972949 858972971
    0x1b25120b0402060f07150f02030403090605030421030c031b090302060c0f0307060203071b02011407030e280905060901092712020f031215060706090f030311030610050d 74
    0x1001d41381462040415218130440140d46e101511008010b01c200548103200300404030b5440304910b070441c0d00740d0500960382d4855040c40c010340e0b8510b05500308500a401d040d10b148a174154000080702000755000c03c600d0581c04c103220030070b242801da00e40006e044c1401c14000340c9446070060440540301d030211507181103440d40c1e50341140c00090003569040e0340401040401c507040502c2c44004d200f01031040d180d140d4540d0002e80402000032040e0110040403401d0001c2501840d0300510601005020354519209034400000151051403d8000001d20f1030001a040c100c5005590050130300401018043c0e0030001004000c10050059103501400f800d0920f080c4161690020200d6006d038001d01400c1d5000400a454213480d0420311300325500c04c10200c1000340d5608900c68001400745115140745401e00c0008186008c2c0d5407020340b403a440d01e83c41108000601c41c03040d100d1842a02c05114a08000d02c2c485c2d000d00080b204641c10001d034011a02c41c80e031103600100038012001100040d214250 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 858975449 1250 858974199 858974227
    0x405250905090c0a0906080601260106020106081603020d0201030603150603060b010203180d0c150512060103020a120e011d06091209030307060b061b25120b040206 72
    0x200200404240308460902290601c0c10300240e21407220a041032601c4040030005201504034400c90b010024003c01045881c0c1c45001060342c5007280030021240e1081e0a192842da16034288505005503103801000184d007880031450806120f1603002030f032400d510355020720000c100d20300c1040b8105541c030b50012002543c0d43c006c030900001510310006290f4158070f400400ca801c80481c0505551080c41148018501020846400030707083c1ea03c64109038162410350900ca070990465001000702d1103043d50140c1d4007001070880c4d10030000c0d113006681c03a184019070480c031038810f0681c00900c0b41d154a1010048030742001f80340c5031395000002003c11a203035030201e481c910181d078103605400006c1030200c441020070500190508a556032403518050400080e660301c10490010100b60711882004001e0307503041c00391a544c03d12507100c03151003d040c202203516079100082414180072250f07200000c0c5000035032108207513000020794951158158840c041080d1004108a80c42075042100308004000303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 858976699 1250 858975449 858975511
    0x3010609110901120e0304060c05010b09070c1a04080d09111201092009190b13090b090d0f0e0a0b0a09180203041a0a14041b0e0c04050405 61
    0x50000041c2d112800c1d0303000141301c02c00103081341c8003240c02c010562804801c044102d034200c62a41c1492030171980d1034504035001d4040b141140703a1164141040080498000344d100706994454401010b0b881040c0e080c2e808042003da40192840a0038482c40c1c1c4c03092443d602c403c0c0102d00038600d01c2d01d89101c00c03000079142085209a80300c40c0e511b50b07607103c0411a0410b2514281c010f00c401400d01403585001041c1075420040c240004c441070b2105241c00c0f02130b50b600c85003400b0800340c4961003801c101d240d074134003034075041c44111000501b100010340c1c46403012074840c200780c046030344420382c02008000c00c40303401d9585400c256008020000000348202801c2c000d1800f01e5450725469036662420000f086600100d440181681f0300400c2001b00140d0100b03e807a1f0700d20459130400101c0c2d118194400010311000001e000d00d05c8010b0203000c18000e00044620003e481c00c03000e8100d00e0340364407403408030714029140039851620a101c01d108900d8075401144d4400c0d0002000140c1c401e191643d110321100b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 858977949 1250 858976699 858976721
    0x303030e0f120406021b030a17040f0b070b0c0702031f1509051b0f0f13030b090f0c150415050705061f0f061707140a0206091501031e0203010609 64
    0x42d0000d001c102d42501400800f00c50300d02110091105400d0101094480c84c0c035100082484122060310f00c0c425a0349016127002d0803d800407520301d5610741062411a5100780416a00b0042c4c0d540058182d01c01d413411110b103240d0140c09003407520f00301a203000c05614a03580840e0707543d4032002004610121040c03070034020300101340041a5400c0c203400c01c5102410044982140800803c48004024186000c03201441c48502103075584a407210410207400c10310b600000c00314010311050140492000400348800600141600c84070000c000c100324981d511100c0e5644051400d120402c1010741c00d822200c0d2081e010300708035140ca1215070f81c860400c00202c84021080f07061000d4010200800040c40340a08550403041806504141c40606081ca1562030300f0007070030420700000e41c0144900d07030480241c0310101c1c510303444220814000c3e445410441e80403102d44210381d004605001d01d00c1742e00c0e04880c0c10203040401d00084071085001410010310507a01992070b001c001807001c50764442d95041e08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 858979199 1250 858977949 858977983
    0x31d01110d0608060621030906040902070204060501020610030206090d120807020c0604030c0315090606081b15030f04050c2d121f0908040e0403110d05040303030e0f 73
    0x160384200540708540032030b0001502c65102c20100400c544459160304000701400a204039088060f100c920701e903226030308000707400c05804540002e00100e981c000d0000544200c40c03c4c8007250b101c3c4012030361380c00212950701031090150001c0015003070400040160032070140c94061000e03019103070703022004508240400080c0d00f031010007003510741c14891100c4c2284212115481c240c99900d800d031b00044a400301504000e42002443c40040d4294070603181030f90302c080c00340038a55898581070b80700e40c00b01410024082c1c896910040354545210081215a0409111800c42d1a200e01203020b6500042c8200c072a031040c0c8401101d25552100706425034180c020101540004800f030f1500901c00840846001d0002d8041d05460700d600814402844ca00c105040d4080612840058014200040300038100800000c2c0c00700d02c4082c0300034080d11a500a45401c0510540c11000f039540713017158005000011414001400000d01c00e070490703190410101d080711040382d80064050b00b1314864181042c071507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 858980449 1250 858979199 858979207
    0x5010f0509010b0901080610020115080718090510021303080d09151b030e0a061a010305011d060d2a0504050603070609140a08060108010501052e031d0111 68
    0x3032038804140c6000d002e40716400d6044c640ca40e40040d1080101800c42481089118003460580e80b007503006a24641110300c00024442e601d100440e26200180520350b40080c4024020341380103a14007540403515400030040c0320703480c5800e80030701c0250800d015560b81c032802d02500101080700700c17020b02188004000c0004903c01a440c202650501c000002c1c5c8d280c60070308880e80384400c168130020b0070340c02c01424081030080d01d14120a00b00741051800810381c5140520703041d84040c1c021840345c079a01007a01c0400040c0d8840b007160840140c2550380c1c20340300040d030001400d1420222109503450f44141800721800c0c001040307c4074041c0d292217501280b541d6180c000c20441c80d041c058590800c0c000d42c0600001400c00703100800340b031080d000e94107105008a481040350344a8500c804001c00186080d91001d5840d460050302034503081c4511485003c440302c8100e01c044a003446201d4103269051400c0d02c1c2e05212000350007402228801181028460440160fa150280a20000a24100e031010360b2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 858981699 1250 858980449 858980459
    0x302010204080c040c0e0906120a03030e1b0604090209040b0d0b06040507090f0b03041a040302240f15040b04060b0909011202010512151f030e012d0e0105010f 70
    0x984082030f201c0c680305a0415036185a45a080803440801e1170b01a607006002c0d82d607120104003000c400041c204081c3c410300b000b40040c9903065102401034002c4d070301961800c108400003034000107800009580c0c01001007008011949080d4000c0140103c06400441e0290340a400100180181c8000740e8007840c1e404200405840d041c4a07540e0700c001903040005800741000c24215126185004400340000c00101040502001004089207003e007030720507002520705850020748a0340f0301c907140040350300c00b21a48140700c45a0b061303203803240401042502d0396980348449184e5003049a04a10f130400d03030712240c40c000ba0304c0e1805490050084808d28a80d10641c2000307011500105a2025196212036054000180c0e0310034103ca0304076480340c04800701500c800c03406103299451270b0324090b0710003001c00181d00c0c4034205819400365000151800c01c06c240110341090f0903074909490b1220038181004008030808146148203c0c2004070340b00000b43c2c81043c41c1e43e142140d000782c0000d5240f00303c1c0001000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 858982949 1250 858981699 858981703
    0x3080706050a4d0d0c020d05160b041412040602070605070c092c0105070806030c090c032d04050d0f050307032d0b03060a06050901181503030201020408 67
    0x70000380e0000d500c010002c00001a0507424040785030408039140f02c450b484070580100d848030710b441c0f119001120703568030307591604100410850f4807190241c000e41c1440010507002e0025034580c80c00441440f200048582d940d07001c40074004100300c600040d00d2041400c1400f0400440c0d000c030b00180c000650340ea081c83e40c080e00c0d14460f60b000300100704081160000144003203030041c044034070564000c511010781d140e022440c107501b441d42e42e04060b03540319040c0120005401660086242c0d072241e030100c0e181c0b5803e058460040c0c0c0015600254110003141140006200965004031785103032203900325184074a078407014290401da08490320101810703c003d205082c0700000c1c01e0f440a050500c0c252146800103801c0340001480e160a0550301c01c0811054000c1102900009003c0e5030702780e0f4142911203012008141c07400d0000c3c086e205890004200d50070f07a201e0402903c1c0000c014000d903070300e0140c0f141d00400040a032895510b48a040046907920b20520300005107100313800242c0c959082c001824 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 858984199 1250 858982949 858982961
    0xf010903031d100c020f0d12051021050c040e01050412030606090b1c0e060411030c03070905060f041416080c030601030b040b060a050d0b0306011d0a0603080706050a 73
    0x1125101c200303a224124154001040801c02c51140008180c0d0100c0c103c044c0d041c61146d125948260080300f902440050b840704608000540801003040152990410008009e0f9103004040031004004985c40039514180c02d440004c0d40705404036552600c04c8408075007505e844001000c541d82d103c9003880f00304052a107010000380c09519042018524150004119030990702c52240c07520300000fa90784c1e4071169072072407503403400c201c240c24000c84c4100c0e521030f45d41e08002c8900b500c8081e2100c0026901c2e10303000c90107500420005001303110b41420304203094000d200180800d40d001115030f82c8980785444d54018200a802c0d440424900d0340f800961f014000304051320b14104120108041002c144009802e80b60024030030301c0c0000e03121410340081030051186070001070f403102020030186005680324000b455180d508420504c0030840701020f1560300c61080c040c02050311070300c0c581540031010740e045072980856040b1000c01d000d80e4030740341c40e54180e2040d0f5041e40e0b865100d00030009143c0460041c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 858985449 1250 858984199 858984221
    0x3150f0a030c080d1706180c040504050103240c0f140d061401021014070e030a140601080d0503040503090906031221090a050c331e0a1710080f01090303 67
    0x4900c64070b4644009002074000031b04240e4040c7d040b60105072801285006e03a0f0103848050320420195840381800781c4d645104848414480278900810481719501c0d0084404102c00764540c2641200000015140d040302d100b0000251142400700c0074030031946020b4400100b9070458000381c2601e41c080021304140c43c050300c02440b43d08112035100a1f80001c60346c503a00904900d03100c1309000c0d00c01d00007802c0c4035403444040c102c003004c010560038280c0302040241c12200010700b01c54489c0f141c04000c0d941808101d41c090090b40062000c540c107400c01500003940454002c05580d458001c0340f08040580d042043c5150702f03061a0000708016262032801250000040e00c000d040310100c41c3d80381a6202c2074109818051200c1024100d111400c0d80140d00c4a244001075001c0c00100842240361030b904040200b040350202d0401c1c124140d2042c00031100d8950700303a96942402a440c40708a9030303001c0040c040c4200134056074000200c0c1318042c8450240108160008a0006d40c0b07070400809903405400c039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 858986699 1250 858985449 858985487
    0x10f050c070b0703110615010806030a0b01090c0c0f1203050109050402130b01181d22120c0b010b03060415052101150b1b0303150f0a030c080d 63
    0x2100d04040001032440c0c110b0318030030400e603a107400b946000c40c0c40e5455201d809000344182c0c07040c0a5040c05040007910010400c0c1c0c0c501c200f6644a5040652b2140f003800f025240310035250042c09001c00076002000c4010041c10326401d82c0820f075550205612a50700291042c0d00c134054030b40290380c0e25005050043c54020402d0005003801c0c0c0008002c101c0701000608020794070000000350364000c0100f441e03040c450800703240b4050340e2401c50f003400b241d003804118881003610000480301108001c0700c0300124040c03215013504c621550368054103800311105e44400e03c010800d9400000d031414200350f0290042100d0030307880e824448240025554090003072007036440c043d46c0c144203d480d00044010940c0384030000103603c0c201749034a10b0040500c554118030062580b000842d8a05c0c03118010000c1e1340074014100b43c0b440f402e209030f64407800705907a03803134403c400c043d5880c1251030905240076059500500440c0e2403a500c0d40c6416a400c0d255100400d640c214042d070b000301c0303508213140f01900d0b04203000f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 858987949 1250 858986699 858986707
    0x17010501052d0d0b0a020a020f0303090d08090f0106060903060b03010b061806070c0e19050105011e030222061103211902030a02040f0b0c06190b040f060302010f05 72
    0x41c2c0c0038001125440c4075142c0036803030050845590f0360718803041102904007010849500b00018010069444001c2050140c07044410601c1020b20010840e03201d408140060a124015020b040b10f0380900500310080754450044960308a80b000c1c86034400034003203929458080b501c2e40c42c004050312105001103109074940345d001220740d11010100ca09124801500400c0d0483c014000344490240342005411210f41c4900445c1450f40c0c2c0e980300740219900c00c9603010304d00b82111614280c65090240900065107030301d00680465541c0071780c1003034403001d09015040c4030580b01421180002d8200c0f4051442c41c4200400130550480c0c90301000e0103201d0090f61824907440c001c24040b100c02c039000100d42007e0000521101c00b405610840100807442c00d5580e03091084224001c0d42250040c07540301da002650000b9030b03811030700469030b0407006071016100360365841103600e00140c003000200080d107803030340300c448455900c9120300b001035001000005030140c250b0000500c48441c092080050080c204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 858989199 1250 858987949 858987979
    0x1140a080703180b010306091b140f060d0510030210021209060c01110301060e0f0109140409050c100c060f02090109120c03020a0b1b01020f0a0e0d05071701050105 72
    0x290303a0300040e142000308208460000d032584038403010740b000d040115480008001c002c07854206a03101809542c14201200741102500c001070a00d1103204101c048040078249241024212040b90b00801403603a420620204920000e0352421141003250f07000e8228144118601004444284c00661008015003940c54949903910310030510194403510021503841008e0000b5048000c2001c40c514180d512940e4400380a0500d0601d00032451003096803c008074a00d502c64038003c4101e8503110950440c05121030180402040502401d8840340100020b01100f80c43e94441c0450b5403600360303501c243e01c007107a060410445804003105960b480c0104800443c40c0c0c0e0140000d010384401d0300103843e250100385040b5409900683c4025080b007a0054002004d81800c00a0070388045001d00f554036140460110900300d00c2484000c40141500b4003030005100c0c1305041c0c02c52015170241c0400280f5482d40c44552801000d541301c0e40c00d499482507001c503016004e0041600409041e140407810324208 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 858990449 1250 858989199 858989207
    0x7020105130f0f06060b1305090601080c090d02221404050a03050a0e0a121a0103081602040f05040807021f090b0307031b081f03020a030201030b031f0b01140a 70
    0x40c0107007010002c5900d58080c4030801e0408400294030010030852103590701c2c12803505400c02c91003140c0038043c090300000d05040c0fa5101600c20f51050356107942980e030710402030241d900300c0d421294020320315074480c2c001a00c0d2030b116101c1c0f0407450b03080905020140e1001c08191130809107a90b80b1804c0380e0302484000743d00080c4110a003036150910302d072200304601c0308407150461224065031140396a0720014204820a0380741c50440d00484003c0580340b40f2100007266454288402846c50314200046840f500751801d20350b02551009101140d0410080d07820800e5680030743c0e0540324014001828070843c1352400810502681e0040c1c0e0b030002c54080f42c001381150701d40c1d07c903801400500000240b69648294030507211503c003204803090b81c248803840200518011221640500c41000c40903075982818400302040300c0e8010300841c005400d42e401140076290200c6031640511501140a5110407500740307421007425080c02c00601069800c0005241caa0b24078041407c4440c01c21050021340c1d80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 858991699 1250 858990449 858990481
    0xc061a121b0f1201050f100e1b1605030d1b020f060601030c260a0515030c0f030a0f121403090c100e03010c02060f07090602030d0908041a030f07020105 67
    0x200700c401c0381c041c0b0a1000400d40983c0c0141c2074008a501e00401c010001d40324002d01400b9003000c08503160718980f40d95800006030025154501005d005d10380740e00c00c484001000b04070710b154204c40d114400017240d40e503030301d075410492820754159100c0d914a042540d8440403140c403001640300502d41a8a1030040d241c5070000030b400d890400d900d40c64403100081c0210101c12006603801c2209001e0304501007021340052054038512056801c1802142d10640e0010204500090040150403089200800c1104203c500c0084030b800d4000c401c2c3d000c01166203d5081c04503c0d018284184440c403001d04018010b402e005440c0c010214140f042c4070041d200080e12140580c001d4a0b900e00d00d042c05042038a48503205035000d5415828003003850030fa107502186150040a403014400c0064507004025200c2c4022801020010f038800c0c4880300c0250540d410000c0c0a41c00f03040100d10342603c0741c6101d9111198603130700903544500001885410401a414a6481021440200005e04103208012b01c8800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 858992805 1106 858991699 858991753
    0x70c03030e0a081c05180a0303120e0102031314010f11040501080c040303140a0302041d07080f010f05010e060f0a0206061f120203070c061a12 63
    0x300000d052140c003800c0e002c444c8071000001d10102c07801d80005a546000c2c86d00882d0b0864507444a00c2c140000e1402030b902c0120640000c661042038a64552070900345d0380c070410030030201e900181c41c0c0078465907100b520546000420017615015202c417140311001d00f8134008065103a10304900041049810a0700c8000701c950f610403441d8400c0c0030f281b001030b005c200030308446015100504000e0482c0115810018103154890088601e00700008d04a41c041403406001e1005c0250070521955020701d16460020341903042180d600300400c03491180e2414800302041c1094940d403004162000c581300c481d0344d03a8980080f600025580d903c00d8a03454054080007411041d010001c009200d0000c50544510407440316088014001f98401041c0304100117203191000c00140050180148440c941840090000b031080e0410500f4180342003002c805900206600e601c08100c04c8921400c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 858812949 858992805 := by
  have h0 := BRFrame.cov_init 858812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 858812949 ≤ n) (h2 : n < 858992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
