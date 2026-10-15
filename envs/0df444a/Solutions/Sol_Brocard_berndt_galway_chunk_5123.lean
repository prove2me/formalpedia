-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:49:21.9171+00:00
-- url     : https://prove2.me/submissions/fea97169-e2b7-4b6a-91df-f625b883e7f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 921223021 ≤ n < 921402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 921224271 1250 921223021 921223031
    0x901111f051503060c3112060b09010b180a03021807090e040f1101020c0402030106170c0c0705060714100603061404050c15040e0907051e03030a0804050a05060c0d06080c0913031101 80
    0x150181070104549001108e1042c5000d010300d44908000113058101d61081c2007050074104000f0020303818040c2c507041241c1c0051005004801680c6030900034640c440090005440d92403c0e400c064030840c041d4100044d4100c034038080000103000343e0040004580d205040c601e01c0054200180e2a02c0c04815181d90300500200c008986180c2c4941404400c1c07000c840c80001b80d4988403000c1c00640315803242c01526410001040c020382c1040740007000407904c00c814440440700b008048504100c118074038405041d840344010010b01801d802200300e040c05510b95485207003095515669100c4a1307480c0c641c000e00f90040310020b452014001c0c0c8000b40340d10f038040d06942c6810392101d03488114500442d445103180100032134140340c5410403d2080400075000f503142c60024403003035551980c000c00440305803040445810005805000083c0244c10300c80019446000007526941035803081d81003a000380e44104c2e44030069503500210541c200c2c00c0c1d0b0245002c4620303942000c640c16528502047c404d50b00300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 921225521 1250 921224271 921224279
    0xc0a03020319080112030807020a0807050105070e041e0506040b030a14120a05040605030408160f110f0603150a030c03080a02010615050901111f051503060c31 70
    0x4402000101c01070409480c12180c1e142c815102480e00780201e680810300706820200090142030340d00d800c00f101e40116a00200d0550f9409103640c0a032400311010394440c0c051252068012089800b008412a03060003070810480e0001400350544032450300303094903000812226101c1d607000c241d8001000e025249601414140195030b24400b580c081414859510100d503001c440000ba140b0a06e8665101c900d0649841e2084075503030405401650011002c0191810001016548408482c450030042800101909002c07035100311610050f400352404080c1c00c406903031940122940141d200396891541244000070541500160300700410151511001106022041c80134144403102e80d4000d001c3d00c0d4480c0203100040050340d00b40004030344203015008140d070180c607490440300b1040e01110048050b000c18101d07110ba991082c60380c1a0b90782d030144441e80020340d848101e5200144e0040000d4180441000d1321445501002212210500c2a201440300d000a03088902580100c0f108074690321 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 921226771 1250 921225521 921225523
    0xf161e06060302091503030301120c0e070810051005070f0f02030a0b15030c09271207030e04060602030313050a02061c05090c0f040c02150103030f120902240c0a0302 73
    0x81c1e400144e100700503500000b450394440c07101c14020000050060350659182003034140e01d5040c3d0403170407103c0313184029001c40d850b80300c0300c4ae0318402c03402c0b0b41d20709100f030801c00c540005141c0f10350001400b64440e0340f104c2c0b0885403c03104503600c540c0c2c003400d07050410303500b4280750740c1c1c001c0b51440096150040c00601d80c00c0c002c0080a10b40141c50182411403036000f01c00c00c05070781c0c105400000c1c1d0003003c000d0000e1101070002003030100181c9440300340d900100400050078180010000da10907006c03808200d40d400d160b1300c450103084070001607808020650608a01035502e000007000031410809031100c1e502007020900c02024151380c017404194503805803a4148408070180d12000310001d240c42d000410f140d10016080340551030142c5120050814441400054100030400340154440d82c02032000719580d04009134001c6029a0741e0781801519102d00034804000c600002007030314100828040941c0c2d410070085007940b40740c00b142161100f05003604140307010311030f00c0c0740150043c00030003024150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 921228021 1250 921226771 921226781
    0x110f030f0306030730150f1e05010b030f040311070311150a0e0105030a0b120c04110c1902040e19060b0a031104051003021210060b0f161e06 62
    0x100c120700b13a5018a03260030900e001034001036a21200352a80e1110001110004100184400e0140154104403003105440106480b6042200d030090f40d0340341c00b008044c410310704030a890840401003e1002d5450709844d40103a002c0a03251081c0c0c1a09423021a04050180942cbc10054040105641c1c0e007940d00d05010a103040c0c001d074400d01174655030b900c85440320031400880e4106192501e8901185104000444461304004c0002c0c0d806541c0703030b80400035030f81ca00e000700222800c0e0030000c1895240081c180419035066404040e0322140a0003403401103d004654502034690110158038003200134000640038040c402c2000400b4081d40c5840950036000b8804d640d4450300801e403d000c0001100c0034409110460310015114407899500305a052800d034200c00d402042e241503e91450361aa000946006907402d0002210350064244c103178007078614060a402404680c210750708000a100d10070086101d05104551811a4105c9400402c07000981d491704c2400704500c01e0246200301d183c0940281 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 921229271 1250 921228021 921228031
    0x90115080709061d010e130b03010b01080f04030e04021b060603120a09140307170313060c0803010e04150e0706110703113c0108070e06030106110f030f03 68
    0x4025000041c4500d0046001d241150351560302c0e10a02c00b0084100040191505901030412815190312101c0b03541300100300d010360400100020301c01700024100f50031a0701220009040c402c905003000424090350b0101507016400d07061040300c9081110008000b8403c212840c0719904d440004103024001c0002d55030312035081581110208195000341403c5401500154070004040d07a1003481400d5100c0040c01074201c2c05000c98800700d0f102d5034052448418882941841c4d40081080b125132265003a400740100f0031410040c8001c412500c40151343d2005024480c2581803030808035003003010250803d04015200030007080344646164035240c036042c041c41050000f9401d0322220065510108440c4202c0780d0021000d903541c41c84109100741041c05140002d00c480c1210588074104021142d01890012007003000401a02c21400141c050800541443c040107210200e00b680d94030b800f4112815079219080114190580c400080c1c03a05a1421b1049414080400c0002080c50b41d100954020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 921230521 1250 921229271 921229277
    0xa09050d0905013b0402040902120f0f070e10020c0306010b0409061707061b0803100e150306060f0a08071706070f0203070b07050f13081c02030d110702090115 70
    0x10031a00085032a507030943c02402d60030341c4004c000c0555044480350042400e500064409820190f860345138800301d0f013040100c240444200410400d40344100f414450f8400400203001c01d240c24140d0006281001c1c601440d400f42206950003121580208100000c1c214000c0c1240c104d5a12a0a2440309070810300c1903401407401c200340071036640d1510f0350005a04484000401601e0318000084903d401c03480d5800010210f48400800850000001140700b006001425514140342941160b15040c00a150015104810403048501d40d00421010b4000c082180c040d062940000f00041c1c5182c069880042c881c0324024001441518611128513050030fa9001d40d00e66940301d15003500c0780b0081d0401040183c004000c00300c00154890180d54001c0c0f02407822600f80220010304803083d60000c242402c800014140400c58640c0400195406c0c0e00c0d80303060403401000031640a540c80c0035034098900c100b91075400c00310850125605890507150000d011000e07959507080134442c0b10f6a030610710000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 921231771 1250 921230521 921230537
    0x2004021602090702030c061f08070909200607031112210f010f120c0f170d0525050127053018041506020106050d0b010605030a09050d090501 62
    0x1c26002001b80c036402c0f80504060b01a0f40e9904010b4111116462500440d02c5495032010580e8007040003d175000c1c107183c000c006116042400c00f48420703080e403800344d0300c80c0c00079040020b0251100016907003855814207081012055880105090902408038500d0742c440125640662106400c05008005240c405010240d1185514440b00d983c0074000c401d41c000030100300300400d82094640082140c003030201d0041440e155042203070400b030582e10200c041002e00320381800310302007030000c40441c00450500528183d039034803000349400d00801440c85d03402200030b921024020203400002801c40c3c2c0042000c0d1120415400310030310070889070240c03034a11070301880c00800001e60310b0200b842da032080000c095000404141480603840301c041c613581c0d170810000b02136980c2c60328007800070070081d8194448061400e010009007111b0860340080d10500d20b0391042c20104e10b0240503d4103592091400e15034958030800400068240c41d20020154810414101899503010401c0310070f0380c00036078803404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 921233021 1250 921231771 921231781
    0xf140a03051f0b190611100c111c12020c0304211e02031b0d0b04060203180a11040c180806041e150c0c020306010e010828200402160209 60
    0x10311104138242a1014241a01841003500450404090203808000c44104a910b00781c014145e1700580355500215030418041c02c0200c00521007004098403200310001500000100200041442940c040d401540041c1924495401703104a0340a44030030f40310004083c440088442e844d41d49a001603070304203085405842c40c00900443c910000e6002002065580340900000c1004d050b1f0408850380090508100d60001e07107403401c403e1040b0f020340030058903071030702e00d80c041c580406402c112207154104c1aa00d60004800000d80d040da01e005640015807248200400c1d14125080c0d412020891070350340700016850400205940f20302c0c459801200141c040b44c401c00e5680b00480d0307000309003140c6400c00040031034080e80200143c819520b0404540a190b80200c1c1c100f060a0300200c003e11b50103401441068001c01c44202066240b8000e003126510390154145807019441c0d00400741c0b20850700380541401c0c1c24040840009008104641e5198984e040007095140c20100b20300511146000036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 921234271 1250 921233021 921233029
    0x3041e0b19050310030b0717070905010c0b04080f07080d0f020901080a0c031d060f070e0a060e0609151c1505090603160f030b100f140a03051f0b 64
    0xc408440c01c58560505000d01001035405401c02014108110243c0d000040030441c040d030300c18005e482c5522854803403819440401410000100101c0920410306410003060b40c4c040c44400c00d041c0c110101e214941c84910701507000b44100178402040c024046000703420300050400038402c1e142060010008140f110204105030b0080340251401303d00c1400c001040340700290019241c001c0d1713529001807800804140d07400098000418250158050700c200604408500c200a0b00161582403120250302a00009820600c07a4003e074403c02c46200a1041e440d124513007601d1192038005e0060400c0780d42038042c261250003503003005ca03814065950380d42c0c0c0c0111a1242c140c0784400f0b000c0320f51090b824481440000c1102800d2240c161140c00d01e664010740d4078488403000b0700003992074805c0040c61408e00081301c403400340503230640c0c03004008204107400d040460380c411038601c032300144071070900c08000601581665001800da40284042481d0590524a0700c980c0c145101c801004854080c0c0184 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 921235521 1250 921234271 921234277
    0x30117010c1409040b041d100b031c090312080411100909020c2a0a09020f1b0a020d080306010f05070c0522020406020c010f02010c1e1103041e0b 64
    0xc80d022940000542c1c501030340403030007840180d201500120f40840d118010800f222040003500f0a09070203003085103201c2d00140080b00170440e407002c0c14031601c1c5200740029142c401543d0b8008043e03000401c544e411900542ca41b60045800044565030302c8213080024250000413603040714012810304240855180c003054001d13000710151b0700d1114441c01d1402510007507002c41e140c510144209200103000c0d12014101e034880c102c0400c1d140d042d10f010070b01400011001c507003010031441d00511a520b2091401003e441c02c0c0c01d000e208810309a00c0121005040101b4020040d4104040005283c18840a10011801140217a0f00c114031107070000c1c2d04481174090354800401034041680200094a0300c034541000030b42034840003501141d1032080100407a4015440500540c2050f038640c881c944c2c00c44211140300c4800e000030f002d906450030000382071a8200880010000000d044091258494282150900701a6040380d541d075807541150a00b10901010040345008120741c0070880141040c1a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 921236771 1250 921235521 921235541
    0x13050a0f120f0906031a0303041805010e1e070302092d01050412060c03021b0708070506030103110103110903030c0f0712120309050c0a060806010306050301020a05071e020901030803011701 83
    0x110f20881c0d0a199040700681903130341310403013079003410003e189a40d5018001400201010503040c28042207503600700c825104141d000c1d486d100700d20000c0010a12028400e03101c00c81c01c0c1c82c44104a5a901c08065001b401030041e15a000540d607500d00346c004c10a124807181050030a5280303042101103c0044070148591f0150b5032100c40001c4443d0006040c9030801031429406050240c1030a420b80441c88107146055003590b002c1c5e0004404201000c010f00010001e0301059540600d15810b644804851446e01ca8801d41015500c8980079030104060065985020740241641e60710039802a039941d803101c0d10701d00c442d41e0740562500090310354400e035015001541d00902c1800500e607140c0c410360081244130710564079402480c2c4400304623550820700703c0140000b902d03020100e00f030040c001400c8070380301e402c0180241c1c810017a0755074868000d800d5032841a4803200d600d0104401000d81903801d1901607009401c4660b880020040001c04000f85043e640d40c448084621807540503124280c40c90f080b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 921238021 1250 921236771 921236777
    0x12090105010e1e1506070b07230a0f031409210c0a120c0803100e100302060412030327292715060f1503010b0313050a0f120f 55
    0x80300510182c40000b0f075031340864440141e4201644c0d40d40800d00591000004481244032003013089403075504442468840d8003170f803500c1040e0100300b9414500c540700f0004071200344080501644130480c0301e03400c41c01c058500300344c8198150905180c0c40d0750380c0e8891b084240e4040401d9801400c801020800d591607400d2503001029030040680702c080000a24103408001c015140c00340b5404600404029070203410011070300c3d0015482c00d07600089245010304542005045404208050b90308c400544040d40c3c480d43d1507021190180c5404da00030010b605040000b0a4003100009002e10000c1030b21045900039004d112419070312400301c0e001c0c3c5001f00301000f4004000b401007148001a54003800b007084860380da688003501160002840c5c10103000c60321540d91154801c109607800d040c031303503440001d006032140807075417074815061451030005010301c0003403840120010b42084503103080f01602940040c1510140316803420404400e2465101c166000c00c8000f0f402d07410b003842091b900c82420800e603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 921239271 1250 921238021 921238051
    0x19030f2007060c02153d03080c010906060906050109051f08060126070e2202090316060e0a12020d12021e030903011a0a03030c060f0212090105010e 65
    0x10b40c5200040c40c40300203100440c82035203030070740480385407486550082c1e1161500320115602c520b011074100b401114401d081e1009a02c200f600d0101503c528815a94813214841e01c0b04110f8090074010601c900016000030b050040010f8800307235541c003980903100280c0c0c0c1e59041e161200c040c17040d00d000d1441d94010301c084602072031344880e1040000c59000041490304182e040c2d04510001b141c00b5100340d0fa210040000c1061090b02a0000f01c1801c6c456010b82c1c160340c42402d000400d40b400040d850161100540000e02202e0725a01402564040681c1524941001b5181c0310b00600840e1450a81030140c15111004102c4000031060080c0c5e09038000c0503030f4806030352551800b45031900e0b800c11006511413040101c040242c07005440090380640002551208281c504060030340300300200219040703031f00c201003001c1522008441001e1720342508040030030444c90f1800300c00070305040346001403031b510108252500c5501c00c0e483c41d015a950900070721169032540306054110700241d501c1035661402c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 921240521 1250 921239271 921239273
    0x5030303012709060204081b011e1103070206070c090b010c0209070c0c081218041a220518010e06011401141c090203150402060409020f19030f2007 65
    0x410740d8560390b0003404030040380c5503403d9960b0348142d0f00250081e03911900049440c000d4058031001010b86548246400c1c8148560a109840e02441d0b9003003880811040d500c0e140c555103420022100d2196020b817a050742d6203074038248020344220500416554508010310000f0961140d604044196002400411280c598460030369a045207144100d03004440c2007400070744900305000205504414a034450b03503594030940108001c1c240d002019100c0c42c50119001170503c09207626184c00c12042e281071030001544074203081c40003214a01400030301d00780010000e51408022003900d0120901e4020320104010388070742038880c003003409280b0f038201085545101941c41149001504d100003022103140503070f0b0000c881441d04940745551001ca071518000743c2182020400480e03501800300081c185400c00380d0010b1620b200e2441000c8803150040f446d003501c240f07c40c040f15040c00c609903030991704428820b8060044e007240c6860070141e5103402200c80c460000300c0c044038840e01e03040d5405c3d445d2500e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 921241771 1250 921240521 921240569
    0x5071712271005030712090f060902010c08040305010c170910111b0604021c05060a0506130e06190c0c1b03080d021206040207020907030e0c03190c0503030301 70
    0x805428044124205101440c07942c403a003041d1642100301e650b0b040e95920b80b1400103003c40c0c0345528030034507a03490007480001140715054080d60f0300f940071801241043d244d000407100c1212030036010703103406000500041004015070105807214000d484030612114161150303c01c000c401c4600386041d030081a202e94103030015a00119900e2210301c99035060141403282d000e540010b0701e408140176230090040c882035141c400c090414007520030440880c0c141032650f9450f2a40c1010b403081c00d10315206c2c000704401c1e903641d04a484002480e150100071450300486a683c0eaa00c0648507c04507580494142d0410507050185032580c01c100d441d01400c968140da20b014810138603403905c2c0100b0b01490408400280036100500030500001000b58072400400c6401e40780d000050011071241e0f10401031040140c80b400481a84091740b81070004580403903840f42400c25501c3c075040380e8540901c00f681b17241c84285031800ca440741e0048054444031512501410342d644001c0c080d03000040c890310820994510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 921243021 1250 921241771 921241807
    0x20c0c0f0108060f2701090f0e07151e05031b0a0f0e040f050f1b070b19060807090c09050306150d0615031a06010c080f0c1905071712 59
    0x40580b4404e00705503a01c0c401d4001d03020881172543c0d008003201c010441240c580c00340c0103001c1c511800800c2541da248218036074400f030512901c6010149a56000505c2d4014901e420054a904002c00380140c42c2c01c07001880360b40125401c607428003001040380d0150205100740c4041001c1c9440b2010700e0b6420401c20f1f0fa48808407214254041d445d02c08520400149010702e90042e0700d030300d90345281420000c040301851411400c0c81091003001340610340200d00051551500122035401c201280700e00f41241070040c002d03c0c0c001361040d00c81c044000412000c0381c0c0c0080700c03034640ca95481d43d1407074488080617102c900558030001290091300d0020124540110700d042214400c0d40002050305004164010340c4106600079103031400620ba6042c50369014448c6560700c03c009290111010301603070b54101d194010011004c0e0084800f058400c0440810000ca20b007500c40146010402c0c86a80b401c16550711590003070b038800200b00345040ca00c010f00000d4a507c21000c9400310344c1800070080d50703414030354 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 921244271 1250 921243021 921243049
    0x2e03110d0f18030f11030c060114010302220906090b0d060e070e040516090e0601031e0609260f09061317010c03051f031106130801020c0c0f010806 65
    0x542d600703400420074050040d400302e294400e072140401c040b900321000e040303281c011540403640d81081104039007080b03001ca2298152008007242400189081c00102c000b40078180000da503040400c001d0055512078480e0b031104540041302c0c140405902c0d80c02c02c2c41660450320b407180e00408442031a000003400343e0801c001c00d000340000c41c1e600650302c018640c06040c0554054825800c0100110400300003003001001402071480305008503116a0641507a650f01407001810035010707103d11800031442e1309148100582c200c103081c09820102d0401c0e071400005901c400500c88913242b43e01c011a80304074161000c0700d2481c0c910908104550091064550010042040d00c55140401242c0125508c00c2c1032501041040001800070030201c4c003a003140c0010700604c0101c3c1489404030202c0005004480070f89034004a400c0003110b0942c0400c01c2ca0081c1001c8440b4034041d4030010444000541c003038541c6441c1e007803ca4aa003c0c0c81b0060000f4407598040c0d250000300450300064040c101184601b03048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 921245521 1250 921244271 921244301
    0x2100c0c02150a021501060f0c1b080309040c0c0b132301020309013b01020d0903021b1e1c0503220506030907170c2e03110d 55
    0xa6640c59001034041040154540c200240100b00301400550411160f43e1110810403c03070fa055040c058043c16413020f4850f00c41c10005046c1c4c8020030420380a051a140031100503028003902c1d10b43d03084548941103009207a0017213142c200f004d088644900e9000d40c40b02c3d046005001151122000c55400d0800054259580c0c40070341c03405000b00700d1002d01081148480c000060303e90070684411820f427082d138880b075403003985440d01404000710041198400c2c09506c000b103a00d0b105288003003d01900408811160140c40d250141045c541c02160002560302031808070394070500203030b041014150142c01c1454401942d81095060342c1064021805402014000100300d104039580b510b25544c071091010b1503003000007150744007030700701070300c64202405044500e1820341c40d0801134241d17241850b20807074032950303000b010104020109008134140000d000e0b000103003180515081c1110700400c111a00c00c804881e80742003481174803074800d40800c001140d21103841c0c89074004060707014124404440c411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 921246771 1250 921245521 921245537
    0x140d050c03060703140609010303050412060f0908070c0b1309020c030d111b030c0c0402090d0b04061505040b0a141302040e090f060c0304030c0821010503060c090102100c 75
    0x129a4100101c0c0d200c3c006036070b804601c0000641c024a1420b4000d40001e001d0012a0300500000b0b8010702a282919922064404106207a0030000d02070010b104080c0b003840e29100800701070002c188001e200f880e0003807038904200b039542e516603100c40c4600f0081e0007450301243c0c0300b440760402c150000c00007845003101320b0b8148200c1812104c111240000070720161500025140c002040b00c070010135000e00c25402071421701031010321154544070309102c1c26125640c0016441603e40e1880c0b166150950010490049482d0600d80400149003d4880c2004c1441c07050001a061903c0e00a00b02800c0d406010180428600306c141d441c8524001e10f010f40c4824440c0c0c8480e010705d0070348054030040421110102a60802220f0300d030810a035864182d41703d80064003080152010082101c0c0c02c55410700c1d003a49419003608000305a0300030941c1d020f8510031a0b10550203850090000241a1030b4200e05880c0103850303500d19244640715544410740940c0040044600c01240c0ea17106066282c424141600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 921248021 1250 921246771 921246793
    0x3c1c030213030528121b150603110409050a0b04020607120f0806040e032208010c0e120105010501140d1d0a030212034309030c0b09150c160f05030f07140d05 69
    0xf03440e9103851221f110560702e04081082c130140c0407940c600c40350305030b0303081103044400e48596032188442c00002d44003c0e0810086800c5480d150115400180c0001544200e444440401888007140c1c02c020800076480b2804103c091400b8441c44101644440045281c100d5a201004400304061150a1000c4540038009103138a000e0180442c413400384e030703a00220f0307200310020800e00c0965014200c2c07580c0c1c5003100501075640c10800b60702594011f410055110f480c11180500503099205510720007001c041a107101031180010030284141c401d80a544030800041414612400211501c6103114020781c00c40700f41d0b00c1e501d0080c1045480020140d004240300401c91010410b00200a60004404540800501c0201c0c2c00800c0078088940c41c203482d00d8880c0d03000441203000c4d081c5109251100262846840c1820020702c884030100d0300031855415520800880d1b05145803081a0083c015013840d044105008100e12090f80c1000c00d8a41c40c04401d1000d002138004191411500c1b44220740d9164 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 921249271 1250 921248021 921248033
    0x115090c09080105190f0c08130c050a17101a120c0603041208090d021b06071506090c1403273c1c030213030528121b 52
    0x4e4400d0b461682d5083d442484880804215900d058200030018508020390f800381f43e001c440c250700444100c83c10205007000f414146411511503000b40d070310203c52603000825140100d9404001401175007600c2c90b100e4520301040c2611450f0880c041c6200085c540300c4030501d0700700707400c0000413030220486106201c1000460754591094606403441024880c565006981c0f040c3c0c9180d0007800c0f24058228012600b101039a80c83c1e4411401e900000313008845142500c80400380c4802c140c10101d03880b5102c140b40301e00b00c000e04280c0220309406003010b004200311406184952450180d40070400d01d5075031800c8151b078058a030f000054141020181d141b0f4001c800c100b200700c06001c40c0c0a040309200c00c02031465072180e50400c0c0c8001e990b04144680301076100020a0846801080c501c55541211008804400038801c030101c031420450031600203c244900010186c0d45403010340b03030040c04541c10f503e841282c0c1d8880280242181601074016115034850550340d5001c4407416100d81140c80203541d48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 921250521 1250 921249271 921249281
    0x1e150c0f010e2b080f190207060c090b04030f080c1c1d0a0b07200307060c060b04020304120c1502030106030b0a09020f0a0e0607050601030f0309080115090c090801 72
    0x580380303561011003103a820804a29070203001c21000c0c20700c83c0c20b043c0340800203085101d0040410640c5030ba10030001351000340c42080b65890100d5071104554841031403809000518415030217400013060305070041240a003403021a419681c0104038441da1885c00e5031803131407542c8078032071f5030381c80c0d0040401080c0c00189000492a6803d540d8961948100418031010040b1181c100f0b031a105020190042121140c1d04086400e43c40e009860107a500307041109a4441c10600d0502940500c651000014050343c016003104500e4803485041c0f02c1400b0400400c800d0b400162805024502400e03210540c19000e85407021155105900343d81c0032021602000c0308980091740040042500c803190580346241000c9400b0141c0580c880c21800c104070900c00410f280070700702c001800e01044c042c41c415a590303010107503101151321904a03074144d178407450400301c3d4800c506400c07000b0420758074000c039a41c101070240030040ba010a280846480c41c004094000e02908400c00007480300c1580c0c0420003041c28059 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 921251771 1250 921250521 921250541
    0x3040918110409030c0807060618022a1e012711010311030105010c020a080d0203040608090729070f030206072006070c03021216021e150c0f01 63
    0x5500240ca0345400c0000075454103005061249103803030000c00c0001c0d000a450001540c1003030b2800d8840c1d19619129008080d184c104480d00c8524901166015125070010a040000c41c10702050400c840c00c03010400ca18181c001500d40d800c540b2038600380d5004008041004140d4000201d81c41e00c40c59440400200036a000b818002100d6603075005208420000350341c181c0d07007883c0800410240d200c40399124003040c040e0b0390410592500b52030555075659002d5001d03080100c141d4004600700e0901a540340d00611135580401c0c071000000300300030008600f503011140104a800d00680c245850300002507100303044201007080a01810001c140b040c01d14244880c401e4004040d00d081c01d04020740400650340c02c0181210b0194403030214200f021480b0b44d08540c1600b449110080c051506038281880101d01c038a07050741c00300d41c0202c01461020000e49150081d07458890850940c0840c003100040d0b0118990080e20107031f80c0c41d04c00880341d00101203607407070a001d803401188404061800d50f40c2241e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 921253021 1250 921251771 921251801
    0x60309071715060108060a09020a0507020415031b0e040602090604080a140106090e070312030e030313020108060904110d0321091a04150203040f1e03080a05060d02060705030409 78
    0x6402e181c1820b20141c0c640050013403c10016610b85500003440911142c01080344080d0080b591b080c41900801c16100030b50350050080c4000b8440c0100c5c040500002e00c015504082258030b03210980d00c4090009003561010505000d030741e910790720341c0d4020750301ca01c4113a504020704100c0010200018031401d0316141c80381803400303500385100c6042c4e401e4030415081000401d1404441030b15064000030032000b2030b50b00624185d4403014040f419401440380203d4410940000003c0000c4042d03040b0f980043c3e98402d8036207564030b0300c0b054288201c0b1081214001d00042a0390345112051900240d04401517109240450f00032810080a144008558201007601611045114204205008000b15640040c1c09000740e03841c06484910107180d11081d10903d056002010400740f01c2c08031407880301701d5000403241514240ba040c48100b4960640c0301a00083c40d0700f400325a00f0130070f5008642c000d007001001400c3d4000650204021a844180100c903184010440040c40c00c685001d2051195a035030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 921254271 1250 921253021 921253033
    0x507080a231206060a09030215040f0b041706161b21230a051b030406080702060f092d1b010f0306030b07030e16080d120603080301050603090717 64
    0x2c84500c0034980050601403280740c0502407104a03d40c8038a040c802c0b60340454007a0303201b90041400c21040c0c815a0407001d0300c1c20b650070b404248055900002c0044440303080d8159110800b8a06154075108203032039480c2002d0f1700c0074082a100b0700c01e400c00ca0385911401c501c2c1821943d15918040c200f040c46a000d0781c2580031000207000c1c603402c071038103035102c800d040c880d0003110070000b00041309032081660300c00074400f010502c05000c00c400703e80c2803200c0b030089045a0f03440f03494440207410408200c03468401446070000040a881c19090f0507405580c680d0010603c0b20f019103038001c00403204080410806580944025440038200001050740c5c461001500814034a4400100400d0301d40d14024141400e051003000020f0120001680c0300c4090320f0000780e4504509550340c1000c0188071307450340e02e4403010000700d0f0058011a248000255949850400030034011602e4140c810b1031001602490041c40100070a091031001907920038544e00554001c1030310391481c52010240b445100d031aa0b4000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 921255521 1250 921254271 921254287
    0x31315200f19120f0210092f0d06020a0327031701150e0f060310051e06040506070c150e0a061707030906151211060a0507080a23 57
    0x40c81204012075000d21040e480150b42c0d02c6540c00c0b41d11020020781008004526001d80d94070030b00145001010821040c4554202810450042042d0038868a0044106900100300c00e0300b0b0103481485400187c03000700ea03410345841e042e000b03400031540c0c00c0500d034442d0200c15a12210314151402e4600d030340014640202c0034100101603041030344403100c01082d8140188041020414a000600024034100381c48611040120300391044bc04d5005030051000b0051011000280701240f00350703081660300801808161062100c61503480007583d800c803c04020a2001d0f0816000038190035011b54800109565102580d525020780340c504000003500c190450300880c6070000022000702505d2404a602180740c000b0099603a5014001409169031010007004000568210654090020380000d40207030b5918084256090786201c102c5031040f51086a44c075501d802c40c203507003403010303141c2d9090b0400300250f80728a03103540b00e40d6900e01403009904000c20750030f1086003142030890301d61000c1c6407121070b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 921256771 1250 921255521 921255523
    0xf1201150803040e13030215090304030609030509011d010c02091b0703050403060b0a0e0610110d0f030f05040f0f050a0203061303020c010f051603090b0a02030912031315200f 77
    0x5d003102c0100c458203031a15001c80d50014811403400c114141c12071643c0c1b42d4a60f114a9440303242e000030540e0303060801100900d03401001620041c80c080c2c82d01641409030341c2006000d040d0b814002c43c0810700514500026091521455500a007140c140c1014030042007078003642a000013804400045c00090300740204407243c000d40182040c2680d1641f201810080114961100207142ca80949203203105440420b01c2a00100d14101041c0309869880c03400d0b150060080d0402230070b40c0d000c60700700180d02030700e600746100ea030344a6900941004440c0003d66a01403403881c1c0414241d90707a01c90021034402603a41130001c54007404110b5041001c1c00c005150190130102c480c19002d050040c3da03c014810700360032400f1520b2030803050001c0c4038441101e00e400e07241e14990b030f0410704041201060000041e5000001000020700407200c2003e0070036401e4801d5602d120b03024400341c006003003590800190441c6600049900580d06220070030014503034050f203009541a00c56416684500807075000184 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 921258021 1250 921256771 921256799
    0x7261e06180a050a0f021003111b0307060c080108120c0d0e060f0d0501060306080d080114012610080d1215030501021204060b03120306120a02120d020d030b0f120115080304 76
    0x8013a0402740400300503c0d054000d1801420340740c5d01210140106441c2c880c009004a850080d80500e04014032000c901d4001c042450034040c03c0b42500c201d054000303a41c1c0d260019a20800d4003280140580304000408071517003213920010a42001090042c0d5a60101c1d120190881860406000a003503241003001005d5895a80c021242c1c0c1d0840114060035a50042526042d100c095409480481480c03004039500d14495660b1120301c12a4020b5210925800c040c00d409100c4007460000700649501072140c83c1d2542c06080d2020400400e00304035000d2503030b040002074136078030103a20854980d00e03110310b070a990244c00f017225000448000c00c000c2100c01c0c4205071406074140e005181c4030344040c0348001e90303100203041c191241200386c90340d0204540401c00c00c0d407000e03030291509040b92a140341c0f0350341d03070405c48001001501507603000802040c401d00c51403c82080041c280d03024641d0f09800c1c17100030015141100e00300e54842101022411318020f4400040250400442e172f103501e40055110100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 921259271 1250 921258021 921258049
    0xf19180b01200322170601080c010e0306040f0c0b0c1e01053303010212040c140a030308091c0507020301050603011802060c07261e06180a050a0f02 65
    0x6495010040302d403890000a50700103400c20390b5460410b0421000200c60240280e101a0303000c0800041d1000c4040d01042d0103040702c4182c402c9442c0d901ca03000054950070022800690158880c40002d000320b50811009880d40d03000b0100d185080b138413280c4002081c3e0000140c1511540180d00764034481c0c4850004510003500d00d00208a030303060000c540589280f00b21008100d4400d020f41d4842d14003000e40320245c9000004000b10b60307a0000f035444098030380c0d08640684401203807082c00110150150040c042044004100f04401400c2d56001c2d100003030043d0040c1803a107d801d02c440070000745528140ca4035000ba4568507250f614610425080d07940c0208032600990516075050168002840700800b07941d4111451a1a825489110b0385455580d034000304070702001c0000c9024030404404915011001d04040c0e036811840d0800b071668805424600203483d0340103c001814800102c05110714180c02d6806560b500001a20b985281450030350040c0e07410421700264800310b141c4404809060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 921260521 1250 921259271 921259307
    0x903100c0807210e1501081509010c020a12020307120e1e03060106031e060e0a06150c06150e040803011e0303020318041d0f010c0e0f19180b01 63
    0x2102c4003415030f407443e003000500c0b04006894800101c4220b60a001400020042c000a0982c540e9112000c956441804070706d1842c8c043d0319004105105410301138045038607103a80007004422003558070740c800408a1034030395007140000c0c080344000031703211400004d03180c40c44d80c1c40c81c011020140c20881200811013840344500c0c6214101700458030045070190441d0050b00700099121108c00711402a40c448003076158005150140c046450340d105d12420b8013944400300104009600c585032000c03604540441c0501040f2000a000002000c6410907210798500c8201a94207590f95404003030300c520141d40880c1d40440100c010300924130b100c19000c04001c8a48a00c803200c3c1e184d84ca0207900c074411810144102107125018010300d48403508441020f5880b180c04c90b0100c448110b015032601030b03802c0520525424401c1000c2424440c02081481d04001840c00c0d241511110810014482d00702c80c441d41547c20400002d400c100854002d107007042018004183d03405004001422210a40c00250031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 921261771 1250 921260521 921260537
    0x21317010b0a03080904111308010c0c051b040b04111b12040b070809150d050928021201050405060a0509060403050406050a03060305010213030218011401080c0903100c0807 76
    0x70355101d490380000c40e81c00000b1581d80f2901d2038042400f801d0350700d2212022460001d80a202100302032012412209104020400d01c1e040e00c60460b10007400d040060700311f5000a1102010104002c0d803844000002031000942c044140041340030b5400c5030081da505130102250b8048800760400400001c0e2113400060f10345100b035400030049500950003081c44100b00410301c402000003071b0040768005240240f5281207050b4038100b81c0b0541c0c0c81144102a0241004003248000a000640640050000d006890000304c18220080140080c8038107a03800691b1800c103014242003841101d01580c005d01c00741440c1c0c941402d0a81c29a0005801c144150b8000300821010075800302c02e450960b145480d015a07501d200c42401c034040c0109070030207409548000ba403168400051540c04040301d00c02c0d0f814203450000d000c0d88121540c1c0c00d110f00261090071200030300c100e61040490952258444410900b4480d007440403074600140514461900769982a0704800e4a0b001420981d100e400c074580790340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 921263021 1250 921261771 921261791
    0x15041b0306121e0812040b0603100615050c19030c21050d09050a05070b040603060614040317041a040e0a05040f061a030a1b060c08040614090402131701 67
    0xc0c0c1070196003c1c0104030448110701410050032a084400a42e81d000300d444d5141480d050101c8a0201650041d10034442d03031001d44071070140c1d40034a804440344030001c0e038420201d1401c252401e501002164070580102c0b10703094982103500e940750075164000d88d94658280454a041da600452280b403003d44910400201c07504035130b01000300d590582c0d0311203001c10740403079629050b032504951f00c40003884c5014011f004104890070724042c10449001c0d03034003400040c3da108000e451600c61900314465071601008240080f80c0c1601d031700d0102c940f0b181c0c49a4a07180e941c001c201d209551044404e180349400250411180101e404480d8111803000700801207814580c0d0350a080080040300248495120603260003000000c2c1c0c12414000c1024007902c1214030a803400b1030101d548188110b40d0804982c4022030341d60711a0f40c500c01420740c8100c25920b0181401c0b02911180e0100720f0020306107000300600c07203d5480b18000f40c0b1140842c00c0d2541d03c45400c099401c3c512201640e003034910f5030314200b0455 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 921264271 1250 921263021 921263033
    0x20d1424010303030e121621020c19141215070e010e0a121202100c020102130f0b0301030305090f060a050723070e0c0c0601080f0d02060106090b0315041b030612 71
    0x16038010790900c840e800564a07032400448e4803282d070107d80505000216000d80d600d4002c0707000f01ca502c1d403c9030720301d9070300c00182c04001a40c03070617010340d610007481f4110360082800d107441090b207000b03a21822114151004003400204400840700f140000c0d03450800781907a540c0001d00c581c008581140d1041d58039007458400400c0340c9001310040e24080d000000302400c18000e001003030034400d112a00b4090340340403041c040d001c0c3d0f1040d591a10001849200040c10603811501c03c01a20745a1903400c0c5182d10315102120907800070078410390300c0514040d5400f8203070354400090070188810744409407108054104100b400701c0064108003050611081c2945000307020440c142a14404c0065020075200c14103441d8090088820007103141c402d410021075694000115045825000c90440d0040c882900080f6100d0300c0c203115170b070007148400d0018000585894041c5034401000030040f01d2070040703c0e002400780c51074120040c0030402c0e181d9000c840d0aa050289402419a2000303240501100303540e51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 921265521 1250 921264271 921264277
    0x1802030c071209030c061106010e0702030f030a060b120f3d1a190c02011704140a032a0b04030503060d08030403050414030a020d1424010303030e12 65
    0x1000001c0542c6984410b5003d41a10b40245810084186100d13480300c001805408003208038403440d205960000406200c2c0c40341072842512135030301850900030708501d00c224640000e0080d0f59105c1e154000071034500c280030b01620440c09a1100240d5505041c150300301041005064500481c07141500c10780c00000f841c555002114032052600c140c4000080d00350f00c100761542091540f80350407442515080004070113407054260540814482e11003014040c1d45188084400902040840090140003c07076040d2540e030090041c1c082c40b0205000f1520740e07040032200e2800b140410b005945a11201d02510400011903410000c54800e44502c0e40302e03c50301220050004040202c00030008000d5210084100c00d00713a0b01c580301c15142e0a041c50054404c0e0401e0140300b201021510841382c2500d400100080000e40241102e40300583c951929940081000c82030b140a03c0f1f0200c150b4498542c0c144900d08039250700c3c00385001035046150003800c2c4d0b4481d9030800070b10303480034104c8080070100c1c0c421 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 921266771 1250 921265521 921265523
    0x606030c020607121e0c020606180112030302160f0c0503030406051222050304050102010b010801030b060409061e1512050607030b010909050c12090d1b060f050403091802030c07 78
    0x504100b8800c02c03030020180121017070f05444e0701d01030701010717440b80016004515035103600e800742d60150380c0e58030601070382080c0300780c04250200e450401004429040d007100780c00e40c1d01904d0050b140c4825482d204030100c0d4090340440d19200442030801c18000b40711109030103464203d0146242c140307000001405c501440040982d040d441c1e0021400010b01c10510030b208000e00304812042c4c01c25400e01036282e41051181d14050b5082a189008642c850800141a01e9015041e12100d440d05800d1000401c200b0300211440c650b42c08204042000e0782c8101020354010070300c00f094000b001032031110460150750106503c4100c44c44e02c440001c00100710309601c001c403880c0028203c070a29004a540b030303980307a005001282c6880140601e48404c00001d04441140303481c0407840303803108081d042d680c103800c070190300014010b00ac00051440c07402c0400c981007401541e020a003100c044480c1011210107071411004548483c00407c004078503080d178500c6034038000c5004c604624000055004500c18410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 921268021 1250 921266771 921266777
    0x102040b09120f1c3b18191103040803040b04050c1801081605010e0f01200a021306030c0303050a21050901060b031006031107060509100606030c020607 67
    0x109602c00803410451a83c4082c800400c8405100b02c006020440c0603003200c2013030000c3c0807074101001c0483c6448001c0481c820540503188051300c2030b2503e10360700c03180d0100e4651200d0311940d5031841e0a00b0b418010f026080000c00703446560000003010040f90300c080c3e0401015003080c0708000200e0070b40f40a0741c0d4007603044000c00049a540d803604a082079403030456254440711f1100300658200380207256905a40e22141180e0301030380d102541c2e8254280c8d41c0f00e11400102c108100741280c1c00e0504d980100050103041040b002e800700c0c082100b00d0303504615141e800d44e01900109065150101181c3d0035002e811400304462410741c2c881c003c0e1702c074540c00040c0c140600001da100c103091240d20214460300d03081d103007806c9110740c424112014240903280c1c03018540c00c02501140403581d10f000c07a4000c0c0c0c00c03000c1001010346800d00c146c3c068070a03010311540700441481410081400340c0152480780070840c019201030441016035070708848407500040c08062400d421004401c0c1c000403015000820380c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 921269271 1250 921268021 921268039
    0x60302090a0e030f07051e0c210106030c030818190b0703050c0f1501090c080f0c043b011206050c0d06060206041719271403010e0102040b09 62
    0x810b041d00c0d5101301e51240c924603400103042d03800c1c403070003040711010700d0072801101601403400390506903544040e48100d40c5c08241d04400254040001680e00c450981a100210b5141d0341c9440318001c031542c9510959140f000011144041005441c05600410341128850512100031041003545e081c103000720441c0d418006003400500d8094803d94400c3d5900804803465483e00811245d1a2a5515403c240a000380c1001041d403000b180a84d00b2000b620355102d51941e55066105401b010000e00340e80b100355810000440c51407e150343d4481c0c401d90340307000d8281100038551850b900d07614004015916114100040c801c41240e4400d000c006a0000c0b0081015141c03100090028810701844001480c600403000a000d500407030400c3c450340c014220307080c1c0d18006280c184160306c9404080c030041900090122491405544480b0070b52440140c000b41c128070011000841c5150b68014003581c20703002d085110f41e882c00340214a02101036800943c10240703021486140c3d0b00449d4440d503c2142c6c52 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 921270521 1250 921269271 921269291
    0x3031b03012d0306020f190e010e210304030b0f01061b02060d3809040c0605030705040e011202030c10020d0507060e15060109060309030e01120b03070b0a030e01060302090a 76
    0x1401d0200b002d190044000c65840b40c601c01030035040e51021010080740d50205181941075401404110a4014103844400400600104005502d241c0f030503112a401c038031a840340350104041001d440a1486030070340308001c0c00c00c500300e030003034001c1640514104030f40c1c0248242da03030508a031405c0d50b0903410b0351207980300d1440e00101d1000e4220741c80300d00504a60b0818000d1070300b2183d0308440d15020300c518071444040e5102c041c0000c2340350840d00a0280380d618841005164032807002181c0c00345091030294105511000340030f107040c1d0b080c1d120342c204555007810002949410304c514980b02d081254a05443c42c481c090107511261502000381c01d029002c6800001d0180a03006034944074444400d8a8000315490030055962100f030301c48a000880c818004140540240301d2105006d406407221406000a100110f034241c003210002550a0307101c6402e6052a102082031501418500d01425100e03200450001c00312603400185034000d85c141001000541c81e0b030705081b40c100e80c803400c0c00b060001407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 921271771 1250 921270521 921270599
    0xd09080c0616090f1215020d0e011a04023901060305011a01020d2a0204090b040b0f0c030a05040804410108150a0e0718091e2c03031b0301 61
    0x581408183ea9409c06010640c08801903110310554000440d13080b000c05511400d1008034014080004030703039004e030340c82122619403809079010620f2a91554038428100b988800e0309458071a40221843c2e9110048103000b04a09808542290000e100070180c1000d1607000811007001210500d000d03400300b6006c440038400150b011000181c000d40140b08000d801d140c00810b44a0840b000e8404000740c02c003281d096101e40c131141c3e014581e00c40c00242140c854030382d510001c0601400407101100304020001d00c800203201003882c2c210f4400c0e0400300403140c0c40115103401ca000c000c05414818484203200b0942c0c3c1040c0b050f40c019038410b40f04412084210041400c55a00360490716200e00d03040f0402441c15030201540901c4018004844065503403480b0603019101e10f40c440540200c6c181c8002c014004069114000301c0008003140701e0786580c04e0064841c40c100e440090401c60300000b00300060111208480c50700c548005407a04c4c40c40d0302d004040024400f4900c4210310030502e9003603900703164031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 921273021 1250 921271771 921271777
    0x309240411011d040c020f0708150105150d0c09090c0201020304050d1119050307080309030706060e010b45040e2103101a0a02010b03060c0d09080c0616090f121502 72
    0xd587d8048580360340e21200c00c2943c80a1103001d0061003415500046440c1c10004407010618200c2081c2d50304000c100607402019100241e1244d04001c5c1f100400100c5c81d80718090440219a603400050340c0341003604015003000d51140c418002d000c40d07501e03202c11315400087d18490000c01c1e500d000b032003e02140b500c103046100e1043c0140a145021040c030000c50800300040c400a840f4841c1040042c0c2d903002c5158600100b4425205d00c500203000070460a042c1e41c0e40c1c0e014440307214200c682d00900940001000902044070708403480c0012a02c0c1049051602c203203050520740c1e000a0018420044030340c1d01070080d1200344d25205c9808004103441c16090352040c5c2c082c0041001010f1001140000c0d2035403074010f814800b0066003096502e41603030801045481c059110304001354907040b0004103510261180000849483c041084040062242841018050280b0542c04008140d618000404120094200e0000c400c0c20030001c0104020b4a66146a02c03035115450b00c80190200c1c201ca40240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 921274271 1250 921273021 921273043
    0x2090d060c030b090a0501030507170a0b16110a080403080a11190b0f0702060408090a0f030b1008150f070e30030405030c04020309240411011d040c02 66
    0x40c18181c62080c0389030150070150b1800010381c0c0112903030b61260031240130744000f84070250250300038135014007011881d0118000c1d07280000302156082162555521200030007103441228090b64044070740c070b140754030051041d400800d40307006202c0301241c1d4940013031344d10039072100501c8000c000404250440c02109090010358110003a510242c0c0c6042c00b00d044200c000d5402c0b00c48581000c0010500018050301074003442065004015941c0c036596944a00d41c40081c01a903c580e04800025080001d0400d10300a1071003000034200504100a03003405002064100003c02d410200c032224004240c101481c0c2d0001c0c40d007411516581740c01900340c6150303144200c2c80742c00000c4864811030b103c4500307c980071a41c01d45114080250b440550050300c0e4000c60007840e500d038105405030f807450f01d045c0c2c000d0350b00204102c0c2074170025218040c148a58034040c966844602c045482044240490089034590b402c60070b080c604490503001034600b4101c5030a46820b80714542d0b4111403140113200700600d5243c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 921275521 1250 921274271 921274283
    0x11090411030a032304141003020c0f010f0e0a0b0c091c050f061f0501110313240e0d08212406070b01030b13120f0f170a02090d 56
    0x1059080007400c00394519482c000000f0349040c0048207a204e03e040b1411140d42e02e140c0b600300d11001c002c0091820403100c0c940708042e001d00c118211903070207200300071000d0380000c00040d40f13800010341e01f0203842c544100c400346034010040a6000c03401c0c0c40b0805a2100c0c0780b071501c03661007005d00000768441141c120300da40700201c0c103040c0703604000000461008400c071203070494003160780d0040050383c1c86d120320409440385041084200919405003030000f401d51a4041568100a00c449a584d00c46540d5800180c000803000c0000686400e480352546484080345854680215544049180c0d4901a1002490602c00140801d5040e40c170a525807c200310003480d50043d030410a1700300950940c402e01080300320070b031000d10070001d141c0503040700c00055010011903550703803a41e15807440810004011030582003000d00c0380c00029041400340c0c84181d88503251504106d04985004080240700c80e40c0400384800d407802025601103031904140d1000140340050b0341d8078801c0c1d01141480c04205001010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 921276771 1250 921275521 921275533
    0x3020c04231e1302090907080712020d0512040f0902030114150d0908130b04081e150406020d0c0513031403040f0e09150c090114070f1b121109041103 66
    0x404248081c500d45051300850350008151540c000780b43d03c5d507142d4410b81410ba40001e208000041c8072200e200c0d4400d000904080080806444940c10900701080c5c20056000015052140641e007481007809080c04000442c00d5604102505a00d40e481d00c0303610f0320500c0714035042588100101c0c1158454004840c1c01c0c4800c034600e02d00242150828100002c00c8034601a010403441c250000340c80c202c450b54801001a111042003011400c808100301d0612401442d940910401078400c4040c0180e2246070300503541c44040340010704440038404480d08004040140c455003c075000581c100752604130038023504000601300081d16503c5954400e90600788070603c0040d1030074081d41298401c40e00c1e58103590101d0706a147c1441c809808440c0c1d240d070900c090040449a51180010050401d15a82060315000c0f041d1540e810700d004e200c404440101c51048110b4090004010a0b4010320050201400075203c90b03640000340510074000900401e01c4a00240c1849002c00d0342005011025043c0d40f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 921278021 1250 921276771 921276781
    0x81c020d05070e18390309010b09090a02150d060603061526130803130309170a1b050a080a0314040f050402030a0912020a03020c04231e 60
    0x340208585039004116002c510a9450600307014a12042d0203440c200c64150b522403080d400a141c051700400700c1e407107140e24060b601c01000c0b040500310805913014140c0301e141c188195400e444010500901410807803080c0003400c0c100155400e80140d04503000d1098400050443c60035000395440e0209450805c600000c4081c0c03d940410150796180303081a110b00400c1e1010b9460403164800d941c0c8000722610009008600402034540240702012503105010068860044039002a14240c04001100c1d01c8c8804060b0440f00d6030b4014640c1a0718000303268401140c1d1038884e06008005030003801d40500320f0542c9100d8810107805420001d101c0300c3c09988981e012503484003100411404140f04018040030880594107440403658900032240300300f810a070511001e0742018060302002c075103c0380c11b10f000455019204040c09020340c0246041402414004d2030b140c0b03010b0b40540a2864007501c60443e0504902c121002c60441c0c8128400783c44101e40718810760083c01003010540e8298003400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 921279271 1250 921278021 921278047
    0x17060103090209011412030a051b0c1504152c040902060a050301061d06090625080903120c0a06090213061401030506043303080d02040509160c081c02 66
    0x1000000c02e44020b0356000b100e28400b81c7c1c070301c81c0c20403510210f2000e024084581c20b01071450345415010405648041c02c0d40c070301090f1a603807060086090043c021a00b8450030003e80340ca07000702c0c0b034140342016025800906102003a40c0310007000c0b61001c1014a101d5007a11282c0001c11a2540074051540d10341c014007004040350400e0107410000340500ea40b5034660039401d070751100c041704014003061070020410300f000055801503404881e51407241010104088072200d00900090181d4060b6586a031040c00b01818201020810540036005101001d07501c800012081c3e81107511080004074940c10303000007007100c0c1c45800c5269200d030610300041454041c007042110800f500703807420703c865201e410030413083d960328101c9220b400c5071410000c04920041c402da10a03a0203550409111141c503034490f08c00650100c001d0300c11140e0001010861800c2c4483c109500c55000103e5924030442c912000f05142c0302d046000d03208103008181403941c0d200d002100003c5022011085540d014180404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 921280521 1250 921279271 921279299
    0x171b1c0f08010e1314030705011b0507080702041505060d06061704080703030c11030d060e010f030203030a0806030c09010602010b0901051f12090210020a060501080c011706010309020901 82
    0x5680014a9015211242800303105418183d0388180075142c60760f0358034259540c5451403403900b42c9968031070501201003200b091006084c060f009000104c0d00908803030500c40c12068140c0e003001000801c000c034201203001201501c90051f812140840d61641c4d0300140010008250000c560081d0001041d00482089030712400490701c3c15100d200000303e4050010b585014221005011104204040c0380024426800b82c0c0708600e4504051a8102e201c3d9409441c4d600060729040355207964200a200384180119014010300c82c0d080c000714010b0660b80030076224060006000d0a01042101042003a5002e1000304015440545101c1256940705ca0082c041c4c0794098019010310b00403000031640341020f241000090310002642000801c50b00c1c41145d03c0b8030810200c2104540c1c0301952401030391031040e2814050f0315940140956105400d025045843c180d00000c01e5a110401821103a6040090a42c6156000542141684e1400e0068029185040d0029407000c200000852107182000c0c113 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 921281771 1250 921280521 921280573
    0x9061413060804141b06092115011203050901120f090b04021014090f180a0c02120a1e0c0609030f030f06030f02060a091e150804171b 59
    0x1c0c2882d000e402c0020f00d6100e50508050171301c1d4000400300f0840343d0808400810761508060300180d4111601c2c4400007105c020340754180030680050709144200403207802d801c4c9c05000b100d49810030011243d60041c00324440c178a221410f0110071000d07000900650350200d610f14022407018011071040b880c0031a04000c08942c00ca00c00c4080300d511801d21445080100501910300c03003001e1030511180100b004155450b110076a2010b050004082c1f04040c4c0c0380d00c14040e100101020405050010029041000000303c048007440140521195903902603c201c1c0720120090041e004840c021078120f880b49151440130700214141b989040c1016400300c03004581905559003040740051401150059a03151700c405000701c0030b91602d4001600c2c0000080400c1c585505003241e0703055036204042070100d5400c0c1c0c10a01c03004a064200210b08010350307060302c2c1201e1450265200d02d0a80d5890010701c030300b04040d8000f10341c082044295040510000c0d980e1a0034201100c000009030103240b007042c142da0364 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 921283021 1250 921281771 921281783
    0xb06161a04030c140a020109030809060c0a06020408070803031b092d01020601050a0e01031e14060907050a0e130201020111040f1403030a0c0602090303040f061106070206060109061413060804 84
    0x80d00750b0303001003520f00003240c0c141e48000c1952700d5030b10340d1141c68020b1007110b80e03c9202041900d0889004015083c64144941d0016032154a06109542065a80d50190959400400400c8207030b10a1601d840700240304024041d071101011004102e2440103128414002ea018503c0c0100450306403150400c81c0c1000da0868100e681c03104107100201c2000d210301d5030750b010194014000a409500808ca00c44034114500c02c28001d80d48600314001c48000000c19190040310038041c0e41e070b105000038030180c002640d030b808a040c07a101c7c903040c0c0441c00801440740403c80303982001c11a8400c1d0445501d03990904052a26a52100e10f850b80b069400e110301d10021442c06100f0030942404015158264010b0f181d442c0052016101d250195000b2605164075000c20070003c10801d02d00084900a0300c41270396101d00b100702c201c83c05807400c40007801a80542d4001001c00540303a920140c2e01054503000e10b4082c460b001000d14099450040c40c15812008282203800700d400d03584030700c042e4400d43c0130399 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 921284271 1250 921283021 921283043
    0x210c0209090a15062108070b0f01090f022a07030501020f0a1d061c0221010303020631030915030e070b0c0d1119061a040b06161a04030c 60
    0x9100b4200b220b0f41486045d59000c041c050551010554903c0080e00174043c10b4000d24014036075a500500000032505003070b1200710b220051110a04030f1060010100400c0302c110b1a0804840b0f02c0c4112a104182d0405850351044c1803040b1a07906016a00042d50b000e00250b4032500000d0f0f50310303d6600a07000c010000f0b00e602d4000b40201220362081080040f025209500c0c0035420390140d4103002d1090700c0009096020028228840d2109400519400300d660901140e0f5041d07150007414184060010720b044205030b40c504503d420380d5031031820784503111070858100a41d40d180640d04020f45070f005016401002454669041d05034200c102d00f07580080903a6140d5880d80340110035801601400340a0340d0050822561143c01036541044600e80f440c2118030100003030740b07030403400615803900700c4201e500d4141005c64805504034000840703504640034441d05000c440440c6650194811a40c602010041c1b400140201000300700308500320324141c148a8505802c0243c001c10181e242180c600d0054 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 921285521 1250 921284271 921284303
    0x1f030b0105030402090129040f150e0307050f03010e060a05160f02031909090509161a03040609022e0909050f1906150e040c030207210c0209090a 64
    0x8808030b0b8815540240381603207a908000300302c203c400310310910764060303550200b00320303003421781d03680034200510150700c00b489082c1c100000301c000c001d4814198000d222a14021546950307010130070340c00303442c0c00b91040020091060002f80c00351622132041c1b516401000d00b403000d140f80c0703030300300078402c47c5800710201880d2100c400803915134401490300001a0028480000500d40c1c030200b100c8164203c2c039254040b581c90700070040c02c0390000c1e940280558441c402d119169601e01d5107401c0100b14181000d050b0f11141c9a1550032031000400c0140841e6480441908550f0f50b00d0509403400e10070707100000f07019501c48500d2500481654100d001c500600d1000448100ca030092501c508004240d400c13158454045091306150004200541161240004104c07040c12030140000b12055036130b15444080c400b0140011111648108070806004209100205903d80c00d03c2151031240b50300410b02c0700151301c041350f100c5406400254002c2c260000c0c0b00414a00241c2400035602800c081c0040140c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 921286771 1250 921285521 921285527
    0x61612030b04020f2d030403180b190305070f020d0c0c1a0406020f0601030f151b18080a02010c020d24050415142806060302040e010e250203091f030b01 67
    0x5101340344440042e00704001f8000a22901d0100e8a00310b8102c1c412411351b844400caa412a000301041400ca240082c010030442513050050315080031040c20426020f08101c0e070000e40300c42d05a5541d100b0f0002c804040c10070840300320100f100402000001c2e050544d26036a502c04070f54054800c0e20014492640c0d0321b01c8014003c6103660499030f00c076808021a40240da15011000da1505007402c0304c5035540562141c01c4030346007e4010707030303c1541d44404091982c4950074110022a40101c1e0fa1640700c44900001030360003904c1d00c080c490701202c112a60143d14030b8040b1495200202c02125000c043e11021001c131303804e402c030500491240070080000034461188001315410311158505003199000414040d002c0d070811120301c00301c02c0071100c007000011103002c4280c0f03200364820701c002070380010100104031101007001d02400c0c46602d01034060a0070301c8054401500b100c48142d620300c024078480042c50081044551a100c0600b180c61f81880400011505100d41c01564011034200455007405601c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 921288021 1250 921286771 921286837
    0x601090b03031903090b070f09060201110a051e1603120c20030c010501030c0510050a0903170702090f0a050903041212140c0607020c061612030b04020f 67
    0x2400650400d1540d105241243c0b60200201080c1075890154101140c07120003424802ca8031900e41108c0c81c0c1c240390380180081ca06510a00859141c25a101313258541c14003150012240c40c40c00070b0300c07809604100c001948241c0a0656500ca0015031a40c620000c5040d000a450082d1660200005401501c0c401e0b5964aa0003100141c0409a07404020340e01452620900200c142180d043c042201100e908481082e0410740c2c1146600314104020324100710081d40034945c44c41c001e4100f0f506480050300d4038802d4000109042510062007040381200001c1c3c2d1401030f0020107403902c40c1845441410b1000042d101b40307096038286400134800800c000301b250200c41303201060703800c00761140d110302044041500e100c0040000100d18406030440a00c05032800207145009490176003020f81c0d029142050017030740c03103000d507006100000d41c0f015a0300b00f0034002a000500001c1c6180129801c0b0024600e0071403443d070252003ca0340b07405038003c42018042da403402d5005003170380c0550381900e6a43d0399 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 921289271 1250 921288021 921288041
    0x305040f0306202d13090f0506010302120f040204021c0905011a0612060a08010603121b02010c062a020a0c05040204050d12110604111c05120a091703030603060109 72
    0x19a21018140211209000304e084d00b6640111003810010109040c0300c078880c581c3e11000340c0d140c50714141404480c0500c1260b801203004d0800f10f180094540030a501c0007030080143c018001500001410b54480380c0407101d9441900c030303800128201b004002c20060400540c16200d96103000c0079028400804501610b110704001c101e5800c0c0041c607050710020401c010700c0d8581140e4018030016540000740214000356200d0090100c60001e002c030014480080042c08035100c0320b40b01404400f50340c001c070840064907041407020500d054549100300001a40034101681c0d0140d4940e8280c1c00c65011070803902040c460742010f99565941d00c00c000a0b4095800340507880043c1070740803000910002c040300016030050a01c090b04c2d2032280c0b007090801c041140d0582c1c0c0451607544c240302c0f5191803500d030040d015444101c240c1c05842919490f503200c511940070b031410100040c1c1c01517840d0046080c0f00041c04c004030000d03403011083c2c00c0c26032246c0003620710a00074441e038400490082c0a600078002c40c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 921290521 1250 921289271 921289297
    0x1005190b011704050705180f010306050c09030d0f030e01140a09030207030b0a021312050a060203060109080703140606060c0d120f0504050601140607080409090305040f030620 77
    0x1000408808600400d68014800d05020000095400b070205a0b0652031041d401a406040b52505c2c202c00c2c02031184c04000101540c007072075000c008500d0160107845040d070f500b2010008581d0341e00c00d45d100344c40c418443da595141c4185d03540c050b012607000165081440c9079039410f000080e29481090300f43e58500e031005444020720000220300c0d211075846068568000d10444040f0b6a4a490300b000e01c802c1a20740b010f030701790006049000446050300034030050031080180c44940c5903985070a034440342640c100030085034000020400c00c1e0720501360980644009170503034000f07540d240303003007a0503410440010a840c0284400035505103030110541e084140d0f0701e006040031a0081600315110480c003d4450500c0c0c3c0d41e40101100c01d40540f103161b1045100704010401035040c00c50761112140342205d024491441088500c000032500c5095030b080350340085001c940043d00b4641070b145400390740c00030001c2c2d01807a0800000d10045400c00400c250356a8505004078504000c0303800342c2d00c030340c040310484 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 921291771 1250 921290521 921290551
    0xd0f0c0c0f08070320012a0509130b040f02090307050306011d1009050702100e060112291e070c0305030103081b031306032a120b100c051005 62
    0x1c960382c40000c1c214030b486032900201d010110035030080c10007804928151583c1d910300268080c0e00740c0e5400320b034918800da40c6042e01c9507071a020081a900c00c030080607001e5100060040c0024006400901c40c3d03d40003001030042600b031001e154000d41150311918401c0c802c1243c001a113060201303a0342d06a23007038042c04101d503011106594007203843c060584402c845545100148000703591250310b014911541c003a209810a100c140d20075101c0c905240b1100360000350040041000e940c040301d01d40f03a40802c0211016a2103142659189054800615117a1000f010400b65154184001c0c0708407102c0c882c000c0d00c81d20380403822158a2081c1400030080b0704100014000305102ca0049d108a44103120300741182e041010b0850b0440c0c2001c2c540d6030507c0303680e00c0c06010060b010f000d40d01c1011400d500003c1d80c10160301c00381032408020032007a418800e2814603144550215040b4030941c00014180d07181182c4603a000070300399039103482c06a9903401200c041403440c01e007501a681c0240420364140300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 921293021 1250 921291771 921291773
    0x105090c2403180c030718050a0515010f09031203060e0a020910030b1c120e030f0c09060d06020705060103020f090f07260108011b050f04060f050d020d0f0c0c0f 71
    0x40d09403840480000f01c0c800c006225513166420880030300900444c61140e00c0c0380301d96010050a413038000d0200444c03c0e0416042015040400c030040d102184246040e00040c0105071043c3c4070603819070400f07804118441c02202d4400e8042c1c1000084502007020381900d80d4600018004a0245154843c0c0c0701d0032404440e44001c5c4203401000c594100105002c0c00882c052101c912840e02625045501c02075201078801d415070040911003031180c1c26030180c0320221310500704940311108415112b10410781c44000c03680607142e920041658543c0580115514130b446e04150b5510712007440220b1050094005941041c00c041030103070b016071003a100c40c0980c0c0c0c669407030a45035503640c3c00401ca44107460106e01500300d204004801d000344040400000c908500543ca0380110034041030500900030f080202807a01c82c5808220350843c5c8061910755992400300364220303140e1240c1041d00e4201e0f4004141caa811842d59480084a000311410400108040780c1d02902c0540c08880e02034240595080460 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 921294271 1250 921293021 921293041
    0x15130e03280c110f03030a020d0e010201090c1a040e011806090b0105031311030d091d04020604140415031a0a110405210d0c03080708040c05010507020d050105090c2403 74
    0x11103c450010000c0a0848000c4082481c0d40c201e107140e00c0043c1c0c0b010580c0d1420503000340e41540e02074020310083c003006005444003078030903410b0f100381c0b0000781503484942402c180010540c1c0103000d01d18004001942d413159006402528640758010702c0c0c1c5032840006098180784200c0e004040185c50340f81c196038034940c0080354003a03064800d03a000440c100701c460380c0707039400e2145c04100c4c80c0a854981060703042c1503031420000c002800b079030880002d2009220259a8030300035182124280903890803108a4640841d000d00510040c076800031540000c00310070412403826122034610b01d41e00c8a8010341e01c00614005803803151091407840c043c20007044c0201c0c14001020002c00d450502403500b02c0011000c42881c0c5848084201c0014800e4110340080651007281150001d0311460008041e0416881d4040c1c50f8403984155414400f0005c0c1980454444400d1205004c0d0000020005454602c41084c0c55219581800d032084001d0030140c00c1d914841204402e4040201c2071041c1903a903500c0580d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 921295521 1250 921294271 921294293
    0x60e0114010513050928090215030709080d1e02010c0e040b1c0b01170606130e16030803011511060408030717040f0201120c0815130e03280c 62
    0xc8100a43c285070007081a4954014141c01051070b10813200e031445014000040c0d410b01c2003810000345013040110300140c0c6e030f0514404003e0019840f525985d84451100759001201c9520000140c002c040d42c001c031660b0420541c03141e40049031680490311010303090890896242120040120702c4408102c030950805600410007500c01402c01040910030406142401c12042400c44000301d04230700505c401c0054103626000c618400008240ea42001c1000500c0d885c058100c030b0f00031998840c980840340c0800c0241101c0c3c020583e0204901d903450f41000711103603109006008a240840348488852440740d083c5144446420002c0c0440b91150380e1018070076400a071104040212a1311000f80c1035455588850145129200845110441d48005059110190307529007100349401c0011006c1600024802c1e485540e04020500c019141c9001a040d5078035014028032a624001c00b100091800000601d82a8004004010381c042e00e000e80703011191030705000100003040c2001403000141c42c41c00b4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 921296771 1250 921295521 921295537
    0x6061e0e0a0213030f03020c031b1e1e03070b0703020715111c080609160c061b0c0c0b07170d060b0a08040c09230a0207020d0503030901060e01140105 66
    0x1c090f14022a0500101a4501a400655048240801d0300d000c16404100c841f0790440d0507000380c05619010003180c6040d00300c001404d030103003440700c80e540d80d02c0d03084040d00894040004c01e4112100005080c201d41d06024161450103031103002c8011a20b01d11000c107440c45c1c0c3d64541c1c014100c03c0d050202d40851028489054020704c650070080848119052100741c8c43c040d04034400381002e56252030010030014025049901404d0040280407140c0e90506510060302094244980d00b0644c80c60310f5402007406c045000180100760702c01401441c0d0004c80304081c00e00030000d80b011035803515416100742c821040c00915000c0355621404160360910302400c4a403645900c001425036882c1c811000c598042150100050080010081080203000a10300501007408080020b454131a01d041d03425842102d00340901c40c0c401d0005075040c206901207410040c0d01030601c01c41c0001600c0e0282e92504190f03441207443d400d015022404a0720040c02c40e04079070980081415088051006640503400120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 921298021 1250 921296771 921296791
    0x110c0c040906060e010b0d050a0603020a030b190f0b0906060f2205060304080a110c011d0a03021c0209070201050f070804060e1204050f060f0a0503090f010c050706061e0e 75
    0x3100241c4081c0d440404c41c02440050390711036490180f100030f1400c4407001016645454603018090000da150307000d030042035079404604c04e0403a4907525010118502001380241045049c0024026411003079048080c200d041910851025140c1c201040b485e40102802508145c405100080000750019040101188010300889080b519680480c060b50b104480680ba405000104036800300c2d480318008081040500107018201c010307000007006c02c455108010400804102c3c502540d03990507411382c004680c028640520385c103410b04d616030035201760302c070907440340f0322400000c0c2e040c50041c090326200705480400c000300f075990090309488481000d0030030380f000b9584800e03040780e0100c10800560400010b041140d00e031858107040219000c02c48020300d015480901412000b86414010740d41c52125500b49941c5943d00e24980310716000400c0e008681070740c04c0a011959064208004114180c041d45041c00000c0d262000c9032200101a08000f206803400f400421503c1d0a413200e042d00036074003038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 921299271 1250 921298021 921298031
    0x200a03151d0607080412050a08011712070515010f03050a120e060c060610030e0c0d030309051002031b04050f010309261b0c090a09030e1e04110c0c040906 68
    0x10080d1481c042e0116041d4020030032507001e100500c00d2801905100c00080d182503843c010084c000140080d50600c00c40824000180c2c008a011406010048014002ea2842501e1b0542c50600540d511034540306845825010030001c1108071007501c100e010b0380d030848020007007445c096448203100d6444a171240c0c20401d6010401c6002e0340d60030b000384480100d11005041600703103a41000448104032080790289450100b58103071060000c22481081e050445042c4948251802d05074013400c031880c001451401014a0741c035040b00b0550140d8020317014030000c0c505842807408552460300c210f004596101010010a560542c400d8002e03191452003540c20144413940034000c00103d401c03d003040c00d040c41c0c0102e902035047c2d101d4200c80c0c91500c1c01074000e1803011111000304010f9500a04100304154079890130fa01810300816081d841c200000c0c110850b4a16114010801d400c001380145210b241006c650001440d000800e8603072000407000905034218480b81000010200c0700030840e05940c0320 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 921300521 1250 921299271 921299321
    0x140d140103050d031103060a030f020d0b041b05040b09061011030d06090e0a171b0706090303030e060106082208040603140a0c050714031204200a0315 66
    0x16004860095202d600100707400750380d07500c024040d5645040c90f084102018001c0061561392121072800701d03500900c640040c810540003040085203240400f500050b4508103000400030707408610f03030710f1481102c44003401580f00c0e010807040d91041340c2e2840d441201d40b001706056107007000441d04020100d040100c14803c110030080d0841d0008210121aa03541b901c04000f10380f858003e00f500381c2d40c81e20280079800c00b150366400d4421907140101e0001000402c0e104441c036075014a650f20a00c0070000c0340c04003942da0074000c00c8003625000807800603013400107026003c580082c006040e10801d4480c5085941c0311503900d08260038006200113400c401141000104035400014406403585540105032070701810002224254007400c6a1216441c2c034403101c08850703100080d2000039038049000043d0302c1000010900c0d5000d114044101d45501600b0b120070001600c1e40310940c0c602400e0100c018076550410420f28400612018100c081c125088a0b0450226030007814800d00d115882c3e0038150315 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 921301771 1250 921300521 921300551
    0x3040803071b08090a12020310090510240b0a020d1b080c060a110708040b180301052701140a090201020708190203011103070c0f020123070c0e0601140d 67
    0x80842a00c1c40c80c00080c1000c4c007070600206080252914049003501070110764080b95846072403600701c121455854600d03004105061101c0b0700c000d061000244256514040000300140c500075841c5540f001269000030b81c2c0e2050f40039200c04400790707000b0f0040080c0d400d1702504d1515089040049425000e14003000155006001e07088085a0a004160783c2c52300411441c100d45002e00101c641d46802d000034000900c02c0012107040e220815221520f40c2c4152a031070700b482c4042c0030500c0c0d055013000c04020b80c01490704103081803030350544d4110401c0135500d0001400c0f00c05071010942030030215070010f007408103540c00459400d881031040700c2e07140341d80300111400e00206c06d6219590707426200841080d4a000d0080f2442c2c20120030207540345060280d000350000c0f400040042c60200080d0884084da07004030003c054130a182d888480381501c2c0b0108144c22580601412510080c07132050104034040c40d0515180704180c103031106003090210102201840e0080c4981c00101a00c50743d0744040c82d44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 921303021 1250 921301771 921301817
    0x2061b0d020d15050f06071e02120604050d0813020d0c080d090614040506160204200d050a0501030308240402130513141f090c090e010602030a050304080307 69
    0x601800a921105660f180c030300d408940d48164441c401d00c00c0941d00903030390101203411140c0c0c441e40c20114090300551300c0c0c006516034000070f5130124902e84010b02c40d800c003081d058800d51003201503524401c62420240c4400f40151100d90149240d04072140060a00c51a8589103500074403041d5030041c0da032200503141010b03103020b55000034010002084420b4100c2c911034601c801b80c660b05400c1c241807101090b07680c000e10303030240101031414400c9029904d840d40024442c0c81208025520b0020401180500b6440010000091031604001810400d1396114142c1a0380d8550f580a5007a100c100401908403000383d8140000c50050000c0c100c565124401410011545080100080e1406040125034040c0d620904000f500b00b61140e191320100350b50b207d52080c8501420300780074460b000c91450032070316500280300d1149444414080c09402915020407035000950014207681c0301c41d01280c99015810b15a00841ca041c130204000a80d40d00140d0340c420a507141a50b221101a110014200c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 921304271 1250 921303021 921303037
    0x30b0f0405151011120a05210106110a020f010305250906090e25030603150501080d110d08060d02031501170f07050402031b04080c0108150102061b0d02 67
    0x18402505103191400c051140e660f4200141c01c03c02031602100001603120002184c030707810710f840000754241d4000e000d1020f4403008135403444038104540b50a4810301d09a0303428050f03c4040389990074035460b2a9000508141d02c1903000d0b041c0c402d1203060302c00540141601400c2c1401c1c280d8106040c1d909441c28041d50300e44c0550301e580e816641882d002018013800f8268104481600c02d220400c80102d1020742080d0801183c1c50f210a04d1000d8010200c0082409800003801441d07000c1070056042000c0c1c10160580c0e400300243c518100550405440c0301c0d015012a140d90f42054102c80b090b0360090b10301c80d82c4020f0141c202070814074194006401c0c0000b40c0c00c020202e00380ca100602910074042d8101c9251002c40c4003c203c0f4080800c0b200b55120285c0c42254440d640010015683d0421304484072040704000c0315568550342c481499035150750b40004c0950008140e4000207030b0380700d5094903030810a181a0060002c9440d001100d00c0344820040030440c0480302000130000240241c40149103034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 921305521 1250 921304271 921304291
    0x703110616080a14060f040213080303010f06050301051c0503070c080102030906060a0f0e092e0b0306010506180103140a0603050c031606110f07060c111f030b0f0405 73
    0x12280290203080250042c00c1e9060340c034a01141c9003402e03001640c0417500564121606542c011040340001e0103071107484440800318944520000b100322001000d0350580e01e0342c1d182c0010300c80c0c0701c0004032441c0c0024811150b000050402c0c0d0113102c6082a600c1c4403260088007507070301d0b0030410385807640c03d24240c0d40500c2e0fa5039400010049128000d00045420010031203510750703c03500e003452180c4040001d00a44808007200004184401001c20280c0d00b014aa100b4071089003504200c5c0b0002a0551719850300349608020302e04c21a4030700030924605075040281114140b00b41042496010b0000c0c007900f50500d565510a420510100c02800b44214101100880c91909500e00581006a480403442c040e5108010810b158070b004100641030710424940185000f200d01d1903d441d10455070380f81c4405025a0101250681d03019040d004107500405440c45d2039840b442c140304148001c82c1803000b0781035101311302c040c00754440c0d00b14201d4108001c05560800c0070034000202100c0702645c201107a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 921306771 1250 921305521 921305551
    0x1030b0403110115060315150e03061008100f090c27140c0703202413081606050a02070302120a0203190917010605010e101407031106 59
    0x806038000080b000368201d2100a000405001d158000c1c0b80c8250300501042c1a00c03240031954004000300d4000040800c15023203030300c60764a12000382610500184050082c003078200015450b09250184404482c50480100b541066049405d40101030f02da0880e04043d0b180c1441001003411200c8213800760080241030b8160805c10840100415074118000c1e210600700742201c824801d01c803841903070041c8d00070742c41a80d0b9001c2c0e140486400c1901212000300e030a0226403084041c0340001d400f60355203081000c00488440d00820720405000882d0000400baa81c101440000790381800502528210b070b0b0340c404480c441690300e0341c090f550121420008181d000c107a200c20703d81e0401c1910069040409114074081010746c000703440344140c500346402e0100e030090308464203100e0103404006083d01d040c811b6104140e401c6560103014544119400640515029001c0785041203c4070554030715a00c8200c4400c2141703a1040c3c01e40c01070074040e405d0112640803094403440601000348240c6002d410170075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 921308021 1250 921306771 921306773
    0x15010b131d0709080a020325030b0a0203060301050a06030503090112180807120f080f07021e100516090e09011508060f1023030c03010f141e010b0309030409020301030b04 75
    0x100103c030381d0f407200321035030b012503407140142e103000c26050110450a51000002d014440e070f4035410030703076642c401032104048508005511545501850199408034020b0299840707011a0400b0f03248079000150454004202c0316440358043c0d0703050111941c0010b0302088074044c801000300c51403002101030b00c0e00200001d210003044a41c91400040b1707140340c00c0040340e0508540e001441180c000342141009040b40000c2240c050003040154200342e2a07142001e500e032204d071a8240c075000441c601d100c40305d042c2004201d04c04421035089034180c0081e600c002c0103074640581148542c6024000079890b568801100d10700f0180745d078422001d8402440201400d0070705000c0e2000040c0000c1c201c50300c141c51007c0174800007200300d5511000210303900c0e520240d0b03000e0400080c00c21810302d000c5a499864400154040da0301900064424410f0588490841e5110f01e0425003171b0f046840da403484020300000620142288001641c2c00840e420126418984c41d02c4080301241c6c401c0e00141c94815401c01004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 921309271 1250 921308021 921308027
    0x106020703060e030c030406050c0a39031101050a09051f120c0509040b04021209160509101707080a0312240306180501020d0207110315010b131d07 65
    0x14040d1103a0000071352030300f1a41c03a8030302e0f102e004500440c4104000040c8854012800300681c051840e04000034908031041075064020036980701c084c000b5003000405e9058500442e15103c40102ca4020f6031460f0914400401150076070710202006003070040101003c5095104d100c202105c4140c20701c0c0d00d032441801544082e000d60f04626101520300d0400c40c86c03c00e110340c4001a07070b51950f000d54001c6658038103c000a40607004160041010400500030000301850018400307503100c0c6880c171000d107500d481300184007401004985040c800c0c1900c03542004046041c186480f404c42030707a41901d038040d031264200340c100140d01034194006400214070810040807417140038186804423043d0408905010b99022503140288006401c65a40d9803079400040c00d040c0a882815903c00002c40d920000c400b4010025000725074252000203107061000450b0400050089a00c0c03a9242e00d40280d80c41c02140300c0c8107921011034019410048240054800110400103640612035031884004c2d10b4052402 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 921310521 1250 921309271 921309281
    0xf010e18100e190c030b0415020309070f060c0201080c030a2a021923030c032808090a11010c140d111b01181a071502030c0f030403030b0306010602070306 68
    0x1a2041d02d05644401e00080c244c03070000812a503100601305115a81c900b061980d50b0000b00c1100320090001040102d072a50220750b00d0152a0701c3d4a00c01240354486e0b004680501407128000d010440202c003060440304420080c541c000d9402c68041030040514518040610045880d0801c0041407000800c40a07014800c414001c5502e8168076a03c054036100c0031101001c5609459501c9903584500d10100c0342070040700c0c01c110001080740d54480c104007220340c07a0361141d180065005001c0c1e0400b94058494100304d4090300001000303000225480d11043d6441d080384100320305001700c2c843c3c03130310001c1c0c109071000c101d0b0003004018100480980300068481f041e00c1021004a421008004ea21001941c4102d101b2040030f04e000015200016029407181030701750030031543c54200300ba6070828480008001d09485208054201e9811495410341007603000a031514195030409101845c061380303480002c0d40e0300c18064503020a0442200012904114003038001e04010b0300b05034070a2007408068028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 921311771 1250 921310521 921310543
    0xa05031c0f05270a02060a1d03031303080a0c0609151a030714030f060a0501150906020a111c05100b0306010302150304050f1005070e010203030f010e18100e 69
    0x1030102d403910880201c1e058490950040004100840560103102d0800c000c5604540c003520300c40e9105035048016120903160707c40304a0290aa200b0264581008401d403806c2c903880011400903941180e4031161590804d40e010001c201d04020700d40c000c0b4a80c0d00580b06103070300a403030440c80c0110030001442504e41401d55111003400c80d5030035508680f40007230004111800c403c1d0524402c0d510700b00090a002080d02e000340f071131088505000240c6595809a8101c441401040324820071200054540c580f031813044c000980c010440d1100410410456454110070082502e80302840b112aa1603043d00d00402c1038030030303a029081a8100700d0092040c54150070301140100390540c5194001684008010404100302d1300100100342045002c205017064a16131006458450b1004c1c0c5041000702401c460741d43c00034000d0b4403900f40650010085a008020420365040d40340c2c01d10244044504018140c80031038181000081600380003803044c082c0c182040540890325601c1802014540662410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 921313021 1250 921311771 921311801
    0x417071b05060a170c0403150507020f060c0a03050a0b060a020f0c0d02060729150109240c02030c1201150801050601020a030809010603170c010c09050609040e0a05031c 74
    0x8283d80c0c00641000c00d40111070841511944c800c8003100c2d15020320790008100c540b100f02800f40c24032103034010340e1041e05503500321221048540d050558903103043d5080d030032202c0204040325110744a5041581d002042c0c0c0c9000c54406103c0c2d003c980c0399444400c00d18016000140c01c40c584040602440c2e1003802c3c03c42d01c0010309245600003d03207078455078000500500101d625a03004840705805900e0014094140c48043d143c6400d4002c04d008401207418001402d1043c0403810443c025200b14902c20400b00a01c60202803540985500d40500707130582e0325206000b419400c80ea1000c0300303244980605400800c16403000403031051811444d8125081990501080104690780060441c42c060b404d03141c49030841e152007024034014000b0703400c083c00400b5603e00700d81e04e80ba42070700148103994130040208440102408115140ca22a0144a91043d400c000000451034540c03c1401a003c0c0d46007920100750b41e6a44662541d40b082c12403032000c8209200740d00741c1c42500c2c40381c00d80d403c031000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 921314271 1250 921313021 921313027
    0x33203040c051207140a0f03050601090b030607172e0e1015212d060e010614040e0a0b030d0e03031204060905010c05030619050603010e0417071b0506 66
    0x8400103881c4c131030f2801800044c80030703801c0902c6a41d4074a507500d001488902603294000d030b102d0600a44a400c01d0082092460400300c4014041c2000110b513407042e03c980e1799207500c0c0e040c0d000e40004080400f41c80c010121812189048088103401c00c0320ba4910001d030300c5014460f141144801c0381510047c141a848403030613100304100b81d02d8038000c0c04005e800b45415881e202601680154240c002c052100240d0301d00f404034040003504030b00600e030355416000344189100fa8404502c0c1654064010120400c10391001007150602550504000503100039402d8105901c60032001e007080421144a05260745038440d08032141014050300710001e03440d2401450f018480750112341e80c0c0c40361140c80e41310003101500040c04d0140075842110100c0d07021000f07000300b05000038001c141d9041547c045118101d090440160314807468a964120350018020b11b08503840c008070303000350040042051b07540d03044500400540c2e081440003810094401c01030002c100440795003100007138189400103030080d0010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 921315521 1250 921314271 921314299
    0x50a0f0605090921040b0c0106050405010902031003030e040212090d08130803010501050706180b040c0f080c09040c12030207030c151d03010b0303070b0108100501030b04033203040c05 81
    0x860f113844036100010244074401414000d204461095038041210710402180700c0e034071030a041d0801c0c8116102120f05200d41d0740c071401484100e10090b5181e0340070000d0841c040002078043c0d0b0074004c11050041005050101d10510140060400ca441e010103402c0070495800d859000107100380c1081240d241100f103450503075503e095500c018022036050050205000b020004180c10590118180c801145441017440c03a080900d107405aa046604020380f00d004106d400240040e403044840100041c180c0744500d20070f00102044c085c4c802c1d182c5201c020004500c2e03003003024003540380f28442d81c02404e0951031070174180d408152603002000350041484803540610782c480d00303640b2043d100d141c0328403048402c0e00010740180108490190140008a0700e034040c0605c8031035a030b048800003402d803450001186014000c54009006c01084002c1200c04a03011a11070340300d1225110042c480c030360031105000301c2819041c11810f00900c429400004000401034041d0a03074000703000654100508608c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 921316771 1250 921315521 921315523
    0x6020109081206190b030702071a07060f11032703180918011815020c03030f040807150b1002010e03030a0c090b0a02030c150103030e0d060f050a0f06050909 69
    0x44940401c0b03965070000c00309506960380b0107000103501e0300d408243c441c1c564a910002c003982080f10414054051540c0010714805d002c00700d0400f41c880290f503249040420380c2e032040140583e403010b40800d0307901c404251039031038003500031406810b40700391206456814114000f45038146203008100758005000080c008105010b88159141b000c59154200d43d6503510b80c1e044107425541518210341c01d201c6981e4007162403400c0f015001e40280c10803035505007860483d80c241c8c820b4404990155004100285498556440d05a000b5200d10740c0c03585098100d031608140b2030740300105950307080e944200054042c0313003e80c2c170510080301500080c0614084040000d444c0e000080102c1001502c58003058120351244054201902c403180c00d1580752940004020f42e40e0300104604181031045c9209012858050388000c0c0c1241c1c0d050b542c45c021080a003051054454451008561440c0c590401c4000316503075005a40c1b007500160000115000e40c0320641c4140c4050b540300a015030b2402050000440c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 921318021 1250 921316771 921316777
    0xc0e010f0f0e090a0f0308010f0b03240102031306030b1201141504020904050f0a1d07030204150b0307080f10061707090506030405070e0604020405180415090614010602010908 77
    0x128070110350350b079940e6540b5907908015039504000c01042540a4404c20980c0164500381a190b480403500c40142c2c69450300c41951005a481101e080c01c078848102c5503405001c0e2280c146501071042d00d0500c8000100c0c0d8541d552140c0201e0042510348840756a1400c10340d018045001100d8001d1215100d4503c0082050a0191070040000e811103050526034482c1e40407901079610281c020402441c000903600c40c0510700341e90480c2e85605280c0c280e840442441641c20000401d0070107010f142d403a603400c01005080400701d4040303c0d050200300141807112000910b02c2440c55072a42d007440e1601030881c1c055020018100c403403040d51082c00f40074490344101500380160080da0260160b0310780d414156138103011039000716801100081003008101003c520a0100d410700c00c4403940a0f1546400c01060f4003030780c02144d800510000b02c031060080f4000c00a50454010b58050f20480400a50390701591041c00d42518081d4642540011300307507401c6c01d1140140520f200030010f00442c0d94519020388 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 921319271 1250 921318021 921318029
    0xe010c03230c0910030e1203060a150201060e0c07060b12030d0e011107050a03020c040b1008070e1c0308060411040302060d110307080420031018020303070c0e010f0f 73
    0x40840c0c00040703125181d0b40c1110300b4401d0040c44407603400c14540c0000e000e440741c0e0007444503d01410f40c1c1c2d005a40d2005055a0045200031310410400e8186050440e0041d03c1b120203c0440d13480d40c0380003408103120201140200074032046170703603104d505081c00c1096580864119004e0303032504540d5080c0d150044103482800d101080041810111124854058413410144145061001a108017088030015505840501c40d800f81c503e4800c2c000308110443c0ca030a81c007150401044e80106d0221131155015542c814024244420b07400c5009002c900c00c0700b0003040c0215001640c650070800c1c182c2100302c2c9548014102e40600c05401507a00c00c0c1c2c01405a840000d02900e03011070b010364100c0c8150010084c281c81d04001c10307201e1034000401418030344256015900c1404003e13001d02e44c2001300741268050880940100808186803100000902d01202402e0551088261003001030360148010200b4900459100d00030a01301480403e003240181e204c41c0f07000d009020100020b15030b503c1c20004807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 921320521 1250 921319271 921319331
    0x1009210c14060f0a0201150b04030816060f0504050606190b091005160b0612011a091e09100b0102071203081e0a1b0203070818030a150e010c03 63
    0x824541008180e039805501c030800340818000c1354680b400c4e07505503c065411051255050740241d91121052054800ea01029104803030402005009141c0350308141c3e80307103110b07030400200c4994018174002200e006443c00c480540004080c000c00e40b52484402050200a14188580314605074a644d8288104c02d002e0380a82136400300d490007240104243d6083e800c03402d1601c0150502403928070500a81180c080d4458014000740da610340805100760f03081403a89820400c94000c3c0703c1c0030802c3d1003100414540d8611040032131080040c01c8440600d0145201d00001c2030300018403164501510380030b402076411035000300c03400c1083c846920a2240103a400d82411611900c42c10201055442508590303800381c00001c00b80b08403281c580c2c1c030561985444064490400000b880103c0c0c0702d228400000e441200c0a00140b2620112081040c0c540781c40201165040a1956a400b034481d0892100b071100075910030080c00c0d0040280201e1914040601c1c0070000030b900640500030403d9480700c01040c2c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 921321771 1250 921320521 921320549
    0xc141314030a080c0c0a21031d180a051f03061a1002030a03110307050702062a030c0705030a0305030f13140a021311120c07021009210c 60
    0x400e880602c2a0601c240d00000c1882d643d80c01d1048907540c540100921600070041480c001980d00303008502e40c16400e41100c0c05090700b07103254030103c0c0d116500c00c0f500c02d0a983c60755400f014907513685064400009100c0e1110304d0515004200004075900141213001e01540300e01d81000e41e21a940c00341c0e0960703a104000160300b51880000d418039243e046407564100c51034485451800e030b000406800700780c55940c0d041c01b041d20704c580b0580083c04151042404030300c0500c586401484d0034806040c0c800c003400b06420302081030208004030300385101800807054000040e18000150288064400760405900601c03941a080c1e800408900c40284104098042980842c000c1240841400c1500c1c0d0040d00040c64202c034002525180e01214508900c035616480540440112034050410b40d0f002c00c04859041550024a20f01c29060050162060100400c00c043c01030713036207201c5200c0300242c86c0d503045c62140c280740c00514a2075544415081403460301c48480001043c0400300000e0342c851f21000c0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 921323021 1250 921321771 921321809
    0x10e010c0501020705070b030f100602060a0e2d0708070e06010c47090a06150f32030c12070b0f0c06060a0f0302010503041a04060c1413 60
    0x10080c000c141000300f45d4003507090b00281515415010b0344c05104e001000d940c41d40c41725000d01a038010071707104060140e0005000128446560361140940071084000e41e0149542200380002000c0504410812902e10400308282410108404005010a03d00030b0600310b0134041c5c0c13400c158400502e003904000c0100984010884810005071541e9a8078405064400c405c9500894441030142310f059a60300319402a1000d82c2c10b0025140202c03c5000030b02456413070744c2c40781c8015103104040b1a041d142c0300c1000007842c0038800e80d000024220041c41078000c6086040b0300c0b46082520001c54103c07055014420a99900891040700030581201c102004e5400003515a0070110b06601103c403a1501244000a00b41090b0040c00c910320441d050310f0059640c40100000480680581a14241482414001075004400640e04940640c0e0b500a034442001507680c04c0b501e040300c0032281d40341c588802543e01c0d0b070811085ca12898101c44e0b030780c1c14400c010818a100780250302c0741221407115158495 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 921324271 1250 921323021 921323023
    0xc0e010b0d1a030a0510240902030403030b06040315061d1302010e060a05090f0d15020d0b04020724110f1e030702060121080a1d13060501030e0c010e010c05 69
    0x400c1070b5202400b40c845140350b606165031620000307010152003500303290310081503403503540e0781020098502e40035800050511440e07100a40000b0402c4085c0b541d0b842c42411641d43d40740c06400158405e90000c164101f190a0710f4099582e198800d500c4c440610300c04800c0c04000b04036099000d902c03c81040c4107492640012241c40c412812025084030b800a01200859440401441032780010758a0319080c0c80a00b0a100802d03885200103001c051500c245800804030b540c0040010000a210100b44a80040001341c103d91101000721000c1d4001140c0040f0706007a480a8403403020624801c010b40ca003100c00a641b40d201c0d1050798105400001050000604420b1180ad20004082c81c0d0640700c3c41c1020001e9590002805800440c4194102ca0b15500c49640c0c81c4500040e48203c0450400d0b9400c00244c81a0798051220142400c000590351b40c162210342d81c108000b040500082020b601d4900007404407070b04003880c20324a07001711049040c0b40e6009030451541107001e18107070300031b0a0541001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 921325521 1250 921324271 921324311
    0x1203090f0c0a030311151e0c070201020d271d09070311060f070606150207081b01030513020907020102090f01030204030206090d0c0306020301060306060f03090f08030a02130b070c0e010b0d 83
    0x1220001b04005118582000720b200ea00c0c03080d440c06001280e03440d24100c0c1e00c8503001e21a0001c3c01070340700c3c81805501520a1280c0760056180d583c0c06074009086921240e02d9020507005000c40a0150522240000701104842d0f0800c080c14098807515046840742c907810080941c503139000d000001030b91011030300b03c581140c1030103402020402a1940758200b0341a89800c00c40a5001881911004100303140040380c0c03540f2a60036200c0c04000d280c4800019400380c100205401e19071415481c0362005611000c13030185c82203c1940c00180e0f10700c0e641c030400140e000c2c04980c3c5810144103000c21300040c0c40e000d04581c01c0d0340301200d404542d0000e0b450034100d00d4903180c0000740001c0c000f200005502c0e405030000426503180b070b203c010507042d50013021400c40300b01c040083e25a014501400d000b0400c40d2000b150419580e07500075141040a5101c00600040355100c802240e40000350382c0144040226844090500700c02284881d500d4101180312a0081e15100750000e0f81e103005440c03860301c42c100341d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 921326771 1250 921325521 921325543
    0x80f041208070e040f0c09050306010e041509152903060109110408030a0f0e010309110904051e1501080115060302030705190f0e0405070906031503051203090f0c0a030311 75
    0x505c0012000b082c18000b40681c41e40000205102c00c201180398a004a8524184ca40c2d103801c0d034038141e407140c81e0380c8446005514900d441965070041400850b042c02d019001c0f512000700c01040e2640c040340501c55204d41c070341171a038400035007911203205950007140e06411900f4044012803c81206081d0000740c0c81250b20000603880002640740c00a134028620f4000020bd50301c80824020300a00150192010b00400a01d080a01c0303442800c00d04c1c010505540090165041f9262440c0d29840d03180175400944200c003c1e58000520806003044070000f80340900350242c000c0c8003050500c0424a00103555000e01001c2c1038000c0005010148144240d640c032711000101e44506a01d800c8010f440c030365102014074000707140d000740c80d00c0a007003500656015100b503a6481000900c0c0003030450080140c800c03c58800b02d40300e4030000200d0410481356110541c1c101801d50b581c10441c4c14545840c07a8106184401d17007050350b4501d0300396a14010401280e805080003a8000420040b1504040d10240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 921328021 1250 921326771 921326779
    0x5120901060b0c070e060102060103020a0e04150f0905060105040e03030403260708160906020718090b041112060103050a080d09050708070501020c010c021c08040e04030c03080f041208070e 83
    0x1e4160314242000804000311800408400d100b506d6610049860700c2003401702a4000c401800d040120400000006501c50300803111380d0181c0d03042c01040c0068410a040000c400c0d622044030105001c0d05104c01401003d044030100000d003030848410b0b07164000100054184010744500c0c0c04465000109412070090211449185240044000e080c8980545181e0204c4160280b0105441e0140c5820410380782d2a40003011681c4c41c201d000c2c40020444c822070254240c03150040e20015000c80d403071900072849182802c058412220600c0b45102c0c1c61030b5001881e920410042011841c082074448080307030000801d550320240424410301404110030b004145110301c2c00005004000411a0746c20f9078001d82c01d40c0d8084040a004640c00d411030700001c1d510402e0111103c103c04400021860b00302d00c10103055080a90f0b9a55035145e1220440d010b60100da50000c941c01015409110f10b03074002450080b0b1343d0380b802e00d40c44600b601101c0802c50401d03c00702d40302044140e40200b0141c040024024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 921329271 1250 921328021 921328027
    0xf0607060207080d06210615050d0b01032a062a110a1a031306060b07291302010c1b0303050903010f1107060f0902060f071106040605120901060b 64
    0x210b4983c220741c1c0240c0c06003074858603150300442c072103c1d500e180e900b031099100c42e034030625a82901d824005002d0020341a40466410310b00240310b4680c5040014214010b000c018410740c5542404601a450002c02d00f00128500c40001c0f218400d0340000c0050b61030f0381c42c0045004c070680c0d410090840f00c00054000d541d03401041c0c641000f1201030307441503041041d21384c0e000b075541d00d0450a246000c0c40081100900003400020101c0380300c244405c0300280103001c04100c60740c1c2d03855000031030352249e134060340c0c2da2012103107502016070f10005c2e504a210012120188514110000700f240740002e0380000d0411240c2d0301000140804c220a5584082c002440c2d0341c40c4035078134a400382c8258082d084042c000d500388105080c401950384601400c0c5022020b2051905059030b07a01001070011100e040034056a6010420140e2594805450b8516586007400d560b01400d04006042c540d0070700059108010400041c41602e50000c15170349404907074400c40c455a125001524007420060700a480743c10008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 921330521 1250 921329271 921329273
    0x1c0c02060c0c011d0d03030e030f0f0a03060506070c180b06040803040602010e19120908030a030911040510090e0a0b09032d1b010b0d030201060602070b03150f0607060207 75
    0xb061244918109032181c4014180d8581120101022003401a50208080107120086802500301d100c40740301e100190b074070701007902600c80c08907045907020619045000c03501c445451b03014420b48001d84002c4038610f0a00d203896549640c940c206001da03000561600b000740c69400038641000500c184004d0001c0e0700c1c1c40d11640440d940c1d07041445014010340c2446828116a01d000c9030403040d25840441c0600c40d400075817105061401c80c0400f007800c0050740000042c0c0c0341000c0c4050480e01c00282c1d4042482d80650401036600080d03014030f06c2c400c0380f5220500940240400c55240ac885412801007058488106c00f60f080070084600a04030b00403500c10480c1c892008001401441d500311210020280304c02ca0910b818141601c00e102442d108101d1041c0349140300108030010b803003120000c50204940c0f07020402c0e908140c58202d025039152103041c0a03c0760188050750260009403119415882c0181901c2440c0c9058460240600c44092a503030003600c80780704884407a07803c1740040d9910106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 921331771 1250 921330521 921330523
    0x3071403070c090c030b010c0b0a2013172b0207030611131703120a060312020d1d03031602120d1106060d11090a1523010807021c0c02060c 61
    0x20010800240b070003411400c00d48c02895081c05e01c40c2c00c800f001c103296907680c82d800c00508540c845030540210818090207484c00c050000c0c04100b030614500c400d19458420036120072a00280b107103c89030821104943c1461800c0710314003826000d01740c901c007660b035034900c1a400c02da02500050f03d03807414505140620550400200400c814203000c0b031a00981e104480d00d12649212000280c5800c1008580d6842c0003a01d8002c3c1c006611103000030314645e80c1d80d108288100240805005608090b4500010980040781c43da4144412021541003130650ba0001e40c41c1c1c8a0060120000d079002a580403e40d200c0303042000e0030303600100071226802e801e508090000380c40349084031220321582e40002c0729800c01b004210f48140c3e10080c5c8080e880d0b4004104028800014160480d1550300d469000c0301011b0045140e00034900c91140421901c1d201840b100341802c080c80e8181400028414001315aa0010340d4001440c41d000300e40d2171016030041c1c103c0d11030401040296001001003203800e80000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 921333021 1250 921331771 921331781
    0x40f14090108010e06010b1c09062013120c0b030709030c050105070c0302040e100c11060609060609010f3b09040c350c030f0303010803071403070c09 66
    0x1140e041269a9940c2195030a0304c115110180c500c0d0480c1004000d0310b980100600000107030680124a5110804030301d400312030312610306607889030700e44240306049080300920442d495200b4500501c1e0003031131384400312103107510f00c40c8815001061000905202c001d140503005072020b0b50101d681d901780450002c2508065020644004211060000721980100c040307442d01e652001d480d54400313145400b000002c2c03814418034140e034001d0fa40942d00c81030f554401d44401d0103043e00c4008524141c0c80703210740f074100c0047c41d450044804100f8422150f90796419506140c009103000c0d107407299810350482d03452041c070314620f20b90003c039000c2400285081c04a0041c001000088a20801000d010040c1c0400c0a0310060b04134030151405105440448601c502c21f24004c040b0703c044001480d0030b40c0714070000300388400119008820185214a41401540d03c4082444021419075051182664a174858003c0c000e11902000c492500340e01410310903604110780200004298550700d00344940944 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 921334271 1250 921333021 921333059
    0x210f0f0b04051506390d02120309100e16151403041104052d010504240308090a1a0d150b2d0a120c021212040317010803041a0a02030a0f05040f 63
    0x800fa003181e948e000410241900c0c809e40d1b42078014103184846001610081ca182c80740d2005600995000c40000082407046000170440800801c00280c3c0a12000345503c0c0201035002540740c0c10018003000c42c510401c1080440000c4070002080c0d00c484240c1c0203040001080d41c1294003284c02c1604e4803800003c99641218415a410b000105040c0d901160407541c40e103035655000c040e81018004181c5a8000d041820006040440441d445001c00142e010b4100f44800c0718100000c0d0408040da000e00455a41c002c00e04141d50115060203010b1500340200b02d443e40ea060b00d461000e141d258800c01c5410300c400c0ca078000c000c1d6a1890180c000305640c510201200d100c0303081400711401d4034400075500320a04480c0702c1e11400d00a031100030304290310340900203908106031051b540c0d6900314070b603060b54001c00303d2038001c55031103103000311414000c00d8030300450381c08003002c1c89256003264020089440c6441c8030700c0d1900c060901108281d41c1c60045030405d20b4240c03a0448049068035507402214560 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 921335521 1250 921334271 921334273
    0x910030c0212040806042a090f0e070302060f0c100203040302010504021f120515060c0318010807090b0d06030501051501021c210f0f0b04051506390d02 67
    0x5400b02282e140c010b2140e8454510702e5805480000e01080341b041d80c80004141c80d00480c1d4600f44210280301e10102c40b90085489a5656002a2074011803840360a0030408000e01401089155400003141401102e0141003031420009000c038040c503080c0a02004609a014115100c0c281420b00074000c050446089004086580200c0880480314181c0701d00d0b0034a80c0c7c0c5040441488032240c1c8098140581013014500184070007111550700c400242044208000055843e030303141c00b142000108a860309141444820f00c1400345540e4849104810707038a04185240d40c0c3d15807809480010180c07540b014000d54608070501c038405910300b00811019009a08030b40103041504481c8840201030488000403c14081d03d00740c00709504010141840c55040c000241d05400c40c0442d802d41e0444000580312641e15805500c0ca440c041c410f00303400030002c1d54103880054074240400d0300d0b4801c5800f2112003030345421045003511480482e400b2401c0b10320103000000303da0b10208a41e205001c20114000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 921336771 1250 921335521 921335533
    0x1101060909151401090f060302031c0801060f0804060209030c0a710105010312050703140d020f0d020702010201230a0b0d0203010c080601260c0a050910030c02 70
    0x807661900035024240c20342c051020260b440c1c410858000c2c400d44d01d81c0c6c142c2c3c42c5c4900b00040581c0e4184034841007409021600324080d1900c02000f403045005800c024280520b284600300d01a512105299109030700400040c2e54001d014000f902e081380074058a07910109100c404204204c5078101489030b84103002c211141d0b02d00d480010304101105150148003406c844045198440c03903111024000c842c2c070217003030314100c180309906032000c0307410022554503039124030040080108803000c1031141c0b031413407a045042c40300c7c42c1c1c3c0051051002200840081a0116004031030314013541c11140d0740f4500f0305545a0b0340c03040c660008084d40010600341e015518100111600340040d4030450300d80650015122010755511001c07000030308a0316031060700300703800315080c1c40140c900344039034814110203449010302c1e031411400040000303c2241c11b45480703a00c080c5640800a9400710308540204212000342c0e22018618000c459600410030585d500c07144d20700c045802e0542640c4612000d9000d030342a110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 921338021 1250 921336771 921336803
    0xf0a2d0b06120c1b030f070c060906080a1a031e100603080f401a18060c12030403080a0203010e0112060b04020315090907150804031101060909 63
    0x42030141000400b03900403a00005481108541c00a291986a005041c003501480c10910751a58001100304905140000b03152018000702d080c031000145550700e000302c4254242000204175400c0548801c5d019034031041c3c44460840c3d90380d641349001801a04030341000c1050516904103140d5540280240e000309284445522183c1c00340c101603d4011581074030b42202040301c001103a10485504400e40c6002c403501c1c0b980481522207022003140700500048180302c180604e03040100e540d200d0f80340260310400c600c0c900840f11003582d02c0d01180103410b610010146000c40c02501c141910300103a0f02404041081c0d0b5443c0b20043e42c000c41c02036542c0a01c40d60f4a8000c0750413031200b8020040803d0b04000100145072524100006140c03280300e000c62155505004503040c1d030020381d4803030041003840000095034148803003843ea009558100a107003042c60000c04607003104e103102d0301d0380c10400d00300d0008003410b00651140071032841150080141d00c3d07a0b56002d40041c8031122045805440b00d001c1c0355 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 921339271 1250 921338021 921338029
    0x4030b0901021e0a170a1406101d04200c06090304232e0e0126070c15050a0c030b010e060a0c0803010e0106110a05060f0a2d0b 56
    0x10502e00b40f0484881440400d100d614200707800c40304018003001a001441c0b56404c07105948140685044900455040c1c0d240c1c1b50480d400340300629050080720b03141e40d100c10203584500e04600d000101503122000e00440004503002d05001e02c1c1e40480340c4104864101d4200c0c0000c02400781c0103141c0b080e100749884d102070403a140d01c40d074413600406030380c1c0000f4221507000c40c0e01042050341000b040d504103c0a9212000040008002055140d0765421010750415400c00c21550408001346071054071b000942024402040d6401c00c1071007444007900c00150201d009102031041190007448031048102681c8003130f030203820119861403000341001c0da0400f00070702134011034401440503142c0d246240b403e88203001050300014841130800203003103912008030b100400198081c151508020a4075810081e0160121000d00c0a03039070710b40d01c0a0030240110340701040c6c03079030090401100c1c84c00c26201c084090001e42002448a100718802222a8501480f01d21501c209100c141c441030002c1c4240e00200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 921340521 1250 921339271 921339277
    0x503031006140a050d020427050601050f190c1a15090c0a120b0a03080408010c050304051009080910020a0c06320d05070f12230907170304030b090102 66
    0x710380442c000b4042003580e10701900c082c03c401d0b0700c21032006003400d9030b41000840c40314100824041000b01615140251201400703910f40c099000e0922a18010b4003440c02202e601c29900045205141001c103003299510900c0406800340d0803c0342c40366603c0303198005020540c016544084100070b020710004107410f25907800d034842c0c140c2c081d400e401c029010000b1758120817008103000400e66196a424004d54900b1140070242d80500301c15038840341401d03c40e41c2110428000c1400340a002e004000000780d000800c441076a10b002c101040c07031601481e000e510f90180c0708040383d01481c41030f04442440c1c0c1c00121403514900880d81c0701641036880340d041c0c0368403000c215400c08911000300e801c0d0310380c404091130102d880c52805c4030520b41420340e8a01c0702150000e0708d105000503203000ea402825603000584007a03400c4d284c01d040000915412410b060010600240c003041c04920000900c480002d102c17400050074605020a0200c0000603000d03140e03405400300700c1d00c0200c00c4000c10802c007414420b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 921341771 1250 921340521 921340547
    0x507030615181b050c0f190c08120f0d020f04090209040c1e1803020607050f060c04080d080a09020406140111010b0f010c1419120e131505030a0503031006 68
    0x5145281da602c2c83e002c0f07030301d68404044c2e02d11510548000200340707a020000341d200394041440c1503c0c075000c203241032300b50000035500090720b9a0041384d420613034404800c1111a604108040d2aa9440d07288400718084e008401c81b1002a20b00070400103803218a5070010900300c1070442c1c0c00c10a07441c840c0d400383c4101c06912150b40840c11f6210b040c00c0403900071140701204c0f40365041200784143c2da030790000d605980221401c03a41500840c203070720700300b0004000b001d4000040703980160505042c0055650f0b0384500520031010004544040740e090200c550021140a40183c003d101e10ba40b180c81d25114501107000050014403504440030411606218410350315100800e01d0368501d00d50401190000b52101e03040d511441a06614040c0c1d0b1820001c0305080c0761003d000344180481814022150007412941034140a444001310002e55030308546030003015461000080c0000200da01b01000e44066000303e901072040c40454824410000045c40c4503410300d142ca8462242c861204031141008818 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 921343021 1250 921341771 921341801
    0x927050c1f091401050c0f1e070b0a030b06160303050106180b07020423090105010302031608210d06120b01140102030f0f1e031006050412020d050703061518 69
    0xb5003444040b0f6014821800f0b11070515003107052800c484003a906020b110881c005060707200c0040049a03150f4810000c801484034000341019a1900f03c40b4031081c490b45904601301584c81b08294426039400042d00c01a0088042080c80070b03c1034134020b402404280100340c0411841c002e032032407500000150000361748103ea10759044c18400e1b0f09010162040307248034180c140c1100006045100c95544042c4203c2001c40045000c1d403450040c14245040310408031002e107000d031401e0002250004001145541600a208251440e503840d140c45000d013030100300c4d4090509100003160100038052580311402840400140e990700d0154020755400c480316580560030500c407071074003640321801500d01e50a03c400360368a03000a0065007090a40e03e901206040030020061020003464201d00f640504041c3c14158a01400c05c104480c40c0b142c02c51009100b101040d03110010001e0a101c0900103550140007800346c0488a40008013817401405840241d41d40b030313840b12035040114000d907103446c50800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 921344271 1250 921343021 921343037
    0x80312010f080706030f020d18140c0603010e15150c160503070b032e0603050f060f0d0302070906090504021002030f070b06060c0d08060406060e0a0927050c1f 70
    0x7202c16070107841e50051000c4040c1d401e0040b98824082c3c0c0c0110400140ba0708278902400307840d4a4100b0495014640d0741113103500005000a0326100c003811a41900c503000c490740b81c6a5a409403035039941e0001c0c10040d401c80e40041007021030700f8911015060320103070b080aa4540f4001c910105080c01182e20810307603d039101c0c12080100212080045400c000440540c0e40183e22a981410421140241a0442491042d01040b90661610403550400d103070b00c10340b00b081d082a0000400c1501e144030f046110300b00810f035200405d8002c020301c60080c041c0541c180801c80d1345081c000000c01045500381d00442841404241041c400f0080741c601c850700b0b00c102ea00340b503420380b100e0310900300040a46402c0041080094400d410400c1031070301c0700d040c954500c002c40ca061018041a100c0e1540540709010916030240e5071559600c00c54000d403081c8910004005c000402600e4201e40e068007002c0b8002407030301020040c40070200300f01d0f00e00041510b25910f40d07040ca22051524540c00526080054604 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 921345521 1250 921344271 921344279
    0xc1e041419020c1c081b070f02100c02030f0c0312030c040918020d060f200409020c011d0a0c0e060108130303020d1415030a0b0c130b04080312010f0807 67
    0x203034081e103248050312045500c40c1030850580440d04503004c5501011882843c1001112664070086050010402c000c2e2401c00f241980c403094508240a00284100c03c424481c410300c510656101c452a5001400c40b03031044140080151a042d680c2c0320217000b0700403001a0318440d00d90904a0b03008810710007460346028507110a1400074900600c1c203032002180381c0c0c48100586d48402000b14418064403001a000c040811070000306d45012103446500514889113100920344181030303804503085184050391342c14090b9482c2e801012000303071004004141d040c602140a0000a1582103a846a541e00e81840e840d04001c0492500448003603001503840c1002079130007521400b01082c01c0303100b802c0c05801e00421045100c00e8031449a410b83e00f01c103061041104480100c0fa07440c91364a4281d025003008009610382050342074000341107407200d0500080c00d441022441007100018440d48030b03901d8031689c451010039120384c042c404a0003180c3c070100c0041fa00b0740b8a40512412a414000106040c0d494 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 921346771 1250 921345521 921345571
    0x20c010815061303050c01030608010c320f0301090b1f05071407060e0301140103020901031b03061109130c092601050109090b0703091a090c1e0414 65
    0x1d0105030084818801d4002c000038148041015501c04c034050300103410600001000c85c0e206078004500c0b0381c100040a410b103500480e4180281e10318800790400c40c0010310380b000e86448a20504110b5038070000b81520654595006141038a0200c4003c0c8280943d0b001003000402c107070b01c124001c5050f04001c0409440c040d0300149003641c4240183c0e804540e0740b1124909002041e80001e021441e040c00301180c0307180c284144a0076041d1500c1c141000d5046402003000b04005005c004c0c80008940b4030150a504507202000003540e00c91002c1c0038403a840f8960782c4141c0c1000487c01c1c0101c4a0311034010300044540107020507500d595650481c1c05107801d10002e801e194585410060400f03008094110f0300342805601c0c06040440d8011030800400c0c0340c481c180890007010302c020940f40c038815000140240e0018020030702640310782d82c420b440d25540b05007000b4542c2d2420741d1004410780c1042e0340000d0440461228101118200201c1c040050030002c1d80c4030844140201c0f10a0b8000c41c1c3c52081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 921348021 1250 921346771 921346801
    0x12010203010e100810241502151e0c0c01050a02070606050d0f120302161101140c0d36090605010f120e01090b0106230f19030f1107050607020c0108 65
    0x103075a111a40c841c001c1b0b8080c442011005030406130001c0f07030050224002680412440c61a00c0600c6403101c018a00842010340044588468490054241000c69501603445040d92000080000200a41d0034000c2c5030000a40c80000d04860060400000052034502040100031a68002d030003030142200c9030f900c00e000004007480d074000b4907a00340842c01c1d1841c1100b40f141c4a0600c01e5440e090001c3d1b5140002d468181e503004905024102048403090404000c00d078210035510718100021a20200a50108181445d80b48240261590000071404507107050354142150740342d1104102c4030f91120300460741841c03010002e001103480c07010a06141c000c1075010712120102c50000203400703042547c0e4004400300c00c0c1c0c4413030009101869240052011400c0c0a05920041030196207881c8460098a81c81c1c0508410200514282e194200956000b60005040f24140e0001040f1080051280d03070b0168200e040140e509101e010300050b15940005000300030f4900586a0490350341d14100f80d110019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 921349271 1250 921348021 921348041
    0x60c1b09150f1909020a0203210106170705070b0a1b090f120c1703070b10031e1b06090807050604051503040f081614060c03190b12010203010e100810 66
    0x11802210000701a13405202809841c110366014581e18036078001e6011051540e02d4030203007040c0c404030040028540003040c100a2032412004c81085690329542a01d89009442c80900301e081301d003040040304500b9522600d080300c44084504420310381c402c0304a40b0304940b400b40f0092142038680500000c009613444cc1c600758404c500341102241c81d1003c0703080c40c441c0d921928000764800301d001030401c50300c010b14980c0840e0284090380c040d80b4548480250240000340c1e40d0641c40c1e80c02200052184000014803415401520740c0f030081d9a1340c1000f0195191403080140b00e0140f86000b00e558134100c41207904603800180340114981800740c51043c43c2c0d00c050422602e0380403541d0f0700c10004140c0c2000d04500098041f90307646240d403600304000c0c0c5e42d404c14200202908604200420039482c201900e030400c62403030140c042c20075030a01d40001007000e07141d501d0b4054144c0d000d81c8441d1005400541c162030100e40c06c0055070721040d2043c0c90104040c01119416000300203100340c0e0494691000100d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 921350521 1250 921349271 921349309
    0x3120822052401051c02030a0605040503070b0702030d0e01051003021c0507090b04180b0720060f01030327060c0c0b120402010806150315060c1b09150f 67
    0x150329100c81a03211030407000808030b00d19034500420041c80e00c40790b04450510007650104c5019010f50019841c1c0e07000c8003000b44055906c0000c60309001040096070b05061f1b0000c009171460130f00207000303580c035013007084040f512500703289044129030418019680102041c0e940da595036415a42003001c0000301d2a103402e210050044800d001c0b4030f08000b0b000090904650005070040104103000c107130345403c0c501000c1880700c0300110300092100440541d0204291a1500e104185080f0540c41d50005051226641c0320f04810302c100400c0b016800c50480380301341c4420203800d030300b4415451a0095020301000c407541d4001d00b041290b0050511039070052080c802ba078a00d80d01c0d0000da21365600842d141c0c2e041c0a105134104021560011501500004103d0741c0b60009101c0011216041c80020042801d00340031114424194603a0000e49030184d99140c01c1d40c001d60140b0b04c134542c40c0d040c61140780c4c0c4a1801240400c01c400411020103d1805001d08101c4210310658244007020506c00d140750a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 921351771 1250 921350521 921350533
    0x906030a0f0224030c0406030f0c0c020112020409060924030c1a09061c05092e02190f080615180f10030c02010b120607080c0d0c08010312082205 64
    0x8024000354840c0422104460711b0b00d042034001000c80b13400e00500b40b102c61802403600000d039001081d0100490b42440e0002e174968043c050f09010f03009560060010700e00340200031644840c40e4000c114040003404042d51803a1034000c03003403440c82441c880540180700003c0f042c0103407890124114040c24501400c80d19106500001c1440381c0d210607002c81d041c200f404041c0200c1c02e80c034000c140d0003400c0380000344040341502c0c1d02100010120307482c0c0e61410801c0808080c2400b07154054030100c20100380045060700181d04064101041c10b5980e02c002041e640002d4094540424100900d416100000f8104400701c013403080d410621008280e8402040541c611265440c1c2c1041a078445144d0382c04950314000d002d0281c252488103000600c00c0d100c4415070041c0c1e07140000d1840d40107495242403034440c0c0760080314018512030718481441d80d0382003076041c0020a812030000d0b41221f1103120180c01c004120501284c081034142d803000d2018102c0906400c08000f0707071000751284c0380500140c4071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 921353021 1250 921351771 921351829
    0x90c092103042c07030c020304120212060408090306070518040b211f0204030515040f080301081c170105090601120207050105160212030121021e0906030a0f02 70
    0x115803034a0344490f030b01001003070502c0e5510701d51030070850741c01c80038500f01400b21070035144000c0d44038012805581d08008001c0b560343c0a640d200c0402c02c203c0e001346800e642c090705050814900035402581514041d00c07072140407035802c0748940c0407501039509042000080304072120801c0302610110301c000d0350041100c1c3c2d0519410039030b16081105403842e0340c01881e05031034030b082d0314400c0f4607414040c020f8144103001c2000814404200c280005011038981a41c56903546000e124a0f0b40080014159080110012542080006182c6480b504120b107420f00c10b040e80b5011202c0c45007690103102c0e40c4480000402c60303418070007000c0340c00c004141029000400c010400100302c0c1c0180740c1c2502c540c0c0d161000c1c04600c0396106045000d01c004ea20281c42c3c660303c5450480d95034807062003014098a13081304560142000d8460422000fa80200b686900c2164280703a0060300000341da04502c40e40740e15020420b00e29002465102c1107070304c0401c01030341010039020408040880041c80c807500c4410001a8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 921354271 1250 921353021 921353039
    0x204080303070804060f180803090115080318060702180c0d0216060e1c110a0c0801050406110315060906130602070305060f0f0a0b1f0e090c09210304 66
    0xd88030700c800f40d0b0344900c3c0d480c09042242c15100c5204c031102d00e580c035201080e418032075009260728100342c0200b000c5a4944a4111482c0106206404805e03401720355980414118808401030070101d0010141e0901c0c0080e02040164078071075818001d41c00070705d00d4044011811104038940d40941c1c146030700d9042040c501502c00030303648401c440000854591444a00300003052080302c00840e4418000e015900f080040043c100940d00340410034088070311105148010100305049c00380c1d41c010100565299a0402507000e071000340c3d0220f880c2d9051413601103804007640241c0b441241d07064200d46e100d040c0b030300c1800303207990090000e1071b08900e00b00144c4241e030703048022080043c400b5600401c105851400c0c000d040c0314014001c1c2d90324041103414000c2002403070380082d0300490501000580300e42e8080c00103000410002300740768591010011121415081490b0b040f0b44d1201741d90201c299902e081d03140910b8812841c1465101001c1c19900d10f010003059154090318101c0c000300e0b850242c48445075 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 921355521 1250 921354271 921354277
    0x160302150705040e011a09121609060306050f0402030c010302130915060f030c0512071110020a090803070b010b0f070b0a02043311150a0501050f010809071802040803 73
    0x80c0125030300160801c00c11090130b07480c500400043c1e038280c03443c413102c2c800002d0a11800400a10640000e01c85192444041c4601c00c22827001462919106a8034003c81c00a05030b144800d40c1d140e85010000740480b00c40b10007007841035a00402501001109200650081d00710401680480c040040d01041c004958851020100701c0c65000521151520b5001081d0b441d9200740d07070301003508020b480c1c021260413406541d1100c0608014509955950030202c170780c048980201602807183d205141803a03180c1354004c04000005070340310701c00c0985a4455913561302c90b8036801813070140c4c0d40d401049003890142c0030b022204040d110291800e4525100c8042401c42a203068041c0307036001030b00300541c00c4c94140005041041ca6148620701907154040f010f6150b0170000401031116210061140c8241405aa1510208568428440c1c20005101c0c80101024015540242c4031498034115540c0104040c2d03100e510300900408074a4104031084184100100e003100103a6024000401d2025062010f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 921356771 1250 921355521 921355531
    0x40501090c08071409132901050a031a0a09081308060711100506010e03030403030806120a1e0f08030703141f0302040b060d0606050406030c0e0616030215 68
    0x855502801e0074180c00030507003a882910315501440003000030100f54040800d84050803102030075107940e070a0104603500c0900c0001050a0340c02c101c00500008600301c0c14000840d070b185442010b0383ca4000307012004c0613034000070301600749007500c2c0d0f05108a07101c1603030391006245101017400f1134260b40d0301205400083e070308402c030523406c1001d000c001800c00c002540005a85400d01d5002500c1005584550301c0c40001ca0055840d1400112140d010701020b074030188001e0101e80d1307202d54038200100007410680b800e501c00d500c58410340d000e00380000b87c4502940d4001c08029641c2c4007a40b02840303031001c54a0201e40700d03040049080d000c01c0302c80b806544070f00c4480e100882c000001444a2034aa1801040c0c0d00541000409040030b80014400b0501078950603980006c150904400048007030207520492140c0604001001c1a202c0e48a0064000c4802c1601d0a000780800301c0802d4032250180041d507a00070a007406803440342158680d0100e8030074001e00580c0d28014200300c540c80c440c4803c0750 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 921358021 1250 921356771 921356773
    0x50a020a0e0106030f1b0302030a0b0a090e0c30070e1009150612111204030504030203100902010f050a11010e160b13060806061c05042001021f020904050405 69
    0x1c01040a0343e054054040204001041000503440b88200000403000c1c0b19070f400101540480050144140c070303841b072511482c00500714280c10344d5900280c00600355010403864a030255507070f43d007110700703011404041c102403c07904044218401890085440441e40304d0050b94400c03880c00180084162254034040d015110b0300714452828808110181c2c2c48140b00c1e40512003c00c80100b185903486450360a070011002000b1841c002a544544550701035003102e043c4050a40060004142e0808001d00440b8400d4041e94035025000300840119890303040081c2c045100105001c401a215000601050100b405e00b580640f004010003401c4485134260031515610896500b00c104e00c26a000c5c9000b48a541d048034a0800c0380070f40d01c903a003c0366100700d4042c000c0040105c1c0e040d54488055400f4082121062050510182da017000942010f03038090718941e19101d640360040b400c1c459100c51110068005000c0142d941240f0074481e1502c5444801403039003445006040d54403405410f0281d03000348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 921359271 1250 921358021 921358049
    0xa0306030c0b0715021c02190311271302030a050f06100e0607110619030b0901060f0c03030f14061504050306133905120316050a020a 59
    0x21524104215498101c114a000180240e80c00503403522040c000110703109101580300c0c8640600041010300b031b02c24450065002060b041e001c0d2511800c00d20160364140d90a0044082900800300a803040008000120000220046011804c1c0c6001c0341200006400c01c1c14140c00180c181089030402e640c5580da194a1303005211a2142e52400c49820100845509011803407403900a00580380025185024500101303011052104c50b098980300d4500180c221541d40403182d07085803039070006407002030109140c1075001185051014816045c1c603c0e40d203400c80d01c0f03900b2000564202c1c0d14103000710201030b20707502c8807048514580078013800c00703881c04000b16070707410000d040240403480100203540c030040030f00c01007205a400041c0f0030f8120080c01030f4014111400d081c002ca100101500180100c080201514061350041401c1104c1c240142806020640c80e0780c104000d6800920522519501c280316503000700c0c80d19080308540d2440b40003100c42c0040b455001c1021260207070f004006c030903000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 921360521 1250 921359271 921359273
    0x1309061b02010c02070603090f0f14010e19061e020408070e06040902090402010c0507080d081501090e06010302091801081c0207060c03120b04050103061a04020301030f0f020d06020a030603 83
    0x11041090904510740000d0110540300a030013941e4840904c07039801099166030000d41400010884184529001080040c4200141c02d0212b10500c180d044040150b282600c25140b40c2e81c0462a4120800c04240e0842d8440d0680c40c2d503005441200003640c0c09440300c49020f500c1487d148000d00007043d10a003d0f0244a01c0e110f003980c2c04030300007850715000b20308007075103100169503440d0300b1584142e090070240344e42c04442c145145840c909403c44403091040044c0c0120035604034110f030f84035481060714880c0f10711929004482010140c03281020320502e407000300c1e008d50b000b60080c2c40071507806004d102e22040e040c42850104403080e070201c0015004100d4800308014100000e0a40a00c02d000601406250030401401f4a44811000d400c000300016410352070052078001d2240101c005206004a507140d0800070300070b1160404d0003100c15090300704e4103442c0c102340c02900d04807a048801403d05822a0700c1d894041d2607100000c0b6807000d004c0302c403840010150710140400e2043c5030341c0025030b2411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 921361771 1250 921360521 921360551
    0x1021605090f36120c1e15010603140c0a0914190f030215031303050d02040510020d0f020d02061501050c0601090207020901051f180f06030f06050103060f0b09130906 73
    0x1540340d02e5504c46000c0184903548580022000c90503000c50362030f541c003285d44901507410811a1665105c42003515000010501d60503003004c5085850203040030a280c4a6900b98626131190742c0804001c180b2200b4100300406184035099083c10001c2d1002c585034516940403240080b0743c0c3c000440642c8400414402d5046c56500e11001444400c0e000d480c60a02d00d03500d114900211200404103d0005900c0d410503409805417801801c02825404003075081400285d110003140c19134800081300c1d000c665106500c001030032040000b0940140003142c07208100035001400006c119414404104016400d4500400c80c1720b000b40141c060050711201c1c144100180c6010681c060b92040c4260100d00d5907038120340c002d4072110035643c1000314011001020703501d1001c0c52544400011100c1c0d003c0051041d4140d00645c01259070240100405e43d02c40005404403070300342c0600701c1c0081c04500c043c4101ca01c0d600042400b07860040900121078401d101c01b5054900c54502110000d4135540d440c05080e103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 921363021 1250 921361771 921361783
    0x1211220f0f0e0a030c0f060615030903020f030306150c071a0c070515090415210c0f0311100207090204150e010207030308060d08070501140601021605090f36 69
    0x124002038411400b0f6038400a1400c081c030b0341701901120070225010200b00c1d47e580020000c03c03004805404d00074144501900600d24000140c0c058002c54004c85214940032045a00c06e04000740542210807601c41c045160340c009110861842c8101a030100f010412100d800e0049800e8481580c0d403645040b2445080039410b07441140202c010ba00389944903280c82007034903040d8000b030310300060030442d900a44100e60304c15800144800466032000380110402090100c8071340c0a0b41603e2005555114076035140b501500c006000d201c901c9035162403074a4144501c55000c1994812a120b040e1150380060490b441a03201301801e041c118243c41c4010380040174402d104a00340040c1c03000d1031a540f809045481d000700500d10072034484000000f084104401c0d61806504640208070110b07000c580c0c140300160a4640e1030151081d0b91046011054904281e01690130140100d41039450703185c072000303103c0005086003d80842c031b04007a0349002841e4107050a1a0b00340480a0000d001d88411941054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 921364271 1250 921363021 921363041
    0x30708010519050402130c0f14040302030c0628020a0b0c1e130306050c130e01080c06030703060b070b04170703050f09040902090a020c071211220f0f 66
    0x41d0404041007446911110198001107900390045410703502ea10000740c4251149403c10085440c1203800d00c1d00580c04890004941010b8a0340da41140c280b907480b8030140a81e100c0250b1550250082480c0c90511750302820b64428400d155040744215900042c944c0c451142094005070b111b0000c1a00f4041c5140f0083e400c41603800340a80b43c002d42016000c941e0f035100b0458210448006244094428128141002542c008030704200358248060250000c3d400340c07494850140b010b807c0822040c41c2d49180c40d0490381c14000a0042001d80e50521070a5003008250105040c0d6840c0001524000500100221031164128909521305032502d181000407001503a820210309019000000360080201c500d400c0e10742c01c2490b01d132107032580060064604c001c0029000340315001840b0ba141c20030707009060019010020391340c003642c0b40c0780709014144051401502c0b00110071b0b5041480d00701010025a13016040c9025442c0d03440c20003481d41500d8544a848403180e64a00c070340da0842500d446408011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 921365521 1250 921364271 921364273
    0x8010e1509270f030a17041112031308010912050f0304060b06070c031b1e0501120e010216050f0307150b040f1b1b0b180109150b01020c0f10300b030708 67
    0x1604050311923110f080085002d80d4040e00d942c82d80c0310b04000080095402c41074506a02070009501d5102c914007070031081c3c1048a4004d107020f01e4285507400b59098803a203940a1104034290b42e255121400980786041c0030507044141040351038082181010200080c0d4020941000203110006291080010030303031240c0065800d1f6219004040c1b5800c14000440c0c80900e013a0b82c00143c0c40b08000e00801610018a955620002d08040151410045080880d000d401030702c1da907054500107aa00c0e8071400c400101081c06011469150104540c0001c4510341d0240000884614001c501c50458080d06e034a004811240080426819840178802d1042e03040740c03000044500322542c8a00c042078006e0b00d4008120404003c44203014130075480b4040003034020b1000e040b0541070b21128402002d491b016540140111490001107081c005400c965074500649601242050075108031100d5244480c045c02c0100d48200300c50043d4801d900511104a5000700000c8041101d0100751a040d070543c010200c1e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 921366771 1250 921365521 921365567
    0x902121303050f07030215011e06031a131407080109061710050403230307030b121e0c060c070f15091401120c08010e1509270f030a 58
    0x2a5104007640e03480a88403c0c81611441d00d494140e0500c0c1c0e0b41c107020341030241c50000006075000041260902d003e11080905411611210120140c0b05d0502c40684094044101e441c40b0741424500080041030004001407005102c458212702d818095480030006070001c0014001c22070301e03200c0d540044c00115850001036050010705500c07442140380c1c070340c0050798540000d018180140c912000075414002d4180720b1030840e4520440e240c00907500d00000900c0d04401c10b169090101c241c92121a0742001031040038004c0074911182c00030144091205c2c0504400034910341c0b281d0b800b42c0b00703244521018201030741c03c08003039031303c220199803001501429540f0107181c034070f070401c0c3e282007130302c20007000c007215800c1440c010381c0c001b100901914001c600e0003040a4001c1d90055126040c0c0d207094100381c2d12070312580282512440d00c10411036000d0820008105a10480b00f50303103a00e44400003400c0c00302900380300f5190070503485c941074642c150000290f10310899400100c00f070035200d07a0100b0500c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 921368021 1250 921366771 921366773
    0x80d060f08011a1c020d0312060e130f0c15050405030f070b030f090c0907080402031e030f090a0f0b0c060609040c0312020a080a0c0b180c01050304080d020409021213 73
    0x100141032074810700070b8600d1640021001c2c42c1300b14403e0030341d8019151480400e4145401894003085501655442e0300d00440441d180c1680035580d40151901d100f481c400e4070a544541a002031481000c0340c80c0c00700c0315400141d07082e000c4c072150045c024139203645072a545041d040c141460090f5811603484d8009841c140424440e400c00c5d02e4021119059900040c1d42c0c88a11900c0c10340003200896200402a04100b00c40741e0080c61144a00d10950681e054202041a03c00724800001aa600b040d001800385000c507400304070151030000310081c1500728095807442039980d46d401c0b07500010092500040d002e0b13a104001c104454011005a8580c4c28510305903e4000e22500340d804010400d26100350103c203e01c1c030030414885441d4001450f940d131070600600140c24061050300c04c8501e010750320f000808a8818002100e0125807560103484007000340001152203510091080394031723003810f000c1102e40098600c0500007a21182500680d41c02ca0ba09085401e0720b8020088503220420707500e964 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 921369271 1250 921368021 921368051
    0xd09080c090403180509040b091501030803151801030606060216150815120d091208190504030807060605010905040216080d060902031306051e0121080d060f0801 71
    0x550b019825140a1188008400b4007501c44021917000c070358415105030601c0140700700120154011103410003200c41e030f20100c542c1c2d0070a1450910001d881c50505000142550003007148400350540024014015901e46400f1000f031042e0030b0b0000e07140b05a54000901005804000c50403070301c00b0042c503018105280000524070f40390074910040c20000110082000e809419110804821005141c4c0124a041c40415a50ba0000c0f104400004082442c0020203008000c2c406140903080140e0a1415000d200c52808807088000c11100700a030401000000c648885d001d800c0c02445260003140203031800b8001000b17140341da00310350302c00e41c07040040b50160038120384c0404595a01c6401551608002d0040d00c000701155070003260710600001c20441c109030003282c0741100511441080220b611104034000c2283c0388040d20b00303141d407075642c01445650070b89001641d041400c0b640e10b182900d6a80c0e40c0c61000c0e0003148803500c0540d15180144100e0400c00d00b01e9010344100c1c3e0080282c481d0401d055 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 921370521 1250 921369271 921369289
    0x3010302060d0f020a021507031406060a020f0d0503240904061d03070309090c05130b0309161710020307020d18120503120a020a0503070509040f06080d09080c 70
    0x38401d40c8005481c140103880e90b000f004040c03003050303011034071110341500c007948610700e1080c0c086d1a4201100010b0860b07002c2d02c00c8180c5c4440103550907490ba070b80c082c1404140d904c800310a0b82907126150f1003091480d01000310f02d0343e000441e9039254807401c0c410040c4034400d038a00c118400c0c60004041c80c03409520742d0301d5429403103504854041440c1140760200d4850a030500d000c0021800001608000c2c180c000c00701d04126100c8003406c02c40032440d0b01c0f04446a0240203103200340a0305422042000d6100725002c0c44e0030181344015241040c41c0310040e0500100749500a01000651501c0c0440403401804056080b4107940010340c51890f107040003c0d01c49150007501350500c00c41c07035800505000b0b00c008a4024203815120311107694410f09000340c0c3ea811500030307044d294441600160340082a030094880080907500d4450071611490001c5d2815081001043e80260385d07080c40443e84c480900440000700b03440805032290100d2040000c1c410794880d00015401c0d0710a200840040d103c200300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 921371771 1250 921370521 921370523
    0x5010b070f110f09091e06060d02011805040221070206220c12050304150309032c090f01090c02010b09010303051b0330070c021207030b0408180114030103 68
    0xb22000c8090000300051410400422054000d03078130340c08000041070b000511605c00d8a0740090040c00e00003c090341035481000712034060304281c402410034010f501900c403042090706011079402c50b039138507200868201c0e044040c0c000c03804130311400d40483d000744642800d90040e51034805410710f440c0103144080d015024600030304000e000801032500b8000c00c06400c0002d0440001c140203c0103c5061543d40ca0700b19000741c400b84814a01e109006038081e00c24020901e525860b80d90310000d07131904600144e2040d07506554007010311000c018250303940712500c500c0340c04d168030706164a504011928003207525010b88017041da0300d424661000c50b40c86040d007a0460b589454000d50354100244001030010701009001050301c40826555003444100c0c82042c0310b00b400c1c0040e4100e09070814000d55034000300b0340301000400c88608000015060150b00c00341d1500c6401e0484059030355030354401c80403840031181610425000b2400404a195042300c0c42902802440c0805011003502d400c44258801844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 921373021 1250 921371771 921371783
    0x504020904110a2d05031501092a0809060123130e0a050106140901060f2706180b1c0e0c100c0303060b03090c150c03071505010b070f 59
    0x80808540e03611161001c0250000b8007000d4135038503200b80d00d00b4040790400300002a00007504000b041c0e5043c00284883d1000d9074030000f14050740380c07402d1000100710300c905603401d202280002050300030843c409600100107079034888640386810f0500606159040c0c0104d0301900e150701417008610710b81c502444841404403981e4a0540f01e0021410003020400000051400343c44012400d20106510202c111a21124102c20201054080181111090045501042c02108005078070b40c8100c0c25903402c821420017409660303031800c0c0c030417140d101036901c200c000802d0071420081c42002090114003d02940200b01d013072404907400c3c1e040f000c102e0241c0b040070a9442000604004040220080030f000182820b000d020049a0090107415001c900b5800b003801c0040008001080c00112840f0340e00b5103014207108000402000503440d4105c04000c120002440405400d00061008240561140380d14030010081820090b05841c2c05034005c1074000340c14000785012030500c1d000140c00c1a4801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 921374271 1250 921373021 921373043
    0x606010306052404090e070e0703090305310b0901110102120c220314010b090907120f170901021207050d05070615081b09090c0907091205070e0a0504020904 69
    0xa0200151402140d10031681d140c1089046c00d0898801700c2c42005a5040203c1c1c510f1582d5400420350556010800080000b401004043c80080c4010121040490172581070014a0544540d10b0b1000b505600120203084002400b014190303002030310500d185034040029410f00722440c1900c2081400103001ca002d4281c00140c040800c0c0c0700203803501a414502c589181565201e09015211241f40c21b0341010640c40c0110140c25403401c3c101c914864182100242a8541440182c584a2034a20012180001c0c0007401100140c1c07096280c0325150800b8800310b4a07401ca06000910f44504a4507051881d001000900040b440102d4002c2500705103042982c2d5410051030014010034040b20702087c4d81007280c001240301400441e80315180d170f18105643c01c1c4400340004000300c1c2e20090f100143c0741e9101c410f104e031031780c1404e0509a510565509118a07034076900c0301c4084800441d04012075480c3c110200520041c0e00ea501d055410040d801c504109502e400e90210343c44d0400508081c1c4240c00403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 921375521 1250 921374271 921374329
    0x117130305031b0a020c0418121211030916051509013b0f0604060504030b060f0a08030403031706031906020d020a08062707050a031103090d02060601030605 69
    0x501c0700003281d0218403843e956191030483c002511022a003030078900c100e040c40c2501d141504501070700c6003010b800c09480d030191110b01c1c10546000300c101d100c42c40c1568035103c1380d07205103d804000c0c5100340c0c1d070803000c0c01382c00c4000d065021400c54a81c00144c0310b0040e11400741d01300c1841109441030a0406c0c01c00c00c944490036403c1e10301c0d99141041c102d81902c100ca41c03e9580c0500000703c007203107000c25a4005000d540703140402c95540620302880c00040c0061108001049810b140d041c0c2040c0d010301000304a01c02000807850480d02c54001212950002070200304041d03022035019140303001203944980c40d040500c0000d41b142da4043c6003c50f2401c40540d120b083c40941c1d4106d807203407544904110341e100d25064002d8020881142c1e518494051138046505207940c050080c001c1c101d03541c2c101945561001002c0c7c4c2c0036009a0080010036607a9140002032040080055000300c3c0044010301c2c1c003032610359001b841c209000700400c0c1054141b030400c108684444030982100103141400072505841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 921376771 1250 921375521 921375541
    0x7120309080d1532060910051803060117061e06120129040b0a08070324020d0207060b040e06011203030e061302011706180a021e0306011713030503 65
    0x1903811000001c1c2e20041300086101e00e41e002400102d00e070000350201003500030200003903800b81d0368030682c001001c0035001880900c140c0c01401540c3c02e90b48001840003001000c64a8884243c01503641805444040300d25032904000340747e4002d401024104d40000c500c80300707580f2180b0203000c150103400042c0606e10444429040108007210301c1032480c0c0d12695071030700c40101c910344881880c05240b4081d944111803c2100c0d40320140e40c8003500414402d03140d40c0ea1820046211840d00006130701400d46001070150900040250021024001d86c0f1032200d0308011701101d5901c00d09510135807504460b0300c2c00500108402d41111400c08000348070452074101940604141341600130240a504200285040400d007842d08080c000e2345e565440c4048240f001c00324542c2950400e030322416181520050b010142900c82c1d020340400e2001d070820440e030054807000c2c0d800f0043c1c1d900030341021042011383d592088016001034418400150303181041a428406070003240d401070100440000096070241b2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 921378021 1250 921376771 921376811
    0xb07021818010c091e0e150619050d0b09040308071107080f03030f09030a321b100b0f09181002030108190305090d0501060b070807120309080d 63
    0x194400902032164000c030f0013401010785010f82014480c82840c1309008051505003035096400d08140c039140e9032541d01400700c2c0d21008200c800e510520800000c1d42801e52440a01c0b0110001e840309615110000d031845c082d1139a40c3e50f01401154184104804658082021500300950307081619062025140f81030800704150040046440345602140142c000080110b201e035610f10f4449a03181c0b02c0c1c4440c40e469201340988000000c1550b600d0f120402c1303228038885d02880040c84403807400c4041071182103450300030112a00300881c0451080f410345d24240100c034000e040c0550f08014000b03840d400512031110a40210b4019201e05e40001d617001c10500704400a0304100048440001c4c9800d200c2d0b01a5109004407a158001d00001103124500c0191050b040c0381e040e1036541c10f10040300d0a000c610403007130900ba10070f59212000001c45803040401022807502921140f075491005082103a440c2464403070b600704040c6070107406808100c03041d017a50007203a5207840205000204196089a000e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 921379271 1250 921378021 921378061
    0x7030804081608040e0f16110726010b0901050102150604020d1d0106050d0807061a06040b0918010e0f04141605040b01080403020601170102040f0303020a05070b070218 74
    0x201d1000c160b40d0500810102030011190500355078902692075160354004454103484101d04500006071280116020707541011650605904403a4190381d5154500c0c0e500380b6000c01c03106180d42d0b1052801c00d112080c0910380e8000c6080ea000c0e42c0e5545840c00007542c859004900e800040030200c0400e12076543c40c0c04503040103500b2b400074801c140000c94803101000610401480700c0d0301c3d1060000307507400d00c60600404907800c290004d08005440e141c001c0581400462603214082d070140d00901681d40c07074003a05c003914005e03510a44540000003800901e80c0c281e954601e00c51260f00c01003000e559854030701c40d0700c003030403c0c018420b0341c5443c40c049600c500c141001c80294001e56050f4440340d15403a034240d046030b40c215410f0048110303840c01034903401402d17640900142c0040e00103000c030415518142c1c049007403105c00189055034840701e0300c905029607003040740143c20403255401840010070100015113560084286003400c070340e000584d506810111502029403820001d02c3c2424601048070f000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 921380521 1250 921379271 921379297
    0x4030912140a0b341202070506090c10090b04060c0f0506010b130b09010e0405090708120703020717150c0706021309050a0b030a06200d0f1b02030703080408 69
    0x110740e00e2508010505044941e40341d4180c1c9440e050109501044405507007415244400240c21280c3c0021504180217007403d1250b25000c201000c0041d100f0801c4a1240c440b0001620403401c81c001002900c8010344030180c10450080021300180042d00122021102c3ca414502e42c11001071034a07116240c203085010740203000d00e5000058900640000341070050860b0580c40c05262558841142da00440c00311500040c0040c65507035250900707a2141d900070092000700d4018607034848d425450503418100070b00c030200c00480c00c07000b0581c0400c00840030f00f900680b04801c0d0548545103070b0b030380d011011580c0107040c1d0030404290310501e503008403507405800880a541c0d41c00d42c0c0c0c0b41400664102c0c0b103009100ae2606000070301103903051243c00b00964009014114640103500d0700b0000d405d0310100c0079444e0354800b510a400184c1c00740100589011804041041810558003004664000b4030303800304c110180080c8001d01e54007000302c50b0043e51504000500c0c1d161402c1000c0b05009008414040b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 921381771 1250 921380521 921380533
    0xf06011404060f150306170d0e031e010e0f0609120d060902070602070c290d11070311150402210a06020414030106090204030203120f0903060a090212060403091214 72
    0x24240000b03110400c2190f02c5e4034203108659030b400d80c5006d0702c5d046d641e0700c2d0010341204c240c62641d6449502c902c0c1c140b0500400310780c040b2803e50192080c0041d11890080140e5603002440310010b01842450317143c80146000e040d240c034005034aa501c5102c00c0398208002840080c0181c44160154001401740c5080316046403243c41516066009500090040d1010030341d1107030020754074041c00e00c8024044241c0d400ca141c1691b01c401c240d421a0400e000284080d80c440200256415905025042c40c0340a0740da102d00304c02340b04041d1401c6c040c0455507030b464880352508003c09a21552515044242d003407828801420b02c0303810040c201740300300000070032217400081c0010b000c1e100c1d031410008058080300200540c944c1c6106607030480c0b0a6201c025007641003400180007440c0d24030054000198102007280c9486092400a400c1070f0341210b402c100c15035203d400301c0a5040048110080000c041d004010500703141d20041c00810840c0b01d0031010038020903685080214569640410030025011180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 921383021 1250 921381771 921381779
    0x1020f0f1605150106020615030c010509180a0219020303090d080402190e0a1d0d0302031308032a0901230c0f2104061d0109031a010e090f06011404060f 67
    0x2c60f40c2402e2080720014810780b0041030a10022899041e4403110080003408001d401f040195078a0704200030031a840882460b4034041049401c26040c41055200d00043c2d03529041220644002480d54031202150710a1041010300c0c440004c0c40b41ca040c01c1420140a2561184001030b202e0550b0f001c001c0c10307c84104000902d111008490f0707800380918503001d100b84000c1000e11061001c8404944529911031202d1203079585c002d40c01190818040c158038103000e4210b031a440c805a00a032082ca071000000301030890801d08081c03141d6418811311301f4003403500480340002001050124154182c2c5030011440d810a0308000041b01e280030085815129900c40035249281c031105141c9118a60194020043c0300ca00c0c054000c03902a20199150720580c028182000a010701081020701d043c09030480340400400e000b80051078040510201d8041950b05103004070705030500c064400c007550751000401240c00310000c20940d0542d5502c1e00d0b41c803d00141704e07001030058080e035032050700c1181080c3d001003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 921384271 1250 921383021 921383053
    0x50402030a1d16050301230c09060408070302190e0f1005030f01150b0301032307050402040909050705041a01080a14042603040b07080604060b0310140301020f0f1605 73
    0x1c0310043c41041e2a903107142d42d00241030070b865461521030b100403a481003925500d00900380d500d80100d49010003d060444d19808548280d003e500007000c15400841d0070802c52a01c0b965001880251300e003500e16207850700081c016080c2c4068032210000607960009a440e0218900c0701004100013022078031015815520540200414800d100407090f1600010444482880450707040301d900c2024141003d2242e40c0544132416811400c40c0c06004001c40000d650380d50340058405000c94440008115505141075890700741190300c214040e90600504681c180010040e15418800070300742100140e5400381d20f9401072292152061143d1486000e00c030602440c0c40d10202c4200650040030902d505110024565001c00c42d40141403049c5000024010351080c4c0c0c440340c00c1380014202007019919a000c000b0347c0d0b00b0840c1e0205034104c0796030042040c0090311421100352141a4000c514150081500321568418444101e601480c00124a00340081c035141221380d8540000542d100103086000381 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 921385521 1250 921384271 921384283
    0x50c0702030f120a0c111f080a0905030a0509040f0203100302100c050c04090305070215030a0c050f0a050714010606021c08070c03080601030e0f0d180303020601050402030a1d 77
    0x140d001e4072032201c40b140c004400050740866014040c07809401c21840250841e56440500710884005885000c2452140c440000940d1619070403481040e2202600c00c0c020700030b400c010020748202d420440e1410100e4030200460b0452409441c18594411400001c5800b81201c1c9a403025034901c00000c1100141603203011000380e034801c48010100e8020315400702c07248402c1520180050b08109100c0741d19281513031142100c54440d06055080c161581c00040e05861003400000d01100000100303d690010f500c41c40c020f440143c00c2039424085403540b200e0650089540d000184600010000c4c24041c07045110800e8451a000903c81070303894440080d00d5891000e52141c0c01c000100b0703501c0c01d0600030000300e4851003c56552a40c91040b548007200d500354060001810305541d4450030001c0c21041c40914a18259040100000350b41c00100402c20324160091860341c040e18030003840002c1d40403900340d04403402210090b80300c1d05c0e01d00c5a0f50040000c0802401c0c41580a00814030000303002c41d074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 921386771 1250 921385521 921385523
    0x1e0c0d0201060f2111030d030f0c230c070b070311060114060a080c160c170307030219080d0c1d0906150f0c0d08090609070f090c12050c07 61
    0x2444010343d285003907145880540074500c040340d40d80424075096028000181d15a500806459007018102400b0900300907083c804c4000003610342a940001c3d10003070040d0300001044e40b0b003101590304904c5a6000d503201208081000500000344a410040104000c401402c180588503651390803503e0007800f52400390481ca0020f003e48400006c1e8034080c00c03190707000008060300311450311052420845a100c80249101d85802d01030014940001c0b03100b80070441d1034440e43d0b4038034105007071055110030130350004180070540e8000c2106400003a030128810003c1c0c549064000320802d464a402d1945002d848103000c041860201ca444a0351b138040000c83d411001420344020b007a004005210000000b1200150007040361050002c10300d02101c0206003864103d2411424200365180300382c14105001240b400150b00b0806200194505008468101410310001c00c0601c0c074051440195030824458481d016907940714070040c2c0350207401c005081c40e608002c01c02a40c036020062090035040504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 921388021 1250 921386771 921386773
    0x9010c11180f1008210703090b030a09020109050d020a120809153c09040b04090c1a0309120901050c0105070216051207050906031005190c1704081e0c0d02 68
    0x303840000840d440f00c4500583d8a82401c55041c05c4222070b15034041002241040940100055400a000051401560483d0000c5000221400014041210345e0016403082800c0c0051000590b5440e5002080f00e2103c0e42c0b10310758044c5410300000a0165080c016042983e11350807019103a0000c0051110108404881070141c1c0090035041c203091110310510501d038039058482205508a038040c0400fa0340080c03011a940d05081c1c0440c050b546d0b480012a9501c1c24240144100c00a011440011240801800381145003040c0510390f01c042038561802808c80000e07004615034802c4003100c448204080007448079050964009690344001020720102c1c0c10500804101c2e0318003451042c4060391324070300400c06113082c03030104542400040d022039818031402040c1e034071a00f03181c080d852007843c4081c1c0403440300280030400800e45103001954001c10910a144942408116001680140c2c00412032a154100400b0380c40300f002d806070700700a5112001c00c941d0b410720400901c61020040300e078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 921389271 1250 921388021 921388051
    0x2d11270111030a090320130207020315040f02011b0605180c0d0305180402040806010801090209061005070311030d060806061e0105030103150906050117010c020309010c11180f 77
    0x78021901c81c0103410b070320800107500d01c8041020808400480a040a402e84c030001840704a100090203c000179081541944c1c0200d1078a00703601e014040d4401e14070760070b02407015600e0035907503d1300c0800d2480c10007414400039444a4003600f28904850580e00c5d8001003c05c9181041d45032018000c2c80e8000726815031240d0100e078070700d43c1800344404e10758035031680b034550500704c180e030b4900501c1303007409003144e00603609001c001040d41d81040428020a4030000000350610384d40140400e0705801000540558100c06030b0022641d80003088130340b0207426150605000700204141403c51082a840c3e1035124289600070405c2c1c040450540e00554003120700c1d5114070328460f40040804ea41e0f460311400f161040c401000450381150a80408801c800c0e400610050180e0b6401c04652003a0054052061036400d84460600300744a80c8514540600007141001503440009043c00b0300803c0080c120340b0303404489001521034030108182e015585004070541d2500d0030081a2102c8102c4104030307140712032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 921390521 1250 921389271 921389297
    0x30b0603040b063a0f021f0201051e070324170c0409030206040803040309030c170d081909140d031b0801050d060207051f0f2d112701 59
    0x14018100003c0c440e054a003104040a07403e5541e4076480b40c00741c4100e80d203210841d00581c0c41020680c2c010000045102030020106002400c42b4801800030000004104103403094000d6803d0056100d2020701d4041a510030802d0008501e25420031038560500204c100458001c44090f502d40041c800c91084500030104542008241c600640300503026030410004074020420281c0150340c400d000e803c101c48043d95030354410214406ca540141028500c03110b04085d55902805240e186000500c0c00c1c0d540c03820f0114032540c0e241b42c2c0b14030400b030107036403103100c841045007611030300860b41c81445c1911240645200060058544112400d1140030003105e0006410300503082581600c001403d0b03803240308c102d55103000003035001702425602c504c958540343c806014a000c5e595049a54044041914240800100c2c244d41400d080101003040a55060080b414040e40d002c5080038480408038208000009803d2244181c40c1c0488865a0201c01d20080c1500500c940d0400507083c0e842c590102d0071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 921391771 1250 921390521 921390559
    0x3030e130501301a072010020d0603020a030503040911070506060d0827030d03062d0305030d0b0f0906030a0f0318170606010206090d030c030b0603040b06 68
    0x90080d800f9801030a00a200010218095000024020900c071001400c2548402013290300c0d1481441c1105101420464081d50020720044101190341c6098200d590f1a60100e440b4204144c402032596404145100c0c1402550001001150003410010480d52a070034415147c1e03015005401e0040d04040c1c1090000c06040d08a81c101030300900503100c01d4464408003e80d0740f0100000392a00079080c17100d0040710203041c141c40c030808102045000108402e200f07040c00d092a40038a80d0030305140210030040c1d07032000300e030520303100340d540c0c010284241000006040d0b06c02e05070005801840302080d90340019800740d0019240100881c0d2a12481d0102d004002607204201c0d0b10a4141e00f003251a880000c06030b00c0c0b10700c1c0491090900400070361089035551071010b41580100c0f0702c00a00541e80c24440d070140400f90b0001428400350004e481d001c03542035a908480301101d070400d692030358800c440500c03991282d039015400411842d603074103050070440b9080c5802c0e80d941f07200d0b40d0548050802415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 921393021 1250 921391771 921391781
    0x20102270604030b040303020405040608010b010e040c020c060304050307170304030e0307061706040f0515090901182303040b0712030b010801120302010f0f0912050408070b0a1803030e13 82
    0x1030014a510719180c2582e8500e00035620281c02102416001d02001c1060b85d0355004071006043c0740d00001504500c40d5000400300b2078080d02041c0100c1c6040c035511311407540425408604030b429120310f6500e8903a440c04e5440c610800d00080c006030441800b03100c1c01c2e180300000718010360282d69070890030b400c0744c7c1c10941c4403140c2c0c0c85000c0200e400c40078075002c100b100110b000c1d40218014000036820306041405020350304100e8000e0403840501e0280029442c1c000303441904050500000c000d103440c420201804610701c8000a40084200d100e80742e0110940f1621490854a240982c0e071210f40d00c0c508851141c03c0610110740d8603101c140c201d8500352080c41000381801d0165100b41d103603441c0268014919184806c180c0440d505d9031350500020700355000e00c0a009045d400005503290043c10028501e950b1030b03402100304030040008116600b00050144161645d03c81c3c5a40e03503248012043d2580b2125503601c48010758900000002d054000b94561f034080340655444130340329044036151003115 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 921394271 1250 921393021 921393097
    0x14100807140112050c090a080c0a03060b131a091608011703090d11030f03070f0308060f03100c02010605060c031b240604180b2802040303020102 64
    0x19000031000c00c40d011a4a03454200d441d0107042040f15015100940380c107440040340d01200c07807036000940b000b040c141005400c0081c817445003c1e00c152040c00e400210840c0181c0300180c900d0791901403001382d48c3c0d2641c0d400d440c00e040c0e0f00c0741004030300f5444502d41e124907807941003d441007500300c001581e40005290000705083c0180d40b40d602030303801c2248a09090640c400e40f0001ca10041c0702010032900c1d0000141003803401208015138030f400007009c1500d17250360700d02046e0305c2d034005100040004020703180c1c0c500c0065241c1000f141580d28100890130407a10340c5440fa52612a0001102e10100141e204101e5078559034002d0012948401c188440d5114034a6032903401d900400118142d01480c10f40c1c10140d05201e01a02d090781e450300003102100d500001284901003519081c00300c0c51919204240035410b418072505000012520b544503202002408041c0c0522280001080789840440500701e0f984180002c40d182d80e281c1c20300034003d400c44049049805104410b00001030f1520320400719503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 921395521 1250 921394271 921394273
    0x302010e090c0d0e1006080106060801180902060403080d06050906010c061505041b0e0d0c050402070309030b0c0c07051c1e05030d0c030f150603230901141008 70
    0x1000c0954288400c0c260000c20903096900c0070720040c041650180103092600c0f5600b4010300d058401072170100200c40142c2c0c4000011380c507000d01001030542080402d4111040256203458a89174405410080c20901e50020f42c0600300003404800c00c80654080d000042c80e04104104d180c2e264010300c04181c400b514a20301140142c500302c2c0018540d900403a001381c17249622210100e41d5030b030202c1c0a66080d048960304580020b0114200c107548030929a05095040303810150901207622584914205401500e010f55000a403507010f2500030101b550095502c15409112031415010580281d0071064208481d40102007002038a441d110000040d140014034440c41c0d1110103503503200d05001841003101c50f100762081c810000c1a400c0c005045900d82c44100031810441d1000002e084034408050342003150b02e0aa40e4030840d400070000c0105030351080c240083c51491941c41c1445070f122036110064003900c14000c1140072407040d045080d0002c508480b2070f0480d00d4050038800c40c001e140c00382c2080c3d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 921396771 1250 921395521 921395537
    0x51f0503100b01050903060f0f10050105070210020c0a030606151d01030510080601080109031101230a1104030c030b070c030e041104120b0106020d090e0a0f020903030c060f10030201 80
    0xc0061039034801100110141400c1e4a8814170070007203401e001c011103821182041400c100902102d030080d01550204c010803110315060304050010786203009410300030340120f200c10014000c4078002c1111015240000b04652012507682c40c10602a000f14029030302e4400b560102601d525014180100c0303141c051140006520300701030011802007030024a8850001406600001ca1040502a050280005c80000708100841c0d00b0046c00400e04101c0c021101d03890182d0f1060f0b030110303146440541103c4c10210311000c0d11103000c00f501403c5200b41c100d00703030702001900000300700d05442014220380c820600c0031015035941c1016035001c040d075400079000c2503035a50001c1552516030f010401d81d0043ca030555040c140c9405600c4234807458a5030440398950101c3c01401080d0301000180c5d00b000d103c0c9403800b50f071810031940078829400900380007c0c460300c9001c40f40700c00d001c54040d41c2070094081c0849031180e1401c2c140e035644200070707681d007030810500201240f400108005803170f080d2901a194256 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 921398021 1250 921396771 921396793
    0xd06020c0618030f0f0904020f04180c0807020d030c022505030609210a210b12070609091a06210a02030606030601050a170a06053307050708030d051f0503 68
    0xe0158086c0d1407242d4400d03400c2248800042c0b4590160015004241544a450942d4400c82003240da10301201c805011255042120301c69001030091407007042460003042e0b4980d5507200b41e00d441000c10640848844544c244a04800001c039440100c803c00c0b0101c0342c60781c4400002603101e03051002013900d031141c070302865005022a040100750000303881ca003406076505182504161045042c4008091946501c6641f1f41d6152200340401c22040f41c4002c0c00d0200c1c13070a50050688907039441550b80303003030300c0e002c3c403040c00c0d002906200c403050005000305545080b03101413494070408203405200c0140c2100041100513101d03100340c84c03051901a04c5a859500c80000541d016003080c001142080a802c07091000f03820043c9445000307225004010491905100402c9031201418040e9500308094040361419202220001603540c410f290450741d940d18030341007103401e000c81c40e0070440180c440028400c1070210140d00103445802c8107a03104084826803461641c244826100300d6500d07601031840c00c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 921399271 1250 921398021 921398047
    0x3090905130f080409090c0312111e0f03030702010516020a050a0b1f0e0907170a0609020a030506010803040611010b0109052214040203010b0604081b0d06020c0618030f 74
    0xc40410300070703c03080c0c0c02d051380c4100c0e001c01d07a0324100c001c40301101004d20420402240c140c0d4011401004e04100400c0e11500c40c20507034030481c01600c1c09130700b103030120b00c000c02440034481d111440c0181001c0c3d070390303078540140e002e40644401d0f0b8014034a04100384000140503c0400d003210701541c44400fa04115215485002002e94081c124131403001d2141c8040c0ba00b0102c0841c0c031801070118001050040c9403404400b41030481e00e0f804182c1d0701807060b8941c6884207001c076148c41c1c1541d00c100300040f1501d0f2400401c070504c200c2d4000070310704c0c07050138008926414004090320482d03030960b441c13400e641807a500150030f0341c07034034011745001c00d20020040c0210700d440140d99421581c0c0340d4408042d0840300110700107560650390012051142c1200344820f605003800750203201001601c07418a450f24018101d565803101110a01092401841c01c2403680d40c3e62001e10400c1e50000410b54440030f2981140b625040d058482c502c034216048001d444c581804401d440000c401142103c0c20000180904c1d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 921400521 1250 921399271 921399293
    0x50a05070f2307060b272a0f09030609010207110a23040f151809050a03080903120a1a0910140a0e1018060521100e0a0309090513 57
    0x11a15161102c0e00648144c44034001b4520820b24251020300010607515981c10000300a0a40780c1020051501710004001c0b01480c1101c034a0000403141e41e450010000c11410f0240c545490fa26003e02d206103d01c0d0101500135024450003000d440204803010b004000c80c41d4080d02c140b41044c0c43c00c1011040b03101703910311050f40b0110007500100d0024120b20302801101c10351170462089200c035075401d00000031404d10800206080d10410843c408240e2249a036a03148074000400304145c144c0024502001032095641e100c0112000d20040d040c0401d24801802d0310700469080c00002c44202c00d96407820b801003d002d41d40012180003458200f2125403d6608038622140c1c110350101400504220302c2b142d054030075030703608505403415400e01071002c254294182e4030311012810500180219550035a081103811034001c4034190050740004080d06160303641400e0305a440c0351060050920401080c6006405c0c820380d510807d064032003a26034100c1e107080c0c40c1070401740250020203000420240ea4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 921401771 1250 921400521 921400523
    0x31205070905060f04061d0a0b0f0909011203080a0b0f010c1106070b07020f030f090d06150303231215060f1303020406051212031306050a05070f2307 66
    0x1004510349690114006900500203c40213100c0013400b00003980c0c1c4102c8524444894160150a507007003d8000b5070840d1031801001800c0c0c078000f4001030701c440080c0c11120342ca03002400071492036a5400748280000e81d8880250301258035280001c0c140c4036144038105040700b0091170110851000001100d54408041d02100e04101c03411a480c1e860b46d804010b808070714407414100c15585400c2000a01305090743c20704c540d03030f40d0003804610a042400410b4840001c03041c0c5a0804c2d1460608100000e404242c0800e51480c0701c600b40881459030200e042d000e00c030004441104040c1154110a000348100300c0c3e031140702160b03080171903a980c480b4051040c5440c0010706850600c81c00f0300996003150f00900b80400c0c0d20024440810450503d4000c0b48020102200c981c02c0d11107100044035107610114119030030300764001001030640540ba1640d40c0303078160096001c00c0700d440e041c0307a514000c2c4025079100004c942c0d180081c880891048030004442c01c1107040703d0303403900402c1070480902c1e0400c0b2301c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 921402877 1106 921401771 921401777
    0xc10020d0206070305060604031a090d050403050705040b040912270b1218010c0201020306091b0d02092d0109060203040620033f0403120507 62
    0x4545038408050700f03010521303a1b500c8001a11b0b52046400081ca076072803407694400205c080a0407140300e0340104c801c0783d060000c03606003a03c40d0b003c0c030710000344681e0007940284020f050030742249100714009400031641c0c80c100e0b80c9041104510100f0800040c2500c8000101d80c0707846038007031074004681d6408070040c0741001c1e10540d0314800d240494451404400c0881c641038880108010807002c0240200b000c02c00c83c000003030203540242c031020b10509550000c5110078001c6c048e00c10b40f84980b401094a0492100c0b40900070b03401030881c0b2503002801c9034412002c1f0307146100408444040c2e04e0401c11400d030480001d0718841e8030350000340c11076000780402c0c40001e40000482210320035020502002c000340186142c40c502c40c0d10740700482c0c008000316090002c0f10060101c8015200941c088008030030781d2030520103044085030060001081d009107071020300d0443e404160083c1e5249 = true := by decide +kernel

theorem cover : BRFrame.Cov 921223021 921402877 := by
  have h0 := BRFrame.cov_init 921223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 921223021 ≤ n) (h2 : n < 921402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
