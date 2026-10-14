-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3579
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:04:21.215258+00:00
-- url     : https://prove2.me/submissions/5baf425c-be19-4142-855b-d8ed4ee431a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 643525179 ≤ n < 643705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 643526429 1250 643525179 643525199
    0x150304021215060a0801020c060402100522090c050403031d0f0303031f1e0302040c03021b010e010522030f0e040c030b270406020a1701090507020d0e0a 67
    0x15005000a150201c100441c401d480d040071421030812540c0c00341c1004200c1642081210340e8000c09009008601d000c00032000140c5403d070181000b0b00c50072654600c01803447c400c074290b94605800c151f120008820440303100704803071024410201c01d203080808060500c0c1c080c00903201101d40544980404100d064031100e90505860110343c0d010501011080d60754508101962090700c1c8001008180500440c40302043d00096000c03030042d000420705030250311040c0e5441c0085980c140e40124500151410640107406030107501603501040c60b4040c8000c40701500049585803401e00201f000381c030317070250000210907195002003a5482a409103400244100054483d11549182c02051101d410700014280c0b90407aa90304000383d101c0c82c05112528245600180460300b621140c54440f20070803010010071402000030f000180e004c11039612950003850580e2405401e180b90070040d41c1c440110000624080d03070b81c20014458090014011130090803001741d6000c0c002c104443c080d00d4a00584 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 643527679 1250 643526429 643526431
    0xd051606060f06030b18060604052e0c0311070b0319061a0406110d081f050406060c120305010b041202030109051e0d03060e0106050c01090b070905010e030c1503 71
    0x4810540d24900002d0044040700d0b07500c0a050740360b5000c5000d0516608201c45203140c0004210a00c82400610916a54901c102d500311a02511a07040003030000d40e00e4060340c5000c0409450215100402d8945141d10001e00800c503482030303d5004206403c250b001d5a41c0c1994081c1030707400002040072540c100d07040c810140ea81e4000543c0801d001e80c0380e1140c800100400b8000d1009800c0115040c0485600030360780010303064041c0000d207201207001000800114010700b41c0c961080d00700556030541c01040d00d0001c0900b401030702c1400b140340c0d82c200003000030104c400e058800c5041c2e2034101225078400e0141324100d4281c030344400d060600308018840b002c1043c1d074003203a03d1b65807007041c140015002e01444800500d1410424540611039480608000003c0d60881c101858001c051101070300594840b81900c46601d0020b40712000c003900c613801000004406000308124600b001941a4048020400d4800a0b0b852140714440c0f0414142d039400403001443d4841071b100610004244510061 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 643528929 1250 643527679 643527683
    0x605040303110a021806030c01031109040504021c0c060906020f0a140109060504050604031106090d14071a09011a0901120309030c060201050108160e060f1906020309030d020d0516 79
    0x6201c07405402d07030014405c080043c0d00300c81e521022604001d05850300740b1080074401e2081c20103014406610001031124810102c204d0304c282d90700c902140954a4200e03401201c00351143c01000940e0f0343d424041811651792003000005402803070f001c40c46501c007042501c0d00b00766a00c002c1020b402a542c3d5800f110325100c2601e40e85640e03400541d00440e24a01515019a015801900083c28282030081200c00030401070a0190321100910818040000750007810117414503200b00545244d0072420504d1050b101d0180000314048824030740316554928071409008908000c00207600421100d580240a0109246d030140002c4010410407002803082e6207203d00c280782c8010304a8907981c43e1180381d20150000c40050b07543e44c0043c800c4030020009400b80f07240c1e80d0586055075283c040e043d001460300030056402050704111000c516183c540d10881d09400c208002c0055607241c03103009540342c2000c0c0b4007500c80c1c4180384c0810720513030020512812040c1566140c501d0002103003407045800e1816101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 643530179 1250 643528929 643528933
    0xa030b0f07020f07030804090e030301050105041514030f1e0603030d0e0709020a0c20130f0b04050108010905120403030f14071505072c120c10180b04060504030311 72
    0x30070380b190b030700340101c1e00174501c601405600e590170042480704460b01e50702d148140703a000b0001405580c1e000001e40c1c0403a00c0000d0b9040205000501c100d6000401c8411180c50341c3c0c0110a01511300c20312100a81b040440049425054800c10044040c124060310b030a60540c208020350300c0c1101c0a0340251100c42520002c640180ba40d07070200104070380c0320600c142e0002d104d0804000c01c116406c401d545d1a010300c1c01c404210190541c0000c0d088602d20280e0181040e40c0303841400c5c000d08207402200c1e43c05001081049a981e68420182c06003d0200b0101d4079030051440b1020000d0304142076a040e07030b400d44c2c1e0307000c01d004c401d1405841090010400001c03040c0284803840010f29299082d412824985c040450507007030a00d005030140082d0050703070001400313405522486811561410390001011180710140e00c2c070302c4040e40c2c01d1210079582c654020340305c2100300750001e401c0309600325501245448410002d90724041500382d4002c0e03005481c0000c80810080012900c91b6212030740c13036803501c42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 643531429 1250 643530179 643530193
    0x10912051b06070305091e070b030a091403030115021c030504150207033c2a080405010e182a19090602070501080112050118060203060a050a030b0f0702 67
    0x11280e00c1c210b03080b6000400681c450302000020346042c06807910b0b90301c0140d000801c0c08003612040da00c564071030144680c803080100020700441100d400600b009501b09200911004110040c40c1d1290300900a440c0c5151a0140c07020289200042c041000d00c1d0120040b00e00d07002a040c02c9000d44000740042d202507101c44100800780f90300b84000c0030003074400e0721104019103d94904140c12201220460000070071209e0b55140c26909982e00c40303200d2400d00e401540450685000b603030034054490f52404045d5003403000c8023007105c80c3d001041a14400d27245e880e50f000160b010080d036800d60703105a030401c000510201c1c50b60740b192007070060300007914034000e01982841a4050000e03005410030103075805c0e42100240110350800400c1e0f024000910143c0b03441418240042d04015043c800c5038008600704c0310000502100703500c81400005042e140000c4000350f0b0078804041d41082e03c1e41803203202c00e01c800107000c0ca0b0485d40c10046a030310100c000c4107962050220102c0c0840140307600c0c15401403903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 643532679 1250 643531429 643531477
    0x6161b0f05031b0c0d05030724060602031c020c0706081312020604030e03071a090402070c120b01081f0b01030f0507020703050601090c0806101101020d0209090901091205 75
    0x440641102d0008044140f52030f111058003a240952100040c4c1c0141010300d40840850004821501215005072204020071500d4900241c5131164159040c80213240480205005a000c4010301c203001410080b5520340000c1c1c0c940c0c0382288a21200703d42d450340496001c1114a0145100d00e0307000c2c441c0e21100c40300115585409405000c201040c100580003141003004054211818011005003030300241845414a21074040020034159083d2513040c01103058141c0b43d503142c04503050154041041c0e49039540d80c04101c0f4045144000841d0b28040300300003c6500f920019184200040c800308400c0510f14030581640141014100141015142c0e002d24012000c10b0007402d0140d19640d0007001a035246091941c02e101040c0c20901c1c01034100311032002c00b82d5102c1c103103a400031002c0300c1e4411803400b1110305a54503d800c04558205500211300ea0750240425070184c00910f0095903440e0166480c1c403026400c8036004100104071031582c10994100c40d2041d4054203e11000e5640c00070450140d07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 643533929 1250 643532679 643532683
    0x30904050c040302010201050a0920130e0309090106030e061b090d0309080d03090210140706060b0310080d120506181f051c020904030e040c02010e06161b0f05 70
    0x407a220444650009810400c42d40d091240c2680441404000c0196440942d0383c0e402c84a000480b20381c20340f49401103a41c59540c0e1164000c000c025099041018010b0b0081d140c5e2644c112401c02071256003c0740c00000d01500074040c81101b0ba07400c2015041d01e40e0b681800b904000401c0000200c108400d20495060b03071500404900c03524002d881e03902c40c1e14988070440e0f10741018081d42c481050b04041c00c030801605c41d0b030b483c0e542150050070000d940120005c4008028000c0110240401d13042040001d0328499070801180a4071540000114594980105070b640d58400c40c2003000041d8144030090f15002039074800e43e04040010014100b09001081542c900c0ba401d45071040d05543c00001861400b007032050450081600744c5819980c0c10716a80c0c94045461441c5000c0d00844072200010304141c03142c088c0b42c2014400400420400401100c003d00070119445d04200c40d11800300032504004452145030284401c0d0b645203464222501140c10071161803035000c6680c1c02400d03100784000303102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 643535179 1250 643533929 643533931
    0xa0e0c0f0c030c01050109051305070b03060f09010303180b03070e09060f03030c06011d100603091a090a0506010b03150d060b04091a060409020108070c110907030f1104062003090405 80
    0x83d0000200d0341c0e5041c035500344d0840d5000b0300f403207d000f0324400c0e602d8005007000c501c00c401c075030760720740405d8480c0d581d007000c181603054103001c640d4048488000402090741200009403420300b000000130205440e00e00b0f9803036600c015121180071401202441c0c850746800940e0075441003000e8503136440569254080391441c0c0207090640c08603000080140450207604440ca005104040d1a0f0741160070464000c1162a0640c003c110402d5103401249091041942d4444001c15002203044071601e088641c20361907544805040719180035010000500313007200f0301035a0294120700e0500484654040402450b260b4141085034100d8461800045503691751003020341d694007808140b030022803060028250394400030640da116900d44a070a20240c0d030302210135603109009080140200b0b1850409445900450500750303407082e1007004002409507d40c101e0403c0003c2c24070103001102c06040f040206010342d001c1c903400245400f024004503001400686c0a2043e18410b981c0b82000050100d0207940d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 643536429 1250 643535179 643535197
    0x150d0b0625050f100218030102070c061b02030a08040905072a240203010501020d0c1703041506090b0a0812030601082a041d0402011d0a0905040b040209060a0e0c0f0c03 74
    0x11780401e8014044000c08032250208100f20700031407900c1e2469a4000402510b800745004001d02580c00c0c140f20014400280c2c1480d0f001411102001d80034a88072007554002c1c01051440313410803010480e0301f40601d880c280700d110043c1202001184803160080c41304100d00c0203640560201400303040e0905008005801c0501c015005039607036040c8000a031410551180d45802c025100d03a00001040076070000105103000c00f000030740d490312141000135010140518155626141000001c0e40c1d80340366004801d070341400d880c0184156a11884c4584845070580d03549111242000005c50a601c074070340180c0e0210381c080510f001c0c0419550100228960000030381200d04001600b40b09140003010156003100c82000558650301d420b0340024086181d0416055120310010030034202d550314045488c0141160030003c21061600e400c020180240954040c2d02901001010842d2810641b10742410780d11518440d0b4425203494000207030380d5004214482000d601480300c1400b810f401d10051040c24 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 643537679 1250 643536429 643536431
    0x12040809041d0106080606090c041217120604060f1d040804081f061a1b24040b06041b050d15030f03020f010b0d06090c05150d0b0625050f10 62
    0x9805c041480d860020060481440394210508024804c5024012202a90240c07040c5281401280c58045880b984800d002d000d074060100313250b0000365400c0c071a5403003007000721024005559120a00307103000505003e00c1e40007440c600007d460098184211642262044031103d10f010380d520060f41c1001100c1a83c0e17100b00c040e055190b013522070309000c0c3c00090544001d4048110905d03241c1140d05109142d601070402c80003124070003590ba8107005450440024a41145010900500200207070038101c070101c89000484010800d14140b5208481d10302200d0140d9103144c4030780700019601504001c01c90b0308140d441e8031a00c1c03001510aa41c24004521418915004400300d190107810b1001291003c51540c1c0b4010490049640382005120501e0700f2000028150320306080c00d0006450700c4c0c0221f40c22424042002d030035824140001c001444000fa010070140711084100f00051149410410560003448680003014503108150380b04140300d4002c440c01c2403c948801424030320340e070b030358440c2d45 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 643538929 1250 643537679 643537691
    0x13080a03260601080115031e0b031203040309030209042d020907140d020d020405030f1606030203060919020d0912090605040e0f1003050106090c120212040809041d01 73
    0x7502210780080d0004900e0420024901100002c0c0805014441c1c210452080d07901c0205403406a846401c0002c5ca00790441c0c0424124021040a020f00410260103446410402a0b0b2010840103a0703010380c1c2d041c3e455160b054515001c01c8485180507000fa43e440030b40080b480040e400844801040241c0c0324100e0218a0541c0104041040010311500c01d021025032050907002e4804112603d9800d0520300686555450728410001d0156801c2550035206040c08582030300c00000d0460403c207945c000714140103458120813001e03800283c915a4200310484040780000807408180000c00910000040c14020000d840c5029201850010342d044004068048005584181014003400171410103a18007441d10030410351413030005010801c0c201c00c0002040d100802062034000841d0030100901401d920384c0750340402070100f8001100070035100302c80740301402020700075201e000c4e001440b8010300c2da0301d0b038a49210705c1d800790bc00c882d032080d5a018200c9050b02d1001c0041188240385000040c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 643540179 1250 643538929 643538957
    0x81f0e0a0e0a05070b0c010f0e0c0405160503040818040c0e040e0a0f1202070e0108150a090305090f040f0f050109110c030a030c021905160611100213080a03 69
    0x2101c60741d0488810710b421030002c690214400082040445042490166891644e204200c0c01440c0030002603003ca810308a003483e4040f00007500480706601190304106030340311506880e00d0030b032251903600d010038030900004c4c001c60003110150001c2005042080000b90752880003500f00e43c030b100c0d014400300d403000038a0f04080c18503210700650420000010b04101e001500d80a401404816000f001888585a0354620b90310074018a00103003410010780c4000d584800e51241c40315031000d8440071308002400050a007448502503415425015107901c0d03e00a8040d080c44010b80d4080041c0fa00280c070340354031008410441c400d40454003120200000c155040a45032000da480d540e000ca400c0680070300c001400054048111030880029080000d55080d04031400c0c0e041443d80b40c1c0301a0b60800f200182c009100e00407610300e2803a281d00720a059105d0b2201c0081d20400e1011088042d280c5c05010a2003074200254002c041459640208100c100d503140c2c241840c00d551098120005500e580440301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 643541429 1250 643540179 643540181
    0x5070206040e0f24010c060b04061a03040b09010b0906011107080607030209031002030606090d05010f09060902030f120f090409150606021209030613020f03060412140f0a081f0e0a 79
    0x44886140780c5244e40d0028400006e200810441c005480740e50745171828889641c0d42e5008500800260310050200c0076545240c010f1904115419600e0500701000101104018812120040402451034840b604c4e410011210072149a0384282648201f5034003045004080100c9841000240d80140c1c0d04d4203c50141030414500e091000c1c4070302e00510920070700e0742e14001603c0d0031800c1600d070403c1c618030905166001d049800c001d151040c1c908030048041c04102e810043c0300c580260115030400c1d01da810000c2d41c4402941d07030f10f00200401e0160044401c0800020002ca69000b0404a182d5106458403414038010405030414a5a201b44c108480380e0140b0140d1504111486c1c1759050070791a00200380ca58800070913420310b804503e0150400c650710461004640500076048601c145464580364180002d0044102c010448401d400711030202d88000702c80a000800b80781c00e050086080058900300006081009a66040390009160307160844107940104079003451031016007080c1c58090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 643542679 1250 643541429 643541461
    0xd23060102071703040308070302031615060605120f0a0617030d060b03040c05060a0c150b211c05190e04150506090d14011a0909061605070206040e0f 66
    0x2420707403030301c02a9000f000b400070040d141240d40201c2825521300c4d1510342241581f01b0842000b01443d00403150009010380c403d1b0209403031050b504200086c0ba03c6090a0b01d1502901d40c203104103003443c50000340380c4001d074400780f5000300b100c0c403010a1040d2514800b039081082c410356081194030108969810440074018032005040c000807039440e50030a070300c0d0462441c25501035203000d82d00014200c5400303803103150010300440e004402490384a400e0115040540380c0c400001e81b1801303000e142d480d54841c1c1061008540030101f0300620640450240c1d5014020010300240c0c240041404104010401102400842500d03a42e61481070800340c0100300803507074444500d1403000b558090501071902c0d034204072149031004a0703030011014014905100c40c0c40ba2910f03181d847c5c1d42082111004010080c1040e00307203200c00c60b5801166070320300c522103640e482c0c03c6496041441d580c064100e1050b0142d03005124040c009400c003894075450b0385042d0b0030f10720300352420703113180c07091804002121035003840380c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 643543929 1250 643542679 643542689
    0xb0301020d29041b050a1205090a0308160c150908030408030a060b03010501090608090a05030c07080c040e070b0a0203070605180c01080705030105120102130305060415200d2306010207 81
    0x20081342410b040341e4070a640034031400304c092100008181c103038107001e1020f900849807603940510030b500d002d02e101074907030204840032004102110086009110101034171000344690b039440c882d1800403921044003400404e2000c801880c2d5900703c40c800b04400d4401140300318001c0c03200c5543ca0a0074008202154415449030030441014401404182c6e03010920318201c0c1c0d0070303107085415610b924210300e081003201c0c0300003819444005481c2d24079510202e02c800c229030000054404800c1e420302404180c41513500b0541480d00803403428031025480e00d020300b104030010700c110307420304202d5560f140864009895812000c0ca800a6400461100308600c1e00d20308000e05e81003440341014100500b05001c180107152045081280d00b580300345095050701d0a0f60b020000090200f6540c0c20116182c41017501c1c160390150034018084440881401040103400d6851480003558802e20800f00841e08075001d00b0322034070780310311000110100c180c19800043c001821410541d051440003e4540185507003c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 643545179 1250 643543929 643543931
    0x30f050c130f05030d0302030a2d06060c08041707091104030b070c03090302042003100504150803030109050c07080a09060e012609120a020f0d0309050309040b0301020d2904 76
    0x3d00964502180100c40e6945508001d6129155a01828050100e0544500c485030160840c400503040403803200b0060161000200300305600c80780201c80058481c0405820540200000c124902040b001c41c001c41090409480c0c90a444807a2917054031041d08203501c4612020a09006120300c11061513040015410107101154169401401004251002034411aa1842022036561070921410303640700c401c00c0025a02c0c5488440a622f0064a0151a0003a40340c400d003450346034602d568200039519182c0065003160710744101d0328094a001800c175480c0400900040c800113036054040e0070f00018640f6601c4119040513030007031200d480f2001c0641008655035000c060f25000040c9407903038000300b0131f03000080c3e50b41ea04030320710340001a41404010a00042c50080301c55001c50000080d0a0704e400755100215411811401d40d49082c00281442d0810401003240d85825400801550300290015080814441c032071012503402406000355100f60782c82d014140381210751340803024641114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 643546429 1250 643545179 643545209
    0x702010e0d0b06091b070302070f050307030c0b030a0219110606042f070c031b0e010e01120c0e1e13110d08090904210e06030a0c030f050c13 62
    0x3281d4215041c090183c5005a41c1140811003c444007040c50741c1144103640800d40c0c5000c9032900a599000c40d20035803261b040d00d0308021a02d440c01140d140200c0390400c1c21100c10a0800368040801d40c4041e154840c195030030000f036802c9101c2103050812640340e0380c550406100ba2100c0060034401c0052100d07104500e040d400d070b04064180800c907000c640500304d049040d001136584080181c400c02e4000b82208601c41e00001c00c2000042c0d14218030321b0400c0c2c00ad0f452642c3d0344e40d28098104203000720460807110340010f00200407041005402240280307030b4a400c10f0341c3c03420f0340314103040c0c151050701015a92543d0241c0d03000d5004c059540000314200350344020120b0352505d4648940003048184120385604018091102107000e850307190000030b1103000c15051500e00040010000e441c0c00544071a01400c690b0142c1c000c10103502c02040c0a0f106500d981e8400148a0040603549000310038969540803003100e402d00c6105030b03031042d1250b03006170756640c1c0e02ca03160b41020b40b55a0311242d41c1c200510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 643547679 1250 643546429 643546433
    0x1903030809010c1e09050405010902032203050406270311100219030e12030f030708330406080f0601030201200d0e0f031516110a020d0819050702010e0d 67
    0x103c0042404811a00e14138013140c4401c4080740d031400954046a842400e080001c9031104440d4015402407003280401d81d014050105c442980e401091809408118107000402c9014059011254180040141800070b12100d040002c080041038005403820b82a559020303203203060203c10000d843d103042c00207050f9840c0300d02c505100c0644002c00103080000030200d0200075256595544625100c901c20b03640c0380d1fa2000100c00a64000b141c030400001c0c4441c000c22191001c04440b9111b04091074820340f0316803020302d03d0001f8441e41d070f44115086503403903400090001c0180322002c20b0481140c05424694510700004094540c1680c40055441d104075520002e044001401e201c00c484a080c04503003c494000090380d085030440b032068150203200c031108891001100c1040c400c0100340e002d007203895240c00c07048500d090303d0f8071040800c0c0d0221180d800035207000c4c01130152180c8601d038000d04d06010030504402c0107045034001000300e1404240b8608642e08025240400c06003503401162800540d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 643548929 1250 643547679 643547687
    0x10021b06070831060c0308010603090807020409020609031b0906060a050d0b0f1002010c090f210525090507020105100311030a2a05040c200703021903030809010c 71
    0x80f400b911404400040a10301c0400340d2030008180d141c010b42040c3d42c69076a1407024148403000d0000710005401040040382c0d40e406407041722800347d00035038044c0c18801c49a003400300500c4084c0c2c05a0f4400c10a001c0000990303001c01203d002c001c400c416100940081c00c06020540a001e8595407140c0000c0c000e02c091154040e05840f5280c034101c1010600c03085e03402c041843c00c0010b10b0255089500b150450313a4481d0150440e16404a155075691411680c3d01c141011a0785503003d040e1012656100d00c202c49500c000144c810f40340104151901c600c024010842d0448030701e1081c001103403486c07400b0000340d06035100d1140e100c1440d0000313100c0c5285c103920640c101011408001e2510510440f8210140c808100d0b5a80b801c1c0c0c05030801e21401c803d51050109031a101b83c07605100e000d211008111400c0601034030604100c039456000c0e01400e5403038000c0d089840705020f0303407091040150000c00359880f5038881e110300b416071001820980c01c6080052050100408002d4581c2c10003e04034442580 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 643550179 1250 643548929 643548937
    0xc02270a14130804121208070e0a06050a05160c05011107060c120203210108010c0c02090c070f3002160608090f1b0103061203080606030a0b10021b060708 68
    0x200d12880d001c1c2c0851901980b0b50169400a0425845201111003000700c50f0760750481000e12900c1d44800c40c2c3d202c0d03604840105403506083c2c2c02c419846420040c05018070081c080c10041c5003412410415500e00d14404222a802c040e80c11489039401000350b542c008100c011814a14005455864280000070344101d8462200602203241c20180900e40c0d442842950025402040264445584140d4192400500380140d81c81940b0b40303624000e80078003412500c076607258083c001e00501c0d60345000c042307465000800103a58050010611000040c08095810404004040802a0040341410f0b21840c10148801c140940d417000d5802251591020450400c42d812858001c0e103654500e8070303060034009102c17046040307071107045a80001c030001c1d602003003d03158082c2d13402c214440d90340702c0740d0503040c2442e00301801040148001c202141420343c01968042078503e408250340c0442c00114411462440510006800415030f04a030411640404090004d003102c51600b822140d40364200c030303482 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 643551429 1250 643550179 643550191
    0x10b03010f0b03071e03320105100e060d0203040b0c090d0605060102010b040c080103141504110d081b0c04020406120509120a02061501020105010f0302040c0c02270a14 74
    0x507003c40007456441c8075105070814050104414030381084103603409400791000401e82d07100d030441140850420100890143c2200d50f21001300c40c1c070b0b640b0307107002c1c0501540350351407640402540c48400f04580e01c458005280110900f5001070761b81c9440c5c144182c10705000781181074144402c0081c034150341d80b05012001c038181c10410020722511041c0050340100340c1c0c0350703c030b5401600384010700b1a407a800c00c500d11b040b24002c440420500603180d5800d6241c02c001c1040001c400c0810004c01c021401e00e60020f003201c0006000c0c00c40e04102da8540300c03540c0d088210031000708d03503001c2c4400c20000010302100c0100d64003500c055050078103024001d0040000034410001403031b034030400100400810094400c585086042d81d55482452160080d00d483c401c540782c00210300c164a04a40307d51051103220304031421071803076105141c15942000041d201500c0c8031010020340143c0d0f00056a50303290b403042c18034049401c43c10a40480b210540c00344100812200d4040c1c42c10301d08440c1c0c1280e8900481e4095 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 643552679 1250 643551429 643551449
    0x70e06040b040608011d010f02091f0210061203030b030a111212120f01081504030c151b090515160314070605150910031e0f050114010b03010f 63
    0x4190900401c0040580d980328085540c00c00c1b68803100c0c0c1300c80403071008a4907100c400a00840300c00005000c160b1090600c5150000307002000120045c4907502c105031504514415540d076811101c0c0740320165041138021000a60025001d24200741e010310a0f0100010180c020344a941c02c5602c61234080038084250b83c0c061003452115440e00c600601001c441d40e12425803141e20b82540504c00302c000d007001c41c0c1c0c4021019469002180c0b86000041041c3c0c10030b20350b01c0d0783c2295a180c2e501140c00c0c10b0b045400301c1b4082d411040b5008600710600903502c2c05d100e0b0304c211061807034070043c1c0200f15900c191300041c0691032010f400c5240b911050102e4003085004e40302a49507000781c2c40c0440300c0100d00061b01d000480b01140f04000c02c10f042d04034a009903407402000700102a02d408020400e03409847c040c8920144103c00c0000440c4400c405001040c00c80c100c1c0c000818980321440303990f800201c119501d07592910000403040e035085040d07000d010140c10b060304542c1404d04034040c6244a02a4a10007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 643553929 1250 643552679 643552691
    0x1e0f060315010b0417060103051f1d0a02100e090615040e040303091506060c0b0414070902030103050613030203040605030a0207021807140a05070f020f0a0303020f0f070e0604 77
    0x103031410401e1421800038020141255030707560308810800e03086400780d041507168100c900c1c0811900050540e050300d400c400500300342962030780d00424042e18072440c06141c41e203a40c08c050200c1141c030320302701c21000010003030010381c00c043c0304020074004203809440910107018482c400e243c4800144075406038007034585560000c1501402112401140e02656101c00864100b0040682c950016080180700d01d41e202c280c0c03441d07604040142c1d451406240e001800d0640082c0c0400c01c1e0300f10b01b40c1c20034064142a143c50300050440d40c10b292081e0016810540c0000c01003040000c03c100a9902031032071404224a6402642d00940303e110700d120ba2030400c0004400f04601d0301c680d90455a0342c40e401014901184058040100c5603102251103801040d415012650f03414140411076680c40c00e00d0b9600c03450f1070016940c650180c0287c18099800c010b421240103038984a03085500c3c05075000f41c00500c0fa410364242068500781b01d510981525810003d020440d1401c90500c079600010304440210391 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 643555179 1250 643553929 643553941
    0x3011a03041a010b07061103010b07150e030406111005060d0308090f1902040c090f0504020a1101180c08030a080c0a110d2c0a09051305011a01081e0f 66
    0x14400719102e811480030081d00001d2524180b0004254282c4180c50901000c80c1c2002c2d400c181d030100341b00f4100d01000410406c0001b80c0581e0302d4040004010400003145a004003c0e10300e0f41c2c0043c0c0245003c40d20f001c4111800c00d00402804c600659443e00c10700852801501041d03098000001c000d060000c0640822620b40c01800501009412a17084800007002100c55252165841d4802da020314500010200c03064865103005040e90b19082e6016891840e10040c0320007580031451b54401c02c015020b007001e04840a0040d01512540f404405e55101818204441442d006034044981c2e40d000700319521040e81c1080e2440d40c000ca041c0d0f042501ca01040c44165854500500514403501406030340e1001150084001241181c0c001424200703401c031100128081c1d80d400805c542d1100d10341104101e070300d09580000e60b0041c54241a0f8400b80071381c1c0d41d07503800e50b440d541c468240300401d6080011256403064107182e100d500c0d03021400c24521056403448407000080e0285442c8180c0e8000644 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 643556429 1250 643555179 643555193
    0xa060f0909022b0618020405010603020903070315020c121b03040e0705070c1d01030b1005030a060905070308192d0c050309100206090c0301060f14010e18040b0603010203011a0304 79
    0x50f0381d03040315060003004e0503412500c2c0132911054040740309620306000410403601c244290f6840d0782014004115080c00e503100c040b44518030254001405400300611030740c403801030194401c46807003006c5860315030b9004842c00020070030610031910283d00507c8100a110390002c0e0042e045142800c00305d548001d241400041c064040d000790b14101007444601624114159185040b04c0c042d48610342c880e1140c1e9215044003119108991b07055006020010100d491503000c00c42c03243c401c07000c6400c0750f540d9641c1e2542d11303008003450f02606032000e106d165082d6040700d1100c082d0000c0c0180140c601d415040781000078203d003099403081040054404080050800c00c9580a000040a1500210400320020340c3c0b4481181c05160a0040b80307000141410140a400c0c08d880c03e20440c00c0d455410709006d01084005510003c0c1040102c110171984c1d919101385105400300440d072000303d0381c6018105464040f8010381401c1c020382c410001000000030181c9800007501008807115507980351070910071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 643557679 1250 643556429 643556509
    0xb0f09060408060612060c0708180a170d0906081315150512120a080703201206090402060319020903030309070305060a0603030504050603041a0a060f090902 69
    0x19801020015002c07985000015056100b0300013207480d689039400740d00846444d110300341c51007881e54400344101d200242c044c202070a000e08012101c020f8001c65031340011246070041e80b040b0124a4a484407244084050114164003102c6080480c0c2841c62b1410042112800501d10400070102c08400000c0003204660220b240180c00d000788901800c0712010520b40c5008c1c40b8a43c4502d44110032070410845c042442d00303070056000316450801020640a5a0143c0010444802c056654016101500d41540d503200c00c5454030303a116444403540d03c485e000c0d1104c0501194400c1d203001d801c000c012790b2001c0440740d1002c00030440540010121034244080e01075010880d07890700003c41000840100041c202045034007030740485070180c868445100440700d00e030001800046040000f40000c1c14400007d6402601c21107031160320000c15112902400000c0d1603071240d40380c07036407410807a00107015030f6031000c0d00481b07104000d0504294002040b003090860705006503030000c41d060070784203100c0602c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 643558929 1250 643557679 643557697
    0x905030702040f0e071d13031403190f0e07090b011b05160b0f041509051801080c01020c180a020c070e0603010c0e0d030e13020a0c020a0b090a0b0f 65
    0x500500c10000241c10280920700403001641c0314070040011a544406451540d03044a890034180b681c88604280030013900d41038083d0227101d80040080c80400902005611640c00c8002a20f203155010324410140ea241010700c192050510705c3c032401d62100450307200304031048114000707028104000180c400d50465604480911820304202c0288400850740302c16202c1c500f100c000c0240c0e16184000c0c10b50007003040c07108141000348000e2100b560002c0e008800007209040c05a00e482d524000640b0301800c4018240081055200401c14100c0c200719035003030000c09001404039a002403011a02213003000850174a0f030040c941c00b007120602c080c1d04840d84442c1c01da05035030456032100080c85880c002650f0141c0690311380301243d04014495440c03d420340c03000915074041401a514103c03840742c82d24401c9523010104040d00b0044c005548000c0450b4083c1c0c0d2140003034036050340100416484941e0014203d010100f10705181da584105d980c0042d03c00d4081081c1e00c1c1c6100c804c01d04000e006130500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 643560179 1250 643558929 643558931
    0x81c030e071409071715030a02060a0c020306180a11130905030c190b0c0c010b12210a271e03060b042a0c02100f0807080c0d090503070204 61
    0x101048400c2401c2940d0400c0328141e554003003070344441d04102c581c540002c5c510621155450003042000701d000a0714890540700400321351080c4800e03000108240d0042400c040483d06896018085007018030000c0d900c400d9580c052400b29440d500301c16111702c40200010045003510965400c541d0720b80501803501320a100c4108036007212841c0c0b1950725401400d148815210307003905107040050384201c0001499001d0410281512007805c00503654106800207100c1d9502c440490030651200da81480c0404414001801c4003001c0070340200300c04060010884403860b04001443c2010342001c4006003000c98500030304c100c80710000684c0c0300c00404e50480c000800c50408070021b04c20801c0b0040307050b64060202000035400d0320080204564500303c401070b81038a140c03081100020006070302d007242d003114202041350000030341c005070061800400312400309074540d0680e00e0307440d84041c0c4264410340c141420b80e11800d0261124419010b00c3c4481c1280540b41c0c07080104000f802c0c020348100c80e0f40600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 643561429 1250 643560179 643560193
    0xc0803040606211e03051b030a030b040e190305070b091c03020a0804020405060612090102180303310902030a0614040c0c02040b0d2a0f081c030e 64
    0x50514064542407082a29203481034400c0080580c50300c0f411604164800001c0d2541030f04803040540d1204c60300e9054060260510004407205484a010b4140b80080b002950395000045800f44c101c6401041e0306010724139025203100a80c0c1c00040031070600204e0001d409a03030b1100d03e8121501d1203503641c01045100e40105010b26102d00280041101c00c0032110b0301c2840344401d400710128043c010b480c0340010341e1103001c00d016040c00d52000380c00c540050092442d141d40084d032a1080c107403d44000d030b4030742c1d030005080441e44010f503042548040304501031443d14040701200704810f61103c4410b08400000301140d1288405842e080d4000c1000307078025526440c1440b40720000f010240f240048600362154161810316083c8101c00d040029070b15030050004403a002d000003032000101c2d89402c50b444051580200700506014448403202804d482c00760b403400a1342c0201d8001649c072181d004d0022500920006a0104415811000007840443e0310340039050304502a0a41b1010451240140a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 643562679 1250 643561429 643561433
    0x606050313230a05010b0d0201080a05091c0215010b13170c0d030f0f05041a09040b0a0f031505040804030605040c0e0106050a020111040f0b0d020c030a030501090e0606100507030c080304 82
    0x883c43d149418004c0000b08103080144041c0040b401150030001e00240f00040040e400111650019402100f800d0480749840011100900144003104400c00941d0110303090704601050b285d001c6014142c00c0c03031f0650401c2081c0c085502064250b00448001000440c0c45c4c103400340c010401400071500c010800c003903070000c07810003070110301c1c1c0f808020002036508600213030082d0260302154221004e038a00240840016941c10302c1603000f40540710b6206403203230420980c1d86c0e0f582040802820851110210107842c0d490000c41d2441e00c00e14100c02241032104100210349100140c504694011502040f01c3c0e50f0b528200841508030f4000400d03000307101d0000b041c1294014050143c1d04502d40080229038413070750b6189082d000c2d510602003584840c440030701c4900c0e2494090f255440c201030000d400d08403000581070554101c142c01d00d0000303a840004200c1039485000f001d440a250764050003030781c00c00b1400b044061031000d090000340140015070000b0117214804258400e6000303c0c009880b03003013074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 643563929 1250 643562679 643562683
    0x705010f0c0c12020f09071e050702130606020d11030405090a0b3003070215161406061c0b0718030803010803070b0609090606240d09060c03060605031323 68
    0x943d4282d02501084001030128140000f85901401803603c03186c0013504c811a044004800c030708415420000c00703100300c00043c0c4400d0a40384000b5038007400868031904100c0003c2ca860000c0c0302c0d4100304068041d4000080301c0100807642a64070569008082e82e90303000850700501121490b69802180307040d4620148003030405400a03491840e902c0c0310604100c08202a968055039902940c00500d10141199501000c002441c407080c1d46c00700344101606c80e45800b101d03d404089894800d4018004212951500340d000c40628030445d48910b01003000c42c0c40c4c2002510005041c0c5080c422001070800c10340818405400c02140e01401413541c03903850b0000c0b247c43e5005004d04880d1814580007140951600f0030416128040c4440246215075400d41002203030b200c6000c0c083e110300203a032001000d100d46a0008c1124004c00607001c6025a42c4c0e103801011220340750010010189000003d1080e40c1d8000100c81d04001400200c4060408500f0f150103a2200d40c4020318107001c07060f0903000300d2400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 643565179 1250 643563929 643563959
    0x50f07060504020307121e020d02030601031a0a0212070309031101020a05040f0e0702030f03130606030f14010b0a0317090603010e04140a0f121112130f080705010f0c0c 74
    0x2003a0f040e126a95034441c441900c40703080c44401044a0740005c50701011852440c0214110748c00101815003014468010034104002a08155540206503140c00100030f200d0600c1500500e10845c00c40c80d21200a101a60121024280d402015154040303603052510580f0305064038240d030002107550303207005100500b099000e13100380341c0b030840d143c200021720316420254140f1401550b0091440d103500c0070300348061030784014003034109240a41c0041c0045851840f500001e584610700048840209003880a807060006040001c2c5030b040c1005044a6295449048101c0340d00003c4806c10b11015071405810b03020340d80c19030341c00800200002410703140c03800c0d104d0302460003600c000e284c0702d02c071003030203034403071086100140c0221540706641000840e809100074440c000c0b440c0a45000c40601206824607112182e151018100480c01d0a00d003000130a50100500b140300c3e504803a545009581c0c0e0300c0d4496489401e051040c100b8100c50f07005e01407045c040b40c00d5480302024010507103c800c12012505 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 643566429 1250 643565179 643565183
    0x12060f150f0409052202211f15060905150408010507052d07080306130504060b120c1309050712032303070e1903020301050f0601030c02031c020307050f07060504 71
    0x1003450081545043c034180041d00b0054802030400e06080140c00740300e00081100d40391080e0340e4007203043c0d4440407c10f10a032036060310405001c02401d2a440d01e00c00a84086201d0340c144003c0001c0e04000f0709801c000c00c0e00c12214161078122643c00707004907070001c074052940081e03555403c207010014100d51101c0203010714900e139043e000a080348c900c521012240e91a5075142440d030100270440115081a020310742c0060014400350301c14254285030401e42d40151001c5230b46a44514000d0a640741c03910400f1807454260004241c00c0300f042e00014a82c582c0718000d0740304650744000201c2444014021600a486c01035000402009140380c01011414505a81555a0a813030310700e900c8004c500c41143e008801c260790700e000c0d40b80c0d004104403401c0b42c488145002c0a840301c10000060310280030b203501c1207002d190510103a1a10500140035203030340411400440d0002c008042104009005042101001510041e01d95584580c1a942071041803c403000200c2c010807014104960303a000644168 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 643567679 1250 643566429 643566431
    0x902010906080f01060503040c081f06051002120f13030507050301050708061f120c050c010e0a030203030f060a0b040305160501090f0509100b07141212060f150f0409 73
    0x1551101c04442c40c0b80c003516000408681040104000c500c602d01a68200340651142a10f4a544840040c5000c110800718548212003030801c0704000712500c1154001c00302621004244d0140740d500035100c20704d902c4561072011000c10510b003200301c60015540f905242001031988181c03a030600e959128447d1140134440e6080100103102244034454590041e01c0180c505c02000c103101188203800c0420000a60402080049810590400f0700404c0400700703a5885090395072008032030075400d40c1d40e0500404250341c807280c1c6280002c1d43c0003044070362004031314000441680311000000d8841c0301c0350740071709100c00c80410007005016000c500141c1007081111041c94040c1d0b1000151111021807056102c14200d11a080099003050501b640e4403003c3c04243c654040c3d2201c9010303405800c0200c1c1900d10030b0700c0883c1004903c00400100e0b0840a07003215107400c0045d02c1940171302509005000500403021400000443d40302e01c030000c012a80615520f40c4c42d030468100481094100d4440c5c27198031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 643568929 1250 643567679 643567697
    0x180d060f0c0c050132071404151d01090b0309010b15090102011a0a050d11270a06030804091a13021e0909072f010605040b0f0d110102031c090201 64
    0x90040200317209100801c510b106003002c030781c000902e0510000611480a0141202000c4034002d2030000401c0507003803061550f001c04000410080203100202040640c0b680b0854582800741e0300f00c644c0c01c01b103540a0340d00b04d40d030b5622240154090405601159040f200c1110022034400046005d400b020300203a008014205440c2d11018110b88954000d0b030b0408180c0c2c409000780e06000c81014040c9000c0c00e4a112003591803400b1554254034032443e20030380108100e82c504120190321040760000c2e04000e052000d00d0031511400c10038850303849080380d10381e502d0380c44094030200b210819403e184002c1c100c50b400d0b0007840b01c85020b03511006006001980144034a881c00c00fa8101740e500d0440085c0044036142e581071800d85552140038101c0100b41c00c0c00c10301d926020182d10b071119488003040c0000c00d0241c6044103000030303641e070300d24520b1040102c034803102502d89070707146d2042c0000d802c520651440e02002d00181c1c1184160041902003110110101401400c41d402c190841403003a0707102101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 643570179 1250 643568929 643568951
    0x105040b040207020108040308130b0f0106080f010e130c0504050a060f0801020c0a1b1509060905011b020405060609060f04080616090909020f060403140106060203180d060f0c0c0501 80
    0x124441c4203c000c1c00b0800103400b081c04a442941180e600108607060502c3c130140075110506a20700031600d2880300c1402c940103000f841c1d408241c094001c0321803481511594105084141c07001c90085c507001307400d4000741210041c0031500842100400001e00100b1441c100f515005e00546860300825500078081500092584c07014401c80d500000c2610203401d0b034071455501c82400382884500016040003010010030404000650003801c1d104030b481d209111494130501610164490780300728180807035100d4500d056450f4039003c00d4a554100c0d00000c00e50b5601d40012060b003d500055500403130081880c1c42164144001041602e003a01e044072005e0307940c0000108003061544c0000e0006080100421082c80740b81c100310045840207110450300b80010303002c10640d400a078015180218000d41d150031b803200030710590018151602c0590f14251143c5500150000341005240c00303180c0c1c82070007000b4006aa8400c1456071200c600074000034442d814010050002000c05407010b51071b00580b524 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 643571429 1250 643570179 643570181
    0x6090c06190e1203040e07021011040501031e05010f0807050607020f060a110d080a0c090f0b1312030216140901050402090415060f0f0203400605030105040b04 70
    0x5850007040340340c0205080e01d4002200c49003061070050f90002640e410002c4141028030140014040700c8105520702c1c41c0004009140012983e80807440a18069108042280120486080c0c035428200851a00c41c9224210400702c0403c45a400c524940000071544010410681085807104d004485920342c1310030400c0142d104060000b58402245007440301030f07083c48000340c44201900e0030b10303002d002000318542d030412034209480e2000034542410130506141a1140250308201440d14400380382c10140304d16424000703801803100c0d0090109104002c02c20345064040a4400d500060a03054158a0007940c2c1d84148940c003130b01603500c3e0b0300200e02d007440b9001002c0b0005004180705516460101440000c1d030094110980180d26006014101d108181019005152998440c541a0240720780102801240b000390011034101b00807020101c054004848601822214a0400c510a5004100003540b800701c203414600030030000002d2242d0040081c3d0b040f10419902800f0901d50300003004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 643572679 1250 643571429 643571437
    0xb3a050618120304230a1a0a0e152701020307030606050a0e102c130b0a0509091e06010f2132060105040b010201020421020612010806090c06 62
    0x64110040c400070b00407560703e500c4800d8480e454040442c100708444845410070300131b110b090b9018a4804219000c030000e1080856224103406401c00819003080c3e08162070788880300181c035030a0504408506802041d03d140f00d0a4800104850350070440c0d045064040d410031111000424034200c000207a07103004c2e10440c2c1d42d5070095518941d044082604101019111100500800c100e0018400809809042117a8090400e4103144004100e620402c205c3c240b40183e01c03050360f07091035400555901d480e002c081c01d80e64220740c900e01c6603071443e440b81d1602c4011140644800610542c1e064a4a0040f541074103a503040704e4800481d036205c01080c07403041820f83d80382c00c2a862842d04240413416040320368070803079200c40075a55401110180659000c18003d101c02881d001100108403e10303141c0f040c080e40c20310a0000b036052501d0003140c14840240e1104c02c0c40c0f12082c103101c3c44210740d1650229207224150181c10441540c540b8910f0341e494001700c40952652040601c80c000d18030f0460162 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 643573929 1250 643572679 643572703
    0xe0f0a02100309030e04020a051c2007060b0316030c0509060109030305090a0b04081f060506030402101202030f06010e0d080a0c0503040e07030b0a090b3a050618 71
    0x1034811075030303411802c40003452102016070420203109001c48083c0e861780001d2001c44002d6451903110b4000c0c0c130404c648003405c00c980c4401907107031007078141c1e00d044813126a5021002c406070054985040f414881c0107002270f0000180d0601491001005a440c840307094001d8030700480561044607207400a01c1079a00d416100240440c111580c2040040d1181d0020f0256a01c080c0c086001c07190756101d03440598002e9045034505230409000d20181d640c00d00410704441d14461014010549060041303074840c880a40040e019200c02c51a50712414010141c43c080c8a2801c1801c541c2c03447c0000080d038021405440306400070715000c5d2500140e15280c0740c465001508a00c0140c079110354898140c0ea5441409002c907082c2c0010320000411180b1001d0a80c41480d0544012030901c0640041028010107604840c22180c03070400a104540c80780244d10741000d1450510111100307444244110054019041324010131400c0c1c0c188003006004038402c0d0142008400320b4518890100c0420b40b50740c1c070035443c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 643575179 1250 643573929 643573939
    0x618030f0b2203083d08010e030f0d050c13080102090a09050f06101101020c03130f080601030b040213150e090325170c032503122004090e0f0a02 64
    0x2040b005c0003480c42c4852025a0034030041007140802a1120500c400158142d141100c2d022003082080000e0181106011403000910710b0100d04115416150007403005404000c2c0e62100001c040600340c204881003420a4401c480400b65600443c03400f03035100e800120b0086480760390028040ca020701030b6030b00409084d1424902d0b41e99a030184001c503108455000b0812640c00c1141c5c0160300e003071000301090034203e0055941c5160f15688030000144982c801c103001c0342c2e00c080c100141e0320081401c034103590780084147c490380c40320700004250f00d50119681c1412450040000c046030700c1000d01e0003c513110920502c801d0340d56080c4164403070141402aa0240d91078680e0001401003403404815038a1280085040c07014290041c00c0d41900708540d010740980c00081c2c441c44000340a000381c00d290540480b0400702504aa80c0200445024000301c280c2e1034450041032040105910000c114003544140b447c0c440341c1e142554030242800703092178000c0c0d025011207460210703000304441c8070039a00501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 643576429 1250 643575179 643575181
    0xc0504050d140309060d0506040c17010e2a03070906031a0103110c061e010f2105011b02010603020f0402030103030e0d050c03120409050a060f0618030f0b220308 71
    0x440d0b40b680a40d603540c128440c08204440e6030b0341ea0b00e400250042c2c005040000405150103000e11045500385060700342804111091002030203d6954003905540c60040c0010b05074950340c1c9944904441c1d441081c000780c9075030603040400e91108001d503100e1030ba16560a000c2c41d035244000e03800c8482c492944d2a500c074101468190550003500048044242038146510301f04148041d14181802607a40d40700c106c9202132800f00640203490840d024118240554912524150710203011680001800403052084c00d403c0050040a500002c1c0c0415900b0344481456204a0300030f00801345400304910441003020f440702503007410304c01d4905030381c3d0503100c50140009060400000141e12403040300c4034400e0112a001c980c40070310261411000e8141019103503401e0038007400580303034001c2810350700600e40001005001482c0c42c5250172078555081101c0074a1102c600281815a43d8102900703076a01e1046000400c0180e10109100d03030320088624074581c1c64182110a8100c180b6006000150f40c24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 643577679 1250 643576429 643576433
    0xb0f010f0b09060906030c03042f040c050c06010b09040c021504080702120a0b040308060103021905090607061404120c080d0b0604051c030e0d05150c0906041403010c0504050d 77
    0x7000804070600010140ca05207510707000051000c1e0320451b2400003410000c000e00c8100140e88030f03802c4094120070642590100c0500301e2152010850348032031301c5140c07582084c90009006e141240c0b2403052071020381d115985c407138810f00100e501c60b44149001d03d1030041241482440425010b60180c250360b41f1002c151106d88504030701d03810a103026a03002d81c500000c102c50941c00c0080440c2213224030312445413841c6c2401c014200b094002c4c207041c1814010007007000c0c2024843c02440214000d030a20340d45400c01e55000c01c1c00d030300039040f0050020340f401255058080380404918450307032084800c2c3e240600320490450b08140b03480d070001e00b005400d10610f440310103030f6008122070f582c0144c856030030a030707460700010541107402680c6c1980b849514043c800340341d44440d01250407901034840c44048a125940c0f1603640c542c03034407003807040c041103800304103582d10032012142c5007a4000e1040e034445407104240ea26000c500e409291096191024400070070780113400352012903d009200011b04e010035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 643578929 1250 643577679 643577699
    0x3100504170708040b1305030a0f060f05060f012a140d210c1701061808011518020c07060512070f0e040f060801060b0c01061a07030c1a070503040b0f010f 68
    0x281b43e401500c85c45040b404241a10100510550b1a0240f60003600c285403034282081100c00e10803142c60142d00309806c1152540700c541d001040c035142843c0c0310300d03000310100c08203200308800241c010007082d03490403200c14000203e00c2c04c4211246401542c0c40c1c002020020f0345d403d440c0944107101242103ca02d80580e42040d44541e051150a05120b0413407071441d6420a0082002d03003004000c80da020580540c103a031140c0a180c042c040c4003000b00720785101d4178100c6540c40d00501c02c0110070700d00c4040e403800703a03086a010790b1110383d02402110304180d03c030480a00301340c100085005400c0300460006e09d055100c0c03820868036505e9901c07100d20354500d240620001d03028490081d840c1c246c80f043d0000e000d6209101c0c2c200100700c40780e10b04e40c44516000c195070070350301700c0da20441200710403900c1820110503803412104281d034181489070340b0341201d240c11000202c02c40303504500b4004c61010041f1054011009501c6144207030349010860791005c2807103c24000a008024a200300c00740140079032909 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 643580179 1250 643578929 643578937
    0x231e010e0604030f11060403031d0c130c0e100207170c101b1208010f0602010501080304120c1502060a051305070603051801050a090302120a1b1103100504170708040b 73
    0x1e180030068a411101c10900d824400d50302100082d0750f803034684020303016641d042104000880003800301c021071240054140c0c1e0480100c4082d8030f40d40c0405061107401745541031060700c1c0c041c10303102d008010342c0d0003c0d44725200703031280e0f10700550b541580140710340c03010410744600400180546180403440c04202c03094124600c0400c15229480d282d6404240a03100010800440e03a031030000540c10101030b403806a4155106400307582c180001400002c8021080d2029140104200b0311402c01c24200304400360410362224009140b0703150841c6182d640400d100c0d04c80d94020b00c1c148010389404401d0203a0180001e80a0020b4010100621a0a02ca90062900200303501c0c2c240303076400034042001d401c595043d11110354107942c80207008101501442904107070b07881034481c1401c0c251000e101038010382c3e0004428400c0c0444103008000c1010a000d205c1300018040c04495030505440d082c2030040c0000d54094039010442c0c2e5010b40c140442a045410250b40900c88900700391500d440103003aa04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 643581429 1250 643580179 643580207
    0x190c05030f180607050606190803041202010c0b130c0f030b130503041a0306090a0501050105030a0b0105070f11130b01050d090501060503061f06020304150804231e010e060403 77
    0x18502da02d1200d2955084050841d040c0510094a11400c2c910300704094a01c00e0409803090b0080c6400800c421003010040e01c1c212021940081e64000d00341c4012a10f280d000c22009280f40d0b500414032408410920007070f03004512840d400c40d02d058894107503c003140f189100060541e405a000524070920b036001c07040e680e070b200b00c0449050540304e901e84456445088010b1070740d52804400c000d4a03180c40b08a4a1300888003120410013941000c0000340a03200052107403040e11740310404071701c8691141e03040300c1e902504034403000c155200b103241c1400e200320000d51141c8100d00444c4800c042819a200e001128003058413002c0c50801640042006407160006c01da805550302c00c400101ca4a003400002d00c2901044109000c009007960308801d00c00c003a4020404650060100b885102c12011075001035121034103142c260b6950707514088120300c140801009020b41c1480002110010000c1c076502405019694172982d170003844c044a08031689441c42039016405031001c240030034021403200980c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 643582679 1250 643581429 643581457
    0x303130302330a0e060412021c06060b0405030d031418030403061d0708160603050a020d0603080a17040b040b0c0c0a08090f0f0d080c0f0a0602190c05030f 68
    0x881e00641281c0240c2d40741d441144500010009400b5a0010901104030400c8136018141402e081c040c41040102180080c0140c1e06800451501c00c64401407045207a070181c41406000c3c1c0b1a01d403d0540e80040c42034074060703ca4800004d08042c0039026484c0700300c640801d0004a41d492124400448110740d44148407404108804004280c45009603070150020900f007808402c1020b203c01d06c3e05c2100d601c012002e03045643e100c03409841f8030402a048400e00c4c5804500c0b61901000c2c0c50080c4101040800e045181145c00401c016012001d05502032003500e40203816035482505c101c03030b00f5041b0380c000c0035400c81000090025440f01950758211070015030203400c1c10859191245441c2230282c082d1082c1d0404640304040f86030070821a088020251041c80c00445d100c0c0108441400322840200f01d05000714032500d140b1000c014800402807044110b80005955040100c002e50041e081c0c03100580b04011620405401a6854140658030500841c50300c00c0d20030845c1102e40003200d8500c401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 643583929 1250 643582679 643582729
    0x11031f110705030309010207021c17091c0c06080a061a180612011401050c0c01122c010506010e0a03030810171b09150103180b190b0303130302 63
    0xc10020001385100b40150000140e8600881c010440c42c2c50400d0604082c1416541c0c02c0e00001e028201241000196120f660381c4a09044001808200c41e01c400c0e1703e800481c0040300c00c01d1102240c160000c03034095443c1d2105030340358441d124055480300e00070020595501e40001340c0c201c10090003018201000d0304800219000e940005503541c0c0031560000c51f0554210040c27000d14842528180c080d2030034240a0329011b4221070064980b04200485030612403401d260121038000c58010210450180c02d8105200f94582c3c022220311070100315606032986414001080c0b5405589842c0400c02c0050140700314a146640440748041c005140020b8200240e8000a860b001c1c41c2010710ba0213102e00c05000856100c00440321444d1500010300d1155140303109005481808540d0341c102c1120a2a010810700958540c5007410b400e1100300401e444034010412101c84c9408104150807080408207218a001c00f2003095601e0050100700c10080d04454400c00051820410241324610303512508032003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 643585179 1250 643583929 643583933
    0x150a020a0212101e1a1809010e010c02030703080a05010501141c020703091e050901090917070507170303061f021e03040504150b0904110f0c070311031f1107 69
    0x3960324401000300c544c0c0b2020091411030309507000d070700c0c9a10014050382264040c85c01c000741349010900c510888003841c80c004142107a5081d04040c4000454000078008160056002552903001c11b000f600000e4944010603a2000c8074060380b4100e49050b515141c1000900d01074146582c013620090080c189050281c00b00a10680090b0060030302075194901a07501d8650b44541d45007110030f8810484403101405c0c40320b41e803045956415142c804100007503c43c0780e480c1c08070314210071500c2d0546a440124000c0100140003550005440e0a440200008a500d03010b55aa030300003900d100307a10020030200c15800ca690010480b041c4591071048034106a41c444034845101d20100d60042c80e9040090180054206406400300c9c0400c1d2030400c1c5462403420401e000140501c0c030302540b14980b581e5490302c00010001c182c0d40c50032000f60345079507070f08480440701d5983c0c1c050b0320044030100b00700d00400d00b5034940850062a00110101d11100c1c0f03060b02817030700c0024812441ca01042e043c081c882400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 643586429 1250 643585179 643585181
    0x203070221220e0708060d1a040b0f1308090f041406040605060c1209010c0b0a09110a0612020919080606010201051303020604020f0a0f0902030f0114031c030204050904060209150a020a021210 84
    0xd0300204030b03c0208c1081c20907080c0001110384c002c002c544000c0514040c0000941c1c1c0d080703c0b0801c2504030010302c0c2ca9094800005060003004400554400d090100c965802e40c3c0111845020340f400b100d007001820350f14028007006005440d585000354010721030810619842d44007c004140f014509500400000d542c0d112071020107540741a1120703a501d29200410115003c10b110f00c1d1011129801c01d24601480141000000d0f40c1034691a9008900d110740703a1502080644400d6010744045401034a408106989607401c485407030041d820f000105450102d00d44003005140d82641c00b0703000070398807a000d0200b90120707104074030b40240b01c0c040002070624055880c800a420a1400580d69040280280c0041841030f04250400008001c001e5070359a00000c50142c601718070034041d100e400000e036081d4024003403036220740d800200200c10001041550f500801a030720b0120303900c0d00c5800b800f121034803d90082e11070420150340a1000c0201500c0c0003a178010003c7e100030304a40c03103c3d08001a0b14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 643587679 1250 643586429 643586453
    0x6070f03090c0b0406180f3206030403050c060606090f040c110f10050f010e16020703120306090c0e030309040b030c130c0f020313090203070221220e0708060d 70
    0xf00140e000f56400c840e03c00e80d009414007c02c01030050100d89410000d0190090441d901c8000c40701c0c81c0004041001c8140d142e900c0070a42c00285110345900e82400c02606641c0000006640790250900207600c2c0c0c54003406980807203801804044d91800144280002896000707081e20502075021031044031000104070b0040c1c400443c00140c4012044504034100703031007010700291601ca0241c00144805140c04650f1940103003069600c3c0400d40314640143d092482e035400151118114034954050aa05904420200d45149a003000b04c848024400c940d4035100707414459140e04108805003039480c041e004182519002000e40300030b482c0c0310700068004401303c080c03034824603151842c000c3c0b841c2e0488416807828115001452074145207000001021742d140c003542a9003540400440d102c00c0c401c004885500d2a05007608080740c140b0700350240f090b00818441c01c8a00d502c881d03c40780b200d2a043c2044104d520220f02041a615500000c0e61015001080990000e600b04504400308124910380 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 643588929 1250 643587679 643587689
    0x1107090f09020a061d010c08070201180806010b12010b03041a150d14120c06042003030304062405010e0d03050730080f0601140c0304081c0206070f03090c0b04 70
    0x240d8055245170b6032440700c2c2d450b1025903042c00461144000803030040422159003a50910b001416860810309021756407580d43c00603540e1344a40400442c40740d050000a080520007070310041c0c4641c0e03a6188062192004940c001c01455030300b1000c1050030780b0000445d40203007540008000248810000c503500310040032050b00d8403011410104400c00060050202441021395014908599107441c55500c4030040c0000b0900c0c440d100310070342129040084021a1880107058950340e08040c00d04c0c3c400f412901c4d0070380c0b0304948000e5102c03000d00c0c40c0c80050021200103031074420b580f408000c10406110b6010100f80c0600904005180c00141b0000068044818000704040c076116419100c050032000d03861800c0c00d03c50240144120003c0d944c06042d0701c00e20034680306194042110794001140106840c440c00c51102283c0070501c61000308482c1410224281e007018200d40713002049a8035442070b02e2403400704400100032082c0038804d0300005250f901400d81c03807022f40d9a909601c0c00950150b844 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 643590179 1250 643588929 643588937
    0xa08101d04050c100914010f08010b090102150a1d061608130f1202060f0408030a020a021e0f0609010203100b0f040e100302010809010902011224030506010807061107090f09020a06 79
    0x818402441c1803611907200d46c0c028070300385906518480002c0c10003903060003190f903d40c0c0701140e010000ea10030001c0040301034006080c05074a04000e18034202405c8500c407100401c3c1080c0301c1c3e40d40d00040018407030744a01c0d2091805110405004000e0b0307903811011f0581d900c039440404202e4080740d21000d090803030034403c25001e08000d6151500070b042c0a40940301e0465428883c051102241d40e04042d240c000c04500300060340c466450720f0030381c988000ba2220360070300c204040150707266005c082003a1031030000100680e00547d0311101818202e10080350341200080c01101e0030b004050302140640503405060390002d141985420000900381d90884100282d54504001401156030040829070807448920003805140810781c0040e000c1e40a0444164030699200203070030300613210f0f480040c000c03085201c04030100c584074104281c5480c001d0207005e000740f242d004006102e500c1540c000300340c03686071806403003040e0074925414003034084142e80741c0a031904c6500d1600503031b82d13400c0140010001519 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 643591429 1250 643590179 643590197
    0xa0311031015020604030f030e010f06090f0b010e0a12081605060a0b030c030c0f0a330503071407230a03140a02060109020309030f0f0a08101d04050c10 67
    0x48848580104031200c0b0454000c074090200013a08030305080e1130710304075050201d040c065810010b801800109111400503082c01c00014011513558001d11a07400445424002c00c180c00300152000307104039440f40d42000c40601b00f0003510050303200d818856403080c818985400b10030820540083c401c482c00356001d401000600007010700c40d200f560540c60040d0040c0000f4080000000d07140d4803441c40545c05071541480c0280742d0761f150144000904042c4e900c41210072130100180f0304032980030000901c0340308403048586d00d10f030143c01528494200f541e5203d50866045240d01d44eaa0449002203880d5442150303c214801d0401c0b015040c0504444020400c0b1045410024085501504001515a0200503000da115404034031241916103a1001607a29110311410314038500c582048100d0201002c9400b2043d2000500100307100541d643d10800c4603202c408c2010300c03201092051081c041c2c803058a81044800c51043c90754480d006409440301041d81901040120003182d01010010b042d1030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 643592679 1250 643591429 643591439
    0xf1b03060e13020105031b040803160c0b1201060f1202030f190203011401051605030a05070c1d04020906010c021207030203073005010204030c0311040b01031a01050a03110310 77
    0x10469070102c02905905a0080c0c281c0020b00300348000743c58072244048a031a900d0081c0400303403c881c02040010102da5480e02550b403c1210002c04150894448083c00310004d4881c04040075595426182494801a646050015100c85212420106c1844141c00303012800c5003003480070754800e03042c212012085113011204005c1620100302140c02c4244180011302c00c005292208921110083c28410360361030031070b014a5851580750030000d22343d1100181091450394014003410041d4442d0989103681c0e51205281c201f4401c490491a84003c20300d03000502600e00181034941054042c1442c2c1012180e94000c1500020010091213541d88660001c1045080802001c401403007003081c107004c0d56034120a80a009110348a0201c0e0703030b41401c050041030003020340c102c40c02140d01002e20f414069603031a2110042400138034113440b451800d104044a54001e0140380c0000351448203503800c0d03c40c0800151495004103d041d400c140e41e031030040d45d50002000055000384502e800c81182ca03071600c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 643593929 1250 643592679 643592699
    0x2040504050604050c2a0a0602120112020f040f0b0901030803070e09360d0c14060f0402010302031f23150904052809020901050402090a0302040f1b0306 67
    0x20740140d00943c40d04c0c00b04050035845006a5143d940c019140d0101d500b5540c416410f501445000d14541d8095481c00e901001500d5008000e84903560b202000d90703a0740d40148c15411b1a50701c1d0b01075009038200c017031000d12f031410360302003854100e559400084034100c0c000419000c0e1800d800880c0c0c0c5460000900c00a60b0f040480c0320300d0b508044030310100e00e00d05058100d501580522594070540b440c841d11004201d00ea02111007600038010480d100813820880080a5000e00740c01680c00c095640410030061202244441c841d00c0c2480d146002070300c841e4011000bd60000b4280e070752260174130901c0c00d8032012003c100f01c01040310202006444030040c07204c2d1010408444102c3c4280d0360b00c1808204a00f4503020340d500b80c00c0c225400180da40e80d8009411041d004c1540b0780300082d030340700142c428a240389c2d4400d400d018000d40381c1101603a06e40007444224803900c4890f90740506c514000b00300625007600300c0b81030860000c0d0040b8180203455640f8000000c0c2c860700c04003280c1c580d01d05002070004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 643595179 1250 643593929 643593931
    0x3070501260c16030f2312060d0b0a050708102301030e0d030207061a0306190912180905060f0d080d0924060501080a0b0a0503100c020609010e120a030b060301090204050405 76
    0x138049090651b80a040c0c0c00a40522070140c020048100705000a00745980d844855100c06401449243c02407600403035000042500b162a500800e810b10f0100314041007040c00c3d90309540600103401c2d084414078600741000810784c0b00103410161a00c40c12800010107010200350420107417401360b240d00062802809a4130300f1034802e054480d150340580d10990740050820340000071850f03412074900c1a403034460003400d82000060101e8404143c0c85010701e80c4402e0b0800305810360283c0c035240c20f07211160384098904c2600c0b03095001a0f1030041c0d111031300e40302c058140c0441c810342d4418070b0002c214562a0584000305419250500c00c1c0ca501d00422170954540d181100c0b071100100082c07810840043d20340c64000c0c1850401030b60794050420f650300c2c1c50500102801c002021030f8000c6003c2101c000c00740c407080d0200c200501070a8003080b80079905000b036942c2d1141d002d02500c402d01e04040d04c1652500002c06060405440d04100703a00c07600c50300001c6018040700900581e40358200800e20050307441c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 643596429 1250 643595179 643595207
    0xd09060804051c02070608130201020d0f0c1b030317060916051209011506080f0f09100615020d020a0210081b03070507030f05130308090a0801020d060503070501260c16030f 76
    0x123008510f040050ba800700e2280c1e440c459a0802c03c00c1d0038242c0340c00b1101100f032007800900203085031000c14080c40e6407501d0b180459200740e660f07181c01c441850520001002c00c1d01c07020780104a00011a072840d07c0c10303492580348032051030040d0400d400f842d000f281428065981c145142d40d520000740b18042d04031007000185c05c2d2428015200d04040b0701c0034900c884010659004641036401003000100d09001807034070000400d005100050302e030505810600e015090710405445a01e08116900d4000318000e402300e60001c11820454a10076070a8480c0d05000300b41c5001c0e000e0705080302c0a01c9a40c0c0001d180a00040d6031420b440701110314001c5c1171401980300480a0110a000c5160525943c50700c260907250303c001041e8681d2288004614200b140e81c00442c4a5400442c24035030400441c5c0c030841c1203800c110b0440d14410341d80c4c801940c601d030100600d040b100702c0506801300c42d20f82c0f403040c540c3c02c00400014980340c50a00f01c5405041d8941c1e40c401c400089581e0341080c00a03600c0789510000c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 643597679 1250 643596429 643596451
    0x1713050f060c030601050706020f0316111609050c0903070b09040510151d150304020405010b070b0c0c1612050f16050f0a0f0b12090d09060804051c02070608 69
    0x20401e0b1188605500000740214100030f0300044c00010000c0c142c064a034454080c95243c1e440c2c0c1840c401c4d244812003142d941000240d1840d00200034103100142c0c0d111031112807195024124180541c0ca0050f00d002003030010302240030064808151000c12000c00241101400c07903490b07400c03078010403051700c002410b1060f02112100045c00100104095001c07150701390708065008480704580d4a43d00030790081d074140d00c8814625821503c1c0d1030140150b110364400c503420003080c0e0b03e5102010744c6005041028000e00301d0400042c19115580740184241e461100494900c01c241138000942901943c01501410400000200070098100100349103004101d020300303540400e083d10001846807034490b00b8810b0404c001c480b00a82c46501410014000044207034079442d0321007410898076801510414050207003040081e100d85004141140542d00f241d5a40c085185400000c43d0b508002500580c0c0034010740c500c0242a010760810075440740c031240c0140100d40e03d048009006100014030302e100300c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 643598929 1250 643597679 643597681
    0x30e01020309150307020f0d05090f03070b1c0e010f09030305060405040210051c0608031201120201050d0c030e1c030e0a152a1805010e09161713050f06 67
    0xc0d50302c00c4408107950345051041034490b130b6285006c038904054000da0204074001d006d81c440750940d0090040c200f0700e100b5104070141e550044149581c3e81c2440c40b07800108281800000381c030001003084110208040d401c0070941300e24040025003151502400007030304a0b0340b410b199003015014040c00e60300000442d400c022607d016004070b0a981000b02000c010000001916946486154030302030708079041d480d0400c0203d032240141e6035250300c003e15100d41e09001400000b010020845080e03100c030f6069454038100a202c000d16005085000009410b043c0c8031610015070381e504200d051001081507000030308074103032840f004d0129421480030709040d4000710781c504c1c049915100000d200b92400c0b00300081b00f0940c590900035403400c451000c50780d120908640d64183da0b201420148041c0c400a060344850b503101c005688816400d103445070002040000203081000d240d26620030788105040c070700c0b00c61851070514140d10400311042c440025200c45e070f880c24820308008100616a40400501207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 643600179 1250 643598929 643598947
    0x5390c0306013b04061104241e090f1d19110406050408060c19110718150602191407050901092004060c0204090206120c0403030e010203 60
    0x11a44140954860305120a1a002c0e41607400d0741c1010020884480c0b40c01c9100c1514080c011086082e41c3c05e0b60580c0c145004103200340140e00032501150140c40c1400141c030002e0740707441e4100c0c0c0f40c41204024003004040c03407503041d41080039600c403540e02c550700d1294040c1050103140f1025100d800c03403041114074401e45080d620f8284902c6402181c10800140c0c240030101038407015200180d400241ea81700400c001545030380000140003511680e2056800d16951014407003c68081d189890f04141d00b0074520700e00050241d58280c030b0740d07001d080644c0c80c2651101261480d55400c8407496403190394404124080740c011560520151880c1c4c8094000c401c580001042400e01002000c1c00d5110401c0110741076420400030341005002c05000401c5940e92010690014500c0309021598500424844202880300c0300072070b004d444964549903d008426001d010060159000480e00950100000b0000200b10a01c0324814400d42525603a154110315009020014004072035056620500041c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 643601429 1250 643600179 643600183
    0x13140105160c020604030f0b09060115050403060213260c0303040506040512011e050403020c0306060108070f181202360402040b120d020f0a120f05390c03 68
    0x2021a01e803904000000150000070310910442d800100810000410002040100b01c007080c0f20359054001d480c0c8a0717989840501d05070100c0c0391201c000440c10881800002c1556000c0c0c482c0c41040700400604c90380b034107014408107180c1c5103250203010002d42c180b03040c0c28040094082984003600990709103031411020480900640c080c0c14814400c0540200c20040250311030381d1040e40c012a4a9048092200d2041c001d14003541d041d401400f41440e10344190600260041c060b04041c3d64280d0259aa5041141d071419007c1e000710400844000c01280001e101c41508007800c0752401c5902140b407540704200000340c14141e030442c0a5007000413400048409150814400301d09071500c5419540c1d480020001d03d045c0c0d0445038030402000c403c00c00500001442d40551149408991170903628924032980d540210700010171001d142484908568810380c141840c41c2e0722420b05600b005c80103012049941014116420000800504580c03940c141011102400507100d000e040d88403181d81c0465 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 643602679 1250 643601429 643601461
    0x30213291207080a120c0605040605061f0f18030803010b0406030501050d051009021c0b1b1206040914061609090902010206270d0305012322021213140105 68
    0x4d4502d600785d0303550785c841134003c6004504099120404001903c0c0030315214004002c241ca640380900c4111142e0f413280300d4820114010855103072100e0300d81620407c42115140024141034595000030040000010801c0c00614040d044072200c00c1d4949040800040440710168000351151036401443d41c040780e030105100c1041c5180c4140800c86901e03034004260a4a11060b1803160a040b100180c000e000703031581910302804515107038a002d9034618001c003544c0c2c000c2920b440340003031421020500030310f0140c1c00000342034802c8001425a40415003540c0c203082c02200e0041e00385a2004254006035071183c2e1384000781800c90130821030510701d600002e6031ba01c00180340070030000301505031380007400d800e407203070148103505008480001001010090140500f8802c01c02403043c000c80d504200780707000c484400d806002901807031400da5951a095902c40e160380141c11140d0f0b08120300c068950241e4405d42c4904c0844500320070404481c43c2038800c4401d1140c000319207900d04024002c5c0417541302505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 643603929 1250 643602679 643602683
    0x32007030b130507050a060302091008311a07020c0d120807030e010f150f080a02150f0a0c12031401120302030c0102070b011d01030c030213291207080a 67
    0x31502d009401d00d4898541180360b0001075202c90604030001e40c0a40c10740040014220990340d481c14240b0521060322440780582c1c0c0e00c8501104480c07009020b0580d882103960200d600241c03104403840c10740343c9445112140b90032112081140041000480d010800724000560035500813000703056607200d401301300d10541203010402089038081100c003407094100b89280d44466000304411642c00344614010b0104501c2402c6244003128000b40b440140c0b05008102e61114024004d644425400c11641540045200081c0c120030300910800921103000b8001c021825220300e440d9601609000e4120a907254909003014200400d60101b01140c000c607904590300f0311066000f20045240580c254000c1c1125600c840d84046580014402c400c0780c01c030704891a540c2c1802842c0e41603041104412001d01000c4c2540754000030410043c00e00521148841c60614400039801807080150f4400f4201c1a424081c80b40760740b242e1410501c0c1890030380d4000e0a4001c0101191464005c0c841d840789100140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 643605179 1250 643603929 643603951
    0x190e07050327010905122d0a0503070207030b01031a0108010506130b063105060f040e0c0408010213060e0a030b010e0a09080f04031104020f07061a0d032007030b 71
    0x10502d1009400d40000f41240c1d0301005403000700c4900c1c19142180e8003c00c3e1034202684441a031805540c2080802c80c00281d00e22100d240307005c1801a00f51a1070340050030600451042c00000804079921f0101203001c0c5215035290011580b00200b284050307203060704840f60341e034174180600000741c0d60b981c0d040c0c0c25002d113a0300104039402072900041980c02a00c0d031100c810841150101101403100022005a076440b1101c401d90907203132401e000d001c1c040c1002e000d61a4000300002e2081103102025258882e40d40ca89039841d05407680809030030f80c5c1001c60142448544200d043c42443d4122807d91070401c4107940c2c145000d8078645a50f48010018441c01c400d1414100100384181c0c0d0903001044d010781c200e085a55944441492001680d00900c426a01e19910148002451400380219550103240300784150610080e621010002c0040e4817803100301d801c1c00708455125480d004104081c2e10b000c0d403190107540702c4059200d481c002140300d81021a4020000c1440094800d11440d50000003c01c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 643606429 1250 643605179 643605241
    0x7240e0d0302120f0d1d06150a0f03080c01240905090c0402040e010311030307080f09030708011104060e03060c0307050c070e0f01171506011d190e070503 68
    0x4040e0b0412031803c03074a89401000251900382518100c004000310258070604103e190b003403400060200340703a50317403da50f25000b40000c100b842c0d030514080b0704810401401c1c08120340e583d00c0f211031104181e5004450240010070070760301200302849072240d03441030003150846a90420100c18042c880602503201d006943d078000c80e81080c4100310a00810302c000e0b004558540c0c981c04001e4080d07a09200882d008503008189072218100402900d0809a00c61802c0c1d0514010301c148002d181c1020040d581c2621510b41e001448180900907225001e41e002403103591a82003c4c4020a696007070302c5201c0c0a40d0000b0f05101c480d8517003100b01ca910610354030b007460301d07801c4254885050a101c0d901040c40c0c410103505105c2000d00104034141214500b481a01c2c00041c02030089440d20b0001080c8200700480c0340020ba59035000341111f4200340300c0c210980c05408680d1f030008440308007210402540c090092410720405204602d080e82141d11401c1c007034118a80716415160102403a021394080c03825480b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 643607679 1250 643606429 643606433
    0x11706060f0d060f0905010b0a0b0a080708130203010507050c0d0c0c09020f0f0c06160f0c030806010315080a050705011e030207080415020105150a24090803030907240e0d 75
    0x9403091400f403404144c00d00c100300c000c1c1000d50203001080021842200d4106000611640b0340c42180c0ca460810b451b4182c01e03546014054030450300080c261100300b80380b8415140103960178440c00b4070444850f1500b41d164214155414a003030b00d83d480c081d00b8020709851200200e000700d803180e021905480d001603644d02003101c03444400c0c00745030704144d2a0740300130408041d8440045502c40c4107051038180c1c01d90a04900700e0444e000100541d00d280071400e2142020f012900c6038403c07942c400ca043c10041145130040d0380806101240340c2c494042030b0400038410003040000d01121008001c2460444071545203460000402541c241da80c4060640c0080c1c10340c01c00c85d480c410f59000741880039000c00038010301c01000e406004112111215402c80e1403410000b840d0a0062100352490030140714114141100e00354100440d0360080001e01c821600b000402c0003041000354403a0904101038404c40d850503414000d5021170241c41480342500c0745480d9003440c0e02c1a2200c10040b4201c8140030450114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 643608929 1250 643607679 643607681
    0x50901150203160602090907050313060c03110721051306050c070f06020a0204061a0403020409020d0c060504150201060b0904021305062a1b06030403020c03060708011706060f0d06 79
    0x10034000c51030f400d1814540010b11a00e40c0c050728004a003620303014040d90b075001e400c1702c0030b10049410032040e240b0810540e002c600280c2c8500a5404541800246c40d40342071071401d50750308403500451700c044081450000f0300800c0c2c41c3e000801209800c2090401e080b00a1401061032280260b5040240200b10b440d0b1541003000340710010080d55440b141c01d541c44460080d1036009041c1e080e401142850380c0060071088010035524501c04008070703507040a0543c1e08010140150140503030344090b0070000030001c6000383d03401c40d000341600d0300d80c199264a00302c1c03150040a101c038440810340e49096010040b51041ca0210787d4a0700c0c00302c0d00180d541008040903074070042c0030380000d0b42040001c60701510300c1e07440030350014182c130303080c1c6920004104e808420ba0356070002003101007c1140c0044001012b05050000d10341003442401983c05502c3c015011078500001103a043c030000f03e900004012401030540400011007004002d002c2c80e18060021480746800003440c5405a540050020284415 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 643610179 1250 643608929 643608937
    0x13120804051c02060a03050916030203060c09130501140310360b090309040608070b0a140c06070806040b04180b1f0308040e070219020402090d06140a0e07050901150203 74
    0xc01071044c4e8450f9121840100140400c5406007064407030008084440101c1d0a008000c40b540240240000d070745400106030603400c00c920a17600004041000e003a0054a40142d9010b00145e002003c031300a0540d00301443d01c448104035503810362900321601446010303900030400026500114001d0010b00d112080c4141c007460308050546903980c3e0600c032b11040c02100503c56180101c80500c411519506101e80b01d1700303a481600c410702010403911000d64029980741c0e140060002500b4142071100c065a810301400f25078160016100c5010002c0b5854039124031325800384144e070100000e140c600070504101c030301d03102c0240c50400d4080000d1040b007400d800c070071480d6580c03440c0440c4172980c9280015843c0c000e4016251f040314070b0b200182c030340f6200080341d8520311801d003440c00000c0307040c0d000d100003503100400b10764101c100b582d0040c2c086400e0b1301942101400469900816240000d0300350201c0d900b180d407042894214840400c4180d540d1880301c0c4c15602480c5002d0b60355640010306a01e1481 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 643611429 1250 643610179 643610183
    0xa031b050d02070f0f1d07050f0406020c01080a050705270d080d05070e010c080904020708030411040b1c03030237120c0c060b2413120804051c 63
    0x20030701074695038003640400d080781154020340103a0202a11541d400242140500541c3e0748418560b4204080c10b001d0020307036800450301d05209240c07502d90030f000a020303031203034002c100541c0c00b4921602c07865174003005040e482000c10200b081103081c10080100248079028500103a20754a84a51a00c01c92000e2500c0001030010038080c0003410900e060055500705110000c6110315000c000760303586014036010506100144d40d410042006582c594809411a03002c06410039801d00000300002e6002d00114000c5020380042004104040c0820060352040c503189401401e12564034800d41c0c41d80a60b000400d81e05040c09a2a009078a40203112022030b00912225803c000280700b048111841002100340b401e5942e0a800003440c0c0040c20944111300a0800040d001d02e0001c408519207501540364010010301082803200645055810701881e080e10f00700f10a000525901201e070055184002084180103200d008440c0b42c0303030398103580100e100301c0740600200d840c1541421000985c290b5000e03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 643612679 1250 643611429 643611433
    0x5061207180503060907030b060d0b0f040602071b1502070e0105040e0c0301060303030c0807030c02190501020c1b010e01171315140402040c110a20040f09170403050a031b05 76
    0x203c0c003007042c0d40e600d640921080d2341200e03a02c00031034924104a400311007000d030444c403480025101c00740c028124080081003582c10550901200d000205690700441d080c800200c4641085414940401040c1004240c04030a66100803c100865a070a05100c1d0440707404440c0000d980950b010010704060030800c0f0301e54107520b0039001004064143d4003041c11207105076550380041da9605026400c43d4454a500c802581c4124071900d209840408107040c1c852080c000581132050703da00345440d02120040800c482c5800c1c080c11400341d640850341640307a01003440c00741a401e0001d0310800e100e40c80503000b140700c40d4401510005010006160080300e02600000308030fa00c0b91a0b04040e003203841560220300c501d003000c10141e902e80c420b0344510307290070b41c59010300090200c079541c490424403c046001c545038982d038040baa096441c2e00c00d070121a02011f5000c505c0d1900c0d440c003d8076007000c2e03103400101000280f000384042140040c042011940c07600b031a200c0d0f0182e5003400005020110740050181c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 643613929 1250 643612679 643612681
    0x40b06060c0a0602042c100b070f0515010602011506140c210c070b0a1b320f0616050d021e0c0d030c12110c070e0708010506120718050306 61
    0x2280e90403081456a13846d0503900002c020400260400c429004c0d81c03143c11030350445405010302d402c09001451454403480c854401260159903241c145074600480c0c4401941880040050507028040c44101a542c0e44040400d14101400507018401e0390425600d465130114442c0612002004800980072800c1c10407012032448841d40325482c2d2240601019078081c000300001c035114407906841c1e0000881e100c0400204d03c0c0700c8c02c01b00704e083ea6181516080d40915000c8668a58540302c00b02100c3e0038581c8041c0400c1171504280340c003030144400b007615841a010040400145685010765840d81e19000d60790700200c2c90242e02901030b40c00e400d400d0011404210507040681c000070004aa590401e4600c1c01010725001d900700c9008a416402003284d0141c058100c91403079200c03101c111413185145081007803000a041c07808911390814801c5047e040140101c0b03c2c0c004960701c0c01050100d400328503040200e070280c0c8280320f014080c9018417528000c5411750509444100c0064038001c1c0c04c403441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 643615179 1250 643613929 643613939
    0xb0f240f1303062d020c150a0c11120301030f061b0c11012a1a0901051f03050a030e0319080d06050f03030306060313050f010c090509040b06060c0a060204 68
    0x25030451844203e621a2412035042c0d00700d02e002c0080d18418082410300d0725880701c0c07041400007a40c000640c5600074000c501c000f20908440c40005da020f0060110300142815040c50013030803910002d50003002a0f4005560411080805012a415694010084100700c0308a01c1c0c114050441c4403d541c0b000940b8580c01001c040c0c1c08620840000c0c06400d1425003980104015103541c40088240403200c4010a00c4c00c0e894141a101801c4640c0708000744005010044590030742c10400f9260303400ea40e511081480b04441c002c50401000701520030a98420a00d1507842d141d0341c001c803200040c203021042e1004440f0b580d040c020309000c0d640e200b1b1a044140011320300360300e49501611600c803060b0716041000c44c03582400c00c90582c003000058019072a60700d41c2c0b004c0021a400080040c80107a81c40a2048001041404001c03c000900f00020070040c2000c54060910030080d0032050280828100f000041102c0c4082103400c01c0c07050300c6c001c0d07440078071490260800900b0308000c1c201600001e80020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 643616429 1250 643615179 643615207
    0x903151302040c0e011e020c0613030c060206090c0d03090e09060906130203030409090c051c020f01170f0c040b120603010b04020c031905130b07060b0f240f 69
    0x1030014402c65040000d854503000c00d0714440441926240000c0c2c1c1c401c0b00e0552141c40500204902426004031016069914000b60342c980c0151108014a03000000c200b0400c60880583d001800c00d5002420301d5151404c1900c0c0c0d25040d03400c5051141c1d0352551020103060142a91b8400383c8068604100c10b482d00b819025601da005550000302803240000080c04508080003441c1e10540c0180035524003480d0005010261000b204241c40f415916040003903d9501e41038080c0e80104240400702c40100c15004106512421074005411b010796016041e0840c0e88100b511548409804106029a11092050b20150081c3c0d04003000d0501e001940d00382402c0603041d060b00c5030304214001d10000e5050420301080c3d002d2030312280ba4a6006214180030b0404088503413402c0074035880c145080000c0c032000502c10305019400348049603070000300c0743c050003018098521102000e48140901110140100d101311403152240107800c10442011090240710074104d40d44100c0403200507850b03c00d24601d401c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 643617679 1250 643616429 643616461
    0x100203100e07111c0207050409080405040204061e0e0603040803040f0602030705040e01080309010804151503080a23030114040f09060b03210d1a040c020706091217090315 75
    0x14029119010788040013082c107002c640d0b0b0f000e2007940585011403403d414040070b0194008101c40318001030102084d40c2c0c4451010340020296540c45081c0038652034203441c0e0006010080e8000c0010384440700d80a40c0b034100450707400a81c000c1906960707a8403802c044141e5a8041c0e40100001d0000091020b925402000f8000703548100e1510b045e26643ca010281d9a886903012050118400f400000c01080d901480200403a9200a020070682a1004444007214054004440400c0301165403031003175502080c3e0b20003800e88500c407554424999482401d181c041442013610344161038010090316141c0d0b030055410310759001020300c101402803400d9070140c42c084401c28068441c3c008208441111101c07003038085403085c0042842c044103400c1c410b019240c44080b400240e10084210040c9407501e100d6010344408a601030100c041c1426001030200350141c0c02043c0342888100d00c0c1d00400e0140d014464040b0420b410a036407100c1850100c1e050145501d015030800c10804200301000340020540c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 643618929 1250 643617679 643617707
    0xb0d061b080112020409021809211e0a0c020607080301291206011407140601050d0305040905100302130b0f0a03031b0501150b040f08030a02100203100e07 68
    0x40c1440100005003258034440034401d075810180c1000d102c0c0c0140c10107a00100703665001400e0048000c100040d20382480005844060690b4012684d02d11b441104d0080307001030448000c40300d403400d0b45d920740300c000210511007005200c220014010300c806024160341c20b0b0f501d13400781101d030312510301c1e05001c3d01c82d800c244640e82c6040580030076180401440160080300d4a5440c6205082040c1204545c0301e80740000c0c0302606000b400145182c8404c4ca0b14090705076140f04044071102580c800500d5401c0c4181070380702d24045c2d1000903e12000a400c038054034203491399024000380710760f00ca1a44210500b0a6030000e904408540c0396138141580c0c5400600303000d581500c80c407041e00e02610a119800b0603a03c4003600244000142200c0002c1010b0288211740c054800440c20701100328405800c000c095000400c0c60714009420043d1441141201004041e810050741c10503005030400f944844110000c42149a070000001e6451aa0b01c01110082e06088100c10041d182080b000752131001a0821 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 643620179 1250 643618929 643618961
    0x1e0905010e1816260c090a090302010603081602040b01080c1e090a080a060c0e0d02120c100207030201090b03010308030c0304030201020408030304031205090606010909020a020a1217150904150b0d06 87
    0x100d1030340b040340010345c0441c0c900d016200218039641e2940c01e200901d40c3c00002c80455403125000408102403e01a104502e44964000c2d020880c901c1003100301ca10407500c05040c4910708007080f240ca24044140c0b145d00900307841d00c0904190a4000c814580b06d615500b1ba4060340e8800041001a400a8441c00c0700f4800c14040041c0107641c0c405440000c11064916031040ca03c881241c0142002003040c206048250111503541c019100001c0503202c8100c071040040e48007004c10400c3d50b03030044548004203c298443d520b90f50540d01c034030485103c001d0074040340c0400000440c0425200758100c400030310740d0b00c055030707100e0515180040080c140c0e004110b02003810070002c03610040c00881c07042c2c09503030161a80c61407146030442142c06508407c1c850f0303056004180c0315801282410410048610165a40f591011103415920f20400401b404420b03450407144000b00b5941c491280e40d03a0441c1c0c00c9800c840318020802c2209010708108003131250014017001c015000c03c0b220f9005404d01440e039000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 643621429 1250 643620179 643620239
    0xd0e01120b100234061b150b01170405070915030605040501021305011d0f18010914070503100303050304020d050d030b0102072106090c0503071e0905010e1816 70
    0x1181c05a13403529000c00101c0924840401c0015500500380c2504118442e2840988040785884100d00200c4008407034202548411004984c0d40c1c5c8580c9180e0060680038007249903007041d03100c09070340740f400b402064509581c440350700c0d418201c13051040000b035900a50074041c80c5040d1074214040c0d00081c40003003411010103004140c541c0544403000c401c9060a100c640c5903404a810004282142100a81c0200700081c4000d0314003110f510550180488880107e0040ea21841c003002043d00205580104502403007405000e016492000080301c0e018600300d40c4940f6079000095250200140081c114815a11920308180e0103400002201c0c600341c00ba1000c0e20380c1d61400900e180707008000d200b1481442c5550400140503581f01c9651a07008002029549440c1c00c082850581c09800801d1141012140681c50742c518540c850040c121150050100d54980321030f0703416000300030748900a07141c010840503268103002c200385140d44640c540380c4001d140e55111500304820b2054100e421081121b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 643622679 1250 643621429 643621483
    0x319060501170a052221030203160c020411040e07020f06390c0709061d01211b030b01080601061b080909010b030603010b030d0e01120b1002 62
    0x4040564840894602c0540b150b030348411a1000301001403001056090b03c059041c0502181811825964411010140c00b1100105200e40c0c940340e0700081c2080600410800a483e40440c0c03070755506107400c3c00c2c1841c031401c00c2e1002038090000702d00c540c00d5064000c0350002d00d8140320802c00380a030042d50203490745040700b142d003a500c4401c01c851042020a00e29a00c21540140044218810340206060203059601041081c03459101b4003180d0600e501c00c4900b03202c986098030400e40202107240301400c160b45d4000300000400c00c140b1524004c00f00c1a84035000c4010407101c206446a0700c0404101c007a140c0e015002000b2405001c2a070726544000c1c0040703032041000a5841c1a40c0440c1c403107515554200801504803c00c00000b1103611f8024080c05103a0344415018074003801e01090020f441c1c1c5410000d02d03013142c0f460f040d8030780b203a400000035030b400c80d030049103506001c00b0a29044c0ba2075840901504080d1102c101c4803508240445038102c0001d80c00302d441c59142009911076441402c0c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 643623929 1250 643622679 643622687
    0x1a040609032606120709230a091703060105070c0e070315030b060d0323040918030c03080612100903030506180703021308010c030609230c0315060319060501 69
    0x400b620b081980c202e180410601e10300a80700b544150480d108940e001c0b80c40e03100e01e20540e00a03600c10064418040c42c8001c1403101c1e1888103034042c0342d2030010015850251103000c020440700701c458022480010124007564031402c00c071104107070000c0c42d00c4c41c0d25030707074501c0c006201d40c04a6503140013915007000b00e0001041c002e02001109d8102003201450707290344080000380c0805080403000e01884185910040001e82c0f044845040d00c0e01c1c42580b03803480c0504600c02c0d1440360303101100d002410910040001c2d000014007a40603010700d41030b56942d645201090100141c00c030003c1152040d02c00c3c04900503e82e4121a88092203a035080c40b0f9038456109001c22582c1140320801040ca00b0700010300e0341c92003035014000d028101c1c003201c14001d940752207103421a2500c03c00d460010307807280070034807110f202070190103044c060301c080248540170000c10340f0301500d9000d4800d0382055000030115080400c607a243c200b00540050940b5628200074110103195900c0301100d4030800e0800c9000525076000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 643625179 1250 643623929 643623977
    0x506090d111b06091309050c0a0b0d0518070902090f15030f0406060504051e15030d05090604080d170c070305030609070c1e1509031b1a04060903 64
    0x9041c01020350340000110580c5202c50880403c1e04040c0030701100b0655503880854860355800c0341c40000301e02e5100e040c101d040201212006000c0c0100311401c000011041c0c0c00c540c40008011000102078945c000102924110000c5402241c407404c000881c07101c10641c01071080150884000c13820341000e0041c40074500c0c1450f2074a80c403400034000201240202c50003642c0c40792082000160b00e0780c40300d0003d400c407881a51040e1390304404c8403501610f0600c804040d81c00c00440300c00845142d0f04107001940d5040b00f404c1e1a8100100070905015a4070780e8030030359018110817010360708007404190300108498240610b00020161780c201103072800081c001215070080d00755450914650b542c07030178015000005400d010400217404e1842001c00c201d0141c43c030440101900d40c1e40900c5503070030245030100500c602100300e0740c9400d1041d80000c9d00004070001026000c110780031503400501340800549070200f11241d064040400b00400c002c101e5100e007041c148603895400d4181c1010301440c0b1481c42c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 643626429 1250 643625179 643625207
    0xd0c11031c0b192105030a080115030b0a050f0103110f1c05091009050c030a06051e090601030303110d0c0e011202070f11030304052112070308070305130501090506090d 74
    0x202c075500780024031030013078001d800100d40100d2500705502c59071102d2841c4c0c4200d01c0c03103000684c0300005000c44c060075007011030105041c1c6024440005420009050480c041c0308a030b00c514945c009000d9584d0294010342c8514003184903030794031402034400d400d8040d800b56404140c01c06000d18880c0142c401840380c103020301700d10f00050610b4550284100010701c2c1d0680140c44030300ca050000d05003541d0400111038031522980c000b14042c1001c280505e008500c803a840f07000d4036904020480022400144c1d40c2c1103c1d010710b40464020220007400001c0c0c4281c80c40e4040c61800e0640813200349400224110400001b81da0702155641007036040000ca0190a1000b080d08506a070100302044608a003560641001030582c3d15003644d800000740841c0b01c9051b04600a44000c550490300d80051050310000c0841180380d0f40350042c9960010101640100404140b41d43e40010030070b00d0404080385c250b4550b0000c000c110032029401c24683d280c00441d85080c15100700d20401203540d20641102c0a544 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 643627679 1250 643626429 643626469
    0x20d020d021b0f090a060f0801060b16030509090106052101050d11010201061206090b0c0a020d050a200a0b06190302010311072a0503010506060d0c11031c0b 69
    0x8400350080c03006107010042180d88440002100703d00d030f6075280324081c010080e000c00040c00c070340b0748076070b40307241c4103190f030290f01964500141003240e080d10303108a60b02042c101e81120800040f5103020344842c0108460340e900822a44008142941c00c40e00038a100081c0c007540045072040c401041c02d44003024040c082d00041078001d07040001c0c510350310720000440d050001080f1540c5904c00b0807400000c0c05001c1c0e4600340c40b040e000c410301000c212a1034000003132048da03e150514480019580385081b040c0d00c010000d0005003907079407501c920002c0012840d00340c0308140c001d15440449075910314505082d500ca00030180451030520380303071404058144070351141c0c20303486141d41c0054009000511080390410010041a0005140d03245000c00d001503240c0c81c0d440380d025022014881c405141c0225000342c2c501028031401c0d507165019128183c0c0807003400700351880a58011200c1280f4085400c109100215200501518066103403c4010a41d030b802c2017020004020000100d04a40c0444009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 643628929 1250 643627679 643627693
    0x90309060503061f031e0902060304020d150504030503070e010c150f020c011508070906060509101704030e0f01090e010911040f1401080c090f060903150f0403020d020d02 75
    0x507000d000510350203040145034811480540304480d214401c50040c600c0020380d1200c40312501c1c100d0208440c0d09543c864010042d5290700c0c2d01140040c07101420107489411140828070400032004a82c2500842c0314105000c5400c0070716000d0f060390000d80f5214003045502008424030352244000c15000c030f40061303504a144c0d648005c0d8400818260480031142502080070030340120b0240240c0408041c2992200c121501d020021418440e03590800690b1031300b400010008640d22500ba038241d01002c4441400008405034103440520203030a4505410340c0c0c1d10100002c3c5900150304020850381540c0d801101c4180380b004480020b03281c060700050481300700050140b440c56601141c3d2000380c2030707640d5141c40d0700c8440084c0c030a08558032840e0342008058018000c1e50b8440c2c1901e8000d0080540d40d81801400f1700022040c010030b8528501410000c0b48980715960108507010246643c3c2c0c1d6481d4444c00c1414840c1c2c6903100884081e0058403402e2000981c862000400c84080702d00341c0e01a10310 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 643630179 1250 643628929 643628939
    0x30309070302090601030b1e04050106080106020a110d050604030306030501050c0c150403020a0b10091a031b061e27310e0c0a0b3108010615030b04090309 68
    0x41c80f5405002a8105607813501c0302c013129200e0280d41000c0da0540a0044031980d540c2d8100820b0328030581000080000c003d004110b00c68000400218459105081c45400c07160b040110303d000b245d42401404134400c100910007419095801081030b64000c50081c0400e41d69405d00201601c601d80c3e80c82c900b40c1c000115080c01d10561491380360018401c1c0305950000b5416200c0b014059405e0b40c1104224588a100b088980c032144250810840c181c4403144002c01c1348000203490b035280c1103440800c0103800404c0c03080c0f5074528080300c1018031111030114541c03034140340b440c1241d0001c42d501001c584154504e04100070341d0b00d101240010000f8282e00308202070706188200c0a882c41d00c40b4004a50403118080c43c20414051070700040d900030010086981d03e081003100c0c05e8000d42c841c04d48071104020304580e042109000408905405c15500300c1e000c0d2035001601c09000316805000e50754602403001c106000440b010640c81000ca0307034107000350000803007084112411450001d003c110782c1182041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 643631429 1250 643630179 643630189
    0xa0c02250e190203010314011404080913110409092f1e0301020f03071e0f030b0f0a080d1d03030403062c010606020d030912110703050307050606040509030309070302 73
    0x40d21490b4054041102042852440d040c0d030030a030002c0720306031601455a0b80b5040240700e080d11460303004410541a003047c0d1100d011130f104a000710350144201d400e426100c140142c010040c086541e0034595600e42d601e036586002080000c0d82140e009482c0000300032011045c0748141103484000700c40380704207071007001000b00c00181d0780042c40c6240c0d28280001100d681c00e1015283d1000c11480c5142d49250203040100741c071400c030180038400005105940d01495000440320720000720350500159400c102c100042d403001075200c84541c021030b504008201e818022454600e142220740f40d04205104c04103c00600f02c0720702d07a086815500c144800c10208078282c010342085000d18114000141038042c202c1343c4400102881c044680d1102c40c00c2144a80c10448540d03000c0349482c0810800703600744d40d500c13182c9825245d48010410110242d4403000303400e00c1720b50002c2d075001c401c8943d200124940907031113040c1114070340c0c465440c2c000040c0d8880c4000c412684107409520203020998115400c03c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 643632679 1250 643631429 643631431
    0x19020303180714011116030602090f0907080f1e13030f050301150e04140a052401051e0f071b05010c320706021b0a0305191a0a0c02250e 60
    0x1000d03034440d441b07581c2c1114141d10300507070155001d0749015989250702c4007031003540380103501c03030900408010b0200400c140c0c1c081c1c007568002071002c1c0d44801030348418401016030040e003c199a4401034520030302400c00c01100c11115898860b4646e07a40420b02d03d0f0007507549000900c01d0820442d10325640030b1081c1c0c441c0505460743d08000780005040310548011a01030041142c440807040e6940092240100f10011851404482c0944511040c02c10074002007070350113100b001e0ac0c0281c0341c3c46109600c40006c0025990f01d000c0a0303200c0b50301c030006070074104041c600a08528041941c1400040742d02d5106081e11903120741c0120a007054036450643c03d05202e4914007241c220000384030b8801d500040188501070040c0401d60050803801c000744050810b626009000520410004008000003880401c0c500404400c200c03050350b0150035814050100c54410141c05103c040000402c80007800e558040a020034240e0b0848001404405c4078440800100204031105401c1032000c000a4203400142c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 643633929 1250 643632679 643632707
    0x1802030d0f05160f0b0c1303060203060315070f1115160207051c020103050a150e18070e070206100803040b0a03151230050f1902030318071401 63
    0x51803500080c00f100c00c80880801004aa00c0e2611007800c005126501c0041c5070002071104a041c41c013005059404211801440024080b580100015520f594240202d04072090600042202c62403d20380041c80c0442510203100450041c112804400d50001070a82d0141d1100c04c851085413105c0300c500014544d100540b404510528102040540380c0a9020010480d484455044001c4910001d001e403000149045071a80c0740c4420107212105072038817001155004405030503642c0b5000c040509409231610100c415214003d000140340e550581d009100310205c0d42643c5035900c8a861401c0c40070030038403400c7c0c0158424002407008203440d0700105200001410f00149035241ca5541c4550301c0001c0e40110415041e090b21074086c0244c82a03052001b200703032545110041c202010381c890040c22000c07050304100c3c010600d8082102c00008903416160250002c5509181c2d80e0301c025583c3d4012141c0002c041c000c0102500c030800009008402d034f44091840d0b1442c01000401181d110240c9400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 643635179 1250 643633929 643633937
    0x2010203090405130c17011d07030f05070f18180308011505090d050c04061e0b1e031915080a141e10140103080d1e0f020309011802030d0f 61
    0x10000c0e07003481c0c0d140c0052004014031b08041c1076001c5101d00b1a44050041c4007040075030350252800c00e0020400005a070340c04840164042c0107400c03c60b1410034190410700d13010046007400322b0f11964039601181c1440c0c1c40003040c0b1044032070190300d807005440010001c01107090200107111071000b9039210b03200707403889192150400542d000019040c2540340c00984141d00402c8110070582040d010b10009446101a140c801c0103262401c01e403e501e45119000700c0308800f16a8580e603171206681a0314000e1813403510b649030300b081d0345880c06400c107140c41c0e143c8152610304555000c07021081203d046504c0032015001c6054642c80d01d890703241104d040039020340204644604110344408a0540c0035011070010041200003c82e40d0301140d1240a0350019000c104004000040100003124081c1010382d802140d4541900ca00e0281070034180401e000590500d06d400401007655409548264035010007030100e08241c2a46000c500705440b0040c1d01904107901c1e0112440c001d4542802c04a46450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 643636429 1250 643635179 643635211
    0x1e030818100207030933120f0e030a03060519050103020313020904050f06091506040b0301060504050a090b10050619270e16020c0d03020102160605041e02010203090405 74
    0xc0307104100d0784100c8040300480c800704824041c4001c1c49160522868846509607a10300d02002c0c001802a80c501c2e6040821201940040d488511350b000581c1e0035810200520060100c100100e8603604100c1211001901d00640001c081c9040c0800024160815a45250650900740114086e51001f441c0d9880c0b0700c1242892401629556061440780f030243c806490b21041d42000d1030300b0110007500e00070b400e42c41840040e06000c0003403c6507400480440700065603200c108082405091190301043c4c1c030a241400708115400d094211030b030710521900c2d0101e25030340c4440c20246c600362607008054001d002401807030814a224180d28528400505015103001001440071188100150340c80d0742d1346000322001c020300710790760700340300e4003c881100500301d084026000250354080c500071040c4268040c034031540605000f035049030880726100c0c0d1250221581401c210024010a0b03c0031140c50480324003100c8a0000c0100340341c6200d40c142d020b985071244907401c110103010082c00d42d22003500006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 643637679 1250 643636429 643636453
    0x80a11071d0405070e04050d0e03100c0e10030212040201030b0a080f1c0206060d0b13140c24030112021818010c030c090306092a031e030818 62
    0x80010900190391120040d0381d46000e191003410940a031340040d82070b02c6800300f0702000490108240200e20242c1c0740a51038040790000013460a08180004200c640c500180003440c5544940c40d804116001d66640c50a41c03409031049040b482070045400c505035400300403500540c441e800c49006002c0c010010030700c59403103000e850300340f0000e0702080380c0d81d5110000300e40c0c80c030350320303094820403070145001400301c614000300411624800c5207801403045a0354000203280c03030000100f003145c20740c12460300894058201c40040e9200d1030103500d0b5204541000318404c181c0703a4107801c101c4c14201103900505591914034480300c1b5411403801264065582d41c440040e585403002c61034441d04600303c803c560011849407480c00c40729004144400c0504204440c401c00703411944020880740c0c8000000340b100c0c240d00b0181003000f441c21070902002d030304681d0035941005090051003964040d540700001e1410b0b004c41c198010038220b100401140c1c83c840081d08100952a010780240204010394803007410403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 643638929 1250 643637679 643637699
    0xb06040803030103060510050d0308061f081b03070504060c060b040c05031504060803180a03060504030801090c02060f1303140f18030615060c0106050307240903080a1107 75
    0xa50455542507101000410078860180502a0084403103038000f02050f007000041021501001405014016180c01052880d240c00d07034041c84070007600704c982402541c9540001c2000c4010388040e0324080f040e1048a011b84120011203002d01075949489192a15000054402041c14002a0f510f035613902c00059042d296806910700401d016901c1c44c1d541e00e0101c001c0791a0710001060280541c0c500001071025034800011281c01201d03440941c20918441000981e03505950b80004180354100004e0008258000010034140c60000609020809159004980e40d8800f03c41400d8800300c9400441c44154040720046d81c6607001c0c0ca0205180205c1d0014500305074800b1040010400c8009508000705d62a00000c514a032401c40191945081442c0040341c0c42c003034144080e1240c2000030303c409002c1300941c8040b0040c100a410341d80c0c80e581e1140b10000001a21002100c00000b0303000101605100300b00341c0091320342c00017200e1304040908800b241c1d0400f110310003100c1849601804100360800c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 643640179 1250 643638929 643638937
    0x180c120a0308041b0b04061e0207050607140706020a050f150f0601020f1204050f011407080c0a0c031203050633040b07060f2405060d02040915063c02010b06 69
    0x59949840d0780c40e0726100c00104070403a402320400790182003d4141100c3c07a400b01d1680304032481160441d40328001410002081c03010155415034074030400a0005081d40c0108040d10f900e170141c1c06844283d000c125809840d031b240d41040224009010000800040001d00c02d550041c0c0c0c1031044030821208840f4440c50000c005841303040501012030108224a040a0010382a241c02c0ca013503444942c040d503100c0e0b0f0b180a10900104503c0c408a1480c003c904108040b02d0001e810046502d031107641d90408000ca892107649010000f0b0401001030f400c0c0c1404080caa000060541003000c0d51002401001c020310b050b04c40b01c03049140d0030840064100d120001529425001c5c250014544020380000e001310740190b41c14509200c10b68483d02c54900500e00d008048070070990314a03594850072113241d80280700700d030031060034a481d20303d116042c0d11100060b4019074119844000c1041504080040c2c005480010850002210010401c4180d55103c0490080c0120700001c40c0801c4c8400004140d600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 643641429 1250 643640179 643640189
    0x26090106030c05010309030816030209090109020319060302031b060c01110409150f1a070b0c09100201020921010b120604110616020105091503180c120a0308041b 71
    0x91103020900c14046661003000081c0300c00d00f0200642c1200c1d95001e025610010b140107031070781140311070040b294000e8045940c2020300900024180d80c450a1180007500140c440c030052940710070101640060314031940040c0ca8008008001004180b003c0b98019920540d9003a00b00c10207001d16080d500c801d001e508040500001001c1d241c0b800c04a00c0c50031600d07030030280d001d6a10001d0b010000c01103488103100c00d17032700d075140c0301101d5085031041542c041c8240320008106801c0c5200b0003100b4181d210182034500c9085450645244210320300b00d00342d0003000c0380d8a600905e2480c4000700e44145c0c0040e1420108040004070711106040d001888541e10606410300340d402c40800c0004000a00100100411048030f04c6420200d81070b14001c111011240f000381800320001d2030402a0340c0c3c0c0100421011504a03120ba034074034200d4090440c0006240c680c1150344148180c843c007a2401c50303c5c0b007203000c003890000c280c0d209a640381111098030141c0b041d14455202c0c200140c541048500c1400900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 643642679 1250 643641429 643641431
    0x50a05220615020f160b1b15011508060a051215010e06180106050f1804060816060203070b150111030f1806030412050c030f07050f06010e090d260901 66
    0x82c5030b21000307804e00050040401141d01701c510070710054149201d0310002c4c0e40e50085025111400c41c00f558202e000d040c4801e4070240f1488842d1480d00c0c240c1140107040c1ea6004800000c0a80001400d54050200b070b52481c0d800300c44135005010900307006032a258207295060448442c10402c1c640c2c01481e410a07008102e42c000107008202680c2000203d000315201e102c0c80d981d6640d85031410040c118010216070071203010000642a01031a41d4140d0b0310003004004000700041a50741d40784c607640c0c021240010001d42150707000042e200d80040203170340c100c6403c001f16800da41c0d50261440c1e8007058181c0c080d4144401d204400f020b00303000300f000d400c81c0300543c4c030140d5403501103501244180e11024881c0c1d02c2000204200400280d40300b09080c0500c419041c22038580264a0841e0300b0f500440c0042103d003407010035180248580011880c020140c030b2000d482d07090b40c80b80106142031a01310f4071010700e90700070840f00e051503108961520045e0b1480354680a6103129054040c00c61005031403c0f9441e07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 643643929 1250 643642679 643642709
    0x120615091c020120070302010c0809030f0706031d061b130609051504150809070810090b070f0207060f050405090405060402120c100305040f0215040816050a052206 72
    0x15604404422444040c1d402c96049a0100005099945d0382d0380c0002410050304a10b01010880d800b0709403014100300409440c0e24607282c41c17011317a0701c1403a4481c08001070305003030f988520004040c4145190850450140900f591248110408451049421040b04904005079006482c6101800f80a4405179407040207551500f0200700c003124035040890031324a020002008a14601560720203002283d06104400c1c1d620004201c3c00c26515600c0701c071140c0100d03083c0e00003a0001c1d600c4041c0342881203004004548690b030048801c802c06600103000f50740000d40074444940201c61000c4140307200e150092825803241c0c0402d110800c10344089603ea80004240401c52401d4840c40d4540c040020003010300c401c2510014a020310101454000e050f03441001c94140304a50a003d512143c02804408040006006102e501c0c0d1107840341240c240600e0761041c60000705215140125078004102c1032142d81410f08015580100702c0d00b0900d80541100d01c054600750078090100106140c10401d124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 643645179 1250 643643929 643643933
    0xd0c03030f020301051e0a053a080f07140709140a05040c09182109080f0304060e121606020705041833061505120615091c 54
    0x1a121615000e05101e401400140541c0e15610300400710f01045440f02da0800380d03544003140780610240c02403a08101303104105003403052a42c2c3c4030210365806003c210300d500040c810b6005a8000944010b020200400241039500c2402d8060101c4034040d100064500e401d824540380340070020740c4412001600c4030344010002c0d030300c4000248d20040300c9005000c9890155100040400e090165400c507503a10316010300703c0d40e03c0601c0c441903154400d01d40031080b04000c0b10010b8040c3e0260400001138807610001c80c025402140910a050121008500740360174803009a5002c0f002e40f0703034580c0100d4428003440080708200405e40005001d00148441c840c104080207003172401a4200a000e0782c10302c841c5502000d030711b80f50052120b802c0f0241809440c3c40c0c2c0c4800428680324107600501e201040c40105034032100b82d00000803684681c00340584445900415106401741855916900c51402c002800710b08205e102c40d82d00e28940709480346807000c00d50010b0348c01c0b00500c640056100082d405081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 643646429 1250 643645179 643645181
    0x10090e0c01091d0106112a03060106020f060a020d0b10080a06050103020a120902030a0c090606030f0e06040b040309050607030e0f040227220c0f08090705091003050d0c0303 76
    0x500511a42e0000000c43c00b15008583e01c0107105034400c000314483c6d080308001003400740c10301c14102022501c1084204000c02c075012001407605920038001c0400004074107000244045000b00100044c149954580700d82000030341214214468054031149441040e5490b0141030030000d005496402c40c0d41440180001100e4603500031505142c810400d00c08400d401546624504d030000e00b000c07c040802c1c2c8042410500c010b100140000e0300b0241c0450650903903000f02d810340d076a0b036a0800c0185034000d0098103544042e000e03178507203801202c00708004c6841050b90550081c0a41405d1455039945c00128007580e00810003600000c49902c680c9060b45006500080d50400070cc5055091113140e0800c2140003486c1358101008011200c030380d01441e110b4100e651680e506848660520784400d60941010b0b11785c1e0140b510005071034080740b91466001d00441c0d400341c001c1a0041806178203190920494481c06032400c1d965a001b0303180000000c03010010001289050307900d40d0542c2c040f40c80e000e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 643647679 1250 643646429 643646447
    0x16020a061701060f120f0f0504081b0d05071104140a02040311060306030d120906020d0c02061003082b02070f051203150405063c0a0e040b10090e0c01 66
    0x40041c130240c60070a00c0e80c01910030310481c042c02c0000a81c00d801030031190007000c2e031460404c4024100703070030003040c40080f0000d01244110080c410703c41380210400a82c441c910345c00500c002c14024819400403541c03154602d084290060b20004482e020b000382403044844c01c40c3c0240381e40381c00140c00e20030000f03c812034840800c025038800b419801c1240010b916541181c0c01c00080184441500c040d41c2c8480d040030080c0c507046401155900450043c2101404031526803030094852000403035408151140044101ca4005074101d081c40700c1c601d071481400b0540340b015858800e01509000d034001c4644010040740f031103242c80290b44030031032900c02d003040d19400c1f01c80900072045c01008059140d0304c000040b41d40c412540001c55a40c0c4000003070851038607207010341341050403480303030482001c095086001041e070f000a10b2400441020170000c201440f40940603e5620500c0405c1c0060b540c0c0100b170b0340241d1000c200ca2116a01c1e1600c0e003080303884803a941e003083d5000b00c450803400e5800130350312 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 643648929 1250 643647679 643647689
    0x60a0e010e03040305061305071703031509040f0206031527070203070804270e0f16050109090b04020c060c0301051005180d0311070b0c100e0d0516020a061701 70
    0x650f04042c030756220a40c99003001080202d00c0c01030000340303504124060006002501005c10b0f010154150b401e800d55a0780c0049030300c020503031001c0580205c98030784408a00e02c11a44410000c031501e945900384442900003600c0c891402055089160403503491403c0c0c41c8440304036548003551030101456010041002400700410b40d0010002d001c00304000e07030700b154207845084440c0c10400b00a24404d800c4a00a002c114018914100300c1c40f038850004209803010034003943c201c070b041d0b14444541465403a8a13101d0305020901445041004415a400c200c40c601c0d00280014103020031a0041c070b0070000112030744181017000000600892900340b00b0f64501014510b06242440c040da0584a01544066201c6119401c0c6401c6901018800c80d10721804410b02c0040e50b00b056075464141080f44c00c0200c2020f0f0078052000341004004091054002c07050580000f003900c0c0351100000d42c3c00354000c000c400a02401160300c440544c40f0404481c00805450b5190b6200d65101070303011103c0790f01a000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 643650179 1250 643648929 643648933
    0x11090405070f09090203060d02060f0a0206060a060c0b0c070512070b0f010f09180203010c1106010509090c010c0501060e2d06030304060e010e03061512070f0311040e060a0e010e 78
    0x1a403010b41d40c0f041c1c90500b84d42c188040185c2d261100000510203820011000b54046000541c4420907a8140047c0120802c141c0071a4000e03256041001041c1c11140600c500159440440c1c60200c0e0388200d00940001d6840d900924100060300c50790704084120300f40a41c8614001001420002a1900c269114655100020980d41021103508900340e0320321420b0109a11a885102e22841001e02600b0441c2d0040081000074204000a400c00c6585500c264140c0100f4000003840d0914807031702c500c101000ca0282401a81142c01521004a50801500c0307039035030b50f0004514010380c181d81130300482c041410980208212842104002c803010807000360b0703607040d0003441740c540c034000140c80540700c082c01d22016841e848001202c0814070030074941d500d482188140102c140c0503520100b5015425100040006000009166980014415081e81406110042010844018010b80030b004002c001250880000b0200c0385020b00c1620220030841e0f03140302c1c03010b01c134000348201501082d5801c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 643651429 1250 643650179 643650197
    0x8040312022103090115030605060321070201031e140a0b100c020f04110708040303030c020304080d0503040204020d021803071a0f1602030a060b03071d16121109040507 74
    0x1030b03021800c44105800c94010304000c004255185001e4002621404a220708821000d580341800805004280c1310780340a4003034800c0800c3c034051445100c108003c95001c82500d80003083d0300440003404800b4124400400d40e40d108540c2e51201d0041c041c400100c8555040181840b0403180b0490303580b04050703031103410b40f0028240750503040301202c1426901154011000c1904101003009018070380100340e4503900006000c82040128400750065074041d80e070401040d5400e8200783d80d42c0c0f01ea40104091765001c0000361880a01c43d0300103643c440d20141000d03003800e407041d5501040e43c1100b02c01c2d440c801c2d40c600004000d403c0c1007103400000d01c1000030f08003007010001400c0000b40304040701418101d40c00503241c600c3c0ba22800b500180c640d0f014040340d401804905108000b0901e540b01d8512074014260002030704250418640451249230f82040340355110706180d040036010086100342480002c60003a030360001c0610581541218802505587c0d40c82141000200e80340203280805000980d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 643652679 1250 643651429 643651453
    0x31a010816030605060d0e0712230a0f050f33040501020c06090a11060405010e040c180f1e0e041e050d050c010506090c16030311070804031202 63
    0x3016690421100c6680404100d41e2400c124058420f6030071a98104000256405c004242d40c3e101281150711761059941c110b03120088130b861182d01160140120340c40e45502d580b14203101c0040f010fa02c501d801200c40034101665222015841800b05450b41e0304020b140b80c00da00001c1c0500da4209060a102c07803580c1160340c0011401d0f24414520a04001066000408100003541101c007040030500c219030051414441c8595100000d280031030343c00c80c5801048505081c04001c0c2c5003a100c0c140c5541c0003d08490040c000100b05ca040c080080000c020031402071405a5100000641140103203200002d041810840002070159a0580003c0c1e1501040200c810324506140c1c010354465400c024003001044545900d84a4440103803681c043d2680c04104107400000910260111000a000740d0365403030100180e0341e10840c0c020810340e0b0300f0002c225200403001d0664411b03a209040028018086141d030301801c0c3c004201c01c640c480c900080a1092040d880c5070500c00c030700644000c150302d510310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 643653929 1250 643652679 643652687
    0x609110909130507061b0203060a0621080315130507120b1c0201180902030705091c15150305120309070f0609050402180d060b0411130b0d14090c01031a01 68
    0x24854402002140c1d58450f4000d5046c561401c0119001000c4550b181440e001c2540104820320480c03941c45000e542c1d4800d80180781c000e0184113900004080c1c203698030780c1403500c0c110040d041c11603070240042c5490501c88186105444c000d0880e036030341e4280c0e80d1540c288127040312181043c403803152201c000c041c0400040b104540750156820301c0d245485407811400032429040c65000b04c28440e001008011240d0b0b481400740a000000715514085100188610b00c0b050300128809072038104c541503820300043c502c0d04810303a000d022058000c030840d52616502c6c1040c07803219040384a0000001030085031709082064402504c10300004080b40c03450681e000d042c111321b510484c5c3c0583d80114590f000b40844140100c1a840050a40d45001c0014a45a0018041e40d8207842c881c0b1b20f80300d42c0c2c400100c6d0400640b41070404024441802904110006025070130003076490b04007586411068000840b511440390280e400071008200705801e00300003406840759059501c03201210028405550380c0c1c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 643655179 1250 643653929 643653943
    0x2070c090b03151303080f010810052205101a01020601060804050102041211100203030c0405060705070b160b01050105210901090c41120106091109091305 68
    0x1080d40009004600c00c40802d041415070080801260580403c10040100307004c01c0c0d0040d10b109940c2e541031660380c3d06200d801501e00b03020b4410a41c0c05016081a00d00c5c1e40d40c041c82c0c100d91502012801c1500041c400074141c0d105a10469450b00085000380304814240030301c11000302260581201c003111400000d42c0c840c0140b207400c081015040214050240030350495014001052484017441c103a820010f58041c5034450081c015801002c9001000f80702000b900e00554a80c80030510f441e1403c001c010303171034108000588240c00b07104c01c00210380008000501107446207040211800890b801c0483d0000c005034442c0f41403240c00c1290a54209070a012082c0f9461741188000c0030742c42d4403040900605112200500402204d14049025110780813101e0881c0900e440245151603208ad1480d041101e0001c028a00a21481c0e2031621380b40c000d080709001440c060001a01e04d41d80c5480005442c0c140903845420f43c0d00052482035070410343c040640c800c2480301c0002c1000050381d107296071603031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 643656429 1250 643655179 643655189
    0xf07090e0a081e0703031406010201050103020a2702161b06080105120a14030d06051e12150c09010305060904030e060c210a02061b030412090b07030c0b060402070c 72
    0x600082c05540c0b4040d010000d00041c0d46103c103154603814140f4003c0c0041c240600c58070714210b206800580b1a6105000b800e050741e60203030070000c03184d140076103600207680f1030f60640d1261000d0203000d41a4401c0c81c400742801c080901c62056104220b4281210500e030102402c1d002459845c034180310840d0042c0c03071541160001e440400b240c0c0c1d0900d851a0400c11001e1000700070b000c01c42803010b03003030f08000b000c0c01804901c0700f030070025195501c04001c01a08502c410070980c400c021164401480c003a05d07050203032001c01c025030f0f4a10065040001811500b01e8003105132030004100a01196854400d83e98000b2061703070212182d06050301c000d0041d0410540240c40b42400040f07440080f1000d02008143c0c0c51a00303a00d03045d500115080020503000041c3c0d00f00144135080000f12411051142036150741c0044079914038580795600c45142c20a41c80d40b0200038440d00500020743c211740c0c0d000a0851901950b01c00c0c080c480c19140003900301d82c0c0a4a0203228600600c080000325220f202d51030f04981e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 643657679 1250 643656429 643656443
    0x1121a13050312220b16120e06151e100e1206070201050c030c1c0b0406030c0312170f0901110f0a08070e01020309040e0a0b011712030c090103180203060106020f07090e0a 75
    0x1c500444080c51104887c44481e400c200100591810018546000718a41100180402c242009115110581c1d00c012220300030508460100e0742404188100d400f0309a1402c248034030545070120b68076540821044841d64411010400669030a102d44d64005200a00745072039410060303070128481c005c54200062500400c482100c40020700d5008541d0402c1c0540240f00240d501c3c20840009402c920040da90082d41800380140d5512a1002c100050809c02404903251036150141905450041ca6051690f5944002152000c0304074050034501c0d11095004d03607109203000c070080003000041c14460900840c581b008680360303004425211014002e40b400074ae0100440321461800000755000740651503a40c0000c20b080e4141c05d150946400000c080b2425448610740b0300e8100c2c882180c00384040c4c1c505005c0500150310a030850080d115504c044410744070740300e400007030804000381d001b007015078031505002e0102482800a42d008003041882004160301100e030b2540c80d403108880040c004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 643658929 1250 643657679 643657711
    0xf070e01060f09150906030b0f0d03050706020d09060f0b010e150d180c050a06050319050a02270102010e0316080c030412030e0901121a13050312220b 66
    0x1944540e040400418015540301024040c144c4050f000341c2c8a4095600045d0905c040c3e499070703091441c0103661002d00a400c0000f20302035500e0440d05500880d108a0b03003550204440c0b02c060102c0e0007020200c80c0250000210810301d03210520486039206091814052404c100481139551041640602e8031127414013aa11010311072000300900340700141c400038628500c0c240d0140700f02403150354191001a0740500321640c85800656907070104441d81750501100800003c2e6a02c200d410158101c4091074001d418003e02c8109051201010f07a04120702840c6030b41d0054240d030382405130803a00380303200c00038510b0b120015841700b805100c2e00c9009004600d00007550780154a04000315070007010b01040c580540c1000303140013012001d14464144c0300e800e00900103d4200d070200541c4407200c0c1d100c000d0204009002e440711400c004000d001000c1e02e4141650b000100c0e01c18401404410b0910111040038507201207800c4400580c03414220580030350f03252410008120254041e00004c1950400d071903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 643660179 1250 643658929 643658957
    0x120602130e0934080304060906020f030403200d200d02090604020a1e03051f0b090907050d090f140102030906040b27010b1002010e0d0518041b020f070e0106 69
    0x3c1150700303004442415030b0084002494500400944241c60b802c1e510354a805566407022a40c5071124204103640b0740040004000041c195028041c102d005018210205069040080c1e07210868400641e0307404031941c07c0a088003080b01481000d4041220042c2c85103205801141c140c40e002080d860040364001032401e00d843c00303140003c00000f10b01c2000003180510a0009015181c1656000c1203921190b8150b50801d0301d0410210a4410041c4002d0400c0d9241081100000001d414003052240030030001d21150351500031100d0490107142c60b84212035040c0350401008641d0000c500307007a441841031040c140c0d4041070700d03900103410681c1882551250b0071074042441401004504203080c1b50002c03807008206401ca034600c80300498807805584075400d0168240c40c003104812900b60803030005000218020400b034800750407050186000c082104002c502112606d0f82c4540341c3c6200b641003080f00903810406452070b01c3d10803002d007082500d81a1940070000c07043c013584041c02680041499 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 643661429 1250 643660179 643660243
    0x31b0e0111010e0703080a02060f042a090609140c07170318160302040e0a03201e0610060314060f121006050a06090f06080907120602130e09 62
    0x3d4144080d0152030001c2c0d41d0349000003860313001802c4003000d400781000082c0c0600c01410b0b103030310964101c064000c22903040c600000081400c1741c04034150004c10ba6000c2040d1a4902c180c8c0c0140c0820000000d47c94030103402000340f9500100481a80801042100001801414042c4140c041940d409440e503d90b0340781140e10f80c2921046025034458080060302c50f20080d00d08000b00c03030017590200207400645e24482c2e02c4a56015014000c2005e6050b200040a14803450540d0149a5020f41c0c00c0882c0401c004041180c40502ca07120a5200406100d0700001c2000d0510051805050821280f08038040c8100701c50002411180300d03d140041ca04465241d0100103104d40da00141070f50800850701d10420000c0200c1d0295a018141e01c0e0804203e5a0150b085103040c4c5480742c180440952030848100c03681d45000f0580340041c080c1c80c80004214450800d401e4455100d64009621440d2184810030032010310b500180e0a81a5202032221801020484650141480b1001d000548a100c8001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 643662679 1250 643661429 643661441
    0x9063201091a04030c060f0e100207050d0507091416120f0203090d0807180e060d0c030507061416060c140a080f0a021908091501090c031b0e011101 65
    0x2e007945401010302d1807000031001401940e2250031891011a15440202d8240407034034a16004125040e10203602d83c40c22030802000b1a007648100c40b255511100450304110b558802214558030247c010711100302180162049803001503841c000c41d181680d03901c0c0ca4407519414450622074020b180070f20301d05c4a5000b039407200b48148015941c9086c2050703840e07a81c0c00d8840d0990001000403001c00e004500c281c0311806012144990248110304010910420170400380c181503105040c0070300100010f44c807100800045011350058100d0038a000e00152016a0f40700b07200d0f030510020060384d00c020541e140744803c40c54004400092a030900c0c9410341d00303541d5a1184000070b00000c220b04406139440b40714a403068506028a43c0a5221749130002d00780d001c2c20980000395801e44d00d05003211446000c07119405800c01048a030300d12203502a617440030f00c00380c2002d00d91540740c03106400029014014802c500c03600e400c41414000000e18004d021f1403a000d2038504000140c60b9440782c01500350491 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 643663929 1250 643662679 643662689
    0x120f0d03020c1207080c1204270e12040905010e010510120b04060b070201031d07120f020409060b12060c090103020c07053012070206160512040906320109 68
    0x103a581d400645c2044000c9030407961484140303110368014000d208041c04103071b6044803032440c0e80c00c01504003002000154101980d040f417802d0342c3c0d07081e01c0c0c0482008100d000d070100385102d0071a541d00d08141101081c1d450580100c030322000b031080104480e8441c6010500304540a14000c0340160141030048090b200180209501608190300464070b405888002e1260500c04d80f020400e0001c0d43d0024110204501004040307a04030350004c12060541250100d155031140c41843d4510031903900040072501044005ea9681e0b0f41c41312582c80d42e00b068070006045505c80e00c0146a1841d00d40c544036094850116520704058000c940d03150302102c10490007000c1c0c4402800410116500070a0100a41e85070252800c030a9201000085840010551090403103448109900e41010740d002c0c8403060344036500c8030308402403a0304107001040b0244000100740c50b41181d43d03079445280018036001d036280d0f81c1062a549404003050414051251512900c00700b80e0b110451a404030b920044e150000a913001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 643665179 1250 643663929 643663963
    0xc0807031b030906090e06030c04180b13060b06091e06160803090111070c03240f050103110f010206040b100312020a020a06030606082a0a030506120f0d03020c 70
    0x7500d410160400d52040907907100317a5600708040e646000e1400b4011040c2c841c2c503016000000590442e0400f9001716441d10001d9104203411209681c0306010b10310101e4003c6044004c001c03807401000a103004503000b102c0c084400350f04006000000401c00011804542140030b219000c408245d01d0b29000d41e00900c00d80c1c50090100c1c2d5080c00c0031001c03a0700c1211906200c1d4a020704018005e00404162160940c10100f280c030460708503900c0c0e200030a151a4a45030b01000c291000b1010009405081e4025076035990100e80e41d491868548485140c00010a03c00c0c141604510700da641d000410a51090300071900b8642e03a12150b07403141c1203200a400141c01224a040c803500c1003a00015040802e038829100440e11550740c150440031515503001c0c00c8001944030020401e04401d02d0030001d0700745258070341c41c40e0b10301c0346a9103200c40b984610208004039858104000342444c05c5903180425541c5070b8054444540c290102680b903240b130400c0d4030203040e400b04000b100c0c09801c10402c004007200d408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 643666429 1250 643665179 643665227
    0x18040c080109080702040501050108040f0303020a03020417032d1c020708071209060327021201050a0603030e090106050301261608060a0c1202090303120a020301150f0c080703 77
    0x404403c15030060f03100b64016130901c80002259440ba14000b4419500010003140c0801c550fa0110060b600180d0054205a0207110200f060022014910b051040900c020b43e82d82c5c00702e02c40b05003540b00b400491203007911140c007040b14182c60081110401c0600d85480300002d035003940c0400080c002c0030000381103298003088000030041c10f0002c0b001c1150305512510704950361001e040782990101001610f042d80035948200342814014440e480303040c8000c1485500c644040c50340c0c3e08642c4119400428151241400c10a16400051a03122000c0982d034540b400c5d0b04000c0d0103401c0780300610800302c2606584080c01c10f6412803041c0d002c600c1c4116825681c0401d8070b541c4030341c2d08005502416000e80180404118100820702c00e007020740b24030b40c844418402007903e1200003900520200d17a058001003200c2d180a5041c10581e40c4184c0c3c0203040181c59505020404d00181600b1340c034602803043c4d4000c080c9160f07030001101e501d0180c1c04010f90390380b01c0f111703d8201d92500303258594501d000c080315 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 643667679 1250 643666429 643666433
    0x30a170903010603141f0c1e0c17031f0e04080306060c030408010f0515010c030f02070f081c0207030c05091b0703020109060c2105100506031014090618040c080109 72
    0x12942c2107280480c1b0201020340c4c450156498103c8041ca400303100070494515419100243d035503044140c00c1901c0c145a04042512385070b0390800321200303c0c5003484c03010000420810078004c03c4805d00581c0741811407200d990030035644d001014000b4101904540300400068159a600012a062201d0303503810f403629030b503460010358003a01030f20041c00c2489050000003074503040040011418040169603090b04424162000d50b800700e0903903034210460040b8030380820301034895003403c001410500c0c011f140b000c00d48003107d903110010300c8280c400c54105007407c00c049071454121034284c0c0e0301207880102076110341703980c00800740c4110385a203900c0c84081140801d054065022210003800703503101380a6200808822030f0b01d40c0b41007034515a10b842044242d0011212030b4000d40d4450708066031724440c0b58035400059400c1d082180c80324100140755106200d40c2e0301c08844643c601c0d90035659410a410210002158580700d244c00158980d070030b0f40000c0c103015400b0340210060042070004c01c1034103118 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 643668929 1250 643667679 643667683
    0x40b0d0b070306060c080a030c180e060a1e1a21070801140120030403060905070f06031407030c0e092409070203120a060b0d0e0c030a17090301060314 66
    0x11a038010102c1e1030f022000403500d0040403281000307a1302c0b000903441e1000000e01034008014003031a0b8400c22100b68400c0030310f0202580818013416008800006501e000020801c810b13006400981c0c01c8040c1d045034000b40d0307111807007100c00e07540030b40c0d0048540500010071034440d0045101c80080d8001da00d8100050306420501c560003400b030351f07584000603070b2a4109030100201202c00180010340101a02c0600c04005c2e0000c0041010f54003174914082c0e0303a4449100341d445004090300c080c0c0088808100c0358401492010003404581418442030340440680203520720020309400516844070030864155124901030466000014480310450034040905400360741c1c1940402144c6c4c200c405942e00350319000c819644079448a60043d86014404000c0440c3c000c0e000e8624903242d07448880103d0059001c00c0070b42641021514001440031186110b075242800a04046010b5005550600040303038030156012035003124425041e5030f601d8503502003801040345600242030007269100e070410324440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 643670179 1250 643668929 643668931
    0x1309110402191b05030f0d0b011106061009030606031a09010608072106110408010b060f0304060b0d060509010b0f0d0f140f16090506180f040303110307080a0614030a11040b0d0b 78
    0x7d21100f000000c00840042d5440c9490300003800c042e030721071000580e0a1400d2403801745000700d1403400c50301c1540d60b41c0d144e105640190300200c40c0b0243d071070032001540004440c060b500000c107e00a00102d440d01d00e005803074185600803800e001070303804081d04002030364400410455601620400411040000d00501c68009025882055081070300b00811840d0040031b03034101c2451041441d1560f00d9076903815000380901e00d000b039044210071103403102041d1140704007803260021000200c2d4203103134041003011150342d180d0083d20034240034003003401081960840c1039000340d2003c00644400c120001003481d1000902c07042103181f007844007070890312207115010f200300c034204502413045480c0c00d001c10184035450244044d20708107050000300481513446005402c14000d00b4001006880b20341000319a40c01164400041001030b424400340f1042da00c41e8400a04444000d1000300d801280046c1c2c850510361000b6104500d03107140c034521a6255030082c101d42c1401454071100b01c41e14034042812801c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 643671429 1250 643670179 643670197
    0x151e0315050606070b090114010503010c0203030114010318051f0516030b031015032102030307050913050a0e0d082e0b0a02210301050a03020415051309110402191b05030f 75
    0x140d4070340004ac0d2030505005d40040d10350241c0265045a080110b04181c000300000d5040c105038480841002001d2080002e0740030700d0254002d824040000c005030a82c4000268021008609e41800c025220300b9100c0603050040461030041180c4007a40c00103458400c80b0100404060300d800851218541da003041082220f01c609501d1819030742240021020115032480c80c1c01507002040000c1c022841800200300b05003000f002554984410010b03074049942c00c440210703000385c0c4c03405401c10013881040500c01e249403c0c0780c2001c0c945409900d04101100307003207002c411000c4054002c411020801031600c050600e400c221601d034080301c44005c0d6a0040899054440218049440d10102d60b02d02220f0580324040c102e4480140f440d42400020860440b402008510740000440c0c560349241402c003002c43c20010103c0c80360355174113203d040c030b2080d035861074404c0d8410403c0030340003020510248844995804c282004450700688260006841e40e001400c1d03003c009118409101d10002825030f5034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 643672679 1250 643671429 643671461
    0x106110c030a03090314070806010b1b0f100e010609020a031401060905030604030f02010b09011e080303060a0504050403050c12070606050909070b091201151e0315050606070b0901 79
    0x40044041c10340b00d400c4601c0190014010b004240302192031961200c62109140049900c880d54400200f07007840402e8100c80740321580000c128084034400350151382c0d07090030600039020000f18a110346640b03001c0486502c001540310303c03003250310710420360028000b41030a1030305640d1000f078403100070b00802c103003100389084051050000c2507007031084021906844014000701080c0d101d03a14103503001c00b5490380000440d921021448059159420304a008096028250300380c400060440d21543c11507811a070603960090040001c46d6031418030200842d1802e990005041d122410111682d03c0344820014007442500301c1107d072141241e00a002c0c40303008020820000d51180c0410290303820944840200d80e02c00541844915403900080100c0c030401064084941c81715031045094404410208e680c1800f10070003044000051450511400017104040749403c0c19a81c8407900a4090004243c055036034a0000d40161141c4084854240d0010450040f502d4021105c0c1d0203850003e030640b03049 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 643673929 1250 643672679 643672693
    0x60606031811090a0b0d0f060614031908070215031909020d122604051c021908041701020703030e0319030534020d2309010c020306010611 61
    0x1c1100c1901c258a880d405040a200200404100440c540c000741111034142d42d106640d406654524010201c41ca00c00c49844c5054002c60070604201c45113640101c1b2060400c203000400c039980407680403940400c5542207010b20380385041c100114050518000d41004a00426070440314000c000346100b102208001103842c518108800d05841a0316002504000c600b203e6100103800180e04160002403490b04941d0b500d20010308803803c900f000351910351640150b0600050220070b00880300304800900007810284000e2900a58443c01100505c91030507030303040304108000c0e13094100d900a00f100d104010340b00e0200c0c10744a0007540070810441c042171a08007801141c03000402958400d040700c4550520059051000798040c002c01003d12003502c40584503102c40002c043d16104401c488910714420403038074000081d18080a2a80c03207404d01045010314290b030240704040c60300200401c51403549420f0340c040141d44054510000070b50500442002149040d440111668000a408122016 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 643675179 1250 643673929 643673951
    0x2706121503020609062217010f230702160902041403060601081303030b0910050312120403030b0102010f0c020607030f050f0106200106031a010603050f2e0306060603 73
    0x20a1009100094100780140000340242c90107038040c013407a00c00c20580749281c9025020302801e815007600205000c03030040086c11101f6400744030b1881c03003d0280b8401c2001c00101044e4110408108600c0703540184c0e031100184041c0e100707000e41908070002466041c040360b2154902c1c0e006c0c1d040b0340500d414101005138102d10f9882c00003001c6002d074506071640e90b0340b9145c1000c01c541202c017031402070701071540f0740907603066584802044602c1941c1034518044413604080416050482d0554584485002400101c0c0010054070304150007a87c14180003d21007054401030740903100f810342d504002454a56158078180d00411028071400395035408000d1040c110309114100c8100303031050300e429900180103005440c01030303411040407102e10181d9026580075201090940e440380d0811204a510341007101c2011048801c0b4601410a40c1030500580c44d2810302ca50302060000c01040000b4201a0000d13580b001c42c0c50074511810540307880d0449940c60341002400760031580701d8800040d203450305181e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 643676429 1250 643675179 643675211
    0x1516050616081f0b0c0129090106050a1b0f02090a05180109030e042304200609030606010c110301230603070302061c0227210706270612 60
    0x40c00c3d0301801c5004901c40d003000780280d280d030810700c280d0126660b43c45c529141001d105400030800030104003034044083d4854140301d0402c41c10383c00141442070600c804000c15401241440000032400d006200b00c80840c20150012140780202a401c8079881050080440e89604402d1040d101c550961121114620036517080340d52044025002600c900d0011740c0c14a03080d082450b001210310700882c04030340018240a0000825107040762016003140d64208814901c0c0910074582c2011242c603420a80c162000c2900c034040103102c07a04020000102030108000315100900618000d0001c02000d049904601c0031101041100d000b040014400240185400942c617410b695001d07203201c1c1084800e00380c04421810029545410076024460303051065050f00034100a8100070b01c0041c1d14410748030500c503501529058203085052450180307201c82e000018804100c504600c1c1072414a0000f00710050001400e052580c40e402121744006440d542c01000c0a18190601c60104540712141c070400f5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 643677679 1250 643676429 643676461
    0xf0906050f060105120c0f030117120301032102100c090305010605030c01300207060b090f0c0301120303020f0c150a02190309050f0109060203070306090203010302151605061608 78
    0x3400103e017040348142c903d00030780d051a082111b01c402c00b42005002c6040c0b0000e60400d1b08480004000c445040890704000c00400d000c0c500c0d5004c0301490f55065440c0c00b0b5801c4081c520440300d45940c8403000c27201500c01c01c0154810811a04208101503108000a28941d940d11040d6090740c00d0050110f02c0746030200b000c080446058480c1c1551942c0614400c1c81501c5150794501564460a600c4060f03072080c6c0010314402d4844c4000003203400f0780a0402000e80006040000c035031103031400700401c0b60105011203064819500001c4010256441d080f000ba1144d0900d05c441e0701c9010901103180400010001c440c1560f5a140c0b020039a03031001503000300c0c0141c02e100b02501407115039015145001e80d0180401c076000320b06840300c0c8030006a845094805581d02120070070750020800201c15450b00c00e41d0094002c070101949903514680000d88829032640b03e2b11200c56002400040d43c0c904d0164a2000342e6021058458521b02603204800000c005a603c2c400305c1d0b0f815001442803c0078118103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 643678929 1250 643677679 643677691
    0x17010e120d0506030f1c110d21020d02040b0d0b03120a0e01171006080601090f09230414100603020d240e0609010e0c1804060b040f0906050f 62
    0x3036810702100403034071070260502030b001c1901400360440e02400740a00f40890b41019841c0d000c2410025201078000304030320418448800c440d007120500d609225448040c01c0302219140101e00410038000011000130b100720709135120101d100140024071506141c0c0a40a0b40d0590681082000c5900042c580c480f0081074403100b039010100049140d49000c0c1903100b001a1f418503001034014548805201d880300259000382c14582280410046d155020035050780c044c0007846c0203022a031030010228100711044c044d400070b03d615541c612200920f038814a0882580c074210b804d54030304060400466500d1000100d161a001c0e040b400b112840b45030140d43e003141d50260001300080c4164030380c0c10744042c80d007a9080e41c031103030462102d40f80405406021155119a0060512404d01c26541821110542445515504001b002402c959180c07600503510421422140805603554034041000f448102200d070b600c246032040311682d800d42540000000b6214507000c10480d216440c2d0b00640340d100300c3e40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 643680179 1250 643678929 643678963
    0x60806011d07030209060c0c0f151b03071b08010b01030b09060f0f0a06200123070e130f051008120a120c0203121f140607020a17010e 59
    0x22148074940c0c1d880c42a0701141c40d180060800d01c14000140c540e038070281201c0c91a901c155440c00d80e6151200d246200c9010480300980e8000080304850354500800b040b84010f5807082e81030490030301c401e1044401c1598801e04501c2e104000004c5010b4400036030003030451942c40d1002c4020b407035029200d0706242c150010080038076940c03410204030000309480c24068000c040b03800102c0c660b403210b900040c05001e507500d9000d505161841d50001315404440c0b00c80003681840254a03c0d4011481048000c16004091406540e100041620f840307030060f0742d064001c0407500300182c2e00c8940d42d00c03100c0840c038803640500003a103499103018542003c50080b1419a00b090000710542d100c0a0000c2c107400050b41400f51607034507528808411540564000c40c050f0b080001c800c500254400412648050a050a4410044a02012324240555000b6128260460b0030f0341d12080d50342000799001c1d03030b900820703907040b1036190801c0110311141d1000c0d032402e641c04c1c1150510120340100301d01c8034000a03220 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 643681429 1250 643680179 643680209
    0x70b0d15080a08193b0414060f0d050604230f060606031503010915050705070b07200105190c03020403030e13020c03030f2202060d0e010b130f06080601 67
    0x10460f0501d81d82c440c01e07038007400700400940c43d500e01240e200d02150f142c1040115128450038150300c040840c0300d00700a04c06c910b0542000720355910a202c0c150443c106071203a00c05032010201042d030050312410f01a0203403148104007c2004460041220344400748580c640910710f03883c0c24559a080001958503864200c0c40000d10b8030b0620001441e13000442084900919804030003082c02c48904040c15141070003401801600b1000a0091903005500c1c0d1501900e818002d48807011070010140400d01004800c10404680f007000460906202c0310074002002282004401e80c0c1081c1c0c220320300c1001050600e0889549035001e4802e075811203415803140d6085c1c9061904014a10b1555280c05503102e5003403240d03138040700003003014520846000000e82000d0500c1514403501e04010200b5401005020a1220050312000c099130005120080040342e02c501d03248000740503000c10010f17250841880c00c0c02e0020200700340c02000003071040100410446449041841d01c0d010709008880306111140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 643682679 1250 643681429 643681447
    0xc0e060f03040b0603030412030e03070b04080604060b0d1a090d1103040902030c160b190213030b07031d0717010501051c03020c030303010303080603010c2f070b0d15080a08 76
    0x5003100b0f03800003005050700d1502351904802c0401c0c941150099000a00c420304210003410200106c0c8081c3c510b074484181800d150403c40ca41d103201c002c00062002d81c0340d401100c002e8880700303641c20380280c1c40881c0d6640154154080c01322a0400c030f42c0d4000742c0c4540c039449011603016200b500c0d040d42442015526050400c0340782030195101403d4512481400c0100c1a180b01c5611140b4621070f224110392003650400b451a2550303003c0c0700c030114000b40d03c10010400040e11030300e0301c281281d52101c22a1406d9586450507002484d800c800106d40b42c40e0100341000440d800700784041030741d90042010b0308810302d480100742290001d000c0d00d5000510401c5801240a5158460401d03a101c1d104540d000010240131a0840c0c00a07070084003c03442d81e00c1481a6460203025485400307856240c600340840d420b40d8a046050450040102c1c0f0004001a04900300c1051045202900c4000e900d150382d40290307400303400104001204a41020010314000c5081040070907825001c40d0007e14603820500e144c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 643683929 1250 643682679 643682693
    0x5040803070f0c020303130e010b040806040f03120507120c020105130f170a09051c03090308030604060b0720090c0702010f030b0904051b0f090f040f02130c0e060f0304 74
    0x3202c0e000601100ca040240140d604000401e030f0b414041d030f842c1001c03a01d48405c62100002c1030b0001e06a03040e0500091210070b90010b042944a03070040c8215150a00a0400391503d031010520b5805003030030305040094881c1c001e1400c908180e01640100310f0711412071012401c8400644003174526180708001040850404840007c10034064200014820306480080460b540a408054082210164200603a20b002c5d4900441c20b02c1050b102c9030142400d0754001c3c00074240380001040c401010011603c2d903191a800000507003442c1590640d12030304c1d4100b0a20009014040d898620b000003452000350501c940c80a0041044440342410890f080d0300540d0301023915001882010b5585288400c180e403403e0005024034014005008080d84802d0114030180392441c215006110100426040360ad030000b1403035102c0c0d02c0f41d4031a541601d413450009031240e0385c42c4011f036100d80845001c180c00d6890741e200c02c3e94801980c503842250703130b44001803043c20f008104411180360020b0002401003040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 643685179 1250 643683929 643683947
    0x10e15030c220618031e140f0115050312270901030308060406150f030917210601170414151603050903030103081b030721120504080307 60
    0x80e0801107410004504507800c02c1041e1160300720502e0400e504100b0040c0d07001041a400d21030300d284034241090840c3c490081d48094a207110044030741005c0008244910300c40c881daa414920810740791480c42c2c1081d850b0191034050401e083d25180c0030800941071400180206085100d420207074204285c6604803070300410100d04001b60444d9600261880d5611052024082e42c031070784903141030b800c2c024240000c549140d0030900c110301e074071104c50302c2c03458100e15a86103002840c90003040302007040c0707044145414040f030760410311000424000a0500c0030500c1003243c0c04054071b042d0080d52000c00440350403a10181c40c41000d00e04e900440c001c900080f0490100d4000305007202e41d0302c441e00c909680441c2c403c4400030f104d442c3e140a200b000d01d03458090745800801020085045504544947c0c07500d00c540340e0b102000240c0030040b850300c1102030096918068101d00d0135051140403044e0f00024041e401ea03003400041d8110304001c0000317440d20038280515000b0b80a02d04540d01e1250580748501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 643686429 1250 643685179 643685191
    0x4181d1c0c020d0305031e0402010e10090314031e040e040b040f0203120307030b030601211a07090f09021e0a0c0602071a0906010b0f0901050415020705030705010e1503 74
    0x34401081d80056110f102c44540024860307a00c00f5524900b00c0e10805203020507856169840c80004184000750303034011811350f1003440440c0c0d070029440701c40e0401d580c0062035910007030255a11500f0700910074130200151100200088602100401c0680ea03808184a03601440201c400180d02140100d0480101c4640c0103202e0700c605c1550301040e40010f464001c5104008924500000030030440c50341c18040e10090581c01c2d4014440f6506050007020070051701407140100c1341e004010300e018030101e00080310a00094000c0030390f403803c00880c001c203c03c5850107400e03503a594071400056042c10610848403d030784a601c0d039a5110400041c110078550040c0b40c007000b004130021211003c103040d4070060580603c40c0d555440941405611007032000300041c16807440d600018010441504080210b4a221640c034015603514407010005980c64000d40d0058140c413510710b048a02d000e41c00140b42d5080d120110203c9807843d07600e400440e40c0c05403001c64990028448440004002a12000b440c2c0180f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 643687679 1250 643686429 643686437
    0xc030b040513110409020607120e18040201170906060114040b0a230a02030d020d1116050f03190311120c0a080906160c030905040204181d1c 62
    0x491400000e055503015104580c1e00300d40000701c1c904100d5012039140007044151000e0110414a400240f0700e4001d5550103000c0d5086180131009040c8500031544c4840c070300a101000303180c1182007540706200c0844041307000c1010a40c2c10011000003a420303501c00c483d40c00c002e120300d54444004640c01d624007118100c0c12801484003282c06406c9101900c0909190364130021000d60205510141206003113403030018880412114803255800b2041f202c4c0706004038000340ea80c0e00c1502c415001003003025841c00201102103041140c500101a0300c02d034080c0103000701d50001214203281c680f40c1c41030000c041124400151b400900030b00a8000462811030003030101c3c1000680044511510b41c1244c040d40e01c1207000801c1400c00f1780002d4501d41040740a0700a00a074070305104611310382c40540e83c0480c203004179003106004042c400d0310b246010b0b200151043d922950b88200d4242082a60000740074100c0c01c00d40200009140708180100c4411135200070559000300c00c800c0c020240820304104100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 643688929 1250 643687679 643687691
    0x1a060a0309080d0e010605060403080a0c0f02030607120e010b0916110a050c01020f06040c0b091210060f08060405032a0d0c0c060e03101a03070e1506031006030c03 72
    0x402c00d107202a000340c030414203000c28020895003806084440b5500b02c0c500c07541092000303101050740503058890024403404c1011140281e41401c50000d000f080000303605100e0241000003581e0300068a41c2542007030b00080c840703280b90640360b9098900145006400c030b0042c400140f64160700080000740c00e1068101050342d4004450881d08003405200c09840c958009241c0b10442d50b8104003030707040e0071008400380c0340b142441d986a69101440d4460b000d0010404519407407140d44904034641040100400c6800354114043c400010300038901c103211403e200700b20005240e107004500144281e9001014500d42107c4000b0030142d055180605001e6003c01080c88c2042c0a003041094103a103043d86030f040303980744c0e10703c0d108190031043d4011ba0208440d00255103000d4500082603850b54100e10f1000c00c030000007070f441c168006100c0c0030040c1d042c032545800268044040c80c400c0d001d02070700084904000110020710009100584142c0100030010304c00b0000c3d01d109500a00744040c0074076002c02d00d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 643690179 1250 643688929 643688933
    0xf060c0c2704050d0206090706020703080d020f0a080a05100e0f040c030f0c090606030c0f08060f130e100b01020712050c04050a0b01020601091a01180e0c1c1a060a0309 74
    0x1490718100e4084500d0b0303000222841d400c3c1d0301000700ca13610011100042005d1030030010007d4503140b05100041c04a81d0100d55400f2150340741d01a2201a50140200354442c124080d004140e404181c81005600f444c03c130224171101c1c04d0080b15415146000801400e640f0f4004010baa40340c1d0041055400305170003040440040c071030001c03107002c860040c08080d16050500c5d002e14100e4420b07510200a0600c0e0103030070a1f280e80c12001c0910498038138207040100355141c1e000719540c40121918940d101c0ca82d12221a140412584503c0d103510a074011505080c00f0040340400701d6845501e9680543d101d444108003004070b01031843d01c081d1042c0e050b1400c9440d07440c04101592029a00c0300e21868503188001242c1d41c0c100035580c01046c03800b0040c081140f089508020700d1600e0a10780341080051074289c4456141c0b00c003450000c04d80103064103124504004180015003100130005900c0010290178010701c4580e0190b49403001c4c0300d800c03a0180030180303000c004050b4070031985942856150b45111b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 643691429 1250 643690179 643690249
    0x3150406031a01080105041112070f061d0a05011e0903051b1009180c03021603020a0512031e0916080c0f2b0213050c07020f060c0c 58
    0x4019803048070741e1185082d200d054120380c0321058100da40d180c0e01d09020031000c160304000d00c0707101d24003c1d20072108403150000c0c241c1c145601034110442200c0c10100028045a0107004c2800000301090310841c0140384808008100c802c034407401d40050f03583c503221500b00e060005440f0a03007002d42010448076940c1d540329070602c540510b108101900c002030b08804c46c00c0a81002c2900e229078030300048610b007404181c569035004070023020096913990740c20304202e500a904a070760f0104500d0000750b194a0a00d8025a51651400104d425002c4d401b40017106080075402c1e41d00032030b456065040904081869290443c200030202c00d4184a24254402a0080c1246840203480c003600540380603000352060104034546503501c14054980c40314268200c8501c00710704281001040c28881459203540006003941c29442100c003038862910040c041c0880b00c010040c50800d2081e0307858000d0b81880e100b0400f0700e000710180b0701c1d03d5400007000703004c49140404001120002c0328043e016803440c080000d038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 643692679 1250 643691429 643691441
    0x601090b06070623071704080307140f031e070207030602030a060905040c0521030306120a050d02060619030b040b100b120103110316061841060f031504 67
    0xb0002130001c1140e0940342c0c00009696032181250070300005240456405414010703008002402160020010a81040c403401c400044084072070035094554506000c01c81055009946200c0c0b07124804c400301c485800e00851640c4242800d401401c44140b80d0b84849020394002042010a507a0f07030280451180042d204050090380641040c0d4823a03030070320313003440281d00302100311582c03c2002803100d160400e0b000044039405502a0346119045075001485840d00c02c1403030004200c0c2c041d4100400d00180d0000d40d030352060030120343d8106480f88918202c12419014003014010040c0c200001e00413030904448181c11020618031109002c1d0341e5183c100403504000e0840e11107040f00b1004100340085000302100003c0c08402901d000708420b90842d08400380c0744200001e02480444211480000c415484000d00703100c10204a00803894020101c210150070030491148503480040781a488200c2d607035044608080e06c10361400c00e12080d10314881c1c100424404162a801b070b0500c41940710350041e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 643693929 1250 643692679 643692701
    0x3020316110411040f180608030304120905010c030c0605090c061314040203060604060c060b0a06200d02120906220e130308060d150501031101020d02010209030601090b060706 77
    0x1101c2502010400c01c400e4651880402407a02d0303042c4014020b5900d1400488102d811200340514201d5603a0050400790502e03038031600850001004100500c190030016030356040700f81e40c1e00340e4615250070055032031940307500000d000160b9850b442d1002804542c0000e400c03406610031106820403040000740380d40e110280e41c2d805c1a0040e031040107904801031010052403400c032025811443d002d4003062460003548688c07402c120b40c05924800344200d85e03202404528000c0e08046000b030316090003501c1c074800c0c0400b80d940e40850100c94400050701003080c48c1d058600b45d01070a1249411304060045d40c001c0110b0340c1c0e010314100b01c1005014020220051294203500194044900e010090545028010000e50f00140d01021000000b680f2100e4680c2c00a001c480d07030169890281080040d0300712224642c1c000c0c502d0080080103001d541450041c24910903422500c2201204004a00340c0c0504809107805600c5000180821003603038001e03611000e8050881400c0010790f40320758003960300301c070b031a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 643695179 1250 643693929 643693943
    0x3030f0c1b080f010c1e080c04180b10030b030a02040b01050c06011502010c02150f071b0308090d02070e0c0a021f0204030c150219060e030a0e10030b0102060c0703020316 75
    0x242c5114100f8002d40410081714200440c580d5041c8850911451350607080008011016001a180c0150365090b0b030040c20108107240401032403a40c440c4002c150480116201d6034880b419400a144a400303026885030b006005803894040c04d5080c04041d2a040300c1580c103010701405a04500c42c0c04000b024020031112410242212008030003a003102c2c1c5147c0780358215003094030140e481002c0d1018140c0c1080350003012601640e18603004490301040c4404200203081d401070340038185680501d210f80214415020340e02d03404081c00c81669aa803e41c490080103e0102e130010303004445040140c03998000c00d0055072500c0b000e0000702d8a9403400d011803204101d07804582030040c00010340d580b001401a1200405150b902610041d5680d240e0501c031112881210584008000c134a42154503458500f50440c0e0b02d815034910040d080f140400d08a901030307022440c1c001121032003401034040701101a0050030180d00c036080a00d10580c4036007001c1c2e0a43c40304201405030b042c205400114124003440c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 643696429 1250 643695179 643695193
    0xc0d0c05100203040308180301150605090a1e03030c06020c060106021b09041a070c08041d0906040b180c1807031401060e0f130204060903150603030f0c1b08 69
    0x304545001e680d0149011988140001d00001c0e03d400d0031100030084c5003602c100e4181564000902401040303450b0301050362420000100305401102404d5484802c540c034410040d11101145501c000c102c03140150340c40880d004001280c0074468101c0824001d480143c600200b02c803030745140010a038840001a808007203501d42c0d062842e0301b000e19942048031134015504041c0c44115110040490208540e00e907100452078140c002d5604158540c3d0003000552030720382e6100d194125800d10310010070b600001c1d6000848244001c10147d03c109c2c3d02c05440c0f84079460300080f00c1e11140b00c0400740c051074483c00049802e95034540014601c0701030031002d48842483c003c800103080c1c9407100302c2c107410164000f00600213107030000341e51604c149080d1b0303007880c81030310400014450f100b100214801c4a440024045035403940000e0810580e0b015002030700300841301f0380c03280c011a0072520000e40000c0c0d010f402c001180744200410f810300b41c0a0400d807600f560700003641415441040d402191154003080b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 643697679 1250 643696429 643696439
    0x6030c1412070f08090a060b060c0601061206090b03030703201006030618050a080913020408030c0f070b03070503190f09140109050303011703250201080604060b1204050c0d0c 77
    0x150303008002c1c0d846860b044c0b442e8142455184d6170b580b015800148100d44480c200d9690b6282e010a6a9103030384290122010740d6904c00300600982d00029034041e00c5420681c010900c00004c1c054100c0945000c0d006516040298800312420720200b44803e0319071a0400f6030314104a000c01c00c284603071121540028105282d440c000c3c0440c3d8881c01e040c0109040409130001082000c2142084a50400d8426940310041c600041a101d10072003100c501a101003808201040000042c1403a1034208040b00d0021004100b000e50f43d5030350344a074981540342040050b000c135100f1030103503801480c400d50480c84403c1c4025685c05440700c04120201c1e080e42c45034140244800c801c005136410040d0300c0201f01559031902d410307450340700c140540d07c184441090b030341551180c05c004070741040c840030500010036000c0d00c0840c074289500040980c005003041011902918140c4108001c48618024140c500002e0810070582c0450041003610340d40150059841662180038407501d03401c0c464404048020b08103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 643698929 1250 643697679 643697687
    0x90503070e01260c10050912071e032105070206040306050a150506071b0815071403071b0f050d0e130207080322210e0405070906030c141207 62
    0x58440010410f5410f031002e10500115480f480d40d101500e00301c00009014400340e415100311519903030485000c5a00b07110700070380400c0c80425512000166001403250403c8851110410300001d0588100012401803203403a565940111041c01e04196042c12603a0b00002e190741c002d94020b0701c0d11511082084030790155441030300100c98400c0c0c50621031030306150218206d4042c0701002800322038450841b1483e101400364050081c00c164007100d450010814980500103400d5030f1181c042500c50108007483d48c1c007001074138880c3e00ca03585c91241c540f201c2c5004e000307030307100c1183d06499a2046d1814000400e50900100080c0765060301c0d1001d01083c078000f40407003280401c03401d4604074818441e590005050404694020520092051343c3c2c0f0b040d880b10585240540342c00405580340415001c500702c0c882d05650390104459190081c0f42e0b40318000744010342e841180c0c034500091944009104035802903000740c1c7c0c2070b0958039206540410403a9075803080e50240301000d01d504196800c1008050380 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 643700179 1250 643698929 643698959
    0x51c1b051002011a04110f070507170106050d082a060603070905010510140415020c04180506040212150903091c03210b0306040308090d020307050304090b01090503070e01 75
    0x2502c020440502441c9100c0404490306200318400c9840e0488440101000800c1d9610744a034880065902c076054507001d0350f901c1d000c1c807800c4280d0a418103112006da4061186200319a40070300041000029661003255a034010100603408031804440080310300400720b810014661800b0041c80035040580c10180b52440943c00001c0712800c0c80c00500064403500f16641c51034105040100400d4070040c1907030350314050798001032440c1c00042000b00980b68000380c40200300c48190f0381000109005d68903d054804022000303011980303d0390109005042102003015a100c40b40c080c0c8400d1340c5880b01c10319440b0700c1910081780550012031400307900d14040310440b401e01101800080180d00540d00540f40e0021038200c200f1400e1200291915038a00c0c0c0c1001d06620401400d031600c52800349000f425138030b002e68009102e4440c001d80c0380d030381e21300000413503002580000003541031510302002c0c10050b045900182d4104440120006a507440400c08203016003c0890722885540c10152a000302c2c40c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 643701429 1250 643700179 643700209
    0x80604020f18010219050a0308060d020f1003180b0405100c1d043207091406090d020306072019030c050a17040611030c0601051c1b05 59
    0x1204202508007040407030125a41d8140e19264140d11542800c0180c2c2810600040d00f0619034484802001b00540410018401032098940031040c0c0c54040a0105220301114005d40018030041120100c2c03030001a0000e080c511446c0c00315410000c0303034840d03110b147c104070120b0b002e8403e50140000c101c1c0601500d4200c454200c03007002400c03040d0703070300404010130309900350444c044180546005441e1900146c244803040d14801000ea948039002c5c590002c0c0d58480207462002c03050100d4605441007a002c402c481280700740700030409820f030402c84554001180c0765804010083c120b8016141409001e10070401501e440202c641e000300e074400b090015864070310250b0041d96004031341e20b0702000710019564041c548040e071401ca0b440c016141407034101015000c001d00403c1a9110030b1504000c20039540f80e5907500b924450b0700d200c841e580303002e451080901500250014025428007890300d0444c00100100240c04c0ba603d615800031000900030030b07101d44081d16206001c5c1c0e05041403900c841103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 643702679 1250 643701429 643701431
    0xf0f05060607030e0d030302251401060602060c1602120307030f0e030a0f140109120e06030c18030a082a0303070206040b2e030201020d140a141209070303080604 71
    0x86480d070740100091131005440b031007420207201103000c0c5842039040d07461080ca5001d02400d00c2405681c8287d403403c50751000c95003448100652441c07101c040c000da104440300c1d50010030013500d4220081002d070b000601e40485903907e42c02e480d00546e9900b10404244000719010350b0781d441c0b5505004040e01c41640340c1401b071001c18181c41d022914001400d8586e10741120520307406940e645004100c8038414400360400790700706101d040c10b20504204407030f200c044030380b2000844031030b001c1480040d004c21188002448000c2c8101420a4101405500390000080c10303103850300d141c3d6450f1043c580050441c11242c2c0c00384c4a0303590104101c46511035503400243c000314158646100c0013075442c0c800500080241e0103040c081001c2c80c030001040e110718108241200045c82308800c424a21711002e01c0280d005110f40c41c110f49030540900c8000307108007804058103250114542091b0707040740b011440c40c1e607107050402c00d4040d1281030000c400c1c002c075408005020070300d00d1410003d0180f10003074500c5200d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 643703929 1250 643702679 643702687
    0x7121a010b090405070905180711070f1205030f0a030506030610080c04200c01021305010903120c05120309030915030907030b060f0a08061602010606050a051605010f0f050606 77
    0x22202070010b031400310004071408210350750303030800880b0810305a91000da007048200300d0280b922075000444900c42c0300c156032100680000c940e0101e581301101c6c421001c1c82a0000c40510070f103035900640c40c000c01e00400489161416801004c54107910410110002a03900c80600c00c0d140340c00e000c02e0383c000300c4402075058158100301002d5240d00740440060b00c11381d9120480c030092850380822004070750180315a26203d2071181c801078043d500146003030103040078501002c0303110744c0240004000c1d01d030807a80910072002c454000b17446142101ca01652244500340c048441c5030040030017140701d003000102840c0c41712902030900642503442c1c5070900310541c1c1842000510a0001000c0d8101ca4100f001185180c881c0c40100349041080c10b074598001c6007a400c081b6000c900003e038240200d555121f004240e0340404c0c1e0482c2202c40c503005000000d04100000c1c001d0350300c90009082c240034204c41c1c9883c10740309680c0d001d085840300b8111b5450a52200101e101c0308515109240e031118090f5000c5143c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 643705035 1106 643703929 643703939
    0x90204090c1401270b0a0203040f1502010f090b130602041503051609030f060209130f24050d0305030c160f1106070b150409020307121a01 61
    0x305145010722503400218402c6560300c03103e4105807607074042c00d100170355011303500c04841041148000d00c40440c54000201107035000305071149000780b44415010010703007503e01030012008014513041c0000b020079009003405074000002c070502a41c26005180c12402400755400c40307010342000108981c80c10f03416a000c2da0083c01c40580401506010700c008444807842c80c003000307044100c01c002d00000103030141c01030980000003c007040e880d910000e10310000c42d1300c1d4900800000d0b468801408100c802c2140e00703a00e01e031f08188103101e81801c1801150034050010802403c00c90000300003582d8142050030740d0200c1445110201017410309003003080314002d00c40c0c0305036800315242520321582e00d8114115940386500451300c4d18cc1d5602d100740b140800312280440ba41040d22113103000d00595042c04030308094030103128032a10190007803c1117000880c00c03c0c6000514600f503401446 = true := by decide +kernel

theorem cover : BRFrame.Cov 643525179 643705035 := by
  have h0 := BRFrame.cov_init 643525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 643525179 ≤ n) (h2 : n < 643705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
