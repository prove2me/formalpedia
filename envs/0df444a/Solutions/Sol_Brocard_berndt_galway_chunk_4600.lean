-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4600
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:08:30.663998+00:00
-- url     : https://prove2.me/submissions/96cf9844-349f-4e72-a531-c811304eed15

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 827158273 ≤ n < 827338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 827159523 1250 827158273 827158291
    0xa05010e040f150e030a0306030501050c090a050f010201060b180f010302070809100e04060e010e090a050601180204240f0f020c0609030f01020f0a18060e01051303080f12 75
    0x105052036114003801402c5a0000f070111120026011141c040990000019000090940b61107890310803000f07003d404a4030054070550b0804004c21890802e0900712891214002e1171400e8491901090180394040c000d011410740d541c600000500d08035210013004451814215a004044010100894800e0070700c80316040500c140009400283c0c01401c0b030b00f0020b0708580728182c00a11010072504251802c03e01030700203003020342c005011960f101260f4140e0b43e0a000c0500c00c0c0e41c1b4400340c02d96071040b45c84050326642c00000104540a0304402e0080080e400d000b0251801d500c5030350214a19000954a461046452070701c4040c1c2e0303034001c0d05110038183c1407901160040b02104000c0da1850090000c1d486410001400041c2c2c0c1d030200003004c3d9030b000c000001d54a840104c0e4500c15582c101c2e244d00c2c004542c03509a0440fa039001d0350b1003002542d455444540c0350440c801d00445150b00520b040d1403142c3c0318041c001c404130301c1d000040c01440c141c03440b40c1651090700c0214010500300143c66044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 827160773 1250 827159523 827159549
    0x110328090e07051803010b10091a0a0503011e0909110907080c041502031b011506111c050c0f211602120a0c180c1e05090f0411030a0501 60
    0xd241c0c050100c454008804403131601ea00302010000b4018041450700726444400c81da030440352607811a152100f15040f01107401300c44a900710118100c0e05c60006d00500041040006000450f0420404001c4c002102001d41c03001c1d48a0a90300206c455a100c01e0b60038040c11018030415180c803103086c5510100e28074104241b03007484854080e0b02c0c012402007100d01010b98400d078085134801c000356a03400c121000070b030304181000307500302b4000c3c080c80300c601ca240703990584041041e90045a081002040203001064103840b80381000c011070359080401c900f0450100405ca203980d0040042120400d040409000c50141a886900d85501100c01c90342e140b680900c03010321070030521030000b8001a0107803501c0d198001c50000a504003c02014010316030350440030045640804000803080c1c400f0400d40030030040760040400d0b991780400d201c2d031320440801420941312561181000d01140c0c840604403070030412466000909544103106c2e4400b00d00008000c11114055a014160040c10100c12900d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 827162023 1250 827160773 827160781
    0x21b030a02210a060f0213060c0b01121a0411041b1d18070302030403030c030b031c030e0f01051b07080a18030602030906041101090510110328090e 65
    0xa40b091000d402c2600001d20601d40040300c002060040034000c03680004100031004400172000001d400c602c03140791070085004404030b403c070301440320302e090990807442e104003030b030710300081c00e04403400b01c480032140c0c006a00c409115044040c04102d00491040b20303402580030138801800115051080120140c41ca0300d00c2c2083c4c10b03a0404800624000041c0c451545440c01c240491280e40840702d54031000c6007510104003c00d54564051402284203907001e004040c0b0701030049007926194040340d641604540f0075440307001000f0306514800c2c2183d00300814240741c1101c6581c01c0420024001a080c3d454008110f4101c0e2610305141d0105001c0d40c509040034200c0d00c03040d0040c05110b0044007801015501c5d80400c4108124510056602550039980c9242c45240c3e40c0d02d82c10b0603201107800e10561032410314550f0040f01c405042c0c0300c001e485807a406802031001c1350402c0f0300c0065010380340001c022941c1c05078407510720180003031500c0300182070700c903281400100101c42c2c0c2c0d0b020401c2c00040308180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 827163273 1250 827162023 827162029
    0x5010903060b060c0d11010b0108010f1401021c0207031403040f05010f0e06070f03110601080303131509050a150b0303030c0c0102121005030f010b0607060525021b030a02 75
    0x90680e6040100021140c0302a00481c0851040706402c000d1881000e807080a141d500008110b82100c10000030b01003a00780000540344000c003806114010300020405020000c542034581586420500c1111008800394402c40c00b20802144400c00582048030103000703000c440c00c981d01041000030000c40c0760510f4603805684c00e000030b0180c40d0401080070750400c502880303001c1140007024010407450740d03800c40b0300d072000d4602e04030300d400c030080340361015682010f00000c600706040301c810f00085e61850362803e0700100d0840412000b11400600c2d0270840c0014021449103031620742c4140020b20040310b140c2031480c004020a880e0342c40d000c0c03e220071444e240d10701105890300701c8404954607858000104016019000351b0ba465404003003140100f00b501801d000961040360400d405680e07109250382038443c00e0310300356800c06810500810020000a100303900c0b05138041c210091010040c9000254410210b010b5218032006034070260402d0030003254140e840841481c220000c008003001d681c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 827164523 1250 827163273 827163287
    0xb090c011706091f0b09100e010206040320031314060a02070620060708100b130e1b030c070303051018050c1603020106180c1407060209040903030b04150501 69
    0xe1a01900c3c2c4403021131180c1c522060180b03941502c000c43c40c0c0c505600c400c046402500011100c510825810700711088490040008625000040c1e010300700030355480d181a607804840c1213510360132404501410182c1c240520146c4181c004014078046500d00c0d041c00c0452140910001502c288000c0024408898000076001c04680c81e82c1021405c07030044411400801103403030350007009030003248200110f05500036a060320407001241c41044c095254903d01c9401c1c002c0184d004810031000c541070100c01880413081d030744900025403026800741c50605e16480d50b0004c1e5003101c81c007040400c80390201900340c081d85030322014407180103100e186481c6c90410243c21081d0750320b140a5860300480c55040916045071705850000202c508005118503000b03000709800c0c400c0a030f24034009400c00581140c00c0c054032400e003440707980f08103240344030406208065118100459a041e42081080101c0d11140118202613000c0d807400940c54503208180001d6039900228609110031100044c0300d180c1e0420b803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 827165773 1250 827164523 827164531
    0x150b09030601140d06060602061023010c14030a02070e130209040b070e041a090c0f030403050d09021305180f0316240c14090625020d0b090c0117 64
    0x10445101242000219800311120710005d0900d41c2040c102041180e0000b84440c0100c448080d51082c0580c0d0384150100200d04021110b10491010102c140e50341c401d04583e18010300580c0035112065000004c18650b81c8080e01400150b08424010401c03010030302d008036441030007000b0a140c1c0061030ba0000b150044005d000074080703050307100403c8910b4403502544541003c007410410007841c81ca5991a0030140404000c0d104010703100c001094502d07058140c0e040f032005d5002090542d00c540c0e505503030f56080071040058884da18044100503956a04005040d50a04440058141003501da242080f01043c0c1c50142107510821041d40c1c0c10900000f1220f4940c400c000c4a2110501c038681b10940803003040c17100e0000060b1600b4554420541e90004005540e84c2c1c81c1c1810016a19074000100e02480d00701a034400028021072020010080a0b1500701c0b03140503010410f13140d203600080e00c01d145907400391080700c1e040c0c041044440c8200b050810720b04090070503040754443d001c907048110304014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 827167023 1250 827165773 827165789
    0x141b030307021320040938120709050a0b030f2a031f0b090403050306220c020d0306060516080a0c1709030c06030f150310060603150b09030601 63
    0x2001c03203203618003154041c0c0d0100c00080b409100b99080c030715244107941c005c0e0003111141031611400510700e102ea4040c02c4941003400c400c21032045025030000c080480440c2c4190341041040826034900030003803007c2d2000d802034200c00a03150504040c42c4040320300d039150a41c0a030740700051032419414009a40c0d91345e00d0181c6208500c203433205c80380f490000e4000742410b41600c0b441020341c450508000c0d00941c0e044480d64104589034642040040d19481a02c0150126500b0008545203007445540354419440710000c0089503150b003041c1500b140c80c515400001600105510b0180540c94040c2000070503039032600714201040c04885008124607410018580d4100245100c0031a02822070604040e401046544c9070b00c1c2d850110302115845020406c0c072030300402943c814986011410740c1c4c001c1084218101207035541030343d56012a2644291240c0c0740c410544000c07a140441d01030b002c0a013070140c1d00400c10700d010b90079034041048160401e0361098814070002d074194030f00123100c41c115280d078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 827168273 1250 827167023 827167039
    0x3020a1109070e09041b1d09030901050f0705240a06080102040f060c1703011d070207030308130204141801140112030503100b04030602090906030d1d060c0a141b03030702 75
    0x3840e115840758a1280c03011480140e25200180b11000001f21010140c01c0f420340560340d42d500e000480d128802d0440c8039011070740500c02c242038604800e018143c41c2c3d2042e030490f94441007050f0b00350003c11450710442c4110524070204a0001118040c02d0002d040c044000d44c2024201403034000310031524041c0c00704200280c00b00c007061203514120b611301d1500742540640d50b940c44480c510040e4404847c03d1084940e00d5012031100b41c40011030720126a055900c03040a0344801c500b2401c56403a01e40180d9015442d120000c00009403c0000c82c002e10001d5445468150307640e0a031400e488841410307845e1001c60700010049198501d105081d0180c0c5803400b00d58076651072100c44041d81c90741e0010400b113100400c1c04000c0025035802810181000c8414066580d5090101566883c61802c1d80d0005000c28500c50b208400001d24481d40d2540100b2290500c42c011006502d844032201c025a01c07101e0403412603030390f08414081c03002030071440944140143d01c0240402d84e01d2041c0f020090240c0e2203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 827169523 1250 827168273 827168281
    0xf0103032021040902040f0f0b0a090303030b06120705130602010519020a12050405011a0d02150309030c010509012a05041809140a11040b0d0b0c09060703020a1109070e09 75
    0x4003004440144c141c0318030440d112900c0340d10b0f00202c8085401004070205081c5404101d800600060780c440c84c0c916a514410141075940460191000050b2180c00050a00031028100d00505c1000d2082c00243d072000e403181e0510302c85028000d595401324045da458082407105e40d6041c5201e250f10a9801c08000d03070b0f0307006460340480e11243c01e078414010700da1070082408108841900021038200c030082500c01c10081801c10844140e502900c001d47c4954580e00c501010240c5101440d80305403172405681c1898101607800b0b0035204100c03500c8545075903036946d035040081119111082c2500340a020300b03481d07900303442c09080c40c441c80c01480750950080e41101e0002d1155000948601d900054a252040c10118150b0b40c40300c1c0750700c08450128503800821340c00d044c14030603601142001810442c643e40c0a4a440e031403404047c0c01c0245001e030070040c901c107603150b810003407051038440c1c1e00500054066081c080b0f580110000010f01c10707406002840005513103c0c4800000001c00c4a00d0120394031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 827170773 1250 827169523 827169583
    0x6051506030f090c0d0f05150601020613020102011e06030b010e011a03100b1209070626040204093c0b0403030c1110020a03050105030d050a050f0702090f01030320 72
    0x11294001c91751100f0450340400400200c0b12225045512078401c95110072101c2070341d2007101c2d404031400d50045c1c5c0200d0014240a802c0c2c41261504c6006000018600401048004500c0d1018000304c642a8a81c98204100b0100c4400c00e4011701d01c0301c44010031035042201141c1444c10f102c40d00d03000e0400c0440429003400c00c038040b00340208001d046256660a18904200d0b12050885a1800c1405442c00000d090303070060040250a24225032005511841811a88100400070300160b0b00325988030441b500164401c46005920b50001590f881001e10704003001b803102c00080d880c0e101d002084136400700010092400c464016038035042c0410400c5c0000707800c4858503182c4c20442298440c0403020900b00ca03440c2d000340a56040c6590a10080e03032a5018180c1d038000c250418400140d0030060111628480c1018000003165a008540741c40101d40020f1034025058485102221020b00100f00309504008130403e10300d0084040c0e4200c159480889403118910b000c00800c0305219080c65807802 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 827172023 1250 827170773 827170783
    0x40b12150901091a03070e01060f030204081e10180b0c07150b013c1107081f1a010305130f11090903070c06030b0105040e04060906051506030f09 64
    0x40260500d01c1d190303550403090015124000303558800590f2843c6110355420003056100907124024182c004503407130800102ca0b48568924000101a8248008942c00000303002110550320b003881c0f00c81004880c440441e0a0023000081e0780c0d846407a15034810300c4001440030240b8000e401c401d036455150340c0e1202044040c4142d1800501400d0501085d20f811041944031100d82042a0f03114980f500d01e0100b45080660350155070400410b0218400f51000803018424407400c06a01e0200c803d200080079081c50a42c0d2500400429017003041c0c00100c2d4103503540d1507500c00c072200400f800382c1b120b03c014070590f050010910504154646002074002c02100005403440e0b0f40c041c21003403950000d4141180c5280c0b001c14075034441c07080d0341c01203089010000180c42007960440d2122180c286400000c1d001000c989041c141400004e0000061000c4000509131042c0e00070540800c6000841c070303080341282c1c0b004250b620990708111640546813542c40c2a2984004200c005c403000b03445201c1c01314501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 827173273 1250 827172023 827172061
    0x3090201120c090e07030b180a060f030807031b02100e03191406010806220512030406020c0705011103180a03170c010c031413170c0a1502040b12 64
    0x2290a1095110000d648200403070f08442820b00b004404e80c903281c000f102942c07130111429a2189907040c241e01100e100c042e4035a004401000001981a525004460501882d0340161080b44000c84d11009050300004080c49603402c40e80d0b2441710b40714580c00070382d1170b0924069203030803c0150f50a401041d02d0030801d4900102d00f200d405594031641e40b40108440351181106401c038000c10000154121001607000d0241d0505240c550b03080c0b01005558103101c1c00500c060310a44200b980c08210200c01d100218080da000f40e00150352010751f121024502500d0743c1c401810440c2490000241c8031000c400d8884140c1c1d180b100f08204c411020000300d0303c0d94550009452010b10112003501d42141000074030340389141c0002400030301c0aa98003a0101c6103000d540c540840010000519151440300c6500b07010fa04c682c0d00203004602410034400c03550054070b26014158001c0040c4414005180c003888031802240d142585440e042602d00d041318054001540400740054022600c0944c403014240c1b45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 827174523 1250 827173273 827173307
    0x90a0c031d010f0b040c0503010b1e03242d0604090c11250608061207090515060705070e1e070203090a1d0103030e04150305150f0702070603090201 65
    0x654a81000c0c80341c024401203250701d0440e0b1504842d130300039091600800000b03145940301c0904507131801d00384000742d03404001040b4580320600700d241c81107102100130f1070040e400b0f00c0083c560490324000c0d2040458078110602d220714560b02c500c4c03a0501203003070f0103008200c0260240070500d4248010890500854020140060400d20b40800955005200c5100300000300102c2c1c08841415418030101080d150b42e240f9000d040c0d50081c408540285013264000c400504455a4100090b522904003540c58210407007a544403403c2c070001e2010b0a074001c000480403500700e454007045540385580c85019100308030701c03100102c0002e01c1c120410340c041542420070340e4103101d02d8a05500001c0d241e83c0600030030752144644404c0490b000c0c4144448a03602178134044420882d034215201601e0500700c0140c019032041d00d074076115221024280041c801148180020070651f861602844140d03580102600d00e1030460f4400c000300743d43d000441608607045810001090540c6000403100113a5190007140d0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 827175773 1250 827174523 827174561
    0x20130806090102030a050f010b0d2324040e1507091e05150c0312061302120103060e0a0b0403050703020114011502150601020a02012a0305070c08010506090a0c03 71
    0x520030700c064004611440707844608000c0c940e904200e90351403200c00c2c015500341034800e0007041c5010ac090340c8032001c80540b80144c0300e40c118205801681e820f108032003009014001d0b0a240b101c801d0b801407900fa0820040b40c0510140a52110480d52200c0c028070440000b5000c00101d400140106a204094500c8405c15402c04041c0c007a4909000e04500c00e00d40141c011418200e05001c450303080e100d200c00100040e40c42d000307080b03000b0344200402501096000041c2c075841c50152074184000c04007400c5c034901007a080c0d85581020421544160300ea041c0e950410401c4100003002e16000343e0f4482d515003015600c031903941c10101d004115032041100317000301101c0080340c0c546810310340080e10344141d402c450131484402900110001e09030ba205002d030788080c01b00ca0042d130061444400e005015811714003528148201c1120030040901c040d0b010840004a11043c0301c1c00003130101c050b1803c5c170002d000700e081c4440841c034a02c1c40285088440e999445c4415501480303900200500201208890 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 827177023 1250 827175773 827175781
    0x60f142b0902150901140d1d0f060619090533090c040b0301030f050a060f090b06030a0b01050103180605070302090a1703090f030109120552050601060e1320130806 72
    0x1650300d8100f49181081481a92b002a9040c9030002920070440c1d145000600e0403031074440e104001c0c0801805005050f86103108815558091342882c5100700605042d10740300c80020001e200340c0d040e01a00303443c080b400411051041034498003c80c4d045952000654840300d00d9420b180c0d04005031140003d05050621000c030342205ca0385c3d0483c0d003960b4000c1d510324849450300010150717900c00ad07403402003004100c140100308a6000c1d87c0911000350100000350181e0040340c0d20802101c00441d1a000441ea010400c05030740d090940c3c2240140c140d80c071038100400112800c1903640d0003818043c3e88070780f6110785080c14940b000e4002d54007207540000c4181d0903c24402e00035000307401c55039407003541001102c900410700403104403d1000d84121000349480d940c4075505542004c4203403002d19000c910080322040040e00410905000301500e42d241c602e546500000c00c080070000c401d100001a0a01c0300484041060b25030354002c81218401c5242d5401e215020500c0980300b660007a00d4074007a403030400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 827178273 1250 827177023 827177081
    0x201050f1602100804020d1707020406090f0608030a020a080d230405010c02010c0c0f0807050d051c0b030c01030b030708032101060f142b0902150901140d 68
    0xc0030078284210740b201100014000116209442150060344c4450b505050340c001c00d01c0d0708003803204800c003081194a4003016401103030940741a41c1c07020000666400010031004468403540700a0124100174600c0c01070811802507407904200000703083c5110000d02d5540040c2e01d40e0000401c0da080030000921032041e4100701a052074120303400c1d112542007001500340b0304d1040c412480c807513210381c80e0340020082c15181d8131200110f03c00b04a6071030408101100100300c04004000c0214400c0ea00c4560b1a0758180c8940040028070880940c11402c1c544040050340d008504905000c10a01c0c00142003400140064034001041c3d01030204c43c040011003540039182ea48166174041103520500c1030a0b40c0c0d03804120390a454581c85d40c1b001880d000820148540074500515000c03440c160075a103084120b00c2d14a006800440211000c25680d15149086050101401602000030641c2d54101000040080c0c14000a4030842c0c0c00300e007001642c41c41e0103c1660054820f82c0307044000703441154225402c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 827179523 1250 827178273 827178307
    0x7030515120f06070503091b04110403050a050d0f14030619080a0218090601050114040503010617011508030f07030207081005061305130807050109021207060e041a010c0201050f 78
    0x680c454000c3c0800280c459014600b100d00403408203000300340003805102888070b02904941110f6110744c9039846644030700d2552011340091070007040500403800d41841d250345408021500702c01445a4000807145d03141d0032860b503c140c01105558555030ba41ea01d00004d071065a00143d0801e00211084040750260001801800891081d030f0010304021030910703e0380314100200c40d01001070303001c00014481544140c01ca02c80000310700300d005051a894100203402e41701e80da000b050403070482984019102c01c09026203038203843e08401c4116110308096500ea160b01c24003900c4480740301700040758010980b003088010000d0000c1c2c4c0070b403402c40d00c0a5144801a10702620503e03c182c40c240b40c442858442c40c461540114922210301c0182040c170b680300c65a41d0031840050311a9581d4404640143e21042c400404610f50580541160ba060040140408100340746d49030185180070084a16804106003030000c0705001d007800f000140942c03004841a10440751450b404c00030110b0029030448040f88 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 827180773 1250 827179523 827179543
    0x30512011403010b0402040b0a0302220623120103020f0a03170a03200406120b060c010b010801080c01050f031b0a0f1b0807060e0f0d02030306030615090703051512 72
    0x4c0c0100350040c020030007680528040e50000e4a010881c030840540a54000d0424a24510761204052a9502c030841c0c0d00c0c010b5407001c408141c1c0c859040f10034000f16211100586010240e890510059510b90044107005010003406007119107210301e01da03560810040000c41d800150401100c0403581240700b603410400d07880c00130030706180c4034078819071f039424000e521156046480c904186c036040d0105c4170506158001590a96142c1e449205038844400a241040342c5c1c2d4000b050140b1403000040c07811005a2241d25160441452018540c1e404030440300f604101e8011039407a62504001d04c42180070040044000c000e00281c040185070700142c0204c107030121915000c928100d8088405014040c034000140100e00401c0a13030b001400342d9000406205d04a021a4207210604088501d440031400194015034004000c01075203103410092654403801440d038080100f90071074003141c0c07180d00283c9664140b6843c0d80000b03840c1e28215003103a035800310003095001c1c0240002003444e01e0ba58455 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 827182023 1250 827180773 827180779
    0xd080f13080c060c061302010c12030903110f0a11060903010c020f07090b13020705011e06050906060c030306091e0c03090f010c050414030c0d05160816060c0305120114 74
    0x1041c00b050f01d08001903424000030500034000580d14091552004450594228107101c01070b142c0754041500016002a80015500c2c0000c0c0146203040180800808049001866002000e402c4040c0404111541c807954000c160301416240e460000d80d15024111449400d0340c64203602c01c2d1559400104640700c9603482c015510207079110300f01c010507900c101c01e00c1031300040f003220a4041503500780c0c01015200d0041d800010302c180341d0004140000c2c0c24082c6899082c4c2c03580310500c01450070301c1080340c003c1d10480e05103150002400c021600c03400300606c800e21070b000640000d5184400341e9241c446400c40e40c0301800c280e182c500407006c03140c0c100b60b9846c200c51007100303140586403105105405800e91117440b00c40c1018504110302198103483c00c00107405000b0503d000c0c0c0952918452810302a119001801e00c4c103413a500740c0c2074205c0007540140000e5120360007800e106485001a03800355801840e00350119001d6040c10b4400c3c0c411a4620303185030204400001c0d20210b004101d980d000411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 827183273 1250 827182023 827182033
    0x90816170d02190905010f050d0e011d12120c030402130204060c0b13030e0603100801050a020403350a03110c0f0d091d090a140304030308070311090d080f1308 70
    0x300d0f42c216542155030040d2400703d2002080d00c050b0034040d06c06000f440d80c0444001c00c2500e40e111185003550380450b00c440c00340c004200c1c1807a0551051180c2c5800c00850b802c0070b414042101351010f80e40130042c0c00901c04034800800b1a0a43d107681c0c82480002034083c405669440d075580300181488540d081c1602d9207404000800c1501c0300340301d42e09902c6601507541030b484a13120020002550700c0981075135854414044001a81c1c40c0078003a507803240a508000603225407841c14030320740c0c0900b070f01e040c641c400d092100e0161024182402e45541c80018048860320b45c0350428081d0001c6c084103600245119000c103608000000014990685d0340e980d00c156400040381d0001565000c2a078003c44907010740c0343d60800d580750314003a28103a00c048094111254070415840f001c81d1441e0001080141d038100003410b000f8190000a0b50341c100502e0314041080164003800e10744907000d83c2c8410340c0704042400e103032424484100c081e074844111500c06a540c1304504113186852082e1407103003550038042c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 827184523 1250 827183273 827183317
    0x604060e0a050901030f032a05030d050f0c041502010908041e050406081218090f01330302030a06050604080c090603010c20150403030203011701090816170d02 70
    0x72400d014100d0b54404002c00c0050f02035542504c0c85450985500b001c0b40000421808000d2308440946a40303015074040d60f0382d804060305d01000c0d5400180080000b00c22441807003c01000c61342150100d0741c200c4001c0d244004440c4007240503001d0000b000e42824404180807a92462a408030703400d411403807645101655071380c1c00340030a484043c45481495000018010503959226009011180045020136940942c80c0000780d118201540c00704011804480107000103018818241c007081c05514001c130f14090490485407185040c00040e108154007c408240307603032450381001c009080002c000c0b5442e161a429450b0f51809914245031003164107001040e06420184a5160300e402c075580c0d0000d105408415000541c01c0c0300e40141c106100701100c004241c030b101c0b03001502840c031031390700941d80e5403412036007000d03071900113219600326454005800000b54010003214a2050200040950341459003041e504400755050348140143c0000f0f003420300345242c1c0d80100824444505000000700b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 827185773 1250 827184523 827184529
    0x110406170108100b0d050d0c2a2309070f02100902090a0b010912080a030606020f0a1e0503040e01030b07180b03061c030e030609011509020d0b0604060e0a05 69
    0x7803045042d581c1040740b0141945140c0c2d001080c8841001c1e00642009400b5640c142c540030b040600c80c0c0c00120300d03480e00d0b0100700e951480711800003100a0114000540f90f610b1100d10f800034400d801ea04213010504041d010400102846030301e000414034243d17803410303031806410b090790f1445802c0140180d40c90013490aa541c0308400e145600940042032598690200c0c9008000c03800ca02c5052010250300040c02c00f8090f0083c0b002d0a1140160380c1e100c04130420041c0a4403980d40046095401c4009080300809000503244001c0c0d8110400301c4002e8500402281080c040c044058028080000e012840101c60000c440c100c0303114445903c855034030280d0849005200c45050b90001d88441c1081203042a500c0242d40c00c640c0003841c03141d51100c507501c2c000b80142d20301030842c0407442d000e4804455160a22940e80d000d500d03440203224110100d0f01200403860140030f08080a0740c040307811003505c0034070303401030030f55032030103801070355201d0715840d016051580c0c4501192041c0c214050210f1b141c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 827187023 1250 827185773 827185817
    0x612030e090a1a150f0a0909050c040302130903091802130603020901021203060f0409050c030c0609181f06080108010605010f05040509070e031f180302060412090801110406 76
    0x141958501e88000d83d10030080044201c6400c9828624100c10b100d001d20401d0920000c1c96829226212204518039096100007520305c01403001c00c2041007030000f0070250b20f5400741640b000249a4000a0190181c901138629041c0364001d86908408a0002c6004a0f00c1d5401001d448810160900e10203940382400c43c10391090580c007a005030401302e4401005480381d806143c000c80c00504450341e603071824010030304a900114041c0c80b9540085541003c0b030901b400040c035600d000341c5803035140c6002440400d1642d4840c1f10045900c1a4003000101220520f84c00c00702c0c2c041520080d10340c2d0766070703c1000070002c40c42802032103c0355281c400b002507150302802000e903164000c4d03203846042038640020004107800c028403c03030520034400e8080040780e4062108101034440b0960055103104600c1540c0b0490b01c2203d042c503040360b00d422034840801d8000800c00e82c03003036001c6240b90341d81780700c440111028000b5a108600c55801c1602c00d075507000f4100090000d075100742d50307601d24840c1c03184480031401d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 827188273 1250 827187023 827187041
    0x7150e030705060720030a080711180115230a021506132a05031905011214100903020c010806010203070b0601050310050910051f020c01120612030e090a 67
    0x4648100034a1000428102000d43c1780340c001081c0f8031280004601190606601d884211000784001030003108000d5030041c00740c0c080c601910820010350400201c0751220038107000b41c1204103101d62012815034810b0324030b00079207100e44208a0344046002c0c1440c2d07540e00640100710240c021b070220f140440e080000024440c80c00108034000c0040c488541e41d0060941c010060100300303881c0603644501140040d8081700120356503ca560b207241060a0b281051800c8141210850502c03004003e640b200c801961a030b181c100c1c10518100094032601ca16041143c4103004402c0d0616130420145a00031800c21800300303007a02e41000503036409004a07168480d9500090034a020000880c005511031009144c0c06640503403d044d10940320f200042c000c0340200c580c1c4102c0c0c441c8207418495030030305181d407900d0059900d1526450440c08a0081e40340c005800225041044030a088102d040141e00503500400814802e00705c00005824010120718500400c1d90096200c10701041c48545548610251 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 827189523 1250 827188273 827188279
    0xd14040503150907051c02010c02014803050d0f06051c030f0309080703211e060503070308030c09180411030c010905150d0e0609071802031605030405070807150e030705 74
    0x1186c1940c0151000e40e0108810703410412030440c4800104015aa001029201c0c01d05000301029071448104284002e2411b0f51a10607075100c0c4440040d13080001e45561400c026404220b003007116410350020040d0758030036030b401900c003c0700c2e00c1218604180606054000c0d0780d0300c1d07078030f08190000340e0580320178400c0200781180070081000401d208000358900d07000c0004865a20003a075100480550f407980c02c1c103c4030000c140e03c10090303001ca103128040090800381c0140c0003545ca19203600d411400000c000c0000035100040d8083e00e55580710000c08415080070307560000d03003000d041401d4182c000d0291103001c0d10038089080c07007a40c09213640000b203030703c01060700d208080c2141c000c0d400d9400000d41440220f0300d42c01e400d48484428446148074400040007061881d25200580c0c4011801540310512940304200307010340e651000b014560440210b0500c01e590307440798a8458500040d9602440080c040d050011818030b0070045540580001a0350b42c0d07150b145184205030b01c2d91624800c540d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 827190773 1250 827189523 827189569
    0x6050f0304080904060b030a0b1f020a080c0a080a091401030b0a06112b12050903030114030c0d0605071404081908040e01060903021e01020d1404050315090705 70
    0x31100b000500d0034250242001c950696a400202c1460f00103441d807600f4152500300c1c401c1e69060454801c0011980b9032203154130003590301d0001c2e460318000c45010300700c9200024024800380b000c0100c0f001456124a2462390755940c004010154151400b0700c403241c50300405e079192998440e00801848140091140c150140f5103001075911480328521000d9a00800c01081050034050b466410804d1260040c00e4030300c24608030041c4107012541c5500c01c024600001c0c000b50700da00005480c15039420401d481c42118115000074680403641c0c988a40c46000540c030b6a0801a0030f403c4603018804980ba1041c0445540c413690b03145008034010311200b0b90118025903402110411100c81090240d44501c3c0741035281c2080c802002d000f41c01c440e0119802d00f9040046044c503140d03400c501001c107096010f0000d81c402c0001e4544020383c0811003080080020100030700c0c030480c21140200700c0141250030f40d40c03035844031404854048850100c81d0041c003900044500f00315441c01e651800c100d020300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 827192023 1250 827190773 827190781
    0x6020f07150c1509021212070609020114270d030c020402030402010c0209160206130b040b040303150e06040e03130915030f0302010b031c02030406030f02090d0c08010606050f03 78
    0x10a044080304070001008880109100410300903090141d4403002c2c1280428003001d81d00511522041c0024264079582c000c0c008808407070143c00076115410740c0310a0104d480c10302400100c03040d907100002220f00e881c0018545120500c0d40b81c0d42c50041c488048140c140391107180421615625560b000b50200340550b00c0341006240ca50b0046511510504181c011501650049004200700311000f1846500921074000e2a0307404002c100d6105450b10741c0001c0310201c994440c400b100028000070818000d1201003000c05010360032400c00e400704207a850107115603540228900c200190f070760b503004600d0109100301e480000b100329800c40034100c0a40d070495152401e2280288120600062150311609000c00050310402c0003e5001c0d000354000b1407000342c11020075042c0480e8249421a0a5011a4a000140c0c01001b5101240d885050018100c0e85100701c11000c1e2283c1c1c200389034060346021a220801142d00859001d42d18844000c00100b0345800701542c2504c6594540c119445041c4002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 827193273 1250 827192023 827192039
    0x2010207020a27051807030c06030525052a070f0f0b03070f02100507030f0515010912020f030613050615060d1d01050a0b15030c0711030a0f0605010e0106020f07 71
    0x121703003003810382000d944031100144803d0305080490f0021924151428002c0010b02d505000300b83c6c05c010b940b1540391841c4028503281d17100e101403084031414490080b41e90300030010303481083302100c000310f80d404150442200210f5190b0085001d400c00000801c0f01c08560034018a51900c251100c030681185942c51300c000039200080c00d00300795021885103000042d40d950035030060600500c0640ca000c43d00030051250041901d4009010030444100b80241c01400c0ea4440101c0342102c004002d80e01c002c800314000f003030700c002c0c0548290385c15214000902644c000b00ca41000e00c0103004a00ba1480ca403074201307009000214038204503030300c520280604084c0100030360104941c41c2000c035440d01c1100e2001c0c10582555000ca80c602c08041d600c25143e03205041190620b07020310303980304846203185400303030f074202c000d0007500310180a41c01e495840d41e42c80d840820260095980000f140e0411000a00e44240a00801d010f80000409013000000e1582c3c00080c0c1206003910690140c6586403c20001d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 827194523 1250 827193273 827193281
    0x10e01021804090c15020304360b0409060e1c020f120f0417060603190b040f02061e03102103080910020a05090a050a05010903150b06030702010207020a27 68
    0xf0603550ba0041c0400012002d584000801c2416400c1e0003444d1240d282c0304801c11824030141780c4100600c45039002c144045444510200103081c5034900145040c004808900105040c0b0300041085250254807e1602d00c00030b1600d0b001a0340700c3c40b12a0094820f0300498645480007000046a03108500444100b031500024003a2092a0a09181410350700c00b0f40b02801a041c0b074038094241c01034000d01c03042d402c040c40358a081c0c1070701e03400900c85411a40d035040303124500104064103040910304018215a19001129191064100a07103405401c06c03440111540c025550601d281d528042c001546180c0e011079055854140c5083d00070811315a1000d50b4821001010319055001d1504c800580d59030328806889018516a0380d1a11040c103030041c04001200c41c2c00a510640368882e0400041c2c1e0b02602c120300b581d501c403024082040c0c2c0c1004d0100540400c450b500e5110101108002400380d05502420308180211081040d0031b40c1d4030004095069007410007a910030742c121074118201c1e210b0300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 827195773 1250 827194523 827194541
    0x1170a060906151202030d03110d02030a02074b020f190618080c03070302100c02030304090515090408030a200d050414070b04030210020307150509010e01021804 71
    0x902040036550f5085010b0000d5142d04009000b0b00a80b168100394101001894090202400d080104203500b4803144458003030340c40090003032500000052a1250140c05440005038040d100720002540c40c0d044403800745a140c4070410102403c2e1803940320000c01e1188211400b0300c850601d40b4203445d5001d010180400400c2c1d61f4221002002c43c40400c41c003032070080000d0400341d446c0c00c0c810300c0c80e03e1034900485903a400500d0f254042500038110f41e8021840380c4c1201d904803a12002c00511400c16980c003005007101079458040414006a00c010540015114851566458161070405010002000000d49028220b02803c4c4000f81022041d90301c494100340d400b50f01140c40d4441c008048400340e00030004544580d8a500c140010045450113060082900001401040d800c1c0305800c03e2034040c074030010b03114100c2d21010928150013401140e044a42041c50202500d1160704240041d1006071507000c1d8941c6410103c982580f410710a882600700c10803a0384042d20440001c00c80940140c1e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 827197023 1250 827195773 827195783
    0x2607110607030c050703060b0f0414071107030b0108060a0b0102010c12020d0b0301020313290a020f0c16031403041202090c0c0a0c03060c05030903070b090111070809030601170a0609 80
    0x601c510f030206804009071801140b080d000802e800b8010000d2182d4184000312031030056082ca40700701881010807244c5a80300d0385a103407075460340c1e601e040301c589000c0042c0c2c00980080620800454010701c042841d621982001809200082c03008004a081b2a614001c0300c0010359450084000050250028101000c4000c004941e940c4002d0020b07007268403e0320189419001c1020a504101309010740c243d0080245088181c0700c400ca1079401d0951030010b003001c006560014001c600c0d00b445d201070b00c5c00265811b085070341c1c0d0040400c004080080601003942c15502106411090640010490b002d031040f9213007035140c01d01c5950034418464405046100d48540500c080e9094407000c1100913103050003110203118251440c100301088843c03502030a0b04100c0b0800400c14007000000840d070301c0b0340d40200c03180d480350b5407444040e00400111080c950f141600250503028401501c0c00381040b200e044054503250b9a0314540300c518401d556280798030303c2d0400c1d80d0360000b00e601513220521880c012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 827198273 1250 827197023 827197037
    0xf06090c150519020304080d09140904020616020607060608102a110a1b0e090601032003070f0603230601020d0c06140109060e07020c03032d0403260711060703 70
    0x240340e1f45003080f03400c3c0c4204000452400d0b08100141030240d610040c0c11041d00d0b180300608164020452901c550141562001860603090301192600e00407100402d802501c20844107459011040e00c0d000400c480d40d210a050610f07003a040032403c11840139120061925011840003c1016030701e551007982650400e00440d08803401050b20305c400c00381444500402c040400f0300300909008140e07800b6014030100c4e8400f00040c40083c6a070b400030344402c56030b140d0303440540741d12500203890060755070441120780c142040c00150303840d0103810805010101603004511840700743d8010101034021643c1c180168001181c1c801002c1c0501c08521580e80a010041501c040b40303003100d0000e180a03070040846035a520410401c5c1004038881035004001032010b042d00705440d0001941d0703401000380803030340342c00c420306040c2e0f030300754100800080041480082600c40e80e980c10b00314807040d19540d00c800031158080340b50480c0701c0d1581c110f0f080154000c1011452580200030b0114039005090304805110704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 827199523 1250 827198273 827198279
    0x333091909140c12010509030703050904091a090c010e030705010503100b03101a130302120f01090c1502070810020a2d14090f09130f06090c150519020304 68
    0xe224801c218000c0c103008010029000702440040008901380c3c01d40e5034940410301020f83d5001c012a080240c241c0380a41d04c0e4404c00f40040c0c010290b115000b04684414136068110b0b00480c884c8500c80c0320010255a4964011401950722407092a4a5681500301c0e400900581d8050000380d50880881c1c2c502d442d056407900d0400401d41c2c000d54003020321031031102041101b514003840d0000a81c02e2480c0f402c0c03c1506404400185803007a0000a200b2325a0000c840d4a0f10810130072207540c001064020300c44c403007082c28444800d03100d0307000306000e0941a95074552010b0000400404960103500200034911010718084020b402c4600300f403040100050803c0030280c06540c0c0001c0ca180c420100d41e00603025014058081d034441025021082010b01040007140e80d0100006007030307107081d00d50a4103540d6020f103a050000202800070020500200e0324410700219501041800e8403812507070720400e40f1540712419407040502c0e010b0000b00104600007071900c16105c3d0280ca600f0a0046908180d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 827200773 1250 827199523 827199533
    0x20303010510031d0c131802040c0e03010f0914030702180912030412030605030d120e0a0c0b030a0507050f0a2706030f06090213031e05030333091909 66
    0x1e1003400c0c13520141d0140803411070030304c4e010b18a440c88164260301044480c030301c004094a041e5081d107001e803040d51b86d004500304d2070303025141c1c191741550002d0080001e03141c07100614000706200c407803c0e9034282512685d000341d04400011114250380080c0765034403080446400800e1241c0c020300c10502030049803403003803642c0c408601950149105100d4410815140350000301140c80e50f83c0000c0c8258000101286099000801602d80108500c00800c2001c6084e19980c540f445899000f4991209020000784a0380b9160155014085070031040c4807648802800700d074180601c21280440b26420003035a02c40c45d0189074001c684220001030742420544035804207130403079601d600410201c0d03283e0184000b40c40701e5200d810301610f004201103080c0300c0040d1045001c40c0203404000c20a00050000502c0880d40303103c2d461090b68400708595603480c00e9550855456400d148180880c01103008604650104080300318001102404450065a03030741e506c0c00500200901d45009940c1e1041c101d40450 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 827202023 1250 827200773 827200811
    0x40807050304050d1a0f0f1b16080910090302181e040809041503050d0f0519020321190b010e04020c01050609100f050f0f19170c0102030301051003 65
    0x50180d01d00070b00c084045c2000c001500c400500c1e000072600c010301040307001c0321501200c03034001d862a000c90703400b40540301c103039900c600c0f50342000c040000b0034804860800100500800001d081941d80b4289114401001d503000740107400001d6000454058890000c02d4005a15501801d103031440c05440c1e6980c0c110712003400f0305450650f00c200300020018883d06150003548007150307151081080f268a591500354a94ad4001400020015282c82c580c0c000b610400a031500e41c2800441420300b00c4403010060b54070703440820718042c402075080031152031116900805100d0004200003101e81c1c0c0b1001014801450404801d905102c500d5003207902ca0313110303840902200d07040300000240900b071000c1007141c92035002300748083c4044502014001402e4441034031003120001d031130920021352a400001c07445041200c41e1900b0880613005148102c0724582100d00311074180380084940f034a910615070310b9074060924035015a0040004101c1c40c01c1c002d02036a030510b010705c0c00213006c400c860260b01000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 827203273 1250 827202023 827202049
    0xa0c0f06021c060b0403080906090a0e1008010515101103041206050f060306090a030c08070629100c020f120d020607020c060909070f0201090506010612061d04080705030405 76
    0x441c01c1e0800c0e0102481c2c80e200b1003000d030078800c040380c2c00c1031700d0b6940e5203041d4411401d002c1d000380c030040340f20101c81c0c90342a05130300503001445240c90300346404d06052504884611a6190660810010400c9283c40915603020b005020381610441504070030241e4004440681030b1445120030080003601192030411071070754030702c282400300b40c90504000b440d64800f805004680300342c20203030038020321610028407080348580c581040110303c081420200d03118081c000029043c0790420341004080200240d01114401809000c002000e03604002d100d082d80031500003002141083e08a071004d03240601182d40c20007402080344281d02c0100040e02c0c20848034503220000340e4400400d101c8600e230188040d0056940a641c15410440240006014414050246005d01005942c0c03503514a20030b400004c02c140d04042100c0c91540e443c00000c014040840c00b2184407840c000c00400c40d80303854403001c031100b0032481e901c900c2c43d12581c032045030b150701540302100c0610003000300089030b03202d0102c081d220b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 827204523 1250 827203273 827203297
    0x61407081e0c0d02070e0f06091909080c060f04020123130902190311030105010f0201152d150e012001060302090f090a1202070e090d090b0408030a0c0f0602 69
    0x3d0624400281c54054136800482c650b204060400001c0c60340707111907651141d002c54a100c6980c5801e4902d0200f1070052640c02090380c00d2890240500501100510381030b22403804640e40c99803280c2401c129a030056400900040ba800800803084400d4903001901c010120729a91030031610101365080b0181030f0740400c8030a5000f0034030171940c0d07421183c07051103060b2608051003403030790206a00f800f41c0700c140036140c10b009154408a051520035401681d4180780f4802d46403485440e1581d10180401d0407580a4008121007241d503000c4c0342e0207807100d0490b98607103100000406002030907560000065995410000070101c0740c0c1c0100500b10000c070403a02441c000080041c21401403004420b0001c154a032740c0b010010601c0781c1840001031820b40300350032028030500019121412030034070f03100e0740c40b049245180c002407081d500d40c00b14011340e8540d695224900c500390342d0900b0301100e015500c200c06854000740051027409010321000b245551040d04009881030307581c0c0d030345c408903040701c220541 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 827205773 1250 827204523 827204533
    0xd2a17061c140625080403050906131811030a0b010215190c0c052a0a09020405040c020f1c0212040b09133c060b070b01061407081e0c 59
    0x2812190a03c03034240c0115603000d00010203d80480c002c0d48140c40b4288480030080710600090915202c0c0041d10b40c41040100306507511071303d000031320700344500600512000e40307003200c80e403c1e100010740f042c441074066020b003050031680d652418000400000745000d0540c064440d181d03010300c8281c001280310b0110072072980d20710441d10b40300c03504a6100035058828031180f480e41001040d00020807005541407090110342207240d4508072039048030040801a000500044045501403580c1c000e80242c801c240c501f0000303d4100c100482c0c5e21050a40e9056080e0420b5207030340c190f011000d0040c004c038480d50040310406403001da86c0d42120b0748a0790200c004554049958102407400c100741c91407004d2038180030311851000c204c4c0320158030342219210415001c0944071500c4461140108a500d0700c0c042800c1004656a400d401d402d84d0041c10100d03040034604002003000ca0084004440c4120801000d9040c68120b944903460f5038007082805814056039211003000b0f6942000810f0b4010700400a40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 827207023 1250 827205773 827205803
    0xa051c050f0a0b040b0a061a0403050115030c030f0627120f0807050921071a0a02030702060306060705070b04050a141c080409020d2a17061c 62
    0x240c01c00159104003070803504626000c10214112510303d0f90459004510050641c8501451400501030395000001c5180342c4090781d401004a040944212130051000740502039041e00481442c010a010041108803025000c1c030201d4054800c1c0c40f0114802e040000e50000c1052001c0890711030303894220f10b41c141f07030f456030f00c10001b564220745591600c40c100031101d00d4200d40c02a0120400a04607800c20102003202c041c682d44560409011400c800801280303030344c2400d000e64540d180742c0070741c1c03054070800101d15405e004070004440a8044990186044c17000175400c0002d5640042d1003031f40c0c08507051120001003501031003d44018541c6ca07018507999482c000130f00640030859030210410800c403960015841e01e80c00030307900c2d0305810b00c8429000c4040c140340888242c095604a40c084903c0864405600d0070b190b803111b000d00d1800854800501580e10480742080721046a150000303020088401c0e1203076010301d1064000c81d0007015002d04002c002080408800d480c0310550320b250b03048c8100c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 827208273 1250 827207023 827207033
    0x1506030c06080411091b0304060c181d0709030b0901090210090e04171b01060503070f05010e0d05100216020a080d081f09020f0d050a0b0109050f0a051c 67
    0x140d00030200703070408410900e000e456010203000c540d2511030064804500061000b04d030707000342150018282c00e0711500c0c0d09180c18900b00038071804034410042001600240d0503114001031000850f408000f0400e9594250003800343d45407005403090b01449128000400020020042107120705221000010803800c0750041040d506030b107088039414804500800d1002c001410800340d40a070b004100500382d40c2c1d50044090a921415201c09400301140e00c00070a180019007040c030490b00f00301d04403141c031511109942011586441114040f0b0003854000d419410301d0b00d8804030443c092804d503a100500c6c03003180c1051364465240e41c0200000d41565400b1032410790805006091010000c090030f4004060240100201800c07621460400109480d05a6113203c80480642005001591284001303040a40e4a8001d40b40c0c2100050a103400199403105601c81c0781c001c100c2c165606104a440c01c014409404145002c5941040e103440000c58640c503119201100c040821070048880d61940c145 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 827209523 1250 827208273 827208293
    0x406030203240f120316030f081b1801030e01060f030204061203050403231207050616020607030b0406030209010e1006030b063403020304080f0604022407150603 71
    0x800a141e42d42200b0302082520355035071040050009440c420034040e507100f50340d4030750b0150520030841c2d1062105a581010351102c0f00803603030700c090307140c2c01442d403641d951012502000d00079103a54910305100d40c00212171481c0c0341061150041c180090600444000c0c2030942c0c500340c005c0a100c4031041d400300b08600745442100700801c083c140c1500384004540e4001c0062113188001780040741681c0c3c441030b445203903a0443c00305404000c111040741c4000c41a0070a582c01a00c400d441502034840042c1c2200e0818124044000c00d42e0301402c5142d5032420140c0040c42800701483d00582d4800c0d0110040e21038021481c007800200f4401c0d02146028aa0102580107a400c140109402c1890000303aa4a5a5040e52950501100750030826200485d061001d0b20300b020030342e98920394001c100c0302456004070040055928013020743c0d20a44010700251f940d600c05440094025560001e00c80b40b113040c0c42000c0001c0075a50240d82d00c0c0c0718803600d411005445500c619040a80d890100708200f00030854 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 827210773 1250 827209523 827209561
    0xf0c0b0a180311061b0601060f0f050901020c010810090515040b0a08030306090c16140105160c0b040c0510020c01030c031a1e06130305010e0f0304170c060406030203 73
    0x30a01d0100341180ea40340c0c40d025010360864010103000c905c00c0c042c41410504820300000326000c4408a40c0c4d150802007044420f4090a8041645203a8680c4000c3c441d2017202c10010041c1c00904c507501d0410011516160300a0504100050320200420980c016000d018051100f03422030111b0200000100001c42c1d41300090f09200f501d14250401401c0e0011054036071128040724042416030782c0c4805170005100d6403442c0b410301030864000070100300c0c001403042c00c0c050300200204401d179107070340800c61030b01d401e0445080170501702703100c0d2400030750740900c41d0780e00c1403007a5454203c865a6a000ca124024003550f1311001d0381041000b001c8a507410711032841d260035641340a1000f45c1c40705800b040c0d1100c0301080c041c000c8680c0140f540751000602400c12501743e0180c26155100402c082424101b41360f400116060b50904019030400107000503064000c02c5030101035843d240c540303420700c5034000146100c1000c40c0611070700511960b8130340011303000406850300e02680c0c038035200740140e4040c0c08046e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 827212023 1250 827210773 827210807
    0xf0415060e0a0e09070e0405150109022706071401091208010617060d1101140a12060801020301031119051801090f150b0c0307080301080a02011d0d0f0f0c0b0a 70
    0x6010851300100000302041152440e1a040c41d00b51168105981001d0082e8080b0074003000c410000151000c4a0713006081074040640000b60006070807421402101c0122079090707102d9000e101400106030581d1000b1424011400001800700099840c4c00010748101e4103c0003041d15440100040ba801140c0703c0682d521014290071946017540020301040c09208000d4080e40e03840b2030101d41640203803140c0500f104184405a00e03840526402443c00300051110054182070200004252074140240e038140e80d400041408030100510600c00a291850944503400405070b500003003941760140c00c1c10b2091401b4200500350b41c14054108280d400452904101928000382c03806035a42c035001c81000c0c4d6010004a40c0c0d40c0382d160006078510301400402901d0f8800000000501407000507503440101c0c03003a280c01003c6000d0b415842d42d10302941c410540c018440b07210b100000f904030105181c0492040d19011078001d801d85828006545035040541c0a100000780d200d651508106000302a20081c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 827213273 1250 827212023 827212049
    0xf03030403090b030406140a0c1701080d081f0806060405090d0905121e03071a070e3c01020609030915030c070f0501020d0b0a0e060f0415060e0a 64
    0x141d500400070015841110042000800480c04000250f00000c2e44102000da144d2075a00300844940000c24204040700045144018410b800407940701d80b00d0304840310311004d41610000260b00b039409480090403410030104100302c205000301d8010300c440c040d00c800e100a02192410600780011603034042c100744d80740d511406940e443d540e40141424187e9405440e01c42402c20307403056043c9000c048038002d50101d0054801d2401910340000640002c500418822b4238440e038012000250300005c2c0c0c0c880000402c0d0002c60340003030405107034001e0385454200f4a6407040491020890f02000454050359081503040d08004041da03041020702c1c0c120f0102e00145d4900800800028060a80130304c2e2400300c8031010002502a454a8090701d15903038200c240d000b00e981c0a458018001d41c0a95802d2031443d00d8030362000118144440c80000740c4401c07102c501d940381c80b1001004040c0301841c0101da03104e0385034990540c5109184440d100140351079142e24041056100411482800caa04515051004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 827214523 1250 827213273 827213281
    0x312040c1a07030e011b050a06060e090d03020a0504030c06170f19151509060f1d040506040908040f051513060f0203090d0309060305060d1218080a060903020f0303 72
    0x107941c2241e00080d4142446060a0007070001603454104a180d00034001440403642d00c1403150101300000740c544180e90422401da02e54042c40071403001600e1086041c0d01008400b15014040c1e4000c0c8a110b1150414506190b40d82d0350b80c2001504540081e00003402a60300385002c907807111a101e03040342400b0703100c1041d407030142415550b1200c0c1c0043d502d600b54440c449071182c1c030011000305001d05641c40c1200c1c880207243c24040c01078207003440b0b004009005203a2140d02c8034898400e00004444000c03560700c0300780c286400c00001c0c100c0034240c6540103030381d080001c0018458030001c00c004c00c0046040314203140340004001da444c4104480703031070242c42000707891703601e03104030040e081900e0403400c040200010714241240f4500510490385e4004603000025401e158101a020080b5540ca84d03042c85a80c0e1200c05010009005d0718000708010a80d25034002582e00501c0b055601c182c2030004182000d83d0707544140e00c0e06003044016203d069445181c031091560502000d82e40928030390040d4a0740c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 827215773 1250 827214523 827214569
    0x302041a03031e07150c170f0f04060209040501090e012019091d060406060f0c1e051f0510030b010302040b0d020301020712021c0801180204080312040c 67
    0x801c6502c54403d0b85449100c90001c40308420546080780d4104014440c61300c0d07520721000c020846002c40c08080784d02280760001541800120501c02d42802803034400c6c42d2600c0d110781d401144080c100301c4095030240407a60b172607102e6109884c002e100003a008611290400c44175400c40d044440e44600380380c9071413030b400309410300007017202d9030305105240102082060110172110300602d50032604064403a80740c4030341102c401d00c112a000e5501120100031090f5102800e80300060300b020031401086071080b995000c21061400d441c1c3ca4400300003441211480c60b603d9500305240d000d41c3d10402012a4584840c451140c4501a032003004030f10009140d905688524100c540e05200007880303185c40f80fa00c00e506031100200c1c40101680034000f5034484440c0d00d0681000e0301c96603080001032081030302c04460310815440c0d0000e403200a4952900f1030342001c1034041e240400f44e003401c0140d03408010000b400035040000304032707920450303c007100d1a042038600b0041c218a203600c40c07003800101c000d0040504d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 827217023 1250 827215773 827215777
    0x92d1505031b07020d06050a0c050a020c100e1302030405010c02190b0601120609050402030c0f0105071b080f07090b0301140604090311101d01020301030c0608040f0c0b040302041a0303 81
    0x141e00c2107020300384554030b04a5001c1c0391160800003034100c0c941c80c640c4801c001e0781750003203409003603078480511280420000407a100c1c015140440300583c800d0940b240541050118104103401d2032030090003103180c000110720040c0010b1505038001d0fa0000400003401000c0c4141c0201e0a002d00c094680f540c62414070f0a46005101c00c040c0204240ca4040303422607001e880d004081c04030b01c2d542400203990f20f035031004c020881110168040e0184040c1e136951031070810340042d036a440585905007002d01e40d40310060100c4100340707841c000c1c412210b808070b00a18200521808424610000c0c0035441c103284400741035420b4002828040c0e03042141e0302d046a01e014038140c1d4480810346000a9861550401701c88150740c21016a40394060318100d05c080c13282c1500804404110003150880340d04100742031508030707c402d10015001840c808810700a085c03082d2019504039004013690f941c4102507440d0000e00c101182e03c000c1c6c98180000b020411030420f8016002251180148042240c140d10701080e00d1b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 827218273 1250 827217023 827217031
    0x90705091c0c0b0f12070e090604060303050f090307080a11180103051c122f0301030b0a05090319080106080a020c073609060518100507092d150503 65
    0x5003c01007030100b0301307200c10000e64121007071440750710070581008103000e4820081450340717038000c00e40c01d000a041424580243d204a83e415a59240f600e54101c0901003035030040314826906004120300002c00034007c002d02c502483c0100ca103207006070520720811950304074006011076490700c41001000820004144903417408001d0308040070516990700d0403542c000300054030a018074a003200b01c04d00503c0602284140307900313a03509085240c0d0f8a16a420b1203000900c401843c031142e840020b5040300381504550740000c0c5260032039080651280d20340641c03100701a402d80000703c0745401001055071000c4841d8100802c1c046c00c600e450041032031980c82d01c6032805001080018030803a2080403c0c030b04030314905801d4806441c414403d01085600c040d002c1a401503680394107220204116070b50001040c60312001340c10090000c40910f15085005e4500100307030100340080e4802c00200d0413065609048043c0c1c201c0c408540b0300110100d8681403ca140e000249103c0c010700201500c103401200f180c0d08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 827219523 1250 827218273 827218289
    0xc0f0717060f0103080901050d11210106020a080403020f01090b270d0201020c190b040801050115030c02030d0f110f0d150501090e06040f020c0d020d02060613090c0302090705091c0c 80
    0x9101c01c010f190b00050198a807090348003845c0046c28401e41d80d003002a10b1560081e00060464698dc2c0d0801282d07207243c0e4520180414400308010401440d00a048010b8144d043c108044a55030700d45c0c002c11a608081c015280704860023200c00040341402d110100c4200080718103104240390340e00001e40d43d801d91313007e0a000d06600c58024040025101e0900c0060007001d4410382d41d01d44031103900d40648001e00c501c158440702640006000f5029000705403803c05240d0055003131114444054000c1d00000402110040d034403104041c801071440e00a01c0c895050315250b0340d0701e4528240c64011600c00500d00c2e0300300241d105c0103210302d0781d00003046011038000340d010f00e29688407200041d0042010107001a41c0307510000da54051120301045018020f402c03602562021401d900c02a6280c840407140c80354085401e038a44140c0046907802203948a0080d804a150652241e01064018201751030a8000c0388003c6030351038071032511207403420b042010b94a502c0010360721643c607402d03044014010180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 827220773 1250 827219523 827219527
    0x5010302040627051309030212030402090f0c0d020a050403050c0f1309020f090703060302030601170d1b0b0a0b130603150507180e040605010603021e0c0f0717060f010308090105 78
    0x1500384407503d84807015003c02041d207121102c0401e08080240003416044025004c0d486d04100c1405506040d0b03886903801401404169861a40090112000034041d80080e40240004840c0c40e58601c01780a020714945c40e4150740300d0541c00e181d441c29041c1c803103d602c5961100a5690340303441d0703000b5850410310941c00102d10240303e0700c00a69030044615109410072186c03010400c00f141d25400082c22240241c4c141e4607580d07200d0301180c8203483c0281401c54a0b90004000d000741d144181048590005450b1200c10040c0d4030b90b0b1172000384d09043d103071000b40607103a01c1e07400d0310b03850040310010500b002840f0400c05245155203070601c0040c6000c05904d0556600e002400745400703800d4011003554003201414040340c0740c51516001760016501640e140e4607110010614601038400c680c00f100c11115503810a100d501220b240c15031081c84030181c3c9004040f100108420100b0007800903002c0c1141e840d02034800701c2452440c00d40f000700100b10341d5a00c1c20040002c10600c90441d14845420304e801c075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 827222023 1250 827220773 827220827
    0x1b060d06090912030b0d0c1a0c03180108010807080a0b130807060903030b100818070810061d0402060d09020f061209070f051503041a040c030b01050103020406 70
    0x200510941d40010a103600340035400d01000b00708185a203101d8181c2e1000c0140d0b104010920640d2055808024200305c844e80080c440b444902d015802043c1101130490b203860061401e45c3e0a540015000051041002c404000e1940e00b208189004d0a0701400a00a0b1403030030301c685684503804040608100903100116441c5040d030f200120300a900580c0d030316502c0460b441c141004201020050b00044e00c0c01012031000e2400740a581580c03591592a40315076107403604100311840411904030910300c00c1c1e04000888460034049500e414051010000c3e440d8a0024600404005010081c1c0541b040c0340070400142e680800b6a22100080400061048141c1c804a9080d2184002040d80103c02055000b1a1001d801c0e45da4400c00442040d9802507030b451101510400d10790180303a0340218251408201d10030900d01559125000300d8207075039010b1100c403968107104010344050301c0644882d00709205100548000500408003072a00b145410304c2c00070001c02d44000005001d5880150040c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 827223273 1250 827222023 827222047
    0x30f0a050f09030f0304090b1f110a0b01060e01080a06081f02040305010203270703030504050402070c120803092e0b040e011103100608060609060a020a0f03080a0e1b06 74
    0x6241031203400f404980b4a055007401042c0c0d42d8001d031160418203404c0801a88103810300c4d0b080c01040c0d1000601d481307502c103100b04e8191040e12040d90320a0052041002600210360031644140c0240071a0715649400704034031000410303aa4000b0060515281403103010403e0100001e00300d00179003041c0c10060580d01074038403604007901c01c0342d0001e411136001005110039410640918249200110446800510016411500c822291001901140e002e010400050801d1f4000740b0384180f080c0101030f61036496503038107010139502d41c1c010788400c0c9021080005241c0c04100719684d014001d52103035008841c1400c00481000054014a0200c0d100d0342859000e0315903030014545010104020302c5041e80c584500c0000d608101c503050a00892244005180c9015140c80c50003a14040c142c1c618003030681c401e00c000c0c4c0d48140c1c025000c501c42e803008031000c10801c80d0113941161095858002c1400c0902203941566240d0401c00301540107018591100c40010b1000341c41e064082d01c0482d02d9910080c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 827224523 1250 827223273 827223277
    0xa140303040806010807172e0e0613020f0924040f0f0b04061e3807030201150e18010b100216090605180a021e09010809030f0a050f 58
    0x10341d83c0c412100046803140c80815500e064556014804020564503002d080e42d50840450300c2140b12079003105c00500d1020007071404d0304088403990100b24440d410f4009442c18004131021111490504411421450500410085502c08850010b90760900d00d40302d110f1008071000c0e50b032550030140b0302482a0340b50740e0415044840484020000c450810b01420080d03e0b00c942090700c0360380782140205e001903540d151441c06000b5000031102c1c071408e09041e950700e00300c03c018160060070080755503104200400404417900c0440c1c01c0303258649080b4138010782034400b400042c9003030107540c0c201805201c1c44240c2d0f8550006942040038410b030a07140002d801841c200c4c03183e64020401691084260ba000610f4007040c0d80e611840740903055a0310302c044c007183d50500415074400c42c0d1501100b469000741404e1764010b6511400107192003501c5214a0242135038004012015101088040c041d41c3c00200d000d038812244d4026601c1d051410300c0d0710103144a1403240d01b060150100300d40c5818840c0c501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 827225773 1250 827224523 827224529
    0x607080a0b0a091e05361204031a010501120c0314090c03150702060c0d0204050414040b07020f0c040e1509070f12030512090316080a0e010507020a14030304 69
    0x2100e1010343e100c102c0c56000c0c00610705003041012555401c510b400f41c40340304d400e110304120790312612264078000d2031104d12040c4106941c000c484452402190000510043c11104d61142200b9a50b5140d46090150408007a1708050101212001040a039030020302c0800e116014040c0020200d007140c20507002441000800d9400c2041c050030003030600c000180e240c0000100f101140c10b40e66810040709500413048502c4801a0003000c0891708a0460704042c0c01501d120080c00360400f601c0b4404101102d00462190785448803850501051005002c0d405801480358405000d205202100302e40d903c80d8001c000740e0050380c0e1030900c03140c0c146c000c1c81442c12000c0c06030182d001c1030410020041d925049800366800300c0e0700601d00022106e0100845a00883d49500da65080c25100c1c1d0780c91050030001410802d031400f0030400e901c0c01904180d00442d20a210300a1142c4403547c43d8402003030a91400b00050500c10b0030807410b00540d43c1c0310100411101c91100c24454605003102003811809140c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 827227023 1250 827225773 827225779
    0x8060607061505031204030507140a1806141008071101020d090605060f18060613120c0602190b0a090611030906250c0b090309060f0408010515030607080a0b 69
    0x40c800350300103258440e280080f210214121200c1e40c504503583d1006100350f100003401079201c00020808803205441c2c007505154001c000c103540e9580c0326080f20410f002c021014008564a010610410684201511602000b9240c8200c421070442024142e101c3c050b0100c814040030150f44007000d1001d404840d50325010840c1403000c10031074036114018000a5800c42d1013500b030007820b1040350414000b0300785007007100b03d502030241d141ca50070702c40700d54001c12030005440f00c0e128002c10701c0403130081110a03076807003007550650040c40d010300281044081100320340480303007a0020744007003908040320b2500992074000c00211150a0b18200c402050310080c4400302040210800c00c81110203c0c00d184a420300d00340d01c6441300b100b00c00526250340445002d81c00b0451800442c00030400381100c0c7c1c0d501c400c214040f60300d000440e00006038076410400c9401401100001e0500c455002030051a401c4003400c0c0f10303602c0407812500000e803201c02c010300140c108007090300015010003e9800201c01d0036006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 827228273 1250 827227023 827227031
    0x20f0307110304050402180f04052401051204080a08150604031b0503060f0a06053001140a0c110106141201140c041410021c0c05030a050c100612030806060706 70
    0x484030448507e140388454610038190800349480303900b4240981c40c46460404420070360202540f4003420741245030300700d4034100031060101e4400d286410315200c0c000c2c0d0144000607126480b41c40010007480d0000d05220f00c0c102c090341c1c07080c0e0340e413218026101500c1d031080d80407100d95000d000708884d48620342d0006500d07110304020700007850910b402c0030340540780500050002c203840b04180a481d82c1803e4080c209072480c02d061a9220340700d5052510304940483c000306864802503400c2d03111400075039402016a1792080d0b00e850080e00903460520180300d1f0002406402d00d050032144454410f0500f5030b000e1003041c001901058020340c4201c007030b8240c03c00420400e0a007800b0803007682d0401c0c0038544039507000c0c00c031401c150325182d181803020380b03010b078001c01c0619500400d8014010140304400c00b030207151003100d4005442070014001c042c60135030b10551610a110f414501e0b01c94421940ca200515011052000060042c4031640c600d4050501d0480e0b03445d0b800200b0401e11405002411480c42c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 827229523 1250 827228273 827228287
    0xc020102030f0406050a110a0c05130f0507031e090203030d05040c08030301081006090b091609030f1419050607180320010e061305040c140328020f0307110304050402 73
    0x20001c3c000d40346d50396503440c010101c070303584460f41c440640740050120b403003040c003c0006151400d6461601c071014207000c9001464489140309541050700c0303000110781c9443c00250103480209203140d6002d400301c820700002a11390042a01c0e4407400706000721320360f250b800003010b0041c800901001880100200d943e40e41e92616420740b1110380c01d030880145803e00c9000601703c4500e0140c6540904000d01041003922400400c181191112864205115252500002080e5940f01c0b21800900030f2042000e0601a401540d0030000c0040f80100000d004000190110304009079003603100a0304d04080452004540c0c0445960406a100a16004070000740b12000802a2040340c0c5040c020f896400700740c01c400007084202c7c05002810461261100000c101e60f290a810961107803455040030b0040300e140300d500d24481e620403906040709d0748112211700c29400004103044400c030250b02c0c0850401004000d10311982c070018115034200205d95950801050301401140c1c000c202c010021942d80b0301d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 827230773 1250 827229523 827229527
    0x90705010801122310060b030c1c0609090c05041104060807050702010c17220b0d02090a090e070f120c03123b0a0501080f0406020705070f031118070c020102030f0406 73
    0x90868030301d445d40780c202000051182c10800c140c9000b604800b10309030034510360f0703070b540c0d020b20380d5410008103483e8480c030002501d08000d11035600700501880450340d10508040501094407210f04900500e254108400c003d0b8650104010303400603101d1600c15503a110030f0004842c0244460300181c448160302c0000d040401c4514000c01401c500c1e0044c0c507502aa5100d58890001d91320300c20500542c404000c0c01e0310a6000340d0040659050042102c0a581d4840401e8000c41e40c50300d000c0d282ea54000d030420b000c1080303036140a80007025070001002e08800d1613606c0f21020070282c8001815a002d5032030510003540581d003201d4048000f6201c150214140c0801040c214207800641d0140c2602c12010322924181918020103490b81a11000101d03182d5200350100c401c1c000b8410b4070015400d110321400038070306000410081c500030150300c003103d046040a04000b00209007891281a68800d4541920103810341581d1180c4070341404404900705000603400c500c10200c444042c00800030707000c03604030703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 827232023 1250 827230773 827230783
    0xa03021e03030316030e060705030106030f0612050a141b041806150501030b151206010c140a0b180c060a0203070503040f031208091c121a04050907050108011223 71
    0x81c117940d081c009074050103540358071840280c891070f0000741304000500180d0b0094000c454060800342d400034000c0e64806207504461900c800455a64219109610501000884c00e0701025200c001500808a12030014803400000c0036100e030242d07031944002c008000d90b00343d60b08001074015409008220940101500e0f9101c140202404a460840b050740300e414815028100701c0e10b01c40f03034586403460f1403504c1080f5400041c0300300d0400c440f6404141c00605d244540c40481c00703041004101291092400a00a0300c000303040501004c6e008140001c0200c0025980440781030960310613694910710207080f4118810110082c01601c00002c00040203940c5000203c1102e01480d02d0340300006800707000702c2f503020094a44141c15442080d518164411804103d60104a6818001d508102847e04401030f109884401850300c0200c489120140c1481d015030356003c40e2180c040e1651078180000030700458010b0080200c6c6600e07006010041044a030004600451b02b4880500154115001d42e5960 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 827233273 1250 827232023 827232061
    0x31b040c03020a020a020616050a05060f010b090f130b04140f060102030705031e07021002010c0e0a051008100806010b0a11060105090f0a06030b131703060a03021e030303 75
    0x11894030480300061071180c403d89491445583c09819440c03519020071009400c00442c40c08012010040703280015020000180598818000740005107400c0c3c00500513200140d01c540c81d0500c1c100201d030065550b036480921115030440d40d2969500290761090000d0034800c03207480d0014138041d400400f402d01484943c0c0f0a80c0840c0c520002e40c1d1b5020012610307402165402403540d84144a0100070401c80784454110491300b0301210b0806409400007071003000d1000852001d40d64408118007801c2d8048001c2070380c80b20039110300c00c0a51401001c98100d2a00150305030070058200041840002001d88900040c54401d0890741d10b175841d0088420345500100300d0001054550415094080000c01e00030304907103000304014620b035240e8000314140100181000c880d03a40e2a03401100041e031290301c20f801180c0c0301c0c112024441c010318111118a10741031411005c42018000c00c5001c1d61100442c5c13096983c103171106c800b403110410000f5980c8070141d20f101e50602002c0100011050520800901 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 827234523 1250 827233273 827233279
    0x20f0303190e16210204020708030609060a0506040915030507141801080312070e0a0e0114010809250e0a1a040c02120901020a06060f080f0d09060e010e031b 69
    0x50610210040e40d2090b800c1c00c40075580c140001c082203104d180d0403013540b0458003001d0529a550039580003500321f03488640212018100072050080a08040c80a180c0c840780580d03910800b507040000151850056100304e510303070f43d103070716000303d4103080722044c10000e40d805811100b440e500da20910f0300c1c583c1414080360160088c4240c105000e1a0b13203420b641200c0f0182d000d10f1070428550640705000b800100804188074102c080065a911a203c14200608840544540039414016100008804400c0c1141005510028404000408100315030000520792114601d5a150750040030348190a0740a01488a000c10400c030050703076140c00081d01812050020080c40a49500f00411070350708240c1d150060780590720204031502003c1c01042c42c00c40500441d04911140c1d0780303076000d40700a0342060210b42c498000800c2805400c222281c0c1c03184d02c2401030611050700c110300500c203505c90303ca40b204203d00b00c615140c160b4044c0844a03168130014080c0d4aa48260032420106039004a5074a80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 827235773 1250 827234523 827234531
    0x20910140a0f120f0b09010e010b121507020c09070f020d0c05061512010e011d0706021213030c14150a0c0605251d09190c020f030319 59
    0x200d840c05004410a4034190b14055039140e060001c00c0c12207050b040000c40b04042c1d000d50354804074552103074481c0710ba2440300000c1000c44422105034252000c442115004100d0409070340211000030403107214480030310444070542ea4841c84100e2810203441074003604002540144402d40d40c1c0040340c009114600d808444401d100c021044403074a4813201c1c0900f141d004080400d000d40250303030380100701f204003d04003210701c21040f19060840f0624410402c4030783d9201042c1e03668080b1f20101d2000707124800003400c501482c001d40a52107075400f209100884400081d40742c40b5090190a03440a0341d0003031240d150f929201d50448400e06542040c192042c5959032104206428000889200b46c1d610341e1000403820550b41c4040140c01c014150380300d8a1058803c8803640c91035011000a400030365510407100030181034880e91a601c1c40d44c1040d0003801d01e00e08101c0e02084086c00030480800e40ea000241854144500300c3c1040081d012040050100000303008164080c1c10315100340343e003000f000700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 827237023 1250 827235773 827235809
    0x31b0b031003200607080912010609020c0c040e060c03220b0702061f120c0504020c060612030708120a2d0606050306091b120c2503140c0703020910 65
    0x14100e003d40304a80c04501000300c40002201003014201040000e020580e00ca4452060142918556000380d075040703502207041210b202c800c1101a0100c1d10507036040081d60701e80c0c00300c0d03a114000100000c1d1180c800001040f0f17680d030740035620140c014003004180c0c0380c0072003464080304501d01502d03600c006201c2d1201150344882c1103668040304100310b640f4101000d141c1800807200303000340d46040d6808054050000744035102d0b03000403c01e5814a0002d017646141c0716042040c00310906c9070005c0c060340280001c0b400101064110f5050a00007000e5155035611090640041c1030441810076081c503800d00d44015000c200ca00882c20a52121400e006498031a80225014002140c074503078007285100204050b40da40d02040460700410740d0003a450464401c080c10150401590b580c1000400082c60703c2e0050401d14030402d1050940d500400112640d0f14010040d00903140f017416034000c0000c03101200304081180070011640548800d01501d80051301100e404458803e004034028015140b0f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 827238273 1250 827237023 827237063
    0x10030215090f01030b060c01020c060601020706023910080105091518040212120a0905090103050604060e071805221707110a082113031b0b031003 64
    0xd039a0001c40a0301a4046a421200440c0900340340b17a00203410039000c00c40d039070b82540b00f03000034404041000001c014030700b403400c0020300d40340190748141d04641004106001452400c1c59001c5a59800c5020150b0656144103400c0e468110f44102503002143c0104d500c02c03680c00444460403103508a4441074190340703d505c0c490206e80d120080d50341c00300f50300740c2180030703c0750342503141d9002030001e0300c0d885e080054039040a1401c10640202958104040342a90001d54000482000380c402074420b84d030b941d491640d4095455102400080c0180d48a14080d001c00c40100194801032040382d00c5c0280018544581c6001041c007a51284100700d00d0a1200c80c1d0f00361243c44440155901409203400302500c0185a52560003080c41180c82d0081850400101e40d51075804801421040010b4000c04010460040c4403035001280c80c00c8901007484807090540072841e40a0840e50481412140b103140f51030030618003085a0025030a0400100911030042400031401090f00c0c8a003103a0500c0d540041c4503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 827239523 1250 827238273 827238277
    0xc02090a0e21090406080601030b01150e0d05160f180c020a0336150905060307030b1305180708060f0a0b0d050601150e04020c03040302010c050a080310030215 70
    0x41924030368071040807035a00b4800d6001040488900048660601e41d03540d002074241c90b80343c0d0000f80c59601c40001401072103610146140140341141d440e01ca4231840850103082c54000d8a80a88111488040b100c2406000c3c0001645003920340343c65000036840e4840d1417003030759060048144020710745402c40e166103403a02c1042e115a2541d0000d220048050358111504a01c5020f403000c989810307841500e00003241c128180d225480c1449030712005041c894400303a11513881c04050300f049014030081100e41c132044100c0750030038001d00d03000c507800e9041c9001c02c008900140305205040c0c508810480c1085400da01005c40e600300c2416103442c981c0c0c5c0d01d0b1041d0394503015034000e00809050b20101d2140d00055010507000ca03009031050340e40201e940c4499042c00803d074801c000703c01c620b60320703e540c3d55030003001c80306102008ca4086007030a1328003074840e6690255010080c10f0044120b280000d10104000b07681101da80002510765a00c1c22942800e0065800d2000f2030040f40602215040400c2c41c5007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 827240773 1250 827239523 827239541
    0x813033203030a110c0727290612360d0503060d02030a110127030b1e0c1c0501051c0606080a0b090d020a0c090c02120a0c02090a 57
    0xa60641e111043ca40b00113040b0b0003802605030b0820881860720400a01803140144018075003901c1d004401c2e42402a8501b00103104e2468134038007100c001d252401d803e2001038044104a86640301c00094010502c0f40c421104201003031592403080100d09407c151501c9480d50514500d0002c441c0700314050b480200c0301c54580380e6250070018031050b8207441070000c0c0d0750000d0000d0882c2c2c6c50048640100f820310030b800320b054a068800c5080c1040c19600561040207038019014151b4811418171007040c1c0a004600004150000440c049400d52004840c450300c11040914100590301703001e440c0c080c2d5a40320408904800740d281d600880a4140741c031425048401c0074004001110034030b00741180822140d04200e5400d9552880031508a904100d000b8085200d6210058035090906c0142d1400d9407000c4407804540c4211448000101154110801c88001580101c1c4400015605034100828008603d007109408a603a1003241d034040c0010031114000d0b2507446442d1280c80681003a601c40c1c1d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 827242023 1250 827240773 827240873
    0x504080f0a02120415110309030d05030a0f18050d1e03020c1006060302120a050c0f0c1c0507060b030d1d06070f050106031203090b0402010c081303 65
    0x409209a200e003808014442091544142c0700100850b01d06460075803c00d03040f4030052140c02c92859045c981040110b40307072444000056003004080c200082d03840814503814002c01c00048082001030105410003501044031240031b20840a8401d4200000d8035100005e940d41c2c8550034904d0680c0d03008840c0103124105e032035045ca070146100c00d0164043d43c0298090002c9100d44107010007400a80e00c140f80c007504081c0e8001da0b03602c01c06030600c2c03e41140030b000e42e0503051411041c0482411444100c4450410f480102c5484901400d00613080091800d125110308104801c1400300c00e078414010311001e4402d1204100c0032811005155030b503255480460f000c01e901c000a09a10381a49103010800b4400800307580c500501c65440016040080200300c2c0d00713a455040138010441c0b04106081950340e1803404102001850300c81085079030000d00003a060110040e99001881010300c1100c1032010709440340038640d6540e15280e42e04408004d282292100034490600d014a140404546051050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 827243273 1250 827242023 827242027
    0x2070b0919033e03090406050f210f0708101a010906031d0f07090c08150d0317041209050319060e07032102010c051c09080c03130315050408 62
    0x4642c14010006189490611400100c14080440c9407643d400281e640758040a982c4402002d803c1c00103658098105622070300340f911103c99542c03031701c0f88441941e41c4c0c0c0c40ca540000161207000d9508140d05803d00002c5806a58008101c90500149124007004059801c01c5031910315480c854118a0b6070281d50700240d107018082080e58483d4010303203607241c4100412032602003081003407480c1c002181d100701c0313454220302c800708140070b0b41c3e110344221030a07503090001d1709250140307541304456510001e140c03041c0356500705107081c1481154904404942d10001d0305c018109800d040601c00340807031944000541240e00807405040c04140c4040d0100c1000382c401011040f691890054500d0310078002c450321811800101056808070443d510700074403611513080c029080300007800e44064840d0381d4140802045901807800c1c54004625070800c1940c8009260400c0340741050540c46041c000e240c0740d10001c00c2100500d8003445000040724032400c1a188544802c0f05500213030303081102c012b081e052007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 827244523 1250 827243273 827243297
    0x90103020d02040911190f08030f0d1815140108011e20210c04050616061d070914060306040201081003080316080601020a11040f0f02070b091903 64
    0x4540c00003c20103119201444076500c0003c00720b2010440070400e41c01d46c090a1808119010419000d6005482c40d40040c61414414101c071062900c100f105292846641d07607004050014a40701c0320401640c015180c09100443c4c94240c0d016045031010800040e44400000070110720502c40e00103208600c1421104200780440290f004003120b041c2d4500d07400c030701c1d0a032500f14502c980041044000c0600c000c001c404605000500c3c40100801c8100410410001030150b85d0316842510b00c1c10740e0744642489500c00924042c00900f03401ca110b8900b1080181032180d2105010442c80305650382ca100410204100007240c05408909030b81442e0544c001c3d00204001d544103002d0301e64005108603100c2e0416aa0350f42d020900d40c001c035800c040355804491a100c045520041c9039070402c800348020094002c441c1c0390840c88040d01c1620301d03c2140c3e918000a10402c07260448501036002420854855600303003003003028210211540110b600850681042800b02d440b500b0301b080e9059074424070341200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 827245773 1250 827244523 827244529
    0xc020f10020c0109120c050709050402010912080c0604030917010501051f05120403090e010b0a0206070e0111010216061401030f0201050f0d150e16140313021e0f090103020d02 77
    0x31000a40b0700c042c0d503d40d5a030b030f400b060340202e100320780318010b684e403900310baa17103040c0b16041100740c1c1c00161001d800c150a00001d40e03400404a17086d21460410403c41a0741e501d00905580705004030980740e80141c00800003496040075009040310050307035030442c01550310200c550888009000c0d070341e408070030440c4c080b0a005081401c031808000c1400e1081ca41030f4a018002d101c1e41048408800046441da02840380c0981c0700e002c540145089041c0504081079000c001e501c1e01c0d0000d01d403034104181040131040716842020758400c008040c50003150340314940080780281890001c400d40d00e080c20950101c00044031070340c200e4100c039080b10b00201c5075203042d0b00455080d80608503170f10344c03c0000d000034481581c140c031400b40d074001d08000100881c3d2401781e44074603608000705500d0112400c1694881c0c46900700d0000410381201f9040942c1d02e0391102c0c43c0641940500304007075044031130000c040c445604032800c0c0d0000b001c02140d541d01e12121103020404c41440900000f5000b1307205124400c0142 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 827247023 1250 827245773 827245777
    0x60f020424110304090b181504200403050f060c04080307140106050a080309010e01030c093812060d0818010309140a03030b0603011406030a0f0f020a02010c020f1002 73
    0xd142c689200140d45000301180303103420982200000c40e5441070300007543d180080303120440c00c3c1040f000030098030b02454110741300200703440b11501850321001004100400c9042d4503041180300304445480b0f80d22410310594420188046500e00e114190204106081c1d00080d42e080b23030004002145004070b1542c9035651008000740301c004964880c5400726555030f4821804018244180c01152140340d164001813417181048841c5052601d000c03442c3c6000c59000007840150340c44290324244c94480d072071551004501280d07040c041280b00c1c00383c4404c00c2680c0c0c0c00410344c85400c440e102d0016103800b82046901844600c000b80740301c00030854481030501c10b10f00d10743c801105040000704281c40381c80e04080c0403ca204e5010194208040801c201034140c4038010b4406000c0e00c40904545c142400300f107491901420582c403c0c040030002401804040c8c00400044004034000e000d4040d0306418413010303400001040001d5420b12020542c0c40d480014a907500203101c4001700300c40c101c0030126800039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 827248273 1250 827247023 827247089
    0xe0307050d12050c07050904030f030c080103080d0b031009030f1103040623130806060a0e0c0a0503091c0201060e0a1b05030603030f0f220e04020f01091d04060f0204 73
    0x20303001700500000c2c195079421400348118001c0d02c4858408034a44d40042c2200e000e08000024032500400500c041600340003130b901c40c0b82d050140010f5543c01d07500002e14042140d60082c02e0030303091004076070805501c0644030014451948404500c00488000c0d262179000e01e005003800120300e10810dd01c1c800520001d0140301420100940c503003c2c0c80c9400404c885029008016194002c6091204900b8030744200d40007048868003c40c03250400c50502e11051040b40700503001c0040101c08940c0005d01803000000d02d0a141442103a140c105138070103406000c00b4440c1c103048410341700c00500741c50068042d0080e0320079403020210f0303c9600c4100948141c0c20291146425110038001c886488101c080140392401c281c003242500c40c1c0803ca06400340c100e441d43c000d00803805000d02000b00b01034040c1107603007083d8110b8282980f4082d43e00100e841d440144c2c880c0d101c41a02c520071214000d000102a070003580191001c0c05a018a0780d0f030304007a40300b207100b0410380180d41045401001074110030704181d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 827249523 1250 827248273 827248297
    0x23030c030f180d05150603031e0c0309120d0201050c03040302060a09260418020702010504030f032a0302010b01050a020c130906050708090f011815090c060e0307050d1205 75
    0x20350702c000d0000c0781c425100000c0c111015400a10310100384000c40c00416803107a0103c00651034400311000c140c81603241100250b80080001c0340c065565101401940c02101001d840e0303c00c001100361140b55106140c050400c0075500e06400b06108520107000c9a2286806400420385030b1034070400c080050804c00c105940c205994410481401109648842d00d0030300415100d403568288890b003030b810181010800001c0d4410015a001070340c018041e1000c032500315440121401084c101a5008000300070604040c0300712011880c902409540c250140a00076802007105040c50801552030b072081660b41400741c0e000c9c90503a031451a201c01144280c10722000e0200d040001d50365044252038040d1658408140b4010030481c00e00b908105030f250500e00c4030000e000303800722021201c030303142852a00500f2400c0c01c84c503072008201c05a041650310540c0f10240814040e80c60000810340f043c5503214034407030701070309000107074a14020308030508240e00a5030005444146000075940c0d84d1010f280851 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 827250773 1250 827249523 827249557
    0x50403031b031707031406060307021c0e0a0b0307021614120f06090606100c2001020312010806060a05060903191b0e01150201020a0905040f0b03010923030c030f 71
    0xa01c0c0c2c0800740c2c1c41070142c00701385c901041c4840e000f1105651a10001c01c0d5030700548040c01004a859800030324200c0b4200c0301007103000c0c0b00924580480e00400741640c01c9411114140f000101d620400c0300951060200d5030030380740b245201c1d42d40380e5040c01c101d03c0b4403c00301d50100c0c5114110714200e4040e041e8211140d04452039001846162803c044c011221030340a9005a001c001d51402e02c1d20b07601c80c6401803440e24208003201c2e030360346000841078160300500e100c050b0350310803010364020001c07618411240c0e0300c2540190795039200c45598103400c50f0071900030000c5000000b01820594185c408004005000e005c042c80c07070306a41110440111000e484d01b0074400b100841c5040c80421b00000340c100500c240c1c40315810300300b400c9424485100107000710380c810441e0071003c5900140d0401580c00031100420703900d00e015010b0000e4180d2056055155180402c000100007500d40e151061103000780d40040540211503005859010725540035256800800400d00d0304040312008003249082581104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 827252023 1250 827250773 827250797
    0x160c0b2704150f0311010f0f141b010e100905211c091b03020d0b06040f0e0a290c03040804030602070503031e07020a1401020f07030915050403031b03 66
    0x3a070b410440d90260400032065041401400300081d84500b0041c028201001101901d842c010144040711520317504000c04102d00440c032200b41c00466849032505d12134203506181e01c049541c02000c082d846001c0522841c400081511064025030b00c1d0184c22134090000741205841d0003001c00807005400d0700e4520100858622968112100103c03001c44c010000380c1a086450512203209500402c070181c886030040400c0183e03100c1c40e03030464036988940034608a880380d00c0441d02400011000b03050840c20030034603100700d581c00100c1800380c03801406040764010003403040c0031001c0d0301c0050704100700c541d290010fa80d10880d00d00442d000b42c841c8cc0121302e89a030340e803070f42c8c0103d07040319000300c6440d040041030104480c58521032113400c9080c15a0444070782003400380a5a40c01c810ad00c0203040b028014500c0040f06020f40c1a1240c903d1011707866030303603400603107802814446103009007900503620301039000f082442102590140caa040c0c0b00d241c280d25484850b9039072800c40c02400c0b42048007414240c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 827253273 1250 827252023 827252051
    0x3120e0d080405070905060f010c0f063e121f122901170304030f0317150d0312150f081513060506030a08160c0b2704 52
    0xe210014059861401a040a250040c1840704990040840c1c1c0e0504080c404d442c0d50b8041004d07040c80d000d013402c0100d103034180781140c0c41802c4c2180151810b03245c000b0250030355802c031441800d0b1200201074421070100c028403c510a4031401c10900e22034009011030700b000401095215048114640300803111500b43d0002d000c0080150419440040c116580e9410843d450340e01000c0750094003180c0003035070081c01d05000a00c0301441200095011540112400002801201c0155030011103c0c20005d1490501410301040003600e141d8054a202c0002c02c80307941c041001c19220002025418101c0c40c81c0c40440d010048441c5156100f680e4250144c4200599401308004140f200408408036107031042d61800c00b810360001d403c4c50b2480004101e906510507906030452a845040024141c68a2011910f001c1245100824040c0001002051034078035244d0700c40c00d144200700c12141c2c0d68a42c0040400e0340290042d1241644449420040041d0310040340489081c01900c002200241c1c0700403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 827254523 1250 827253273 827253283
    0x305060405030a030e0309280902180f0105030403081b0f18031b09010b03090a140f06070e0d02012307150c0f0816020a020405090318030706020a03120e 67
    0x440307030340d400015040c000c01e4050141c100f035588203401441c1011071800200d510384112491034420500820300704043c0681c0314500718050202150115144c060710141d80082440b001c1c3c0d10b40c8602c0381c405403009150b11510841e4807856241c1c1d034210090301c5400c0920001c2c4400018482000d001b400b4004a205000c3c024041d078441c0303400144680b0b40800e05050800318036840d0380190325a03507001030f02c00d41c9800d61458110780710802800e90b01d580310b800307203420140aa5030040904e10510400b9a80388400180b80360315a90401c2030ba50981c603440c3d003d590802000c48015040340c0022500e2016600031800c400d11451244043c00b8401441403c9070b11580c00280d040b0f50b5038511404020014010740700700b1f1880084c60502a08404d0b900c1d001030510f10005080410200000b090b039075280e4400d002088107264081c2081c030642c2410729aa0361607030044007004011003c040004c0c0024075000a1810880d4040d030040c1608038001d031821204a5031012041c2501c2c2c0c0c03a60400750201c20200b207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 827255773 1250 827254523 827254531
    0x60b030103170c0c1008181b13092a080d0c0201030c09031407031b081e1603061410031104020a0c0b07090e13080a080a2013050d050304150207030506 66
    0x40c030b501c3e01e1f283c03c00c40c0003c036a490340c5c000d020981c41142c810b42203403119050140b103c007046030030007a82c080801e141e40240c0703035080000340207e01c20403074807160b0300c04d802c20311a4071100d90001c0e0740c41c0e41d100e101d07803551207410207030311000074404052103405940a81d01400710412a460050303942d0303460340c440214080030103801101700c1d840782100300b0900c09150f00300c2c071400c03401d801f9640b940c40c501204295101400300507950459003001a19400600400c509008598081c1e50b07441001d03a2400d20074000c01c403441c210002d840e0654001030500c00c4400c510412349602680152175490000188402904050f9a8109002c03114841002142074929000d00c944095500c6180c513508201980002d06006800c044d90300300c00d141d017100000c03e40020340f1001c018514004650f507541781c1c2440081c2130007001d03407043e1040c0d00344000c4007121014002d00f143c0800366a15898596600240800c18842100241c00341e0024401400001d410301c4030120752500c2d0b84126542c507922a1580c90900c08192 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 827257023 1250 827255773 827255777
    0x2180a081c081e18011107020109120506150d0f060c020d0f1202070809060d1409150f0c040e1603060b0403031e050f0c0a06060b030103170c0c10 64
    0x15464824441d6080c4414070700011a140c003464030300f855110807590758600500081810b19280000e11181e00c0d0190f0a11600e020310003d1080b9103648140080030383c40b500050340010a284c001103046c40c4184254611582d01070000c1811780d41e4918501c283c000d1069250b680403030009080c40104000c400504c00490048100240c13111619002174a4444070170005800c0c810304030a21003040380c01180c5180812003681025980d4852032034a000c1c50b10420401f141d114a0202d0815074000c2680e12039803114000e200d080829031030b040303600d0b5990389100107000c1c00981d00c80d00040855044800c1c50340c004808600f001d050036220b00c00e42a820307404503040801d040740c084040d069650b150040b40000d003120350559103020b080d07031802066240514420520850080114081503102d0b40440341c04502c190a00c0c4d450f00c0d00400d07415210103410106035429030409501103102d489001c1124100c81d4050494600e44100400c221a1508551142001401059680c01c42d030389035005a02040440b075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 827258273 1250 827257023 827257033
    0x40e0303130204060506071118040f030804080409050c0c01050a0204050a1701060b0720240a1e110c0405010f06080403090b032d09100b060f0f19020c0108070302180a08 74
    0x842884030751807281d27080701241c00c4201c1c01d00c004202c482107801461501032824680542e1f8900b0444d06500c119400b581c0243c0c54a0304101844428802034051120702d54001e00164882d1983c4c0d07000c0e8003860180541c0000f9071a0104201d0810900200b14103250034004a889503940030175000b99000248140d410003c00b280d021007000020402c8800c04000b1a81110420107014444500301206000d16408500015984203030307034007031841e6800501b0001001c2880300100750000300710388d00032148034072144a0f00300064024a013034002c0380d05803034050144002c12850080304841d080e0000e00290140310600300d0114007645001c000b94030071301503440ea104154981001051580e18140d2034162400807440501c07160080108400403010103c95003c205592014001a05403084481803920704200041d244180c2d44224003070421a01d0108030307405540902071040e40c84a0921803242d000803201000074520314020340c0908803035040e95000240902240b004126180c10580208030300b0351103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 827259523 1250 827258273 827258303
    0x6090507200f0a0308150d05010c030b0d121404090f15120309090b060d050405011a12070603050c070210020106031e21021212010f05040e030313020406050607 70
    0xc51881c0c1046400c44001c04030b2040c1106155202e08501c0002410000c54601184900c40e4100d09040b50000051020481031000d1814600070107003c0d003040c010030704040304000c452404c0514602d00b035400406042415070854400c035444040c00310264500102400f02103250102c51140100c50110710350002003100703240641c060088050382c8030246014880d80c4940003c0e501074117203011989404e0000c030b501092100015250f00880c101034200c60b140c6030410050040c150440040c1d54003003000008181030041c140104c2076074020354118103074041941001110b02ca0b5000036403113610024681e0605450368001050b640a080003100140c1d1500390510500c8102601c152808400d00c0727104900c01059910102280b0244403a8400d5070151400070301480e000780147c01040201e43d4603103503030300e0120f8210303401e0076020b0094520300c240803c008038040c20079114185001ca01e5000860540e55844118000030340e610742d040b40c010ba00c4200001b005c2c2c48480103400da01c2d200e5403004e206105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 827260773 1250 827259523 827259557
    0x905070b040906270903050c011e15050616050a150203161b0201080901060512100b0603061e01020a080301080d0e0f0a030f06060305060a0f05090a02030d0c02010306090507 76
    0x440d540292000a0b4803c04c408400a9040ea03201c0142d1000c040114100b1140d04041d40d490003030001003011542841d6540100f050b034585595403008080300c007044800c1011032882400c0025000745608450b08009c12504010350070700358040f030ba05c034074101d034401c802695400710450151000f501038240c010060080c0c5501160b030540c2500403d02d000e00c40c0d0681c00401e011044d115401c0a03040c0030440300400c4480c442908031001803c3d020f00104946049442c02c40c2d0344001c0201409503051800c40d416130326240500c100c1c0e00a400060220510044405c0004540050403200c00d05601c2500041c50008040e100518000c08244000c0d01c1c0d960000d56019020b1075020042603c600b007903000c0382e5640e982d43c0410b441640d4000311555900c00852400c00000c09081e00044c156102d08001c020105000750840d003a07204110105000e030340c5910800b640d80e0012140e001358590042c4500400e85441000f024103030600500d0003041117584c504004003100c1007692410700152140e0608a500340d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 827262023 1250 827260773 827260781
    0x20403030518120304151215050a060e010806100e041104092a05031807091a0f0306063a050d05030c0301060503070309060c0e04052206050402040905070b0409 70
    0x1010349143e044400d03c01c0d0f0194403486180200c5803401000c3d11800d103454824100360500100200e000c115000c1e02100854500d440e41c442d40e40710304000c03580440d52520551034003100150603160704a060300c81710200702552203c002e03602d04100040f06005096500d60148444da81484940f1300e90750341c01d0095580a0305c801d6080320301c2e49100ca003001c140c210014800040601c009152035501e03034540400c140f406130410401c20180d0b114401d00814140c8889d40a458424940c40484106100c001e00b8880420280e2802a038141c10210004141d410f042911450702c0c00c3c441c51010300c4d040780010920010b142c05d5101e040d10300110548a0030058200a50ba0314844d06060107070941c90850310601592005001d0f85007084000300c0420b907214000c1d000542004e6220070103120386005564001c164014032180c1780e2040d41801d0101c0d4103060b084030300b481c3c07058500f140c031200e000c02a1140c2c40174204c040d00403a08070f80e5800c0c80801141c4240711200113444070031146541c46140014407425a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 827263273 1250 827262023 827262067
    0x191b0b010e160507110f0a03050f01060e0402010f1d0a0e04060b1807110c0a030302150601140702010c080918011703161103012702010912050703080d06090204030305 73
    0x2000c0003842c4100301e03982203400e0300ca096a224400e990f0070304880d40414080d80c0340360030030f0b500035032400d4001c01005000b0403558a02e490020017044926501c52501582c502c003540c000e40403c1e030950180e59a14400c103046001d400400820080c003646200c0031441201c3d43c0d90119001b0321041f07051004005140c06031001212040390f07001d0f600ba40d607e03040b08890b040a003d80b818054080ca00502c482d20034061030412140046c6440340341d603501c1c00c02030340720800c5800c5541407036008000248958028404400301904814010b41800499401541c3d00d2007101002d83e5424420707c00804140c0c0c800c07442c1e0300c5401c900c3c3e000032807651510620350a20340c1c1044440c8180d400c05d0000310414400d0400e011000c58020325592003a81090340841d00516250020820360a1150003000c00983d4565030b08000e903200b80c0e1981e01e000e80e240c042c62055030b80311000515580202e5420008103651703101a12001009480004003e030386d414400c4102d920580c01180420382c00700c2d621480411180044040b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 827264523 1250 827263273 827263291
    0x30f0f060112030509060c25030209070c150f0f0615080c0913050a02090301050a2028170a090b0603030903060714092e14191b0b010e 59
    0x50b85101c2d0f502074800c0c003521820728051100442d00307000584080044800c4130000510380c032801c0c1034412480b003031245903010990140070030b080404e00c92403103006a91503282e0008138004000c48007007034035809440600181912140c813400d240107490007510602c40140f2015094100000300144040e100d4117005040c8a5056818003480143d61a1010558000c0d500d1050003d650354072022a50028000c201c0c11903090340c81c103800c018043c017141d80002413440c0310700007001c4100c180301044401407056641040e03c41c00c41c88910401d031039201400c4c2c201c80410742000301c8074403108034803120040f104a40c850070305074807900c1e44000d2220610109400c9402600070394a0a800031307000c66038030540505003000b007104c6044145020b124100942d6402c0c1e1009184003c6030a00f1594030b5404a5021945101d96000903002000c5501400c4000c041e50026011203017060090a40c100400b21420000e41c02e10031800081d600344032001c1c0c40c1e100d0b06403141e01000606d504051204820301801002c40b04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 827265773 1250 827264523 827264549
    0x60c06100b0703210609020d0507020609010b060409050907180f05010f0b22080106060302030901110717130902041203170709050d060204050a08030a120c050a03020a020c030f0f0601 80
    0x401e603c8144c0c0c45031645100f04000c040c503011181c000c0101500d9224442d9144003042802e12001187c21143c0100240d5084502a4072100714140c221003000c02d540b0360100040104011040250b00075950045255003030b100d041d0f5603200c40c0500400459002031110740c1e600003e111440b1144101e50252910f40222521207007010145015480342403810050640241300c2020b103450110514400340c60204000d04c2816903030340300a0302940050300d12101c25400d24a070703a0f841403829001e80310710542186030032125803c654000030340d50303026142800203c02c000380701003a0041d07540020001401d80d800d01c034014803450300700140005107007210b9460f4039003040240704440313502c062064103490003111007051050ba01d1402c640241f10790381c0000d0704001281d0300001c0480001c00034010701b160503114120792400340c840724400c0721501d8000d600414410300200e100300b4840c0d03029011519490045a121300e444c40c000170324041844a4440a45e444000200030f00307001070104074010300c40c20038046 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 827267023 1250 827265773 827265787
    0x910170312070801032001050d024504090221030d05010f061806020d0e030c0910180b0d030815183306070c1a0711060313150b060c06100b 61
    0x92261203841c2c162055113030046203120300f00550159001140c00c1c070f41551141030196404c1300e84072140c0c203880c20300e81010f92040d00c60b640c1454051090082ea00030020381544000180070403f6101d1f0700c0d05200140700500140001c00124450140038081a0740720110340c43c0307040c000031300c0200142c070491000150034a082100320740010b41b208240305641408081a5003107408a4a0b091041c8042e48d840803d032414440c06662125001d41540d00c01300e00d0349010300251a0341c0d1305642d4880c1000340c004030440844d902003841180c1403500000031a000d60b901089035030020780d07103c1c545045000010780700001c3c05034800da102c0c040070300c850803005c05029008070140000900300700244618000e90f00040c3c903000b040504500c3c1000b4240d2011510b4011102840428041d0440101190301c291101000d00341031a003641628858244030900c0c000502c02550742c007104541c12180700c0382586e1640d040d4213240c1d4900b03000d0210f003101c68006080350b02d42a8450080344000c0e5102400c80e0b01c1c200810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 827268273 1250 827267023 827267027
    0x11a0105090a06140d110a09051c020d020d0503070c150c050c100512010801020316080f0a0905030903011109090609060303120c090a060c03020c0910170312070801032001 75
    0xa1401c03101c103810013001c070300c01445594899128425001009074a00150708000c10703014030141914003001e640d4500d1003515801441100d00025200e4145801d202e500741c1c1c010301c1e101d5028601c032031001d007011101d01070f0f580e42c1f80c0c6546c12980c0e085030a00d240d51014003103400309000c14581c42055103440d04882c0c2040e1aa00d481d6207141c1c00d40c9000f60002500b0394038042c001e00444410b5500004445280c1d03035181c00d014000c1d0401d55000c0009405100403c61292082d43c2c403034025130104041d100c617034844405d40c0c1c004240c40f10007151180020300c08100c0759036080c0b01d52651a00b034180c03c0c0e655a10580704101c078040e4000c1c60503101c2c01403c2c082c4078150306c000003551410f00401d0075543d455210342c1200e011a01441d1b000c42d6003c3c00c1c2c4d500c04608994020340c01301c482e5219400700c8449a2800e02040b00b2405c08642e02450f00c075020b4402c2000b40c0c00b240f501c0c1d4801c600311050742d160850f01010f03038054606c1126a0000f280481c0010401c1082d03140b00c1e600301580c160350812100c3e91004c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 827269523 1250 827268273 827268289
    0x715170601260c090a06080711030406050921011112090a0b060126190c0905010f0e0a0b03150a06020c1804050c03250f03170307051b011a010509 64
    0x109640c424002e4000b40d1800d0151044800f400300080c4160159580c0e02d41c0103180b80c0e011220b80002801110300c170102d01e06c0000c00d440540310b00d9100c032400c1c11903910900481e040c04088c100e0350440c02c075615002c2e0a1081c45008030b80740d00790700010760388c0582210400344084040e28024003940310080780d0001c120514462030300104240390901d45600184841d0120398080a01700031846450014010400010440c038441291290390600c4042007031030059950272142d205860114a00300140710155100b162071601145000f00300703488207525180340d0046604215001d00611402d41e42004540c6407004103200100094401030861111980108900e5104440c0600c40050007001141c100401448990351002c005403c40b41003a94412a044047c401070104c07061264030b02d0310205034060049411016250070100180015000c03c507005031683c80140000c082200c1800f60140402899200d0b01001d00e80000114141c182c0b1002e42480000307038009681400703c2000148166212680 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 827270773 1250 827269523 827269577
    0x3120b19060f0903050d080103141b010e0d0b0c1b070609030f1502030403081609080c13021312030207140d060908090301090b0a0c11060a0e0715170601 67
    0x103001111002c022105031607240840e00000d001e0b00402e41c5144c0c03d9644aa003490480c0d000d100440c02d40e0f48249511603da002031015403400300e17065803100c81194011448030300005400b800d0b0303494030f48050312034010503041555842501940028100e80352080c0150303500c85100d0003005010001e01d4010042d01081c1c0b45d00c170040501ea010580c00e024010606082d00d0b40d0901500c0565030f92405d40703001019408100d442c118003100032100300340154807601d4000c05a40c01c520082910003916410844000d600c42c40003100d540d000c202d030001e240d9a60700e0b10310040036220036003c00000f1600d000307410098203400c200f46000d00c81d80c00d17140382c3d51180000c80d0038036000840018041c0a0307042c01000b9100706207500380c040d070914020501300041c5414991203040081e10401034104542801c650304042070007410803c0e80101d020030401466640070520005403003007103440490340d5644a02804503808000d41c04078090094645e018901840307960b5200b102480c001c0d4622841511440604010300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 827272023 1250 827270773 827270777
    0x40f091b2417040326010f0e09010216050609010f0b0907050711060f1c050108120a1e0c140105270111030a061805090a14150403120b1906 61
    0x1c1e8001d54014095605420880c091014112a0349882d003409840d6502c44958001c3d80f04070302c0c070400304024140c80d4041c10394440300400c441807460715011002102003e884148155801c02c015030510300d241d1800c1141a1040b40684582d20b0801501030856101480548a050a2001d0300c800755603100d81d00d0354884014205240c0350f00c81410203030b020445040c09603800041c0010400302082211004d040321803002c500841d281c56081d02c4090503107000784180d00b100c4e44400b821110810303c1d807010308a004182d01d03102c0e800e403030000c10aa209008441440001c03c013940301c001c00380551140f80c8010030741c0e2031b4020300c0b00d8108075101002c1c8070640049448100314290700d48807442c0003904a1040518110b40d4152a4244402e03800c0c01403d41307104030313a02a07406610411a69959004a501c00c0d01514007900002e220f907218901000803906603541d21340140c40924060104010110b8003c038041c2c1e40e00c4030103110009844044031102e012151088009041500d00011001200e5041d038141b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 827273273 1250 827272023 827272079
    0x6040506010b220803030a110f0d090213020403030e09090f10050703021b0102040f1a1c180308090c0604030b01140d15140c0c030a0e030c040f091b 65
    0x243d183c043c1d10341c1e0400004a401600100c002451134000010758090b6051140411030f0b5884690780d800c042c450190710703883d001410701406180131040d522803e141800a41201810758050304107000300c0e030164008401091013006800190304103002559844504040145048005000c1c0300d40e81b480250759020171a901d0b140011071032071107501500d02c0f071102d858071001c043c0c0710802103a0103074009008041c0c160b14112000100c1c540d50112050320080c110b4030b50703490308403641104c038400d00392895020203070390b200c4e50030210380354024a80b40d290500a9603110450304005d200741b41420304442c0c044d407240d0014402840892840c1c000035045a00e0902090141d64012020031007562900300041e00b00540700e00e6101c0000115000045890200c950919003aa20001501c0c0c407401441400400c0c0d52041c400c0341c00c05801480d0701c488060b07004044492f04040b0000040590300c0034681090380c00d48070125071040000c80c10b40030012150344805a050fa500301010448080010540382d8250000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 827274523 1250 827273273 827273287
    0x1311090405010e0706050408010c083115090209060f0117040204111b0f06040c1806170115300809060307050405011206150c230a050f06040506010b 65
    0x1d500c44143d400e018400e440d101c0e5582c91000e82180c2181c416003400c4e5003481800c02c1403030310034070f4050701c01c16000c41000d1401c42076062640001c0035100c0510342034405100d0401c0410784589172004c0e0902c100d5000300d650b000e20702c140800960080c103040d00540d2210304100043c1c0e0810200143d0b0b21840070307003007469940d0b400040c01514400710441c010351000a202000120300049402061801804880680140f901081c0e9102c000321400740c2030036000c0e1800e000b03000f0310500709058034861510200380c80c2d0b1605c600c0c03000c90703054043c407095580d96030006060100c1e05c0201540240207042c03070505020500c60451440d401c03405804105025002c80c401c0804c03071030b141070700c116400141845480e442d0086002c2c00c0c550041c0591404550b0035a00c440d007481c5c2501401c015940030305c01e1403c031900d82910564059aa1060840340eaa04582c0039806500421010f101c1c4408103000a110841c101c0c240b40b4208900d00011081d9900610100008254001a041d044030001c400d442c1e6540c02d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 827275773 1250 827274523 827274533
    0x115030903140c07051e0901120f020409060e06090f071a0306060c0a0b04030206070905090912090a05061c0c110304031e050303090106080606060a0e15090306160813110904 76
    0x40366410442d40850346e0f01c2403884403202d481008039082010b07900341040341d80f01c480c28103908000d0303000100085c0b000c800210043c201908140f1045204400c003041418402c0c0c8030031304040007181c217100d41e43d1141d8840100380b001082a07900900e4640380c0380800c0c0c11540070004c490303c001055580035110009410030b1001c000c2201b1051503400203044052810f01d850003e40f6a00191103040c0028049100440c4034640790600703500907050300340141140c14802114020326000f02d036801f039214425040000b81501d8820003403102081072081c0141c0d541682d20b200e8202c4040504403010041d281c0d14030951040c00200703c4d400d0f41d41203c5c0c0445405800460f12603044c01020004000d070101100340080048150044810707102c0c0202524240c1c0ea810090000c00d025815003200018031403c1d215015080511460400001c1d515080f0b1500f0291004a40b0304107080e00c40c06410810785804e40711642d4460415a044800c510b1030300c80c00c28080e107031084440b450300f0605210303114080118007000303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 827277023 1250 827275773 827275783
    0x2c06030a0c05070f06140f0106020a030f020c0a0b0304060c1112030a0213030f060c0f0c111201050708160906090b0306040b21190c15030905070b030115030903140c 72
    0x4d40c04041c02030700540915260000d018071100200581c1504130208000008008800c0d040c2c9000754001c02c07921186407011600156454901d50942c0035010b82401d035511095124000b5044c8002400c0d941d0030036180c04000c59114084150400646d621004c40b1500302040c441da1a9031100c0481d52a41c5031540c0b508000d00c100c55a40f000084802c00c000304018a240391407800074002c0008106d04e8141c4801070f90781da100c0c0f19840340090355440050001402041081140000240540641d102514200750031074105072581e5011400e0300040001c2030351a00c04600002c1e000c1e01d80381c0c10040c60200050104000d0f401091490381002c000601244c81daa8080702c2e002d034008227040c4040640000100301035507200c414141e64019801d460045601c0717440071401d00e2340c0c81a9609482c40c5048540514002181d00d108105a1280c5c1e2400104000b0896280034000c940c0c1803d42d607526020791503a02c448030924450a15083c14011008a9004188024903000f8844040e42e1068600d19040c148 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 827278273 1250 827277023 827277037
    0x201080415091202060f01030209060d0f0f0c05030616120c1b0321020c06010306110715061809120806030304081605090108030310050402070201110d2c06030a0c05 72
    0x180d868551070209000c100c03031003000409a144c080e601d444c0c4500d2440d015030720003404040d40004861000c6002c606000307201c841030382c5c00385403040b0002000b80c0d500041c00745000b00544a05c8200c1000303010500d018002c032600056003040351200e03010b4400b0040c007a0705e80302442640199030341e004080103c0c021a202140b00503040201c0044001a02d005080888181500000040809025404030b0f225100305d0700c0a000e036070000d080503841c540d1003d000e0810b8420300b00c8030942c03c0c4041d00006000e200320700001500748501056007410304962042881c080d188140f803260810003c0c0001c14003500c00342000c00b0080c9040b03a95680c0b03200100785588900d42c8541c049201e100340f500c0701d2400a101d0a400e403482110540a070ba640c07002040e80da80415112040700c4a2000c070104494540b5a008040c01481814040c601d101019416800e00c0321001828000c00d03024800940182e0340c20300040c03050f9101259407090041c0c03100100398107020007000c0040807613541140c004894014030940d003003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 827279523 1250 827278273 827278313
    0x171909080307020f01050114030a0f050703020a030f0201081303172e080c0a030206040b0a03060e07170702010c021b0a031b06110a0f060b150a0f0e040c080402010804 73
    0x14904001c0b000950350b2078034680700341c0340b54a032800100707000031466194508000f0041c0140340b104420344403003c0500604400b181d80340b00d80c6100000588036232600c08021805694032049001c51400094000013004202520072406040000300180c0c008840b0309007800e038209450403e981d584410340c1031b41141c0066070300b00004443c040100c200c550880300c007602c1c0701400f620303002d00d90750781404a110402e00001f54800d800b0700060106d41840e4014010b50fa10914011643c40d0fa07403440c5980d9000c003600e81d5000910301e442a900e02d10483d04546030481518030081011072480781000307440ea1300000c0e0b0640018030140c00100140e460000740c0c0050b40d00521400c020140901440f440c0b0f44c80d500c91440801d107817400c20760f000c2e0004185400311941040f04040c80f003c40e40c0c1c0b00b00080212000b043e83c80f125001036460f1001e40040604141c02d010744031803266082414000d03024a18400055101d1030419206541d9107501c80d1043e41c0241d420b00f42440c05031100d00c0d10351400101114580e81e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 827280773 1250 827279523 827279527
    0xf0c0c150a0c0318210210181b0312030b030c040c0f020f0106271e0c03060803040f140d06050c07020a170703080d140f01090c17190908 60
    0x2032110420b51041405100d592000c0102134441414010007411000f80a403401d50080501c00f903a8141201d9145810141e10503104600c40030f14080d0304443c9824038901541990504a00420003011801240112584248000c1030300d1960b807035001c0ca031580450b40400d915042a0700c5540c904203c0744c001020020f10620800034800d00c01002c60100000000c0184100140c40449072010300c200416241c00c18004821140400c1c03410440000c0d0456903040150307610aa140c92030302e80d45c00e0178032501c1140300204901114603002420f40700c0e00e80012145400806c400c10020722522004d204071001500d04a00d05031020001a503030f501565009403c00342000c04000c410510398000b4403915108550461070181c5a01002c9820350b401c0c0c0f00507501d5400f4110500201c1d0300c1c2009050411411034012898103280c420f0078007484e1b4240c400e40040542e2000500c079020142c004c03101549080d160402189101c040440480c070406032240e80556029815442d01d0540c540043c1d03821908400c0b556 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 827282023 1250 827280773 827280781
    0x906051c1202030f0c15010b03091b01110f060106031a09010509040606030f080d0f06060c142404020a050405060907050d020904110d06080105190f02120115020d080f0c0c15 76
    0x2e501c03012500741d51040380100706d0000c42c4450707070502076a000e21925030040c80103c03008021080040325850005041c800b511020b41088401080421402c5152001800d885c0d407506a014007a2a0100a1b00084010800011480d03440b4141c503181194011a0082c02649560801400a000343c0e00301500c944a00c102e810280311060009203140305a090042003004030700c820044c11203156008103000180c8031841d040101382c2c000041000c2c400400c0076541010103d52140d04490a80c08000059001c094208004c0d031401ca45a00014801036900b400b0625100000544281004090900f402008034ac0708000a0700396056038406000644108504c0745201502140b9800002c105103c290910401107104141030061502410000c199144032203522401134018051380028030117030980c2808141401c60420360201c0c0204500248556003d00e280c0b002402c001e086601c680074048610309001c01c048900407504e91002d0300c00c1d80242c9442c0c455440c6410181c00c076400403400e0f84141d00784 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 827283273 1250 827282023 827282047
    0x2071208030c0d0c0801030b0106050f070b060f090a1d0102030717070306080a030804150b030601050607140d1806050306030d03022d030a150b16050f030d02040906051c1202030f 78
    0x5e5050f280100643d100ca607030380360400c40e5180b0640c0014512240c040c0040d80010303104015058100c0c000500c165440e0303152a0200f02940c030b0440741300e01300580f50030360080040b0b003a607040d840316021301d4001d40c40d502c6d00c0c00c03016084488454444151481000c005000c07030b4400c1d44400060816401541d07181c08450800038003d030030585003503540c0507a41c50500501c8440c0d20440700c1d40d4a015000d4242a0300c0c140402c203030745d008072000742e0b401c01c1c07092000d03400a1401d00034900000d0340c645030740141117049500008104490341210007840800c20600003203070f5001a40e4000c1c000545001750740c942450454500754a45036820b40c00030009000003030314046107000a5441641c4404c4100300da04a16409810120014484c034002468200042c039900c90603980c1c014030480c02002210b242d403031402c0425107564403030050303c6003441e80840e01380050441402282c00a080c101c40444194a00510341050b085000c2001400304e4410801030b08014028015a80c2603a1803036011a2145400f901c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 827284523 1250 827283273 827283287
    0x21c1b06022b1403070302070b010306060611150f1314100e010903050d0b03150108010b040518030913060f03081c020708030f0907090515010f02071208030c0d0c 71
    0xc0c90098102140480c1034005100703110080d0040350b48203c1e881003000d036203014580c8060034850130141c0811820b000300c3c40c81d40a903802140305910016685150070720080c0b120f44508510410784d00b0250b130645501c0140360101e81c100401068680d1107803121650b00f81120111000201042d00b1940a8059031002184c0940d41400401c0c0c14400c0f440184446801c076403040f50b006000c00c03001e010034005528039501c015684d02c0c028007211381d0200005013030604c44072309901c070240f546e445500c141107a007458054260070800000040c501d403100f40040035224000c0c00c040f03134000c0d40c81d0100c880314980b440c1c0001c0010b1500d03081150400d5100d0030819000d5001c40c412520341650403200c03030349140f5a8401c4030303078094001c070740781d03055449030701c20120252806050400944075a400200c0c0c0011a80700b4140240041400c41402405100024040f04003441c2e00354159040b0b0360003004507110301e0303420b40915503002e040d442d03030f940d10540c150425008001840f0310003460181c41c0d480054000310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 827285773 1250 827284523 827284543
    0xf060e07090b0a0f2610180501030b04110321090901240f030b2101051501020613031709060106110610030204050a20091c021c1b0602 59
    0x10300d00030080c0d11080c0720b03450381c460750224400061025480c180903501c2114401d140c0b550424581e5240d0341d008450480c4071000341e13034028042c00580d03803c204000001100711802c0304504814401580b56803210100d5034070007000548150003400e40100a0350f410300c4400e80750781a088640e281750710008107409041d00810386450040014000100c1c141e408103042510b03100c1900c40b80ca030100200343c01200d041d040030200382c0038151245001500d03990382c03881040d005000c08a03a0911401d07451140c80c00e407540035189070340510711004410320701d0b41d020900a500c4199503000032404640c520742150382e4000f000082d02d0080b202420700547c8040422118129403207a603442e03c03800e8043c07a0742915050b065811200c00602610200014280740d0840d0f40d000c50140f1300014002e07680d03001045a2500d50b107170300102140000f05400b691600082c0c0c2950f541c811820040340e46056400f0a1241110342c659000c070481d900080000c20210500f480707100341071482040d003034688c0c17034a01954401d0307114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 827287023 1250 827285773 827285777
    0xc060403081509160e030a0507270513141002030a0212010e0c0405100e0310090201020f0c0a0e3103020111091f050c03040602030403020906040203280f060e07 70
    0x2c91494039160780d100340280c0380d444486800226071603043d6102c8010038403003038060040300b4038040841c0c0c00b0310001d001082003442014129a1050a520303082c2060780f10420766900d400c007480610001c00b100380c0da245900c00d0b0010108444000c4051525080100c8100c03500d000108000074002250040c0c0444140c00b11140309507621145001c101d244100d80000312044140002c112515102e0050240d035002401c04054031160903011038113080c6010700041c0b40341d4540030080d0440d40d0402184541426001c003038960b0b03000210000302004614810a0a0034139848045141d4a070b220441c400c03803108003500504802500d181d8480c80f400c040130282d006d940b0380240e0f1801d19041a08841200070024580d9043d09200c410042c00b21041002c00002c0120501608071400c104000800207440c0e503030015501d861a41c41004020500105614000c0d4010700134442d246140c51441042c04402030140800c80740c134451000010314103140a405950f00704500000c841c0d64200311517025500c80c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 827288273 1250 827287023 827287051
    0x816110303070813090902030a1119080c030d1e0c05010b04140f010b0702060307030f09021002030d0501050a03080702060c030702040501090507110d051803030d050412110a05030307080c0c06040308 87
    0x1421141781203601003c00a9090b0b00031106800010360580c00d06101400006d00d000f42c40d40181c444216174410302d8006254642c02069030400520301008001044a607518042200c6034010401e500c40d041c140b01540140400c080d2a0010404207400c018007110740a4020081d090040c44104a0f2000a032207003110120700100114140f000c640840f405590040d203014915100c61504070010038a00c0c0e501c01c1840d6540e04440b005039901e00800900f01c0c0640e0003181ca4034130480b80401114010707405107100e022401004c05c00140c6100c1070fa4001d64040701c41c5078581c0c1d0600b82e15419440340410003540940340c100046000041d690140b800f52030b10355241c852884101001503a20274801200c0c0020440a021926900764010350801080402400340c07401e08032001940e100350384d01550101c400b80502400703030303101035401401c1120304a01480101410019619007980360320002d46141d003008401e90000c0c4840000101b240c150484210858005150030308000f8000d040949a42c241380441c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 827289523 1250 827288273 827288279
    0x21032802120f0318060109240e01060c140f0106090c050924070203011b030c1b03050d0e0a050c010909060506031305010b090103050d020c04090816110303070813 71
    0x4009a495107841280200510308010749189030010340006221240410f074400c07816081602c2400468000d010000010134104030343e0f10964840805107140740c1d0791041001d0104030302e05103004914111081810311281c1d507a02400c010102080001c600c49151289200075040700ca01503020740111590250304024400d11584210340c2c2c2e03c1000840c0780c4c0100e01030004004076200001a00b51218410302e00f81c509035450780401d096808441c850001003900359003001c405c0f5014080d074101c4104c6498081c1d0000a00200759240081e1310388094200706000c10540400c01540e0711985030540d9640440b6100c401600d04582c2d24841505041d001403611100003030b40100c0b5000e214242c8200500e03060071039489a45008079501042c10640e104c0d0348480c8194042d8803884103007400781d0f02410107041d6a00c68040c02900e01200d8508460145181408100c0882c4150081c0c0300d160b42400020840a021401c183c503c3e8100346503516070600000450504124800c0000d00240401d0b241009240c0d80d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 827290773 1250 827289523 827289527
    0x20f07021207061d13150f1d070c0206070f0f0b010801020c070504051501030218060304120f050a050a180b0418060f0807030b0c070507060302040602010b0a03020f210328 75
    0x70100342290007021a54030740205e40300d190024100c0022120400c12083e548403e0749000200c2507002004000110020006828403841c1c003d41c07050340d50400e180304001c203030b01141541c450070034050101001e081100307040024800550f0b20356900310100042a5844a0301c042c000d600100448100d485000310008960800e405814403c1c8a512981000202402c4c010760281d841081c6801c3d41030f000e692500c2d00e41d5164006180198080c00703000c030382990080c00140600d20551000f40074860140a8070200642c040f0813542c0c849040c1c41c0c0046903a400c080306400c40c1196130440805044042000328440c0580404907246d0590b41f80c0034028039a8415440010000b03a000e0921b403900203160500100c0c9148542da5000400102c02900d0015151580e90510009410120000360000ad042020b15424003440407201000c035000e91046155500103001442000c85083c01038010919070031110074003a4480401c3d082c650107980c0e541c070311240092500802e443c0d0b9000301c200c680d0f0307036107070720034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 827292023 1250 827290773 827290817
    0xf0307170906070f0c03170c04050a1e03020409030318110f09060907052d0d061d150f0604030f0b1308030c0304020d150518030f0409020f0702120706 66
    0x507544c07a024058415580100c0c1c000b07200307080c280c09028a81c008420219080034000340702d005503002c8141c80314209400c200d1401c83c10f0b80114403000d505180c0c1d11042c01d21106100440e42d046030300081c01c104074542a40500f44044160410740e0001c850201030040040e6440448003040b40c1d0140010044800c208051740207491003504840900002120240190010221860029031410050400c1d25150b030707003d51644141d0314000c00110714905682ca007070044c500908407005940e074415041005050f0300300700c002c04245800201d22102c2c041c0d0f84528181410700c3c04042d0080f0740e0790740c41c0e040034a0036100c407190403070701c082c10320f80014a40d2904030804002c0300c2d4060043c038551340320800001c14580001d0010f9034051a81062540040c18062000034a1500c0030008995480d2500d049602c805c014408403d44da04100700b450041041d4800711030548050900041e2600244c2c0440c41d210b006145009412420203130301d9051008000ad0403c0c201c03141c1c1d81c1c940760319045609445400f4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 827293273 1250 827292023 827292031
    0x5010f060803160c2414070f03080c0f041d0f070912020609040e100b030102180d0c1d0906070e0f0108130606140f0609010c03080901020f0307170906 66
    0x70b410901c10600300b000081c404840c1a8004e100030840c09031121484500e244401742440d03c0d40d0221042024680c0c0c0001e96600341240c08405581444616111303503000e01010b8000400308407500d400607400c140307240162004101c02070a015140d54960f018100c0c05602400340f8000800321000068500aa1001c10f920561240e510300c1c444526044c0b0480856004401c100c0c0d100c8000e019886054480c0d114090b0b103407509400401c4e0502c075030524582103c0400b100756029900400c148152100f200d8084440701205440143e001c195030b040c000701c030040c03d4114485003d400308003500a65914400c482c002d0100f1000d550381502c2d4100251035a48000510541004d6070002c0000d0942c041d0000550010b6803c201e184001c5c060764412045071202d81044d01c0c0e100602210048505250b03c100d10902015100ca5290036880c1c40040d080c2101030800504012000000815800c0d003901035038181d0154135001d82d1203041440d0041c1400c3d6901c41042401e18007031000942c030310340000c1c502e801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 827294523 1250 827293273 827293289
    0x1a01051308011107110a06050909041a070509040e0f060106200d02030c0601120506010b1606050f150d050c040203100f03060c030f0203040f111c0b070f050a141606021605010f06 78
    0x15003e41241440b651503c002c1040e198a082190f0510603144601c68cd03600ca01c040d603490395980c010345030801080741c90002e00380003668801e0364010006540084c10740c0c103590305414002482c10820005004d20400a000c241c80b90003428600d4503120380003c003a0054804440554105a0301c0e400084211401d000015010354011001041602e40c042c0c01042c3e80101e4008a80813042c454135008103481c001d9a00c40b0090f28140b0400011503900c5002d2407040300110b8a203016641c45031180ea41d41e42c4246501c40c03042d43e0010204800c5801c01c00760300018013034500d001d00c889640e4140540100546280d0700c0c00b19042013109050551248200da1150741c0c03012801d085003020740c4440c0310001e581c40f90550081e0044c00ca01b401c0244149150300c4840c42090800002d24114074003c1c44862589100c4060060901032642c840c1d0f0400c240c19003007500c510310f09031900c000d50000c401e507105a08000d81340601c00210000074811802e103001d4254011402030007040300d10322800085039654402c88003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 827295773 1250 827294523 827294527
    0xa0b130219030b091c050f0f070c0509150d0210091d060f010f051215040906050a0c181a072003010e06060f150f0a0f0f02011a01051308011107110a0605 67
    0x401709005a01820300710402001c210706055480080299607482050241d40902d0360701001c1040340780c080c0f0300340d034440729500a00400000ea0b202042d01680d003101c00900c1400840400710a1500c03d101c0c0f18014071041d00b012a42140f06e0319101a10081520454003e0260320401121035008516544681d04917550390b518100e002c0d6544100309002811420011448a00204075552030380118500780e80259000603080c00e280d041e44045072504014402071000d10590703c2c5144048801c090112480c4210018000842c15401130340c4c1d2090f018010041201c84000c407012080c200142c4c1c080c8102603000301f1017980b10041440c0e49800c101d9405500001b01030f0410494144200b40c0807680f11034140c1c140c10030028050f00002c580044040340c0000d500703201900940c907448501019555000c1c0002c201d100191501c2c41040c0220501060500200007000d04807410f40b20821401000c100d070007000721b1680d00d80c42d00541c0e803003400256007282441558501d02c0c5407160414040303c81d41c2e21064 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 827297023 1250 827295773 827295823
    0xa02060708090d050d02010e07090501030c05060d0207021804030f030e03090d0507090e01020702010810120f030e090c0c070f262125050a0b130219030b09 68
    0x1c07005602080d01d09030040000c0350044005001085620a1407a8503000400c10200d500750007442c04c1c2466204112180c03c220040005c100c1102d8001e06844082c1ca89507a00c18580390030002912510304001d4010032404501c4400303581c03c816943c0034078801d039904104440c2c03558003182a64036985200c1d000360410800c1c030b461840c0000400c40828460b070262100b09a880321000d0450b1500e800710101650000303411011036074000800380d0310020030b8400400c0c89090240f00e0088140010004000541240020040c58040d009856903013a0050030380702c80749400d00e4013908c3c42c0c01a2480090038881c01201151496105014a09880c1022091131181011012000c0150414000f6a5403030046036003848148491301c0450b20383c26500815680e407110315440d81c4401e905e0f80522130184005580c90717280081d8000c2880d0785410707041102c0a42d0b94940703c0715004c10b1145030301c00951117400004420010b108a5010340c00b2280590b10120742542d0316005a07803142c020864914204450104807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 827298273 1250 827297023 827297033
    0x317090601051c06090c090b120309010804171605010b03034006020c0a0f03030e010c02031c03090606050907020607180e01080f0f030906040b3007030605030a020607 73
    0x302ea40b610000d40000e000000c80d11100e040f00d410b0441901d286050704000d000a001c1f5014000c5440e1007035901c940520b0304803540d5510303402a10501c0c0d040204c0030011a040c0020100407892450910031000c0d580c2c5003003c4051042502003070125a203500b0400a07029920700801070340c90f140307401c40a1240c1c0001d00d421910840c5d001ca40e074403601e24204507039039212a403400301e00d03c040c017820340003001c1d040411800c01c4036007011035008044d001c10ba0081400007039400481581c1c1c044007030034030845070310f10f5200207414010003c0c40880c4404690840c4203509505400c81e05500c0e014020403c280307510b03802400451041201d20314096884580441e01c1d80d4400c1c0811018003804450418085032141d0030000200c04c20f0f0b21a00d09035008a80c80b0324030000c00d104910349140680c000314030704200180422090300803449a8049207602103040c81c1d01c2031a5490503541c04584d45802a14410000351100c481c2400b61b0b04003000030b2034010081a54207000804002c01500209003500303100880e596 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 827299523 1250 827298273 827298289
    0x60311070807050a0501240806070f0f0201110d06051507080703080c0d1e2a050c071d04051207110f031c02010221010b040501030207050a0c08030304031709060105 72
    0xf2034042c8034001c84040824004e02c141c96010701c62104001041807000a40c4000c07000d550011031030b40d0044030522800c550002c030b820450810500f0034450302c04080070142c0c0100440c2d14988000200016000700ea8020303a40b20300e040e030303504561404440c007050008800e54016000018003580c4100301000c0864000c03140aa8000081d521140ca001131099070401560420b1313000c8100003020f0450702c40034514600480101404c0740c0390b11882400c4020303100965504c00e007107500900400003451203e00000744010805006141813070b814008070109025207003241100c09039254020095010000c1d0075400890307134030541007444400e003514154100100c202c1c11140c026803600c910071054070100f43c2c59408110309140c58000607114041c40040e10500d00503044008c205d1400e00b0018032038032025805850689900b031800584850680c603145140c00d81d520006814500a45400100480c0000041d0310a0b4400e0b0f035170220080e5142d0080f0518502903400c0d050b01e400c000011b015500300307140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 827300773 1250 827299523 827299537
    0x606010c0c03080c06070e03150105090606040306110a02010c0503040308280c0c02100e010210090c0e09030d0b0f0d120201110a0503010e090c0a170c1206040209010603110708 77
    0x740c0c0e5291aa66941d404105074040d4950b40c0b41c80d04542d040040d2950003031001101c82030150098544d81015184809940005010300da22408981c0f000c2000e64880d20140e80103941d000d10b08002040342d0722080811900920b1010006608140e07030315000510480580340030316415125401640c4403e06400f0703400c40c00c020441d20b02842800d43d90582d02c0300740984896060306072101208403c6038014400f4000030401510f00b4131280340a0b000b40344c1d0340015101c03a8421001400503032070020386003020041d14140c2c860b0000c498460148403000d04084003c00c0300c01a180d0040050120300300c10300001c03054013003d40da40448104552400f190489000380514802480000354040c41451207901c5c0d900001e845000103031000c001802114086510b00d41c1100c0c15600a0030031001e00000204280e0507401000700343c440b0810100d410042c10400d5482d401d00042998120300e5904487e607542e00000c5609074481d2503d44000244140640301e5007a103504800c014500d0308410b41c6800903640e010130 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 827302023 1250 827300773 827300783
    0x6061709010f32091b06090a060f08070f321c0525050a170a0507020c0f010e010c08040e0109060302030d170a05060609101e03020702030606010c 64
    0x85030400840b04500c2101c40c1c22207401c101c440643d80c480303110100391480600a200c0740d400c01c000e010b5680b44c0090513000604103a00516500240080411200d0181c3d15146810518441c1c01144180c1c000c3d00d0600c0d896110303035824a04c1d079500c60085441a030402d81b0f00c4013082c0d418010341d8910a070080784506c15a4604d48904420324500b9610b411540000090314a00e51905001255110b640c040c03950400f46111440c8c0b150308441d0001c00307070074520a043d00180030340002c086206d1402081c21910341c1e0078200598010b442c0c50880800501001c40b0104014011b076164030105142a9074aa88003090680d03d1074194440c100043d12010300b852000da0303001c4800e1100085840070315042e41d010307001c0f40c0d8011482c5855881450325001045d8841390902c081c03411051004600105019031144210303001255a403180760204100e40302c1d203000e075a04080110f104040854011014405640d480f03550080806503803c2e00702d00301e002e20503000798107400210200d40a5071089098820301c600030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 827303273 1250 827302023 827302031
    0xc0c17190e04060e040506130f05010f090606050108090a031101020f04080f12030705251a0106090b0405031005090705030a060902010306060809060a0903020f0f16090606170901 78
    0x804451089844010034100001e0007901d07a004007801c20740181d0008200d428050495414540d4815889403401845410ba1013000401e030001d1206141c1a40c5106030410001c0150f1103000d00c440018107940b10701900c17400d0409000051070351080c0703640d074405d001400241c085e100b440c1d502110030340c02d460003440c42503409002014141c210704004000070300c03400004001811b4034100541c1020303400c51b601d651500c0309108201086800208035512a480d11103003060400c240300780c0e084002000c25010380002056450115400321130f030705803030690340107440750118155038131b03445c9251b4071881c02002e415810042140107040e56680095422100702d8060354030058640000c01e240100702c0505840c1ca1307445240d0070065503054420003000c0e00c030500d442c0031b6510344500c000c0d9503035001400118940f603495120754103043c0301703000d0441a69251001e4031020403070300301416035030010712003206000201e080c00041e94013814030444080399156101c50f081c1034001e4600780400100103000409035521 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 827304523 1250 827303273 827303287
    0x160e100e1203090411030c0a180306020a030203060a090507140d0608030c07090c08100e07020109060216030809010203060d021203071a16170112030903140102040e0a0c0c17 76
    0x1d086070300359200400000554461060034108829110310020070b0400001c10001c1c03101002101044524a50550074500d42c0c0115104042c050305099600c0584005d00c041b401106865040c3c00460240c0f0013280e072002c0f05900d40300f035130b021180f068070014045034910520300314002c0f0450242070350703210081002030510355440c03041e4115440a070781e500103500141000d02803c1410300c00e0b0102c02081d031a113103005250140404854907054080c1d5840007100c1000035a901c0d201b50407607261680d12220039921124440e2071074240004134081200421601000140c8444051003901e00c510001020014044074540900c030300c0c1451030400186a0000b0070004010030036078600700c2c000c01c42141c1d0202603440c20058902d0210319400d440782c100000d4401d40000d207a40c1011f058151000c80070101c84a200c0c928085e00e1f038200b260300040010f01c5002d0960030f0907c0c1036019104840701c4600b080060780d100c0c071034038049400e2065050003103000302d0311007400b013040786007042195250920842d1501071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 827305773 1250 827304523 827304529
    0xa260304030501150f122d080a030606080f040f080423090619090e030d09050303041e0807060f0e0f01050103030207080a0503040513090f05030909160e100e 69
    0x80181c00c1920345039103d500d035569041c41024850700800c2110f10610f150b82c1400800f811280403418060213a41001080140d201c4c24505812407501d000400c0d100040c5103450316100030f41280085001003441c00030300041c0d05015072040c80c45031811000191042d5200e82d9111003440400c801074414020521000c2400c481c5a405400154420040441050440ca041041d40070005100030b015541c036000006048030305650b070038180c40030540042000090184050f16500400c2c451300b40f658100100201030200100043d4066402409803140100004e0b00c1005000c00d04000100b650408000c03601c0400c00a50184480f0f8035540b02c003260813000da0320001d241c44085441900e551750760304010000c141e0100940300c000d0140c1000341c075019a45441c1d0580380e000e644502c1c0d00130014011048841c4041d076010320700b100d80c0800ea0700c03444140f5040190741ea030003001499015581c0600071034400501d8401242c025520340e9180c00d041208c4800780700800c03800c1014070060000c00094541155 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 827307023 1250 827305773 827305777
    0x61d01150e03030f0316111b120a1a0601090f15021203180607020c01120b030a140d030b22020d060509190b0f0d02060c2b18050a2603 59
    0x80e14070903401761241000d48414503a155004204410700101e40940e0038910001b0070740c1c0a994088544030b074640c6554401080c484260075041c0300c01400f41056010401205a25110700003002090007041030755820015500c1c9945402814125403580404101a800c96111040d54240b5441a9480003010303c01144441d0000e40c0d43c1d00050601e162840c51b002c000300605a48016a072009150642d100b5001800e43c206100e8454042502c5616400043d01c0400100920544c80003500c410b40c40405030346905c90329404541300001c4c0c01d186441c05240b4002c2002c4c442c940100e03449445282180c0c01d000020b600078110f88210a841d0100000c0c0b9956142a01d88034950048000004034211050316080350200e0111500c03e440ba070307000010303035250400305007410b5506070b450654809007040120300d40071030585200070b1750380b0342c10860100f02250519400030b00c0c11622680c0c64403929100d092400001801960342046140100300074800c02c818051100303135101110040c0481c000184d490444e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 827308273 1250 827307023 827307037
    0x204060509030c0a050906040f11180108010b03010501020d0e1906030203100e0906060603070c050303071d1e1e1903021825030b04140a061d01150e0303 67
    0x1080380030486186a04081c4802810014221510f640060401c000034001e02d601400310340c0202e98070005513000d4103540c2c2c800c01c1a40203c0c0d00e4252510100c01640884d0280001d9140c00034541b840002521403664081e03034180c0f00305801a00c110043e905084441d034114800d51a4811804400c1c445c1e1072940d01050000703895183d03005681c80c5090040d8030f0310242960b20000310b0858000030003108a46c0415442c1e003103842219040d82d6620b90720811140c4050300d86000e002c0340000001e02c41400d400c18450f0f000c4002180b080c0702601802810440c094a10340c10101941c0184105008545418608100f1048450030810003a9800e400031585c034040414900003034026400c418000d601d48441006c0039003510000c1d0039400d140404203c940c030242c0c0003070b04c00030103042c0038047d4842e070107600040d0480c3c80141c0200101c03803801201da5000070003503c40b070441e140760075404a040205214128540c8030050b174001e1032646001c503040700031072042c400e40080140311355282c4020b9505000400c03003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 827309523 1250 827308273 827308277
    0xe0a050c09060a12060606020c1002070317070c080304050114070b04020f03030d02070b0907080d05070b0403120c02100c03020a0207030f0c0b0424020309090601030f0f0608030c1501030b0c0a03020409020406 91
    0x11b07070304010000c4d00d842080c03956a4851002c0b0141403001e9680094a0f409072079000c035a01d030940c6116800741241d80a0000d0080890f1481000402d120100002a2085a409036a0040c0d0120b1078902c1d0034081c800c10030094015107018001901500b00304401d89014100a011249003000c54540c0310126000342001f141d003400c1100c14811140020820080508031141c0034100454240001030302d5841602d50091610041c04000340c00d16020304081d02c0c003003030351120900a0341c61100000b901d0380300341c4074400b072058901010ba5000c10722034801c0d0380c001101500200402420b5071075442800103003c00c222150507984401250b0090014044d20080050392600c0c40003c7c07503804401140592044402c003154010301c042079141d9101040c040c2c01000038240081d01d015241701c01c1d0b010301044c4a903203500c0e505049000843c00c00010040c0b01040b21002074407220700f801c4e1340c121000c1d2070070f2101900850a80e000314480c5012100200000051070070018a0b00d82e952956034180c2c0c002e9800100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 827310773 1250 827309523 827309531
    0x1120c121a19020d0c1d0904031b081207020610030b01061b02060a032f030a0c020109060c09230a1a13060905091501080a0f060911030108010e0a050c09060a1206 71
    0x480c070307401040502c02d1b00540b0040d50b06000480b0040313046c01c00020405020080b00314840c441c8060300e00c5820318029001008580e40c0c4449501e00080110301340c490034014403858000640096003503540c401900e43c0b0100c004c1084e482e1400489038411200072031501da0000c50451030050340d960000384482d0400b03403004101b01102d04950041d2013540041074102407c41d212001220403540100c0381c2c080402000001d42c040c0070b800490060114007401040a840c00c8040c060480e04400550210766483c0c8204080c2c0f0540c000800398088132110b12074102d80c40b050f080c080014054030480783c5200303a99400341440c0310074642495190040e03000c46d0120714010701c240001d06248049542c88409211800e25a61074200001c207203a100034201c92115035241521503603a01141c02c90002400204400d2004c0408003010056176402031160030855803801021310700501e40459990706164221000d4480f00c02160140030b05088002d06890303100343e8100c0c3c040703401e165080b84240181e00a2000003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 827312023 1250 827310773 827310791
    0xe010609021b07060f05040527090105060916120203130b01151d0d14160602010b0f01090e0c090d0f080307021006290c0601120c121a19020d 62
    0xb40c01c00320f498104404201007014444240ca80100480c0e0480d2003d544070344103526196410060000c40411520001040708248401094150406409000100c2d1400701e1a107802001c404811000b28161021420050144c0c0603e049603025560143c0081d00d60b000322400b40d601c0804282c000d030041881208002104400258030214001d82410f424004020f41601000021121b1524107001005281c50040254640c00148020500d906040b20103070f004944901004e80600340e0101ca1900a07094800034050562103280c500e02114a24565100c450300c0340381821031560300265031560000c550400503400100203000e400700705070041004ca80c80f410011402410000403079220030f42c05081c01014000404104a54005170061b404111000804000d0017107041c0542e81144455002e00000001c1546141c4044041284a0018134202544501c080c2c01d644d51664006002204c803100c451400d001886072094100358408403004800740100c403600c069074803c031402c1e070546480300780366 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 827313273 1250 827312023 827312077
    0x20a0e071205040804030602090f10020a0b1609050d1103071214010912050c0f07031407060f050f0a021c27030b0601051e07050601210f0201030e01060902 68
    0x44001201e4026007484075007000e4588036120300841c000982540e40c0041c091011703585100031031103114170103001c00c0400644000080d403208140031042c1c400316030000001e225011108224040343e89292200c1c0d642d42e00340301c10b12860900607002261a860441c006500e2aa0100074038030081c40000904e00600d0058079241400800d02540000143e040a0501c00001c0515404002d03ca0782890b01d5501d4902296031b441c9000e0040e1110507050140b0400401840850720b4078914040800c2d00711403540369555822071700d405080201d0400141e0074070242801696403c010510601984122410005503040c1c60490450b6200d4800104141d03000d43da4050307200100507031840010482c5038400701d1035515029003450b40101010f040000c0091500203507901c0800c1100710040003242551200c00740d1411300d0f03440b102805402503c80400c5900d5980d40560b80114075402e900c22500450340c03100b0f0b0b005501518141044403200c0d500da05010442c400b043c4050301d16410f00050441e60300c0e00c00414 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 827314523 1250 827313273 827313287
    0xd110a09050f1e01030204030b0c0a11030c0d05090411030a050a0b0a0819050a05030a182c1909050304150302092d100f020f0c01090308030c07020a0e07 67
    0x3a80185110500b90761181e50b02c0d4000303014880300c1103841c4156111240124020706c140d80005056401c1c0c2802d0180001c1c955015143c5420030791641e090001000c1c0f010b81e580e000d0452140c1040d40200350740e0081d1031040703000c0c200c411005040841d604072100014061500101c90441e000c40d0b5804c200030f203412541c041c040003004180d40d483c051a040843c150780301c003110044544023189084d202c3c000c11030104101da040b11b4000099035116844000c1c01424035500b00301ea410a00a11312010440b500400c0780074040107103c3c0c000e10003109074010718060304240108403030b030380c0a01d00180f440040081c0c041d50021501c02e00207103030707100e0500c2c0c0869481312200002d901050302c14800002640c540c0016030748180c4811034290610910310210196a1700c211809503082030b64040120711094201c44d44000185c080d40036207502c1340d02206840c2d070340c40303400c021507000900042c003c201003000000110341211104180314070b800c8090300070443c140041da2016190301108010041001d84c0486 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 827315773 1250 827314523 827314529
    0x6060112021c021e1629040b07020f010c120614090403140403151b0206150d030905030d0c051203010f1a0706140612010e0706030507050d110a09 64
    0x40c0450800ca0b00d00441c1c055412898401820903500284a88207550040b003442e40000310711800300d43d512801c80d440c195000080c2c20485400c17009400c000d2440d069025041d18201505e01c8002140c1e44644071803040caa03001c0c110005600401240d164840000c2c099098421110344800582d03014508040701110400d0b80140700d500004e2580368501e80d00c1441c0150000d0b01403800903100300490300000200d00c1558401803041c2c1c58a0700d1150007105503042a40e4200d0030098949200e88504001c1c0c3c3c803003500300d4231018060035801c07440c89586060fa81a00590b1700030318000a2507506c41012902d8070381892210000300e0441104601002005c101e88400c0ea6454910f44c0e080d5490f160828540c50203d01030f5094a881c25000700100c640e0700d0341a1001c0e00c0e0012030034801c5003035600c156400001d007942c41a014180b1030013500d48010050041c03010340111030009040140ca403400480007400040c00080070080100001031080025005041a4911409030030b035a03400003100141031211158 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 827317023 1250 827315773 827315807
    0xe06030f060906061909060f0509010215101205060a0b0307080d1218060b130c1b08040503030f090a05090f0a050606130b0c0d03050103150902040914060601 69
    0x3080010480d500e00c0503000401034406181c5600c03103030300062950207902080144060380d40c41070348001d40d10910301011140300f034407286014008044107d0b018400e8403000c601507404800c1c400c0001000c494107690056000542c11041e0780c642c4030070a1070503004207055850b94000b4051140b1003c0c03d11a42240d041d0850050a1003480d050b039003500c429501d0703032100612043c000190303002d01403500b00d0035141c6031042e007031003105259140280007402e0100b1450301403140d441e56804100ca0a201d01c807070642c81604c40c1c482072010740000300b045a04280c03080b508000c0a0200241c0c41e14100044e0030f98402402c803994440076114284017110307106038051fa1198000c04140041040d1215030107410006408012406554010104100b4825800d00f120708880055000030b61048110242150440035000d642c44d0003c04081141620403e00002c1c05420100300e003501c1000160b80b00078080b91025002141c00d08a985511b00007040b84582d46007990080c40c100100c9690049a00304003005007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 827318273 1250 827317023 827317027
    0x40f060b13090c0215071704050d120b060715140c030103210c02040b0109031403040801060b07210332060409080d0b030a02041a01120209060f0a1106160e06 69
    0xc1c2c00035510800c5e200000c010131180310200300b4191041841540d94043e8400c0b100d0641010f20309540c1d9030304400510800110750710303800520500280a07002c0041001403107541400100e880c0c4030200070021074101c11540d50340c5030220000329034641d103604c6400c0004006840e5859420302814907140c1400300c0c196031140c410101c0840d50026110301d910350b019030703000a004200781c1c01650081c4c200e4001500c88820169001200c600010081040d1007020000744107807a5503401c0c242d164094640014141403603a00d22031414425400d6513680c0030310624012641e240c45620a0324210f80390205607541440402c0540103a40030030f0f840c40c1e00040240c0c0c04200b9071010740c84400f000d01034070321032968a50320b403420110320765010800789a000e42c00400400440403010b0203c0d0143c10002e0303249010800743c0302c014011100314401c0e82d05440000c0c00080c94550340c02581c47c036640c01000e10800b1302050102000c400107040025600c280c4418500d28100a040100030b05107020030fa0781141316441c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 827319523 1250 827318273 827318291
    0x307060f112a120703050706080402040f06080c031902060a03020c031204080a0e01020a0c0308031305100b030715051c0e010c0207050319021c060b131b080f0f0402040f060b1309 78
    0x1c0080c00004230391091614000507101c0d8400a0003500000704490241420060023056845010401501880c800c90488081400720196400b185044c80400b039030020040c0101d014041c06500200008480d020070f803860680ca000c1d10b041c0c0d4201c145c1d01503034006030100310840b9041d085022048100424001809004d2980d40ca410b071408482c000142404c00201c04070b168164141d449070350a40c0c0c00303420348500740b1b1681c03042001042d80040340ca121b0701c40c031031000030406215000341514040315940d80e860200d802101400c1c00104040380294641d0342c45152011040a01c504040307004158054946249800101890002c421400e05072005445060b0001656211490910859400000c10308003007a03051030741c000c2000a5003070303820a02040a189003413440b54040d03504500d040e0100319042240340e5044894600888402407500b00344c0d000b281228101d108041da000d07200800100da0400305000040a81d1000e0380b2041051102050807000c4e030704e08000a201900c0c181100f0042082 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 827320773 1250 827319523 827319533
    0x3040303170910090602040503031804050a0912050310150804050106050a0b040501030905190c060206010b070b070c050a05030d060512120301030b130606030b0a0b0307060f112a120703 81
    0x40f01c101c0124660f503191010300402403550141c4000b040c000701980e49508910402c100c40c0145121540d20035450440000c007819014498031840343d030003031230400741d0410302e6009603456030000c0c01a60440390101b000003007118507003030031034107001541e55146a2420a4544035007540c0183c0c00c19840781d00142411b00c82d8040410aa9044601c00d1801080d0700055040890401a00c03900c4600c141101e689002c0c2402512000d45085548070b0342240d04603130f41d844841d11309010742c40004100c03a1001012801e040d21800031075880c240a0000c0d202400140d64406186030311200050f01d1080d00d03a0401c02182c5000315892860040d58806461074104640307032900d1a2105010041c4001056004201c1c480e0245600c000180d9024204101031612070801c001e20071f0b42103441000450620b50a80322a040201d5240125a52030310b0303603d0510100c003030039503040c9882c01031a1540d20030301e5006a004000d0041044983c050303448210303450746005040c0059520b001090340350542c0300070001c0000031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 827322023 1250 827320773 827320783
    0x12031602011d09070507210503160908010e0c010f0f0e060f0d1a0a081c1b05010207390603020a050f03180c15090d060608030706050f0a181707020a0305030403031709 73
    0x1490b030700002403492b180d680300f42e40f00002e82d00309090540c41d203100600040c100258000100609882d402d552a0f9040703000c603143c0e0b0104411a002a0301c0c100300588505099002e804080030044070741b414034003031590a00845040c00307902161043d903401030307462900340801030402500300340c006010410540011041c0410f2030850620800120014a0004c862002000c580c0c666021000755610302c95030524031420f59080c1407042c0381d442800d01d0320800150381c103100509024894060a0018900a81074009400158035101404000c0010208500c1244000c500c1040e8490a000d007110034600a076203080c0e49174103414000c1c00d0032803400500e469580e0540703403818402c03155120100628605000035010b02c2d0302014083c8004a5041c0c00c0180680000b0700c15804144a84000c2e56620008016110548401c10b0381c41c02494207c8041480003c08038941c641c041301152800c0700a6010030010080c6500a80f1907410109050080540c000c171111501b2041d0b0004c078030b541c03c21010b650340314 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 827323273 1250 827322023 827322031
    0x605072a020117090105090c0406060c021306120c15020c060409051b0705061602070506040e060a0e01030305071a160c0302100507090512031602011d09070507210503 73
    0x510103440141168860055000c00c07050210000d01e01d07007000c0d06200d001e0182503a24200da070207030400b14042418507100b40b1080740c0c0c01d650345090900458081c401e68095860040c4c1c80301e81c0f01d1402103524030307240d01529895031107403030b80400091400b180307203800a84050b4080119041440084002e5683c0b905035070030340e40c66082c002910303200d070008020038031a40c0000b008000f80108140d0700303028000c1203142c13185c0a00d521150301c1659042c070481c1c58201d00c0c0101640400180814070007a032140c01d800340e000e0700c041c0000301406d880b01003103400301e4001da02c01c90004400096084c00c0195458207014000c0c16218003829a003400048095452040200d00080001916403041414405c00c43c2200e4071505050403c094180240c004000b19541e000f0203010f0f088248183d5002c98000084940d00022819002440c00d825801110800e4104820107076001e00b02d8003005950362901c012501420040d2281907860040345815810401030500e440d0008622951001400b50040701300c80d80 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 827324523 1250 827323273 827323337
    0x10e06072103090209130b0f010605040b0a0509030a0c15050c07031403090901240c080909090313060c0b0c0702090402091e090309190b0703050703030608030d09060507 74
    0x1c140c01501c41240209240310b40030703520188500c00d110340e101015200c1c400880c01030250300c40b190343d9101a140101001c1c0328043c0003540c20031040008a011002402c0da020680c94010314184656001a00d011513004040c0d40c80e51711200c08100c00c0100d1000041d000c080350601c83d0030a0510440a40c480707010b44005842561046d12036902c0c29000d0080f12000c40300103041d60b5495031a80d60034001ca43e414048561102c1d00340c1c030302d543c1d0300c0e0042158103410b940c8006414900f09076001804040200905254201d10050002400410030098000c0103448181da0701c0c514800705062254071680e000e404152082010010507004d6240c1900041d4081d40613503c80820ba2110034204042a0b10344024903120718002044c046414008801400141030407035040b1010b44511054003445090f52240402d0a6010441507000900407005011054042e06001901035940d40155007545d0180307403ca00d0655454003040b04100391071103030a03001901460301c0800b6400301115243e100c8121070030841 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 827325773 1250 827324523 827324573
    0x70f02040603080705010c0f0c2001110a03050901021605010f08040c0b070807110306070f0e0411040806180303060f0402090a1a03070305280c12020315010e0607 71
    0x9544654008800555120302440d0390303a151420a10f0081807040360250005012001d512171841c810b8101c50040794224000000c3c1c800341e190369451078400071105605000c441c00a60445210a004c8907070031501079180d084d6100345107400203081045005000079402c050620030b02890b43e1000803240c0d06200d80c1007030703403140d00c0700d0a01c101e01c05100d5101c0c0c0712034540043c0c21000c2110702c10103041d11a2248080007050245541019100c900c21138080c40080c05000480b003071684503403019005610081c1c80041c1c1580301c00800310031079115400c5800302e03511034400e2014810788504000c1d201110000a1411824000e000036074104549403160f1207250042203460325031b40c3e0006144020011245104200d4841d0940f80c5400d8004446100100e854440050b024051031400000d5005200900076401101860440c0040000f03003080380030050403601003440300ca5640300450191140b1114151500300d1b11000601d1a1350b43c80101d03008035000d000c4000080c68580d050072400c251400241 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 827327023 1250 827325773 827325803
    0x2103040809031c0905030111030c1207050705010924050103080f070c0b03010330080f07122c1501140d05100b0a090519050a090b1006032007 62
    0x64945600da40e4480707403c0e601c4040401a241e003118001c811a8410b4000340030b596194a00291140012540c103c40144200611107c4c0550188440d038030042e1810803038101070294481c0e9085400b000e60403100c002100700031005583c010050b0703051034020501c041c4140d60643d95050a64080d040440c9403683c00800c0e1842080a80c0c000800504824500c42d9200d60392800c0c2a0203007040204580604150007040400707404158220582801c406c0e154501203031180c42400080000082041c020415507844a010502c2e882c020921080b00403004d078600c198441441e1100d814401814000c954000718488101c0b40d84000d0a9044411860b030901c69103005402290f0003c8004070000c3c800e00030b040400201c20015030040840d080251000014241c07501108001c6803401d46d2074003e001d0382da080032004401560001a8003011004000c80c1130780e0700d60b90b1613181c2c00c0c058944210007003803003409010031503040c4038101c03000710060041203807002c595901e40058418003402400c1d0100e032a85072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 827328273 1250 827327023 827327029
    0x40c0e06010203160606061119030c020429010225031205070506010f0f1203200705031209090708100611150a02180f18041e0b04052103040809 63
    0x2c0d034081130684048003207690385890200b00826950207924042002d00300e1a120602c4000341c1244e004989490074104030300341c2d071000c0c1c5103410200307400c0341c5c0b094a40e040d80001c3c580d0b1422000d030a41c1d501010007540c1c00340700000390911007141e131250740304244400004040d4058180d030f0720440380c01901510001c80c031614103d0f050b00c1031101c083d080d4454a000000d50a4021418504965011000c080c1d00c070b0b1103900c288529090f90001030009510700180611503d008540c024002089408507148a03545e080803d040020508421701c64003c0810700d8030312810481c0716550701008514014600f8607103503450403402d98081c01104200035a449011400450030800c1440d52418180c00094500c0c10000c01c101075031003c4500390041c7c540340c1d0108164100b4181151400000901d800e00b0410007109806503010000c00642d80c0000c2031900052a03003c40307020241060291300c00c07908a140c241480c500e0490142103104040003880c07002200c0642407010360b5009984591a01d0780d0315004400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 827329523 1250 827328273 827328277
    0x302030a02210f0106090f1e090501080a110d05071503021e04082a0103020717040b030402120a030507080309240a180c0b0903030d0e0a0605010b03040c0e06010203 72
    0x520405445020b141c20000d0016011580c4252030300301c3d5076030f10760380c80300030417070f0000c201e417161000c0c0198009050214140407114510345500c01032000d40681d81d14000c00e015a0400c1e4800122604010002070600c45180300c098007409081e94000d44c00e5000340c3e18203944100c1849001080c2920484e12070609220313804440800e2481d0b080059482c40d04943c140300e0f607010b407240e400b45100c0c951040050103da1941020a1550360000103c85a2a54015400380d4000740088484a00c212250786400e505000a440940b180a1040d902c9180600c10302076500400702007115164400b40c42000007a9001d0200c03808298049511030300d07502d0790320b5058501007012138180c008070f4054007901c40c0010a050100c0c03080c01282418800381007040260080d00561000241c08801d80d0441484111943c01c0200440d16000c0c089a1410b120002c0c0102141c00324210001c498014000580900c020340c000c0c40d01400307181d00c0301032940c00c3c55550129504054402c0c0c1d0701d06044030002400d0340c3e00a2003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 827330773 1250 827329523 827329537
    0x6090f040b060d05070e01110a0c05190f0e07030605060f0901140c010f05091011270904050c03240f0604020d0207030924020a0b06030a0f03050903060601031b0302030a02 75
    0x80d0030311150170025406402c2010b000030045c00505007074820302407031500149800d02c4a0300078121102a81c24101404422100c404d9000c4a10440d21000682070f10500c0e6440b000b8079012900101ca81040d5000400f907403001d40c003507441060140721a201741c2a004c02100d5640200342003500d9004440c030b02c400c0e1365002d240c01ca15a0740d440c05c00f60f00078840841d04228883e56019060b11030801d955201d80c801c446a615444175925014004a060551074041d40211a1840c5481e0300481c446e500001c0c0d240081120200c030f031034004001e45c92290404005c03000a45602d891403007101040481d000b0000d28000b45640d0002d5844004182e041d21580d04803240119425000d42d03580b20740d41409422041a803081840c0707400d810045100c8c50005070900d410300d424035800703080020107680394805008005803030f0b03136414028083c0c100c0c0002d900c1c0e1811407030309220b9200c030307038446030640205824803100030412418141000c494001d01c00740c50320a4201400d1500300181c40742c8075050424000d015901e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 827332023 1250 827330773 827330797
    0x30b1302190909030e030f0705040908070210050a030c030204050d031b020901060e120708120a260406050603010c050a120902130921020d080424021806090f040b06 72
    0x7880810021081d402400d001806925603d40e0b103100071060640d00c800e00d46001100343c02080d801e000c1f910f000c1c2c2002070090700a4110509051243d00001c2121140c04031200210350002240c403501b47e054051802003c19504045041078600800b081e5806100030f001401c00081e15058044118a41c84054030302da006400001c65684429000e441c5403041258107204941d10400b842c140c402c0050200c05590100380a011940310400240c0501d420040020382841502c00701414440480e0200500c0003080c00c0d941d1030a401d088c1410000c4400140405000c0c3c0d04050001117400d03000021912040502c1c17610003074990081850340000c5c005600000c1d0301c1305000e52002015200741d0401c0307500c0342c0125800c942c203004130344400c0386c502d85115000c009a004043c1d0904080d001d5040c00740d020b40901c2c801d000b42200340c840800106102804100c103640d0204452050030704070703c6140710a400568200745080004000980e01100d6130031018800c0d03464910000890319072009a442c0ca2500c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 827333273 1250 827332023 827332069
    0x507140703050d06082d07031106120a140f060a050108100503120d05130309030b06060906030f0403020f070303080f311104180605090c1c1b030b1302 66
    0x50042c9078445d041c682080c0c0d200f150440107a60354019105001d111151244010a1403c8c42d542d601003100c000c0d042c440c2d500c008180100000205600f010360b10556004000107819015000a0035440001422001c1c410140c24100103194665001800503942e0908104099560b115480110a42a9008260980680400210000c0348400640130362b10362040701303011998034040441034800b040007018001581d803002c10004a04030704030f110341225018084c9450034a01c1d01c0810020350056541d0081d101060040009140d41070140302e00c42c6107554040c001540c50f68400900f4044041c0c9200740500300c1c8000301da041024040c405c12040ca25100314a10005000002c40304040101d0003a40c49841018407001c0524080c81f40c105902c6828030a140f0201c2c1ca51203500003000300400c00c4d5541c1c411400715007000e9480740c040c9400c6401d5002d8a0310401900c2ca4014800004d2000c0c030708030b40d0000001031000030700c0c242c88954408498070006503250031a000180a01e00000442c95600603c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 827334523 1250 827333273 827333279
    0x3051c0f0e0604050609150406021e1c0e030913050a0b0d121818240f06020c1c1b1e05040513020102060a0b120627010507140703050d06 60
    0x30031140c3c0304a0040303040d5003450362442c1450746c941241d10100c0306c200c0d00703100c00140010841c3e40984181d806004650240000c0c0001006e6250700400c030136550710700104203419060080307000701c0b4501e403803510203141400d0380140801d80c0d661001582e4490300c0e49590015816000c15840070020420003081805815514200700300010041140b0340000b805980105c012140f4060382941210f002c480c13110381c0381c40c4141c2d1a20041401000500301c00d43d11031500000d0101c004200b1028202c01c0c49529981454400064038003500624400d001c1e040d8025a580c10742001d01c8285141d80e00039085a04070003552480c00d0241c601c0f604483e000440541c44502603420000f14001641d034291000c10064a484c1d64000d00d003008544000e00680c4004009503a254a030380000c19907481c094401d0150340080303480344c0c0c01c00b90200c40001380280c0007a44886214103145106050b02805c0c07008000c1800c00740030080001152410701030f01c0306c1d00000c900e002c161061080f00c0ba0503100c1c0c0401c01c0300a0b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 827335773 1250 827334523 827334551
    0x4020c060f16030501060503070c05150115090603230702030d1104030c05030a0213021309020c0d1701080304290a0e12030c0c3a02090f010303051c0f 66
    0x28040d95850b010380701d282c00160440b40284101da069035282d44a00303081da510b00508460b1200e00c144111030310701500304800b15400d05210864080c001361402407018240321540289a00c007264001010141080b580750000e000306443c006034880c503500821310030f0780d80f00b0090340303584030300e42402280910382031500d0b65609803c0050419a80325201d028580c580d0f030000c040d60303541010300c080d40c08041e54804009402c4c15900800522888124000c000c60355004400102d800c03000d060000e64014441004200707911070b007210081d80740700041d1002075040003c02e582e139005a01403140d01c10f20844603500418030080765009290007081000390350700c2460400400b080441404a0b0207942c1a1002d1386c5901804070a0355444e0b24080018000003c40c08200110a201941210408480c0138100b9a14641d43d10006441c415950024980c2c0e04a07841440191000207007440d00385081d400052002a50040c105c0b02040c0806282510280c15090040010010b058011271820b00d0070035840c03480340c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 827337023 1250 827335773 827335801
    0x207020306070c1515080703050105010f09200f0f040b0a0306062a0c030506010b180d0c150e0603070e1201060302030d050c031e04050f0a060203090f04020c06 70
    0x28425000e841c4191115402680c0c10042c140c80184a000d103116521528010f41d4000d165102c2c000c114001072691301c980e401d0519115030005e43c0d00f40d440d100180401403004000d24000e1030840d1040007a51a401c1c40030012108400b0542a82d00380010320030032031481078094903c4c88401000690340c81c1c0c0d50b105960b509a0000d1601c00201c0d0800701e00080c418002c228110165103c0a40901c052540d00c0140c802c50a0400301100d105101c50404000301e9410007200d8003802103a014039030f560340c1003554001200006032015200781003612002000032050901a411207a0010004032085481182520743d000002c62842e00210044104400d035640f10300c4085103081c0946800600a0140010500b40c414500019405512a042804800d4400d000514140140d001030b241840030811000d1040e00422030310032030681000c9003e205a00c1c050200c541b103000c00307d50310050603284c0600a51a8064980010300c201c0f95401c4406a640311901111041a02c44060301d49a01d002101c0040d10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 827338129 1106 827337023 827337037
    0xe1e0102011407030203060102071e090518010c020d0e0a0f0e040201020a1a1005030105090d051b1f050f010614070f0b0414063619030302 61
    0x1014240740c24041d0030f482e0b90150703036400c20741d00080c68100150070203c03041c92600c0040405040504034241240c25801010609545600c170031010800f1103d06082d0300c1d420f03c603551804a50124140c69130814139104c0040c10320310340090104065260081005820000c40144240711241040c660300c40e02c14412622400450350fa02d00c10707400a0701c074074403480000009001902d107001002d08003034802031300208110f14008802a5451880201d080103000300080d22443c060310402c000b050b40300202080380e00b4a520207043d144418200248211003501d09000b0078081e1401c814458100c07549a656941c10030a8010140e000703a03c03040b411030341b0204013a0b201c000602a01c14441c86503000e948030348030b28010760809900b0180d0040400510200080e00f0b01e11101700701c0708140001d0b07403201c10500b08500340e0203440d181592603c180448401204c000707004040e4160020040 = true := by decide +kernel

theorem cover : BRFrame.Cov 827158273 827338129 := by
  have h0 := BRFrame.cov_init 827158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 827158273 ≤ n) (h2 : n < 827338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
