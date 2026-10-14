-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0128
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:58:53.783311+00:00
-- url     : https://prove2.me/submissions/3b7fba82-c472-41df-9278-b688f407e5fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 22841732 ≤ n < 23021588 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 22842982 1250 22841732 22841747
    0x1022b0612122705040c0306080d030903020d020d0909020307051b0105040302010605010f080a0507090b070b010302040c0503011a0f130618060203031e180a0b070e030c010c030302090307090c 84
    0x1c51559403054803d501054200048450350300248100c0703400e600a12052610358001c000c1904c6d039040024102c1e54400a007420010b0107124031010076641c100b040285501070058020620700c1c0e10242540b50321043c00a000b80f4124040d005032581e0101c0058004c500420031141241e40720b0030b55102001170f4407161800f0301011542107005500f04040081e0755401250404080c9980b52298201691031540c502c0003000000c20141c00c010001b0300c00690081301c10300030101036026140e41c624541c110f00601003606e03901c0b115842000810001045854820b0840010207200c41080e26540c000da010040102c0c00340010020410001e0300c40041d2542c0c00c440c40e000108005901800c0e01651550203a0710f038001100c8650610458a41c14000e4882c8805800c1c5d01900000318428140032000e0490315044901400b15100f6030700c101803200e01504181d9040c20340000714000e2046542c100c0c0024500411101c009051580200766003450760f0303050203040050982e070401040244c424400090044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 22844232 1250 22842982 22843013
    0x4030614041704080d0507052e0f020403080304030c110603010605130506030103020a030209101d040203010c02060606090d03020f060903090108090c01020a0602030a0b0d060c0e010314040807020d061404120201022b0612 96
    0x94902b011070700b00e070b21250003650116900860002e04580c2c5d1030301d0588a00c001094101c40099280200c0e19050b50740d03501440c041e00c120f54580d5114046070500c103590018a4011920421003030004000580e500920603060383d505403140030040c0c4486003d41440b80b2141c1003501ca1810041c0c010140804004045204a00807402403160400c0b0b110300b80d0b241c900944029030885004c0050458a003084090b950209201e40f04681c5410014807400d801c00c0700030b440c0882d00b6040007e04000644e030002e46180c000c105c003009000b108488400203542c854561400034080d54001c000151000c0250b40044a441c80107448803400d100701e46008801440d9000381240410003500d03031200035500c68462108864403000048503a0344481d00d898001d50401d003002ca07071100400036003100107042402410300481155030714054a003050300d8600000c009100c481811a032051200746c004071070034200c0c041d00503260101c02000000c481104005040d4680000803012101c080b1310702003188490450111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 22845482 1250 22844232 22844323
    0x20a03020a0e040504030c0204020901020c1201020a02010506060c070303140c0d020c0301050a02070807020d110a03060605030712080d0e07080d0e09061005030103080c0304030614041704080d050705 87
    0x20850403004020481300103890140004034145820001810300758001c101e01d1074140122188446402c00150003e11105408903003a500403891003807054090041c10740103902100c51504100c41c00307000954541042c0702c00b500304004108101c4034900e2400448031104203a1040c1d48041d000004069601c0e103070240380d54082e41ca41030005c1c2804410f842a201402e902c101a070785004600c0d000c01902190030b02003034170460b1251044c14030598071030110070300651180c140400c807585400e04050070442544d00c140950000100c41400007020348040300c00d059000040064800c040107110303480e0210f1a00402003501c5015440101560000a400d6023108201d03040b0300584d549600b0310503a504a200c141d070208405000510014403000301804203107540c0f1302104d041554a850740340c19520a0701ca0820081a14001c1c00184030300c01c814118800740c03401b8070702d00e8185020029995140042d1040d400c0040c003160250400c0310074004101075080c13116103502507020250002829403010200640c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 22846732 1250 22845482 22845497
    0x50402030613112d0a060c020405060a050409140d0e06070b100b0a0512100e040803040f08120906090105060102060c07050f070603020c1501030c05010809030c0604030810051206010603020c030d020a03020a 90
    0x8041c6848502c0c941503401c42e0b1f844008201300341c1c0c244800782102901d43c07544a004600b0121741030f1035501c141e91820f40150340d80c10504640300215410281b05a80f94820401540700b40344080d110361041301d0001c2e60052114402e9595412900390024141e00800042c0b9030000d01410f0700360307001c0c0240c02101d0581c82902100c0e183c100180041800c140320302907026501c0c00c00038020842d68405141d000d4004d40e0001c580109a81c0e170000d040d44030301c0d54034485800c80c100b4013040040420081c3e1703025000d40001c002900f05800044e42d00d200c000d103900030384e907000642441000828081961213491800440d00340302d4407140041e02039049504200d41603c505243c00003207803030f241050f604994010ba141c00c03130305040200440e071840300100600c001d40f00c10441c03502c031030000304071941c81180240c2e42c0c002c5608207212641d6012071306506c220711405503a0381403804c444012680b5411200b90f802c00582d19003030300150b0790450140060b004805440030840c0b00700207030990002d001074502581e07000f5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 22847982 1250 22846732 22846819
    0x6050108040506010312021204030c06090e04050a081e03090d0807080114040b0406030b0703051506041a0c0a0210020601030204060f0621020409061d070305040203061311 75
    0x6a030490308035405412540078a00403c081400c0d0244070a83c25280d10540d17a40d006450f4101166074840d5104558180c280d5804000d9241e1210549010381440d000003c401d0529880701559200740101c05403a501c070008812001621403500b0200c0c0220704110562246410424035448184c0030300302601080180c400038601c2842035861f54113aa49041c65010341038102d10502c8001c1141c002800e800955400c004004964899200344c45543c50b80d40218651602c602c00603000380100c06443d0044906102c00c1c0310021606050318442c2c900c0c4824a9242c0d1600c440a07840c05041b00030194000858891950109901143d50341c103981c0280da05000700c550750b050300c078002d001a118150014600405580c2c1035125034502180405081501509054952404074100c0304c0682c8100702080101c078003484440b20a13580d00d6030200c0a402d003041725207410740209850f610010130a40c2d1301e25100075113a0400c004281070f0b404500002d400283e41032892190380c00725400c0d4820b1800071400900408 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 22849232 1250 22847982 22847987
    0x12020304051e1008070207090902010c0606030803060102010e0c0d08030a06030204090807050d050a0e090405071505071412090613030c03030819060302010909020c0102041e06080a0c08010e0604090212030904060501 94
    0x3140104071700d0b07000300461480c0911000050400c000101c1c10004543d0b15500824202d0152001541c05801496601d040a000180c01c480c0b4001c940400b03600030080740c00c0559a0001003198241d0000307461079907030782c518805000400d00c41c0c10080d031162408900009108040000d804558840e104952000602850030b4900b8010000980001580c4059400103030404202c240d030030600c54001c481c56181c9511540f41c1c40a0b8a6002d0000240041000002d12015400d42c0c404810389401a01581d080104410014400e81c1700050049600046040181840c1040e101c011034121031050400b40c0c903443c000b000c1c94000d41d60f405a001090070000415002407003607100302e81d03058640c0544585010f804401079041945c0e00000755509010014180d0001e81501e03844c54900035951020604100380030308429009000411105d04d8003540f0603106810006a505541c0003a94201d400c5d5207540004001d008080310082d001f11035040b500c105440d00001400b01e042c0c0c1150b05024113902c1b40c004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 22850482 1250 22849232 22849247
    0xd0e0a09152904030809040f0c1107050d08090f0102070b070305070201030b03150406050c0705120405090106020d2703150b0a080a02010210090c05060a0801030512090d12020304051e10 81
    0x240b01900b004108001480c2c03600070548401c01a10102d000c1c0c03140c850704011502e51000d524040f400042030407881c0441805590003030f0004540201701104c9944904141e80100003100303016180521503102c980c0c1c0200000320080610b0a180740e45c0700d4107840c00404503006120224003107801d00c0c02d0f4400c0c034500031071403c0c464441500054030075602c41c0ca81d20060100502600c140c01c804101c0c29021450174082010344521245896640e00d2600b01400f0f00100141e0041b811174100280302401180d01c4002d416120f41c40381016500c6084480c40c0800040940c0d1000f410b0b0088030000906202d03664101a4002c00200d503108800341c1c0e1841c44549514007424002d0040c0c1100304500b0f0f88a100e50320a2003110b020f000994406500d40b4085403450b4888805400818010300041080000400c00f0340721480311440a141040c5030800400e5545041c2c620040c01c4182031a0380c500010310800649006050042c40c100c0f4406c1110a8030710040380d540b061502803042c1b10048019240105007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 22851732 1250 22850482 22850549
    0x31d040e030304020f060904060603050402031605010f080c1b16090204060c03110c090705030a051006050702060d0e0118060f0203010e130501021e030a050708010303020d0e0a0915 79
    0x507601d140c3e100e03420400c139048503204065102500740880041500d8034407c01c0c000d00100e41340040d00b81498010580743c02c007070b25407104281c045213400b03005c80e0740d0100c5042080d050505104005441720321065405010b200201a03203020302d81c09455281c100080c07820f0b0714030055100c0060141c1c07581895020f038450341c0103800108040b00c0403000001e1141343d012030908036070425038080b0810000026561017003610001d002810200c02c0c4142050a0700c81c1075081032080301003400e858600800a0101c0c000d4040c0a4424580829521039001d400d402200d03510740281c3c020040881403e0244140f02005003050715010300e02201140191964400c2300c1c166018284820720694860740100040c02100400b11000d54087c0b0180b26410701801011344d100080d0680d190312882d20020342c0084940040203d0104800e0b100100023194005c83c02e83c205001900e000c103000010342c8049441004a03601c0805184e14101d1203800c40c88900c1e811000303680c005011941694201c0200900301401402c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 22852982 1250 22851732 22851761
    0x4030509121002030a0b1203090109060e01030e010e030a02010e010b0d060207050f03040f0513140a050603070314070e070c0302030a030b04091505071b030503060405180703031d04 79
    0x810516454550501c001e401c0c0444220782498140c403100c032041c2d801c162105000b0607220300c408481071030800a00085e401340e0347e0085061135406000280351740340d42e100300400c4c00442c400005480c2d106c0d405c602c003d011008020710010055940d540d569030b10050342140194070307200d40343d101c000040c0a0b110104a00900c4141c00110700d4464030001d60104400f2a494031808004080605083c030240008040451710100268648800d101800110072009000c5600c2d00c003c00b1030b2610304505c000d80042050700c1c0010385580b400e0110f46846d0958202401e021485901c14110b800b0004804040e0785010001d20060340303a00c0d41c00d5030011803400c4020b0150304240080c101c0a8481c0d0303c01031040310020004940e0721a25110308001c4100d00e0f03c0410040c3d124000c0104030350308403c0d10b405411850b0143d001104e41902d00030410301014040324032176078880c00441c0406109244c54070341d4940080554603415600d15010704484000f015559028180200100700c910f00340c030a01000c1075081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 22854232 1250 22852982 22852987
    0x1030f0603050c06030c0c120904060e04032007080708032203020108040b15060a0e0a05010905150c030705030a0203070317010f03080c1f060306050f06030a021318210305040305 78
    0x10f010003c1a070001403401c0511541401481090f040c20445070f414038a091540a0313454507039200b404181da41302d070009004801248288000682d011401c01810300c0888800d5548402c8001600d00f002d40d41c0e884040c09118190340481c10000100041c01e060484150344450b201c0000c04200d080045448068081003242c80094089240d1700350140d03214141c40350f0103020b042a80000740d15504045441400107600c0b0640c40310728240001250090402401c04003546441c250018070601e0300300b00d40311120400801c05074240c18041080d5451680d00c041501e49407001c40300025602d0b084440f042d00020b0705800c8100810031948941030580d061841e00d00d4240341540c44140e00c6500070540f00200c2d12444220030301100070031060b2403620400e0300d80031841903e10704042d42541c4024050015041000051120350b0341c001440140040d4195a54605807001213503610003051103450801e034080c4090f60800400980e411802d6210541100181c0c012035026021811a40b04850040214008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 22855482 1250 22854232 22854253
    0x2030a050a23070218091b010c050d031401060302040501050a03020a020a020901030c0810051e0405120c01020706050f04020307050f0a030c090209040b010f09090504060902030a1101030f060305 85
    0x281004116003480c0e0b0402c80510041000d080310310b4010344008841000000c1034110452400d0016a120402c00192001090034018900c98a40000d041c0d09031107056200e0058960381d0040c015030020b150420103032610341c0d200103c0a400740420b29400120a50944008030b5501d000e4405d81d020b80d81e0680d1281c0c14585006002e070300a510180f85401580b04101490005a54a040180c00707107115800d191034803443d01034040d140c824030100d0040000d04043c03c00c90b0780b5650000c550f0101c8a0500807454039202d5081c00d90402500c15a0007145500c0007641760407940b4150010b082e25807150f041003000d95907125007025046e5050794001c1d8560030800c420001443e10100102210800902c0c0e903001558a03951403801443d035070700c00c0309410340119142c0300e030b45054424401a4142800c0092911044800040c40d01d221030140c80346a549d6200428107000b03160340001506c641c040c003150807030603d50504030000b140e030360100b0780002c3c100303a21007031003105a0240d5411070b80d014000340303040c00b00f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 22856732 1250 22855482 22855487
    0xa0302030408040806070c020a06020a030e060708042d050d0b0402121216020306010803090901060f05090a060c0605010501030e03071403070b0f1501182c0106030b0418020102030a 79
    0x4098415554002c041c4000f2840034030501c0f0132406030246407114181140548144041c0f40d500f42d008a040d03400030108034011030b402142c24141208201c400ea5650401450180040d0043c0d400418400500c06603940710100d401e4222150100d1501d42c09070115518002c00c28030161f03151005001c1c0f40b00b0000710380141040041410443e01d03d5050324080b01c849506540ca9802a090420098522805003010342c2814414580075000c0b04000d5440c01e48244086000b508040c81984104024440078803c0140b1072400e030790b2940c0b8028000000241e80d40b0f8003c3c0340300e11209041e01c901e071038800005601c2d0300078840d9441007500d44001c0c5003084038640b13682c0140044020311303004501082104000050392054080d1080324248812440e07070811038040c0003050b2400004a050040290000c0c4000724145c080743e08607080081c00c0310301070380c603820500b444004400210312100d0062002281454158202d02c181d41802c0e102040402419a20b03085030491100c0003901503041001810b10413403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 22857982 1250 22856732 22856737
    0x10f090c02120a170901181203090503040b0712080106230904052d0702030301140102030c0a05010506030c0103090807020118030803010f032009010b0901021203010806060a060c05030a0302 83
    0x140d5500640350a10520501c480503a400310071640c0000d542c03510141000080800c6280c0c2103000040200501c2c4100310300c081860581080c0a8041e0000512050300d0071300c280c02c54400a64810b007074a440b1956440c450946400c111011030303242041074100b0309002c0c4075007032040c12220a0380d40d650082c800c0c0c24801c503213007a480f4100304411404000c01c2d00a52100c0c021940145003042455409030758120803400d810312420fa6041150780c5c04420310140c10f40c000160390651b041c404032040021040c20042c7d180d0b1141708080106030180300311110500406600007407003150160103031424442c1c81c070011421545512002007034175034240b00040155109184401420030400e0b814070aa545170f1700c4410054000364004c0550441045050003044046180030710b601e502c03007036181900c4c0208000180a13020501034808400c0d00820a124907a108010040d0844d26600c582caa507035840310303142612145d088410300e005000110001031028800d820001e5103039005400f450404107208000c402030b5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 22859232 1250 22857982 22858001
    0x3171608060108102303010506101d0409060905060103020108070905060d0b0a0b0403050304090c0905090402090423010b030f03030c03150102010b10021615020a0b0a0906060e010f0b03010f09 84
    0x2251595004164019044903160310f2108000f4000c80c0f2042d4542011f00b500d80050580b405402080d180c505201e40160110040c082c540e208501c0c240000d8000c42c0c024201500c0c007034600c03403c0807480404e0240102d852410b03039000f030340c800300d25072740d5070806890403032507403140c913401c8141000703c50010005c59006400c12a070050414240d60754903007841c1c000d9003080e041070783c09400000313081040b202c280c85903c172959010700b00082d9407454240010150700c8003c0020303009803042e500040030400c6e5902da15000c45041c6c011001d003c20f07030185003402402d9203106503010780f05003042c40100d40b000100b07403803241e48000e00d000d14542e01d021a06841d81152403040d4195921003000c0b9601c2d583d109101a03030780a032035001700300161021000c00b0f40c40506d544600840f0b016120460026035001c0703000002d213500480044e485440da42240b100a14071410007a040518000f000f15024504600c060704032101e40c00c240c17089035100d8003240c180384800e00c50354084904000c010000c00509c1c2c3c0081085 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 22860482 1250 22859232 22859251
    0x302070606030c0f0807050f060f1606051303080109020910110312010617060a1505180604120203062511031b07080706020604050309040b0310060303171608060108 72
    0x507543da4030a03007500d031140c00401c8451041c1206102c006802c1120b42c000300400c548010500f5105008201c2520825040c1800b9840004800e410440692245400d080d84644104250310f00b510318500c180f00c80b120220f000661400c000245003c4c64004d035994220300416000c04a15684410344034010040c2900c03485000502c401030141c08002290b60080005803550000c40c87c40c10307600115000001e020a100d006130000c24400402c014461001001071814100d0703070b401d400b07242070702d1020f0803114856011200080204015605000345907000780b09074102d40080e00c90b503a070510088111420640354005207980c902280e4403808401e03880030210b10980345800a50700e00015040c0198103d40f0317090b48404010080300303104006180044c800c034406001d050500c2c0e56915281d00c5008a8103100301d41340c1d40c29210598040c0402c3d070100a02800030000130781c1c1c901d0007810b030307007042c030700d0004441c0582c00040d291090980c50b25406034032640d02d140c0c159031564015039000c000038003058032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 22861732 1250 22860482 22860491
    0x204140405060a09050c04050103060602030a0f080709090204030f03021207080304081b030c0d1e0206010b1b0f01140a060302030c0d39090b0303030a020c01090b07030209040e03030105010f03020706 87
    0x10340d107901703220b10350103158452201a40c0c0e42c103160015090b107685620200440d4010040071019aa2100c5006480c3c03482d4030b0038020a44603606e0480b6049d6040d00000f4070706100185c0001001403d03108800c500c0d00c20f80030b6414400c00445104114011203401030981c40c0108001400104008024078800e104034480194016140310301500e19040b5418840381d942c000d19070302100b80c2d040b14280184440014280c0c020000404000351950818415201c400f00042141140d50012000404006402108440c03606142c1c413901d40c040c166903d060003080034020301103140c80d1414001d00c010f0340d80140091401030b21880c14000383d024012010340344851418000940541501d032200c401c1280c5ea0851030b040391b81c4505c54070003aa111fa0145111901c2c0071110743c8152004026a0740c45412100d0050b20ba6010000450260100356801404c90350b41d0b00421032001c0d0558003400e00150262030800035841060921035981c407080c0180c81c04646c0b140031100d42544290020100c01d480307a8004203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 22862982 1250 22861732 22861739
    0x30e01180312110609030403020d020d06020a02030301090615051c0f05010609060e0f01080f040501110f03091006081e01020c011109031b0603010302130e0a03020d0306090204140405060a 82
    0x1652048903001110b142c1c00030820380c51400c1c0c0c0168004120881400585070038100500c44503500e200d00c0c480280980d03256608074041d0360f08e0100d030122443d0805800d5642c0c20040710002d460350300c240035064856207040c0e00440d0b580c13068185c003121000582c07505407034118000e1944d040300d0144880b00c00550344440315030344400d109019460003032245454855515083c800041c7c40a540b4000c07081c0a4521a07401116036a8021501a04000803400c0081682c4803410130b1405415141458880c030440000c04104d00c80d24600118490819501501c0b41002101c0404c01074038164403a03002c13a80d200c800b6031790380121001001120aa40303032000500d0310f0080c540040c20354800001c010440c000c08602c106031400c0034404e00c22161007441580b0713150407400b00010050f000c18040030b4010700b08464907503100004e1340c1c840c02070882450b0445101d4006458020b40d26041c0c41e02130b0300042d0400d600000c03030551a00031307901510100740c19410381442c4801844004e00d030082440c5e601080905000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 22864232 1250 22862982 22863017
    0x30803090f0a05100b010806030304030f050f0303070c0b0a05040507050105030a060e01090c080c07050706080604020c010509070303031b020a17070b0a09050c0904080306090406060b0a1d120a030e01 87
    0x1c54900d1040f0b018000c404c0c40c1c0410310046944105200381400108800c002003940e01104a030705486c0d12041100081d00c0c81e00b006d07880c00400c9a01d0202500c400402c0c42410b54100504c103000c47d209042c1c0315015540e240c000b1098440946004242d5405500103011301d40c0a040a5a4021243e1038002051030341d0314074440c0c00b03040a0303004802d5a40d8500d540404198000d00f02940160200072040c50060305585a40e980c001621401040120281c040340d00c0360307a1a0122030390191540300070700190038000b12807600ca6540b440100c0129241081c1d07000303a4a80803a0f00c20700e03800c068000c0c01301000306172034030b205041b080d030410681c0e180100445c1c4002803a44c1490b90242040c1c80c40010300f0180c1d494a20f1034505000701c8079101d44140c0040100080021044940c03219083e03805920940301e0b480c0c480003800c4a504100c2d00780001007040004030fa4804260200c0c9050303424241504503031241800100805050f05070304a401420300c490200e0300624a04001e03500615000c0c400d0050100d58 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 22865482 1250 22864232 22864243
    0x15030f0102040b0d1803050d0908040b0c010b03010e06070221040e0f070f020106030209060d110909030a030f1104060f020309030d120b03060c0301120206091e15040f030803090f 78
    0x203502d000f0000c0307200380c011011803190200480c0440100c0c0911203c03500c0c003a01c1f030701406076422070a0f80c8800700c81c0d00700302402d0203560090008544242d11080560441d501030440314a003140290b2800800340c1000100080c0d0760302448290300540b10910302c0c1045040507402d01d400c04598200100000181c101c007107600944a240c1e554803c1c03420f07041c01c0314020b103c1e015941103403045a04106083c00944d179135204a6402207002c40ba0200054640c2c07a00034924030203020041c0c0d1000040c402c001030404040b00800fa40500d59400b0451010140452421a004000038a406900900c003c0c841c2c00d0040504040050b110300442e820842c041c00000c3c0382800d607820120000700078513035011001e0100c2c050221010801c40103050a49030881600059010510801040c450044295000d545035103048460900d00600000c128420030084e9160400840f041c490103002289900001e8250315000da90580c0d00c9445100c40451540c3c0724074029810241030501c1b01e005c1c10001e141070302401c005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 22866732 1250 22865482 22865489
    0x9050a03020706140a0e0108060f0301050106050301090b0303030903030105040b0a030f030e0108070f08060415030506010e1005090f04020603070912051c031806050709050603010f0918030815030f010204 89
    0x1d218490421100500802c4101090b140c814020300c14170b511a0742010312815071490138030f0440301a40d907890024030010314050071550994685400401c003280c0c0180218180c900d102c20520601e16008249a07882c80101c2c0d00c8485504140f006011901d429000b001c1d00000041c4030500403502c80d140c551310110900c40417400724039052403c0e00300c0c0d42c0140d0a998011403c0c103208042224601001d04242c8000300b0241c0f042c0d42e50590501d4059042040c0009181c020045480a42c0c45203101800b4071401d8070207061b000021000040c1925040e10034511400c00c260300c01a5030780707507942032207101d03000030300342c00c003441a115404944001c01d5483d10110a000784014030720101c010254501c68003000903140105404c0c0b0069003501c17400c041d2030110042d8031000010f1940d4829104407081c0810707401c01c61b80904000000203098545d080044280d80008004010440311f024041400380ba6804008001c181007400140198005104001d030680010301980c2e04801109c0540782268010340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 22867982 1250 22866732 22866737
    0x90c050f0316080703060e0402090406060b040b04140f0a090504020d2009090c01170903040902070c170d2c09070207081b0102070b0307020f07060c0203160b040b090409050a03 77
    0x201c04030b00031030b80200b000e500241e0506081000e1070420790740081200700100083d00039030040001c01d04009007035010100403c8010143e58039240c86250040c4150f1084c4204980300140203000b4a5515110b03180d2042104018800c400c1c40f0b103800d0b0804080d0000500c16a0311581000c00a804600d2610341505c5100303400c1d03160000d90141a00700700310a440038000d007685601032145072a444e6040307801d00380011b0241c25445055510010003e285102d142c22080f00c540c00450810208181e0740c0010042d6840450b08004003004d0340541c2e0b40c0c1d551010103840001d95114020030000d024101d490006c2403001c0481c0d0700c0c0080da00c0101c0d1030ba02d0306541c03000c0140c0c0704140401081406000409502400f205800c00c7c1716034502c0001d50300c804d140181e0803000c00000215042c02d0007007008901688110060340e80d81696500044e0058184650aa000f07018036a001403131140101d034140140e9114800b2a0306050405030012081d42043e940700d43c11550301c00413603020130340c20800c082071203200b603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 22869232 1250 22867982 22868011
    0xf09080106030b2d070c0c050a0b09030f0102121302040b0315060f040915020a0c0f1203050601020303070c1203020702040207050303041403070503030a1e0203091005011d01090c050f03 81
    0x1000c401120101026400138900e24031101c144100ea8090f1041d80081d801d2600a0105026003440249071150b903001ca903000e500c0c070344005150f00154001e815410b200701d0035181000301c0745286070300b40d100e0f400d850780700581010f0024944001c1074002601c82c40c00903100041524107280420724040d640b03803940c0da00448050400041d031a25404211140805540a004070300642d0350700c81c6504125002007000303d0300412080006403060701003142c802c4e040485140200d919081c00588000c000003041c000900b40000100e040d4000401c0340c3c001c00060b980c1c030002498a464800301440c64810340300c00c160702044050050f03500d0f40040c111a0f4003d901859032400c080c6400941c00040380c245003195001030000c80c006c6640401620762112030078402084145504c2d0a51262100d0201d091100a101106015040d280000d03c420344a410700d10400c1281d0f00c840c4041212164843c105400394070080051003007004a40010038003520074140356043c007980540288064008840070700054106 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 22870482 1250 22869232 22869241
    0xc080d0603060f02120c030a1107080c06011d07080408040909051b010305040b010b0702030c060a02030a0906021923010204150207051f0f0c02040c030911090906070f09080106030b 79
    0x6101e9030310f038014004070451030084000210300e400136005103102107075a0080f00082c0030340201e4004d0021000c840e8840c40d6541040d00d013512280d0401401d0114510500300086101c0002d1120302006d40c2000302c0c01412603030380d10011205524002c0c0300b207500785401d100005205160380544190640300c0d07000351200700c190041d40380d5290102c507100d2b4105030601050201040c100030002c0d0540d844411032550f50341d00780c00424500620501c045801040008905e030400b0350110103402001e005070f881102403036640703a040f6a0303103011110b4240e505034855030a000081115400f80d060031800c00c130311070749244480891422a002503020419480404540240c0c1a03814000c0602412045580c40c407190090341120145076142c1c4005401e000c2030021001032540544040045607900500c20700c100311040c40010b000e001500c00454292058550350140c1c2d1814000c20b42c4a44c400000030001035035a0482203c1d0070100300012801e015a248000c50121000e01410f030103580a07854640c11401d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 22871732 1250 22870482 22870493
    0x302060d1d06010f0603050f0112021e090a0915050405030a03020702030a0206190f020f03070308040305070b1008070b070f0201140d0204031110020a02030a080901030608030c0109060e1b010f0c080d0603 89
    0x80061441d0381561aa00c01030145895101b0001081038066944000d5400209000350f541a41002003507400de680c13100b0420807040321f80191a00a20034440c50100c80f0801c00600c056600039074001b0300580040c0414980c07030340b0985c090f19407140010110f071400e44494000c164154464241194400800c1c600c081a16802105680e0141c400e4401007420f0b81104036102e440c8e000344e010007001c011f81c1d40041028540308105444a840e04040c3c0304607681482d003000d0342e240c2d49a01c25031110707000e5210001051358040080d2184160403902e19102c12515500444030503144410b5007080c40c000f40403154000d5154405800514400c10b04402c06514410400000026062003001154400640000141c070081003040540707500002031611036952a0041c4d01800260f0440c400911000c1110000710030150403d8000601a1000300000e40100101030340700d000d044440a000c003010106034616510035038112440c0c3e01145004c5d850341c510350795407650030f6010806c44010592540c03806d000340023 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 22872982 1250 22871732 22871741
    0x70f0609050d0801120f3014180d02030703050f030310270c0504051002030306130203101a12090c030601050406060219020303091206010306050f010302060d1d06010f0603 75
    0x400c60412151561501800e0142c17920003190007002400c070841c040d01005a0080d000c414090401200410084080403a541c2d1000b0001c10f6000520700b030031504070f0080d455084502e4400490841e41c3e6803980301e018440d4640121200f00d815128072480040807800070b00114021052400146a50741025000d89411040e250040180a8103441d0f545182068020300055803110948002c10300761100001510940260b43c0469044803545060000c11036000c4002c41c4541822225503901ca8000c1201c5802c83c0070031100d8a03400218070500b4483c0d803140d1011920101b080110392850600c2c1c44c04c403c506001c00350790600d0540d000348190300041c5801d103c0e080c05400e040e201040710502d000c100035070300e48412219040b4410072901c060250340302031045400031403029041d400801411031500d962a0b0b024402a0340301c51400f0042401e403400d00880d2030403290018901c82c10400d02d88030b05001043d04c0004021194a0410340410082c1d007403100500800001c1c051819503468944050213a6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 22874232 1250 22872982 22873003
    0x6070c0b12041106090904020904031e050a03110a050f0708040f031110020f0d030e0703020a031a07020a02010804170d060602010209040b0619051b0609070510020606030c1302070f060905 82
    0x44d10140481140780d140d140758182e1003601282c3c055180e4440d424160b40541600301480c0725181032a800525241d0800000d003c441015581008640030202c036031960390158102c0c01e00002e41c10043d42c9111340d0000040d1a2003801004840c8c600b543d00c85039404d41040543c0200d403a03c000140708600d9140c551640c14008003140007038620b0300c5070f5800c503580f40e80e281101e040c24160303035014401c0c030224100000d0019650181c81c58008689a003000d0700300345072554008800620150010b104580302203010107166906031101384007a00c2da551803401d94515011084c03280003041c080e092902d01e690240030010642e41d0001aa201ca4041c14042510150390045014100070000b0b03503182d542628071402c00402c45c0c82d10300e0f19448810741c4100e42c0300a08240b040288074000500c0f03403800c07000c87c0540c102d440440341c0200e0a840703268240d80311081202c1c4160305401254542a460400401007620070101000051501d00d40e90344000c5e40c0b444070501610b03202e984200000c20040f0410142401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 22875482 1250 22874232 22874239
    0x150e1302180403080a0f0b150409060515040320060a030605040c0306030f02090601051204050f0d030c02060a0b01020c06040306050103060e03070c14040902041806060603020906070206070c0b120411 87
    0xc916090720003034400700015103421011556009076041c0010f29510183d030300e500091400e88c01c101810748508076a0420b0051000044c0381000010f5907103008132149a2000581c1442410a4036580300c219040c5181e2a1080b085034100407a4005030780c90000a295029541d1400035000d401d0000b0720080380e85503403030401894a40075042c000f29524500d840c001d141e04556420032650303100e00403582070150303030300814403001034100f880200f00020034140c000005000c102c4540e0601008120240c4003202c05039030160700680c2c0841c2c1c60f81c00f0390308200707854581801110f541d282e038140412a107611550095944c02e42e070328010f0040000c0d078081c2c01c52800341c40c8020342c00c190307094462240b41030942c0b18107013000d801c0030b00034070142d03c464210800654004004100c4240569420f141080c8441001c942c114075000c1c0101d5844e019209a030302d60b66010389194206080755007030260a6005400688000c00300360800644411200d0081c01000d15681d0f42214030309007403400140c900c01c4861210b12 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 22876732 1250 22875482 22875529
    0x21030403020d030606020c04020f1605060910020307080105010e0102070509090c120d0207061b02030601030807060507080f01050f040906060f060f030204140114070f051b0901030206070204150e1302 87
    0x946d41c000351480c004c0d0030442c0d0040e501d0340ba52a10015130301c03c4084586116445100c040f05100000ca1903510900000082c1c4a9401810b5441412032104032046000b240c003181c0188803d512800038001502c8060044a83d411784400015003054000c41c0d03000e91a51048070080c0e0642000f205a081048200000348400141400048d444051b180641c0b400c0041011000011040c001e0740c003000303990060180d41a03561641000e50f081c0e404510140c611500f00b4021801146c03040071510b1284020f407880c006980d007014100000c080070415040d0b48151940710440109186205600080a04204030f800c81440d01c03d011749101d140e0f008079028540b05100070000c0c10803c03182c0710500c04091a02104d000303a205204070342c60044450142040c1d1404001c14104040050044030a81c03150ba00c020440d160881080809802400025044082030202d41c005091a801a040f0005000e21003c50a504c2d88420028121308031111a02034044802c0801035080966440340b5810041001c00c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 22877982 1250 22876732 22876739
    0x804080705090108031803070f03120e090f06060913050a0902010e18070503040c18050708060301020a2705030d021c03020909060d0602040506070c080706051e09010221030403020d0306 81
    0x2a01d0b8011410100f00380031806c44019403d64080c0700b0303200940050800c21350790680700c1c00c18032800d82200691344080340c1004003042040c60200c50703082c031440c81d0490b4403000e9602c1e01c0500007107030804e1100b031340c00102c034525614900da00c41c000d06104140301d0000107080c1080d40001000c100500d500b1500404501c284000302c0c80305000707038651144003801d206a4940780c519103010500c0d01d031b0380038101484c1501000c80d280786c00358008034010307009655244400d4641c00101801c1344503a40090b0702141d241c0080740c14900070b00050580c5007120242c0b100c007031651100424203100403440604010780218900e506808880c26140c81d110003289011414080c0c0503000c682c400c14003810b2648105824007a0104201441d011540a8080540103e403a2410313483c000307144003d00e0240d11564081d000d0046003051041d070035510903a856520b9101c01c402e0a5404612030342c8401c03c1d0300c0c11401540d181403d0010400c04c00102040c85030455507580c6072074100213042c0700540c0d02e084101400d220702007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 22879232 1250 22877982 22877999
    0x80306030606010f1e0c0609051b030705010c03030f110a0c03080a0b0a030b060409081603110c090712020405030706050a0e040c0f050a09120609120305100b0309100908040807050901 80
    0xd014002080ba08201c5e080300c8001078964005c801c0c03000b41440d06180c0d40c10100718001c03642a030240401005220380c141c0c0c00c000c03d52128070a000b644d00060b600e142d03000100f8840d4000346081810350200003100302c281401f2131103e501c901000808600122808810503a00080c035603840800c40400b040071000e0340c00040c0b01c100c118800601005050808100140e5940c0d1180c401d2036444014a036603004c1c1803040041070056910203902141000b24804d00e40f040100d40103280c044000c0800c40035590740c84c4190b440721038540780b016006509210109060724100f00c0e00303003e40303c0c40e240d00d611204108401042c40450182c0b19000f0780c140545551044d82140c60a40340d003015051060b154049128105c0c0c5c0410164414003030301e000c505000c414004142d00c0340d610140200d90611180723800500950541c1c106403100484c1492111003080102d9845000d150050340e141e003070b0303150f031580049035000f0f9030f84c00d900a035024040081c0403c245001040307074200900041d80c2000d010362601205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 22880482 1250 22879232 22879247
    0xd090e0103021201020c010e010507090608010308030a09080705030301060e0f0607051f020d060e070807020d020304050105070c0305100e01050a0e03090d020d0503030109091505190f02040f03080306030606010f 92
    0x38003d800403110304103803040a4040ea0403d9203828000c10610090302e8069010307107415525240800e90f04800800d0b224880d0420905894010f40154515180c4c208100014200c40b18181c0d844401849003100041d024070066008024a41d90300c076416800004004182036280b541a22a034810000440001ca011442e0005080a205800d180c030030070340d442c80003038440c10343c8900c403181ca071440100c4c0800d03a00002034010404c41d541c840d6907039501c030800e90399032081d8011000540c4c070a0104010540c407a00c000e24140d441010350510310b036501d651721032618501c980420f1010b6100d02030303404100802d100d584c0d03001c44004014000440107050090312380c850f4805082c003614180a0300c0c41076465a80c1c90f814500e600904403540c82d03075160001c00040c0f001c081c04035020610102c544030005c0560141d0b9001c0c12002d48403505184100ca900030080c8005085c6a47d100d40a01000400038629003a000044d0b000303a100a80c3e030700d004010541410740007842c0d10f042c02019004408545c1d4000314 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 22881732 1250 22880482 22880489
    0x209010f0807030e0106030303090501050a0504021503101503050403032d020711030f1b030d050904021812010605040f05071b0503091c02010305060d05030f16060e0f0d090e01 77
    0x706082691200b0030110081d0054100100d001c0d07090500000425501d07503c010351041c064002000355868bd858400d056800a030740286d4029a05e030101d07040340101c040110303081184103040e00003c66650b11400080203840031904042907a5004000c14141c05000d0a0100409220440e500c216042d0013442d031840202c02c1140c1d841c0e070204000d810403030b40304804006000c0c01011a00c1d81c03000c0401442d0b9941014152200c41e0b81640d03e402d4140c00c0c0000c3c3d101c2d0071a0144c85181c14601c000003840002e4000380c1049004407190114a0250b8a400041c044c11802150001c1000d6040c20f0520040c0d07050042d4049943d881c10707080205d060750050400e400c0c00d005000b042c5800350b0b142800d9155000345c5404640c400000442e580d030000c018400052902d20130b8030148401d542d01e1003081840103a201c00030b081c681080040c50075a40c010713002401d80318403100701440c400140317441e52411107644c04031030041548809404d04042034200604038640206103420310311503041000c0641000010310 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 22882982 1250 22881732 22881737
    0x3030f1409060310062003070303020702030c04240b03060310020a0207080d0305040606080303090c0f03010905120d060b07050309010c0201090e1006030608010b0603010e06011b060b040f0209010f 86
    0x1212511000c08101220341c0c1860041020340c8909000000ca0b460b14014824440410101c500d60b070110b5032118018081c40401c0c0001c1e60030441c281c0c8040e00a58410303a002c81c0e142c0103c0305c0b48a0303950741d02e210360740071074000e02c00a071042e841a580b1006000442c0d000002d00480c00d1040014950f80003804d0000400b10240140c1c5844480c4010f0f0328201c03283d0802c1906005091044ca501c0744d159001a2082d40a10f01c140310842d65144407a407603100035281d0001e036070840422401e0714108420314501c0e0f04405030000410401c1a15440d0902c50980c08105a10500050a900c20f040707a0094801500016140e140341c5020355031005d82d81d208101001c4d06100004101d031096a00070040f0000074158800b54024a00d4070460703262041d41c3c0c43c010702c80800d1034200d0224440c041481603850003040648003d10310b90a101c00403450050007418641000403800300c481c08056a0b40d50361007401d2007106e011500d10a41e03003c200940300540c000e4080144188440101030f13920500b519030b000080d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 22884232 1250 22882982 22882997
    0x302090a0b0d02041a0903100b0102030a210c0c0b0a0501150f021203070e040c05040b0706090807210206010e0601050a080601090506040b070b061c080d020903070311130603030f 78
    0x1c44580081d00131075105100d0301418035954000c00c02024000d042a8500300c00780c4661011007143e1200706c1d134041240a005034814805910114040c004c0c02c10b206c03448102c00004408151400420340f103058203004009542d05424404016424032610740000e1290030030700c17042d03051040d02011980c0b003244803003c020050768121850b50080c05405050742c450300c0d109549150054018102c2c641c3c3c04607650240d80b80802010429101d038003620180d90340107038842c1c6005856110f0b84003a207402401038030100010004000051885404410081028035640040410040001c0c0c2030401c1603001e402d00099204c10030100d80e038000112100c1e803810b4149031075540c0b924801210003517229000305400800000e8040307a132450b500042d0548610946046a01d07507200030600c504c50041d000503c056803c809003410014103500040d0001800700100141031106000000b45445843d600546000c1080c1000f11080c0c1072075481102c403880c0340c1106100c11031859900800c1001381034411010019074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 22885482 1250 22884232 22884247
    0xf1a09090a031404120b251202070212100510080607140a030b030d03380103091a040b010302010801050301090308010509130c0305010506030705010f05090409020d0209070305040b070302090a0b 85
    0x2002d40c2c019100031003024501c0c170030750302d00701c910904182c4000140300004104041f05405500c2084101308441c0c0da6148441012611003020703402c110405c03a40710801c42d0410280ca001040360310000c1a0400010625092004003115040281e4100715140e03042041046041c54011588100d01104034542682c0d401d80c4daa021402840b800e018a6131601401d0241c68081c1c1d0b15801580c240c0d0403c100d03c0d81c1e1415400180074900c1c503032600548007103030402e9080c1d0566020342c2c4190031482c09030310095a125258190000039601c21074048405440040050043d540c0c801c140d1809000b080c3d008100c01034840d280039289080500c2114850b0f200c500009080600502201402c5a03002001c1684c0a41f41d1030414064001240e4190003031254036800a0150b11481e1550510392158603540d2610500340d00b403101428043d00305a03000030800703c00303000503210294254800c40352642c0004031400e041c5020364004c41c02078210310825005000c02c8210756980b5051204440c0c0e003581c1580d54520 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 22886732 1250 22885482 22885517
    0xa0f080403020d0b040309061106010b0c03160503070303060f0506030a151710151a0901020106150f02010f0e07051c0501090c060207050109030b0606070201120f1a09090a03 76
    0x3541c1000303401c4010003d5000c10801c0100031070380100e12035110034241c6604c400c801c840500c02c00d46052040e86c0a14010000403140704010704110707500409a03803800f10386401c100c10540035100101c41c1075200180020500d9410b104a0f405045a07400070701c00c061030704000413281d01000c0e02e0107418a503124204a032071001842c11030b0040074170549240740e0000f83c1a031751f40c4900740c8161001c0050304102e0b854540035621214042a14698510305038070f05000c50450191750041c07226141999650314000c55940d114140140c800720607680e40344441d04600380c0c000c0c2900c9801941c0010581803200f05070440002045000a031501610342c07403621000c1c208015285810300c1d01c098030651a000182b802d0143c901400385c2654840d40803a20b20660320700c011146a4150310000c3c00a089900104100749032250040042d18014508a00120b07414a8002c081303500312020b4852240d510b03000c40c0e5000081e2007401841c941c00b2a41d54a103403802600300e40d1144840c4000504104107040c05108241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 22887982 1250 22886732 22886737
    0x501180c020c03061e1602060c0d060e040f060e070f0504020906070602030a050414060906040b0601020307060c030608010b01030603080301060c150504060501180b030d11010e030309060a0e030403050a0f08 90
    0x108010115412420000100c2c410f1401003103010050185e0100002d0600420400760300c210307403559000b80901e598180d42d40d40301c1c0c2c0090a919621540b10480050b010f0480340c07003a402940a60500301d112000c51908200f00c850b1900400c0041d00000000c004c42e0620400c60402c841c019100941c5e1000c0800000707180d48524200204040c0c400f20030310407075402e03e500a5116074403541c0f4050b400c3c080f5070b140d07943e11103084031400c0741ca602100000b030024440800b00c540104040c0110380c02c0808654880040d102ca242d580f0700041c1e074804040009460900462464079000c0c00c00701320440c01c61b01c5604003880140075040601039410043c100308400f440e03d1034400c85440500300041d003041e1030000c018040a204e82600c0c00d181c464001c0290a603071003501140c0034010300511351740042a000f9508099a005c000b41c1c00d55980c401c1200d52581813004501c01c4403084042d000c94640300d41510104d4901000d0366405034400e00c000d01c00200f0008040c40040e801c03414004103c08c0300e00d414109032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 22889232 1250 22887982 22888003
    0x11406040e0c0a080706030c080c0301091d0303180d0c0c030b0c160804140f0616150608060f010609060801060809030d020406020102071110050405010c05031b150108010501180c02 79
    0xe2100000081404c0c0c042106400d950003540c0601282c4111001207a1000c02075407141b06070441003004000300080ea610540680c4a105200340c07000511140240c00d5420441d0006042d0700f4008082c28806c030184001805042039003400c1e0b1303070030100d40c13583c18840d03802d80030081800300300002080710000e2000c01e407101070700010041c03a0030403160301c0c02e58050707085482183c00e45161000c0f0400e04e0b1074003031001d000404010f80058105064076009001d810040c140c10340b02104400c00720310320561a801103102a242050081000303080c280c00001c00288141d003c8010008140c1c070500c19903520240303403811100b80c6c1ca80b65000c1c0d2540603400d400e51040085075080c3c14400100001d03240c2d0103401034041c641c081c40c5c0c1c1c80180d000e16414030070f02e03840c6c1e0400d10300020f004000902466000e0b00040030114080d6007168148512404640d85c4003084800703011a560000010b0488500a8501c09001d40401c1c002488071f94580308210b11401c50036486e0020715078440340c901ca441c034402c0082c201074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 22890482 1250 22889232 22889239
    0x40b090103031d040c17040309030830060306130c0815011e18020a050d090501060510030e0a02060904090501050109020a020d03020f07030c080f0c0607080603011406040e0c 76
    0x555079a8500504000e800140c038020b05803610100d03868a15280c85045c000190f00e0300c40d40c00003504e42c0041c02c903d9000900c11001d2000040300440414210405807090200140074820046c01524820055000d2580440342c442440404c000c00d544001c1510780d08a00101c07441c90300584d43d407420030b215009a82040d00c0340e1064120b0600c201e5504031095040380e21207941a8081000741c1000256005030340522a82454180c801402c1d004d140c0d4001d01c0107007143c0c5441800d002c000340c810702c140e60441030140c900f691680414007091625144205810440d0308040115000a119040c0c0354090800c0c0031b4421324020030700815985881d0060f0500c42d511030001c208075a101c00b0b101e0000c6d004400140e00500c80c51403880002030003442121010081103080c681070146035034003126080200030742103580c410180030501d1403601c002d001c0c16405103481c01805080c6031408008028400080a06100e603052004494071892001c035a1500b01006407404a600b1840301e0b040d030f26180010184541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 22891732 1250 22890482 22890499
    0x402130b0a020102030a0506010203030f0f090f0708010501060305060d17030c07020d0303050108100903050909071403070804150b0d0201031d0a05060405010f020c0601060c030c0204050a050a141311040b 89
    0xa00c1c56040d40114801c2024100800854881100480c0c0d24001140c021440c0d46560000c1642d4040c100380082d44802c0c50004c82e95003c801c90340c014207100141d4401c00c100d0703445200500026805018081e4061402c0d500146000010f0f122000e40e2002000702d240702c2e03a40000480c012044d080c5c112a200c0f6005803400611f2805454010300a003000d1280c040e00e4040c1440c501d5000900c1c0c0204880e07190990356040c20400310038100000c40d04054003003014040c0b0301840f101921000b0001e54031a06070750b03c42d541d80e850a42050f45c035441c0c1409041004529100f0451425680d0b0900c10341c00c41d8082ca000108180d800d45032170940b4882c400d5140040c881e88800c102001800581d50344030394442c1000340590a0780f10030003006e0f80180c030045003040d003003240184141441200d0b410709481c0286008801080c0940100d07080f96010758034001c007161200d08209001c10113000380e00120b22482010081ca19010b00c040c13000519440e0001c0480054203000e01c01c0d070f500c03a0404805008001c140c0721 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 22892982 1250 22891732 22891747
    0x60706020c100501060216140303041e09050a1e020d06081c2d0c03030908030109020304110a060504170304050301180c080d080703110c06010b0a17060a050402130b 72
    0x907038074800240316450b0030341800000b181e1607201055504c12800c9201201c0f012900b0300750202c0b401c1c0700050141d0341510051100049401182e002102c0c000c4460802841c0682003082410a50380001c000d6a201030900c0243e45074098680446c0440b25040000182c51b080564015006002c00d517010040a00c65551400084000c40c4240384086003a83c8800c1e40b00d001100d500d18074001c1414034605051060408840c406016907030300ca0300684030703160018840303140c0e07a602410398200303800c141c00d0590f001c02080100300030a108650403a8044038400c1d0494075180c0010b001744118007450501c2007134403200c000480010800c2d00e02802009000744000121600303940401e0b8080d01d0192594400b902c030008840c2002b16a40c91009450303601c81074103a841c00070a130058018003621350b4880d42c0c00c00c070481d4000b17424403555000c0d00c00480410340da450402c000810440ca620700da0381c0800d03c84014440141d842c1200603040324010f03500540c480c50301c2e1001c1e14200c0080c0d8000d1840440c00a01c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 22894232 1250 22892982 22893007
    0x11e030204180501080c010509010c050a0f0308010501111209060405120123090c0d031b0308011701020c06041407030507030804180902010807030b03010b030327040207030c0f0206070602 82
    0x3002600c107410020b0441d4100d002c007000c2501c03000c1c851085e030780e0483e6101c1120340d489607006000b08603040c10012100c0e000c6039500f51038051030340360540d400102800000101a4018111070041c002443c020805100714201c584d00c030100c1380c0102031507080c00144800a40c980d2410b960041038010088017a070300310300c48968080c282c000f030b0a0458905590002d40404e00000c511401240480300401d19213407000240700c04140b01007020fa0500c0f4000c000303c2c2d941c2c0e0b9113440c1004410301c00e40e034100c0d0310b5140c0303184072080d5600760084400a90051220402200c00015032070781c410741012000900e6007901d095541002d416403c05040c0e4012840003105024040004204131035007000c01c48816110b0350914001c45904240013070015007840f01048200d07100780c11001020340000c0c00003400e40dd00700002460740e80090b101844410100200a05200c02d05401c020b07403644c143c0d03056150407150b590060400206440007003001c00e9480017001035445003015502c1c0b451b4400070441da02e1000201c41c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 22895482 1250 22894232 22894237
    0x40b030f01050a0315020d020d0608010219110a031815021c0507020105070b0a06050a1401080604060302060a050c010e0a030302040e07020a030504050f0102010e0d030b03070b03100311011e0302 85
    0x5400d5180c4000000140d90b0901d0614141140d40000030340c00030403020306a05001c1d50288000b00c0440c0d07020f001100b02c1c4050762003114014030036240016510442c202509698001850100c0103000c003580d440d0000f031401064446210780c1c10f140220000a042010f485800c046400c41e50107080019080132070540c0016802c20311030300da146001c07001d6801c4102204d180c440c00d01d0081c0062005e0001c0c0001032002c651450b0400003189c0007280f8180c480020681c1844251300c40c030314011041501c0c00c2c181d43c0010a403034001105903000d000007401c580101d0818425841c0c403900b0414001007142d0180400c2d071260f031401180d003060710358512103810300801a4000d4010385061a9804010030f66584c000117102c02125803549485043c5031900d000c03c070001c1d0b01a2101c60540d5225800200d0742c207028080d0165105140c0c4001a00078142d0052502c1d10303809802000c00c0e40010400c0c45207070846065980c044a91100b0a1f8800056403001210781c1d0040454584481e111a40d5424195805401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 22896732 1250 22895482 22895491
    0x150d050108250909020102010b0405070201051005030622050f060c04060807050307090308090303130f0e010605031302100c150911030106060509060c01060e01080304030501060e090607030c1202040b03 88
    0xb10b031118000601c4240000d80e14608100e0300705081c00080143c8030300d50f000b55605038014000002d0004203840402e00b951411250400144d640d4020081917a0b055003000c4040d200984c020300d09031030112020360b200000d001d84030b0409140c80119800b000300400c071000400c03500b9010360f002410710f009003ca40c0e8000e4020b12020840304000a40070030702c40c0082d244210300e160390710110185152140ca015030720030700c034554045c01308210240c402c1c0543c600300d00040280e4a0384107100e030300e0410344500204060304441c0400130300300284010058009440c1c2c14454044071501c2d010521070000340c3e510f603000c11004041c003000c6140c2014003c069808114131600079400803040e4244281018202e614601420300800c0040c0820440c908040c3c000d03014190241000249450b121070ba0406051400da02901c0154000078045c801c0284c02c0c001c1070020041200c0701201c1d400c01c0c6154a85074500207040d80304040d980c3d0014000c4502c41d080310b10440456403021940c50b0b490750002403140d803040701c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 22897982 1250 22896732 22896749
    0x60804020f09041109060111070b04150f080403050903010615080402030d0806180c0d091202011a010801181103130317040b0705031506040b0403020918030306010c02150d0501 77
    0x40c60781c40d504010310b0340b922aa034001c400c00b809078407440400803003100c081c0095041000c000000404200c00b005441c0141c18141c280a846900c0c280c0510422211102c8220420a5001d40c2041c080c1e01315035030341d030006c0c0d05090098550110f540400c0c01005244c0c4020f460300ca410b002c1d1f82006070070284080c0118002d40a40e243c248501400b56000141a1000341e00803400d076000c0d4120840c8504811382003122150300e01e181086008031007090395180703101a01ca0000d120201348803e0380911542c94018810b11541c0c8141c4c080e04000b8250341e80503c603403c010000381c9070290941000350f12250502440100542e16420f00d10080c04410305110b50840128001d480c110b03020300ca00401592145d0b6104103a003074955901c103821035030f03070f003000d003400b00201c540c000618441c0d641c5174064400351800d0200161540d15500400081010141c0307110800049d59110440c400e802000f00d07035200c2c1c82801c02c241241418070203c2c0b0f000740c4540c081c407200b00c00880c0c0c00e001000c003501318034121038140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 22899232 1250 22897982 22897999
    0x11040c030b1206010f0b07060b0406080f060912040b0903161811040806041b12050303040314091003020c03120a020c0715050a0806011101020307020601080607090501171305030406080402 82
    0x50140c1c2d07481038203009960100303191741030800c81c4001d00c80052102c1f42c401c80006c500d96032a000445c0a80c1c804c0d401c50107654005c07000540d8102d004200749644401034000a01c00c0784120121568640328601400e0041c11000030740b030049803030030442050244101602220b200d941c540540c0d12038942040e07003004036801c0ca08804c112840c58000c0c1d03801c0e140888090860340d03d0350356914a4030b04d68a0a02c400d0115600da00140301110101c440c4d0409006001a684e00d152a1800504004105480d11120b00e4180600d20460b00e0f82e100c00c90342c2024a0600681c1c8101110000d413450062022410f0300100c00001c1015040c4250050800910f1203400c0302c100741d07200c01003034078441006103a0b20001503051207581c804505ca021201d130402070605100003280b180016440c00e9a104590400c003590240004004810042000a500c201945481c011041c101400205017240c2c1d1000c4000081c1c0180c04a1840d20000242c0315006511030202c0303554544d0740a000c0c1203880111016813003803804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 22900482 1250 22899232 22899259
    0x50612010614060706060b0a03050f0708041101031a060706060906050307030b040f03031404050109020f0a080a0303020f0906040305060406060905040b07031a03070f1e08030901050711040c030b 85
    0x14091003040e15002c0802030114031041041c440b450300b01a400b42d0310a0344960002a0300040c0394000d143c5218a940c01048074600002c00c444084405072003541003100c1d042c02c00c404103941c05100c2202100034a80814404040040e152150b103058407076039401900010668100a210b40c0003400301e03403908005118440d0344804040c1c481049100c040c1140320b01200190020321019105915684207040000b40c1d220ba110200f000403004032402c844a82d5210110030961030241c049104910303080f01c1c130000302800e1141154590b092688000c1c141a004100840103038a80d03404d858214402034030058503980e0320b0600320341e11401a1400d0350300c60724081d40403840070b660b0301a46208541005003400c0c40d1304c0302d60045009003075019030004540080200060595130600030680141800175a1600c680c2c20011004806107030201c128014107040802041400d6000c01611030701c0b2401d0034174540320300c2d0310300344040f4511848020991052070301106600254041d0b0021010500507280325800211 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 22901732 1250 22900482 22900519
    0x20a03150f080f0c0901031506081204140a03080a1805060705031c0501030201020c060702010219121b020d020405060d0602070302010204090c030e06010e1003020a0305030414011e05030c0403150506 87
    0xa10b80a9400c45030040060000c2a06001c1801e00b083c0410f1000889d555590851801d085060204840d086000181003040e0303112000c000343d501c40c0882e0050402446c5030754898a91140325480414800140d080000403810005403200a02c0054186a503c8020380341c1581c680c0c4c4244003400c0840b42a807070f030003c0e4619074880d280c1030720b03410f80040c4603500a03002041110382151108038110701c290b0071410250720344140c400354110b2041c02c0104a100c1c04d2180500700030401c5085c8442c80450265800250340c074010280e01480d01650300082980300d0f9000b1480f1b000903c04090031050002030041300301541540280200d51038580100600d03040c001703013101030359881c020500c5250b0080c2c6c0144038180080711195001002c0410014083e5580d902056202d0141d03801517456810100b0108003a09401d110010590400d18014004403e108203444000200d00046420804040001800c0c02c4e0b040c1c08440245410030860181d032a442948100580310842d0760502071000c2203000304003000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 22902982 1250 22901732 22901743
    0x605070804111917010e0f0312060d02060c0607080a0b0a032001020f010606020601090c05030f01090e0a1e050d03020c030405060903070e01080d110a08030604020a03150f080f 77
    0xa03441010780808000241c208402810f21030207034420a403101c3d10005a000180d003440c0107120040d400403941c800380b01a51402c00701c5a10103c04030fa00104404d0700e008580a00c4154002d400f115404008030f600d001041042c01503122143c030074402e10003841071868000e090184242c0c2c1d0101c0a11050500009001d0540010b01c001444181d60280f08280304603840c1140103c031506104860507081d00c450554291000c0780d002a025030042001404040345500aa501040d60340c200903296003071205076902c000030144141340503144d8a0034901c40707002041c01008036840d04211607840314414403292002c000d132581d000701c506209805000030f5190003030080c4d4803500400340c059820a8030700424400d032a480403040d241e05014035580840c0c14103000103114060300380d0351f000781100d821020014202caa410340c04201180c0c44000c8603030018402004a0b5406401134501688500d99404268081e04440b80d041c3e060a08440d00413a17041e0040080d581102c0c0300104403621071100002a503103a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 22904232 1250 22902982 22902991
    0x3110d0903080f030402030f07091a030303071e0c1505070e011107060309030507021201060e090f030a0c03050d0e0c030d030501050d0b06011806031e020a0c020f150f0706050708 78
    0x82505100f43c54104a2000246034071900240036212161584850380d42000025080300759025a00d03107000c0421183d800e6601d1624600b54010340c41d40c00d120038040c002c20310f401000c2c3d440403207441041798418850004c40c0c158581c002003051194207004e1074000649001c81d02440003417103040e4004030710745c814588a61001041c20181c207155040840480c054509888260b0034024100f00210040e01c030030840000c000e841000014107581014810b10640b240600140c441d984808403070482c0020200c1141d040d440709040c598031729141c0e4035065500d4080c1e28103003070006291042000403000c0c04944840d03a0301003201a10900e11680c1010340c201c810a0096a40280d00c68081c0b000203940340741001d4000c60141005900d148036000d0100386e03001c03290860000a0f486840c050641d80300e01084c0344500c901103406509261440e00b00411004107160060311450440181d014a0b45615400c0c4142103081c9600690340c461035100841070345d01450b01205c5542c40c103c00111028803401170070f8040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 22905482 1250 22904232 22904243
    0xf09180215031308030a0203010302030c03070f090209040605120a0203010c18030210030b091609330e0a08062203080a02070804090c0f030608070b1608090303040303110d0903 77
    0x11000a0148002030342c00061898071205414414100071481c101c01442c0700351100308000da629070648c410b00d418040c84030b80460290340548130500803070030310b0b4811400340ca108210060700d603a60100003d0140040350b10043e004100c821a80188980208056444a009400a01c40c8600c05c07441142c2c00e0703070a4185841500c005910510061500c4490546e1042003440e01003180c81c007880010303184400035200500040c6203ea0310115561300003098400070052200f0340c04041414040e4202610810028001400030f10b0b200301d044c80d406203803041c51110000c3c14508050380c4803801c85503961801e540708070322515941403007500094581c122902441d81695001d80d141c40d0001510040d4200d80002c07103040314240000f10f01c0302c120b4800c05540c14026640c12401700c0d0300003009002c075150b0b13410004090700400740600c1214500c1d0120f4280010091220f000d030030081c108400c1d10302450710211f515002c0010004103050f406142803606c00d40a100382c4005070f850b21020b940d480d60a2100605 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 22906732 1250 22905482 22905499
    0x1b01050f070b04050304050402040f1a03150d05210405030106050a05030a030804060905030f040612050106080106050702120d080601020f011e02070f0501060303030e010b180c030c0f03010f091802 86
    0x694840c402c540092040048904103611000060160380250b003045075a1041170030100701020501c564802d681c140780303580b94074600b000039284010350340c0620041d005503551344880c1c0030840108140402c026800011035440400c12088001d607a000f072255612039800c0010119183c41c0880c0b000301140c0d0300400605038500c940e07800365500c0701b0042080d01c016580e0944000410403d00061003106000c42c026595142800300c00b80000c4400f00041800a00c4c000c01480b00c183c125400e1415104182040e5480d6101c910004c0c03a40702c035408004c5094081c007144d04105d80c0c1c00c02190b40c080e2409800340d81c4962a840400d60032a00e00300b00c940c0034103901d0b0491030481d4240d58018000b0794022410050f0f240c2240c1c0b203403420b4820303580c01103002079503403012420344031420f00c61441c00d56030880d04000380314520480c00e119010094003030310f0b02c050004042503c0425200840761080d01e4440000e88a680d00d51a900103200184101c080352400d02c00d8000300031034195200b0b150154008c2c881e56 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 22907982 1250 22906732 22906747
    0xb01090b2517030610030b18090a0f0b040c05010c0b0105010e01050c0303160908010b0102100e0102090d030504030201080708090615120a060b030708060106050d18080403051b01050f 80
    0x444a000e1403540c491000d46041c03040125521004064030454100000380e40d90070f102080c4001801c6910768801050f10b003c1d44820181c3c0c582e101490f4620407000c42c22a01d888815006041c0036043d1402040500030f480088204580a402103105034003410200080c240d907400103407803401450800034610b24140380184119070181d404e807220050103240c01820300c00d0040e2010b103540d2007502c10600111a4824070700380035a1012600b009004080002c0c4503036011880080d40d26090044c08e0200140c136001c9030940211300358152020102c008042042041c454100a8010340c420b0000368005060b01002401036805a0030035409400780c280188600c0d0307504402c0340800e4090a031031990000c1440c01d0020804010056a41164012030001030001e500a080602c2c0041550049001e600101c0c010484241c0043c1900c240b0398032a0004202d000d003800c0b0000d1400c010010041649001060103c00e0040c009960303c148040742c0004286405040d0041d0b07081d005a4902e00004081044600c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 22909232 1250 22907982 22908007
    0x4050a05161103090402030a0209040c11030405060904090605010b040e0f040c14010908030301170c0d020a0501050c030412152406050c01140408130f0303121e110c010b01090b 77
    0x116810710b40d501a00d04144030800090140e0b84166030041c2c1681d00415410b5040c42d261285a0094400d4140000b101b40480403040d00ca000724400e5500c10140840c0102244e01c42c1d400882440d5800036013084190f0711007102410b0380d081400f07031800301003294000030081c0e010024000c2c01103400070442803e05203002c0000000c841d0200903e4104501c0a4000078002020000382d4080c0003940a10321080c0d520110710b518140d400e0841e18421915601c0318000b41e00d8140400081e22400e1815591790400f030081c0b83d14500c1a0b50043c00c2401ea905401018070080803140043e0101078242409000e945446004403c41e403c0c0740308100c0e040c00c0508001e0180503100412105000b10700204441d019035940c0308100384201c0d01a1207000002a8040110519207003800142c4102806910b803181180c4005061200d610007000804d580e030444a00d002010451468000444100a000516030b01000402c1900700c010036400d15820100b41c4200ea42c0180b40c03003400d49010035482402c02c40080078a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 22910482 1250 22909232 22909247
    0x906051e03040f0f0b071103030f060108060307030f030306050f0904030e0402090103060e04080403020a1d01030f02130f060806091f09020103091506061704050d0804020303090d0c0504050a0516 85
    0xc4a0401420a08100140188460191081c024031700c4200f286498040500168200340140e00e064008004116081900e03c0e903440d0841c10070b1030000c219680c5e41001c2403801e00070360009403000c01403213804002c1560640041050f00c81c265501d001d51203002e0144002d84805840003004180380003c1040d003404d16501800c9400c905140100b500c1d43c1d0399800d60300f00f90007510180d400b40c00000c2c0500a41c10b101c40000d005040d140d495980c2c150031951641555081800b004000c0e84125000005658074900340071001c4c0c60740c8004101c51450210407100806461048108038020800046c00c0c0c41000325207200e01342941032100601030340c409681c0004141e4031070304906050756014800c020540201c4003c0d4100a000c1d000115a407c18001924060142101e00c080300781d90b0042200107a0301091928594256051030003094803584006401c40c0a601e1585400c070395405402024072003040416011213900ba1020800e6403500e4100c0380c25201d04a401d076800c511202000000c0600c01c800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 22911732 1250 22910482 22910491
    0x50f0102060a0f0b1003020903010e07030506070f0c0611030601030c030506030c01030509030409020313030e03070f18110d140a0603260f0715180c0b090a0305010603030201020a0906051e03 83
    0xd4480300413400101c07084100424100007a601160300c6001e0308013403050442030b051010040900501d10359134542c1c0e03500b00610349820028410138945006024200005842c0d81c048814401d4003d032161600440d00100d5003140080c0c1006800781c0f510b03010740f081074054180900580344032010340005502030320001c1d0070a0b03138500c01040002100640c5202544c000d500b0b81e00c04404400b11030800400d0100c0c40200c1c188682c111501c10010554600302c46822175081802c0d051451a8001800000340744a40f4950800714000a210710080785603030004e14034103594100b0031015210008808100c0740c0c03500005240d01201045500140440d00c411140a0b1110765114500b0700d00118003121508441022900b06d13580010900540300107010340c5101032102820041800d000b0745907461286100c0c420002803880014403154135403a005004c001079604100240445a42d92900a000b0b50260b41040c0000d1900c000100b143da102c1c10440e01c400164103583e1a0f84030009400c805107500150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 22912982 1250 22911732 22911761
    0x40c0305251e110a06050402150c030306040908070f050303090d0207081209030a051014012909011b0c031b03030f0311090409210c02030312060f1305060406050f0102060a 75
    0xf4800361a40100700e4401c1843c4140c001080b18141481030001d6540301c4101603021284c140901000c001000080d240d00c10310072035001c40c56101c0c508080d07401e489043c07000340c03019500e4181e6000380000080158018200c43c1c044490031040d0b400b040303880d62141c2c010215070f90004035000445c104240050072070840000c0a0305d02c845610346d00e092402c0c141c0391440382e18607143c0c0d0a02c02d9806601003c94014078062001d148030104270b4a1200314100158501084941d000c40d540c60141d10520f10550f01042d40c40e90700c904a445030510703944001c0e540c4004c40b1811500300c1201100321110502c4003c8030790503141d18008070341e07080058014051200c5041580c90090061110715902c40c000e01107150300950808901c42128011189a24800c0c5050700911134003411620068800000300c640c1c0c13040c100300240c03c2e43c850300c001408417285c425000b6132161004015807040c200d254449030040c0030840e401c12505588409200c00400c2c403840b5503016030032031400100f00f514943c20064545880e80c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 22914232 1250 22912982 22912997
    0xb0a140a030c020106090b01020303040303110c0706020a050601090b0603040f060b0a03030f08060a060903060e010b0315010f0f060807030506031c0201020909100302060307050a030b040c0305251e 86
    0x14414a464000500c80c40029450b00c80034603a10f42c081c440c0c0380141c04400f03000e010880280d80080c1d520302c80600002c08241da14020054041e40010a480929161009660800c1c5c2d079001c0c000d544411100c0140c850b40030358000028001d6941c411380000f110043d01c0281142d61707540b1001c42403d510342c0c05580aa032140003004142e42c5051400300039500c25102c1852021254100814400c00184440d005061621003403101a4004a02004682c0d0021011a00144040c8106d002d80020364030260144140705031340c90b4603450390700c604d4182d80c0d030810040141540c45030b03040d0a0340708900c0346c40085803c1801080e046031007900060381c00700c00030741220a080040001201080d049601801c0181d5010030000c0140c1781800700e05800c00360082c07a120713000d411500098420303c4043d1407031090080c00611080300b40d0090f0081500814000c00811100284020140140c4401c407900e0b0046010005038200d2000182d6402c1c50004041e0351b8080c115400030b0002644500c0e10381141c0030b00442 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 22915482 1250 22914232 22914257
    0x40609120f080906090c0402090604030209040c0513090b0601051b0f07180209060a03020c0718061401080f150105040504020f040618030302030306040908090405090f0c010504050a0b0a 81
    0x402403004606031665250100344074001002040030381c01402c010704a4000318103010002e03100041d48117243c502202d0040e45d13a000c8000107a1940b003075910003500031105200f04018000c804410341e04807042982c03a154040b658003028411944083c4000345844405d0300418a254400c8014052144a076040010b50040f920740492400d101e9185858069100390030501107020300c00c0807110000c0340514207509000e074400000345503001c2e00040a00705580443c074401042c0040100e41e00a04d4000c5259081d410003900481c06040b00340601204481c119101010300d510485151b03114034200561070001382c03641c80f03039011508142d03000d17103040000c188404a400d0780c40388020840c003071048145aa49502d4083c2c05064402e0344040315034004034480040010a401004507980007400f198009110007aa10f00a0064006c0c2c2140c80e401c1442c020400c00a20350000c3c1408040c043d071400c45990300340083c01124680704a000c2c26410000848080140145c92809468220118203241030086107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 22916732 1250 22915482 22915493
    0x6081b1b0c04060f030506010b0a0216080102070302060705040311040b03070519030506070f02030403080c0709020d0902090609011202090c090303070507140103020403030f0c050106080d0302090108010e040b0609040609 96
    0x15030294102080e009401540d640c0e25003481028020080700d820b4030400c0c0c0c6991516134031944144140f030040000002e02c0d401c0b6074402d00425400c02106c2110721001529140824000d40044004502612441010420260013001031b40c0450341e105800114101c400300501000d40b03803100c1c04603010700c50510086881d0769160300d030402e40c1c07284030005002e0b43c1c51410040c3ca805000b81a90081c840b07007079000e426456001c022502500d400007003850344c818840c1800c07407500d50103034090150a40f02048038503518019402c400010b9008803100c5e02d06448490410506400a209444031500006118001414080c0203503034000c40411065046c401d006003c24210341c0480702c00c550700e0b004250180106611184245030905c1c00f80381c114246410f42c2e50141448030034400c2d0400f4131030340f00c0400e03080001c2504404050801101528030410b24130f0001350103034122507215404590300b040003065145d408111184641e410142211140d00d0300024844072100151050361141d8075004c90201003003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 22917982 1250 22916732 22916767
    0x30f0e0102031801050105180c030403020c06040b040603050604052503062610050402060403140a0501090b010807090921050d090b07030b010e030d1202120f040303060803030106081b 80
    0x1100118425042c8001010f582141e40580109102d00c2021082403241103c51040301e0b4062603620800b69641ca4908050345012542580d803a03100100080104070352203060050421607030161014051610b8040c00c02003582c40c11a40c42c0b160b1030441b40708101015006180040044a50400107100d6442d021f420311043da030241500c1c81080c55910741d40f10b1407030810135015080300f12502040320b420703c1d40c0040d2043c840da00c0080e00c1c030810200700030b07680b002c140503001e01cbc25440b80c0204152002440c118071021400d2141d91302c140591800060f031918a401100314107980300200380c03080e10034081d02440b02520741c0e411008208007071200d1500c00542d0720401c00054011140414545070043c002401c5e12654042c0c14100006074440c614a500c1c0011000501509420300071640030002c0110b030000e0041105108a41c503000c0b080c003100203d0342c0c9442e40190b001c0d5405201d80c80e101d88840c5c3d901d100c280303c1c0d0390009100000003400c40001d52411000ca100840c007140c41c0c40042d0b020b102040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 22919232 1250 22917982 22917991
    0x21f0605150405120d0e06030402010e03010c020609010b010f021002180604030302010b040b06040b16110a0e010305060903040e0705070807060204031104061a0702040911150a030f0203130201030f0e010203 90
    0x103507800101400300e860003813601c003c54a010701c0144a01c0262100003007007042180314884c0500740200c085011603010b41e0340d803048120054002c201039005808002e503100303c00e44010f2100e510306455100254800c504d2a40301500306d80003446c45008084800c0001d51125950445006040200c00340569852005100450007540081120b018020801c01211108000781d4070540041004212607200c0724152000d00c170103190f443e441c1010b241000c020301d00340e101c101c1d98007a03441840441d100a450030654180d03030040c401c8401d41c3d03450f01c921685c0e03441603006621401c415040000d41031fa100d03c0050040511924003181002100c1d0b5458050f80c00c04c1e001201c000d1106104415070b802e081c85003600501a40250000e440c2040c411954588035007d4064082e989807000340d81408a07618440c521890050b24894010411a0f85049c01d030700202c085200081c10040e42c05d40d808000d0080c1d034040c00281004641420036a80150001c00042450010003512807507200c1c504482271001e075205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 22920482 1250 22919232 22919269
    0xb030f06090106090b0d12020c04020408031e12040b090a02090103030e0f03070609120206160317090d09051c0c0e0108071a0304060504080f0301090209040f0c021f0605 74
    0x450414110403420340f40d10b6040300f08143d00c1c010400126603240b00070394050030f0300181c40c0407102c0c00301e11080303083c050000c00e19900540000380014903510000700503c105440c0c52103480245418280110345403144803d01c1200310607444c086030209a1001d0001c0e0001c41e14003c075100c82400398085401c8803402d81c030950100b00810200c140600f4501c1046000d10001c50241100c0f505051020300400e03011301850415450f0200b42e4030454684004451082e240c0840c050400002c0f0728004102c8101401e28500c0c0c085140701040c00d0050014554944500310b407110100f80f0b0800e414070003003040000703400040200c00d1500700c02041e145140507010300f107900c003003072800e40c10f2104040c58801a0703800411000c0809544403603c9501300d00f66908968044000f144a03100c03370500075110700520380d0946086000000015107080c060f40141fa448105070340902191042803c1c0b08100c4070300342c29050241c3c00c600044c035102c809496003040210106440010359a4485010031a10403c40b4240c500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 22921732 1250 22920482 22920493
    0x2030403050d020715020604020102060a0b03012d1410120213050a0902090c0a080a0c030e0d0206040b0109020702010c0f02240c010e06060d0f060b091e070e01210b030f 74
    0x49001c0b08902205594106e000900140c1020342c0000c4d96010010040708405a46000012182d5001e400c1908035102c22034140c0d03891000801c030018001154090710f0195458184401500310003080750030f00c503d01000021014600e440c04130200c980c0d003902d040764404030706001c0345003070300c1a0300c40c039402503641c1100041c1600803441409451600904245050401030103001040d81d4010042a40b0140c60740c3d010480e402070000035405400c51407540721980c0a8000702048642d8000740c01440340303006040d00489640c1e2080e1510481c403c400f0080e000441c207032400404203031541d100004992014001018038a030f01020000302d0b40e4814074052800d54009a40c074282c004c240105034124800c03501902c0e00742003200025035090000307d0011300d5030550b1b00341d480134007941d60b000b40c0701b612005d05554014038050003503d05064000800791402d24001c0c011031010380c0b04801c2e41d01e028006840d44401c882c0070b241e40390a680040d003000300000d901e41103511119201444400e0b07128620400070030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 22922982 1250 22921732 22921739
    0x90901090b0106050c07030204150305010c120c050f030408130305240f072f060109020c240c0717070506070807030e0604030507080d0608100e030301030206040b0a02030403050d0207 80
    0x480180706070700040030004180850a03c500d00460010101c960442c0c1c00180300c5102c00b51030415003110f5002403c40d520f0844d50020b841d0700034004001e244859802001078410100e000c0e1446d005215100c4203d56082c000240050711503801424080c3da1039208040c419529980e151800c8010172200c0750a040843c0345001b80e0760905800d0b5000003400082c5280c51410000040800030445158480701100102801880788820440c9000c0d403a0201995529a1600584800396100000c418060720802c20003500200c880c0302c50350301c00610641e45841d56140c03000c0039600c0da0440e42003030301ca0088144a849a2049600c0140660f0344208080c03e080d1606c1c10010b8000701e00100368000341403c0415001c2c130070801142c000c0c1d0083d458203010b03803100681d09061f105805104140544d003440d142c00414010300001d010708252424800a000319000c1003482c5072079000030700c07000f900700c803042c40b0501c0508900405040308481d0b9204480c10720b580c1e42c0f074a92a165883c100c0d1005604640c0092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 22924232 1250 22922982 22922993
    0x306060906090503100b12030408010b18070906030c050c0a06060e0f0709060c0812040b04060e0708030319150609080606010f051206010306120804170109050307080c0c09090109 78
    0x30002003089091120b40c4616000c0482d440303840f860505c0000c140d44511000c584c2d50380a4132900d960a01c81300300c81c1c0340e54070303003803880e0003043e01401041c0708905000c00b42c3c041503003002c0b505100ea07040d591104130084c54100160b001e4140c910324002808000d10400d81c90340d00401c000d03032080f8001c3c50040341d845d00d0081c40302106078000c0c0001040c480c130382007004440d60308920060700700c5015152881d07542c9202d08102500340a00a44818015031a00501040c4900b070305c10701d80100d0180781c04002c100b9034900f41c0c0365100c20300e103d01406504103100065403550015044078400100c9680412220017802e5a805c40e140e150300800c1c08200034440a000c1e06404200480d840700003030911006201c00d00c803020707046000c0c00e081c03d20005140b00000b035003079100b50046001480c68120000c213075102441c244c107040c4c002d4029242d080880410310400c00d801406011f0080b0b0700100135500d016015169000194480218146a0b2041030b0130040c0c16240e918620744109610f00001407010100c2c5000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 22925482 1250 22924232 22924247
    0x10e13050a022209230115060f0e0a12060b030f07050f0a09020a020307050d0206040206030112020a0b0a030e0f0601060915020708060a0609051b0414040f0906090c06050307050403080d0209030d030606 88
    0x142107840c1e02d04249400c100c3e03609100c06080c0c80c6141030100107003510849c120b980b0200e4044050700f1003040000000c07000c0ca05417241c08a03e00c246424400441c080701031540c0c56841941540303065003c040c04204906041d4000b014542010704800002d5881d41e034400d0503680281c200400580c00001d80e0b030b0a2010902102d5150078161018204d6030800360000340c424007040c043c2e410403190008401045607500e030780040080486d40d100c00d03241c0910400160050001c05968456801424185038600c400400c6031030680310701e44c941c42542070805403100780c10303445401e403841903100e950008500d0031010042d05115540030340001c80c80c00d00b001c0030142035503c050710310b0b011a840300450b40b41030f00c01d1317609440588440d440480300e0125008000780140c9003105034090401e01c4c142c80602840b01c541c203c140d0517405484801101552220122807a00c01140e490000480038001440019a00300c020460700304c1103000542802520030011f400c0440d5414010301082d44e8010800856810511 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 22926732 1250 22925482 22925543
    0x30b070f03050106080a051302030a0302210f0703080702030403060908030105040c0f020c06090102070902070b060405061002031207090816030c05030a03090b03100f030506010e13050a022209 84
    0x1d00b8081945014000f600492011349994404c64032007002800d14a10304000ca031005400408580d503e082c0344c20b0294940300c1801c2c2ea01001e080e1a098101c50b00084401c41d2003005050054525007103064904a41d0407901a19240450104000c00400b080481c061480d03c50700034421250b503545000100300445401d407402d4418090304440e99052150081303100d17014854161480c503621001c40b00102d0a20216401c2a61904c0c40400c3c5181480780f01d800d41881038006440c00c1005442e41020816501072115a100c01a402001b0401040308100702e100c1d0401c00a04210031a180c540e13900c1801e00740d6035001c807040340c01c221508000b40503c00540d440208030a502401100c24075480007020340040380140261101d001000c560b5210000d00640001c111802d030b2031240d55101d00e4034540b5400c0c28428116801003010100b03500319500c00c5c000c1210b5a00c1002003048500c1c0d0f03824003d203a0128030744118001c50355066042d91140790300640409600c14001481072020010001d00c1003002e095 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 22927982 1250 22926732 22926737
    0x506010804030c022404090b0a0e0415020f09060a1805091504050c0f04060207030b06010801060512042f01110a050d1209080409050402030105070309020f04020904090606030b070f 79
    0x307010100740c004115448850301940e40d6005a000f072204404400024950404607000008001500d24007940c00010180e10032a812580716981d04c88440c00c0090954028140c103024141410041c1203542c010440088203142650805032800002100ca8001001c0c1d100440c414210054112030412407000c00b500e021124215203080032181429440f0b039100c416800f0341d5031131001c81c440c500a00f0644031114051501d0f20303510f45c3c481000940b00c4c00d40d0720045039001401808242258010399400b81a40e1385503542034108025001d90011455005d84280c510002d15502d04150010034141502c050201141035103030f4031070003c00140701c07d200000d0042190003e2580b06d002817030124516280c40880d182c400092001c2c15000d0004004c8214018000300c0700150010f4269107981010f403160340210001c02c1541d075018000e400b5111204002580a64040c101070795500e0198085c01d4030302d201500000f002035443d030300c001c122001e9401c250341d4602c145082006590748030344200822022031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 22929232 1250 22927982 22927997
    0x2040b0306010812070303020c0a0c050112020a020606011d04050c1909030803040303151206050a0b0613170a020d11030601080d081605070f06140108010b03060402040b0d0203100209010201050601 86
    0x20846031181080031420790104c0001074003038141403107901a0368040f840501507580ca11064034000012440340d00c1540d010030302c290390700030200010307100b5034035001020b8018204a80d5410011141e0440341c0002c6400d0b149802824003030303034440c6d100b10f41c400d03600d40c0742803035964030151a41e500d0045074565000c200008100c081c40000c007100240d80c2c001c1c0c0d1500700030a440c1d41c041c1c0740009161060700841c00c0c00004001860910150343c1000b4001c41040c041040104104400d0100901c694030741c0e08414014604204a000004004048102c14410903030b01031440039400141000d071407040030307180015051459140340c038080c4031640c0100380078001044c000020303290240c11220010409c81d4207400680e41d040150380203d04850080e588010305449845141c6400710043c4040d40c41400c02210850002c1958841407290a080407002030090804e80d0f01ca80c00c00003d04a0101840e401c69090b10240340103072400c000b00800902c00c420007607110b8008100080c2161030092815040103c0d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 22930482 1250 22929232 22929239
    0x30705060405040209030a050f010b130605030a030f03060b070303061406031311040204090e0607020609030c0a1104090f1415011a1602100c0c0b0f040605070f060606090302040b030601 81
    0x3010210303802c0760410b0f140540c13180310070000a41132000a00000c0c040d40203c6018081c404819840919098002c6510f0301840469051a00443c1d03c1401641d03010740c403100e10000424050105c1c0e02800019180120702207403992003018190300401e80440100e5118002444104240c2c942c0c1c85a0407000d0350114210300d4080c00181c60200000d00240a1042c0f15141d035100e921150100c0d0040c0c00051401d110b142c80007003a172544c500c0c0c1200c00d40700501925010030b84210b00401220300040c2c1e010000c00742c50281c3e0301d4046a910202c004c050341b1640d1071030450002002c03802028802801050100a6000c030942c10710b09000c0e5143d014200b02d401d80c401809440118407200c041c210758a208a92a0000b540030003400c5415040301a501c03141c43d1b00e084c9100da900c0f91001480d140704903d0351440c0c0f582d43c89445014000c41c03401c07000d40e2106100c00d2007102e2040700036101c0d5a025288180c1304564135102c69044941031f402010000e04515014001c0d0300f8640260300c03003582d0683c01004298035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 22931732 1250 22930482 22930489
    0xb1207140a1a030610020309090103080c0105060f030d36060206070f0f03180b10140303131703040b12180a050a1e0515010501020606030d080f04170c07080c030705 72
    0xc020045442140b8082d585c200342d500c00c000313483c0300e0030010300120001c0d610790400d1451604200c5401d01c00f90700b860005029070800e0540c205841c0380280090070101d03802942514510780e59030100e10784917100074200749804600d0044081910390300304030b0210030303080440c02070405000078400740c24041000e900c042800e511951a0912002174030303000880c45c0c02e46a01004c130586640f0044c241c0071211090001281b0031540940480d504807414000e187c00d00c6045c1912030003004403108244e171610008014400350718024843e501d10703041c1540d01e040e850369071350300d03040e0032148400200702601d0b02080b544c0720b402100404410300c031000404251000d070351550341e80e0054a10050800c524030381015868101e20341c6441002ea03020058807039102c6082d26a0b072008009205050041c4100710108000e1308000c5070217040318040c0d82d9030113400e50b50000d19101814002d48200e40c0908100c03410848000100060040f825491000e00240340c50104017615100300190018460341050008000b1070344c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 22932982 1250 22931732 22931737
    0xa080604050d0309031407240b0d0b13020607060203010f060e03030a030c09080709020304060501050603041a040302150906090601060302130501030506040f060b1b07060804060b1207140a1a 83
    0x2c01618011500b2140c0f07207011141d0b0b00124001d007031003900100b102020801642404014150526a2a11141c00b03150000302503c000b440e009400a00c100042004034401c51801540b060b10410151401d079116404100d00742d0004000b920000d41c00300c0180b040d003902c074600b10014511407030150881d00c600703000030391a441130a445200341540c2d4110010741e40c1c011925a00249108020364002071f6070385913948060751080358221100c0c0e144c04004191483c1842c1a0f034022600450340b10310004410410403110314001e801a02544510307420f00f4043c5900c00c5203030307101d00c03a41000341c02070781401d250451030300006800400606006100d00ca010080f0a000314040b581d0900c4c0210b001c0e03c4100100c1c000307000c071402c0002480d0602d600030032004040e0300184107a05252401c41201d0807a184015200c10b41da01a08001400f201d0100e0041800c87c0c2080f8141f6200030980d118525039212580c1c6000b01e04d5124180504114455aa4620300004690300500300114200451359190f01c1959091 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 22934232 1250 22932982 22933003
    0x1a19090e06010513030b070c0501052409190510060806030a02030c04090f021003050609010f1802090402090a0306050601020d050301050306010e040c0b0f030a0b0d030905040222140a08060405 84
    0xa00402c820042188130341c01200115040401c04400d803c1003400108402c0b5144000c1d41d283d030801001c103100381c0301c40020f24440b4102d00000540c1d14504070400041c040c000e442c40c01001085840c803a03210415104d40c50081c2420b00e083e04126292603c00f41030204000d00300741c441d400c000402000341c0c44c08100c1e03040110086400085d14002d500e4000c44214034404065001150040e8440303120f501940040d020300c200b00d0344a03150780c0e030b200401080510710740103101101070748010300300300012641c0240030401e10090002d07062051280120b0f052282d540e105031038990301c1c3c0c41840815601441161100c01e05882d00b24515814107010954900043c495801c0248003040002c060210380808440540806034550303036951811300b00d80c080383c4c100b40d40c2103111f20b15200b040c0e4030364540820804061581620380303518103468482004020340159401c54031040c0c0d042c01e40b6240c002500c0c41c410182c8282041080083d481d072080c00151030181e001043c00341d1102040c0008544000707a1480b1a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 22935482 1250 22934232 22934237
    0xb0105040212010b030702030f0c010507031d0a03030f0f0c090e0106050c0a150b060a020c0f010903030e0f0301020f0c0109061a010c0803070e040903050c0f03040b0717041a19090e0601 81
    0x880e186c42100f2440c5100c0c44442c8024001c01040102400b070b0306400c1640220865541803000c10a001c40b280c030b4a00d40c90111150950142e040d000009000e1303000703580c10035400c04001484e004642e12040903110458502e000085000302c00b0b02258009051443c050102c920380309091402002000b0f6a600c1c1c0b100303001d000300c500410720004842040e0132078088001c010b4801522002c20600180d50f801c186010359110b000e024902202c1c551007802c4c410304494160341c4c1c04042091007018000c0242003450310a4040d5020004105594a4200104405803c0741c00000e00c403007460400d142101d8150304c901440c10301c483c4100f4289d80e8411581c11683c1d4110070003994030313201c88400b510300d01d19100308217420504040b801410305411401070300098490105841c2100001c105a41e1a8810f90140800d902424080305c00031641200d1040402c00007100342c02d1906072078604010103003002c0c920700710645900043e1844008100e400c03800b0110340c0b07270800556040c10124120300484005201604 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 22936732 1250 22935482 22935487
    0x100207021302040f0f05060a050a2001051f090204050105121003150203041b03050d0507020a0e0901023105011b0b070806040e060108060402010f110d09030b0105040212010b 76
    0xd540c0c41c000e18036640000c4040842d0703903555800c0d540c60340980c544960440100030b0240080d490070004101d4a0052080d5030307a0340381200c0e000303065940c850b03142a952400e07002041d140408132000d1060728040d2100c40504120700030404904c01210340319070071044c2441e005000800659801900380c80c0703400d00d061454403171b6588407801240719040342d0740f0262006030110900510341c5603940c0214040c0b0700448140c07007140207201201310325030300c1340c8001811030384044039905c56035224001070303c680e6200074000118295544e84102e0103907015907080055075400a8140382010402102030190b0110101030900000003400032650100c0e2407113024184480b0400c1d20446000c16002c07040e44a43c0f00e01d0865441c204420010030005d82142c1c01c5000b20f05d4150502d01070140050014101c0f40c1c884010b01c0302d03940b260b0046580388222076000d400c0c0145046045007491060040400540807551000b80c02403070350511842c6501c0603070000303028610400c0360010b09040f518200d81540e5022005d0796 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 22937982 1250 22936732 22936747
    0x2a0a03020306121204230f040b061605060105030606030f060a0506220b010809010603020603010b0a090302030f0a06050c030702060a0b0102030903030403030806030601080105070c0f170a02060f0106030e1002 91
    0xd80f201d98441c5514a903005080c0c000a014000340c01800940301c10210150002c200074180302d0074030380d840c8803040e445203549072401d0152809820625030b40030050141401c00d6401c00010f0b0a0592a000031501600a40018030071070074104022944158100c00502d600c0240720f8006071103140103030050346429140d00008406854030f52003c01d0403009030903001c440c4642c0004460082030100502d50000d81070001160105005015440030343c0d400400c202e2640e443c01540e811650b003c1c050800a102c003001c0c00001503a02441600d4030341c149a4007920072082e4038038110040710001048008569014018001c5155001a00503800a5542400937040c050000143d1542c0508003040c0c1d0b0604c0006000700030140d00401030790060340150100c42e401d076280c042150984004480040c00600003030002c20115010f505410b0041d406400d650000c40e5504c103e00c0613a5006402000259000c4005d11465404050141d401030555140c10844680109141d944403a803200a441401c2e0b0041400e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 22939232 1250 22937982 22937989
    0xe010e06040602160b0a0921230d05031e06180a06091413080f0408070b07051b0f040c11010905010603020112111b0a060906052a0a03020306 62
    0x2194010401000039445542e0ba000007035481c510302111090200c0d9940300018402d2040d02590030300030603500c039449030342c0c01c148428030485000c9a200f230107200c0c2909460041400303407440c043c00070b5410101c200c41d881090580c038580300407801d011003080410820001049454605090804112034803000603844610000f1101d0101d503042c4c906454007002400b00400c016031002044445140c410320605070b1581c8000da445070101c41f40c1c044030184260680016062100a0004030300381004542415140c00300c003803502d00d0941084012490014006046c4030003000190742e42e0124090842d103290702200401d4009a401c08214015622001c500400702d019148010060107031a0003003144407200d00b0041e01034041d40c4410f0b404203030002000030b5454003d0140b1105080c41107080c52401c0c10411f001080d80b0b412007a80c031010302403a00d4140020720075000320300201c2c1c043d50300031405040c03462440720b044503007100d800c04409103110f8900c0e8811440c81910714080c52030a00580300c1c0e4039000403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 22940482 1250 22939232 22939247
    0x4080c1002010e010c0806010207060302180607030c0b0c0301030317070906051b160302040501170a02100302071a01030b09010c020604020618030d0305010602010c050315090405011e050105120613030e01 89
    0x220f1080d400d100e11907200c181d0202001f13103d031409900b141c800303680d60007050b0201e2180b41034014550a801c001c01c04103003030417402081d506109142c5030342c0302061600c48080281003540c11841e40407000004100381540300d946500c42d2000640b010300c550030415000b900c1c070030f4244903510902001144d4991000f1007205610214007001e8107680c7c00400c1451041c024480c5030001b00d219614250011405401180100b168114928000d000301d500710b4007041101001c801c05081010f4080010400141580402c035049403002008000e05504610b041c440c035400c000d101d128207a142940d8411000ea00255894000350140c5819940300f58040c0e2111034801c0481c021600740c03140010250f0a540d140d44158101e5141d03600800c0b01c2d0018110880301480240c9a807040c000c2003400200340c07403030403140b8240c201c4d105400000c1d0011a60b8403411484058180c200746060740c800c010001c40c00c01540c220102003005000c0d01940ca04680003604960205101030104007440000c41c02c1079000b840c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 22941732 1250 22940482 22940501
    0x902060409060609150804030813020a1505030403030c020c10080408090a0b0a02010b1c020112060e0106030b030c030c010801120309120602070203010c0e060d02090105160b0708010b04080c100201 86
    0xd102d11070301c6980c040c00010b050701c01ea50344440340031144403006115080c40341c0102c1d0702d80c0d2000000e861345030408140c020b26641c180d23444480c0ca407000591696945044410100948805441c0c1c54a418080c1c21107060500304000d64008a00084096450100842900301c00303017040b883d503407118148203200d4051032441c981c004075a204e0200b0f00400c184003030902411540c0c000d00080c0b12650510840700c04255404d400d410700781904000541c0146103001303814a034900d00140d40f82e41d03400d5101d41d01e0001c0e8448400710b540e40003147c400e13003014010503c9041e8190000c0c401c80405100003030031b8820522903c6201043c0050000400d44142c854900800000146002c40d040c01d00f400341c001c2d800505c00324032a62902d004203030420300801d00d10204501c000e019504184231028481c02175800754103020704210342013284151500480d1882141207004c0c403010043c40c0751058020b0032004041e080000c2c8480c042c001003041440c00603c0104014085e110f0200740035006170700b6805404040c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 22942982 1250 22941732 22941749
    0x10b030303100f090204050307090216050703141b0d17130929010c03030c0c020306100305070b0301080703030e040f05090c03060105010c050705090402120307050c040f06060e0409020604 82
    0x20601551803480d6a0703031015030300e60402c1c00f41801d5440c00c0120492003244203460700b50300000002c000440315a030217491a20707241c800c0c1e21161070a660703d59080094640007240d0307140c046c5021800c0443c080000300c240d4080d241e4410950342450001070804e6030441c00040c100b0300d003010500390f4403410780180c80311032001d80c10544006450345042800740655401000901ca8207603c00040715080c1e100920080300c040e1204040080da039102200a0281c84002c541444808540400140c6003000a980304101d0f0a2600c1000e60070b41c83c01c82d0a04071a944048227001051005200384100071401c3c000b2a070b0706061588810b01041c010402420b141d00d0f200c44201c0c40d00c0200b01d92080c0104000d1011038045040d04c680341e0702c840040d2004030b1152409031159005074014040c0d41041c1d0001d40e0490f00040c0f1030495212a80080740c9136501c0110b044450360002d607038801d40783c18240039100f01501d0b855010701c1b5103414408002c0941e1962104280300f180c40e001507405548030313202120040c04484 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 22944232 1250 22942982 22942987
    0x317070507050f01051b030105091f12060209100212040e04150606050703030b09010b040b03090f030a020307060506011b11010905150901080f0402150f13060306080f070b1b010b0303 80
    0x2c420340d84c0200421940310f00c80465171031a40b40030781c4188044034107a03000200420081d441c1d00d001e1881c41c00c0d00310200f403409101c0c54000b04036414458a190801880780703c0c096910388000e17090001560140d100301096502c81000300414001c004140c5064800c80b80c2d1100807a6158100310003008551810000c0c2c07549050340c082071079513100c401000c002c0e009841c24008801208103001031060b00344120300007800c05000c14840001700380019a04600404111640300008080090650344400c0e080405a880010f400c0c08001090080c1035008901f400c0c0201d019012030084004042c82c0d28008203200300b4406a60410307801000300002401000c1e152846c50401000790100d10360245601c03a000c81d00000000b50701c908406d9010388100d0740905081220317000204481d103a0f80024000c450a06814002e00c1800082d514207000280156507010403440e00c2c06907202d040031b103d803805020f075400c00c201c00e120300c080f003030121110140f4101141101c06d880300c413014018001c106103142d050000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 22945482 1250 22944232 22944253
    0x6050103080405041a011d06210618091b011106040503030106031802100302030c0d0f0510081506010810030b0901020406020d0c0b0606070311150a110403031707050705 74
    0x1c010700162074094904001c00581e03c032181342d0b0004406103490004e000c40769641001810340c0302c0d000e160b480140c034003404c04406501c00301c4c0110903825030031485400002006000d2a00300603041540c0c5074500700090340e0038004221a29403940c1804029149070356410703246264803c245101c044c900d071034196450350400c2d00c1e059403264420711440d00002d09022500c4500c10401d0f411910441c1e0081c161202101700310b006401940000700704c810160003e00001008401c54002c0c0700c0b01d10844400080c85140c28451406540e4960304440e0603035000c820140301c081310200d044c41d00700c00d00f42002c1d9050794880305403801164541c2c0008040f6a0058188901124150064410340d965602911303e1800d046900b26110941c8810241c400b5006d0404100c05017803210080c2071f02d40c02407410405e08080c2003800b03032520350f2660003001e029503c54208503c28a0034442d81800c2c180e003809483ca014610b0b10b0092246220100f050b07115611000402c2e60750740140d0443d041c2035806003d8604c5c5214 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 22946732 1250 22945482 22945493
    0xe0d020303160303050702010c080103060f060b030405030c011a060d0902060405120307020f09060d1202010603080a020f0d08090a0303021b161502120409020306030f12041412062206050103 83
    0x110031400c802190a040110306d40d980180500414161581d451044580c61920762002901c4409002042c40e80d070303514042400c050110086104e11b001da0000c55503004907052a40c00c440301d4a17010780b01c415504000b49050380c1d5410460380f018100d00c0c000300340d452a500000b4035030f100310f900c440c0d884180e036050408550408006040c0060007250400500303040340c070a101c1e05540c02c540d01d9500c004036507460b10021b4011200e500b00031140b803000041068a070f07542c00e41c6551001e0404005a40200e02141c00c00340100411303282c030503040c07130900040d003042c60089603501424000102413540124403954081164009040e000300d8402c111402d030344103100703858007002090094011081d0340010f01c0e0781031800024882c40182042c01a149440e1078501e01c240290400f07000160305003c1d02e25141074a1408014001190700310016083d591490501c110502c4205036100c40d000b00c820342c410004003440840d066500040800380f1004650301040140c1c02e507078000100401592405c0000f009205 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 22947982 1250 22946732 22946767
    0xe06012718060f15080f07030908040315050a090309060c03030b09010e04050f0312010504050c120106090503102307050d1107060b0301020720040e250b04030507060e0d020303 77
    0x1c0345050750586041d00d42403402045566141da104c0490040e0001c202c41c41c201d41c002ca5807011041c50000741d5815566900459a48a42c2c0143c40045809680b02da031002d0300d20074103030012081c2d54204412509070303502a0141600348240814858040707050014140250402481040c00411112056031540090006d070315040d1804c0e41c00d8400e81c4100c0300000703000011901e5264990504204070707881d000800019040007040030b100400107024410160580e040180c0c041d040980358054414180400d1501e09030301c103000341c400b40b4140703200c020412500c0f01226408000d600e0080e03003507030b80720300058580d4400d00a011104034a41b040e09142140404040c1c851030344203130710510070b0b0f891403070800d4241c1c007440c0b8020f00391100145001d42482c082c0641c03101c3c00d01d00680b000c00c401d86a110304034140403140c191007059803203040d00000c071070f65904509405403c009160500f07150035a1540c0341c0c0d5103401e0045400b44004008580d10030b1359094102e80c0010340c0101207954440e04094004c0010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 22949232 1250 22947982 22947989
    0x503091006090204080106080601060e0607060b04021605060606120103060203180703080903010c080f1303020c040e0a02030c03070305070608060a09060315050912071e05010501060206010f0e0601271806 89
    0xf9447c100001c1500c000106606049407480d039100380c240c0c5441000c00c200341c0d12480085898a030740d400c0c004040d0301c17a0b001806619003c428000e0012685d03043c841e080c94001415103200742010400d5004e00c1c40485400342c19260895070043c2c80e0340c0c5080011022401d004c00000c928031800701d0003c00c1200c00e00040652100c00c0d0001d0001441031030702075540400640380d241281e9030510014800030084410b4000060003841200d402c881580302040c110b0b002e034074a656031500103124a00030f5080400c82c40308a44005d07001050010b2454507042e444070b51f40e0196504105060700814150395510342694003030640040200805562450309110304c0b00c0700a040901c0c1c506142c0051151100441d8035038824002c0c1d4002d52078505203035600d14a54114085075001c50000b6080300002c0794091149601034405500108940d50600c3e408907602003c50f880159040d807400d0170080e403640c0c0121210104071501c5580401d030000007030503005041d15500404040030f2000c110038000e22498200300700b00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 22950482 1250 22949232 22949249
    0xc0b090c03070b07031b030f030906060f080307030914010f0807090504111903060e010504020f0c0d020f0610080a0807140d080109060b120c13030501050a0902010801050f100503091006090204 84
    0x2c1b02e00603440c0c210a840113100c0500810000340211a0072070207a00b181424902c40d03140001c2c203c1c0c5404004003101815000501302d6031012a09000f055040f55040018003140c541d00d69001040d08002080c201780d002d066404c1145440100d101c19001c1c009117005008000c000340410356080340c0301d00705d6401017500f507607014003030700f50700400c040c02031254000780c9100413040460340e800c6c6001e001c041d60010a20b002900c4082100085161040c40200d20b03401171603000e03204100c041c240d4a40b405c070004d04100c41092641c0000c0204c01e20024203028180d40c01070b401a01c2d1000b41c145010000030340781d082c003018003801c80c1d0344c082550b004e42480d042c1e403540b10f820080c05850340141d801d02d0194180104074003041a001c01d80310b004901c0034012003103c01071850520758a982ea07560070340307500355101c41500e502d50004000f1580c1081c0051701400302500d4210041c0e010302d00081c40c2c038444040c41c409000001020032030402081c0311014283c0e40420303050050302c0c0ea4030701180007544a80f0401c00c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 22951732 1250 22950482 22950497
    0x2d0406020304120e0102060106031505130504020f011403010501030b01030b090a0b0108070201091e02030a0f0305030f012111010e030106030c03050d020c03030a110102040909030806030d050301060c0b090c03070b0703 95
    0x4100e005490740904c03803034180d0081c080d5a003000c01c254003c00c4c9242c070010340d40d1b001e4a4001425525000103c907100300c0c019020071603003414414407103c0e0b8011021181403120000c1540b25800c540810390741143d009190105520368810016002401e82004080c3c0051441c0108803100c0c44c7c0b43c00c42c0aa0042c00e99441100b6540c22408038201ca8421400524008600180c0b029103507000c80714480081c0001c050310300c00320040da9050820080810b044000c51404010001840c10080502e40102000701018203050900040144450394000d0010444c0da960300710000503900c00c4035000342003c0c014008011541d20380c10a1541281c0a10045401e0f1042012110b0b41c1ca20102d0040c0c0b064074090001c6051039030106e411345000f42414603020003598240000500840d070b42c00b509a056000c2d48582005051070f0f1b040c181045030512600c400e11600b08010420070b0b91221a58504580044211815883c0d00e1005814440c80f210300396071511030381801080030201d0200804840c1d100751500003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 22952982 1250 22951732 22951763
    0x80f040f0308130806090703061e020301180e0304030b0606030703090c0906180209012001020c1b01030b03060c0d0e10060303030506010807020106050904080309011401080c0f06122d0406020304 85
    0x985c1c0300303000c480034043c2da040000e0400008240e50040034030380b401c424145401003c0029514220b070426400031070190561b45030a12140c0c043c1c4201000c00350100c01540c5071500715112010041400307404c05001d890004005418075210b40c1c025421f0603403011541c00d07c16034811844018001c03600454040010720043c00110460603c2152002c20040e141c00070003d8160a96498410240840f218555020400c1c82303500e0406100100c0d140708009600e201d00032412000408481d1080ca6540c001d50020040c00b1240308105c040c0e80c030143c0d0b110004119014031601550420040304805289d076410310b072006c410103804d50492482102c080c0d80741a090307554503408900780c81d0075101d1150440b07558404039000c10100001036a2000d82000046440c40305030740f0703031b40103060241d201006030b40200052216910700340c050407828000440b043c0b801d007a06110381c3c0b0808480613090b40b41c038049001c01c2d404210390a81c0201402001042412624034050031301c81c0c080d500490b001c032800c091229094 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 22954232 1250 22952982 22952999
    0x60908040f090225031101050a0c09091401051201020d0e070e0606031021021f021209130c020a0507140306060616030804050c060408100b030a050a080f040f030813 72
    0x1106103511642800340c00103e02509813011304c3c0441029000c02c50011141c88420000b401028021598042d000401c114180c00040114040e500450411801c203540d91305448000c116042c1943d500f140c80b84000c0c0c41c0105203034020310500d044980840d08052102a07a0440410074104455601e10400326513510041045060702c02200e19080c0d000d45490184240f01c3c4459550718a50b0149a141000702c0c1e01c0e40004030040007054100c003c0d0007445000800c52035040c0050240d61008071241070401c540500012541085040d03502100d541e200d8800c450b161003081075000c0180c01c14140c980003501d482c40001d001049142da0360003445000003190150801c0d1086800e84203c8154070203680603da9411282c0d0300000d03100307030f907580306800c0103c072143e5a40004000809192005204500d019041d080039100481007031442504044841c0000c50300c0881d102c2c1a107a0300c1448d075a80d828140c0c0680101e8050b9400c0741354405520311010080000030b2004000c81c41c80320401010b82c545c0c40d80c40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 22955482 1250 22954232 22954237
    0x80610050907050307090f080a02101d0d020d170d0c0c0807020d1b2606010305070b0c07090f0b040513021507020d020d081b0604030503010e070507060908040f0902 72
    0x9550700070084500080c011840343c005140c000e40c10703103401641241d0720b4800c00070311003158005540076048001c4040c11031030b055500400c0786415051400c150b44001000303401c40810350000601800055818008656030071201c0e140040c0d1007030b44c001c58505d8a003920002d580141201e01102448c048450007507070302500341c071007040e6405900e075403a144c02c59003801307510f1342500710882c1c1c5c1c68103c451111290540304180300150840401c0450490080c903610707440c0c03800346141110700741c00c10801400411b50120724030301980d640c0364100c2c3d40c0d20004103600d80391540f40d40c004002c179481c00000400707011aa411034000060100c900b442680c4520b0744840f1a034203946002544201d11148401c0b15a400e5006000e03114002004102e19101d9074000c103141074280d4904039a04140041d004844402600140100f141d05400030803152500e41d034040c06511060180d84581c0308420001000c5c0d45c07050f41150309032540254180203003c00c900e400b00e000d030002c1c080d203141e00984050120345900d0f68403d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 22956732 1250 22955482 22955489
    0x6010e090d030e010906050a05070e040218010e031903020d0f02150103031b020405040b1b0301030305070204050406060503160305010b01050c100e03070c030803071d030a02011812060501080610 85
    0x340141c0d5011100c250010200d0b02400c0800e0b5403034104920100d240c0d48119449001101030100701882c00c0f40004001650407401144030310702c10320200c09201c800e4550036600c404c003800c2c01820108894002440c00c8020040da04000048240c41d204050340410030b40e00286154032022016012500300f80d80354000d000200c136031042070800401c08203201345c0c40c032003401000740e0102d80d030710109401040603944d0403a07094850000e0b40c014030540051180d1307100a10361100868500310750543e50010003501c41c209000e44103c1d21030000ca000d01031564001c5004201c001c044803590081c00c0c4800c401c686242c40203a0741940f902c5103030625540210100d4191440c1880a0b0504091901581005200642c40c12245100a01505000481c5800c26401450191880b03980300e1034a48401440443e03002c00060064100211000050b00c000442c036a04a509080000404c8450401000b41d0f5905620180e0040f035411142c0040c08929442541030f85d0f2a0700030303103040c0d40c7c0c0c562400d0109a154070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 22957982 1250 22956732 22956751
    0xf0b060a020c01080a1b0e1302030919060b13140601030510090e01020d02040b0d0c020a020904060b0117070f08060604050a03120306090c05120a0509060a0209042304020306010e 78
    0x4011040d070390310955000b40d008605e000001101038005180008034461082040c0101d6100000d400d51440c040f2840304000305181410741c03941c0303000d440c09134542001c1250b002c0f0503070f014142e0300300b0022150045000b030500504030307000c0185400c0504014201c0c0d005d8480a00b883e441c0030402551081c083c4500c100e401e401008081403500c8070090052030f07001c0c0c0c500b03403555090200040c22045030008000910380040ca5507203660312800b2400072110841a03c405640c8000c5003c401619080c04041c2e0068102500180c128a03a00050315102070700403000e03908001240800c03600b150890840d41094080b5a90110f4580d036031028000030b44118010035034004100281040000e003940c03208082151a4603002c1081561034024605861812005201281d00822002000b41c22000016408000c070141800507040c801d013100c3e1103050146c00200820303000500004a521603070045410a030280c1210340c448410740f641914240d600783d404034401e0007a507000046d00c0d9804c9090b140a4030185 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 22959232 1250 22957982 22957993
    0x9020102032b09050d11030c060402101e030218010e0f060307140319050a0b01230909180105070203070503041202010903020607060e0c030706020c090601030902060c010f0b060a02 79
    0xd80040c040310030600740d0407a042d85804110302d070000d06401044400d82c444c3e00101183c03103d03a103014080d1820303845101001c1d44240700744015203030001031864001d501030310148051100c54000300c401e0800400614039070540d1503050103406505034020b04800c071044c00516448061003004423000880201407960160041c141c1a84030f160400c000c0d03401c07011034180680c0406070961108503680003250311150079070400d1452a500c080170700031583d1110500408112401200340003030030044510003446450042003082d5565004807800312001e0a0004211910518046481c2d14147c59610143e004a5007408085040d0500000c00d88010030b9002000d10b040c14100b0212001141d4038000590410591a00000c0584c8a80009040060144ac030100d29034094018031803409580c140140c2c042e1703100440401506a000c10310001c1004119441c5030325850352001200608821440603511074400661014030400540c4100c41c1d941da108428840106600200180c90180208000241c0c005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 22960482 1250 22959232 22959247
    0x50301060b1e04080a03030e06010603050f07030518161401030204050a0909112806080105030a1403090604080303011a1305100201090503040602010605011202040b0906070503040306110703080603010902010203 92
    0xc80c03146041c1d03a00c2c03158080c0c2450707940c40071140350100e01e01003680407a80e80c0c0b6600200490602095026102505044c0018100520500c01b540e100400740d4040594800114948000c82c004414098000c002280e04071904c2601076403814042d0304c1109502101060108030a5001c0c1c001d032011103e0080c20070940c94138000c00100640409001141e15000d03174a100c0b4080d4ad540800403104030300901d504603500071815072148540c4481d80242d0207001c0c840c00100240c5e43c2c00034550300c0460344228200002c0900cc010315285000ea415450303441080070401142c05103000019504031240a8090014081c400721928068450704d80d01c2428107a1541c018405420b140100044000e66403000296150454903054110f030801d410080044c2d4403407070204642e41c1d005502d010b41e013a028000f10326080c917081c502c480e14440c07880d545000f0f01e40030803084180002442510000d5130040c0e010b020702c0605403070015060388030340f80407004185c1c00008117519050505c20b008103194103030000c600e003404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 22961732 1250 22960482 22960507
    0x6070f030c02060a030b040c02060103020f13060e041407060309120507050a0c0b0306130209090103021002030f130e090c0102060a05060f1306060206180703080304061d0d0306050301060b 82
    0x405640680500248000840c0142c4500008025554180d40c00183d104007038003c01c4203440380507458a00315480900144090307521114501d06c0400100c415840d0102c06a81c000050304855111252604c407800410062040f076041c2842042030f0a81902c8205032070385c0d001e07070855140b40c00291032410740221070243d00740648001c003561130090080b10001c0c03402c1d41e1440c0311a030054011030740e0308101105100c0b4604000f01c1c0c0d0018000000000d500300421103001c2101d0010512000e0300c103410300c40d40080d01500030f004841d0326140d03e42003669a415040b442a190030711034402c9060540c20440060041c12020442c8092114143c0c0948a65248e80340218040c24016080c04d90040a4030480020341da03c003844145034103441000460703043c1c07030484041c3c10091700425803802865045a41410580c021821005581d8010302c07150301c0780c0f6a424220700400c4090110000e0007164200b905801000050300a8074420356074003404256220300c10316090b185541710342030210b141802400041032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 22962982 1250 22961732 22961753
    0xd05030106080c04090c0207030516120204020d1e0608120c1e01180b100501180905040302010b0d050a02130615030207051222090203060604050d060f1d06010e060607 73
    0x19220f1075944d0030140c0302c0b0700000440b000260303c580540d0002c1810001c108081c405842d00c0440795020f490404d20341018988038031f880d808000c0c801da078006001213091016911996032002411060706010b101200316400030803441c01654154071801d124100314050381002c4030b6200300c02c0303405030074248000a02625412405200c155142d500c4400c0d00c07462592000ca4040510700400d40d110703c60800c0c1654030b1100805804c11410046102040c41c004201e00004900316010118000384541d911705040380101843d02c42c15521403654004a424000001400564140201d600c5103103626a04a0501101c01d1446001110b0003c0100004014060350240c11924000c00680703c1c14100f100240301d8a40c0011405010007598641501c10020001c4070714026109052003145141044000a4076a0103031303104a5114901019049003008000d4001c1e00600201c11002d02c048800e840389154100101400e0101621070070300001240600c03918860700450700a04041d142084a884040306030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 22964232 1250 22962982 22962991
    0x9061404260f0a02150901090302030d0f170108070e100b03010f03050c030c090a090201050c0706170c07080d111201031110051206010e03031213060b3705060c0307030306080d0503010608 82
    0x2308080000035032000c1c800070001410395030705c5261012010340e01074085414000920302d0711048a005202d84a00001d40320140c0340110f0b0081803c2c1d03181c10360711001c0c05032600b100180c41300120001840c03500c5c40c540315054a2107101580c8241b4004028180d65074040e90394281d000144c1d0300070652081003540414a03807801858440d1030510410507103450310605500460018098810200c0c000c902c11818a070044200c0744018501104c0c0d85506185000c0c580360314115a644100c03002c91940c1450480754640710003411a1240e6035241410340d900908211418003036101554501c40c0588914200d410b04502e201d40300d815901c8450045a5a483e142040c80d0141310400002080358090740c0704078410b0790f0718010940c0c0c99410346000c006403502c0c580540e00034400381c07070003e100401d051152882c01d06522010041d40310690a2418002007a80c0241e420003400554030000501c0407000b070103558080e8505200f15565007280e6a5a808a04c810340c2c0010030a200511102c0d106000b0079401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 22965482 1250 22964232 22964237
    0x20d0e0906011b080309060903040602060408030c04090c020c03010b04020408031b1203130c0501030c05031303050412050105010306150f060309020109090509030a02120a09061404260f0a02150901 86
    0x803c540c5410380302510400d002c25500c603071004c42082074030002084001e5000b04d139500503606241c50400301940c1c41d50042d1000b0203000c40880080c80012415040e5002019600020b001102c400c01c80a034030b0b259858100d40c025402c02c0040000c605043c0220f0303045418a034000c600c6c104095a904c80f000410303006441031405461a04201500510003840c0614142a81c42e42007400034a0308500c940c20550000e418581060211a01d850700602560751024608091b00e107000f655140072503007840b55820094043d086005000c090140c1580058141da101e50781c10000851046402d499a840921640c6d0040500303800178040188a500300d030200500c1030611104ca907445804460640c2c100f244c407000310354008283c0d074103103941c10840d070000c6600680c04c4900d0103040c100c00500701e030040d014460a0000101c1e04400500810301100c0041c850000e44038050f08585000c00790b40e4100e810034404900c0394000ca0000304501150196084d075000340001c002707411034200800701c0e80001400d60305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 22966732 1250 22965482 22965497
    0x3010612080906040306090c0603050906190b0d050607020708010e0a0804050105160204090305070302010c09061d030a0501050703060501180e01030b06040906060605030a15080c121903020c040c020d0e090601 91
    0x44180c010100c031b07103224a81041105089c00d10040459200502203800c540c0310704244080401d9405010280c104482404140702c040c0c01c0104504d0026800002d00702d00c40d4004201070240d0101d220025241100300920407503906030a403e41e5007189000c0545601c1013004200091b60090004101070605c0c2003802c1d08100040d00000c007242c10300c9605030040303903000070f000d010035a081c031440b0581c130003605000d40440c0c1042c000401200301c0161140c19213902e5524a0110394003001600d0b2a10340c0100240003c0c034203030100034081d02c1c040c0b0805001c601c039030402c2c10fa104141d00e40ca03002c0d1101c03025411070320380c81d5841390404c009002d4030fa0758120b0307918400c04002c40c1e8180914000344c02c280d2641c541d241052518001103680b54590000050101c140070700611030003040c0c84995000c1111018415407103411494203204e60a4180c06181a0320000e110405030049132140c00c0d04d03401c441c1000a102e8040b010f03a25000c204643c01c000410b840b441ca042c034904403106030740200040c0340820 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 22967982 1250 22966732 22966739
    0x5060301062d020304060905010503040506010509090a0506100e2d070c080d091e0809090c0c0d090303030c030c020a03030e030d060306060e07020a20030a0f0f110301061208090604 79
    0x2070b40040ba16070610060b000080d041c003a40390480c02050003001c0070710303101d880d40c9400d48030680c840d40103014040c400c0610502084948004004210901d0380081c10303144503041c12103014141404910a1840383c1e01d54a000441c000c940a16801c040c0760a054507001100081e0b40c01c0212840082c09002408400300c41400454104000303008107401c21900000c010115013090304420000440c0b4480c14403180e1000c10014090f00c050318075400c000d683c05a41915071038a60542d42c0240c8002c440244200c01c201d2500f103621904460449000b41c070200040281e002046003541d8030180d80c3c40241e800114100d000034400e500504140440b042134a0a0054140f0360328180e8400d9842a01c615450300d2041c031046910714415900030f00c40340001c0400d2001c07a030f1484a2242034141c070004403044007184d262951003c0c003d41316915030081444c0352b01c002502d072070380d40304003501c07030a0340c4071b4050f03081d21000750805100d03480030380d480642445201c003465540c030481540720341c0c80030f0380280e010300000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 22969232 1250 22967982 22968047
    0x9091505091c020303070207080d0e010e0a0803030906040308060612060d031701090c170702070e0408090409080c1006030b060d03020106050a080307021203031302040207020609030f0105100806010506030106 91
    0x10b070482d00d450340c0516030b00d084c4030390000e1a00d500750700100c0300c54105600c80c2c07211603040300c5c0501900b4004e00304400d100c0c01880000340000d0b040ea00800d52400000104081c1c40d002241c1288524400e80b01c034841615103a007404810300645e001c4400c0e49258402080440c507040c11a080c003a4820700d4024807900b00021818800d10013070784180251034448604003003494120880c00c0e0310140e810412202c0f45040c913030080d0754039954840d8030004402d034404901403061440403111081d070b0141c0140404100c503d44030101b640107019101042c000c46040c2c0d8031246042c0190000c6035048900c1c04203d0310786404100204404200c12025913581d52800643ca0b282d1030142802805268041c41e150f1b1041e0061101c0409144d6a2a425400400810548201402c94041e43c1901a5801602ca60039480410300604c1130184190b854400c070321062000c0341054010300c0c0f0402c0910741e2440002c0c2d1383c800c02550b4910a00805602020600c010f024051180132450741200c1c0040c100a000d4000d00e095 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 22970482 1250 22969232 22969273
    0xc02120717070e0415050705160c0513020a0804060e151302010f05040605040909021302031302030c01050901051b0a080c06070e011e11030d14040b010909150509 71
    0x41c0d00d0038035420305505281c550500070780004250303c61100001c4c0c50a40c1d10302d554a00c104980e5030085d659a004030b0000d42c403a00070381c0c4180d01d404015140b0400f907824515080c03060361085500c2340c111603e01018201550003076500300416034982c003c00344c4072a0340712000b90007102441d840d544586103907142190b010341e681c1070169407040c50640001e150307400010004a59001c0c03a1080c00742c10001040f4103544002120215400808005880081c40c4005407054483c103042121107030010042c0920403443c258042c201c5403080307040360300011040d80155814003840320b00d80e0104800f4444552851100812801c81500010598160315039070707501c03400d0310b4126001419865110004105000c1c0c0c110459842d04002400c0030748684000100300c1e0300c540c0902c4c00716800c0200a41e840040c2030f6013082541c1c103070b44c0074240500244518010504003030b20101e030141c407403000e1038000181c07041c607078440c01040c1c90708036080f458012013541894000e00005000d06c00c0750300ca00c0000d20409506440c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 22971732 1250 22970482 22970489
    0x506040210052119020a02070e040302030f18010f02010615110102070203120705010506010e090c070c0e070e0109050613030813030506040803040506090c01050a1101020c01020403030804120801030c05010c021207 93
    0x80d103e80354203040e602c102c0c01c00c1070b0100a8401c64810442006001d40024081d821503510f440c62080c550b903a49405ca056000c1d40c0d400e601030010103c0c0c505018113100e284001000403c5c0d0303c803c43c5100c2d8020490036034a0300d02c501d1000280002076500b00c1841100111a2840031000151908003a0b40c046490b0032000400d4480303400c404251403040010a000702c070742000d030901e0304031400310583d8005021001c000e4a25844906c00088503820040780085901c001c144a164081c410314006002070520f0b4000c004c900d0008001c00d80c041101c0c80e1600030b40c1d224481c18022061030034155581c0705e01c7d0758030180e800c610001070021b001000400411500703101e24800c0406648070b0420307241581c0f0f00640645011041e420288115820382d9101c0b041e10280400ca15083c104604502c403000c2c024803c0a0490129500008020082c15040340503a4001c610814440300702c04002802241d09000a000082100c0a456400c0041e98030449021212a0004224100c5000c005a4081ca03008090b407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 22972982 1250 22971732 22971787
    0x120e03190602120a050402100503040303200a140c0d0e13090812010603020a12020a0306030b131e12080705040509040f05060601020a020120030403080c010b040f09050604021005 78
    0x11080074921006580300c0e000549100c0c2404a0b0411f5800070789100b072000702d420b003000408400202418803a412a100c0501d0562218086007404220900940d00012003140494210040c0c0f2105503002011510100d449001811440b1400c41e0b0454400e0810100745501c8014031144501c001d03080c0c401c82c0001031003041c0c0704d9603411300c01e50171034420f80e0140d0000e0185803051002c07890094101c0100500e8080004005a9818500e10140c0c0201060340000d0500740e40c013001c01c4030b0440194001840c1c54091104040e02d244200900f804a480e070180040400001250554201e170040e10a690040341da81001d50826446101056250030308071030030b40e80608102e0ba407509004047c00120b40051017840a0700700d4080c00c5d00040c09201800e0b0000c049080c00352083d0060550902c00e403006140c1c801c803041d036120500b0940743d019044100e0014421850144810010f2940d4419540201c0d40040038005a58650b0200b103412290103542d5000d00c503080040000c11200f032a501600f045850 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 22974232 1250 22972982 22972987
    0x6210105040605090114130e030d020d060f06050712021018060507140702190317040e0609040f03030509010f0c12050c070512031b07030c02120109120e03190602 71
    0x3000c0006948040d0310080c09014550014818480ca580c0f00b191950f40540b14603078140b100c250050014103415655480c5400041840141941d0b00d40042004603915407007807100c04e840e200141c0c413004180c45560702181e4100003010000c2d0701110b0303404641e401401078880040100b0030078410341c1c1800308030600c0b25040c0e2030b0641c00c00416100f62600300245180134a1401940303202c2040c103104400300030748a0112070008000c45400000542c002e035510009c0c008000d070080600d100b50380c206020b4415048440c10020b0351909028080c0e500c2250040000900400305840580090001400c2c1d1420f554840c0c01295404800e8094500c1c03209880d0344107156000107600b02000c81304094400a007644041040502107800051448600c00c26250704c0f0340d030b80c0c54988500701115500c41040c003112002080340014150040e000c11082402907454a1103042ca440501e803c90b511010020318001201c400c904c2c80c0c0c2c0c401c0c0d640500c074400140031501c84000141420303800302090b00d8101d40c186c3c1c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 22975482 1250 22974232 22974239
    0x2160b0406050f060f01031e06060503100801050603030d0b0d12020609100e030a05090117010b07060606020c030d0e010c0203030705010516050f040302010311120f01090507020703110906062101 85
    0x20348507155120003d03149207850340c28902d000641000007a5245410035848845440c4e1000914140a6442c0074014040126070f0307542001400c1a007007251401d640f0060101d00049100040c060b191007104010080c0d4581020043c83c00300806100a4840c0c03c509101075402c0083d0410401ca4003e2070300790010882443d1101101d854041d0f12490200110700b092074185c0b0408000080e6803146d409424019114503445004940c0341c820706085040c501d08650001480d07402c1040142082801600144000e60703d507641680c1d02e00d984800b05030154018154104014894150749a07020380502d032100c80346c940d603000240b41d030300031000984a03070750340740305200c030701c8c554481c0b00201001981403040c1030810200d900350103401680300c0079040c1a2589440085942c1100403100032010261090810741808481d07195001d03024055440b20320300c1c200114802c80d00000d21300003245d5000d0b001c608650f0b000820f000540ca00034103040e80025091011018010a02c45080c07450082c408051500d50714 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 22976732 1250 22975482 22975493
    0x4150c0b0a09020a0504020703050909010b090306060a0e061306080f010225020108071101090602040902030f060103060b0d0b0f3d050405011b020909070f05030309030a020108040602160b04 83
    0x100901001c080c0c0385800040c0c00180c40d030000c90b8049a004450060729901c86090603a2244201400113901c00c000c44008584000240c000e44000d440c20740884450760f803518213103c401c1c58240607100c032070340007400028058030301521803141e1024114000b180340c0e42d03110350f441e1416030b08114a010317603500841e103a00c015625035034113583d5141e00340f2481664111a000039012400150424040105444491824040075001802004d50100301150f03502e40c0c46e04140000e420036182e08040c4802c400204005600c280100e001751032601c2555480c09011f034500400408061781000c0e0096820802c00c5842e035584241007000d550300202a2000002c1d1000f8070f02c4850000181e44102c20b200c65610500701e50203419101a20341c00e003442c00b4810040203002c0e0030340c40408070081d0700c02241c90410801c1840491030f4011540301c00b602d500602d0301d5400305903d0b4012800d1407134241d44080600f0000d0340c440c0306070780d030442d005410040c0740500c5640c1d10030000010301d0040c1c8076008031405000c00c001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 22977982 1250 22976732 22976753
    0xd0b041d160506070b0703060f030309061805030c0d020d06110a090b120105010c02011110060501090501090315050709080a06021c0203091b180a0e0705030d080105041104150c 77
    0x342030801d0101e01038180000644240160300c0080c2c041400340000070143c80c002e03400395018000c0e0010300003c0954a10b0000c0c203d000d24007411740040c81d005270300f103080c032484030700942030390b1006003e00710180b202d1042c040d50003820001680d0101da0081c400012030424440d50594401201b119a911612040007600c540f2495221001d885c40130800d60241e040c2020f6210305484003440c2c4070f07590005a00040395890f0080c4ac0c4d1004038011012080c40f48000c940c01a41211402c2e21403280850340e400054403441d0040c40040e00400380403681804441d460f0b03000780d43c8201141040a02c07147c4554245180c11036141040f66800d0703002440049005544021903540c8180f4441546146019600355440d203480340c0700c210390111502005980d03030740d03407102340d99007124128480c0504d490305048440c080d060b05026a1414052103a01141506010401200c00030060b00e4003801039203007900340001081c000c90301e01324081084c00702040701d51000528188400c0329a4401900340c059080100d0100b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 22979232 1250 22977982 22978003
    0x80703030e010914040218120106050901080d02030708090d08120f0109020705032b090303061403030708040e04020a09020a02030d14100608041b060206070f021504080d0b041d 77
    0xf02e0022010400c90b4a0700200040c0c0d600f0613680562a00c04e010400341e01c0c503288540b0154070070540807000080140540c4800102e030000c45d241516640e80307051454481100701801c00040e002000702740d000c00e008100500c0188000340136004011001c0e21080504d400c03a9014a110349488824001084082c10015014040c0700200714900711156944a41c0c910803004508040340041e03c030305900410f101c44200c0f1404c2360180c01c0c84004150704c0c1c010000e00d00d901070003041d0740c0e9200c6034551074200002a5403500d039104640501c3c103401e004c26104440c01c0100300300c2e480340038400081140101d42c0042c001250481d0011521442d0410000c0103031640b07490030b0700040096100300403141400700300e0001198440d003050800c85d1220309001d180520719a0f00c10703940c05100000012083d50001d4894454000f035511404079904441701241c07203400040500900c0040352021601040407140100074001040400003907103030701000070070140e91400004400c0480740a19000356031005028407c00c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 22980482 1250 22979232 22979237
    0x509030406050d0506011206090b090f060108010e09030c0d0924050409090f0501060f0806070507020306010513090b091c020f0a1b03080408060a0c0804050d0f03020d06080703030e01 80
    0x10907080a200812500034868029000c544940c0030800c03d074064125400b00380c0400d1001d000542e00c41041802510941d84a580140c2007200016861107040c04000d00800c0142d45100c0c4591800f1200a2101005024840305000030080850001c40401089a000d0b004d6182c03034120500e04910b58981480408451215014038441c48101c030344d000c01214181e414001c0d000800069a040c410311054403424018401d600e4450302246001101e20b0b2501103c0300603048940070303610f04504603001e00641c200250907501c140700600c420328143c07601d41c1c80e82040c010002084007050310742c14050ba03000e84a00d80c403130300510340c1c2d402101d102c402c92030903407980d9000410b10541511292542c40e03001d40c20140c40507100300d0f010000506c00881c454000d5800070451500ca07521a01d6003515010140d9291a10030301e4140025403050045046c940f0454218000d0f00300342c84081e500741c1e620701034015484101a400c1290140c103005a12501024100d40b03402031000c1400c5281c040e2507458842e54081c103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 22981732 1250 22980482 22980487
    0xc06060a0e070903060203070203070c0e060306010611070905061302030a050106140c060a0b01020f0f030a08060406030b06041508010606020303090111120703180b07030902030d08060f01110a0803040510050903 92
    0xb540e0300840401e0441e079020304c0050796030b1385511080b801c6000b0003c00422119400c0d5000850429584c0c030140a903400310155412030f43d071000c0c10340e110811a40554081c0d00810f07020801400702d54809503000c2c4014010000141c23480d41c40500701c0e401112180010f42d50b5100500c10a42c1c0004600c002900800c02a0f20b0888402d000c42d42d59403000b0040c421281d103031042c10328cc0c3e910a1121400c1e04510208072103e40803060303402501c07034010740c980c03100203002c22000546c54989808be000480343c02914660017a10f5100a21010304000d0106a0444200d16000664a40c1c2485a1401419258040c68980c20b06401107400d64030404401a4140010700040b6080880c0c0350310f16070460384500303001070301b00303490305030280c0502692034003902101c16001003110068060304061082c52088003581c0c0924044042503640c0102030f1445600210100c201c0700a0394014519540200707a440115520903035607949602040d80200d0301107840350030803146040150168003840341c204800201560 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 22982982 1250 22981732 22981741
    0x2010213050d050a05010e0f010c050406050a030b010c1b090e0601060806060a090e010b0406180303022e0207081b010b060a031a0d030207061409060f07020102030f0c06060a0e 77
    0x54550419004140c81884480b10782c40070040100a0000440e501400900000c1c0005540a4540151884005183d403c1ca26075905030743c1304404032400e41c3c4da40e860792414102101001c034024507500c0007407030610030010704800104100c4055901c0320079441d54a0303850b40f4181803c3c5010344076141340c5c2c118558880c50044c0f1059801c28207032540010245c0d1081d8990744800e00440c2e03c450f603540700310a4024150004200555183c00801c02c0e110075851750403613005611070080050360584400340050304013003421030042c013890468104901d5403004040e101e51080c1d00300b8040b80c1c407a24084071001c50011300008200d0121816200c40c5000318000c2000c4004c00e0003041d42881100302c41c4e403c040d645c084810254820100203a81d4031809009154000d80c1c42c54040e40d2052140180004280e2608291004203640e0781216240b1030054502802c00c0f89c151112020b6800801c01281540800e0000768495111113015210380700314440104803a082200901c00c4100a41c0c200090302c201c0d0030b0800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 22984232 1250 22982982 22983007
    0xa0e012d021006030f0206070213020a030911061e0d0204032009090d02030301060c020402070506040506101e05040905010207120509040c0504080a020108090c031f0b010c050a0605040201031e020316020102 90
    0x910b44590141d4044d6555608c0c1e20000724002894164499600c2c0701040784145a0351541c41881481e103d8480c0d40341c0000d0074010440f07607001d4001c5010450740203072080060410550007401c0e250f0114000507003420348135981c44140f203954001501da11901000d06008d5441c0030302007150001c0710180944010070305010002e449200500462050149404421046407150f604071140d25030408160340c1d007030500307251960300e41a064030500e402c4242d8a030003050820007000524444c80c2c802d200c40c00c03e01d20b004148006850150400d5403555801c0c082c42c0045002040580c00c0c000f8250b071565551001001084100c511030b80d0f0300010400180300a00c100040002c484c582c454090a006a05981e0400c4c2c06180041e0481101d4050194592144601c00c90004c03811621884540178000e1030009401195420f5202070060030036441084680301046e940c0e8880d41d0414010700d0041160121400c03e031b080c0d14034101003400c820b5400400c110200902402008007803155100a41c03401c280c01551 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 22985482 1250 22984232 22984253
    0xd05010b09010c0f030c0b0703090201030506032a0307080106120501151202010507140f0d1704020109060f0e0405010311011206060503180304030215030402030d140a0e012d02100603 80
    0x140f0b620302c024220310034140a40c121459847e4002d09514103841c01401c0200a400d00003800c9011070b09013004100c3c50b00c1c02140e00f00442c480c1303038000c10400020807052400e0031091491260507008601c00411010302c00c0c0600d001402c030741e000c0c0c00c1210f641407a02c076007103544011910381504e04550f014003048560341e2011505540928000d6200d9005007070240340304007a024000541d204502c91040541c0c404201c180b040700703090300c406801c2206865070300480001124000c0c0001d440002c140086030040c4d407001445500761901c1d45051141c280800c084034000e8100340d9200105115269081d80d101c00071125081901206005140c030301035010309180000340084c145c4000a000b03c484e884800c00940380115002030406140c02030b0030382c0c03c43d81070b8810f81d0f00340e001e4020403401d0911540582e40e002c0b5021002c00c184c40ca8551400030840f0010036045555040250a100d150785100c0344803590b501c80400400900c080c501c1d20407010f4980101009400038650a0400400c08070b11100c19 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 22986732 1250 22985482 22985507
    0x706050f0921060a05010914040206040504090312050103030903060501060e030d050913060308031509070203071b0302030d08160c05150405150420010314060f0a05060f0d05010b0901 80
    0x20b81090006406010128400b9030489904540c8100d2080101c0300186400c0310781202d14449040118440424001d03c10308011035019411540400c81040b176420581c0c88015054000e29040042c0702184506005981c82030f40140e00040008005005001d2144140381c018035107030828080c0d004c001c602080c1c0b1503681401034824444040703400c04554545004190540c416071108004543e1a4604070100d90002c0e03ca5000e021150b4918140b035041510312140690515001181030049680d51080061f544084060207407492250000041c1ca0800c030b000306455150700d0700d032042c1c41d010072292007450082d01004104400340305003001045001c00c20a004283e5a8100c01042e40c40f8102079140008c920015040115030f0300c200801d21802058411115240015440c0e00807501c0f001181954201c16141c0742000e481030100300c45240c40742600520140241c03a41c200c541d0303a0700015843d6000401d03448102d90300012070529542d00382c81001e02410148280d24141144040020300c450032a05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 22987982 1250 22986732 22986739
    0x20c010e0307261212010314010b090c07210e01050d060806130c06090b04180b090a020705070509010323010204090603030e01170c03131704080f0706050f09 69
    0x580d18a0354406000400251282c3c0030b00410b40b1042201e03140790104050076011030781c002c40450b1418003441c0011030b00d00c00b0913407040d4407841e400c5440e82d480100f0002da4000c01c540d40c0d0804081c10391a40f00300c40388241c1c41e907800d1903214400d0741400d41420702821250303601103001c2c14960b9103c5d0f40108500302c040d2000e04e00310303840d030302a0703050340c402403a454022505500c1034608015501d00110000d5544034400c0c44001d568a90b2007105441c100000e018580003030000b07020a11442500001d440d580300203c2101050715044000490000c0a0540d14080615000510b00081c0401004120018141610075104940c910f03241c5000300528118107007080000b441ca059170300300094055802409a8401c10441259640b80180c00c1c2542c0e504002c0c04903000c0c0301c180001101001d02d142c82001c94403c81031441d55440c1c000702321100c01040c11200c0045c081280f4044a000c0300180014081d248000c0c001c10100318240383c0740804a42c40314040003410080c0d1100c41c1458002c5e544601c1d01134 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 22989232 1250 22987982 22987997
    0x31503010506061e0408190201090801060b1603020c101d0102060615070f0b070f09080d020d030c1701080304090e16060e060c0a030e01030605030a17030601030b19030b0610020c01 79
    0x5134038090417441243e108204034841c5031011941104101203041d0715034800d0b01c0d07031840c41c3d90f503404c09400d0790035a2040c500185018441c020aa280c60324003106400e10910540d41c1d040300880004028141d00c2860800013603002c400624030213260196500f5200003400185131902e8864002015410040829220400c000ca0745000b00242c5c000815003450348907103030b070040340380c000401030010a48011400004407104c000003444900482c40034a0340080c0e50140c032102c120303018254040c0070900124020088011b103800c541c11071742ca8160740a4000c16016503a100e00d0001e003081035aa000c0b140c04155006130800d46000201c3e02d8491007107546a00b001d900c0a4803000000c1c2d4107024030301c490b92850150402c1c5000b0182c1c090051060301c0002d1700d003084000e4840041c0b56486444040062001d0110140c11203002c400b00c010755400340b070514000c0391405c14100462041440d1444c503642612502c0801c1c03040201e1310800d5075001c0d000340c4491744003052a080c001d60b608014170b8061f0610906 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 22990482 1250 22989232 22989277
    0xd0f050106050306040605042018070e060d09110103060513050405070509070c02010801060504051e06210f01140604120609050102190806030109051c02030408010c030203150301050606 81
    0x390015802444003c040d25503500e454240400505001c0360100e07122103610126042c20403145480610f070800161800d084140d5078200b20b244440083d1400050207155a210446599950300601c2125004040824903021502c0c0022901c081c3c1e00d401d0303041c50f0401000303100a03154200005000040d2101c00300d007581303031410114100760301a08003d801003042010004003030380107800101007510070790707825005030b90300c0c0b40031101401079008103607015041030410340c69a07520000030141000000d03c09803a107408010001c0050581ea41c02e40040384640040080d8800d9070100a40180040e03103641c40c607c2c4149001480520440c01209200808540e10074103200a0b5408803900705c0c2c0c0300000b15034070b240c0c0d10581d9a010701e01e41420000960400700092082c00c060080d030b4890f680c0007008182480300900d904c29503105900c030450842c403042c40b00003041442402454a02049a00c0c01640e030704107040109845822100414020780c100320034005651510400c69501e00b54a14000b0032805e40d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 22991732 1250 22990482 22990493
    0x140a080325080f0a03050103020f03010e0d1d030a060e060c0301050607030c0501020702210706110307061e06030602030f0105040c080c030c04030c09020408011803021b04020c060907081603020d0f 86
    0x80c9070fa00b09010f9000301e410020707103401d030380018140d0b4000c84258032584031075010503080e00c400c1a0110401c2e00603105491103940a107110300020320b040403c60b40d19501200200b8a03007d10014290740450700c0f0800e15007100310601015420420510045203158140008200c8900c02c5903001010081c114140700b084c0700d800e5041d10f04055004003901101151001010340401c50030001c00103074011203000190050049501540c403490050185d400c03e251925118010701683d0300c1300da45048030b6403407240c5000d45c1d4412413001c3d500c108030045e12400c0081190b10741c0031051f000f480c06a468007032180001900010003d5108015003446540e941d5207400710a814082d0740d2004146600480c404940340325690042c000f501d4800b0001c1240c2007a11403900141013210402401507000542000c07801030a80c55031500f030640290000d4035004801c40c84618200c4110f800c4d42d102d0700722450510405205210750041e01c01d51350b00800d1001d0a680005000c0100c1c400000d10340845412801c04004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 22992982 1250 22991732 22991737
    0x7080616050d0f0b0a0b070f0605040c08031903051608190b0a030501050a0c0c1a0402011809090b070f0504060509180403050a110d09090906090c140a08032508 70
    0x82e0440240000e9220100c008003a051344400e103807064a04d000040790084084082d0b9140c02d420082ea14455111034413640001c1030048e1068460180c51f00c00850755450420042c040c002e80d401e54a00d4423050713040002d0031201d0250420146070070036404404e41c036910103017541c2c00c90324032600c079244504005201d100410a00c130b20b907600050611000800e02134107502c80c6115803501a0140a5040b851000b11959811131500a014008040c96229419500c0c448180c4c000d1040c1011464503004402c0050307005040d134880c0110503180e10b02c2808010101c0310080c2c11807041e007010000c0c8292510094268000e42c0510401c0250228841c856a13440c40d24050b054916501303e000d4600301420000c09aa001d650607801103a198443d10405400024521804002079500e00c0060760078088110040e000e411010380d0340f81c1c2c480c00c2c24804542010305000080010080781075199181c0700912882e4210b9501401041e0000e20054ac1c2c15620107910001038910641080360802e800d2410290a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 22994232 1250 22992982 22992997
    0x2090301140a0c09080d020703080c19080307030b010c050c04110f0301030302060115050702091605090a0e0901111801050901020f16030204060509040302120c0307020301020d0203040b0105030708061605 89
    0x7101c015060140444a40c1d120004941403039540085140d1920361095464502c000e2120060384000750410208400c600a0000340e07a070b500a40744502540c03540170300f0342cad030001c007050710301800020921211640520401120354428201005090350340e84a80343c991324100030b140d00494540403517541092891003103c11844929103520385070b58603802d00a554040034060301003040000803402c21064086c1050f9407581d68000c6c95003040c1e42e50703211704801e80401000c2242c140300c010b10a41d6a980d030f9000407500034165201801c251440c01c008000c0c00c1d50582c0e60585201c0b00100080d036051391406910884000003130904540d034001c200b0040381707400385513a5140100c2c0950310203001c40d0140044900c003260700858051040b65101e200300400304a00307890007805079001c00c0d00e0385603030704001c0c0c00b40080d00c188405403404c0a88903004607003680d2201d80c80301d44c120382c000200b0080011144119016000c250300030004c3d01c1c00c0c090129551100602441c1c0b1819040301a0a2028821030403190340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 22995482 1250 22994232 22994261
    0x5090c070f0b060306010e0c04090c03020706020a020c01020c0a0b030f0405031b010903020c09010803090909030f040305010204030b010f0308040605030603031b06040308070e0f010e0d0203030703110705010e09070302090301 98
    0x81c60090414910440d81641c48030303c60300640000040d01c02005d90750900a105404000d45407038039102c504001420440340301400d060f020b101140118605101500410344180c028081800314440020f040811190646202e100441d509000444000003030307039800000000005220786650506d030303207540100d440214001e1007205403004890030642103850b1291003a000c98401005020070401c0558090141d003040e540300317000c02c880b20711303140e0a0646c01c070f01c4806c1628030380500703024036020a038081d8005503007587d0005810000c1110300d2504a0062440c881207407003460450350354494500c0b42e4880d2104002c008000b03d5050fa134140100c0300b004808183c0d002107003100ba0340c915203e400494013900869607180019280c0e40c014142411042001002080c100c500b49005640f000700342810107801040000d0040c0040c0c40420040095034042d48401c0c4610125181c118504011380c0c214a0400519003211491078488240007504006103007809030b2200403001c0405d004241c2c1e08190001b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 22996732 1250 22995482 22995503
    0xd020706091407031a04110f0a03021f0206060312091e0409031d0f09010b07050708070801090c080c06040b07050307020301051501032a140d02040312030b090f0105090c07 75
    0x301107000030f0600100c0340b00322000c0c0100c010a2440304000601114041d2800310f0700c0d0618206440d04648207106044001c00141d0159103c0e0041030403064070060342c0070840f2001c440b4403a110b804001e031503031140003280100380c074409000709107581d0300801060301e004641d409024041407081180b1f441c0b4842c4007070801c000c1c50129040c002c0012083c00002503405244000c09115400d2800040700d808038082e08032003003a4600034102070b007640004010340b0705000d00840070480d25828001c2c840144202c0d8001b00c1c51009608040f2401840d660140c6002e1303000010101c410f40b9108255000c8400354440350341c48158609005080d0f109200009516504e818100b240301d01c1c2d01c3d80983c08455080c0e0b020049029070025045249080700303907041c0d083c0c94000c0504010352064030001068680390300c00f941080c0000d10700406a0704140c10458080811545101a041c2e0601ca1000c444030111081c8c221404c4c2848205030703654041c0100e82c02801d005000035000c8052000f1640340c40d84c08101984e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 22997982 1250 22996732 22996763
    0x1206060303071209090e0105040b0f0417031803030108070501020607020a1a0a0e010207051609020703020c090402010c0f03090602160e13030e0303040315110a050d090204140906070f140d02070609 86
    0x1802000221412941c60b041c240103e0180f20f94034402f54821980415030003d454000c1d0402200c0307400080c02d0000418400d400c0c0d800c4a042031000c2c0d8020007a03d402041080d01b40380c0064100031380148000704641c012580c01703000c56185824181c0100c11030700c480d85542c4132903d012002c1d046400e91491039600024002081002c0064448004010810540040c0f51a06085cec0141d114844020300180e101ca00c030582c003131a100340c80a4000b84141441c204c1c8031180c0da41c5650200c3d0741340e011703800b01e900c9190070000907806104c1d4210142105090405150411400c14a14000501203140c8560b142c1c4080381058011001015080b400504a0b5201c50ba80d1070308000304030040035070340740c0039041c002018001442202601c0868925480755801c040840031200002d00c46010203a9201e03403a901d103034000c50310300585d9500543c40f0101814491411840144c5240c602e84040c90801c861011071548010b1580c0a59601c50590140135a80d080340c1c0c02d280d0302806d8500c2c0c02400205c21a041d15 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 22999232 1250 22997982 22998011
    0x109020d0318090204140a05030f0c0f0415030b0118090c030807030c0510090c150203070201050319050a0c02150106091811160b0106050403080702090703090f05010b120606030307120909 82
    0xc01034500d044504a030508c0d204c038107054407100d14110b041125804641408100e00d0442d6040c0c00704003015100203884032032009443c0c4050320351742c01554181c044c1001404662000039031a40b002c1003a80040c0702c94a615a24003503118201d01c00030303210442c081a4641014440c1101c0700d1050b82060444000303403c2c2417000c5000340a4240d0850b1240000713800020b113051960510200c03031340e45802450504a0540040d585584020f18086050f445015003120796000c0d441020b005031110032002a00d0300360311101038a041030044032004d00101910040005c90b17800000a801c0e00c00109040a24000c505000130240001c0115003817501c07400300b840050542444010700a460041c6560356803170740e81e54030503940e0384101d000140c040f035801c100c0c207009800c0a03400030b604046d8518000400c600e840c0c036001076030340101004032040d1351100c140e00c24074038100380544400e01221300941350342c2c141f2200183d40c0e03100b184001801000d500d102d01103000c0c09820010000c0804860900c14000c519201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 23000482 1250 22999232 22999259
    0x30c0a0b060a060908060c1b06010801020d241a070506040b0610080108070b070c090c0903050c010f051603020c0a030f03030f0207030f1101110d02120601020109020d0318090204 78
    0x41c540a4082ca040c0050007900c200e900c4011580d0010251030141c0740c3c4054a0080e9220101d0f46420161400c0d10750070703d00d020403c5500030400311000503240d2008005410540710700c244109448000030382c2500c400054585181c04985140c1d071402034001d04d868211140c8e010b200c41c003030302c6070142c01d00308024002034248092143d042103403d0403102c0c8001c04151107107e000e0180100d194400d00c0203201d541c030341d80c00800d09107004400e042c8640d943c82c1c09000581c1c0003603150f880040d21541003081000810004201944030074280100001d0001d1001402402411300300e810030f09041507101c0c10f041c0203120381c0140c100c020741000c03001911713418a0346020021160840010f0702c3c03d4041003892509200703442516516607500000c090b10714808540012345185032000c039569410304448401000001001c07580c2c809a0050303154402c104000d0a1110020069815641030910b40401662500b40e0f84204541c141442c911600c07800b129594228035076001406070b284001008540c03401807191 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 23001732 1250 23000482 23000491
    0xa030e030c0405070c0803040201021f15050406060e0d0204020d020703050c150106080403080907050604060e010219020f060a090e0703050103120f0206160e0d0b010515030103080a0c05030c0a0b 85
    0x21928148680c0042c8002c4076412113103040028443c100c8540000ca2142c01145c01c00d0051040700d800c1c00c02014440403042818640c480202c1d5a81d411401c1845c10035100d4008080c00c540c10000b040c50f00101805d141e102c1d80e0300703511130b088410a00d0210b54441e4191881d64600050031500c0b0021450041c242d5445100110030500c69a0080e100e8500780110960507142580d842105548840d542610715a1014101e90694041e5010200d415200e40011b80020f04040d84d8280c40100844006410328803400c40c0348030903610450300c25000d6100c5004452544009071003d0b0740d10006914104d40c550f090b80c0020f05545a200c09010440717a00da04020706890184100c141c0030107a0381d40a445e00c60701031000c600940c01ca040021900d503a26031095080000e00c0c00c00e24144a4140001120429040c0e800c4440d1035911006110b40c0c01c00c40b0713180c0403400c20f0390f684910b1541141c54904850040c0a6404100071103002468100030303081c400d0b80c01e1040d20340700320f60100701340b840c20840d0b6100444 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 23002982 1250 23001732 23001739
    0x20307030b1801030c030b04020105090904030801091a0a060e0303070501020a20060f06010f02010603080d020d060503031e0a05120f0106030c030209010e0405130206030403020309090105040608100b0a080a030e 92
    0x25204000c10100035155041300c1c4c1c00301102c0f04c20b526545c0c0e0a02040c200400070f0741445401d021014607502c4001c5003034801c034802d50b034401c100e60502905a084801305060302242e40a03450000e1010345813502c0740010350350076041c04a202d00001000a15500c9035610040240d400440c240d82c0ca180c024010255050420b05461106820300000550340c840886130f400c01c0304824404500e0780d50083ca44001801074510003c2000c2c0d0712074880382c41c19804110551315040d4002000841000306100d42c402410088001d9850642504c14010160882c140d40c0381000302d000076120a403600500485145030750300c054807000352502400081641401344924000719003080d400c0e40b0400c0c070a108071411100141c5a691204101c0c80c1403000803e4020240c04142042416070741c0540d60302c001440c4514440d0b4000c641e250421405c0c4041500b040e0311040c000e40c20001c040c084003a0214148030890b0404100240850135071001821102c010740c03204109001e40403296050543c0104c0442c000e0f001134 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 23004232 1250 23002982 23002999
    0x80d020d080415090804051806100212042d060c030306050406050109140f030f07060f020307080301092406030207030201060506040503030301060c080903150f060409050607050a0210020307030b 85
    0x10380c400d40c1d004034212801400398508090480800402d0b41c0200741890180d401c0c607050607100d5000c00c0000f07051141e40c1d01546028010401c0c149031440d0807107040c203240d01c0035011480714039001d64132502460203040042640303020400090391307800c0404461010b01c0d0b04210300c0240e55a00c0907000610701c00c42500002d040910110756410180210800c40c0c1043c2d4515060500c0e0036801d040481480c410f003544500d0040005100e075a0401190fa80402d0b88005000c0f21882c112014200d0104074003c101950400c0c810781002c03552480940341110100540403605182c192a00a4411404491014010070408003c03440036499405445024400c1c1c00030004241c46038104002c42c083e41c030800344d06501c10001806070511a11001041600c41c511440c2451035400002c0d080c894500c02c0b58500d81c07810410002d08000d80c050035a00590f003582e0410495660b501c4151301c900d40149004180100080c552258034800c10110144042180d411500c2c1d06003008001d0243ca441103000b403095064 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 23005482 1250 23004232 23004253
    0x30105012c0103021c05070e09010e06060a110a1401060810020301050d1103030d02030108010f0f0207020d23030d050702010c0203120406050a06080f0606030f0c0901052107080d02 79
    0x210410960300da5007400ca03112844a2140110080d40c080300203084c0368120204803407642c1c00180100c90007030800f625812058040c081c1403001d000d4059015142c100c070300b030701440070f140c0b9003030203c0304107500310314141c07943c40300c1d04a1031803078800c101e20010b00c0c9021040c0780d50b0008106500080c151440c80c41540c038103980c2c505001c0164002801400d5000c461020208006101c405954404890190607642409035910984041740c2099024144e01d07511001c0c0005074540074800c1c0e500c0c1d9a10b10604604050030b540205024a02c0500d0040086141003a110b811016007100d003075540020504507651040343c001020017500c415500d040266003801b5001003a41d0000c01528481c0c0d0341601036a095960b6a10381402824028201e016601d950f8580860954411700c50a141c2e401c0010003800e05003001c40030b2525000b0301008844050b001402054801e030ba40e21b80d040d044036001c90700c1c1c40018036114000304540792058007104280c03090120001346640c0105401203808880e03002d80350401c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 23006732 1250 23005482 23005517
    0x40209010501030905031c06050a030c0501030507030903050d0b040e03130f050102030a080a02090103020f0f0702011202160303050a0e0a0b0906060d0b070810150525030e090c0d0c0503010501 84
    0x2881000400700e4006110b40e00608a4401d01c7c1000713040324000110f1200d540e02c02040e2114426001074400c13a014880502c0f40d56050f004258001449140c208400090343d217000707055001e8001409010358980301c1e2424140d40b2500855142c40c07652081d44e940f04641c0d0380008206c0c0c0c42d8451000d81c0c0c50300c003200046542c000710a41e107a43ca0300340c8a520132507803500701d01c0000390710030307041181031560a10407909141c140402410b40c03801c2007800e030307a9942c0480c000500081c20860110b0603031801000701a4510020044503448a941400c020a550b1140c0c01141e0107000b50781c15492245c403c0a402c0018001501000e03030007200c40e0010345103551a1034081c0000300d00030500251002e041c60b00490003a5101d0940c2c55849140555000401074840b410060b141e050908001c3c0001c901007010b40310904250941844443d05084545c2c030714a15030340251215445041743d51007504604001032000e90504100c50640380540c41c200203041c0900d4014040e40c0081c0506400900750210a40b00c042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 23007982 1250 23006732 23006741
    0xc0c07080f0c01050c070e1305060901050103030e040903020c0d08030610050304020901030212161707050406050a0302040b06040305060901090b060102010920010203040b03010909060b150711040905030c0604020901050103 97
    0x25036074015015604102e4019506584195000180b521940f03100003400485d40d0502401002c0420b80d518100002d414114500007001d424401d03203916120040002a811295101094070180e8003c100022182000e07418028940c61490304508189c0303040701000364450040d80b00b0709080300c0342c40c4942545081200d190008403402500f01c1c0d0b0340001032000d403a0204d101e1940e80050000c80da030740803810700303c2e411115280d4071480c03502c2542c2d0340c2940c072840b043c8846005800c3c162000c0000034908800284501c44070304c4060b000d541d0700c07403204c02d6980340c140803600510f4000c1c085403003a04084a0b005d000300b00310607040e00c0c215081400704246610600030021150b4218880041005184c1c5100e4072a41c8032801c02415440b01f000000f0703403d00042c02039402002d08642c0082c104034942889810b032071040080a100b01c2400305041c40000740d0f0340641e059190014820441d061551004c10002c00c038424001d807461101003070300c0700204400984548503620a49a180307069981d0070042d801d88 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 23009232 1250 23007982 23008003
    0xd0c050102012403060515180f01050607051b01020304081501030507060e0303030403200a0302060405070603020403030504060507024608070605070c0302040903020d0306060518060901170c0c0708 86
    0x3c182c1c820800114515801c546c2c0c0150a110040e2082d220141c001121040c1450034900c0d040d1b0010204408401c082c502580149400d94400c1c0ca0a501390342e9990700c4880004402440302510700511005906c2081950041c10f43c0c3c1d022102035105480c002a4490000d2004443c0f52141c181d010840a00c561110300c100100030f001941182c803150b030261060201c0440d100e82800300042c82620400007042000d04007802500580418103060400500b0642a50061303805d040c010442040000c1e03000c012541218083c1c50155140c10991002405045001c01c885082c0d0071301080307600126492811484108500c0681001c040401005082944501d44212801c80e00b00308810001035018800602d0454460b060b41944a900c4c0ea0016084074194141a40141e024400621135150180f04c0c010180019082450800030f1131490101400d0540e07a20501548021402c4020799000b000d07481300c2c0c0c1c6150700781101355282c2954400c55603040700c120010035100d14440060800340114400014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 23010482 1250 23009232 23009291
    0xf120a020307030f060509010c0c0b092b0306080a03020705150408100506040e010608030a050a09080f01020703080c04031110020109060c11070f03020d02092d10060f020c01031104050d0c05010201 86
    0x2a503c4d071720b504519a400400094203801342074dc07950f4001001c1e000140030761001004100106606140040485035141c0014803503034040042140481e8002815500300e070021030b00c881204078403982c41d50003030060b503104883d144144020841c15420a400c400e1180106940810031107071100781c03990980340d031849040340981007009200c0d4914440d0006105001541c10301d031034001e03a04e412031840c110b08004100308903540801c1c0b200400d9440071281c0d4000703041d210043d003004d04607112241005a9101803520503421900411600d9000390844c450043d00040c0401070f03103040c1c0e00013510000c44615001c026000d40c80c0d0100394520106d5030141502d4000c4d1a030740146a8a84c00c1c40811107010b4201703c820b040c404e48064402e00d4901c2400c075084100310040010f814000601038040340e0a40208040c0400b0160440d50203600281462204200746070200d400e1900000104851140b40c1205800050382c00d040c1040c40022a248011610300380d00030488501e1507145440d500141c2c6e000a042e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 23011732 1250 23010482 23010497
    0x40e060d0b0a140f060d15020c03040305030712080103050606130902100f09050102011e09030216090b180105060304170d110408060702010e07030f02010e060d0b0907030203060f120a020307030f060509010c 90
    0x203c0c2401d887d01703100c5442c90100528000c51504101e1464006510450b000e42c400594001001920001050070416906080c40c241d4113682d6030b542c45120050040c0d0013015001c17900070701080303546c10054841e0340180a01c034103000c0b071010003050740081001c445c0105100c1800055954414402d410500501d002400411039274030f08000c02400040b041901140309040001e16480a101c20300402003044510014001001d10140408811840c1c00010100d0702c202c010003494690784102c0340e11643c402e01081004000e00c0340400c050068541200325245008a08010031041c50010801c0d9028401185c4e070381d0761482e03002c0f426a1050601d4404907004801c003040041d200342000426584141050300d0103096079008907181d50401100e500e640d54449065650904220a4450300710741c1924041d8514504107000c14054158403580c2e9000300c45507103180b01505d00030310183c040326500605903000c043c0c0d64117003084089480c00003991480d01c0e00c008a0401c810500c03400c02515500d481d02d01c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 23012982 1250 23011732 23011759
    0x3090a1a070f050312010f06030b0303070206030f13080a20030921071809150903080c070c030204060e04020306010e060f100e030703030203190302040b040e060d0b0a140f06 76
    0x40d07030001c0303002c4101c03590301c400d100705660400c04580c00f502030650b400702003000710b03e0800010165441c4130100c90098208002840250b1140011641c4c070103004000e695a0341c0380c90f00000704c54405e0b8200600001d1020600100d41c541c40030316185101041d001a204160200c5045030b141d1150505850384400000a802001caa618503019090315502007940d04290b9526030254140031a08044000c079650350580000300301900110ba01140d00d80300042140c500213a40c05040c003100035100d0303000440f000c1181c2c0200300d64511803201455001d8014084941d664042000c841070580d006ca100e4042c00e000418041280d264480c42020004c0c015081310365141c01348112038840094440c100180480141003e4804101c9200214441e81c000d6035551505280740032244242814002054010481004540019004d031000c0d500740c184400f05949a01740001d0700d4a00c421001802011100b040102c0c1200c140c1c040d0300c1e540000d07070070841d05a64401c803128070301e5411584554888411880c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 23014232 1250 23012982 23012993
    0x803030403080405120315010f1814030a080c0a0303110307020d030b06070f0b010602010e0c01050d0b03030c070306050109060f08190203160b0c010f090c120201050d060803090a1a07 80
    0x2d0740c12074011015101c090f00811010045944120350080c1001100a900070301c55038452031190740c202e020716145071803c200d0002040b4610340c520406e03040c04a0494504407565040c002764011590002c3d10f107070f888140020485c0ca64929480c1600844c1c03610b494010b04c0118182101d22800c001d0703020b4182c0040c2c40c0c00c190b00801c0d900660a0f089a02848440002189030400c008907034010401000950b140500090940d01c000f580e207400da401001107800d45076000000d44a80862042001c01c03a100d05501003440c6024105040f0024405e030743c03000060142d80d52150781131b01e07141030092002c0382d294040d070710800c0168480c901241d030003428400e80c88510640c44a0b00c03103200078240d039071002d10004040c0c04c039501130308801200311002405115568092107064444140c001e000c1c407055800d9101c002e0080c01e18800d44d501000f009454a085a1084d4111456a2000c3e00c040003019269250140c0d40e80000c41c001d801f8224108003c1103054089500150850301c0c0c039540e6240903415682e9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 23015482 1250 23014232 23014247
    0x106030201090b031f14040e07051c060207050d1808010603020609041a04020309100f0c0206040b09030409050a0b100206270304030605090a031808030406030c0e150307090b03010803030403 83
    0x40c040041c5d44a2005842d0820710002001030300111440e1440d4003003000102d91188094401a50003420200915204c810a070405048611007400003181d035820110080d114881c401080360146926480b10b141d0007a4408181c40c5040804c3d41302d11b03480d003e605d401c071442030001039070240c424003c0c847c40f032500780c220800c00105170b2001100501610086030598005883d44035294002d00985031200a40b80324802c5102405002840000440f45003e500d429000c0c00c05032802c0b201100103424000204100c400420444404100624240001344000d14a05915520503100342d90318540a91001840c03034000d03059103100020080803114410100a00b0070840c0c07405000500c0000045440351280d11301c10408030000e0b024080d035619000704102ca020b0b6034180c0c540c80712481170003456000402e4805442c1c03103003030010385000002c005949150440e48820740c881d4081e80340501002000001c0c501031506901c42e1030400da118049545180401d0090400780d50040c800100800e01c1400c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 23016732 1250 23015482 23015491
    0x603040602071a06040e0106140405040201200d0807050a080105040b0f0405040602130506070f06021e0316020c100e040209180408040503060106050304021003050402011b03080f01080106030201090b03 88
    0x51400b015640e9402da1101c85000d0501100041d8040011074203080c06a940c0340004036008000140c14146415012030848042c5801280d072000001e0459018610481026030800010094610400c202660340e220a15055001400b0a008642981e0145090b1030f0029425120301607143c0c00c06081c00000e01044032401c0c3e10814098800e640c80d1100d100d0300f03000300d000c3c80c0302607035070000141e6200350028268030440c011801008180080703203281d009142c2c1150b200402503614044403000c450b01c0c2c0000e83c00d5401c00703603000081c042d00c07070310a4094540703140582d000d45480c0d003900e504111000c101c8543c20f002051020440000c0c5142c04e500802c88294010310a04494106500703c1022400840d001c0b69820000a401e12681c5000c1150358010550ba00c0c00b9499842c20341e020920040740e0380b403500b013407584070b502044c110380c020110003451681e4a5014110019141002804170509681c580c900618050020070254410f00034013040e240c0623142e0115803031a020000000b0b070320003031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 23017982 1250 23016732 23016743
    0x2060f06010306090c03060312050705060121060c0f020607030c2304080d09080c0d0f110307030602030a060e09030301030305120903160c0e150307060c0501110c0109050f01020a0806060304 83
    0x200c0110b8003010b98410305034017065554001035200e05514000d07400170160300c2c58400f4404180b019900003500040d00340e0556006040800c0c20054003030780c494000c0c2040360b0090180b0b05000ca001021a4040f0403402c0e100706550851704181c5419009074101c074045100d50000595547c0d900b01031040001621107900100d141703c81c50155904103050a001402800c90005800400104100c170b07820044506c00d580c04407060021010580d41c1d8182514000c68014442030310440070005c0766030144210402540c0000056540b03103005403072103005040c0c0703004018002c1140170114032002000010749040e00c2d41a01c0e4280381030b800e040c01c02082003004200310024170080007115012401d4154003d2418814145240c4403410240b0721551040000c1c04240905400101c42c074090f9000521130003180d0707580c00d02058108071410801c2c013410621000d582c00050010346641c2c107450551100320041d0017007003030701c861404050080e420703481a441d1040c001202e01000c151181b40110055030445e04c1407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 23019232 1250 23017982 23017991
    0xf090306070203040512060601080402010f02011b201203040813030813090f02030601090510030204320303031504110903010905060708060d0203060a02090a03050f030703021002040602060f060103 86
    0x440060300d0100110754490050b00702007010801070130301419401490060001820f031343d00c1d010740001c198000003031010b8104003100480a600301e00079484036881700700d255452003484c0510032018210085a10668550306880c5500317400804000c2200320035040d08107611403442e01d81da15611400e40151200505011505000100080031b190003004c07070541d0150f608501d0752600350b400d4110750028003854000b6004004011040c2e0f40003103030340103460045030305c06801c01a01100700e00038099608000d045001e03035848407500e80b400245082c0034083d0954a100c48001c0c41d01850b441e0301080d0749039562110341c0c100d4403c10389056003002103c080154200c0c3d0410f0611800607081da030240b401600d40390400e005001c0d00303542c4440d40c0c590180050b030b03035400401c001c1d90110f030751684010014041203074081560f88896031840c0c1044011070f00300d02115101401061003039100da100c0c0c7c808401600c42c84030320180000c0d07103000740e4040350520340182c1825a2540a41207504800410450405554 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 23020482 1250 23019232 23019247
    0x1f0b0306010909020103051b09010f020f240106020123061813020f0109060c081309020406050a030b0d0206040510030f020d090b100b0f07050a05060411041d03040504020f 75
    0x42002a000301803142c40881c25111600024007115000382c0900303000d0b41005124007280c0c4c0404100e96034180c0c20b19050584007001c020480c18030906c240c00c0d0300ca81c011421507510002c110301c8194202e0050804111882e40e1b511420703400c850310b040c040c0382c40d544d14500311804040e44808050340304201604c09406544818521030107000c003110300440c45054200e504e4290308021240400804081c208804042e040440c0a444c1c51032131301c00201114800501111654640c1c41001e0082091701e9040d034581d030b00d03140082e22581143c2e5840b400280f620090040d01d00e01003505503e519000b919a620f01400e010034081841c012144440c1072684880303244000c160700c1e00c018002d02c0c04c0c483c8002110101450b20300e5248001a140715000150140103000c0ca20409013201c1e40e0f00c0c03031070301d083d03a503082146420f03403c2c40745040028026004020400052101200300003a480710708a0f010040c1c180080650a245088004203070070f20ba00c288401c0c01581440c0d4028803082c908009201d082010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 23021588 1106 23020482 23020489
    0x804120207240e030a030201020c0f0105040f110103020715020408010606050c0d0806011704050c010e10120b060c0106030c05030613030e01050a1403070201090c12051f0b 75
    0x1002c0d0280740800340a401c09900e860b4026090f50045801d5080c00ba00035000004161034500850107881200c580c10301c03540e4800c0340c2c800f485114940351030f1110100c01c0c5503a030b6403074181a030810090300422444980e0a402e251503080160b40c85003405101c50a4545542c0a0000d001c41808440b0120b02c02261400600a85191099060f510440101c5100d1407540d4405100305404040c041804004188500c00c1d50007038030340c00c003241003841c00c0c0301a18110400f2007001078001c0700c00441031601034009a4280000074400b5003050a402d04403400c54207240e1040b02c82c240010b204118504007886001e52080c2d80d03070255074000b820307520301030400307506000c40c24104080000c034003507080c0c00751004100300361110251640764500300c034020b0700800c6101000d641450940c240050b004983d1003100514070741c400040c18504400c0c1c5291031b50300900100d03d05a0b10b40f102c18154060700c = true := by decide +kernel

theorem cover : BRFrame.Cov 22841732 23021588 := by
  have h0 := BRFrame.cov_init 22841732
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22841732 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 22841732 ≤ n) (h2 : n < 23021588) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
