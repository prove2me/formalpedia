-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5540
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:12:25.873998+00:00
-- url     : https://prove2.me/submissions/8a829b92-ca06-48bb-a4dc-52ba70601d8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 996223021 ≤ n < 996402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 996224271 1250 996223021 996223027
    0x6071b03060204090c0c081902120a020d0801080606030a32030901080c480a0b010906030c3c1e081f1d0708011a091b0403080d02 57
    0x455003217450b841c204405001d44030303001000152140f01150b640402d40c9030000d00034000c5500687c6882d048018014013070a000c1680c1c11b565a000031006000a900d0340d4000711640d959000545a010994080c0e402d6040701a003840400d05208240785058034500710421070b9002e40c0007070712448803d0f5101024a03000012500c40d80c1d82c1c4882c0321b6800c0360307403100443e1509446801e5842074160070903e03060404c4a408030008a60528000c000464803812516542d55500a80300d80d222852814100c03152407404c2d001088002e135600c60142600c0d84080b500449a0030031180030441c1c80e602d001009800380c25070b01190100452030040c40640080c02d05551000c0c02d100d803400d51401c54010749807081c60304060422049070300060841040340c6a40c002d64507908907038525405044200c0d506156038110221301341c042c03c00003c0300030840310010000c100d8107400c48150a10482d9000b072141e40100b6040200d0030041100c4225075502c1c401403405490540e4a6444003c83c5d0091400a41e49a07404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 996225521 1250 996224271 996224279
    0x1e0809010c020c01021e03070b0c0d0c020f190807050d0503070e030c09011203090b0c1f02390d0504050f01020d0906030e01020c03390a0206071b03060204 68
    0x74020a903814200340060304504100d00c000039962a0352140042c815054442c464a00c1c034401d2040701c2ca502d400000000540ca4551011440365006081240700d0706d2070101503200992000c5005c4100c810741d04054202c8069190352030100042d484416a01c03005c00b0004500010001c01c2648401c4607503880d003e17101c0c0307046040a440c2c0000c1d03d000a0080d00681c0082d0340507901e40e51264107441c0d0f040722500314070b1400d04044803803040f15001071005a100140d8001a0000082c0e80407291507640400036640300c0300710324101a8010000c003070101003940c0e50840c1c0c08039180040c107010100f00305044044c5c40300a04402d840c1022980c2d200e008500b00290500172400d180360120f0000d03900380002d00d6107038002000100008060302c900300c201503480c2c0c040e54110000717404580c0703086900001c49843d41c585541ca0b501c0040103c2c4e000c40401d0141880000c15444031800901e07030540342001e0014110070303800b400b40c19403085104650426402014030754901c0300c259410042c60182100503122810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 996226771 1250 996225521 996225523
    0x2120402010915050703030507180605090f040e1c021f051501030c02120f0409050c040f080d050f0703092706091103010b07020a0e0a020d0c080919031e0809 69
    0xb080d00b00c0e6400c055510010543c440e0004103e030a0b250b03251030b001032140d031344440c11108020712110000249220030000200d03242e10001a15015000f120700c200a60851750030441241c2d03403160006250703002002005900082d2000100143c013140c01900c24500304a0080e03a020001c0b101d1741e000f000c0d641c1c0e062150034090441c09220002c801c1c2030400034400d211001a550f151403a20191804100013044d801e680c54040c181d400421082c1c0050040d070a11003219100c50308980a80c960402003013000003400c400004200c404510181c0301c0c9071070142c2540303042d5640c2c2d110007815024000038590001c1d003100d0f440034101c440c40c8d81041180301d801804030554255440c80e804a9551800c10180741080ca0f18007007141d0441d10341040495503400244085510b00d1001d9100c894404080801c10a60a2040c0c0003000080c05882c010010240008401e4814200a2395401c41940c007498000500c1004805104d008074040d090201e211640c0c05900140e070880d030360001c4002000207050042800d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 996228021 1250 996226771 996226787
    0x40506130206030a0b062115060a0c08090411070503090f1f081803030907090f2903011b030e07120f02010c11100c020f090c03280212040201 62
    0x980925044180c0640d40001d03015020207450303607841c6942c03402034110326605c0d203044410540301100b801468802c404800302200100b110001a41035a040703105a42e0b16000088640100194070740d50044106c649440f4606c0d0000320207582c00964626002084030409805803001c00c0c4035800450b515010107051002902d084074445c0c1c0a4905455000d0040c1c0025074080c510307094a241c00080343d83c41404000c145480701e002004540000030902441480104000007070b01c11051007884042c0c41c0c03841000403100105003218010644800115011003000102d0380c0100740100080b07400748030309a118568a413109158000700307540321002c0400c4503041c0f00314401050141000c9488014944800c120042c441500904000c54541d51204120715441103151003800905003656106102001600700005407900382c1c403d401200c6d11028914214030500d108d0001d1110342402c42e01d981005801040c0050030004034003840070050a061641d9101034104001c4000040020b803c05000242000d2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 996229271 1250 996228021 996228031
    0x2010b0103092613242606041d0303180303040503040512101107140f0703120309150b0405010602070e040312090b0907030c05030c0d0609020103060302090906040506 73
    0x16050403080808600c80c01c0e00c0e103c4030b104041101c00200300c80000d000c5148a05a031450440b103064001217124001018140d8800700ca42d2141d1402c444c0030082640c1d07442c0c40c0041514485a44840020064621510150010310203000400e8040b01a1140b5040d01c0b03210304038018a03800072080000c209680380d801110703034805501841c59400e0649460344c4030b10645c040c1500800c3c80a2907070841d00c10412590710362561048042103069403403003402031540d2000701e00b500c80407400c00b902c000c00d9a020034280051908000140401440c640c3ca0f29030f001c503400f21007814035a0310f2100c0d4000c00c050716014803a00204440002d900f516580030081291410f800c0b449c1150702166051048041c1c3c81d20164006405050900d035920071041007002030005100028507007090786042c088040790019560301502d109144215190751517000381660b03103080030002d5070702c102c01206d00d02c08a580b03a4401c8201e14018503011580c242c403a0080b688610090359000c0c9284c0c0a1000c00080c450f050051036000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 996230521 1250 996229271 996229277
    0x3051c0f09050105070219050d03020607030b010906020a02010806010203040810150f03030807080405030409020d0b1e0d1514010b130b1216030f0e1005090d140a030213090207020102010b01 83
    0x15500b0700740000c00ca8000c1600082c0a40707840d9024185002205400d100182402030100507405400d140c02501e81c003069030713200c0c04641080c4000107a5800b50403142c050314520b078000d00780c810303103900111610745000e800c0c1d6040d400104004980b05c88240070045891900100c0403801010026800b01c2c002d61b698014000303060f1000040c00040c0d880600b0340e40040301c500c6c3c02c2000380c4440c2445404d511450707012481c2544005031152200369560400c0056034403c03038100d80c4400d104a5130802c000c4092580c598002034043c0c0c040005611900301d074441c580c5d00b910020398107807480322100000714203802c4400420800b080001e1400e101e452140003501d140c42c2c4035414240300c5200c0300c4514201402c010305010381ea4000700303082ca10951102c4e4a44044000a0103825152048683c885041d00540710109080100007802c00c8000a052403201416907900d00d00610000301c070880503004401c04d10b0405408104060b25003a1604001c00505010313100141e80e1046072001a00311442002c0c09414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 996231771 1250 996230521 996230537
    0x911030d05041715010f21020a05060a17070c140304050604030f06020d0617010b0306010302091321020304090e0c0f102c0901060c0c061803051c0f 65
    0x10056002040d50125500c05040c690200d080b80181c40c20180d008040c1d1001c4d042402c000034401c02e0b1030141303008454100446101003071012054155880011501035040504403078208818100180200f24003940d602e0007010006d5150380640c0c0c10744041d201c0343d001500025520341800691304202c141c444203040118901807401001c5900da005502c4007401c04d8055058070f0061000c660115000300c43d01400030070800f078990703841d403060303840d1130f4840342240d881c00c2803018031401e0001e00103042e6070300141494025901c0710381d8490300c0c48c0300342003c6944103042cae180301506140409400c0e0950025030090340d01c80d41881c0c100b100721040540a81140e511845845a49446050f080c0101c00821b031510f050500c01000151000c4078180242d0540030004405500d51800c0b80301074688050b01242c03100c0207a661890211480044204090112003000c3c0c81000f0b480e000e2070307149400e0364042c01405034242c0c1e03030b13207883d8106003c2520000070300e00303100c1002c0780c0180d0101e00d44143c0c112500f49107903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 996233021 1250 996231771 996231793
    0x4050c0a030f021c080c0f19020109091d0a03120b04060302060d09030e030a0807060b010807091e15050a0905090c180604081f05010f05090a09030e06030901091103 72
    0x4050b00c101140a4000c440e441d00300151110b03a54800e48007242c000d6200b40d900c1e094420300c40e9481840c4ea03035982d15130103405481911001210596100c264050f5181d6403802d0402c1c0d0000001c0c100210358041d8503503030144013400b407441402010703500d0b8005e4076030301040600708007414144c41c240c100c0c60b803240b46890410f20041c3d40340003e44440b04000d46001482c0c290303d10303040d181e003e49559003a03414450703080c01d00304000f8400000c1044900c51502848800c14000054495078420f40350000070504016041c03051101811030645056030200d4003001507a41c0d111201c502c1a8840c84001c001040001c21700c040f1904600d405000b8103040d513100b20185404000510240603070002e06c1c86250302d40000e440340b83d0300c4109a030b000d08081401d50b00880f000c642401403143c0003100072681d55050400000e05144400408400c889024056112594803a05510014025924111305100e007041d1002501e40303503200074600c6101c0f03c03400080c501e480e50074540e507181c55070035185200f42c0c03001d5002e130 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 996234271 1250 996233021 996233033
    0x60b0a11061303050702030a23011103010b030408071a1e090c130c020f03040b040602190210050a03020d05040b100e100e060d0602071a15030727110304050c0a03 71
    0x6200782d601442c02d9a203035041c0344006410030140c0707034015090040042c5000884102c5049070a207401a146c000c020012803004041454082446030068049051000401280b2f00c1402480c0c118403510341100d40702050540215260320603511100b0720081503241442d9800c0103c00550090b040c000105400041d0310b0000e008540c0100c0103940b070a4231183d000003402d00030080001051281001d40b5242ea49600d25503c860700188100e07001449082c3c8454150f5440384a224142d64006e801d6400c1501c0290055809502c00304d1100301b0554200400b441c0c58445100d1180102c5c0f051001070802d0514101601418a03982c100b2407204425a080c45820002101401c040701c400000b4244180d0340c000018944410042e0302510705800001c007901080030010803052482603150580056445003030743c00d41d0140c52411132503019403010b41c090000d024901009040c2040d102000c03d0010b4400725110251071140103143c00206000c002e101c100503041c003408038030b201c007502da100f10340d85180c440e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 996235521 1250 996234271 996234301
    0x6040e0a200310050103050c030114070212070309170706020706021506090402012705010f0f020a060e0c10050705150f0109023601090e0c040509060f0301060b0a1106 73
    0x442038880216407018516101445545072404003008100031a6940303042c03d680319824940d0042c480e500c1e06035814001c4880048490040c5001d07070007040c0c1110050005d000c036601584054051040700720740000c03507001555a0b81100d0b207101d805000401e2505c04080d02c0c00c501e581103001550040032440e00120488044541c0c49001100c058009890364001620580d0303c40c8401040d01100100c10440110301060240841c0c42c20798400160303242206088401e00f00319621040140c126000f5640854a00d40240c0300300200c520903280001042000a615100c26101d0040415004907028060282c103100c005104004048480e81601c1c044041003285c507414090002c0240e80880c8019003805e01e104055800711083c070040300a00001200078000e0700c1000d25032400580c1d901d201083c220109082d0f00c1c010321644110a051500300820090213007401044650840024401104030b80c4c0e00b40070301e0b4010200704221031307a05c05803403000404080a05d0300c0881079a01c04028481c02c00620f20304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 996236771 1250 996235521 996235553
    0xf0509010e0d0f0c1e06050301060e040b010e1002071707080d121401030804050f0f09060103200f090901080a030c0f020103091a150301270c1a0306040e0a 68
    0x1460b00b05040e2524940784100460064400543d2500110340404c5d64008104c418001940500e07009546800881e6548000d0050400050003445030062604050b0443d1101c100c05042a001e001d41c164046801c01620000080040c0d20940040050640c10840307071019000450242c01c1c1030b420501c07211382e601d42c3c1003172210420408001c540c0d01c156055001049041000030868200d5a4a0034190f095030058050030380305090380f0800e0f00c2c203403415090032049810302901003e040c2d41d42100540090465820040c04015807280704d40c2e1018030b180062041d024601c182e5520f0b129002c09001c3c0c00700058000084941c0076100348004a034010b610741c0c41090b07001651303140b80c104502c0100c024000803040200460501c507075500700809680741251041c1d00c21820185d15610410030907003a03500d101340040706490f60b0355503035805041900c141e4030300500418049000c156107565091002241c00c50f0b4010b95080841480f15520b010300469600d0301d00180207004000c020345401c0344030801040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 996238021 1250 996236771 996236779
    0x4060f1a031906080705120a0314091201290d0f1b0b0c07050405070e1e1512040507062105071809020706050c03040f0f0206040e160f0509010e 63
    0x610404070b002c000240b82ca4032400e06200c819070f02c500c0315039100510b0040030303c00c4480b044c08124002d40040c00224040e00369540307038402e40007140342e034440350f000024054001d0290600c02c1ca102200340602404010213805802010080e000ca040001c02d9102c40b25101c0c03143c0181110206002009441a1035000000150310f44980403414240c51450b43c040c0180c1c10010454099810000c1400b4044941c04c2d170f02440240d42d004002c8070041221100168401000d1100c0c4030851113030081c81480b10000303007040307980181c00c00e00f00019411050040c0c003c03d40d128208000c01005005050040c4054142200303c610700c841031415070072814164541d402d5030b410001d40072900c2009400681d2080b25022107140e500c0d99210340c00f03944101815940582040b01142c480213540f4116131065400040c045418001170340c0e01c03d0300058815069078098810b03c80070541001c0c0c174903010f0061b003c0d86030300c0c1c80c10041d0341030142081401001400511000340101103140e604402002081c0400710f0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 996239271 1250 996238021 996238027
    0x10501020303181c030504170c0729040b07030f0f080106081512010f050c0a0203030105090a0e1207050d030e071e081b011713020409020d060903030b04060f1a 70
    0x241c4091410b100c1095071844c854007480781c00c80b6550140e0006008900407100d5690b11107040900c05410710400b4109001c82d400346e24204030202c01c44640b016002c4a040564100982011551020740c000d9080300c5001320002501d0002c0640000f02504402411305044d00300300c0110001034040003051080d0700521078504005000112103d501d02e0600600511050000064081081c0207000c0709170407604151030540407902d607108441c142c884000c000e600652035a820704040c0080c036013020f004d4001c09512144024100c500600c144da00100016111036202d6182d41042232074074406040c1e65041c14a0504172080340c0902044160035510140603661400041d0446011a804580d1110010b03010f1540861402e0100c100140c040304002d907220024555841c00d00350441c0015901d02004000c0d04011000508054000034a000d0004161440300003481c6c940006407204404114000795440d4106c035860b1415104110140041200e00b003141403e00b00c001c90303107101d00c50801034642008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 996240521 1250 996239271 996239311
    0xb1819050a12140f011b0206010e07110f101a0616080f0702040e01061d0f0a180f110108220803040f0f05160918060f062c0f010501020303 61
    0x150080f07102040219242e000b66410464000c10010a4900d09414401c2000303190610001f00941a2100c03000c0759502a03c0e000c005130390003003642400d8192802168401030108070b0600c02d1200d290b80c0200085051101c40f00701c1d40c80c0f05003012900c0d100314014021820440c035103000b10031100354400c10140d034038070300c09011640600030031000075030003405c0c0900c221100b001900311204036142c80100c0341d4409440c1e4103030780e10040111504444c1c0205240050520304541c0c0100c0110790b621110f03c030025404d0f0710b800300b6020031000c09a40300c88200c43e580441e542d0285e001a8051180f140c50004007811030760306000342d1081100034018800100215042c80b030721074030390704020b035100150084d076500e1490301c03903144c1909907000302414004000018940e00903000d00f00c01000001c0c003103e281050359540720001c00301201045a07071692403801081015428140e0f44a41d0504441e100b200304052036511486580285000c81074560640104203a90300007068903007021004405015100309 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 996241771 1250 996240521 996240533
    0x3070f030e122b0506090a110f0a0f0f0f05040b0f0d06150e0a030209010b03100323010e030703091a07080a0309050c1206010603020705070b1819050a12 67
    0x50b0803090308030000c0000d10340700301503042c04030003090540703101c1c0740c2c00c0c1c061110088000c40d00200e5126411914a00000311807000543c4164005d41240e06060b09100040003604040d401c401c0c1d00e040402c181d42b80382480c030f40d080307440d04901c950b60b0b00d002000700d4881400280180203034072900c00b20a00c0407804c400b2280b5144260707245081c0c0144100f117030326681d0090420500c1d1070b52a100210b0003204030f903104d41c1041d14040d000d607a0043d04070710b03003a440d000042006500040c559100c40d502c0d0300d004000540c510244001d4104c4d420b580401042101007003500315518050300c590958403c119420000c3e8004042100721100401e018a503024101590141c0f84113421008009a80c00504c0c2951940c040d030100320b01c60f000704216503035110a02c00344014000242c0c01d6120380e9021030300412045109170001d000d164410000d0342e54540c0d65046c005240e40000f03004110f000c1d508644011301c2d040c1030b403102c041e10112140041e00f03549490f002c21714034500b034041c2502424901031010700b8046 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 996243021 1250 996241771 996241783
    0x1b03030e331621110316111b01020a0203010e0d020c060418090845130c02030408070f060831020409050a06090c0f030818150c0d1403070f030e 63
    0x1ca2030f14140014144035005440c1039101311480168400d68164944626204e08450111122014018400f084058648290781c1d0700540034141148111381c00c41d00161428010380c0e211000c804000d24814008400c0a410440380310b01e13035802480180003c000c1c40b8403c51038514415040c030740005280c0e040c0c4c100385c00c062003200d581c09403442c1d56251400420007a03c815202d00c500b0f10042416400440004881482e460b8025542c405c0096080c2504c1c1c040d258000070f840c00c118011039190a941c2e41120303003004e85640c881d03442c03070b400d14200300142508203030310b25400b10900300c220170101404151f00418a59102c103484100121421400031912150300018603d07801204444070100b291511078050140d0a00807030b01e8501c00040010207281c8255054190f17640708400a08150340940340040703900c0c000f90003d81c4048800b49141c00d0300c0742280204440e00d004c1014208050300207038043c2c001101481141060782e810420040f9460388010001c0c140186444c01040285007042c0042c0380c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 996244271 1250 996243021 996243077
    0x30d05120c070c0b03060f01030b0904060b0a051002010e060f07020d0c020409080f0307021005011d060604051206180a03141b010519050f0105011b03030e3316 70
    0xb55061402013030b040c0b81c81e07025601c030313103002c541c41d25013924110300440030340b280600043d4120750071001180c0001d402c2d0b004549560409819002d840c0d0b5190001030050040200030720141c1d42d103190194048806000240d440203810500b60010300340214000d54410000e0b0042041100c43c01c015000c40d80c66401081a03142c00c40c200d95107414008450001560055956902521880040c0340c4444c050b8011541250040403103400000d44160500b8070300d0500410295004000f0000030495030b5502c400110b0003155880207013503500d0103003407103115200000e900000c5903002c0301400000036440f4000304101140c0c83c80b0181c4442000c2c0c1e110a5a11184003501c209509103002c000c031108000031824a110440d0364240000e0700c490940340c0c4003003c00e000752070005030510042c01c0ca2801c40c1200c440b2051003890005550044018072500786a2175515070401051010b03007070300400c4031a034062841410009200319060401e440400240305003c0800c84c248000c1c1c07424029601d829542c03004c4d9013 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 996245521 1250 996244271 996244283
    0x9171c110d0305061011061519030f0b010f0302060405060a05270102070905010f0603111201061d010f0228212c0f220603020f030d05120c07 62
    0x80750900034001d05801c0320424010b0000514502c80c5520a2520b4910900b800c0080c050548070340280404101c0340d5151241c004a400b00c1085111322001c1c0c0e0701d0021801000000c1c1c2c0c0c000a46080250104103902500300031388070310024009030f6200070456049540807180642d4500c0a407006035040c2c0154102410540e28843c1c04c2603050380811504010040c1c00da007520907103901c0c2c030ba801003164420700404c0c0c440b0481220611140d80694003104013080800c0c1c415003041c4c0fa0400040040070b09030450f40000362060500104282d20700c0c2c00e0303c0001e000b403d0655448140304d000965841c1d0241e601c0f5a021200702840003200045500c0c40e80b04c54020f00032030711702c070019545004402c20000e850380c00562140340302014018440f1800c500d20a00d0300010180746606800c01103800c2020308503961100e4032031500c0403c2e88030354400c4000b19426546c0400c05a1440c0108101d003801294110300a801800c80c80010702c2c1d2000841d0307980c2505102c4042c440d107982900d10482c0c020914000e240d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 996246771 1250 996245521 996245533
    0x2090a05060c0a060f0204140f030f0d0207240e04111b0f070f0e01121b0611120a09171203040c14180711010e12070309171c11 56
    0x2c0510301151141000d40640e105000c400310412800049200e11303c80e501c149100b400c1181c00300e2074003088640341d07040028102c0d400c0700070031010301d428850401004030140e80701400401c541d03c400000040d02c808200501d1041f01e0000001408190800028920595844a00d03500c14100001941c070040100d141f018021309003030017010f0340d80e41075020303440e1244680a4001501d50080c0c1502050307a148010713421540c1d03e003103c1030b00710100100c0c04aa0b81c050051010300740d10780580c030040045c80141c1e45c140c0e0720303442140d07a181420001c000c0c41c0d444e02010003d40c1706c1690407050140c220307540c03000840d20010740b81d19614240265080c0f40008440000144014043c02200d444252000b00389146055007100d01009550001080d0801d13900c040e084c0061905801b40013680c1400003040000309901c865800d55030709061b201e1100880c811004a840f005040c1e1101c1c0e0640504007851070500884145074940785e84041c0720440b09180e0b54202e8118904d5840b402420400b00d81000031504 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 996248021 1250 996246771 996246787
    0x414150301060e1e01051b010204031a01090f2f04050406031b090e0a08030a3804060f120c0f03050d0e010c0b0a0e03040b07050f0d0f08070302090a0506 67
    0x1103400041620755104e0300700071a0403071150804900c1c0036543ca81c140c6640d40b4040009256005200094140c00600e55003840000007088407030f00f1404400e003250141d03d07055810701c212002152041159201004e16014141c400800e02c0030303100307142002d0f0b8140f01c902c9508005421060348a20340046400600b011800020404803080e04c0c11101009071030741c6461619441020200d820101004034541d00c0080024081401e120041da04201c040c00d000c1001420031074100a820003814443d218070f80c01818401d0264000030740252400d1045a040c4000d070710306088030303501c401d882c0245e11200c110540b0a10412075501110001003004980703d07a089a40c90810f2a15046c00c4000400440c02c52a5010400d44c031038055002403d500444003046916400d18500040441c841440524801003001103541100d400103450044e100e500100b500b809110211824090304000715014040100c03210b19031141c00481d0254480050300c0c0050302d641031700000070400c0f01181d00140d040107000500c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 996249271 1250 996248021 996248027
    0x603030f0d020c0717030a0c06020c15070315030b010314010b2710050d06050a0e0307051006050105070c03060b01180909060c0503062422060801050103060b041415030106 75
    0x40003c400c41070701c2c141c45c5e03518401600e040e220005521903410400c00c02d00190f01482072a80c0180c0950001803c01e01d108800e01d1a00b025580f500e0035411039902044025540350103505802440e2801020b81e403413035a81c1d440c04011042c0801400c000500401d002000005d40c410b0b80707030210040c02c1d24400f00e910341c00110405e44d071009603000c500e52413000500115103140e8010494101401c145401d03030340c07034850f85c0013040041c040c0d15400b515500045141041080a04559402100905210003a552031042117410a501c1241400010701c580008194000b481404480e0000d60202d0844640e030012201d28002c000c0b0140390703603110070001c17440c0d042c41d80c020840244a09000c02001003d80029582804101d03180740d408401c10040d149207040b040b1101803804c1c00b80c1c0c0072908200c0520031118488201c4020f00c2603d09402c40c00304000e6034000c00e200d00619007800c04005150410f242a80103101d180104407108400c010070003a2a100e10040034406510300700040c0e2a96140d003401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 996250521 1250 996249271 996249277
    0x2191b06120e0118060e0a06110405040501050a050f0111010b0603190c11030414010509132304020303030117150108010c12020906160206130306090b1602070e0603030f0d02 76
    0x1c422028640050724916010501c6520301001e844201c9401c08a030640e50000a00455540c1071118040d8541c800001420b6004e026844410f8204075516142003109000440f40c059110078450901981c00304119124101d0000300074500b07107081c0b500d90103085400c42c054510100c125401c00000000c000b095045880508020880740d0750601080c00201c0c01183c1c1840d1000c140400c581081000700414148801600100c210606101c1e08002c2640005503030180355606170f151960701e4803c9030419401281c1a80c03616002d0180030401400d060700403c1c0d603800140220f002c00c000000654050403000c0101e04c410b19059143c3e26911b41c5c464a41c240a051140c0004e00070541484400c505aa0280240c40308030001411441c240410b00030120880b140da240180d0300100c080019110404e00314820741d0245000e80c40c0803810204620340000d0084008112009590407440e6400b00c584e40825000c0455030003200f450400c2e200e0000003411881001035008210703000142188a407220b580107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 996251771 1250 996250521 996250547
    0xd020307030b0d050d0f03110c15010f0f140a03020d0f05010c0c05121803070608100f030209040f020102120a0804050d111207030c08070803040215040602191b06 71
    0x1007400042850b4040c040e038040580c800920303d4010b000311480c540c0c41001d01d03064034102441c000c039030400c528208035040c0e0302c030440304c1d10190003023060910b10f60381900b0040e00600c40e0405180e81c0c81d16012440b1000b40c8180070360040c00e98424010000359980d0010071000d1900142982d84211036894900722044090702c0c211030300d5080014141010b80a4854030102d550000007610004854118084c3c4560040101e0306000c2e80700100303030015031010446000902405d1301d4038805420b12142406042e25164840c104140ca4440c0c00d1005894800c940391704071340e02108040250700c141c4010703400d011503070141503140100850ad4001107a44582c0f868052030007601590b1001070b55074011205158a901c0303080540d44850050b90b180700750300c00144210b9000b0700d001c1a0080c865070340d070301507a802980c0665000002005100541c41d2405945202d041040741403450039181c142c001c0e46034400401e03018402000b8000b00c0090200341030f41707205542038040d529070343c2640b07900c0040c00d503140d070f454 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 996253021 1250 996251771 996251777
    0xe0a0905060a06140a11070803040b0c1005060607060509120d1401150f1d030607030501210c150309050f030304031205010807171c080114030a080a0c050a080d020307 73
    0x20009406008059440c841c03800501030783d00d80031041742e0548140c90100c0c5820498800ca5000080f8060248040c0002e008030504a540d1404d240e2201807030200e11250508a00740350209000d62503503008100c03040079500460124103580c6051300d080c00c115030700d0710000c00c050002620302c8a01c003640c0d00c400721102c141645000b842e41c071800c80c0705848040e01e40d05000708440614000740c65014200e440c0c624113210800d0780c480b508501c04a41449400e99121000c41c0d00c40c4014840004589880040307036200c401070070900d1440d82c50300c0c0c0b481e80191192800d00540c400b60f1449813403207500007465098220080762107980b940039a80d503807036000700c505800042c1001a110095407850151a040f1004000201607482c200140c0700013507000d40e46258201d00c2110319400741440c441103c04444c0100c2c1d140c01d11150314007490242144802c143d401e1080d002000d0100004805c40e064902c03020440c030f0481ca4081d1b151500d180f41034403410024042c500041010039071440d090b00114842d01c03042d6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 996254271 1250 996253021 996253039
    0x40608030903010e0721050a08160b0f0403080c0a0c02030102041805010b0301081209040f0f0501150f09090b0604080a0b07090914040f02010201150b0403021527010e0a090506 77
    0x584c103617855051034010321658043c064210054409100314104006004505807000c0002d542e80c0c694a582c003003101001c1c181e015501c4003051000307580260741e0003a2070201c0742e0b000b85400e940050880d070006003005550400858180794152258407420702e00d5501038000c40d520703500c0d8925000a080fa800c2000c801d941000004030f0b0f010009015641200c006400504981c10328070404400da8021044144d005565000c0001c1904414011840040c0c00800000303441d50504081000e50000035000b90107200150040444503540004880f0403240c4514000445400f080000b03055442941c0c041c00340751058017440300c140084400c1c034a000b0222074450640c00350345e0720981000c2e02c00b08459240e00d5603c000c002000b140340c0190710481140705100000d00041410b10f4078111000300e81000c0c4c3e036042e000c01c0138030450620300381c08040001c01007a514240952050032841003021042900146801c4c104034002e00c0e40038015200c07028070024455440303940c4412100c2e00401c002c440b031034815a44c3c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 996255521 1250 996254271 996254291
    0x60b01020106050a090f1503140c01030b3105161b02010e01031805030f21090d050c010608010f02300c0c15010605030609100e0a0c030b04060803090301 67
    0x144154801c5841c094544c00c01c15240510900040c80c1c00881300140719111a03101002c42030349011500507610070110204c0052514910a2628148139030081c103040c41c24500d485103030380d2440e4000c15242d030f02d44200415104200b0001200d12244040710b0b29034100000d00605606e11284220305905955480700440c0d41845450b20f005017080019000c20407804040545520942007400b00c40c100000709429140c55075505840c6a0200e501c00030013000200380c4080350344028080381d415907c1c0710650502da00305114100d850300c0d1301e848050148171b40003640801590007900020000d180050081061450107400440a076005610071101039514110700408107100d401c00350b8036614841003034007190355a04c2010555a22542e4951814803031520f141300106089400310b0301910310340d0b5566440742015024880aa980504000100c0c0e4045000b4004010b4248000d0350150749400c011458822202c0d060f802800c1048845030001e0424402042c070b04000070007005a81c0080d40204042080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 996256771 1250 996255521 996255523
    0x2f03070503072f060f090d020a03060b040c1d0409051f0606080705030907060f0302040e09100b06031501030906230403080a2a0e060a03060e060103020403050a3507060b0102 76
    0x300d03c00e074090400d01c100c001c4000344401174110080054040c0280d0040d580004e075a50015900c120b80d0f0b1a15029141854101030140812001c49810003010603440203100c01e00f4034908031022400360f6030b2142040305010f402c0001d07010609e40a621100014192811903010300560301034600420202c0b00440c40c01c6201c0ca007200d101782c0c50000a054101d0a0078422a41b881001307140380b0825809110106249644a985500642580c8001c0c0300c020a200590742c01c0c1c3d45207e03000d6100318401c2c030402106004000880441c40400d00e0000751402c1d44d441c00c0c000410712000d00b0f2910303684c2c01d856480e1800c628151180198003035141c0d5901d40d1341d04085441519025081c1d04004c44084081500388880c034580e1309080001c81c142401c1c10300355a0007041c8103400008050780020307103440742002a058503002a94011100b0f03c1d00350314003400c2d621190b0f0758806d001c0000f0070000c000e4800b82c6006007490744000c142c000054244c8100c0a03015207401c290b401160061340c1683c40c0c10840000c40d80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 996258021 1250 996256771 996256853
    0x201110703050d0c23090307090c09060507030315060e132f04030b0f042d03120b0405190e0c010e01080901022b0b012f0307050307 58
    0x54155142483e003420381142c0320141a0101007a41484032101e8803401403d0611700c4e031303210001c07120030a6895032203040c1014036001440d844013500f1351810a0720003416038812035400660f0445e04045589441e607140c2140100703104148070990707049164020560590007480304001c2d010855040d00c08110208102d0221903008507007d9940c1c02c10000a038821820441644803514016149410603a49890b14010300d04101ea040503000044401c010402c9888070240c1102488194841904030103081101d514583d02c010207018800610204180c40344150020004207001a0041c03001c0d09004803012801580c0d003c0d041d181c1c605107030080d0b00c402d200149048e03555105230f54080300350584400550316039001078111240da540800168074055010385100c1c0042c3e4543c60007051817018100704100315809040c405040000711280d001c4001c0c2c900f40d0381290b00b0341c42c0702e842815060241740c483c0f651180610080680c08007107408810310040420001c00c814260500003841404120b031030040d01c3c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 996259271 1250 996258021 996258023
    0x3051501260c040b03030d05010f03140d020d082701020d0e0f100e0f01090809210c06131a04030606050a08121305121f0c021b030a170a02011107 64
    0xd0b00000160b0420b24168104004200000c1c042c0c80c9020a00b141e0382c4290384003604030082d0000301800070801c2001803d03660001200c15405810a200d040400a40f241c84410100b07042000300008210b502020800200e42000b041c0d035102c840300341d8114000d021350480c110b00180c00d032808a030070080786000301d0340d40d07a06498440035003041c41100e42e1010041014810b52a42d40c81388450f580604442481420329041c06030f0b843d10740342e07510601000a40c8507503104031040498600804014110300252900d20302c3c5e0225501d6484040d125188500300700c065008901c00071002c5001c1b1101a482d60003001030ba40100c00602a16442d40c052100030041403080c07200550042c0403540c246600740020703120410020002400709175441e800102c0724100070940b601c1580ac144040e80c254015002c07407440142c042d01040c8000000d080c800303912400d40c60200a24040c0601841a513a50180b140102855009010342a070204017010030849811001c0c50700007640c42c08106280080070001550617603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 996260521 1250 996259271 996259273
    0x2011401090b0d12030209030d05270d0314190c051912143009070503030702010309080409020304080d060608270a14010920060a180305150126 63
    0x541039543ca01c3c8140309084c500034201039080c0b00f245c559075014802d0300b4000300940d03512038031220010050a448240460754035151880e10300e456005032182e0380c409032030340c0d058101125040443d0306040c105101b14140b0722590802503880e654019000242041218060700031140042c9103850304a410105481c4040d0104040407611140c06104e44d2083c0c480780c0301071030079504040c6600e00b8184000b60a0605180010303208515411003068030034526800114000144140d514000100e516171040c014040c3c101512580001d0521840004540040000e44070840d60792400703007061035881d00031003c82042907007449400105144201c0c0c0302c5000c0c404458100101007000c0c9028540c0142680344000e43e40a00d00e5030350f0201e02c41d601008a4a01da84002191261040c0380010a001c03070080104540380700d5111085480c2c5845060310180c07811418040c20400d00c0310820086c1480650000385148512001007180904451425049651640090505520030a680ea18002e40c4072541815 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 996261771 1250 996260521 996260539
    0x160822120b130c050303040e060405061e0f0a1d250e010c03020a0c0f091d0c0603041a0c0a0f05090d0213020706150602061308030123090702011401090b 67
    0x41d001c0c4008200e1905031107400503c000c503680c0c00100c0d00315040b82d400500e0311038890b01041401d00b4503005241d071002e0704440f880e5802c2d8903d000c5a9002020001c5180180c1e02c280c907410640d1600203060000e0701000c038281da4181c070a0748221079080720455001c003d208102609055054131102005d001d0b41458030b40030180d801000045403240d04c00d41c000c0d41103125881345800880c18228061001c2c2c40034119424907103051181080079a4540b958000e901041010140051301c0003091a51400c502203a02079900d44030360400c80321212108101c0ca401c081d1030410b12241002c041d00804400704203854140360054003460a440c035018540c1804e4100c0303002c0c4804801864500c400e002441c8511000500345006911040c00300c5e00340e2000c04020f61042d41c01400031b0b41d010000c01da4420903031144048106a2a42e42c00c1982c0010321404043d0401c02ca04c200200039210b001c000a04005030404001c1e1074a000c00030b001e485100104002600c1ca503002040c80300301405846409000607081c1c00b6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 996263021 1250 996261771 996261781
    0x110304140d030504170604030f02070e040b1e07030e010f09021819090c08060a023103080a030203060108063001090204020f040e06090402090c160822120b 68
    0x805071100450407000c0002c100300c0030902c1000d034030201000c054040000e1050b0303d05441d002d0200f44801c42401c040d1f5103d0714042103c602c00352091039010350701c1900c0841c0da460360390741005100c2040c61ba85005040d544100040203a042e8040d04846032034100a0180d43e1040300351104541c80300070080d41040e14000c41030f501c00040b400a40d00408804001c40780080404521005c54000307441c102e840304804002001101c108014254001e81c0360791007185000800d202190300c14404400d5a0640d000308900707101a00000300b94000110b07040380401d0754500c0981c0303004000398421510140411240c0010408606040c002d0860172220041d91071250714000c10105403c0000040f00d03070440d92100ca148005803914005054102e8030016401c0e240d504180340d40b0f080b050b00600a50041e500078081001507500e643c0e407141c1064000442541d610351846104010700311101c07014040300f8000403c0c2000365840140803080006020700034081685441c000c0c0701c0b405100802800d84850703540419 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 996264271 1250 996263021 996263029
    0x5100906030e0f0d0e03120c0715050f0d0b040c030c2c19080f0111090108070e0d1401060603150312120f1a0d020306040305091c08030711030414 64
    0x24002d1250701c0e08607501d8100750704086190005a203900d00c00120080800756150030100f084008402403075610310b040409010440707680c0d00321489188540750f00c80c0a1100058017030000c0340e0b0015201d18645a0f030b007400b1054a80039040358020740780540d01d0031003200f1801e8824828000c208659039110b40c0c1c1203925241003440d24181e00c02c01c4411003a00c0003542d81b0b0f5620724144002b1045600d407480300d518609505103061044007081040c89905001420b000d03181d00d00100c40d524034003402c040e032094031003480807100003103100592500028450040810700c80d4484001a0a0383c2400007403000796280e54003102510001403003009262013044040c0009a07000c045200350585914201b0507003200c42c7c018405a480b82e01003821416940d01c010120400e48140301d8070074110070340307070340c000c10301142c0c04030350b5940c801400074040200c089480f136840c0c0d07207038060800d031001d00364030001101c60181000711b5590700031340d080780200b80c2c0c1000c10102014040117403801c03104414004402048400140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 996265521 1250 996264271 996264281
    0x60804050a0818030609010b01020f0a05250905090109050c0414010b0a1e030c03110703050a0809010b0d21030b0303070807080d0504110f01050309100f02070b0705130510090603 78
    0x10b00ca0b80b90b010303c0000380a0b2010031800344186100b100200c2c0c400802c2001a003005840100041207801c10010800400c500003586094201d1000c3c04625804031000380403030a868035040b8660041c100000c2c030020002c1504442c0400e4000c0c2c080c1e8041c0101c0c101000201d414540084901540c4c08004003c0c41d60303440054401c3c041542000c441c4c001c2c1072030120720100380010004c0042a990388558010341c1c0d05100300790005e401ca64400d45400c0031a100508075000b420107070010403030344400103402c807042904601c4802c5000b400c1c444c078505003490301620560b0312140001038a1403c0342500f14442c4603005101c550100a009586010321035120506076600c0b079030080c2c5411a0402a0304d1003d05188110341c41540550369002509181c0c0e8100300140c8460302143c0d040040c280103120076920040395408195441d0440002c8403503003030740890040d01402c40d000d00030011042c1004910b41e04031000740740d01070620f0054403400d5141c40400404a4000c45040009401082c00f80004ea02a52107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 996266771 1250 996265521 996265537
    0xe04060e0655051509180a0c1d06030a03090e2206021c1b030b0f091501080109060602030d0209060d09030504080c0d020306041209090216020a060804050a08 69
    0xc14003801616001d0a0592074090016440340d00329040140c4807000c062103140c1d00b101c9101d0030b40c403156611400080c51003002621503800741e006e00840d2408010f003080150209030380039040072060b696451100300c90040264100c040544030800190315442c0110350031030000da140c9c480807012400c08405c0040c8200040000c00e2003842414181003500041d0802c0303100e0303031140b000580c0d2105503540107400e9120011102000c0740c02c04584400c4880311082850303100480740f80004d8203c00c201e0014076030804c895506600b0400120503c014070040e00003460700c202081c0c8541006990712402441141c0d0284514001070b002032211554040b1503400400343c50100814860402c040d140402048400c2c0d90800c9010400025042081180c1803098192a074811280c420f810b401e690003098440c0402440105400c0301d04c2c9400b100d03180034840300c0014000d180c1d021911450441107030b1a461070600b40903849101c100301c00080d4580700ba041c0601c0f807603100000d446103419a0b980d00c2d80303640203400c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 996268021 1250 996266771 996266851
    0x100618030326190e0a02131e0203090303010311030f0d0503060a05041505031b0303041403010e0715021e0c19210b010e010303091a0d060e04060e06 65
    0x1c140b2a021074084000750080d09948120249003002940003001c4400110b02c0f40041e8000e5080c0001503505c1d540280b094500913100400c21481c501c4e020500240500e07000c6000340d10100a01001d00b01c0080030714140d900c218032000b481c50040d01010340d07941e031008542d20305501a540803000c451081e000303036070820f2010742120003080d1204006000d845541804100c6000002e00801042c50200aa0b1050840441000454142e51804240c80740704a00845801c01d402004000c03443c0c4003544180e16207165031064441e800d4032103118880880080e006880184142c4001a01c07407101e01131001c84848420b40100000903452082c07100d160114001813100c4c500b0400c00140d1080c00c5001000045400742d04600040300030328101c20161410b070004083c0128500041c070009402c181408140c6950341d5241550f1181e0b600495054499210090340c15402d0030000540032584000c000d000794410641403112640c0300f2081d50359250110740860342c640300c0b07501d0302c201501501d212548075041d5203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 996269271 1250 996268021 996268067
    0x110d0216020607050a060f110a030504050a061b0f030b0d02090402030703060c030c0909270602390c010f0f0c050303070c021008011208030a090b0c031006180303 71
    0xa0000740b01078100c1903065a02d9084001007004109880c441d503944118495010003c18030304080451150040000e07d0007819920b1021a0074403400b0010b24070001c0d44000c00b801100d5000d60251009020030186002190b2000c060ba022a4028001c1030809240500206440d00064080208006001c2c4c410b0360940980b07003001c0f01252980c010107014445640300428602c0090f60000c0c803d111641c0700c1d61910b4609110386030300a50714070340007103e05208181c1240c1d0001c02d082c410024460b4480e00c0010311100078440300040100007010b80303490780c010f071155007108007000b41c6e0741c0383c013201c0785041d000070300c017602005006002c0d10021009081c14a4401d55001440e5511031035507000361941790100380683c010604503d080b14110304409032901e0040300c10752500a01c4802c010141d20010980c800200000f803402045038095404142c1148134100c050408204074002c035881a03031071401c0d81c110780401060480c0103814140744403400da5100301c0c4d00343c03942c1c404480c1d202c041140000588014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 996270521 1250 996269271 996269273
    0x112052e051e0a0911130e070e0405060a2102130501080c0613060f0c050d0905010806060a02070302060c1e060109050a0e060a150803070f02090901110d0216 69
    0x9040c11008005480d00304611281c10301e000c0040c650141c07014044072040048400030143c4550030f8410880301e00ca41c02090108014203008030600a01c0d2410041c54022000040d00e50400c00c501402050b05880b91401132068000340070507100100c941c141c010764407900400004011040180d521401020000c14105103a4001071178000102c0d10403080c5034a910040c00b00312424040165072480881c3c2c039034900355000520001c0301106100e0f420600844150b400c2c0060700450010541c03507400300c01e039000810700b031101800281c0d080c06403d001a14820014505007800c50441311144900e40003805070900e16802c0051030b40c45404000090f00070b4000b83d184086c280d410a102541500018100c10343c1401c40c41002c03180010101103405080802c10300e10100c02203140c80d04440920741c0031400308400701d03d001c2c058009905c080524400054901c0c10300807500c07000100b0303920840da141303850b485082c203841c242c542e5090b112002c9001001800d04061595005101d841030200a0604032045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 996271771 1250 996270521 996270571
    0x10e0a120803061003050708131104020301180506010f120f1d0a1104090b0106050318030a030c03111201060c110d061a03150c0c0106051302040513050105011205 71
    0x1000d48200c44041000c41400b079a0701d020581e1084580c03003031074100043e140c80d01c0d0080404001500d2200c0d1118007442c03001c00c1c0a0702e1100b81140c1c4d50090025556940d65801c3c4890ba2043c180005c1e031400d05c1d050104006620501c2c60000c400883e95600340181c56011000d002000040b0304000d415a40e04185198500840e1040320703180c250760702601078a40305051244a50010302142d500c01c1e031034403100600181c0ea40c40494103441d8607207880c03902e9079180c146862512072031070512a031a03c0f020400c007403003d0745900110f40c4041140e0341800000c2c060105900300f4010300c0e000000520b0102d0061008910841040f440e49001c0c150f10340b40b445003034004c41c81c41d5144400942307800780c0b10040010001d403c01080d010500b01a001049400140300c811040000c010307024203c2e102d0001590390500d2000d411000107800004c2c200c540051117215850000d42c0305100d554058500c20b003c9601e00340d82c9128241c101c4906840b840340c9991009841401413034020260172901440e4583c072070352060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 996273021 1250 996271771 996271799
    0x1504170715020303100e01030f03050901050c1509070b0f030708040213090615140906010e040b0301110918010b030c130b16021c110904060b09100f05090114010e0a 72
    0x10003900611390383d0400301014800310f0703010b411080350561000d00410002d84039070240880b15030103103001070300c400742032004036036520030383c2000c0441d88103c039040003401c140c90041a0040e81201c3c11250700c0d80c0e50780c0d224142401450410b40c1360b12800d0000400c0b950141844542c810301c0204403403002c140c00351111044032540e1030305494466070382401d031684035501c00400300a00340901a89007200324000011300c204100038003260401c4001c04011803039440b150003c14000800400a20150404510703e04054009003c40380c4141080038114103803291403020b030360590307a41114007844d60f601d0111010030b03070388a25081e03116583c003507000150740b401900141c0400e12104030400032411881c010020140341003001071125402000800f4000b40d00004a8850003500340d40701c00207640c840c10000700400060203000d0f00000040200328249240328004d600303550b103400b0341c600795580b104180840080b0034003603620b2015498140d40c80e150700602c0d5144021030010b054840880d00c8003110300c0b03042c0e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 996274271 1250 996273021 996273059
    0xc01090e090307230106060c021c03090f0308030402040c1106070813060606080601030f0203011809051221090a03080621011505120a03080c07060f1b080615041707 72
    0x541c1291002d150420038006c08001703182c00c1c40d100384560700e103800080388181030000010220410020300d03810140541044002000e040c12403509040d640d003002452984200d404030710651405404004141c01002c02900d0780ca400001403c5a45d1082410f80c0c0307c51020308116240c8aa81c00c10500240180c003c04000d40f603ea51002400e0403d80c0000d0b064440c0900810251401880184110f0884100404052003820780200350114107060045c1400744880016a034014000395190181d0000140c1c140041c40b06100008251780700b1490b1515440c2660300140002c2050740800c496280c00d1000f04141d101c1403400202405400010074211485007842c42c034148004e03142005039207481c2030341075282c040b01c0014018643d0555001004000024800303c042400410004103020303a80c0e00880202503024810000f14084031910101c00e901c126030480054140c40c001001d07030a0240c006034014200c01e03031007801e060030511604804080030400c1c40c02c44c0f044010005603400b8110b5958244 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 996275521 1250 996274271 996274313
    0x70c06061409090d0e0f0103020d0608011e020a0906030207060e070f06180b0d1808031504060501051215011403100303020c2403071b051e0c01090e090307 68
    0x45058074060200500c40108450f82c81c1c0c01c107035100d03400140c00440d201100841205c420101c4080c102c01603009004418503207024a1400c0004902c140d01580181505455514041c20000121401c0c0081c3d100d2420a00d00245030100c04001c4280290040c24803030344155408034009483c50055882e15004d5401a2054141e0744000c01c006600706102010015108250040d4541890581c000d02c2c030540100c50036245c0e07940351040740e441c524040d002200303a021a145a590904c2e903032000250300c004a541c1e114a10307047d0001620740c00307002243e61180080c03507020120703079031044000d00c646020303140241031050350070510b0284040074006510401c0165500307885603056040081c586030031940b6040c00340e000342984000d201c1e42e0080c840007161017800c445e5130b82c0e641c1c01d4080310480210119003e01c00e08003500c080800902260b00101c1d90703055000541c60034645202c40d50b8504480b0344048c0818881c1c3e0091011010100025510120704d000326468540160f40e1880e03019442c007444c1000e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 996276771 1250 996275521 996275549
    0x6090209160f0201020c1b0a03080f090109050406061706120d051306030603020901031b181d120723061e0105090606460909060b03070503070c0606 65
    0x8941d0450b80700c0350082100d10013103007013204c0d426403142d585224810400c003a00480044d521544e4420780309001a45e4409003658544014031540b03040c0e1307044001c01902081c1c0381c035804039041c00d00384a03450031a4616910390500f5144110004142c150151036260000c9080503102808881004901004d0719503a4685075500c51030448220700e903001d904044101b504100040016988966800d41583d404c6509818100d0710a694601010f21307507400620304201e42c0a28512a003800d41c00185100b5450085150303480413101d14079190381034640c010074a40c100b030000f0030200350030382e07142c03805070000c1c40b40001c043d5123110140d03190071070403030703403c91249605103010b0140800303c10418018002038643e10040d0500c0400144a4001e0148204241c0c4d603040901e003481c04401c0c2c0c000d0003d10740e002d01194000c03e800c1140c10180c400855800450140000090300380d8551203560202c580d1840903034116207900100302c41641c0081c000c40100502c6141d0f00d00424424071803134000307003540d00a00c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 996278021 1250 996276771 996276811
    0x3041214030f0406140409141905061021020706150b0c06040602090f090108161211010302030603030409020c011401050102031903271406090307120c06090209 70
    0x9040d0300c1144030021581c009004492100c5110300546040d2282400c00c031240445600c46040240181c2c2c0c005003055040403c2840003c0c06200307040d0003585031100000c0082e901d0b00d00c55041e0745080c2c6842e40c100b0032140e51461054411042200c03000f55645003d00c00340d002240107000d98221920682d0f0050340d0303181c210b2000350044a08001002140061030500e50786408484c1ca0b258001c00247c1480d8000031804041d94030884010500721000703046035025612a03011300c0c1c1d204110866205d00d548241008101131014625040c1e446030300c50700c0b84410001100c0110080d401c080c2c2105d8051005010100d10780003180042d0211220a9000050005501e00344400782507040c0d00450540d002049a540d8003409100008400c1005080101d920380709404480940c0c00c0d40e8815421408190100c0410010801c95620441e40f05000b118243d0300d030f461045480303109111000741001e81c1c940e1241102d6010350030081c00d06000f6440003d0702c5aa03500804c5811000b15454452001e91100c542 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 996279271 1250 996278021 996278033
    0x6130803101d0a14070206190212090f0105070e0d080a0203040503030c0d030b04020306091305120d05040b06060307020601031202010f0207030216060516020d0609080705150a140f0403090503030412 87
    0x2500900c54501c40c4103045c4500d01a4030742c2c10150045101d00d840c18a480d506400d5034049403c03034203031000f440328280707070143c0308507161245101c140c9015404c1c41c001c100031358810503045c2e50f90440142201c0c00040c0325642c40d21240c0c080701c1c0e904158041072000281e2070740c1c280b000d00700b02540c3d007000c2d000f0701c2405040203048235030810707466100b58414400e01003245c85d65410585d01a5000704140b00070b45850500c03c0c80c0854422607241d07444030006071842412601d40000d80624454403812203191654800c008090008941c41001648600c00400118640d030a40b002c082005d40000903a1031070310900c2c0c500341c0c0d0020b0025070150b40038042301c40c040407050710381c18020010ba1505070304001d40c10f9503d5400d4096100003900c2020750514903010311965a000130035a41d405031401382e84021350300d03001c3e464010081c4000d001c208003c002503e42c5080c0e00a000c00245040c054034440e6640c030b030700d803010f84001620503420001c0c00840418252000c00040c4050107610a02296540d20703880e2103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 996280521 1250 996279271 996279281
    0xf0f06020f120d0b030a120e0f15071203180305070b060a0b0406050705011e05040b070c08161a07180605071e020d050a0305180306130803101d0a 64
    0x404102d9001d00000404042c0000960307003000a51400480c110485000107032800071000c40203441c0340000c048081129400c54001e90826005940948086034000b0811100f85059130382d8010b00442013100c007000580038002000008918100020b0b1190254a02c3d40c4501e050b4074200c011030710002e81c5000b8404941c41c1690b000301d0880742546500e0405440403058000c1c0d10039942803090209500081100a4025080a0390340c00c4090f0f084a002400b9040034100c02d031000e0310a512110089824148a450924540d64100884a29141d1040c03240340804480c400705450345258075071020200c0d180c03e10702e9030058180c0e030f031440144850072089112102c0e0320b90026080c02402c02020300080c07000c4849801c003015102d03407a0406156400030404c072a004100041140c06981c800c20201600200a4540342e1008607800001142d07030001e055a59900340c810441000c80840001c0000d0030300da00441d440009207000208055071220b4450140801103004c01140d0041c104121a60610340300e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 996281771 1250 996280521 996280543
    0xd0305060301052505040503100c09120b160905060a0c021e01020a060537230f150d061413081801180305030711190509040c0f0f0602 59
    0x3c000c2c9052105510b01442214805140f0861283c0200c0e650300d4003440640e0003c00d4060196080d40c1401d0180720001c282c038a070b43d5404200e20441c00714280c406001ca111019074401c85249281e2509034030802c03460422031110040080891000c00e550b220b40b4087c1401c00f0907515200200103582c410020038600344030120810800ca030380c1000881c0c2c0d00241881107603405c0400020240c4407044003200118407400802c3c103a001b041000311f40c1c84031141c7c4841c10000c500104020322540031549401c000e59480946070464003c0011a0a04d420700c185c042d04074008030082c200320902c17500840d0b007001074208140d86040d550031300a020f103480e24071641c0c0e014000c0903400035134800d0b45d521456607001c3d141c1c000c0d04400700301c0f0035801c0c2e80c1d000383d40c6191106424070b4041582036a9280907030f40c0c0e5102c180121615105486001c4850426150450750481695a40b445072805c00c8140155107500910503503650751048000035200c0c051500765406000703d10b50709203000d82001c00207803504520902e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 996283021 1250 996281771 996281773
    0x2704090609231b12060108030d0e1c030507270518070813170403150c020d050d09060209060c010e1209030601030b28051504050906010e06060d0501080d03050603 71
    0x140500e002000c40c403a40e483c801c4079071251840c840e100100350284141080c085052280c40004110014000041c1c40f45038440e840a000101005040b2600d404402004400d50285281078040c40d9009411150307000e00b4500c0c3c00d06d5900416454502070703041c0c05a04800a104449c414000c80c1040085801c840301c5450840100b420142002008520014002c44441d4100300c050007c001d0000480d600a075488106161642d440e418001c000072402000341c002580342200110205001041010401c0c2603500c400d41000b00c403030189006050701c000c0c1124180e608204440c150350300c030b2010b01040c80c400b00000403d940d01d50110b51074000f460405211040040c042e008055400080c8681541e034490348024884e180c0403100302c0d0203140d440c132010a80081c86003410b40b52000e03a0006108041328072209861840401c00c0c04100e41040c0c0d11203000740c00c660011b1080c0c0507e00d011580040717010307001910b0b04205d00b8401b02101c000303030040491500300d400c0840c147ca6040c022207030045000c030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 996284271 1250 996283021 996283073
    0xf06010b25390902220e1b040e0f0a180b0103030302030c04170703020103051b0306010318081803070609032001110601140405060402030c0702130f1d010507090b2704090609 76
    0x1d21800c548400c014041d040a01140450582242441099400500390212707081e046091441006001c0141110a880c217185001040d40c091006500d1515403560008000d0307107564259201100654801410301108c64420000011043c00c5100351010915810001c0c0110318150700c001029074502800d891074001300b101c104400142108122030300b000b403d080002e005060522581d0ba0700d1641013022300304c1034012940c0d000c803103854010010203a07803c07016181c80580300c03034007619214014003014007411004440c2a40382d80c144881c0c030700058414144001700000d0030140a20300034098022545c5c1002e80140015241404d014960304048112419415441e0143c81c0c0d4801b4000c031034000e84078000c0059041d8256132542e011542c0c56030000000d2003018003080c6034200d64208510020000d40ca801c0010324218825007003d07007a42c2200281528203144242c0b0701035086080b2100b510502da19802c85e19450386c2d0f9200d19500f4910401d0040381c140110700300070743c0201e1080c1d10152288401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 996285521 1250 996284271 996284279
    0x1606050c030610050304020d06090f02031203070504230d050d2d08070309150b0906060301050d171c05060f0a0e01090e0f06010b2539090222 62
    0x710702c070f200c031031200c0e480c2c8540c03646d8840c000a82c002101c00c80250285150083c0036040c044601c881e000035a0080c3d0480311500b880524195044c801201c2ca04c1c0000d00601c024420443e448009408560150f00c14801802d81e200020b0113204608074115900d078011b000711850581c00800b40101036042d03120703886d6081048910100c0514024891600700b1805900182c402400303039004800c07082d004021100110340e602c0d0302c04e000701010018030f0300c100c2c03290340054494079107401140c1c182c074809042120350750304664441d079800c1091407a0680c21001403202c411411012400e00743da0064050000c550b60400c40c041c46011807840c18190b01800840000b400014400000181140d01c5103030002007000900d0b420a061a01e502000807490162100005410b480c61000d00b5511015082203000021a0012180003840b50000100140c540003000c0030440c1c82c0705841e4408008814104018050346840903214203455080718007080d0b408141c1e003810050040d0480e21102910066213411420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 996286771 1250 996285521 996285529
    0x7080705010212090102100c030f0b090615162f04141f03020a0b040603051608040602031504090b1906050a150918200a0c030c05121606050c0306 64
    0x2580303c2118210800070704144581d20800c10745801104041040107034001d0500001d0103041d40c050b007000800d04102d100301c603502d0315640050041c000102030f0503070345480480005464025120802c5504800401c090200f4106280e0807400d0313428804402e0090396101d031440200900305034040c000d0f494100724100c2425646140b0307801001c200d200f20000c50203c580c103900ba130386a800080d00928501d9001603031940c020090b100f62030b800c0d02c0c18802541d48100c840c0c84103482400e010000342c0e0050114000ca083c40d4000c0d0380000c200c181030814680b48038007103825600040011510460b198080204801110340c2011000552960a000992800c000a1903400c0b0300c1c011050084606409520f01d2801210b0000080c50641e80c1d1940b42010380148400410441000b101d8801000890700c20b8140910304480745030b80c42d03071540e4084403e652411500d80d00005011070b81c3e403061641d5400304001d51000b1b0000910084400300c0c05080d01c1c80c200c0300b41c42d0050722000b84d00380284240310140d52 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 996288021 1250 996286771 996286783
    0x507080f0609060f0f0a27090b040f08120c0d0509010227061b1e1f021b010e1f0501050a060f0210060b040305011506092c0702030903070807050102 65
    0x2400c40e2002c0d48644e00d040001d070342d036418001c0d0360b5003e003841400143c1000411042c0c1060001c10404800080b031151202d010340340c2d80000104440e4000380000c002a00501b200c40c043d070301401540d814040d100130510b146080c2500c10f4070200d100403075481144e240744d02640c0d0b03004102a00035800c00b248840c49541e0712041540181c910103540c02411015103aa109803400f581c400e040780c84441d00103034045030b25500d0070a2a514900400c4c84540e20304480083c0c00700302c0b501b0401d1302408024060b25284000d401c20008a1804003c0c0c00340d044402d1001d000380103032440c0c00005030500451350064119507484810a04d0242401c120040005644500c80c410886c0d5060522040524203000c080341002c00e01501100c6051401901040246450020b0401e07a88120001c100740518032006245900d1030b4422500000c0d0040024001940e25108a03440a05500000e02c07550060041003812540d00321040340040e03001181000031440d0402106008040075806081e2160030840000d4840c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 996289271 1250 996288021 996288031
    0x331b09030b15060d02031005011107080303010504020d0f09030e040b03060f0403080408071b1815140301020405060d0f0c08070e0405150d03080a060816050424090507080f0609 77
    0x80002d4003601e280d92907042c200c82d11100e4180c411552440c004210404842407406280d00007400309103003134800303d0009000400c0e0b0740c414009504603132900301080060f60000803105600c030f446110310360540c030850241507007651103a201c100f500f0745818144002c941c100001d05109134440c80c184081410100700446e001074162400d030100e642d0307500300302c8480e2142035001000c1c43c110a403012490391098102e101500e00c94045803800002c022180c1080d05d4a5005502c02c0c000074410810880e01e0f440c000c1450301c00050000340c100b81e07075800003c0540e0400000388a8841d00e40030302448420451003041041e03015401d04800b20b041c80c0c68000c103c44030780028070340603680c1c0e03c002c11100c64120301440714040c80202020100ca640d80b50003480c1c80002e03580d0341c10705401c0803c0071540c01d1011a4500040d0840325020401d281342100300000340041c121500c0e2003080d0103c2c17a2603c07140280456028210100300802e642c200580d005240100040a500c180c080d0401413101942d943c0d85a15000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 996290521 1250 996289271 996289291
    0xc1401050708070f020607051608060f040201020618011d0303060f0409051b061c0b041a18150303160b15061602010908010e0a020406120807331b09030b 67
    0x100d07005e01c0460300922031410068014801c01005201442c5184d040000740c4560505036146071302c6a502c1c41c1014402900e0080c0560880c40000304100400406103400410840020460140c0d40c41092410040c0e07807180c1c03003590030000422800382004466000030765415581000104510340b141d644408081080c003064810345181040c02c0c1d079606082e40c84021034801900b00300c0911084510050014404603400b840c200800187c940b6030340010340d0701013007005d8100060040290501070850200416030410b06140302c605100e40d45003000036003c030359442101603240940d14204030788440401441d500c540f0320032040c011010b483e44010340745400e04584250749404c03850320050311801165000482c440d03107080d5152146000000e450401640241c41c00c001141e16000070700742c2481d10750000344c520b4404121640000f0f0042e00c00b00100c4001d032020584458140c00001d10079284000118001515a103000c80c0c41000d24401410143d1942480d02419103160f554561004006003e0404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 996291771 1250 996290521 996290543
    0x10825050d0207080d0506090915010b0d0f090308041703011a1b062505192601080303070e10020a08030901020d060f031109070206040f03090504090c140105070807 72
    0x81d28a00d4064460595000842c151a100c410759200b00600c0c1c202e9044e40b00e2849039010440034140814001074054250903010724030382c03c2c240c0100b01c82d4070003481840c40d00d90300c01206840d28264441e100c4598480d40c2c2d16401ca0800f4107000259206603904441ca82000b0001005a0b070700494001d604e08100c40401070702d07017915441004d04401c4050800106024000030070402551100c2e0000440791458440101000e40c0c81040340d15014901e500361180f0200b101c02c8298601881e80c01200810401c02d0030003079440864004610502a4440a066480402445107071034001182c40d008504c1a9071240f00b102e08007034000e554a41c600301c003400003000000400c03071401c1c0a40440d10b1980d2600c1c42840900e94551000359485a6484292075214800d4075040041c030b08008034034003551b02c580c0100400c0d100e5890302d0b42031903d11a01241440500000043e05480341e0144200507801500e60340c003c24503200200004107491843d003410050100410380014003c0001d40300083e400680080e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 996293021 1250 996291771 996291787
    0x30a05090f0705191d100b040608040f1e061e05060609190b1b0c03070f0911161209051c0b0901151215060b040b030603100e0c01082505 60
    0x1051000e54001180c04407417010b01c0700c0c520280d10342c0540295001d240c0c42a100d0f076500d84000c1980241d002c3c03e4001180340e80801d020416994203084164000c900700080740891030340810740c90130482d41c22140652074040307100b03020000210341c04503980010410703c0507140903030010b03076903108135094644600c940381c81c1008608a02c03050f80340a00480040e02d81d584410075100008946080b140f01820f1141031500d065a040209810742115804600e402d001c0342070500401c06484192001c0e0301c021402c0c000e400544256540c4180064081c07071410402140415005045159a800c001d0140d68501c00c0070050900e5191507612a6400c0b00d0940c03071545030b88440c1c6000d46902e20400110404520300032480840501000b004680301c0d152074442d818101c0312000036038031302c3c0c82866003440e414041044200844002148d000400a0035645000c0c0a054140210713011b07240400c60940c04a44e08800a507000182160040a0300c0030074039203185444e0b0700740101c0681c2c401b818100400860300074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 996294271 1250 996293021 996293059
    0x9050904030c0212013321030f0314040602091e061909080f01140f060f0f04140c03070905030c09010911070b0717130215031b070602030a05090f0705 66
    0x42e41c051078100410400c980e00e2120640300064030080103041c011000140c1080d404d1075808600382c03860040c5030b047c95503201070398a0911550410140740e111a800203d0606002043d40f0542c07103400010784413032840d024409907410002d400f002c031001420020b55241d81d10802c0d190f000384d00208072810075030303446822500800940d01080e85440780da04580354112040d0803005039104072500c0301c3e0302645c07002144101e1107001e40740d41c0c0d0842130012098009007400c00c0810462100580b02142e01c3c1098100e5910f0113008584041680c4808810b00141b030707902c01c2d8200d00401046005048400d6020000343d035440381880303010041e030354039420840880c81c07060544200c150400070b25402ca14240c030010340b607142c00b00c407284861140301002566040030b110030515220b030090b099030242101c135014602c01e80c0c00900b206004d5034203541d4008682c1c0001008019080c4038000150310b038280303254000103a42c4040c0c44c0ca48650040e6601d601c0500000542104540d4201c81e800300c542c0716800d600f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 996295521 1250 996294271 996294281
    0x180915020a0c140f030d020d051f0b03180d02071e03080d0203220f050c10020a0605060f121b06030f04060218130b1f090e100b0309070609050904030c021201 69
    0x1382803d8040400ca212440c5020b50140050781407890003403040c4da81d015040d10480d10016480380c030103540d00d03005000305d800b2032014582c04034107880e14035140c0da81d03a80410f140841d043d2070b903001a40040800c0c0080d01d41920800201e58400c0035009800f404d60344c800c00c51340183e542c2040a00c0e8003000040c04503004021120101a0a191f030441d12134050410b440d070504400000d031030501c503840310b951440c2000f000d41543c111940d4060090541e065a448014000140c020f41d40700103081c950b140903a8609910700402c5842c3c20040078100c40c08442c00585503082101c10b03104800034030030400b5941500980a81c0f09500580c011380e2100c0c00445040d0403503030b49a100f03400c00c4402070300303005900e800da0095184100845c0c1c0d150040c040342250314180c030480c10340305d0005914240300700211200c1c154481d1f080303884034840410640c1c44203603807c015003085607481403e902c119020082640c0041d210030140c00c0079200414070b454103480103052600d0500d002401114200e060b665018004e52003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 996296771 1250 996295521 996295543
    0x1050a03091506030b0f0114011d0a03050601090905070909080702090705160b040605090c0f0d081b0c120102090a0b07020d050d0806010e01021c0e030304180915020a0c14 75
    0xc1280704d13128103040900907004c4902046500002001240d4a010f1025000d58035405945580d0805015048403600310310690b2a1a0040d40c080710120000b00d007070142c10701070038003d000020000f4050905a02e040196808040ba0601e0710101c400450107050440c0e403440c0d01a54090318546a1081c1200e043c0f0901e0021242d03815083c00e90130401c502c003070f0040e00440c012032080c081510750f1041740b901c0c2c0440e03040640d44078440c40d203c80c80c07504010000400c124024032000381803030344081c0c07035014440b0301030b42c0c4600301d8110081034800d52505440f040e0440751200000c5042c1030b081c074042b5050b84018000c039042c41c1e4000c00c1c540c045548412510b908180d120042e40c40ca001c0c80728014000240a5803814041030344070300780003007035440014400c44520400b580c2d2055140c901c00b00340c0713251a41d01f8140d0b4150000704000700304200c003420500880012000000348200107410308034900d0b40d41c0c109020300f082c01009180c02079988100519002d40e00401da411000703040f108450320302044401c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 996298021 1250 996296771 996296813
    0x10203010b040609050f0a03060c0507080f0d050c0403030804060f1107110a300f05030a170703020403030509100306080f0105011701020a050a12061a131401050a0309 73
    0x4004905003075401c0c00b402c100c0d015500c0d01c4145589074010851111a0201e0041d042480c2e480100082004c0b40c20903c7d1880442c1882d51820b0101d4031072041d161f00c140f811031000400040c05680c0d00845100ea294024081400c1c0b43c20541190b600410503800608058206902c891a04266546592003600b002050b200b0059840c0280d10b01070034803c0d903c0b02443d115000e041ca00003080440d0b0311a0b003a400081c1c0d00e449020303860a02e4441c2e0307a147e040100b902c0e0b4868101e840e030009102040180024002901c1d450000c40031481072a00d1810018540340405006100410010f078000040e100b010304101c4036401c4001c0344810840080c81c06034040e403910f03c640c4425809036601076000c241a1042807000302591010301074400e081c0d10940081e800003a008009800841e44034402c1c000c43c0e04984440802c490703603070703200003088550f10b0001642e1400c000030701c924400e4200fa014000800b10000795048078820380d00060300c91301a86040c82e043c1a00e481142c3c0c02c008141007506c182c940041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 996299271 1250 996298021 996298027
    0x18120c07050607030f020f07211e1401061d061e060301060509031b0105070308040f081809070807091202190b0a14070f060e01090c080c0307052e0207080102 69
    0x100b8005c081522441c1c042c4054052054805070078175001c14000c040e0f48000d40c9003001c4501c0548200301c6009458000d55864120b62040f40d0480045080070030b41a00031004400901c42e20952182101c440794804d00b007002030a03070106506285001030680c041d4003201c0503400f81d40c80161070781e011343c8401c4100394460000000481c40a0b000000303890b0a6000b50226081c2d42626100c090703500120307400c0c0302c1c0172540a0000000091060322030590081c4658009440e540007541c2d40310994000c225100b0044c0c2200d41200214140761200c242e1201e414540340c1150304216402034100040c030b010b02d0703505443d268410429501d900304034000041d6403140b03114cc165990076002219402048880340040e10140810b8a9103c400058802050300701c13000c0345800c0d14540e1a40c00401800c58540740c40d54803211810040b07584840440009e08120010b01a5000c0c841d01f05400d111040d0030440c45042514540703c1c48403504440e01c0304504e03c1d0341e400a400b0540c0b031400e072300e040c0c6140d128100540c000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 996300521 1250 996299271 996299273
    0xc0315030115140102073005031204061103040c170a08040e01030309080a051c030b03010c270308090d050c0a240306081b04020906040e04020918120c07050607 70
    0x18901c4541201c52114148907a07101c0f05004907118200d911601401c916038a05061011480e00301400003250140d14070040703288207a0724181546c014201140c000040d0340200000c0c89000e0142e9420310ba411014549140341a030344805508071103008079400d0b909032030040540442e0030080c800010390003a0302d0503140e41d0343c1d60900030003c0b0700740001c0300080d80110300020700b0080080c80a9020758000040d02c4480d514031400342c100c4400d1712003401010f85500c070f05100ca45081c07144400d204241d59403001d1009928404188240b00c5280d0385010912085d010404a40300074284c808030407049441c01c10600590820174544203181010342e5010094030300000b142050442040e01d403a05811000900c10488201039045404a11803082c0581007880950000312002c084046220001000182402d01e410040b454a0700141c01141c503810346e050600055151002210398810b480001000b04040c8140c100e03500c0e1940c500b03921104480c0410702114011050240700060304010300995103495071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 996301771 1250 996300521 996300551
    0x7090f0501050301200a1107090606020102090108181216020a271a06030a090c0b09040f0207080f030a180305090f191203120903021f02040e0c03150301 67
    0x82c4500d511030740c80d00a040d0081902d5926044c0c101180d07000b0351381841c03144070058900030a01400fa60050285a4001c6201c600d68400c1d4806000f15074001038481c04408005081550040d144140007042e015201d207400b04001100da580c030a81030341290700c0d01d9001e204048040c1f81d900009611108050011480780010b1034140f210403510382c141c20304500105051800c58403000040070b80303003400d5098008242000802940c01140841d00010b0b07a010581f21207402034450303003200c4208040091000468a0280122448081007a00841c41c00815070b85a115500c1038102c004211840880007410348800c03684411740c80055101010458241880c1c014610784c402115a0f1144c1420345025030207003002001d140011850114200354982040926000315040150807000c0014600300c0000b850040e00400c00d140707104e40c0040c4040030409080581c011400014500a41e2050104020b0b0104110b8540e42111403817141c10b50300d4443d440700e40100c00c50301241940541c20015140c020442c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 996303021 1250 996301771 996301781
    0x403030c120c08030601030b010c06060e1b130510090801090c03021503060a0302130e1204030b090d09050f010908010c080105130c0c023303010e070c022107090f 71
    0xc894001ea4003107076011482900d107600c1480e000341c00802d00384001000c65000754001202e545050400c80398240065480406075203c6421007425904004248444410900e0000c80d50914070552641068540300c142c01082000d4410148681e0f80d03059046881ea004034031304c90140c10890020300603840d0600b000c41400056100880c018402c05803d040c3d0349460354149ca0144400500c0100d0162850b02040000c030803804d00d1802c0c09988000c0804c002d84100140000031620842c1c40d03071140c4c50341c10000303141040180400314640009140c0a200e0760b0054038601036036801ca420980d0b030980400101d5890740583c12041d803542c030706190240442e4220001078100c45080711042e54a80c802c441040c00e65210030344210100b449082d4000061900d80c0f10440c2250402050007039500d01c000d841419001c44480001032640008014001d065181c070500c0d80c400b46a04020b10102d03050b501040d0b442442001140d1020755290302814018005c3c8540390081441090500503d0001c02078032005007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 996304271 1250 996303021 996303023
    0x1d060705040510030e030306010f0302210a051e0408070f17191119051618060614030403080a0e100204090b041a09090a05190501230c130b0403030c 65
    0x1045050039291018424007501d81c0d1440746601460840d1900e0700152603110035513212b14107164003440000703c0400d41c6c6d07a4100c03035806007000f85026410403140140c00c4031009424005104103800341d282d045c0c020940401d410a078030640c02a500c51311818540c42c0384051000003400d01c84100c581d0400425417101402c03d26000c5107000d5140302003103805403644000130f140f00c040c513000002070aa4981000c025254618022010303900840c4c0b004c1210700541c030058201c6103599011000d840d4141c800303441043e02501c100e040000c1448400d6090400781c0c080100300a0400c590707000001c2c030488164101c0711504212808075000581644610b40103034005020f1190001d01e46031031441146490702841086500002c20396104075900018403607a5500202081500d00c10f80d400c1d00300145040007615162250385c8101003141c406441c06a095511503103144541d04000445002000040661301c0d411601d140380751583c5a0800c1488012468154011030384c07040d02140000515410002c204c58103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 996305521 1250 996304271 996304279
    0x1030605070806030f07121502040f180c020303280603050c12012702011b0b0a050c0306010e09060301061a0a09061422050d150c0c03020a061d0607050405 68
    0x99070b43c4400d1540d070b44003925080b82c50341d12818081040194400e4010314550184203214440400d81480500741d074820b0b130003840c1213a4642030030028611500682070f07110f28210750074004a81e80d010002d41d41d00002e8205545814a5003a42c500e0004034001c15944008446040c403c41d56242080d94541e049561098010504103a03170030300c60901881102404202030711075500790f41e5083d4101c0341210b0041030881c144540c5001d4a5040c21906490106480c8201190082860042401c01c00d4500203000307100b2184050051001c2c9a07080340d101d0030800d0003502c070640280e0b90311001a006d0401a803050340205140c51b200441c175104600100603404290700c400d4142da5072501d08580340c0340302c3c0c10100d1000c81d050080305114140010310600c007a401c0c20302c07040041c0c1c0703a40005051055090040b11320100d8215003c40300c80950241900c1c111880c1403c0b08959640d803406034451039a05802040d803030b80d803003a070040300c2824044030780c03440d107401d084030746d40c2ca031a40300a015940240111845 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 996306771 1250 996305521 996305537
    0x3072007090b010e090412110316020406123914120a0503040e0a060b0c0f0708073006020a05070c082a240a080604090f121101050103060507 62
    0x2d19402590035400703000c809002c4000c02e031b4454030340d0020100703000301440401144140c0c0680c0d400042002c0c0402031000c85007461850007520401c41144c1d841d501040705003580322011408600d030702d0000880100e0220f02d40c0510101086000600200144081d05c45503d031800851202480580506840c80c26112b0707070f080a0070404c203a50b45100526004103039038010001400b040c0c04c80004141c100c0e01c41c1c0c001055041d00c58440200c5900420030101055004400d4070030301a02c02c0107040010300e60000034120090424000304900e44c0d00c0509800f068411103981d1011001425a8010164001008540700d08215a0040031075121f184243d41d02d00e41d0140c0400c071600e002c0307007a0701d0401d0540401080340c1c0c0c13181a448100c1c4243c83c005540030050450f8016005442c1030003450300c500d0038000658442601501521500c4090101c3c0d00031450b0414900c00330702c5612200d41e000c1d0308419070a45000c03c0344001c44414215104511165080c01c00001c10800c80d504003a0195500ba2901c0c03a03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 996308021 1250 996306771 996306791
    0xf03090203030d0f110c0a150f0c0806040c0f08060103110d11030105180f160309021306170307020d030315090e15070e031c05070203031c0608030c030a03020307200709 74
    0x2002d400380800380d02842e046561f052001030404604081c01c20500031001c1000c0703494012000484454100303410200780803404001803807130326125900800c5000d080003240c04000f280002c14200d40200810305040e600d00c00030329866061010f82c0c0900481ca1400d01c403005444070300c02095007081c07003242e0040c2023a0508541c420601c0304031a00ca11345074100c0340000d50700e42c0f100c142861810004602819550412000940c80b15200680d1158000350b0210300381e85040c925044402c80c003101c2182e147c02c1800038800507507441d00d1484400d81c1528010030360180b0489003c0c2481c1441c0d01180400b03180c24007a00b45c040000c6115900d004214900e60360a990b07490044e69400c200c103c94aa05801ca8a205620010b0050500304007522a2614508100345036011920f15801052803800907402c0048120313074000c05000b01d001800f1060702460402610130310303950340d03805544120801d064011001a01d0148501016154011100d0040240030b46c0100d0b05505e90540b800345946142c03d00900e05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 996309271 1250 996308021 996308051
    0x1060605070f030e060702090f0f070f091a090a030302011e0249141006050301030602180a0303050706060608010803040306050603031306181a0a0f03090203030d0f 72
    0x2481a030b0442241403a00c6002c0d50203e41c83c00059640c1644240e081c41924090f85820380b245218031901000b410003030605851285005000900400c20029806d585005150740405584111a41415a051100c008443d008810700804955540007085084000305159054001000c803003c50b201d03003501540c007240c0d403500b03038458107507078401440a0940c01541043c0103000303030000d03503480c05416080030491203040002000883d558044c06459104032502480188012600107052040f0350308043e01e00540500f09020511002d00102d501040010006050341c04e10404401c00030041c0700c02a840c0c1c90007910355008104203544003403a12801044090042100e10706035541030005504140c556540c42c0c0284c60b00801e0b035901404248441d42880801104a1010f41841d031142e02d091000040d0b003e40300c42e0704c0e501c00c0d207034540300030900020f0030f091504a4004201601d0610544003c03544281c01402c60f40500075018807001418800c04181d507440f10398946c0b03140c1003d1105c52104002c2c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 996310521 1250 996309271 996309277
    0x6170303161713141b0f09070212161211061302030705150f03151005070c06030b180c030106030b0f100f1b0812060306040b0c090d051b0301060605 65
    0xb0b039082e80c1c14400401c004164a540c440703e45449a00500c010b07182ea140800d0070b0200c1c1003d103503204840c00c4918242e500e400340390316030f22850598441802e488c003001c3c0256940303200040c2004151000072402c141000750b120000c500f98020003407910140b01c95000070704070341030074090420500070000420452034408110300c80143d00100248101810300d0100301c3c0d400891030907052281000c001c2e00e10000d40d44000b4500c50350b0350f0b01803003200c0c9100340705201c400820f0720003078800c010080000d680040d5090103032906490040c0f4002074a00d1200c804142041001c00c01003441050b03003010040d65550303050081d8180c6606a07024040b4402020a03c40a080b80005669001c07140d0265526601d1040c0d0364140201e000b8601240d82031602c424840b0142800041680c07420000100416001760348900603070001c809400030021482c050b111503540304005004034421220006034005c00b40c0d00c0120000d1019004010346203009000c6a0500c2001d004c511444d000b5400d0034000601d0602583c15 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 996311771 1250 996310521 996310547
    0x6071101140601180f09020901180f12020607052a0607022101150e060918060f06010e03010e0105010e090f100209030304270e0115090e010617030316 66
    0x107501e6280c0b41d02c07005541c0303006282c10718195120b1026001a402c0c6002681d00b00418105900581c2c0305100d000043c8881d15580c44000039110018081088441c0120142e080300c1032580c040c01400001e01c0000c3c194490020040c0c040d208005820030020304408500400c980b5100c03885129465403020300c215030281841c082c2d401000b54003e1034010441c0d500403041070310000e000080d0360030030030250403180c2ca060f001b846062603910208101c40c00c20300800c580000c4200e00d054011180140c400d03030b850310000c14203002e422031300010640990140916032154907000300244002c00c072030101c2d5402410309115400c823103054a400300d402d030340000c201075101c0d0204030044d00311041980c0e80e82c00a51300410724503030188010080001c0411800314600c000d900c48420320b081c0c10000070034160554900b8082150f03181d1401804502042c88100310b4001c0300e60342d41010070b1155442d07032200d0040c010f40d40004001484c0c5007040c2c00d101d001000451040381d2840030b005c0d140ca1100c42c2250a00c0300c4140d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 996313021 1250 996311771 996311801
    0x50a15150804050a0507061e02070f050d03210209130b01020613151505030f0f0d14070b130b070201140f1f0b041d1504050c120906071101 61
    0xd5440000c03441440c5042e4002d0146080358030800300d6540389450000103502910000d201012102c2100d1660f00700201c22422a2004041a0381452005688010140314181c4540401001d540806006400f8064141811000070a4400000c0e5960002e54040151180702e40b00040c801113010300b46115200e24084107a0003044240d491242c48403040c40410300960f9248030803c80380149203464020345951100440701138440c036140006241c6804040e209903c0c089d00031043e816911070000807401c0d01100c542c5000300000c5e4130040c00c031410b03110f10440500400048810400c03039003801c141d10b0f03d4841c40f07010448070301d5a900208034220b6080001000e201c400350000700b1107004103e1055a0030540c0315100303040b800716868002842a41591203502c0007440800d0412081010700401c80401041c40220055450823030039611090070740301401da1080799110003280384104140d0503a0300c92080c140740030101d4141802540d603100c1040b609600000c1060440700d0082c8810700810100d160343c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 996314271 1250 996313021 996313049
    0x4020a03200c0f19020405070908010923060603060a020a030204120c080606091006032003070306170d0905040c0509150d0614060d11091005030405060f0f010303050f07060f050a15 79
    0x5406c100c06048060301900810006910118082d00c080c03041c0c8001c548110555011800d030070f840d080c038041d1400c5079004180c104404014150320b020990507071203020a035005a03900d69014040d00280100c0c0c00401d14604261a070078108161900407500391801b65007114084d54034001042444202100d24111040b402101000b4040c00785d0055004010100458004030014034a180e45a82044924074002500c50104004088100380310f84165a0302c1d2015240c01004c00380c0287c4140e02ca4403440d0b004036078640c000c0d222144200155404540006c04032091405044035403d600d0300400180442c4514250300025215040c124030305181c940500b059042c1420240340720002c003042078650007446070820842000e55284824209a1512921120303268241030510b11315090f030042850068070180018018051402141141140c0e80341c070b882030307480c80f08641e40c4e4014080c00c1d40c000c1100b0f0070320700184140a4242c00c07543c85822680d40c1000348645147c6100b2b004078042c407034690040146 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 996315521 1250 996314271 996314273
    0x41101032a051e16110103091401022109152212080a09020108130c03080f0403030e03160e090709180212120f071412030402011706090604020a03200c0f19 68
    0x174410795075105805050002d0406800d031283c13a40a000484114800e9500160003641e002e000401d080101c501c0e80140042841c00074007403039032440045440e038881c4800c000099450039400d0403182086100448103031200c2c60390f2500c0b902d00c481c03c20204012490350800142406a184211760340160140d4542c0007503192800c104500f0f075101c0c02c0580e00b8408006020001c15100c800805005c002c02401c80c0d40d403482c600300100074040c400e05881c480e0300413500e040600c214000ca013005462002504540d40d031180300c000b40c905a43d0b42d10141c10749042009000b0590034060400388194001d0f03e00140a0480c0c10b0069100c041b550b5015076110014415200d4a02030007000d42030f1644105803140d920300c4610741c100c2c58854009402c0450020000401045580c441104072528100d00c410b01300c02d0510000084603400014282400f8a50120705003482c00c0c03281d044140c00010404c0c0e03003545000a46803880321a80680c18040162090301000c20307c4010008440010070703c5450800f1070300c045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 996316771 1250 996315521 996315533
    0x209011e0f08151206011a040506030106050306030f010c0e0f19170c18011d070e0d06060e0f01080601060509031b040207120c02090a05041101032a051e16 68
    0x10240c502407007070700356003c90109a1540c42102d90440c807403400506031585030010b80301882c040305180c0060b02409100802c800d48078403058a0540b08141021922a9546070200c0c4c0380c038045490260300b641c01c1c181005541c54020b288080c0c2d41c00255501d548101c00d4509020b0700b500e4640c1d4669050f42215400c00001c1c580045c0b08000714a0003040e80c41d200d13810000074925011030680401d10070a0f5600400140f00001c080500003d60080214a10300d4006009000280782050b154011086101080304105c51a44610058080c83e41c010b10a410030020841140c0e20901030013005104801c0046141c074061026107000c4900100205259201d1410002c50390442001c03403504240c007400568005840403500c0d402c905442c0d0340780c00082035075004102e40002c01508000c0c1d464034003001d00012460317801407000108820300b40807503201d103130402c282c46001100c2013041c2802c488004036404944c1c00002400c0f08000045240f020101c061190241845180c00501128501840d803a0000d03034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 996318021 1250 996316771 996316787
    0xf0e070c0f080c101401120c090b0f150309060a06140f0310060b0c07060302031b160803190516090e041e0804080d0903030e0402091309060209011e0f 66
    0x200c2008a20f040112401019180610307110b10b4a0740544c03200004100303000f1002100d8010040c4d86050320002049441c2e0f40c3d05a0054024082c41035101c1c0c400030250b40312101c1d4a05056000343c05034002240103060310700140c0090b1840d41c100d000c0e040114180c4101d5004d1841074a400f004d0004e81e0a0120042010041d1142c051580500600500c42001403140c401c61008011402c40240e403130780b003c20324504005d55604003c05243c410703c01d020380d415035060b400d40022901c00e44a540c41e01c50001e508074070490050003d1426800008018180c0501642014405d6581c04103101503101d4010084840116100002c00204100820800c408480c08100d800c14094940120359000382c10041d00c0e410144081503400050020341003281c80c0080020403201ca4043c5055413600381141d41c0100070030312006915108507004610601d0381d503074080349412a0010b1800400c1034142916083d4040c0d0084144140030900b030fa0703118515040b02c800b0300402e01d0002c0c0c7d940461450b21700c00944042c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 996319271 1250 996318021 996318023
    0x30406050a0e030a030206060310050106020d050c0a060e030a230a32090109080309131508030304061a0904080909040c030b040c030507050d050a06020717040f0f0e070c0f 75
    0x100e914440c140b01610244160701d0050300a6001d03241c60310707001c0c060510f004207120046030782070702e0701004022455011a02c4041c0d040b00785081039444400d0341d242072070140040806402e2070300d000b03461940488000010a607103841070300d03020f04841c12001041d82155035000138550f80401000140c2001d171249481c03465462441e40c804141058070b010300342602a41c3d200d030500e074100c0012180111360300006214010100b80008510b40381c000008145040e585c4042e82140c039480d640040d900d88643d148040180450204603501c0789054105000544509121402c50441007040b0391480d04003000030360702c11500b141d0385a207440000000d01c84000c1c0000c00503141c1c1201c00802200040c0800f100d5401035024103a84a442402c5007821410170b00b1035480340f80b03c0c9101211100c00520080390340030105402000040e1540c1041c20400c4102c3c814010724032090700d0004000c5040c86002c004d001c01d807108458032554554981e80b1140c180d0b80150384041c04160201d002c480001d03a100c1d001c02d40340e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 996320521 1250 996319271 996319277
    0x480a06150f090f05060d110d03020f01021303020a12030503340503060405060102010e0d08090705030106120506131707060902130f0b0303040f0b0a020304030f0606180608030406050a 80
    0x2280e92450290300401c07480d04581000b0b512000e03c010300305042d004035a00702100700c40b0742d40e000161390b592010440c61130a00fa4082d030200910355061500910001c4486000c0f10025903940a0380150301188424900040b40306980482d00421000708001108880d1a41038680710314688030f881c0c205100c000d0b001201400390700c801c802d42d0000300c040420200c0211321500d4451b1a410a401000f00b5510000c01e44c0c0e04582c900780d02c48000307a500281008841c020f07401c1c0200241c80e00711a02d0b04001454202c5a0550309102000900a0b44804080e209034000c1040c1c420503150041e0b80d000c012007040c0094082e510080d040d0302c000da1400300500b0800d105200000782d06645501181c11100e54611b600569556030012011000c064000d01708079003402c070007171883e00d410a640e403142c05010780120200b1280101c1c01038171050003041203401668204100441c000814a40f401c007400b9113001e070102c03581c403007001403042e54500d00038401038a203990080d608050030a0305c03c60b02c03508805d801d5010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 996321771 1250 996320521 996320561
    0x91217010e0c340f06140c0d0c02030c0111030103030f030209091504090516080f0102040509160c0c09020a1d1008060303121e070c080405090c480a06 66
    0x42e603d480140c1841c05202c1c80703005208003080d0909004958100101600c20403401c0704001000c0302c2c038022240520391005000400002000c0101e2031402035004a885035031810f420010a00d54010155040780d100b0364032850b0000605608401b640129440c2c00c5d0003050360b84c046000300c0009043c550043c40013810004081086845076468107140d15414000301d01c2001081c4210a000e20000030000c254000030b510705031408010a106c0e0100400300d06c508031000c0c0a202100d48220810913019411000030301482e0f40300e020440096004094841c0070039010807e181d45243c01c2110140040d00c003c10704100c2c2c0420741d6040c0c84040300200f4650f454002040602c400d240b520203250b0045080c4c522040620710b485244a0f100640507000304280b1800e0700001001a2001c000c031f8080d80d03c155001601030b2100021031405004403203448200301d424070324014007022400180c04014408050040035504c500010402d0900d02c46890202c9400c4803001e00c0c0400c006412400b050f03401c4c0790240c09 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 996323021 1250 996321771 996321847
    0x10b240306041410080d1701050607050a0b0a0218090717180a05010608100b06160c0902070506040c0b090d171e030106090e01051f03091217010e0c 65
    0x20380b40001c45400410700e6100d5000d21402c070040107480d0100f1943c0c00c00079404d04680071004047d410510945102e081c0019071241080000d0209491565110769286540e05105414030060b4001d003030380d10030040d00d00100d003046182a20000307025150b107407200b005244c80614450042400108144034402d0b54030101c0814680820010001c58001e1000044e500d0404038a10b0034400f284040e5407447d4149880500c1c0303943c800c400c644040c600c44801080d220381c06d01d882401d0030780c81d600c5482501e20100300e28080c480c01250607403180e0722440500c50f6480e203507000010700d4080c1004c0150040a850288800074070f80d442960852442e400c261414141310070780d80300c81e104104001c40d0001c20084010042a41c1084540d0041e00704020345400301e60506011600c9582c1d441c90048c0c40d10101d0101503642da000e46e01a0000d50b8002c991141d42c0098490040c7c000380303209580e03250044104000042c15a00c0722042170190522400181c6064420006210310784100750510b00038440682c0751034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 996324271 1250 996323021 996323051
    0x1030507230406080f15010c0303060503190203010b0d0b16201f181205090406030c170f1905030c011401090b120d080a02072003010b24030604 63
    0x2007111040d0040d2039a6450401d0b800074415440a4100002c0c02010700038040301031603080302e06030040c00a1074560b40a0560b41001c8000d807006a200503014000d480c82d0411a0980c1e121507010035000340c0081c003c0042490034004549030031080580038281d140e000c100e1114601c0036510402996291241d03a0a14844030074000e80104140d81040b9070080f518003a401112403181801c0508001081141d103201012080082900c2580188214803100c4109440e0b80520244d41c3d20410241007081500e4903840c1008100105000741d10141c1e0300402001d124a400003003003109020b10001400e40386c1c0c1900b0602270180200c80c01254a80018009100d80b40c800344507258000040ca10040c00f6545410703604170031174a202102d40e00904400203102c640d100b00040c032010903140341c81c0c13507041a910648150300034000d009000300f003c171444c41c0d40340030a800c1903e1034011741c404030001c2064500c2c000030814941d051f6048a40f03000340003e1074809140f0590003a40e4000c1019002041c0401310340155 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 996325521 1250 996324271 996324317
    0x60e0f0711150f07030605030607020d03021312060605280b0a1103191b081207020708010908190801180c030b0607030c0c0509071704051e21070b0601030507 69
    0x100c83c0c1e02d440d001c0080c0c0a5044c000c0714000c003005c1c4d016050500302844000d450301d242196684c2072603000151001034650b842c03c030b10002d01803483c024450081910f402c1010f043e19100c0c05100d00d010150720358903056170561901c0c080e41e81c0389039680e800b450500c0300049500040b404805200e03540c0804c410500d828001441040400c5900b11503942e40144003501c004400e4008240008000002e0b0000600c030400b04c070303200540300a41c51383c0d681c3c446100300d1400040d80c000d2140c6500b000802420007401c103019081403954460840c06070f0b1501003085506210034400d0800103800c4d00420701c2881c0ca43d5000e04c4244046140100d0b081129101081d21903111150850000340c0e180684c000b444103568186010740401c85038030301d060070b04a0009140f203200d140740610300007810380440c080000401801034148c000300140c542d49001c0b801050b80b9820b843d085110520040340d41d4407031041006045a0440340e105000341419103915004500600c001040320f414401201601c2c82340c3e103030b40801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 996326771 1250 996325521 996325531
    0x405090106081009200d110a0c0506160e01050c071a0408252d0902040f0803070b07080403030b0307241106010317070b0108030904060e0f071115 64
    0x1800b02641002c3d801d5480001e40c642c41107000f180340c000e600d00d02c0e000040c03030401c0a501018a054032641003030754010046c0002c00200c601d48000282e5500200d800111034201da9000d00c040c2c81d02c80d07540e048803010381000031402600241c01058208036640c0104058107044403480d08a480d06900c1d625001d03228640b2044ca4001644042010040140200156242e00441444001c854071074004000c0b510a0300380642000800a0720780845190155100c600ca00b007050b4032058291580d070884c0c40c0084d446070003001014914071602052a2500008480c00303954407040003100750b910b07104121000f81010b0030403000c0540703c14010005940400c00000a080100c48410308d007004000c1c2e2600e0700304145068400e04c0705c0c440f0480700101c03020580c14110303a0449014807100c0b0034002440300912070150010300310700104001040c6c42c180000034040d41103098504204058888980042007602155140307405030000c00000c1d8054840c189008030300810a0446102d0012013041100715101156 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 996328021 1250 996326771 996326777
    0x20c15030c0c0318042706051509130302010605121f0b04020c070504051317030405010b09090f07050d2a0f08010b090f0c0a0c0206070b09030307031407230405090106 73
    0x2c1c0c1d00416241c5807281c50558640d680390600c6a10222441000d40c00c021b0a000e048181d5071400103102030022080e0f000d2481000b42001ca4600c1c15801c6218582075082082d80158031f0000046428148858210110a02800140300001c1580091108101c1c80c0c60158081038443e40280481d460360700180c140d4003600801f400d1800d0030310040c0401c40c3e0008140c4044015101e404002050b40b0707036581a420101c03580195521b54690034018090400d0812054200c1680d8040269400c8003003203461094500d00c0503070f80c41d42d46e984200801d08118100181000c5084101c1c0349031142e00041130320001011031800c001d0701d5a11165003540c41d116611414059448801203496894800061036218616203840080d030f0415181c11a403d00651402074103005940c0e001070255a40c9000350b0b030f5803580c0409042000d203041d0442ea912500195140340100b401d04c41701102019a50300c201d44200f00c1942d50000010764161030068464040c544828514000c2001048a0301d03642940e9000e0304042d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 996329271 1250 996328021 996328057
    0x506010215280c1202090f1c0807050a06050601171f030b19061a04050121060b04080f06160c06020c01051006091707180e0706020c010906020c15030c0c03 68
    0x2c0f0f009800b60189a40c0c03200302030300c100012075282d40e41d4017001090b040d0135a1080d00d072910311070710302602001d8868081c00d1406d0205802040020005841209521400080c00284c43d2a001500c050005611507800c9106800c0001c00c0c01c42303041c00c8c0c43c2c000c5640d07644c6141400d9076921140c0c4a40c078244c80300c00e1413101d03070015003200d141c5900800380104080b50803c1d6440c4600700807211740f801107001e00b504011450030560700c0d0340c1203550b0301d040a00e43c8450030013250f60364a60450103584030f0311900000f0302480d4440038103010003017a0a0710685041000862003c40490f04903031400c3c4d02c0004841c0c03194280031031100e14900340708840c810000303000d2880c0460b09060016044c0100c41d800008401c800e65031407802080f01040420450f00071115800000c1c3c80d0000b410003402900040e03005a08c50801c0014100e40e0028030195001002e07207906000c181c642d04100c0c0c8681200e103249070000100380460303099010a40085d94020600111281005030100185047d03510581d40700107030385496 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 996330521 1250 996329271 996329291
    0x10c0b07050d14040210051321151503021012020d0507090510090909080d02030415110717070206130b040603110405091501141c05010801050601021528 67
    0xa403054210072100c2550f0f0b07074a945050380c002100c0c0f1501c0e0300400c04001c0041107840368004241030003c007911004101081c0d000804e402444030205441068404135140e81030301e00074880c0313071003014154512002c41c9403882d030440d003c0c0007068228211000410040709880604020188003900c401c104442c0040b44c1c9003403441d0020222231254000c3c1e88940d880410711600d00da080011a0129000040040341241803820840048e025080e90440d03014000000c1004110045c0c01c0703030350a1700151101700586400041079120f1409110380061030040c5094040380c02c840c2c0300d409030415520040c078440c038150500d0b000c2120700e1403543c0000401c140100c0c0034824030b80c0502a0740920161040b10300d060500d0000000c51800c2d01410b8000e1010101c41100c01d540d200c0c15401c1d4140350200c0490b80d1b11201c0c0131100340300c00755111008a200c0e00e80b5001081072201802254060b10f8141d00501e00c540408400030300403e00a88280d0340000080340c00d0a0365442d5030700f00e01c0741455686000a1032501d0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 996331771 1250 996330521 996330547
    0x8070f05030d0f1b021c080c09210d0f0903080d090204090c1d16121b02070501110705010834111501050a12050c120a170a0914010c0b0705 61
    0x2c038403444c15500301e034080201d856454100c0302001c1c80d061414011a4440b008910340c03510503417040c240c008a00070109059200028006e0241100350021100c200103552400c44e01e0900c1141e1260000e58481010004078401030090b01c094040240002109101e83e8005070031145404000c40310802e040008000c00142c005202e0312509100c41080024a044120007a03d00c015076070940502800c0142504182c03600d6000a0440342410742000d0110680c100286d900c0c00c0612900d03000400d8200311090b1000c001c41c40c54200d03801078661404903150012034040030200e01000503800708501c1d600304c0561010280c00f407100340d660384601c010304207174142c0d86d41412842300100000c08040001084181ca82c6c2e8200030844554410312524482e1520700581031164800f070442e4400303a03501114990000216484020710310561821180e81c040941c0e51002d4010030b8a41800303c0c140403000c108030014118000043c0405140c8504030000503911a0300c0340c44e0645800d00050004602c184034501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 996333021 1250 996331771 996331811
    0x30c010b01090f031104110d06062003040315090f0c060509010e0d110f040b03012a0801080a02040903030b060a2001141f080f0307050601050d08070f05030d0f 70
    0x410b080c9003040c3d950940e01d4040f0021060940e01d40120780e546a204904412607041d511020340200c000d00446964801c0140f0190384644444d030030214200011710403e03c0002100d044035440608502c0b11504100968002d1059007801e40715440b001c0c59020000751028030100c003a0041d912030a0b290221600010b05070106203803003a010ba448940c00e82d001c0b40c10f001038844150002c4410308034030300c0d40c400490080d202080030a2780543c02d144100185000341d000f03074420120f0904002000a800c0c444c111800142072081c009281c0142c0c004c40d002d41069003005810500904012941003460000309011381e01455240300082c03040082e041c10802c89002c42da04210880c0020700a0344400454001e40071780141c0380e17440c4412018582e800306114481d1400c010712501d420b0303440030f40305040440c4e241d600401040f40d080c010300d00081094980804140403103034000d01c8050600c4140c0e95500c0104890820540391480184210001d81c40a070003109100345103000d0124041a18058040070a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 996334271 1250 996333021 996333029
    0x1a010905060d0b04060b19060503010e070302070b0f06030a0b07030e01110a0f260103050d020708070e1305070b0c011a040b180709051509091609170c03030c010b0109 73
    0x885010301c2c2d5008101848011078010780c00c20f00c00141084214001040c101d51082c40c003c420b0007003003000a4880c0c215026504884001c203560030103a4403103408a080b84a100300081200303841c00040303001c0c840c103000200d6029002804549141d0480c6c0c407003d020702400c07514240029101c110840b0440da0030f016201ca212846030071a4181842c240c0042d2050001c18001c8081140b020045800c00c076000515443e00582410610040d58490904588506120180c0c3c4d0241c030514100089003075001400000312010104440c901e5200c2404401c2d070210020707010b441512030001d000c26500303000e0300200030000d9000c0c000074040190190700c0c04502c02c0c1d0311442e4425481c103034070702c01c894540044c0c040c00641a0f03803c00c1165a5440e8068170005010f400554205080c5441a401d41d16004018130720940210340c59802035903004581c0640a200102010005040103420000301d1a10f0700d541415108200903103c54155602c042031454116503605580303a034403000101c1542d41c114003070074050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 996335521 1250 996334271 996334279
    0x15020304200405150d0606030605130b090601150806040212091e010e0307030509060f030109050109061502100506030f0f0102130608010815040303090206030f1506072307031a01090506 81
    0x1502d0144400b0084d190303803440b0540220752003290b84d020405103900c0326015552203a000c2065007003030440080e6004c40c965040364401c1a06022604001c400070340c81d4101c1c1c41c020155100d014001c071080304c449401520440e0400e400384808840004150305143c42174500708001c0031010031302d145895400241d601101840d0b4034190700e1885025010040300c40d000d805d07091242e40d03101d0f820081b40e1144100d2558240d401000701c0003103603ca40341e400c418101d0300840ca00b031020340c0e16002074801c0303072040c2c01710313070f40940c0c081c400c2d043c0b50200d00d81046502c414014244d0f00082d08600850342008108043c41416941c0010503080d044070b808640409000103150502c020340c108121a9514007000844800000720ba00c0000c0400d44650095030b0382c2079024000d1622030500c1c00d02001c030220161003100220480312041407050400340159014944c01012650b031204102c03054050a841c07250708100e55000d61040070012520024564210300d41c040e18034500c0390300d03107021a001c07030740041d00341485 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 996336771 1250 996335521 996335531
    0x801050708191a091b03090102190908060406050c09040e0f190203030a080901020d0204060f0f05180909250303090503030f030103030f0909060b0703031521150203042004 75
    0x3003400c0320411000c1c01c3d106807180420b9446008442c443c10302c2e400d4032004d80c41000410021180c506401404012555401583e000081c01c2801c0e94001090b004c0d91a030b5a100100040101c0c0168000d150010070500a4511700300e83c1030042400c0c0e540d6046102c090360310803200f003000304030b0410a500c1c4d183d002c4003008240c0c01c0d0981c006500c034030410140904002c9120086112444290704451402d415244111b585a41c2c0e6500601100780004028001c52090700030221124024803c640381e0f5003040240092038140c140800101100140200026104400c4c0b81081e0140a85009000c4044450912480792442c60010a04102908014000d4000344034040c050745020381901d06403070b4141496010081c0d4130800b141c010300f142e0302c490442d905000c030000320700580c20f00070800d071400781d42c2c10711442c001041541120a110303c00c3c200010b4403841d5140c0f003c840910340884482c0715401c60881500301c5002c0341b00740c0e00140d40c2921001c4450030420020a40380c171480002030411784003840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 996338021 1250 996336771 996336791
    0x1f090c090806060f091801060f150314070f0e040c23190c062309010605030a052503080d051e090601060305090a02060d0501050312040f05010f0306080105070819 71
    0x20b040d1003400404c0d07001d48203003c0400c8803150443d000b4a0b94001180c02048496502c124165000d1528402c0b0381505964014603502c9a200b070184502c00101380c52488400c3c0c8841070708941072851400c0100400c40000300a1348196a24080c45000307200680d5105c1910a2042c400c640d80b5803145a0060140c0042103021050200d00c0301c580d020110508180000d002d142c03c0c88005824419050303411441207003880c0400b0b100c121107580c0562112002004010380760410b1540d220700e20400500f440d403014200503600c0114101040d500c0800500c110007940e620b50b50b2a00507003100f5882c02d07110340c8400c100030045c0b0020a045030329101d4102c0e400d9040c100005030686030001800784408050b141c02c00549401820041c10306072682c09006030343c2d0342c1401212000100420b000742882401002d00300000050408140c6041e240300d0444041280d251400541d41c0c47c029903404d000341610b41c1c100044400003841024421101038035600001d240c2901d1580e0840b904010b9100d4003031a00c0c600714 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 996339271 1250 996338021 996338029
    0x2330030a0905070f1206050c07020d0f0605070e0f0d0816060c0e01050f03240d0302061005030d02030d0f2c011409120d0e010204030f050d23031f090c09080606 70
    0x1740c500340c10010000700e0f41c40d101c100c28442d100d0360a0107074014032100311203800c204002c110254414000c800c01c101507114140704a03600084164050383c481000610702c1400d16051128003410361081041502e0042c918404040c2c40c4da80c020203940956a4030411a60b1580000bd03c414a103824a010351034a440c2100103100344c0030290151001001444e240762100340540c0340302489910090031040060b00c2450029a540000c5800c469030341c40c140000551402e0004111356080d4194001d90f0406a01e031000c41d009000518269007541d0b2903103a0101c18548804103504216401640003440c650351400c2c9509464410360714400c11014070042003604440420f480c003e10424240036580c8030503521000c0c0103822004040319a03944005030010801070007008202005202e10103480705107012050690303601224044080c1c642d43d90018004110baa640000c503071142c0c206a0360511046083d5900c01031079641e4204030210dc0e55507010542213508500f58600401030880142060300d060b0001c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 996340521 1250 996339271 996339299
    0xe1608071d030f0709020c07080a121d180f060108040804090903140c030705100504150c120c0e0307141813060504050304032330030a0905070f 63
    0x140700750408a0701040502c0d5028032540d02090070b954101c4030b510792a003051500950100c9034242c4903215035640041d9818010400898250f0407016103481150000d40a90b507114100494010240705000160401c0d642c2640b98500395404290b42d010f20f00e0314030f490f280c06100c080e00460521030307010100400240803004507811344144420110f0054054034091300d9450381120305000340d14000c1907020b403845000002d410302034081c1c03044488000403010600c08403541510041c10359520385890717016440a58000e0500c1e1013113898161140c2c0724401d04541129112003007980000c5890003090b0042c40d0800a9002420020110641d400c51381800512803a00f04818481c4da0342010000074804895490381441c0c4542104041c0f000d0701d4146032440d16544079020032a0b10180d0620300c000c10340040c1482c021245c0799840245a11058900954441030007a004800c0c04009800d03070303c2000781c0360ba025600442c40c4071400719401c82c013850b1590502402d500a0301c845404c000c010013000c41e100c0c141e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 996341771 1250 996340521 996340547
    0x6030a150e030c0303092128110307051509240c0408070305030306030d0903050303060f031e01090c080a0302060a0e0102070c080a030e1504060813020a0e160807 71
    0x60003807450304520382503025044414019000100400030032000c04030307451502441c510700000d07405e48030032008041070049a030080c4080000074000500c02100016050324401f26050100f484040ea0202c1441e50b8001e502c101da098200002c500c0c018100b801042e0341001c49400500001c1c0c0351606c2c0865400860585602c8601c00100404c202003c3c032411280689007000a50f4582030b181e05080c0cfe07880e401501c00500030300c03603012114851485031051009903603000000c1c1d860b58817000200b024081c0344800d9290716000c1d5418081e401c10483c940e81c00495184c0f4004a009000b5007051010581c2551181100780c1104044900080d03001c0b41e840c0c1d01a4210900143c1e00700c1c0700080c68020701595800a00d4210540408242c41e000022010f000c04d00c80e66403420210001d8041c4141c000381081030071200b00c82030105004260080c2c0826034001034900301b05c0341101564001501140090b031245070ac0d1121002481107190301c005501603110b40701c0c10b160405040100004003c0c5e491180 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 996343021 1250 996341771 996341813
    0x1e12070b0d0207060b03030a1805060a0903030c030909020c0a060e1513241a01170106050f1621111504030302211609080a020108190911010806030a 65
    0x3400100b040b80985c003600345940c000d41103d44a140421024150f02101c0081c1001300d58003e90001e0710303203000411521003945076030300d55510b00d103165015030b0402604d1404409201484038003189580300391003d8180e010800006020064850800c0c2d0100c07003058580c000640c0006050080c04410300c3e00440d000802e0341b4003581445e42d5410402220007c402488801004926144209654903000f46600b208101c141e03410040c14400151142020301c41040c0b2a01c0e189001008400e004038090501000d0300b00c1c03420310700f144030500c0c030260a030007e004642c85004041d5007206006002c0100907011003a051400244401086180d039a84000070138098103005800028109403103034040d01d0050303140121454102083c5c184590b0000400c8680a076100e5501c0400c06a4511403fa160101d880c400040c3c0f00d001c005400440300320350000c0c1400740e07042c0304000c043d603041c009128441241d8010b4030030100900341c2000041164001401152080d8000749030b10f40803692441001c01c8290f800c403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 996344271 1250 996343021 996343027
    0x306090417130e010501210c2d03050f010305030403020904150c021b180f100302090109024906120309090608010e0307031206051e12070b0d02 63
    0x200e4401140c91030726900035105140400c5a4000d209600c645a0980d030183c2041031043c3e80340c0c40111900610f0100310031001c1507c00d800841c91029030b00034402c0c501d451411240240740c0c042c050f4840c01501003071504010b91030100c948502d90521405400442c0c40301004119451034855641d00d0060b800080e100e01c5203000400c0c1007010000403501d07440242d000c10320411100c0301c40a5110011a41c40c282c2c4000c002d80c0c1c0101074a001d4045440030044400e00001c90303290251100748402004140c041152041d00000c800f50b55100d100034002c0c050040301680d04e045800d4645030415440d048200d06480360200c0c00c4a83c06502c01c00c40c6100c0000a080c1c07403c0281e130316040f01a2078954040202440c541d9440c00034141d002640006481d0044400d0007441d0303448000340c4c01caa10540201c0600c4d0410b11081000921a00d11400440c1c94100d010a0160321140042c03d406117000b0420300b1004540001d01a40c2007110050705a03422803170140c10355601c0c1400044140c41102e265070015a400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 996345521 1250 996344271 996344273
    0x1207060b0901030f2a0b07030801060f120b0609040516140702010c03050702040f150303020c03070609060f2f010c02070302060d0b0a0e07080702070f0f06032f1804050c03060904 78
    0xd5001c2242141e040c070317a0308460958400c1902011782c01400142d00141c000340c0080340c0c050113000c8924011055a03680640d6442031545000101900140243e0000080106080d50340e140d0203941d026100c0c9404102c030380c0d001c0300300240c9a02c51109203034412000c14045040540e801500c40302001d50542000c0c2e990b40120301c00540104081e540e103502480c03410141e012183e02c14000001584e201e5022034012804030810140c0c1e170700c980c3c428140000c4044009020841c40303401c130454443c809041c074070424031280c21200042c06d06085034070a2079001155503c036207a000d0262001001150026010321030962300413403d036201e05595400d405440e5a490b13078490b1201039030b410007000030b0303e08542030303082c800c10050011405882c0f403c01403140d5032002c502c60385c80b140c10a007124070018141c41c03a546440426400b521801d81e41014000c0340c030310b4205104151a088442e007082408890303503241c1c4120f4859a01c155026600ca00070b03842c00c400c00888100c4070045a402c59000c5420440950725 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 996346771 1250 996345521 996345563
    0x8010e0106050a050a050c070f060e0f10050703020a0519150203040b0f1009090506070801270b1f0f1e1409030106030206070b0a05011a0a0305181207060b0901030f 72
    0x1484416844503c1232410010300707034a9042c0c401c0103488082d59088405900f007001c00006d450f2144600da40002d00320002c2d03400ca80182c0c010100395104c2c2c01910400e0f507140d192a403c0440380d1264150038140b907034608082100314038100c05407210f034040071804c43c24183c075814017454000300b0842140c7c20340c0700882d0840f030380c011144000b031020700c00504c0b00200710315100b03440d10010750340344011801d402c001007903255040402c0c400b07141100b03004000d440200d003400e00203041e13000c680300d800c12070781c0c500c2c02c4403000c15050240c440600c9440e030000380c01504800821594004000084500058a00e05c00283d0b001c59440e14a50243d11160380b2401d10b800028010481903000035403202000034a6070810038060072035403007000025020802603036201507072901c0318003c0d125840c15030010080e25030760502950021350822035040c1e10b0720414091a89283c540b550070280c90310000804075440d1b003009070341d0040600c81f00e000da070314000079451503a54001d14201d00c50001c200e811800842003524413 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 996348021 1250 996346771 996346777
    0x30712020319051b070308030c0306010c0c06020c191406070c1e06140f09190510021029100e030a150e0105010e06040f020d05090d08010e0106050a050a05 68
    0x541c81c414015100c00000e803c9038450444900645510000418103502c0456024100d07608000550b1555032202c16140e581d90000f08201d050111001044001c40d8a030507a2402503e0765400a2102407440c4080204010000e8200142c40e0b07102d000510080240505007104000700b569026250500e0345080342e10a45c482e08842e03a100f0b540d100010440c8015400301c821948a602d0f00c0200c1c0e61039541d11001481401c69110b00c8110400400c10241445100e59060081210780c1680752612100002c240c0c5021440c9600181e0003503c402c2c4040c03059100d03080b804d0140340099041400071680c4800c101d9468030702188a80040d01d094138495014555102625400505403103003d480c0e0700d09845181154104c0d0036541c0c0c540302d17048900c6001445450b044ea081e0300d0405280d540d54608000c0501061408290703070702e40130b1201140d00c480f240a070b40c2c02a18044083c0502c482c00450003130070548141c0c410001c642c600801009103075041801c03220140c801d4642140d131080c08103002c0e141e500c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 996349271 1250 996348021 996348037
    0x17240f04020c0303041b30060e07030606061407050c150d050403120e031204060c0207030615031209060f1b0f030f0305060409030e091b0304050106050916020307120203 74
    0x200002040008000594107800c41340f00103d0000c140c0c442d240d50100f880800700c011340c1f045842014500c2e54005d8140445e01101d035201d03410101c0c13001d8030004002c4c1402c610b5401210a1034503042c081c003060340c004100c41c3c11019000f4600d81002216100c190340c8008001c40c0da0b010746440e030b4404051150400031107012800111091180c0e060602c1e00410904c103907502811214605102c1c6001100c0100031251540603981c0403481ea40c4503904e450000742448c18a803029031040c12320001c001507141c01801c500761a80f803c121000c9103036051407280c003a4064540300401140320824400355800c400301c1607080400e840d12151540e4448100c10010a040c0c1000c1e00365020691408101a80094200e81908a9541c10302450312560180001d654220310002c02180840140c8040780c00c2000d29103500c41e0052400e0740020614000c00a2141e1060720180c03426511010203010321306007001c1842e002601e50b5401c4881010021009407603000d11800200f200f0764180c41d01c141c482c42002503403450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 996350521 1250 996349271 996349273
    0x30c0b0c071703010806160201023109050403050304152a200a021306050d030903050106050a0b040b03061206100305211c020c0d17240f04020c 63
    0x40c1400c455985180d00206002c680607242e00321480c66811000d02030302e04841c140720060a040c0c548425021400301007136110000c640d0700344062642081c6e1020118420350982c01804624289001a100b0314039582d0000f80c06181000f060000087c0e0203012207a20580090029209a401104482c0904044640d03207264402217059034401c005e441144c055080c80a48640120f111607902851500c1d04a40320307807540e40c00c400c2404003d410105c0b200501d42450180001d1210b4071240000d200013444442070f0300184980005004111091168002801d411640340400c10325008898100b8800ca00038480c1e010f4000c00800c0700fa0301d4214480350303002418019a102d500d82250880700c030318900d1106441c98402c0d072040c8148400200c00b00c1d40381245140040b032030700c500200302c1d008004500a800135956420400c0d0319444a050003a120460344558034032400b880d0200c03400e00000f002a019114008180303e460403440710b0300203800161841514060281e2041d00300060007801154000000c0f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 996351771 1250 996350521 996350543
    0x9061c0203070f0e0f0108070311130f0e0702070b0f0a030b041409070608041205030603120409050a0c0807020c0f01030618021902060f040f02121005091b01080604020304030c 77
    0x100d5000104011000c00c25500c0c50640c44c0c1c2e0000300500e000316528990b011620080c0800c8086210b0340000003545201c0943c00d1070214084044107985000d030748166030b4000c1043e010301c45c00f8030003107020340c0010303442c0300501e207090401445041078410b0303120004c01c000c03000401d1040140240c10205240c00010020452080c18402040b09404122210121400f4016002c915903008003441400340360001e2103c0d80c00c0d03502d018180c0380c950000d4220383c0e16103e1048800e01c10101c0200500c0905004d032004949401c190175420141c40540c681c450500000004100c840c550008844200440845451491a030004c0042e8014800380d00030a205181c00d12301074100012540080c003c40b18000c00300304810180c02000c90b00d9420988250031074400c40000302e400710700350904502d421030008110090b28070310b20960b41d1802c522054081030081e122070400107009000e100c1e030880e80d906143c00c00d001e584402c1c00204003003001008948981da0104c00304080c1071140103000303d41c2303a0120030914 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 996353021 1250 996351771 996351781
    0x30a090b0a060303020d03090302060a0203130b0103030e010f0c0f032d0e1005032208090d0311070e010506040303080c0c070e0a11130504230114031005090309061c0203 74
    0x8050301d80c0740011341c054802c011101607540d110f4450b0001454050f4040c091944903a50090044d510103401601ea810301c00da00800480c0740011082c0c0214402e031100f010325004c800001d0036005d50301c6148828041c5d07030480c00010881c1074604452555162811808007030248408102000a000b041c802c15400d04101040e216007101b0248040c0c0310031200c080041000d15802c5550744000c50b10b1001c820807405c042900303d811400310289051160100b18180304592011400c02c644580701940041e40c038403c0380042607802c6c0300700c84c0a132034501002c17010b560400340495801d01c901d2100030100b282120010f44a111884291610070602d00180c1714202d070365480007200600261000544280303014024028550307040300b1101c001c1410213400180c5840c1c80308001c0100440c00001c2040c407402a4001c0e10301e860b034282c2d94042c0070703001d00d5514080c6081060500d0104031020801c0b0b000d00c0d120030b0005950300002036402d4400103e44640e5507480b10400b400003200001e00e83c040003800881804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 996354271 1250 996353021 996353041
    0x315040e060c0912120f07080706020a08010e0708010e150301062d080f070306110714010509190c0314070902180405090a0f03140702060d0902011106010812030a090b 73
    0x6900c43c00300c0b0039000d01a00c2142c45900ca503284c0510b2900303890200111000b803c164405415900d00a000d0b440c24540141c6860051341c1c003046610f40001c0f524001442a46043c000075a0014490703d08803403550304211024500c0c2c03c0180c5501d00a0200e00d18910255409400c0301002e4002c2404041010b6039600c41800d5100303c181030203000f44061400414500c40c00103003038075078895404c020405245907440300d100910241c401d0700c280344000c00044000c100314115070f01012031000e00006039403030004002030402150300d902d5120001c44180e51030100300020300c88015607400c00d565001d4241400c51207840c2800c0c42d030000c07503071a001084c6248406140402c1c607200882c10b5a06210a5032803013801030701c40701d04900080400d94103c2c0c210000c00e220340c1c0c46070b01c8480c0c600071140c03402207280c0000e801904520380074012103880d65002411562300400c0000180e00c039200410655041c50f4145442d051003009410140384080b0020306101250340292a0580e00002c21401a0410407012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 996355521 1250 996354271 996354277
    0x3080c03060a331404030b040809221b050706050705041d1e0105011d010e0a081b090906011215020703110f030301061409032b080c0702060315040e060c 67
    0x4081c2001d43e03180d1112034a01a8030900200160031610034078043c155a10f499036104050300580c1e07903a805101ca19400d403500100256800c270601004150707420717880300410554420628400500803101c480d0420190000150746400368002d030081950b0741d88842c111003034000e90340300c643c0a03c80b103c00154075003c40328040d4040d450a055101e80e00e14019400301c2e94038028072030b5a0014100c5904007413000c024840240541405140402c400000329000a0b910401500030388401d070850b482040000b0191200010030003001d450280b200c0ca000c120300340e1690414400d0000b080464002d070410464060054101040c0743c010454232400303a414024028107550400d0343c4580310385d0103401690310740001aa0304039143d071342d244002040c10b1040d141540d00701c041c0007501445080f052004059501840807207030b17a2540011f4060350481c5034002d0000102500c0c0090080e410030801e00542c4030340f021250320080e011046403401443d4808200240400c0d041805240120300034003000d80403910007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 996356771 1250 996355521 996355589
    0xf04050d05191b06080708070c0c080d030e0609060903040501181a09030d030911100e090a02190507030206070813020d050f010b0f0d0209040215040905180a03080c03060a 75
    0x81d00010f980ca442042d18908815182030010411740000500a42e00c0b0b190b203070030100d21807175240f10711341d948002840c41c0ca034070200400b011985032002ca501c10f50003042100e41c01a2540c000300140c2c03c010421545074821401400e04000103040041d412485240c0440cbc020a00364100d0640c0c0346800d0b01c5804950840840070780b02c0d0160030b44d0261014820301031807050a4018036040c2040c100030042110074061011008280178402000c0711440c2e80c0c40401902ca02e001d0100581d88070703003800c626000f01c07610b00704000512806002c00c0d0b000c2980000e19a502c201703035091222094440186002c40103844a4000794000580242c0c84e00304440400c211641840c6c90009000400c00101000855448910100e4020000f400c2e11805890805183e0740c1190000c0c0ca03026007200c0340c640da8901c1707912a81120b244c0320340300c0d0140941c005500d18500c802711385002c060102000990360040541201920045984801002149550740ea00d0350240081c507503000150b101c5d809111144c000c03241c400d80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 996358021 1250 996356771 996356813
    0x2e0e010510091a0909010504140f060a05040207080a03060e07082701021909050a1404021b060103060c0f0815010f031e050109050a05070210050726040209010b0f04050d0519 76
    0x17000040604160240c40620342e10303000c3e221556913881c0080660810001c0c842d960100c240e00c00000e6544661004184003030145150613031b918040036001e0207803040340d802440c8800c010303010003054940c00103203a0f80241c40303010f0320a030910000708644180e00d10070356403000c95440041d42501c4000d000310b1300f00680d4016122610345a584104000c0c011107a4031443c040c9040f4480484c03601d1626900400c031402d03140074172270303009118a82136614000090300304030388855860749585007060300b0441004044803603181c4049903141602403120307210f4001c500c1d54107000000b1808400d190007030b0410f0a0314094a10440125254803194001800e000e2281c0c60041d442c210100300b0f009541d001d00d91085000e03400401070345403c6590781e0010140144400100b01158941c0c958040c98220003560f00c0021301030713110090802d401002841d4006030b101c0100343c80c04101318212190210309640444404030b81c019808401420b0607802c000c04100c05045c500c25911043d800c00800041c180c0c01a10a00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 996359271 1250 996358021 996358039
    0xc05010203040b0f0309160e04050c0f060d091109271504081303050a0f2306180a0615030507090b01090b09182e0e010510091a09 57
    0x10016601c0307102d10301074003072802ca040048002031006240110340041030207003119440c0c0c06401310071409900c0c5820129040d00050103003c00c1c042c040011012200c0c04599105250380d41c1c1001900b5807041007042020310ba22160000c092090303050300c1e1a240d43c00600010250301c5c203c0000200786207801c41c0005215515243c1c00200100040c0c00003040c3c900000800e00340d01c43c1e8a8180325600b0020154600d00c8602102000041d8207000180071144100101d03e048881803034107510500c10089058100044401c443e04626000038807075400100c810150705078601f030718241c1410070007203600c00790140342041100003d00075000700e20421a070240f0160754809482d41500760542e07220240da50300107400b845c0c0603c402c1d800300004100b101c030001d29000390862102507940d40007401310350380e0151490480c80d40e26104054140c100c8407581c1f85480c418407600300a5a04058a018041c0c14050545080240c40c0c06005100c0d40300500011000c2c150032502c40d03402c0c0e1130241e10901c09103020708041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 996360521 1250 996359271 996359279
    0x12080912010b0a0b1c2c0c01081f031202030f04120b06030d0915031b030c030b120a151d0601031208060d020f060f0406050d1404031b060b0a120c 64
    0x1c2c2c01901c6110141300842c0e540f400c00418090003400d42d19000030000c01b80f00d05022a540c840665040681400c01d0152055030041c030005005403c00605550049502d40200e20b0707012401440002a01d6102c1c80804400b250701204a00d18041c041224200d62000030380415500b2290140030501c500c10040300680741e4a200c28540c8a08002403c000428082e240a100c850b865841c404d0030400c451400003505055641c05140d0040d0404990f00880d6840291200d5241e0600500040010640e0032280315003449801c035555902d07090000c5d2900e4104030044400700300702d420100102d94040150703042d0406010445c2d0f11070f80300384000c1b2001118248044203990040107803c4c071401f00113120001e24004c81d001c1c040c1c8420002c004561001080000502030754228010b00003820080d41d80c0c03070700d031a60100384404881c4480885d00040070700004010010780c0c09180303290076211400e8200301044440c580500a03004050000e64400074001010480da501980f014028502440d560307139880d036030707 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 996361771 1250 996360521 996360539
    0xa0f0801060b3c122707090f0e0307030504060e3a0b01060908070807120323040e04110103060510031508060a090b07030b01080112080912010b0a 64
    0x10303c1507201883c0301e00c01203090758801c030108004000000c90942c400d84040f01c2a000d8825400585004007410002c024800074003550910108030300000441c0780f0766a08040000c1d50703544094803d0178141030b140c544003001050141c000f240780640d0380044039143c0c2d01c1803902420680003070013071100041c6503480700c0d046843d060003140c52082003040c9034400700119465011038150484c0100d20780505021800e80080d00083c0b840d802001e03903649604866081c402074030f0030080c2c9548074a0f82030780a2301c4c0c1406440802035071140700940c0350920740c2c0b000310607061144160030316002c03410041c070010070001900302e000211148201e10500d5104000003c0b4001507003126280d0181030f8109a03105042c14800b40070b64801810455103004c0d070480c440d600c042c401d00d001d808403400400c030b43d1100441d001300021900d4454000e0b0090400f80000701c6a00c0000701481c20500c01c0c0002405c15114890501034070303100b1910544d41c06018450011048660980a020607424682c042d0040c8039001032440d007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 996363021 1250 996361771 996361777
    0x10c0206100f05012a03020615030609030f070219090501171c0e0d06051f0f142202161e0201020a0206030a0b030a030306090f18021e0a0f0801060b 65
    0x240c2c0082e082005040100448806048002850600b9000c0080070f054910703c20071482c0301d5100ea40101a2840d1036041d9441400191400c2c0707010f944101c0034485407060200558043c2510341d2f0f2165100e0200d40006481d40c00c0d00c2e03450500d0304a029801040040c61504018140c0700281032500b010107014040c0c960750780c0000840c0760580c1001c40d40303004192091807a0368400700c00618007da254601e88400044501c2030f01d00c24040e6030408280c484a14007102000010320100c1d00c20a2124600150500011a09a0818800c0308049052900c0c80081141d50704280c2c074500e011074551610342c52003095110300704003c1e81d00c012000c8800300d60030301c01c0b00303c00491581a4041c120511141d030070301820f0b400290000100079203a100c1300d038260710104071440c0e03628005e60f008039803580b5000400089a141446148699060004015103c48051030202c0d4441d07050b100c040340c0045200000a40c0040b9280082e032001d8280c80010300192020f03000c005903842c403c001c201e003590b07076204104544 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 996364271 1250 996363021 996363029
    0xf030a020a08011a030a2d0506102d0512010602100f06080a11040b091f060311030c180604170708010903090302060d0f09080301150207060918090602040305010c020610 74
    0x1010400018155000c207801030441440d210180081c42d1700101c1c07229006211f443c4e50130441998440401010313103000440d508245000341014030b00d0001c501000301c01c40780f10403400300c0f4203290071122840140c421002c49000c0024808414100d50711040029118902104110002400c0c480c075000d00814610606c811121450010682e151043c1c1e213205a003e840d034119903101d60781d0403c000d51900c44d0154070b44074184000c03800c4080c0c20b1120854103d4a4950000c5040518100c0c030b032141c0d8a40c440c00c4070741000145007203d480e12041c1c50a003105544040c4001d8000401060014046030500c001d000f600c8144070558100903151300c1c04a08035116101c2c040d0010340800d8003000542030400007403d141c10320300302c08944404003e506006444845001b1210b020740000108030481c00e4030304030406507a00d48050400689007082c01080c15402d400343d500c000c500c2441d1000450103ea201d0707000944e000c0d8080d5140d90b80c030305200f8020120b406035000580181070016070000f03180c030310260540d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 996365521 1250 996364271 996364319
    0x12050a0f0b0108251404110a0503071409030d0815031c0906050c122d04170a0312020c01060807030b0906060a4a04020f0613090b060f030a020a0801 65
    0x30f01d280645c050140d0410a001940043d90360b1040000c812091006080000c016122141d9a00345101e0007000484c110440941c070840500c040d1280349e902182c8095814050b00e422412911001d140003105000d03440140e074907120394079440c031700350f169003103000e1104190341c681800b00b641c0c441041c0d0b101c1c0300d80129060990059a0449862440d00740602401010501e0080c04031112143e04091703400c2014104514074401b0404112903c1070780344d106940ca2101c00500394209150754040c11212080f4104141c2907000b06501a01d80b509510402c000c04c02d50049449150b503a050100c02e001054034103030700600400d0001041414502101e03421103c1140d842100301c00c20180b41c480108000310300c981c40e18240d010344231004925442e092111a181000000ca600b4240304000d0b00c1c0c3d524000c1140100300030b00c6030740030021890441c02c00701c500c145000309451600e00b0000d40c49225024525898a402000b48900c04443e03a000c1d125018080e2194480c07079032107180320304d404c1c1140c0c04a20a070b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 996366771 1250 996365521 996365593
    0x90102070b0307051c02030402150a050d1a040c0e0f090c03040308040c09050c12060415030209060607080c060a05010501020c09150d0c0b09010e0d02030712050a0f0b0108 75
    0x15050320070003503501c09140c0c5844c43c1040c10b100d040000c50100b0110703c00309140c003c000e0006503e06070100e0749050290390009481c1801e203200c05020f07030003101401c40b42d09030b49107180741072483c0090541e040031200802c10000301007410005080d0b50305044009006005100a100107420400ca9050003800741020b941d0941e41c96980c101c50079a07004001306c03a0361054280010310b5607034a000301401038035034818098448440300c0300c2c201050001000b41d8841d5007081803054909521002a00a403501a6540b007031a5542c103010809520660400800c684000120088480b4000c503455008280c8448240000d0341d880c00126511400204800d0784605484003240204001044050003140080c09200000c1041e45400d1010002c5034050102c2250000302e40b2107540c0d00101d4182c0005007200c14100e00d54154000c20b907510f8060090084002c0d001810f8010700c0410030041c6409907004e52280c103101f030140341c4000c3e0b00e8428410480d880c821403042000c10340d0000d0451812110650003811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 996368021 1250 996366771 996366779
    0x310030813030b010f060201050f19110f0315030d0819020c1c1101060501050f070803100b13030b07020303151c020d0c060f090f050112020c0102031e0c09010207 71
    0x1a0720844a5407050000031800100007002960310318020104020740003103551400c140070342502c00c01450201918148410000210301e000c1d0030300702e00d084445001450346a10340340b45400c0c2c412000080791703110000c420441c10010f031443d4100c102c3c2098098402c6800061815100c12030190f5421030001d4003113421110b4420254050002c02a4030000c039401c0c5240010860303098102c016100300010501c203900d90300b001d1b0034017810b001400d0a00c4d189103000b404010a00040c012480004d129400010100d6500004060050080c01d0310080241d650310b2103030390440b0b1200a46c8000ca42d003030802e4000031025030020054901c1004400d01c8120301c80040e03010066200740805008000b02500890000580c455100c0b02000f24032500c0480302403810700c48003414440c0e00109080410072038003c180000e220500028080301c0081c02c294000b80340c1c80207030002a004074143c955480d880403042050707000b0038a08000c40000207600403e82511072048604c01840340c00600340c0545e0003048204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 996369271 1250 996368021 996368033
    0x804050f060d0c0201151205060123060c070e0c071e03121e0506060310030803250f0e010509031e030702040203040302070e070518090601180b071502031003 69
    0x90304280103051920744200c50b4190402c0f21050140d40f00140e64403800c0206400d8000d1611002d0107108040c00034408031035507007a950310014000c00025951b54848065000d090b441c0d403c0c030135100106181d4540c400301030026503c4006100d5a0460407106000c944c0c480020b00413a850190820359030480241c030301404030042d03281c0310011002c01c01600e001c01c5c0c0313200040c41407070100007020b01e03645224000d001140050340e402501052144070f08000b07016030300140c03481cac100c04c5a90205819031207a4424410003030010102d8840a0700c01660f410702e9844550140c0c1c3c0110342c0d0131585500c0045142c40004580c0303801803024250300740c1d0110401d0454411480e00c3c0702030051020040740e01d80903880c0d0100381660402d540403070140c1c0c4191014015810004200c42e40501d45180c00c604080c40c1500700301040a20320003890142242c04045482d5900c9140300000d00d001403a034131400303140d45a0710741c2c240d80d0224030f00b0f8a000910700004203126096000300c9008903e0122590413150441e1200c2c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 996370521 1250 996369271 996369289
    0x5030915070504030204021b010c0903051605010e010807020f190b0901050c0f0706060b13061205090a030c081603090816030209040822080606040e01090c0b130b180319080405 77
    0x1c1001223813142c0850140708024003031030011034041c0e40c48800a5140d440d01a107000428403940e03150140300101401143d9002c2c4040640f200240b1713029a00d42c41d601c0080c1d0400c1000030030720b025409808a90300d10040c114000c3c5100341d00c9031000c043d032136407134034201c2d03080f51f80070307248811036403001c0141c0d900e171081800103081c10901a910001d29a0750340e440544017580001000d83c2c18180740c0004203c0c10b5000a1040d02484401005002900e011103a01e0b444481c641001024401d000105c1c40a00c00e4020a80d10303c005d01d8030208200031640d00700038244550901c140f40c0c03a403081f079084414000a22b50b441040365409003012031140c565a40740502c40d000340103100c061841c1208460504024260004000d1a1500107485035052610600c01030340c00c0c1926401a40e0b050071030b42000544c450350442d085501a05105032242d20a2002c85d00da000107900c01d640c102c102140311140c2490801c416407521804404032290220740407843e80002c81045070241042c841404100301c1b90130480a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 996371771 1250 996370521 996370537
    0x513060e070f0906060f17130c17011406100207030b090a0503161104020403050c22020c1e010e030313210807031a0a030602070807020901060503091507050403020402 73
    0x540d058552140042c01941515501032200320b620b408081040c1a007107000c81c08002c003075240946614441c182540c508403000b403c4001c010389005d40040c00d03c0030310700356031003e0140c845208103600346000e0b4250103003046074141c140300342161002c10f42034546840c1044060065401070f1515503d50b0301c0c2c1a00e00c01005010300c02c50700941510000080d01800140310010624401c0900202c0d01c0c100071201e408202d0115005900c1008180081340c070002d580b04482e4021101c0094a02d84101c407e48200b18801404ca0007600115406808072404035412482f01d240c1c18140c0020703800d041501c0d0a0707070900c90200105400130400705019950483c850707486140a00081003411000312040000013502e9401400011400b40c00c0c460400e034503024001c124561806c40020b4104a00b0019585407010304c00100b030136034001035580812100c041a94101034004000c09400c1d81e542c0406041644104c840041d980100c0c0c02c207008624031340460f03d000c3d030f0003503991a0034a8115800d02c230081d445540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 996373021 1250 996371771 996371773
    0x240a0e06030105101a13080f03030f0a061404090f0606120209130209060120060403110d0c0507060507020a180e0d0f1b0201110d050a0e0307081914070e04110102010513060e 76
    0x1b00200b0780e0705007003004200c0f152020b4011580c03450170440800c04400e010780f01c494110b08020041182100d001000c942458044500180da0040c5290050385451740040044c0080e00300140022410114600e44100c180252005031483d036400c0ca81e09072085400308000d60001c0907101040c0e465110300386e99850301c00c0e01c4443e5402008220791842c034241003141c04a00050b8092140c042810f400c1c8856544408913091035244080070360b4a03580c440803a80901410410b02062120966484032807034001003840d440220202600d002c40c0b1009811081c1c00700010b4481e18014004a0b4031440e4448003c0c0710586d00c0809007525034520101a501d40d08040c1e0400c00352132102c656045003400080d000071880d071103107951070b000710300c2c00740100b540248a07a20a0700100400c00c0303061300c003080030081003c581004c0351081441d480c3c910240921150800c40380d1003060700104000d0900c580f45401503005e5a00d5030307001d0009400480c241c40046400c00c00e0208201ca1140c0080c4440d00b22403070035980d0340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 996374271 1250 996373021 996373057
    0x8160507120807020103110c2109130212010f03050a0b060d0510060503101e05060604030f1203060b0f07121e080615030f240a0e06030105101a 63
    0x71040c07034051151540255502d4000003060400c40d038041c4204510f441c0c05109190038592000e400c1516083c541203680003101d4010039800000611404a4440d800e0041c007424403110940351000c000d40015080503880040c1600124090320780d00c00600c06c4a62080080100482c19524a18415006401103402050303e107040303000a0001c1c422a0300307480c1c0b00d030b400041c0c0d1441e0a08151610b0001c03000b020301c0ba454161140000680034041e95102600391001085585402d00403444911a0342d0014000003043d442400810512042010300e0344001d94007401455150441c0c42080d104d99154541c2c0b00e402004800c1c002511684522100c008a09111380c3c070040790811884428010300c85e0400003586142040070301d180030700c186031082e0203001031a070852610b02220050000c029041c0c2007100504000f00c0022a80c0c1c40c501a800d110142c0040c0c1901d6039520520043c00c802c0d10040d1195003401d000580800300b040c04d20003100e001010042d01d0800d074a000040d20b5000c1000c807800e0107816 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 996375521 1250 996374271 996374279
    0xf0312051e030408070c061e0e03100e060a06050a050609011b0c080a0303052d04050a120503041a16031503080c1c0206063d18050d08160507 62
    0x101002d103225034000d030300c510380c0c030503c40c60110751140c1c80c0c2e0820000e0100d11100d46082d0100c09001c030194001c01d06090f0b9011121800192505142c440c40b0022030b0704100511401070f5000ca00c1c00d000c0c1c07010f20414080c0c0740d1544108107072108036002e004d4009000340035030b60782c540c410300790503103902c03540005014085c260f074031102a10986a0001c41003544034007402000c00d541403003082c0d03201950f0010956103002c0e03000c0e02140c40700c0e0070f0014001400d2307007000304040c40030900c06c0e4119940e100c41c10103042000c1000c06003064108a0782aa21a10000d2840740002c0c0c0b001e43e401e01c9111501080d24051b030440c4c205070000c04c2840003260355120804008000100035100810b185070f0904014401e049034181130540003401880e800301190083c0041c0078403034a50740749009450000002c03240ca01072400d41d40b18081402005100d8100c014001043c49440d081460510a08034032002d44001686074024894581c249070300080c03401c801005012840030b81000001400d51250043d25012a03607 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 996376771 1250 996375521 996375577
    0x4081b1903080910180303080c0f0310380d02120903120606040308121306050717010803132c071e0918050403090518010306060f031205 60
    0x400c1d00215403410001442900758a000402108004454680240c4a0210715507505800d49540b00040c180014840420141072004041c0c54031400d000d07003050707140e1400d022000c04030301091003148840d40c00203039201510381c001c03121070000c01c03d026110700c1151444003e21a8540c85145c030b00111039070034805040c0143d1030001450044038000010340e140d04201080304d045035070250000744942400c00c02080000c400d401a038500c2e02e48411070b0180e694511000061140481e980203180314502401c2008103074010004c0800310002c000e060f415680c854a100755640b107143e40c41100c0b02e110210401c580d02c0500c602d01268411400c0411503a1110380480d841c0e484241c54107004a15089580344040c6007460250710381041d03d10f020b0751000e00d80300103100c104030400e0282c0740d0107403520001002d06025030401c50040c44040d00128819100f40f078038560b4440300380400c4071a03c2c00d10b000011000700180d084410703240c10140c00c0507400341035402542d40c2d0b8032501d40031402812082c40a44100c074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 996378021 1250 996376771 996376819
    0x80c18031e060a0f0b031005061306091a03010501080a0b18030406120e0c01200c0a080a02030f01050403080705071707030c2108060f030c0405090d1404081b 69
    0x300c050010016070a003e4021415666400d10380403200c3d15011005101d0303500024400c2d0038441042d4001081d03112100800c1c03c0291151400c140d107800c20303400007455401944069070707640000c00b414204809103000c01d800d8602c01c1c41004020360040f2050800304021941c101d4000785034902070795801c0c0c4090220380c210b412036407268000c00c15000082258403070500800c0b45102440010348000107603100040c0c601d90303903002100b0220814100400520504210005045100900c95500c0e6560344451030b5a59000c810308078003034060302402d400c024105000d82ca0107542d164807001100c0d0340312101113850303402c840e005842c0c81400c000c9907070540b0403040003802c0c0c89000307540d2046892213505000d01e02c41c9066941d98004040251541c40701a403051107581c105104484004031003142c4400070b4580030400c0c00e2290700ca8038000500840e0039000801c10303800a5241c86d4007000201203000140a8095480b95001c2900025840e0180807044100550304e0b17a4000c04d41190241c00f01d0002100e84 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 996379271 1250 996378021 996378073
    0x150c0609060501080f0105010312050a0c1a070e030a02030a02060c190f12020c10050a020f0304181506020303070f14031f0b0405031002030a090818040606080c1803 72
    0x40c1e82e40018880d4000500c13141c41126030303000007401035515503641c403008800c0c452031107410040040f48070300b0340030300c1008a0320308250040a01c1600310b03c69100586200011b50300c40002c91014880310a10741004225009500d8008018001c0029180c00b0302c19940e00400c000c200500480700d800d070454456070440d400007406403005c142114003030720b0400384841031146140190740c4600308640c040e43e28801e203e110035019150031a16140440c50603407620701410400400340c000824089031481c1f00c03011041511108074400d000102020009103c100c0e442d02400703005800400004036007078010341004c21500450f24266283c1405a01100130940065903d055000c940d5642c10303908030320744007441025003401003100c0d16013407070000003070781d170368505007800e2626500400083c1d440c010507030044a081e60044075030350340e5640fa14403100708107558007082c4d0320a81c905000450780314070600a00c1e00c250204044075280c180d140950744003040100c01c0555141c4101a030510301a001030039142c60711 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 996380521 1250 996379271 996379283
    0x1002010903171302131d100c030b03060a2301080105040309080c0120120309151509010b09030109062c060f0c0a030623030d0c0b01150c0609 62
    0x800a20701d001400e154004005400901411040c0500201e1285891912940c11968120421007030090070000c0c2120924144201c1c040d034440c800c41610114102a244080c4c5900b04040501401c0c240c044802440158ad0182c0c8103400140c042c104036409503109140030500b614203403203c12001c0040c030400360002c0d00140d4490061008050304000c840c005000b000029102024528000130884511803081d0f64102e440794080001b40300003886060301d021000c48a096580c41c6c503060f400d0340e48024159103450b400718a800100d031142c1c3d180500c0510f82d401400e2a02903443c0005980140e0040d2050903455541c901e45000090030910403a40041d050b603800d00c14190119000d0012503034480ca540721607800c55403c100c80d04400041180e4411002c904060322208240b1044005021580200001104c1507144080700300c43c1501410321840100c0c02c46d0240f0b010007400316000382808000401d003003455001848078260808075102d4001c1240792926200d589500c900041c1c0d00340000035504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 996381771 1250 996380521 996380531
    0x70308070b0f010501230c06040c0e0c0901020613080d1517010e15040c080a0804030c060c120305071704080301030c24030b37060906090e060f100201 66
    0x30401840c0c07446a204a2031000603560b50324040000e4240315a03940500c0d51801508032000190202c0c0040d22000c8940d00c0442d60940391a10300041140c0590046050f42000b903800103a115490303100302c42000b68183d0140800e0f0300c4501490340010503400c000c54a06105012a1401c01c440c0e215000d0b0050094100c08103503440c01d01003483c030b9088400322003c50703410700c0c0c2265110034000600049600d08019500c0b51035071a800e19156202c0c080e00010040e01902c5505024000300300041e00a0340d010f00c428980d590303130394101500c41140004004291540301404152590700a0b40040e9101d0507030b050103207100e01183d015000c0c01c2822101114050b201000500c02d0280b440380b1032010740448444107140100c00500f00d440800c0c000d90220815031202862101c94a038a03014075000704001c4260b000719070b043c103203003107000c0d118180c800c40c0c00e1490100002c20500c02e80e00901247c1c0d09456524030399051107124040d420005091a8010a0742842d440890701d07640c3c0d1130740b80d02000b1f44c00025 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 996383021 1250 996381771 996381773
    0xc0f1206190e010b0a0e0606070c061e08042316031b09020913022505010902010315051e03030f160c090515040515040c11060c12070c0c050307030807 66
    0x3048818120303003050680e1428240101036164190175106490b945148100b16540d101c00140321480380e03d1009041c0070108400240c0c4039009200302d000034403500900d11300201e11560482e0180780c22100503007039411040d4088a05602001c1000020030040143e0f90480b0041d110034903206620b5004480a000c103420682c00015a0755450019011095080d490080100001074140843d4030f4103030305841e070010303411a00b400307940c402800725203440007098480341c4e440c24000c5c021311080f5010780c040381c2000001c545014059000c5410781d500100251400d1340414561b19540c102c00d0b0500c2d400d484100000c8200150080180c0816180c0421602c1c00c50804d1034401c2038101c20b40e01054207107080c401400f04c0015501405020a5001d9500142c03e5481000c03809850f45070304d410981181c940780711001140d07823081c80d8041c403691400c100c450a0b25020141041c42c0314280a18240460040c0400c280e107128503400a289070007100b5600c042d540b80c0c80048c0c20100594000c840301c090004000b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 996384271 1250 996383021 996383071
    0x41b020c01020f03030c0a110a05061504050603060103022d09011e06021207030311071a010617190b0a090507020309040612050607140d1a030f06090c0f1206 69
    0x150f02c120804000d5800d5040c041c5404501c2e00801c10050140034813807118901d000000c10085009940000480e400c0b810305682d07126691000c0b0100b54021801d042c0062214140001e00034100d0758060185082c06003034000307100134001f14100c121400040c0c2d0214030010355404812078040d00b5600c0d950320700c0d030402140c0101d08900341e600c9001550004c080c2e080030041c154061781c042daa09400c0104008007050580c041900c11034030000c148484100042d034200140141c1c2038181c81c815242c0c40d000c5d80304800e6580000000b15404d1a541c51014080c101078421900651601c0001806d000c221685071014102543d008407288001a4804900f840c03040c0b40500030078000708a00641412401069180d031910b43d84010400018401034880304583d0205410460b450b1550b6a4010011200c035407281c1e030001040e100d121440b0b840740d071032541d0b503641001c20224000c0c143c4500030129205c0321402d0040c1d02040c481243c1d8030030450406103100c980c0a0018a1003400c0c0d45080050041c1949044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 996385521 1250 996384271 996384283
    0xb0a03080316110f06070c031704050d0e1507080a0c0212061b0f182403040b1b04142205040302070806010f060804020d0f0f03090801020f030406020306041b020c0102 73
    0x1c98481e0b031041d4034007140c0c0304c00404c6090b045080c5281100020a0714107040c8e444100b454208020314450750204024050040b17200c004140312650b540d40340c007988400f0081030307441c10350030301c07801134010484480058010002001c0c8564203081842e9994a1500000c52102e0108150070f02ca4100d0340400a0340c06420180c0d100342d0740c0e120b012038104521a0103404081c01002100360a20100c400200760580d81c09889800502c06280d04c12041303801000039007030f2500141c1c0c04460b001e4140703000c92246503220301441242a021001c0070b0070540f400507e00c1c407443c00c00c0c822a400649103035081c08140003c007503801803181c0b20000401c040c01e00c0c1c90300a1814503d03502c10700311500100c005010a801c10743c9038004940d807511300000b454440d030000411a03602d541c0b00801340580207610404100356000031400c483d000ba212003484640d1420031074282c0c400c0700039402d4455400c00000300003507015805107801107406003000074048c1800c1c2250820010401480025034404c0c0a0070301d685da070402c07070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 996386771 1250 996385521 996385547
    0x503011508071704020d02060d1e0b01020c1012090b240609100915020c013c050d0f1a01020c030705150d02030a0f1404030804060b0a03080316 63
    0x110000c1e510b40140700808a8040700201d800341000140450f0565680c0c480c0c1e1880240c000304510350380e80310b00303202500504881d400c410310f131800c1082240c0d1440b81c41c89000207aa070181c02520481e10038204000000072540905c80611000d00d0700c65084058a03c030b60007040d0310808460403141031080040101e800034111100500118800000c8107841c0ca00c242d552034035040e1082c04d00c904d0080d40035202c01c0c15981020010748241404404545d500280350386032144280ca034650201614500386041030301202c5003507080103112000b2100303407012034055045420a480c0c80c9080020a880c080300ba69110200898240e44a203d9984040c03010850209200300900051a4503007010010a071202143d115840c461026071b514011020441c80441e9000041c1d208210340d0381ca800108034004004c0411600c0300c980c0341c00b005a0060300d0005c110380c00396806403504103442e030b901d9880346d0181100d100c1c02500443c0103140000041c0c09000075601401c02c04800003201e020340b84004102c0c9884c840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 996388021 1250 996386771 996386777
    0x203040c030c090c090306020307260a060b040320061b06040203190f080d0b060c07080c010c030203091201060801060b2d0a050a030b0907230c0c0f03010b0405010605030115 76
    0x455004c005030000c1c408003c40f80d0104000d03890703558040050701e500d03400044404900500690702108a64034444540c819620a2420400551104403c0203079014500004000032000e507100b040c2040c10b04030340c81603480e008101d6454032004003500c05010580d241500110751000c4207000861606020380d904840108001d50b500c08101d850305040380004810280a0303080000b803420092000c2c0e0010681040042c03d901e594812420000d5524007441c032501d00f1902078000b50001c070f58450511512a0354151340210b0400100004205c00b804e829030344d61320b403507503642e40002d81f001c1d00303010300b0303000380109040c1c1510b9040440705001c0344141d0318282510044461803850410224005030b5010403d103190168540b1100c3d1001c1c1c00521103c840190f1001001b002c0041c4142d00198024102041014804401541c144044464002c1c68402482078029921414803070605500042070401c0c0100046540f20200b00410103e410a03044040010780000c01801000003200745510700d603d03a45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 996389271 1250 996388021 996388031
    0x70501020105150d020411070b010608090606100e01020c030105090d02010f02040b1204060b090a0911031605131407050a170721140a0c0e010c0230010203040c030c09 73
    0x169035503c04401c046144a60000340701071055458941c02650034812001c4041d03a9103020f41090002080d00340b00d040b002500d00800502412000f2900c54010f5401500c400e4242046200c03d440c0c00f080c00c0c9140381184a41ca80d100c4481c0c1d02401200c0c01005203001615464030f2480000303003510480d00140003076a004120070442c0c200345404481c4e1801601c1c001d9000c5440c0d40ca0400090400102026072165040d001e02140e0440b591024107828422160201c101c46d00f44241904d450303880084040384083da440400507070900362418042404903c0c8006003900003905401c2e82c3c0a01078600c2000900302143e030b0364505400c058082d06001130300303459481d54500558001c0c031000b81c542d400942400280107082c5500f40740e0300801494039501d20905194070f020108003001700000c18540c40014400044400c2a5004080d84015150091f1414159440e181c01581d12006021802c0da807046000f02c41000e151400e201850180c0d201d210810021843c60070140c110b01e4082e046406000c0c580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 996390521 1250 996389271 996389281
    0x21c0302041a210709090e0106090f290d05060f060108060904210e03011e06051813050a021c06050109053306040b030a0f0e030d0b03010605061b070501020105 70
    0xc80406070562203994015226964030300c0840300c83e40070741d00c44039220341805038610f0381f042d064010780c0076900b0140c0100705001060403640113803202070a403803521807070f1070999034050f00d0b2010340810b1012028140b0301401510b40da0b55890600704a07000304100b0950b4007403125a41c4d126038900c2e08008200e82d00200c5040c10303181e521500c902c440f911a41c0f012070042c442545400b9400450030841c0041c020071001e030751003008040034103d1000c33503481186404804a03c0e071910003a040d5130b00811191485e460b41d0740540c0c0400280c1c10748400d580c00d00ca04451440140e4520545c9005162440d10f100421074003407a000080c0d070010313042401080c0c140310400000300c03442e04a0308000c030910001e090642c032144d2060001c0404c0ca00340385030020000103010820b00749a50095000f039a8041c81008400303440d541c0310b003c42c0c1400218001582080040030010420b6400100d03891000500014102d5620340014001b50312180d14501d04001c120702503c40294240b00c00341c000d050a0009000503d01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 996391771 1250 996390521 996390547
    0xf030604111312020d060f050a05090d1b02150a0f0f1b0227010609050f1005093c010807020a12050f040810020705070f1410021c0302041a 61
    0x2030007141141e80f181604002999a6116200e4900340c10120400c02c840141d4080b80c0909801c0318031440c0f503800d05006c50b818220000310041c680015a6032201c04401c408a6048295003100e409ea90002001a06542d0481000b0041518011b2072700d4102c940c80e0f04050142100c0c0c40c1600150502c0010035410216800c880710006000e903040700c1000100c0c040c600c000212030070f500418269080a0000443d9607500516030105680044408104035110389003003003003c1301065124030025005001c040103d0a1034911181c01c6240d00060138102ca20185207642c10421011300c10b040440022a403241c1d81d600410140d070000310a102824121101d03842c0c180e1141248501c00301007050004800c0c1000b180d84e070581d405000c0210585031401090080600a500a5034040d2620702551000241c07901c0c840c006941207031110702004034188c0d86201006181204807260702c0641c000c024104c40300c64448841038a10082a80780162100d0500c04c2c1500c28040c0e940303444004c8202004001d5220358 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 996393021 1250 996391771 996391807
    0x301080309040207050a1a091e07270903020d08061e060a110714150a090323031b010f020703081305010b0a030b1905190c030b060f03060411 62
    0x38142c50240c0e940e0080d140c940d20b040b2a441c0003804811001d90900d00d248174507454940240c071004100c0d03e01c80041881031080241d608111182c03603200500c108020300d0b501c20380080d00c481d0142d0103040140c04501c91410303500044002c030b005070407440301001e090b600441c1140e08030304103807520000a0070a04d043e18ad52001c0141d43c52080d07402080000e45544032300840c06940040740155800255104c500a51110203c070803203100301c42c103054024007405603000351401000960b0b2200344907851a21241c0c000b800100381340001440780540d64000d803004100500d000c0d01ca81844c0c581402e4200c440d6800c4031071880d5610302c89401004114003190b4000d50300e94104111800c0000c43c1070700c03440c085004118400d612500440ea00b02d0000034003065010003441540030044802c403a50390306030106c2c03c44404860710390380f4201d01c4070b04550040c0d242d07100e0300100c90309040c00120f924091000501130740001c031403055000c03000010001d05060a0242d52110691032400c00d06001d8040030180002e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 996394271 1250 996393021 996393037
    0xa0c02030307200106030b01080c100801122609040e011b12061214010c140f03071404080c010e0301020403210207120308040201031d1002160204020424030203010803 73
    0x8a21543c01112030390079002101c41c500c00100030018190380e85400c0d1080c5c80c0074131800e1100e000e08103280001c1d0a1440c1181c50f8a441a904c0a8542e802c1c1101100703040c012141c1641d0110100d556003101500c01314020b01481201305100b1303114002c4c4000c000a071488160550302a0341040702403010304400140092140b901810002510401034560302c00500c0280d102800700c504d0381c4628000e000d400b040300490201c0c520000e1007508000a02562401c24031407442c4100002001000e8110941501441d0050b12a24014590150340342c030038109600550040030040e00301540c00394507580c110051b24070110080c1d0080d41840d14584910b24030782000320704a4160300300000f180c5046031013070005a01415448a11312448a03aa007002080084110703000c0340402e1a0590b45c44103506840d090032006000e9000130030b4401000c94100d0082e4200ca0340381250301034a40c64800c0180c1d40c42c009000030b001e5110762424100c9505050f201c141042591410905204000500a4210200c100c0d1046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 996395521 1250 996394271 996394277
    0x50a03090204020d151a0c071203030e0105010e0118200f0c03070f020f1c030509030a050a05010c03180302120f090402030a0c0f0e1813081803060a0c02030307 70
    0x2850074004103010340302d5840042485840d00c04003901e01285000110b00765080760403400b613034003001e443c00c003603600c24510031400d55801040c04102d18a41c82001c1000d640c071918020480d890202e0300c0030b00703540702a007100342c0d180010340c01481620030260b500d80700c1c040703a00300500c5440c1448541180c840c41c1c80043c582000340c00284007411909100807130f199490b5801c12680c1c1c95520742443d842c500ca81c09030803071284240801380075540c039108d00309103e076840550b0022110074440d942a1650f6100850050300f6012309440354010440602040440c3e602440c00803440a1100d00002e048986460320240e01010385450b003c0465400039420f09180c0344000c0140c0d89503500d00c52046140500c4000a600500010421680000a0704200426030142c0c460507580da0202c60b080c0c4000595081583c3c0280c009510a80c1c0010f201d01041e4002541001e803081010068952661550200c0e07003881480a03c12401d80f0356040030000164802082c00042041c0c0c526414001e48912000d0004410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 996396771 1250 996395521 996395531
    0xc17070302011d180a0b01180e19061d190e0312190905010c08090303130209060609030d05040e09060708191104060201060608060405040206040e150303030a0501080f010c050a03 78
    0xa515843c1c501180301504902000700340c0342c4011400e0150402130b002c84e0009007118046444a13491900c0d2300d094a00c0201c1c0c2440964507001081c600d030004001d01c400039030700d0700307000140301d40000601c500c003e0410762004000c3c60b00c18400b1219030100f1011803503692501420358003214001c41030b9521011200030496464407500c0c2100c0c1c4458000d00a043c02c0d5140c4003d402c10400158002c00d0701c0c410325201c1706e0803030b5030700e002e5162280802c4401e00d0001410090050040c50710407005030384a0301c020886400e1150344c80100f49803448c1d030303040300001c01c04c00202070055413009090181c4c45085d8078001c12040c23609850040c02400c02518101c00342d003042c820380d09440290780000040c880100c402c00c0d100d56484100a000e0020340c414000412001000f14099050500503284215006050070349010701d010300f981c071980300080040c902800400f000200700e40c1c052000f1406132450707241c00705141d41007038082400c0c80840300d0110156858001c6500e125608541624140b0130346042c0014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 996398021 1250 996396771 996396827
    0x51203091c051902060105150703020a050303010f03262517130b0306060406050c070902070807140c03070e0712060816120b010e18010203040c1707030201 68
    0x2181c0114669540035090591a400302000d901c440506110400c48000e1142081c01c03a2042e038880100b8041d10390004c140d58105105164a10020204103210344100e0341d07500e4a544941d400c60b00700307800c54562141100010428000c1c014091310020002c0840e06926109060780340c4010303c903c0e540c0c118584615940c60b0317228521141540c1010782c00005940700c40b0704070114118140d0019101c0d42503802030300d0021405001940580340b00300c8019201c24030f0203003000c20030383c0c664010340d43c0c04d8224400c11402085404440c000b8002251103182e8040d11018289050550140c03910544107075684407050440403035600064003030498541d0202c1943e6500c80c25400c8891041c1c00942d100501c1c20407100041224002400f45240c1158024914000351500380100261109207000781c0030b2000400103000111507003c0c042c3e00900e40800919000c05002c01c01030983c0c10448040d50301400c4030004100c8615141c200b03907200c030802005000041e0460b80040e016050781e15451809885454030740f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 996399271 1250 996398021 996398023
    0x9120204060305010c08061002070602030d050c0c07060905030d0806010816030e0a0f1e021f0318151113210b0f010329070e0a030b0106090e010f0305120309 69
    0x3a020b0b5810000a10a064807403e002c0c110080c2a0790143c050102c000704060050b01c0400e40c0c00031340e022039000c0c514084040ca40300001c3d110103044102c05540c00c02100203980c03003c020540c02005079884411040740761000301414484161141414850000c003082044c2c0c0c0d00903000759008252400c1d410504068413011401040034104007446441455800d5083c442c1c0c541d01000310601c18800c801415148900e00e031014003a50000940118038514940c41221624440380746030350242ca0000703012142c20091421803490800c043d1007006551030200603002311405400c402d0024809068903000401e03810300d060701c8040c8111441c0c41c2000c41d4080011042907021100d0b56000220b880f480d0030500c0c8040300540081c8400c4680c00c100038021440d41d10189103d01034074654546408140d5100e04d000d44400c0700e00c1c00ca003640580b800101200003405409858003a2030b00b666208103040c204201c101c418101a0841c54418071964007c01c0060000245840035402541c1d206440792522940c0d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 996400521 1250 996399271 996399281
    0x1050a030c0c08040f030506130308061309051014150619050d1b0801060201050411090c0910020c040c020309030c06160804060e091e0f130c0e060f03030a09120204 72
    0xa04040e00084c00240c2c903019144800103070b03401001519a540c5a40300c0b8440b0440e000c000003030101d009940000e02516002c0c2101044a0902102040c055030035958907041c40840601030300383c2079440400003405503030f04011591080c0e003c41c0462011036403030005506402030328014014101480102180b907480b4409540c02c0345541c9000388000114030002d141c042d00c40c00f054500042c40ca0000041c00e5105014403030050f80c0020241520740607134000c3c0103039000d00815032916614108200c40d2a03440f070000c80c41036003d40b9400b500160395010100025503600c1421642154818418a02c0a0b540480d07106407105048554035903403c0005501020461448406007800c0c1c00803070001085a0031601000855804491022856513145001c0a61071034140f00154075111000000b01e80320080d80481d83c200b00343e031000940540b1980e0f50764901d807403107400410b0080300751024000541030040500c4280201240994200f8034902c2c0010070110f0b10717100e000066a0817900d1034041d526542c2c80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 996401771 1250 996400521 996400523
    0x20c06030a0f02031306050907061218051605010915020319110304030f020a0b18040902040f090c050a0909121209210e0a061409060d05011e0b040501050a030c0c 71
    0x19904d81c50038400307240c0180503005041d2480750810000503034560b0041160390a44070152115600c8030040302010000300801c0d01c404100680842c446008100104411030b0500180030b44040705030701f4000014441d02003a8400740c0d613800c034940d501d11b03130540100a0701c0c02e115070080c03a0080b0320006201219a08240080103800d404005004001e02a2081e04025164003e50300c4143d455030f11100e03511944628a4074466110360b8219a4031030345401c1d04002070b0140002d102040755129412810100d030300305042200d603200c50100c1048039080c003081d8080182843d140400c420040c944035858110900c03941207080080a1010b040d00942d9540043c11031900060310603404036004241074030070b1b9030100d044404030f814803090b9801d515103a0450010786405644d21904a00b501c002c10341d66411180341141c0c8000d09119680580e0401e110f168024020740c0d19121401c7c00c0700303101c200120415004045c1007601088144800e980010407211924000c2c500012000c0340f0440480e2104030800b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 996402877 1106 996401771 996401801
    0x201030c090302040f0e120901050723010207060515030705131a040905060712020702011d04091a070e030f0601030609050f122107020c06030a 63
    0x424410202820141c00050301c035030024041d24002082c01031520741d40c0c0e0712184d81e9403040000e1090000503000541c40c051510b00020803501c1264030241c10a1540542251600c0c1a04c08200306404003074000c648a500f0b40c581000901016218400080304003c4001c215140201c1d40c80308881c002851211102821001d4001404d0100c0000052414518507002c550f00c03140a12a1440d2040001c4e05640c030700740344047d022050300c080180c0074920500910006036040504240c145080140c40240c84076014000390140c0010395009000c041080581d82c3d032001d074002d50b24004d42c95600c507801c03070f90b21450a1603601d07c0000c4c0301c0540d952100c2c004101103000c6500808195005030141c60000ca01c02d1219481e1030001070f140c0d901703a4000070320001a8100c00007800340e10308410b1003085040c03d14a4000b0b644020302c5241620646000000c911032088541c09140c0f4204114 = true := by decide +kernel

theorem cover : BRFrame.Cov 996223021 996402877 := by
  have h0 := BRFrame.cov_init 996223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 996223021 ≤ n) (h2 : n < 996402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
